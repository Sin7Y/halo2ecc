use std::array;

use crate::types::FieldNum;

use halo2::{
    circuit::Region,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::collections::HashSet;

trait EccPlus <F: FieldExt>: Chip<F> {
    type EccPoint;
    fn perform (
        &self,
        layouter: impl Layouter<F>,
            a: Self::EccPoint,
            b: Self::EccPoint,
    ) -> Result<Self::EccPoint, Error>
}

#[derive(Clone, Debug)]
struct Config {
    q_add: Selector,
    // lambda
    lambda: Column<Advice>,
    // P = (x_p, y_p)
    pub x_p: Column<Advice>,
    pub y_p: Column<Advice>,

    // Q = (x_qr, x_qr)
    // R = (x_qr, x_qr)
    pub x_qr: Column<Advice>,
    pub y_qr: Column<Advice>,

    // α = inv0(x_q - x_p)
    alpha: Column<Advice>,
    // β = inv0(x_p)
    beta: Column<Advice>,
    // γ = inv0(x_q)
    gamma: Column<Advice>,
    // δ = inv0(y_p + y_q) if x_q = x_p, 0 otherwise
    delta: Column<Advice>,
}

struct EccPlusChip<F: FieldExt> {
}


impl Config {
    pub(crate) fn advice_columns(&self) -> HashSet<Column<Advice>> {
        core::array::IntoIter::new([
            self.x_p,
            self.y_p,
            self.x_qr,
            self.y_qr,
            self.lambda,
            self.alpha,
            self.beta,
            self.gamma,
            self.delta,
        ])
        .collect()
    }

    pub(crate) fn output_columns(&self) -> HashSet<Column<Advice>> {
        core::array::IntoIter::new([self.x_qr, self.y_qr]).collect()
    }

    pub(crate) fn create_gate(&self, meta: &mut ConstraintSystem<pallas::Base>) {

        // if (x_p, y_p) = (x_qr, -y_qr)
        //     # point1 + (-point1) = 0
        //     ret None
        // else if (x_p, y_p) = (x_qr, -y_qr)
        //     m = (3 * x1 * x1 + curve.a) * (2 * y1)^{-1}
        // else:
        //     m = (y1 - y2) * inverse_mod(x1 - x2, curve.p)

        // x3 = m * m - x1 - x2
        // y3 = y1 + m * (x3 - x1)
        // result = (x3 % curve.p, -y3 % curve.p)

        meta.create_gate("complete addition gates", |meta| {
            let q_add = meta.query_selector(self.q_add);
            let x_p = meta.query_advice(self.x_p, Rotation::cur());
            let y_p = meta.query_advice(self.y_p, Rotation::cur());
            let x_q = meta.query_advice(self.x_qr, Rotation::cur());
            let y_q = meta.query_advice(self.y_qr, Rotation::cur());
            let x_r = meta.query_advice(self.x_qr, Rotation::next());
            let y_r = meta.query_advice(self.y_qr, Rotation::next());
            let lambda = meta.query_advice(self.lambda, Rotation::cur());

            // α = inv0(x_q - x_p)
            let alpha = meta.query_advice(self.alpha, Rotation::cur());
            // β = inv0(x_p)
            let beta = meta.query_advice(self.beta, Rotation::cur());
            // γ = inv0(x_q)
            let gamma = meta.query_advice(self.gamma, Rotation::cur());
            // δ = inv0(y_p + y_q) if x_q = x_p, 0 otherwise
            let delta = meta.query_advice(self.delta, Rotation::cur());

            // Useful composite expressions
            // α ⋅(x_q - x_p)
            let if_alpha = (x_q.clone() - x_p.clone()) * alpha;
            // β ⋅ x_p
            let if_beta = x_p.clone() * beta;
            // γ ⋅ x_q
            let if_gamma = x_q.clone() * gamma;
            // δ ⋅(y_p + y_q)
            let if_delta = (y_q.clone() + y_p.clone()) * delta;

            // Useful constants
            let one = Expression::Constant(pallas::Base::one());
            let two = Expression::Constant(pallas::Base::from_u64(2));
            let three = Expression::Constant(pallas::Base::from_u64(3));

            // (x_q − x_p)⋅((x_q − x_p)⋅λ − (y_q−y_p)) = 0
            let poly1 = {
                let x_q_minus_x_p = x_q.clone() - x_p.clone(); // (x_q − x_p)

                let y_q_minus_y_p = y_q.clone() - y_p.clone(); // (y_q − y_p)
                let incomplete = x_q_minus_x_p.clone() * lambda.clone() - y_q_minus_y_p; // (x_q − x_p)⋅λ − (y_q−y_p)

                // q_add ⋅(x_q − x_p)⋅((x_q − x_p)⋅λ − (y_q−y_p))
                x_q_minus_x_p * incomplete
            };

            array::IntoIter::new([
                poly1,
            ])
            .map(move |poly| q_add.clone() * poly)
        });
    }

    pub(super) fn assign_region(
        &self,
        p: &EccPoint,
        q: &EccPoint,
        offset: usize,
        region: &mut Region<'_, pallas::Base>,
    ) -> Result<EccPoint, Error> {
        // Enable `q_add` selector
        self.q_add.enable(region, offset)?;

        // Copy point `p` into `x_p`, `y_p` columns
        copy(region, || "x_p", self.x_p, offset, &p.x)?;
        copy(region, || "y_p", self.y_p, offset, &p.y)?;

        // Copy point `q` into `x_qr`, `y_qr` columns
        copy(region, || "x_q", self.x_qr, offset, &q.x)?;
        copy(region, || "y_q", self.y_qr, offset, &q.y)?;

        let (x_p, y_p) = (p.x.value(), p.y.value());
        let (x_q, y_q) = (q.x.value(), q.y.value());

        //   [alpha, beta, gamma, delta]
        // = [inv0(x_q - x_p), inv0(x_p), inv0(x_q), inv0(y_q + y_p)]
        // where inv0(x) = 0 if x = 0, 1/x otherwise.
        //
        let (alpha, beta, gamma, delta) = {
            let inverses = x_p
                .zip(x_q)
                .zip(y_p)
                .zip(y_q)
                .map(|(((x_p, x_q), y_p), y_q)| {
                    let alpha = x_q - x_p;
                    let beta = x_p;
                    let gamma = x_q;
                    let delta = y_q + y_p;

                    let mut inverses = [alpha, beta, gamma, delta];
                    inverses.batch_invert();
                    inverses
                });

            if let Some([alpha, beta, gamma, delta]) = inverses {
                (Some(alpha), Some(beta), Some(gamma), Some(delta))
            } else {
                (None, None, None, None)
            }
        };

        // Assign α = inv0(x_q - x_p)
        region.assign_advice(
            || "α",
            self.alpha,
            offset,
            || alpha.ok_or(Error::SynthesisError),
        )?;

        // Assign β = inv0(x_p)
        region.assign_advice(
            || "β",
            self.beta,
            offset,
            || beta.ok_or(Error::SynthesisError),
        )?;

        // Assign γ = inv0(x_q)
        region.assign_advice(
            || "γ",
            self.gamma,
            offset,
            || gamma.ok_or(Error::SynthesisError),
        )?;

        // Assign δ = inv0(y_q + y_p) if x_q = x_p, 0 otherwise
        region.assign_advice(
            || "δ",
            self.delta,
            offset,
            || {
                let x_p = x_p.ok_or(Error::SynthesisError)?;
                let x_q = x_q.ok_or(Error::SynthesisError)?;

                if x_q == x_p {
                    delta.ok_or(Error::SynthesisError)
                } else {
                    Ok(pallas::Base::zero())
                }
            },
        )?;

        #[allow(clippy::collapsible_else_if)]
        // Assign lambda
        let lambda =
            x_p.zip(y_p)
                .zip(x_q)
                .zip(y_q)
                .zip(alpha)
                .map(|((((x_p, y_p), x_q), y_q), alpha)| {
                    if x_q != x_p {
                        // λ = (y_q - y_p)/(x_q - x_p)
                        // Here, alpha = inv0(x_q - x_p), which suffices since we
                        // know that x_q != x_p in this branch.
                        (y_q - y_p) * alpha
                    } else {
                        if y_p != pallas::Base::zero() {
                            // 3(x_p)^2
                            let three_x_p_sq = pallas::Base::from_u64(3) * x_p.square();
                            // 1 / 2(y_p)
                            let inv_two_y_p = y_p.invert().unwrap() * pallas::Base::TWO_INV;
                            // λ = 3(x_p)^2 / 2(y_p)
                            three_x_p_sq * inv_two_y_p
                        } else {
                            pallas::Base::zero()
                        }
                    }
                });
        region.assign_advice(
            || "λ",
            self.lambda,
            offset,
            || lambda.ok_or(Error::SynthesisError),
        )?;

        // Calculate (x_r, y_r)
        let r =
            x_p.zip(y_p)
                .zip(x_q)
                .zip(y_q)
                .zip(lambda)
                .map(|((((x_p, y_p), x_q), y_q), lambda)| {
                    {
                        if x_p == pallas::Base::zero() {
                            // 0 + Q = Q
                            (x_q, y_q)
                        } else if x_q == pallas::Base::zero() {
                            // P + 0 = P
                            (x_p, y_p)
                        } else if (x_q == x_p) && (y_q == -y_p) {
                            // P + (-P) maps to (0,0)
                            (pallas::Base::zero(), pallas::Base::zero())
                        } else {
                            // x_r = λ^2 - x_p - x_q
                            let x_r = lambda.square() - x_p - x_q;
                            // y_r = λ(x_p - x_r) - y_p
                            let y_r = lambda * (x_p - x_r) - y_p;
                            (x_r, y_r)
                        }
                    }
                });

        // Assign x_r
        let x_r = r.map(|r| r.0);
        let x_r_cell = region.assign_advice(
            || "x_r",
            self.x_qr,
            offset + 1,
            || x_r.ok_or(Error::SynthesisError),
        )?;

        // Assign y_r
        let y_r = r.map(|r| r.1);
        let y_r_cell = region.assign_advice(
            || "y_r",
            self.y_qr,
            offset + 1,
            || y_r.ok_or(Error::SynthesisError),
        )?;

        let result = EccPoint {
            x: CellValue::<pallas::Base>::new(x_r_cell, x_r),
            y: CellValue::<pallas::Base>::new(y_r_cell, y_r),
        };

        #[cfg(test)]
        // Check that the correct sum is obtained.
        {
            use group::Curve;

            let p = p.point();
            let q = q.point();
            let real_sum = p.zip(q).map(|(p, q)| p + q);
            let result = result.point();

            if let (Some(real_sum), Some(result)) = (real_sum, result) {
                assert_eq!(real_sum.to_affine(), result);
            }
        }

        Ok(result)
    }
}


