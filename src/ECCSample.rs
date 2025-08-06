mod testArith{
use ark_std::test_rng;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::dev::MockProver;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2curves::grumpkin::Fq;
use halo2curves::grumpkin::G1Affine;

use halo2_native_ecc::ArithOps;
use halo2_native_ecc::ECChip;
use halo2_native_ecc::ECConfig;
use halo2_native_ecc::NativeECOps;

#[derive(Default, Debug, Clone, Copy)]
struct ArithTestCircuit {
    f1: Fq,
    f2: Fq,
    f3: Fq,      // f3 = f1 + f2
    f4: Fq,      // f4 = f1 * f2
    f5: [Fq; 6], // partial bit decom
}

impl Circuit<Fq> for ArithTestCircuit {
    type Config = ECConfig<G1Affine, Fq>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        ECChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        let field_chip = ECChip::construct(config.clone());

        layouter.assign_region(
            || "test field circuit",
            |mut region| {
                let mut offset = 0;

                // unit test: addition
                {
                    let f3_rec =
                        field_chip.add(&mut region, &config, &self.f1, &self.f2, &mut offset)?;
                    let f3 = field_chip.load_private_field(
                        &mut region,
                        &config,
                        &self.f3,
                        &mut offset,
                    )?;
                    region.constrain_equal(f3.cell(), f3_rec.cell())?;
                }

                // unit test: multiplication
                {
                    let f4_rec =
                        field_chip.mul(&mut region, &config, &self.f1, &self.f2, &mut offset)?;
                    let f4 = field_chip.load_private_field(
                        &mut region,
                        &config,
                        &self.f4,
                        &mut offset,
                    )?;
                    region.constrain_equal(f4.cell(), f4_rec.cell())?;
                }

                // unit test: partial bit decompose
                {
                    let _cells = field_chip.partial_bit_decomp(
                        &mut region,
                        &config,
                        self.f5.as_ref(),
                        &mut offset,
                    )?;
                }

                // unit test: decompose u128
                {
                    let bytes = (0..16).map(|x| x).collect::<Vec<u8>>();
                    let a = u128::from_le_bytes(bytes.try_into().unwrap());
                    let _cells =
                        field_chip.decompose_u128(&mut region, &config, &a, &mut offset)?;
                }

                // pad the last two rows
                field_chip.pad(&mut region, &config, &mut offset)?;

                Ok(())
            },
        )?;

        Ok(())
    }
}

#[test]
fn test_field_ops() {
    let k = 10;

    let mut rng = test_rng();

    let f1 = Fq::random(&mut rng);
    let f2 = Fq::random(&mut rng);
    let f3 = f1 + f2;
    let f4 = f1 * f2;
    {
        let f5 = [
            Fq::one(),
            Fq::zero(),
            Fq::zero(),
            Fq::one(),
            f1,
            f1 * Fq::from(16) + Fq::from(9),
        ];
        let circuit = ArithTestCircuit { f1, f2, f3, f4, f5 };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // error case: addition fails
    {
        let f3 = f1 + f1;
        let f5 = [
            Fq::one(),
            Fq::zero(),
            Fq::zero(),
            Fq::one(),
            f1,
            f1 * Fq::from(16) + Fq::from(9),
        ];
        let circuit = ArithTestCircuit { f1, f2, f3, f4, f5 };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
    // error case: multiplication fails
    {
        let f4 = f1 * f1;
        let f5 = [
            Fq::one(),
            Fq::zero(),
            Fq::zero(),
            Fq::one(),
            f1,
            f1 * Fq::from(16) + Fq::from(9),
        ];
        let circuit = ArithTestCircuit { f1, f2, f3, f4, f5 };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
    // error case: not binary
    {
        let f5 = [
            Fq::from(2),
            Fq::zero(),
            Fq::zero(),
            Fq::one(),
            f1,
            f1 * Fq::from(16) + Fq::from(10),
        ];
        let circuit = ArithTestCircuit { f1, f2, f3, f4, f5 };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
    // error case: sum not equal
    {
        let f5 = [
            Fq::zero(),
            Fq::zero(),
            Fq::zero(),
            Fq::one(),
            f1,
            f1 * Fq::from(16) + Fq::from(10),
        ];
        let circuit = ArithTestCircuit { f1, f2, f3, f4, f5 };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}    
}

mod testECC{
    use std::ops::Mul;

use ark_std::test_rng;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::dev::MockProver;
use halo2_proofs::halo2curves::group::Curve;
use halo2_proofs::halo2curves::group::Group;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::ConstraintSystem;
use halo2_proofs::plonk::Error;
use halo2curves::grumpkin::Fq;
use halo2curves::grumpkin::Fr;
use halo2curves::grumpkin::G1Affine;
use halo2curves::grumpkin::G1;

use halo2_native_ecc::ECChip;
use halo2_native_ecc::ECConfig;
use halo2_native_ecc::NativeECOps;
use halo2_native_ecc::ArithOps;

#[derive(Default, Debug, Clone, Copy)]
struct ECTestCircuit {
    s: Fr,
    p1: G1Affine,
    p2: G1Affine,
    p3: G1Affine, // p1 + p2
    p4: G1Affine, // 2p1
    p5: G1Affine, // p1 * s
}

impl Circuit<Fq> for ECTestCircuit {
    type Config = ECConfig<G1Affine, Fq>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Self::Config {
        ECChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fq>,
    ) -> Result<(), Error> {
        let ec_chip = ECChip::construct(config.clone());

        layouter.assign_region(
            || "test ec circuit",
            |mut region| {
                let mut offset = 0;
                // unit test: `load private unchecked`, then `enforce is on curve`
                let _p1 = {
                    let p1 = ec_chip.load_private_point_unchecked(
                        &mut region,
                        &config,
                        &self.p1,
                        &mut offset,
                    )?;
                    ec_chip.enforce_on_curve(&mut region, &config, &p1, &mut offset)?;
                    p1
                };
                // unit test: load private
                let _p2 =
                    ec_chip.load_private_point(&mut region, &config, &self.p2, &mut offset)?;
                let p3 = ec_chip.load_private_point(&mut region, &config, &self.p3, &mut offset)?;
                let p4 = ec_chip.load_private_point(&mut region, &config, &self.p4, &mut offset)?;
                let p5 = ec_chip.load_private_point(&mut region, &config, &self.p5, &mut offset)?;

                // unit test: point addition with 1
                {
                    let p1 = ec_chip.load_private_point_unchecked(
                        &mut region,
                        &config,
                        &self.p1,
                        &mut offset,
                    )?;
                    let p2 = ec_chip.load_private_point_unchecked(
                        &mut region,
                        &config,
                        &self.p2,
                        &mut offset,
                    )?;
                    let bit = ec_chip.load_private_field(
                        &mut region,
                        &config,
                        &Fq::from(1),
                        &mut offset,
                    )?;
                    let p3_rec = ec_chip.conditional_point_add(
                        &mut region,
                        &config,
                        &p1,
                        &p2,
                        &bit,
                        &mut offset,
                    )?;

                    region.constrain_equal(p3.x.cell(), p3_rec.x.cell())?;
                    region.constrain_equal(p3.y.cell(), p3_rec.y.cell())?;
                }

                // unit test: point addition with 0
                {
                    let p1 = ec_chip.load_private_point_unchecked(
                        &mut region,
                        &config,
                        &self.p1,
                        &mut offset,
                    )?;
                    let p2 = ec_chip.load_private_point_unchecked(
                        &mut region,
                        &config,
                        &self.p2,
                        &mut offset,
                    )?;
                    let bit = ec_chip.load_private_field(
                        &mut region,
                        &config,
                        &Fq::from(0),
                        &mut offset,
                    )?;
                    let p3_rec = ec_chip.conditional_point_add(
                        &mut region,
                        &config,
                        &p1,
                        &p2,
                        &bit,
                        &mut offset,
                    )?;

                    region.constrain_equal(p1.x.cell(), p3_rec.x.cell())?;
                    region.constrain_equal(p1.y.cell(), p3_rec.y.cell())?;
                }

                // unit test: point doubling
                {
                    let p1 = ec_chip.load_private_point_unchecked(
                        &mut region,
                        &config,
                        &self.p1,
                        &mut offset,
                    )?;
                    let p4_rec = ec_chip.point_double(&mut region, &config, &p1, &mut offset)?;

                    region.constrain_equal(p4.x.cell(), p4_rec.x.cell())?;
                    region.constrain_equal(p4.y.cell(), p4_rec.y.cell())?;
                }

                // unit test: scalar decomposition
                {
                    let start = offset;
                    let _scalar_cells =
                        ec_chip.decompose_scalar(&mut region, &config, &self.s, &mut offset)?;
                    println!("scalar decompose uses {} rows", offset - start);
                }

                // unit test: curve mul
                {
                    let start = offset;
                    let p5_rec =
                        ec_chip.point_mul(&mut region, &config, &self.p1, &self.s, &mut offset)?;
                    region.constrain_equal(p5.x.cell(), p5_rec.x.cell())?;
                    region.constrain_equal(p5.y.cell(), p5_rec.y.cell())?;
                    println!("curve mul uses {} rows", offset - start);
                }

                // pad the last two rows
                ec_chip.pad(&mut region, &config, &mut offset)?;

                Ok(())
            },
        )?;

        Ok(())
    }
}

#[test]
fn test_ec_ops() {
    let k = 14;

    let mut rng = test_rng();
    let s = Fr::random(&mut rng);
    let p1 = G1::random(&mut rng).to_affine();
    let p2 = G1::random(&mut rng).to_affine();
    let p3 = (p1 + p2).to_affine();
    let p4 = (p1 + p1).to_affine();
    let p5 = p1.mul(s).to_affine();

    {
        let circuit = ECTestCircuit {
            s,
            p1,
            p2,
            p3,
            p4,
            p5,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    // error case: add not equal
    {
        let p3 = (p1 + p1).to_affine();
        let circuit = ECTestCircuit {
            s,
            p1,
            p2,
            p3,
            p4,
            p5,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }

    // error case: double not equal
    {
        let p4 = (p1 + p2).to_affine();
        let circuit = ECTestCircuit {
            s,
            p1,
            p2,
            p3,
            p4,
            p5,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert!(prover.verify().is_err());
    }
}
}