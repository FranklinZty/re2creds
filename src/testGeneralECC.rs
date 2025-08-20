const NUMBER_OF_LIMBS: usize = 4;
const BIT_LEN_LIMB: usize = 68;
use std::marker::PhantomData;
use integer::Range;
use integer::{IntegerChip, IntegerInstructions, UnassignedInteger};
use ecc::{AssignedPoint, EccConfig, GeneralEccChip, Point};
use ff::{PrimeField,FromUniformBytes};
use halo2_proofs::circuit::Layouter;
use halo2_proofs::circuit::SimpleFloorPlanner;
use halo2_proofs::circuit::Value;
use halo2_proofs::plonk::Circuit;
use halo2_proofs::plonk::ConstraintSystem;
use pasta_curves::arithmetic::CurveAffine;
use maingate::{MainGate, RangeInstructions};
use maingate::MainGateConfig;
use maingate::RangeChip;
use maingate::RangeConfig;
use halo2_proofs::plonk::Error;
use maingate::RegionCtx;
use maingate::mock_prover_verify;
use rand_core::OsRng;
use ecc::integer::rns::{Integer, Rns};
use halo2_proofs::halo2curves::pasta::{
        EpAffine as Pallas, EqAffine as Vesta, Fp as PastaFp, Fq as PastaFq,
    };
use halo2_proofs::halo2curves::bn256::{Fr as BnScalar, G1Affine as Bn256};
use halo2_proofs::halo2curves::{
        ff::{Field},
        group::{prime::PrimeCurveAffine, Curve as _, Group},
    };



#[derive(Clone, Debug)]
    struct TestCircuitConfig {
        pub main_gate_config: MainGateConfig,
        pub range_config: RangeConfig,
    }

    impl TestCircuitConfig {
        fn ecc_chip_config(&self) -> EccConfig {
            EccConfig {
                range_config: self.range_config.clone(),
                main_gate_config: self.main_gate_config.clone(),
            }
        }
    }

    impl TestCircuitConfig {
        fn new<
            C: CurveAffine,
            N: PrimeField,
            const NUMBER_OF_LIMBS: usize,
            const BIT_LEN_LIMB: usize,
        >(
            meta: &mut ConstraintSystem<N>,
        ) -> Self {
            let (rns_base, rns_scalar) =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();

            let main_gate_config = MainGate::<N>::configure(meta);
            let mut overflow_bit_lens: Vec<usize> = vec![];
            overflow_bit_lens.extend(rns_base.overflow_lengths());
            overflow_bit_lens.extend(rns_scalar.overflow_lengths());
            let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

            let range_config = RangeChip::<N>::configure(
                meta,
                &main_gate_config,
                composition_bit_lens,
                overflow_bit_lens,
            );

            TestCircuitConfig {
                main_gate_config,
                range_config,
            }
        }

        fn config_range<N: PrimeField>(
            &self,
            layouter: &mut impl Layouter<N>,
        ) -> Result<(), Error> {
            let range_chip = RangeChip::<N>::new(self.range_config.clone());
            range_chip.load_table(layouter)?;

            Ok(())
        }
    }

    #[derive(Default, Clone, Debug)]
    struct TestEccMul<
        C: CurveAffine,
        N: PrimeField,
        const NUMBER_OF_LIMBS: usize,
        const BIT_LEN_LIMB: usize,
    > {
        window_size: usize,
        aux_generator: C,
        _marker: PhantomData<N>,
    }

    impl<
            C: CurveAffine,
            N: PrimeField,
            const NUMBER_OF_LIMBS: usize,
            const BIT_LEN_LIMB: usize,
        > Circuit<N> for TestEccMul<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
    {
        type Config = TestCircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;
        // #[cfg(feature = "circuit-params")]
        // type Params = ();

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
            TestCircuitConfig::new::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<N>,
        ) -> Result<(), Error> {
            let ecc_chip_config = config.ecc_chip_config();
            let mut ecc_chip =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(ecc_chip_config);

            layouter.assign_region(
                || "assign aux values",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);
                    ecc_chip.assign_aux_generator(ctx, Value::known(self.aux_generator))?;
                    ecc_chip.assign_aux(ctx, self.window_size, 1)?;
                    ecc_chip.get_mul_aux(self.window_size, 1)?;
                    Ok(())
                },
            )?;

            let scalar_chip = ecc_chip.scalar_field_chip();

            layouter.assign_region(
                || "region mul",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let base = C::Curve::random(OsRng);
                    let s = C::Scalar::random(OsRng);
                    let result = base * s;

                    let s = Integer::from_fe(s, ecc_chip.rns_scalar());
                    let base = ecc_chip.assign_point(ctx, Value::known(base.into()))?;
                    let s = scalar_chip.assign_integer(
                        ctx,
                        Value::known(s).into(),
                        Range::Remainder,
                    )?;
                    let result_0 = ecc_chip.assign_point(ctx, Value::known(result.into()))?;

                    let result_1 = ecc_chip.mul(ctx, &base, &s, self.window_size)?;
                    ecc_chip.assert_equal(ctx, &result_0, &result_1)?;

                    Ok(())
                },
            )?;

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_general_ecc_mul_circuit() {
        fn run<
            C: CurveAffine,
            N: FromUniformBytes<64> + Ord,
            const NUMBER_OF_LIMBS: usize,
            const BIT_LEN_LIMB: usize,
        >() {
            for window_size in 1..2 {
                let aux_generator = C::Curve::random(OsRng).to_affine();

                let circuit = TestEccMul::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
                    aux_generator,
                    window_size,
                    ..Default::default()
                };
                let instance = vec![vec![]];
                mock_prover_verify(&circuit, instance);
            }
        }

        run::<Pallas, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Pallas, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Pallas, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();

        // run::<Vesta, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Vesta, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Vesta, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();

        // run::<Bn256, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Bn256, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Bn256, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();

        // run::<Secp256k1, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Secp256k1, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        // run::<Secp256k1, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    }