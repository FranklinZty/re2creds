mod tests {
    use std::marker::PhantomData;
    use std::rc::Rc;
    use std::time::{Duration,Instant};
    use ecc::{AssignedPoint, EccConfig, GeneralEccChip, Point};
    use ecc::halo2;
    use ecc::halo2::halo2curves::{
        ff::{Field, FromUniformBytes, PrimeField},
        group::{prime::PrimeCurveAffine, Curve as _, Group},
    };
    use group::Curve;
    use halo2curves::pairing::Engine;
    use integer::rns::Rns;
    use integer::NUMBER_OF_LOOKUP_LIMBS;
    use integer::{AssignedInteger, IntegerInstructions};
    use ecc::maingate;
    use halo2::arithmetic::CurveAffine;
    use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
    use halo2::plonk::{Circuit, ConstraintSystem, Error};
    use integer::rns::Integer;
    use integer::Range;
    use maingate::mock_prover_verify;
    use maingate::{
        MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions, RegionCtx,
    };
    use paste::paste;
    use rand_core::OsRng;

    use ecc::halo2::halo2curves::bn256::{Fr as BnScalar, G1Affine as Bn256};
    use ecc::halo2::halo2curves::pasta::{
        EpAffine as Pallas, EqAffine as Vesta, Fp as PastaFp, Fq as PastaFq,
    };
    use ecc::halo2::halo2curves::secp256k1::Secp256k1Affine as Secp256k1;

    use halo2_proofs::{
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof
        },
        poly::{
            commitment::ParamsProver,
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverSHPLONK,VerifierSHPLONK},
                strategy::SingleStrategy,
            },
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use halo2_proofs::halo2curves::bn256::{G1Affine as BNG1Affine};

    const NUMBER_OF_LIMBS: usize = 4;
    const BIT_LEN_LIMB: usize = 68;

    

    #[derive(Clone, Debug)]
    struct TestCircuitConfig {
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
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

    #[derive(Clone, Debug, Default)]
    struct TestEccAddition<
        C: CurveAffine,
        N: PrimeField,
        const NUMBER_OF_LIMBS: usize,
        const BIT_LEN_LIMB: usize,
    > {
        _marker: PhantomData<(C, N)>,
    }

    impl<
            C: CurveAffine,
            N: PrimeField,
            const NUMBER_OF_LIMBS: usize,
            const BIT_LEN_LIMB: usize,
        > Circuit<N> for TestEccAddition<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
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
            let ecc_chip =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(ecc_chip_config);
            layouter.assign_region(
                || "region 0",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let a = C::Curve::random(OsRng);
                    let b = C::Curve::random(OsRng);

                    let c = a + b;
                    let a = &ecc_chip.assign_point(ctx, Value::known(a.into()))?;
                    let b = &ecc_chip.assign_point(ctx, Value::known(b.into()))?;
                    let c_0 = &ecc_chip.assign_point(ctx, Value::known(c.into()))?;
                    let c_1 = &ecc_chip.add(ctx, a, b)?;
                    ecc_chip.assert_equal(ctx, c_0, c_1)?;

                    let c_1 = &ecc_chip.add(ctx, a, b)?;
                    ecc_chip.assert_equal(ctx, c_0, c_1)?;

                    // test doubling

                    let a = C::Curve::random(OsRng);
                    let c = a + a;

                    let a = &ecc_chip.assign_point(ctx, Value::known(a.into()))?;
                    let c_0 = &ecc_chip.assign_point(ctx, Value::known(c.into()))?;
                    let c_1 = &ecc_chip.double(ctx, a)?;
                    ecc_chip.assert_equal(ctx, c_0, c_1)?;

                    // test ladder

                    let a = C::Curve::random(OsRng);
                    let b = C::Curve::random(OsRng);
                    let c = a + b + a;

                    let a = &ecc_chip.assign_point(ctx, Value::known(a.into()))?;
                    let b = &ecc_chip.assign_point(ctx, Value::known(b.into()))?;
                    let c_0 = &ecc_chip.assign_point(ctx, Value::known(c.into()))?;
                    let c_1 = &ecc_chip.ladder(ctx, a, b)?;
                    ecc_chip.assert_equal(ctx, c_0, c_1)?;

                    Ok(())
                },
            )?;

            config.config_range(&mut layouter)?;

            Ok(())
        }
    }

    #[test]
    fn test_general_ecc_addition_circuit() {
        fn run<
            C: CurveAffine,
            N: FromUniformBytes<64> + Ord,
            const NUMBER_OF_LIMBS: usize,
            const BIT_LEN_LIMB: usize,
        >() {
            let circuit = TestEccAddition::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::default();
            let instance = vec![vec![]];
            mock_prover_verify(&circuit, instance);
        }

        run::<Pallas, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Pallas, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Pallas, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();

        run::<Vesta, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Vesta, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Vesta, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();

        run::<Bn256, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Bn256, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Bn256, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();

        run::<Secp256k1, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Secp256k1, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
        run::<Secp256k1, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    }

    #[derive(Default, Clone, Debug)]
    struct TestEccPublicInput<
        C: CurveAffine,
        N: PrimeField,
        const NUMBER_OF_LIMBS: usize,
        const BIT_LEN_LIMB: usize,
    > {
        a: Value<C>,
        b: Value<C>,
        _marker: PhantomData<N>,
    }

    impl<
            C: CurveAffine,
            N: PrimeField,
            const NUMBER_OF_LIMBS: usize,
            const BIT_LEN_LIMB: usize,
        > Circuit<N> for TestEccPublicInput<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
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
            let ecc_chip =
                GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(ecc_chip_config);

            let sum = layouter.assign_region(
                || "region 0",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let a = self.a;
                    let b = self.b;
                    let a = ecc_chip.assign_point(ctx, a)?;
                    let b = ecc_chip.assign_point(ctx, b)?;
                    let c = ecc_chip.add(ctx, &a, &b)?;
                    ecc_chip.normalize(ctx, &c)
                },
            )?;
            ecc_chip.expose_public(layouter.namespace(|| "sum"), sum, 0)?;

            let sum = layouter.assign_region(
                || "region 1",
                |region| {
                    let offset = 0;
                    let ctx = &mut RegionCtx::new(region, offset);

                    let a = self.a;
                    let a = ecc_chip.assign_point(ctx, a)?;
                    let c = ecc_chip.double(ctx, &a)?;
                    ecc_chip.normalize(ctx, &c)
                },
            )?;
            ecc_chip.expose_public(layouter.namespace(|| "sum"), sum, 8)?;

            config.config_range(&mut layouter)?;

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
                    // ecc_chip.get_mul_aux(self.window_size, 1)?;
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
        let window_size = 1;
        let aux_generator = halo2curves::pasta::Ep::random(OsRng).to_affine();
        let circuit = TestEccMul::<Pallas, halo2_proofs::halo2curves::bn256::Fr, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
                    aux_generator,
                    window_size,
                    ..Default::default()
                };
        let instance = vec![vec![]];
        mock_prover_verify(&circuit, instance);
        println!("TestEccMul circuit mock passed");
        let params = ParamsKZG::<halo2_proofs::halo2curves::bn256::Bn256>::setup(18, &mut OsRng);
        let verifier_params = params.verifier_params();
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        println!("finish keygen_vk");
        let vk2 = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        println!("finish keygen_vk2");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
        println!("finish keygen_pk");
        let mut rng = OsRng;
        let mut transcript = Blake2bWrite::<_, halo2_proofs::halo2curves::bn256::G1Affine, Challenge255<_>>::init(vec![]);
        let start_time= Instant::now();
        create_proof::<KZGCommitmentScheme<_>, ProverSHPLONK<_>, _, _, _, _>(
                &params,
                &pk,
                &[circuit],
                &[&[]],
                &mut rng,
                &mut transcript,
            )
            .expect("proof generation should not fail");
        let proof = transcript.finalize();
        println!("finish create_proof");
        let duration=start_time.elapsed();
        println!("proof generation time: {:?}", duration);
        println!("proof length: {}", proof.len());

        // Verify
        let mut verifier_transcript =
            Blake2bRead::<_, _, Challenge255<_>>::init(proof.as_slice());
        let strategy = SingleStrategy::new(&verifier_params);

        assert!(verify_proof::<KZGCommitmentScheme<halo2_proofs::halo2curves::bn256::Bn256>, VerifierSHPLONK<halo2_proofs::halo2curves::bn256::Bn256>, _, _, _>(
            &verifier_params,
            &vk2,
            strategy,
            &[&[]],
            &mut verifier_transcript,
        ).is_ok());
    }

}