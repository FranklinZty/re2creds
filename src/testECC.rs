
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
    use halo2_proofs::halo2curves::grumpkin::Fq;
    use halo2_proofs::halo2curves::grumpkin::Fr;
    use halo2_proofs::halo2curves::grumpkin::G1Affine;
    use halo2_proofs::halo2curves::grumpkin::G1;
    use halo2_native_ecc::ECChip;
    use halo2_native_ecc::ECConfig;
    use halo2_native_ecc::NativeECOps;
    use halo2_native_ecc::ArithOps;
    use std::time::{Duration,Instant};
    use halo2_proofs::{
        circuit::{Value},
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
    use halo2_proofs::halo2curves::bn256::{G1Affine as BNG1Affine,Bn256};
    use rand::rngs::OsRng;

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
                    // {
                    //     let p1 = ec_chip.load_private_point_unchecked(
                    //         &mut region,
                    //         &config,
                    //         &self.p1,
                    //         &mut offset,
                    //     )?;
                    //     let p2 = ec_chip.load_private_point_unchecked(
                    //         &mut region,
                    //         &config,
                    //         &self.p2,
                    //         &mut offset,
                    //     )?;
                    //     let bit = ec_chip.load_private_field(
                    //         &mut region,
                    //         &config,
                    //         &Fq::from(1),
                    //         &mut offset,
                    //     )?;
                    //     let p3_rec = ec_chip.conditional_point_add(
                    //         &mut region,
                    //         &config,
                    //         &p1,
                    //         &p2,
                    //         &bit,
                    //         &mut offset,
                    //     )?;

                    //     region.constrain_equal(p3.x.cell(), p3_rec.x.cell())?;
                    //     region.constrain_equal(p3.y.cell(), p3_rec.y.cell())?;
                    // }

                    // // unit test: point addition with 0
                    // {
                    //     let p1 = ec_chip.load_private_point_unchecked(
                    //         &mut region,
                    //         &config,
                    //         &self.p1,
                    //         &mut offset,
                    //     )?;
                    //     let p2 = ec_chip.load_private_point_unchecked(
                    //         &mut region,
                    //         &config,
                    //         &self.p2,
                    //         &mut offset,
                    //     )?;
                    //     let bit = ec_chip.load_private_field(
                    //         &mut region,
                    //         &config,
                    //         &Fq::from(0),
                    //         &mut offset,
                    //     )?;
                    //     let p3_rec = ec_chip.conditional_point_add(
                    //         &mut region,
                    //         &config,
                    //         &p1,
                    //         &p2,
                    //         &bit,
                    //         &mut offset,
                    //     )?;

                    //     region.constrain_equal(p1.x.cell(), p3_rec.x.cell())?;
                    //     region.constrain_equal(p1.y.cell(), p3_rec.y.cell())?;
                    // }

                    // // unit test: point doubling
                    // {
                    //     let p1 = ec_chip.load_private_point_unchecked(
                    //         &mut region,
                    //         &config,
                    //         &self.p1,
                    //         &mut offset,
                    //     )?;
                    //     let p4_rec = ec_chip.point_double(&mut region, &config, &p1, &mut offset)?;

                    //     region.constrain_equal(p4.x.cell(), p4_rec.x.cell())?;
                    //     region.constrain_equal(p4.y.cell(), p4_rec.y.cell())?;
                    // }

                    // // unit test: scalar decomposition
                    // {
                    //     let start = offset;
                    //     let _scalar_cells =
                    //         ec_chip.decompose_scalar(&mut region, &config, &self.s, &mut offset)?;
                    //     println!("scalar decompose uses {} rows", offset - start);
                    // }

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
            let params = ParamsKZG::<Bn256>::setup(k, &mut OsRng);
            let verifier_params = params.verifier_params();
            let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
            println!("finish keygen_vk");
            let vk2 = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
            println!("finish keygen_vk2");
            let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
            println!("finish keygen_pk");
            let mut rng = OsRng;
            let mut transcript = Blake2bWrite::<_, BNG1Affine, Challenge255<_>>::init(vec![]);
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

            assert!(verify_proof::<KZGCommitmentScheme<Bn256>, VerifierSHPLONK<Bn256>, _, _, _>(
                &verifier_params,
                &vk2,
                strategy,
                &[&[]],
                &mut verifier_transcript,
            ).is_ok());
        }
    }
}