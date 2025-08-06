use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};




#[derive(Debug, Clone)]
struct CircuitConfig {
    advice: [Column<Advice>; 2],
    instance: Column<Instance>,
    s_mul: Selector,
}

#[derive(Clone)]
struct Number<F: Field>(AssignedCell<F, F>);

#[derive(Default)]
struct MyCircuit<F: Field> {
    c: F,
    a: Value<F>,
    b: Value<F>,
}

fn load_private<F: Field>(
    config: &CircuitConfig,
    mut layouter: impl Layouter<F>,
    value: Value<F>,
) -> Result<Number<F>, Error> {
    layouter.assign_region(
        || "load private",
        |mut region| {
            region
                .assign_advice(|| "private input", config.advice[0], 0, || value)
                .map(Number)
        },
    )
}

fn load_constant<F: Field>(
    config: &CircuitConfig,
    mut layouter: impl Layouter<F>,
    c: F,
) -> Result<Number<F>, Error> {
    layouter.assign_region(
        || "load private",
        |mut region| {
            region
                .assign_advice_from_constant(|| "private input", config.advice[0], 0, c)
                .map(Number)
        },
    )
}

fn mul<F: Field>(
    config: &CircuitConfig,
    mut layouter: impl Layouter<F>,
    a: Number<F>,
    b: Number<F>,
) -> Result<Number<F>, Error> {
    layouter.assign_region(
        || "mul",
        |mut region| {
            config.s_mul.enable(&mut region, 0)?;
            a.0.copy_advice(|| "lhs", &mut region, config.advice[0], 0)?;
            b.0.copy_advice(|| "rhs", &mut region, config.advice[1], 0)?;

            let value = a.0.value().copied() * b.0.value().copied();
            region
                .assign_advice(|| "out=lhs*rhs", config.advice[0], 1, || value)
                .map(Number)
        },
    )
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = CircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column()];
        let instance = meta.instance_column();
        let constant = meta.fixed_column();

        meta.enable_equality(instance);
        meta.enable_constant(constant);

        for c in &advice {
            meta.enable_equality(*c);
        }
        let s_mul = meta.selector();

        /* Gate design:
              | a0  |  a1 | s_mul |
              | ----|-----|-------|
              | lhs | rhs | s_mul |
              | out |     |       |
        */
        meta.create_gate("mul_gate", |meta| {
            let lhs = meta.query_advice(advice[0], Rotation::cur());
            let rhs = meta.query_advice(advice[1], Rotation::cur());
            let out = meta.query_advice(advice[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            vec![s_mul * (lhs * rhs - out)]
        });

        CircuitConfig {
            advice,
            instance,
            s_mul,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let a = load_private(&config, layouter.namespace(|| "load a"), self.a)?;
        let b = load_private(&config, layouter.namespace(|| "load b"), self.b)?;
        let c = load_constant(&config, layouter.namespace(|| "load c"), self.c)?;

        let ab = mul(&config, layouter.namespace(|| "a*b"), a, b)?;
        let absq = mul(&config, layouter.namespace(|| "ab*ab"), ab.clone(), ab)?;
        let out = mul(&config, layouter.namespace(|| "absq*c"), absq, c)?;

        //expose public
        layouter
            .namespace(|| "expose out")
            .constrain_instance(out.0.cell(), config.instance, 0)
    }
}

mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver};
    use halo2_proofs::{
        circuit::{Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof
        },
        poly::{
            commitment::ParamsProver,
            ipa::{
                commitment::{IPACommitmentScheme, ParamsIPA},
                multiopen::ProverIPA,
                strategy::SingleStrategy,
            },
            VerificationStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
    };
    use halo2curves::pasta::{vesta, EqAffine, Fp};

    use criterion::{criterion_group, criterion_main, Criterion};
    use rand::rngs::OsRng;
    #[test]
    pub fn test_sample() {
        // ANCHOR: test-circuit
        // The number of rows in our circuit cannot exceed 2^k. Since our example
        // circuit is very small, we can pick a very small value here.
        let k = 5;

        // Prepare the private and public inputs to the circuit!
        let c = Fp::from(1);
        let a = Fp::from(2);
        let b = Fp::from(3);
        let out = c * a.square() * b.square();
        println!("out=:{:?}", out);

        // Instantiate the circuit with the private inputs.
        let circuit = MyCircuit {
            c,
            a: Value::known(a),
            b: Value::known(b),
        };

        // Arrange the public input. We expose the multiplication result in row 0
        // of the instance column, so we position it there in our public inputs.
        let mut public_inputs = vec![out];

        // Given the correct public input, our circuit will verify.
        let prover = MockProver::run(k, &circuit, vec![public_inputs.clone()]).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        // If we try some other public input, the proof will fail!
        let mut public_inputs_fail = public_inputs.clone();
        public_inputs_fail[0] += Fp::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs_fail]).unwrap();
        assert!(prover.verify().is_err());
        println!("\n\n\n!!!!!OHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH!!!!!\n     simple example success !\n!!!!!OHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHH!!!!!\n\n\n");
        // ANCHOR_END: test-circuit
        let params: ParamsIPA<vesta::Affine> = ParamsIPA::new(k);
        let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
        let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
        let prover_name = format!("MT-prover");
        let verifier_name = format!("MT-verifier");
        let mut rng = OsRng;
        let mut transcript = Blake2bWrite::<_, EqAffine, Challenge255<_>>::init(vec![]);
        create_proof::<IPACommitmentScheme<_>, ProverIPA<_>, _, _, _, _>(
                &params,
                &pk,
                &[circuit],
                &[&[&public_inputs]],
                &mut rng,
                &mut transcript,
            )
            .expect("proof generation should not fail");
        let proof = transcript.finalize();
        println!("proof length: {}", proof.len());
        let strategy = SingleStrategy::new(&params);
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
            assert!(verify_proof(
                &params,
                pk.get_vk(),
                strategy,
                &[&[&public_inputs]],
                &mut transcript
            )
            .is_ok());
    }
}



