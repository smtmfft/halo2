use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
    poly::Rotation,
};
use pairing::bn256::Fr as Fp;

#[test]
fn lookup_any() {
    #[derive(Clone, Debug)]
    struct MyConfig<F: FieldExt> {
        input: Column<Advice>,
        // Selector to enable lookups on even numbers.
        q_even: Selector,
        // Use an advice column as the lookup table column for even numbers.
        table_even: Column<Advice>,
        // input for xor
        xor_inputs: [Column<Advice>; 3],
        // Selector to enable lookups on odd numbers.
        q_xor: Selector,
        // Use an instance column as the lookup table column for odd numbers.
        table_xor: [Column<Instance>; 3],
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> MyConfig<F> {
        fn configure(meta: &mut ConstraintSystem<F>) -> Self {
            let config = Self {
                input: meta.advice_column(),
                q_even: meta.complex_selector(),
                table_even: meta.advice_column(),
                xor_inputs: [(); 3].map(|_| meta.advice_column()),
                q_xor: meta.complex_selector(),
                table_xor: [(); 3].map(|_| meta.instance_column()),
                _marker: PhantomData,
            };

            // Lookup on even numbers
            meta.lookup_any("even number", |meta| {
                let input = meta.query_advice(config.input, Rotation::cur());

                let q_even = meta.query_selector(config.q_even);
                let table_even = meta.query_advice(config.table_even, Rotation::cur());

                vec![(q_even * input, table_even)]
            });

            // Lookup on odd numbers
            meta.lookup_any("xor table", |meta| {
              let mut table_map = vec![];
              let q_xor = meta.query_selector(config.q_xor);

              let inputa = meta.query_advice(config.xor_inputs[0], Rotation::cur());
              let tablea = meta.query_instance(config.table_xor[0], Rotation::cur());
              table_map.push((q_xor.clone()*inputa, tablea));

              let inputb = meta.query_advice(config.xor_inputs[1], Rotation::cur());
              let tableb = meta.query_instance(config.table_xor[1], Rotation::cur());
              table_map.push((q_xor.clone()*inputb, tableb));

              let out = meta.query_advice(config.xor_inputs[2], Rotation::cur());
              let tableo = meta.query_instance(config.table_xor[2], Rotation::cur());
              table_map.push((q_xor.clone()*out, tableo));

              table_map
            });

            config
        }

        fn witness_even(
            &self,
            mut layouter: impl Layouter<F>,
            value: Option<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "witness even number",
                |mut region| {
                    // Enable the even lookup.
                    self.q_even.enable(&mut region, 0)?;

                    region.assign_advice(
                        || "even input",
                        self.input,
                        0,
                        || value.ok_or(Error::Synthesis),
                    )?;
                    Ok(())
                },
            )
        }

        fn witness_xor(
            &self,
            mut layouter: impl Layouter<F>,
            values: &[(Option<F>, Option<F>, Option<F>)],
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "witness xor op",
                |mut region| {
                    for (offset, (a, b, o)) in values.iter().enumerate() {
                      self.q_xor.enable(&mut region, offset)?;
                      region.assign_advice(
                          || "xor input a",
                          self.xor_inputs[0],
                          offset,
                          || a.ok_or(Error::Synthesis),
                      )?;
                      region.assign_advice(
                        || "xor input b",
                        self.xor_inputs[1],
                        offset,
                        || b.ok_or(Error::Synthesis),
                      )?;
                      region.assign_advice(
                        || "xor output",
                        self.xor_inputs[2],
                        offset,
                        || o.ok_or(Error::Synthesis),
                      )?;
                    }
                    Ok(())
                },
            )
        }

        fn load_even_lookup(
            &self,
            mut layouter: impl Layouter<F>,
            values: &[F],
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "load values for even lookup table",
                |mut region| {
                    for (offset, value) in values.iter().enumerate() {
                        region.assign_advice(
                            || "even table value",
                            self.table_even,
                            offset,
                            || Ok(*value),
                        )?;
                    }

                    Ok(())
                },
            )
        }
    }

    #[derive(Default)]
    struct MyCircuit<F: FieldExt> {
        even_lookup: Vec<F>,
        even_witnesses: Vec<Option<F>>,
        xor_witnesses: Vec<(Option<F>, Option<F>, Option<F>)>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        // Since we are using a single chip for everything, we can just reuse its config.
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Self::Config::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // Load allowed values for even lookup table
            config.load_even_lookup(
                layouter.namespace(|| "witness even numbers"),
                &self.even_lookup,
            )?;

            // Witness even numbers
            for even in self.even_witnesses.iter() {
                config.witness_even(layouter.namespace(|| "witness even numbers"), *even)?;
            }

            config.witness_xor(layouter.namespace(|| "witness xor numbers"), &self.xor_witnesses)?;

            Ok(())
        }
    }

    // Run MockProver.
    let k = 4;

    // Prepare the private and public inputs to the circuit.
    let even_lookup = vec![
        Fp::from(0),
        Fp::from(2),
        Fp::from(4),
        Fp::from(6),
        Fp::from(8),
    ];
    let xor_witnesses = vec![
      (Some(Fp::from(1)), Some(Fp::from(0)), Some(Fp::from(1))),
    ];
    let even_witnesses = vec![Some(Fp::from(0)), Some(Fp::from(2)), Some(Fp::from(4))];

    // Instantiate the circuit with the private inputs.
    let circuit = MyCircuit {
      even_lookup: even_lookup.clone(),
      even_witnesses,
      xor_witnesses,
    };

    fn transpose2<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
      assert!(!v.is_empty());
      let len = v[0].len();
      let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
      (0..len)
          .map(|_| {
              iters
                  .iter_mut()
                  .map(|n| n.next().unwrap())
                  .collect::<Vec<T>>()
          })
          .collect()
    }

    let xor_witnesses_table = transpose2(vec![
      vec!(Fp::from(0), Fp::from(0), Fp::from(0)),
      vec!(Fp::from(0), Fp::from(1), Fp::from(1)),
      vec!(Fp::from(1), Fp::from(0), Fp::from(1)),
      vec!(Fp::from(1), Fp::from(1), Fp::from(0)),
    ]);

    // Given the correct public input, our circuit will verify.
    let prover = MockProver::run(k, &circuit, xor_witnesses_table).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // // If we pass in a public input containing only even numbers,
    // // the odd number lookup will fail.
    let wrong_xor_witnesses = vec![vec![Fp::from(1)], vec![Fp::from(1)], vec![Fp::from(1)]];
    let prover = MockProver::run(k, &circuit, wrong_xor_witnesses).unwrap();
    assert!(prover.verify().is_err())
}
