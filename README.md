`cyclegg` is a theorem prover for equational reasoning.
It is based on the ideas from [CycleQ](https://github.com/ec-jones/cycleq)
but implements them on top of egraphs and equality saturation in order to avoid backtracking proof search.

To prove commutativity of addition, run:
```
cargo run -- examples/add.ceg
```

### TODO

#### Organizational
- Add flag for grounding
- Add flag for each proof mode (cyclic, non-cyclic, both)
- Create goals inside parser, do not expose RawGoal
- Decouple proof generation from proof search (e.g. put Defs, Proof term somewhere else)
- Make partial applications without $ work
- Move from SymbolLang to a proper language.
    - See babble for inspiration (https://github.com/dcao/babble/blob/main/src/ast_node.rs)
- Emit a proof data structure
    - Right now we just emit strings that are (mostly) valid LiquidHaskell.
    - Creating a proper equational proof data structure would allow us to emit to other backends.
    - It would also be cleaner.

#### Search
- Canonical forms for termination checking:
    - Extend constructor analysis to keep track of variables, add a canonical form extractor
    - In SmallerVars check: compare canonical forms of the old and new parameter and require that the old one has the new one wrapped in a constructor
    - For grounding: at every split, replace the var being split with the smaller var in all prev_instantiations
        (store prev_instantiations in terms of eclasses so that we can get their canonical forms)
- Blocking variables analysis

#### Proofs
- Conditional props proof generation
    - Add explanation for conditional unions (cannot just `union_trusted`).
    - Include the premise into the LH precondition
        - This can be accomplished by taking a witness of the precondition as an argument.
    - How to include the proof of the condition holding?
        - To use a conditional lemma you need a witness of the condition. We can take the e-graph from
          which we are getting the explanation and ask it to explain why the e-classes of the condition
          are equal and use those to build a proof. In LH this would look something like
          
          ```haskell
          let conditionWitness =   condLHS 
                               ==. condLHS'
                               ? lemma lemmaArgs
                               ==. condRHS
                               *** QED
           in conditionalLemma conditionWitness args
          ```

# Comparison to CycleQ

Results generated from a282086 using the command (prop52 removed because its
proof was made easier by a bug)

``` shell
cargo run --release -- examples/cycleq.ceg -t 10 --save-results
```

and compared to results from CycleQ.

All results come from runs on a Macbook Air M2.

N.B. We have cyclic proofs for prop_30 (49ms) and prop_73 (5364ms) but not with
uncyclegg but these are believed unsound.

N.B. The cyclegg timing is a little suspect (e.g. I time `prop_56` as taking
201ms instead of 5000 ms using cyclegg).

| Name    | Cycleq result | Uncyclegg result | Cycleq time (ms) | Cyclegg time (ms) | Uncyclegg time (ms) |
| ------- | ---------------- | ------------- | ---------------- | ----------------- | ------------------- |
| prop_01 | Valid            |   Valid       |            0.673 |            0.837… |              0.589… |
| prop_02 | Unknown          | Valid         |           -1.000 |            7.748… |              1.684… |
| prop_03 | Unknown          | Valid         |           -1.000 |            3.529… |              2.117… |
| prop_04 | Unknown          | Valid         |           -1.000 |            3.090… |              1.654… |
| prop_06 | Valid            |   Valid       |            0.134 |            0.202… |              0.142… |
| prop_07 | Valid            |   Valid       |            0.210 |            0.191… |              0.142… |
| prop_08 | Valid            |   Valid       |            1.270 |            0.237… |              0.166… |
| prop_09 | Valid            |   Valid       |            0.641 |            0.783… |              0.350… |
| prop_10 | Valid            |   Valid       |            0.079 |            0.141… |              0.108… |
| prop_11 | Valid            |   Valid       |            0.014 |            0.029… |              0.025… |
| prop_12 | Valid            |   Valid       |            1.007 |            0.504… |              0.343… |
| prop_13 | Valid            |   Valid       |            0.047 |            0.034… |              0.029… |
| prop_14 | Unknown          | Valid         |           -1.000 |            1.963… |              0.400… |
| prop_15 | Unknown          | Valid         |           -1.000 |            2.072… |              1.029… |
| prop_17 | Valid            |   Valid       |            0.051 |            0.151… |              0.120… |
| prop_18 | Valid            |   Valid       |            0.163 |            0.170… |              0.126… |
| prop_19 | Valid            |   Valid       |            0.847 |            0.480… |              0.333… |
| prop_21 | Valid            |   Valid       |            0.143 |            0.170… |              0.123… |
| prop_22 | Valid            |   Valid       |            1.591 |            1.110… |              0.593… |
| prop_23 | Valid            |   Valid       |            1.104 |            0.422… |              0.212… |
| prop_24 | Valid            |   Valid       |            1.445 |            1.146… |              0.442… |
| prop_25 | Valid            |   Valid       |            0.640 |            0.716… |              0.430… |
| prop_28 | Unknown          | Valid         |           -1.000 |            2.503… |              0.995… |
| prop_29 | Unknown          | Valid         |           -1.000 |            4.213… |              2.262… |
| prop_31 | Valid            |   Valid       |            1.352 |            1.210… |              0.586… |
| prop_32 | Valid            |   Valid       |            1.071 |            0.452… |              0.202… |
| prop_33 | Valid            |   Valid       |            0.427 |            0.417… |              0.271… |
| prop_34 | Valid            |   Valid       |            0.709 |            0.524… |              0.351… |
| prop_35 | Valid            |   Valid       |            0.059 |            0.319… |              0.126… |
| prop_36 | Valid            |   Valid       |            0.188 |            0.332… |              0.125… |
| prop_37 | Unknown          | Valid         |           -1.000 |            1.310… |              1.402… |
| prop_38 | Unknown          | Valid         |           -1.000 |            6.999… |              1.343… |
| prop_39 | Unknown          | Valid         |           -1.000 |            2.048… |              0.250… |
| prop_40 | Valid            |   Valid       |            0.014 |            0.024… |              0.020… |
| prop_41 | Valid            |   Valid       |            0.978 |            0.476… |              0.280… |
| prop_42 | Valid            |   Valid       |            0.067 |            0.029… |              0.025… |
| prop_43 | Unknown          | Valid         |           -1.000 |            0.593… |              0.306… |
| prop_44 | Valid            |   Valid       |            0.193 |            0.552… |              0.420… |
| prop_45 | Valid            |   Valid       |            0.101 |            0.032… |              0.027… |
| prop_46 | Valid            |   Valid       |            0.020 |            0.021… |              0.018… |
| prop_49 | Valid            |   Valid       |          231.569 |            2.492… |              1.021… |
| prop_50 | Valid            |   Valid       |           21.207 |            0.796… |              0.425… |
| prop_51 | Valid            |   Valid       |            1.855 |            0.453… |              0.459… |
| prop_55 | Valid            |   Valid       |            1.516 |            0.631… |              0.381… |
| prop_56 | Valid            |   Valid       |        1,615.585 |        5,194.048… |             12.648… |
| prop_57 | Valid            |   Valid       |           35.090 |            3.122… |              4.161… |
| prop_58 | Valid            |   Valid       |            3.633 |            0.910… |              0.651… |
| prop_61 | Valid            |   Valid       |          163.463 |            2.073… |              0.874… |
| prop_64 | Valid            |   Valid       |            0.660 |            0.413… |              0.393… |
| prop_67 | Valid            |   Valid       |            1.045 |            0.653… |              0.366… |
| prop_75 | Unknown          | Valid         |           -1.000 |        2,770.103… |             17.077… |
| prop_79 | Valid            |   Valid       |          507.399 |            1.054… |              0.284… |
| prop_80 | Valid            |   Valid       |            1.082 |            0.682… |              0.415… |
| prop_82 | Valid            |   Valid       |            2.437 |            1.176… |              0.726… |
| prop_83 | Valid            |   Valid       |            2.687 |            7.345… |              1.645… |
| prop_84 | Valid            |   Valid       |            7.110 |            1.412… |              0.847… |
| prop_86 | Unknown          | Valid         |           -1.000 |            0.768… |              0.219… |
| prop_87 | Unknown          | Valid         |           -1.000 |            1.698… |              0.398… |
| prop_88 | Unknown          | Valid         |           -1.000 |            1.157… |              0.405… |
| prop_89 | Unknown          | Valid         |           -1.000 |            1.606… |              0.360… |
| prop_90 | Unknown          | Valid         |           -1.000 |            0.630… |              0.312… |
