`cyclegg` is a theorem prover for equational reasoning.
It is based on the ideas from [CycleQ](https://github.com/ec-jones/cycleq)
but implements them on top of egraphs and equality saturation in order to avoid backtracking proof search.

### TODO

- prop_61: why cannot prove with List Nat?
- Detect vacuous goals from condition splitting
- Logging: how to print out which lemma we are applying?
- Implement fancier termination checking
- Try abducing lemmas by finding "almost matches" for current lemmas, and trying to prove that they are equivalent