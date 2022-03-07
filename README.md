`cyclegg` is a theorem prover for equational reasoning.
It is based on the ideas from [CycleQ](https://github.com/ec-jones/cycleq)
but implements them on top of egraphs and equality saturation in order to avoid backtracking proof search.

### TODO

- Create lemmas that can match on all variables, not just next scrutinee
- Implement fancier termination checking
- Try abducing lemmas by finding "almost matches" for current lemmas, and trying to prove that they are equivalent