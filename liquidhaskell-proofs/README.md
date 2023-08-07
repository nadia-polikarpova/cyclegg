# Cyclegg Proofs in LiquidHaskell

Mechanized proofs from Cyclegg translated to LiquidHaskell for automatic
verification.

Generated using

``` shell
cargo run --release -- examples/cycleq.ceg -e --proofs-directory=liquidhaskell-proofs/src -t 10
```

on 0a798f9.

Then the failing proofs were manually fixed.

## By the numbers:
- ~75 propositions total
- 62 propositions provable with proofs emitted.
- 53 proofs passing.

Among the 9 failing proofs:

- 3 fail due to termination checking
- 3 fail due to syntax errors
- 2 fail due to totality errors

## Unfixed proofs

### Termination error

- Prop52NoCyclic.hs
  * Termination error
  * Tried to fix using list sum metric.
  * Commented out the function and replaced with `undefined`
- Prop86NoCyclic.hs
  * `autosize` doesn't like mutual recursion in `mapT`.
  * Commented out everything below `mapT`.
- Prop90NoCyclic.hs
  * `autosize` doesn't like mutual recursion in `mapT`.
  * Commented out everything below `headE`.

### Syntax error
- Prop87NoCyclic.hs
  * Something funky's going on in the definition of the prop with parentheses.
  * Commented out everything below `mapT` since it would fail with termination
    anyway.
- Prop88NoCyclic.hs
  * Same as the above
- Prop89NoCyclic.hs
  * Same as the above

### Totality error
- Prop61NoCyclic.hs
  * `last` is not total.
  * Commented out everything below `last`.
- Prop64NoCyclic.hs
  * `last` is not total.
  * Commented out everything below `last`.

## Fixed proofs

- Prop06NoCyclic.hs
  * Add verbose proof on L66
- Prop09NoCyclic.hs
  * Add verbose proof on L77
- Prop14NoCyclic.hs
  * Fix `$` on L63 (needs parens)
- Prop23NoCyclic.hs
  * Add verbose proof on L71
- Prop24NoCyclic.hs
  * Add verbose proof on L94
- Prop29NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)
- Prop32NoCyclic.hs
  * Add verbose proof on L71
- Prop35NoCyclic.hs
  * Removed `($)` that LH can't parse on L57
- Prop36NoCyclic.hs
  * Removed `($)` that LH can't parse on L57
- Prop37NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)
- Prop40NoCyclic.hs
  * Typo in `cycleq.ceg`
- Prop44NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)
- Prop45NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)
- Prop43NoCyclic.hs
  * Fix `$` on L68 (needs parens)
- Prop55NoCyclic.hs
  * Add verbose proof on L97
- Prop57NoCyclic.hs
  * Fixed termination error by replacing `(Cyclegg_S cyclegg_m_140_450)` with
    `cyclegg_m_140` on L101 (the two terms are equal from a case split)
- Prop79NoCyclic.hs
  * Add verbose proof on L65
- Prop80NoCyclic.hs
  * Add verbose proof on L98
- Prop82NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)
- Prop83NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)
- Prop84NoCyclic.hs
  * Commented out `autosize` (see section on `Unknown func-sort`)

### `Unknown func-sort` error

Example
```
    Unknown func-sort: (Prop29NoCyclic.Cyclegg_List Int) : Int for (apply : func(0 , [(Prop29NoCyclic.Cyclegg_List @(1198));
                    int])) (autolen : func(0 , [(Prop29NoCyclic.Cyclegg_List @(1198));
                                                int])) (Prop29NoCyclic.Cyclegg_Nil : (Prop29NoCyclic.Cyclegg_List @(1198)))
```

Seems to be caused by some sort of weird interaction caused by `autosize`. It
might be that `autosize` can't function on polymorphic datatypes like `List a`
since the size of `a` is indeterminate?
