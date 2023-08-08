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
- 59 proofs passing.

Among the 3 failing proofs:

- 1 fails due to termination checking
- 2 fails due to totality errors

## Unfixed proofs

### Termination error

- Prop52NoCyclic.hs
  * Termination error
  * Tried to fix using list sum metric.
  * Commented out the function and replaced with `undefined`

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
- Prop86NoCyclic.hs
  * Added measure to ensure termination of mutually recursive functions.
- Prop87NoCyclic.hs
  * Fixed syntax errors in the proposition (probably some kind of error with how
    `$` is handled)
  * Added measure to ensure termination of mutually recursive functions.
- Prop88NoCyclic.hs
  * Fixed syntax errors in the proposition (probably some kind of error with how
    `$` is handled)
  * Added measure to ensure termination of mutually recursive functions.
- Prop89NoCyclic.hs
  * Fixed syntax errors in the proposition (probably some kind of error with how
    `$` is handled)
  * Added measure to ensure termination of mutually recursive functions.
- Prop90NoCyclic.hs
  * Added measure to ensure termination of mutually recursive functions.

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
