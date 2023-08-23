{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_07_no_cyclic: (cyclegg_sub (cyclegg_add cyclegg_n cyclegg_m) cyclegg_n) = cyclegg_m
module Prop07NoCyclic where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

{-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

{-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ prop_07_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> { (cyclegg_sub (cyclegg_add cyclegg_n cyclegg_m) cyclegg_n) = cyclegg_m } @-}
prop_07_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
prop_07_no_cyclic cyclegg_n cyclegg_m =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_40) ->
      -- prop_07_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_40) =>
      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
      -- prop_07_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_40) =>
      -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
      prop_07_no_cyclic cyclegg_n_40 cyclegg_m
      -- ih-equality-cyclegg_n=cyclegg_n_40,cyclegg_m=cyclegg_m =>
    (Cyclegg_Z ) ->
      -- prop_07_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_sub ?x Cyclegg_Z) =>
      -- prop_07_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_add Cyclegg_Z ?y) =>
      ()

