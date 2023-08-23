{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_17_no_cyclic: (cyclegg_leq cyclegg_n Cyclegg_Z) = (cyclegg_eq cyclegg_n Cyclegg_Z)
module Prop17NoCyclic where
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

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_leq @-}
cyclegg_leq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_leq Cyclegg_Z y = Cyclegg_True
cyclegg_leq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_leq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_leq x y)

{-@ prop_17_no_cyclic :: cyclegg_n: Cyclegg_Nat -> { (cyclegg_leq cyclegg_n Cyclegg_Z) = (cyclegg_eq cyclegg_n Cyclegg_Z) } @-}
prop_17_no_cyclic :: Cyclegg_Nat -> Proof
prop_17_no_cyclic cyclegg_n =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_40) ->
      -- prop_17_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_40) =>
      -- (cyclegg_leq (Cyclegg_S ?x) Cyclegg_Z) =>
      -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
      -- <= prop_17_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_40)
      ()
    (Cyclegg_Z ) ->
      -- prop_17_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- <= prop_17_no_cyclic:cyclegg_n=Cyclegg_Z
      -- (cyclegg_leq Cyclegg_Z ?y) =>
      -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
      -- <= prop_17_no_cyclic:cyclegg_n=Cyclegg_Z
      ()

