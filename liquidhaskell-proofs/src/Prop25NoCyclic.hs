{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_25_no_cyclic: (cyclegg_eq (cyclegg_max cyclegg_a cyclegg_b) cyclegg_b) = (cyclegg_leq cyclegg_a cyclegg_b)
module Prop25NoCyclic where
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

{-@ reflect cyclegg_max @-}
cyclegg_max :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_max Cyclegg_Z y = y
cyclegg_max x Cyclegg_Z = x
cyclegg_max (Cyclegg_S x) (Cyclegg_S y) = (Cyclegg_S (cyclegg_max x y))

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

{-@ prop_25_no_cyclic :: cyclegg_a: Cyclegg_Nat -> cyclegg_b: Cyclegg_Nat -> { (cyclegg_eq (cyclegg_max cyclegg_a cyclegg_b) cyclegg_b) = (cyclegg_leq cyclegg_a cyclegg_b) } @-}
prop_25_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
prop_25_no_cyclic cyclegg_a cyclegg_b =
  case cyclegg_a of
    (Cyclegg_S cyclegg_a_50) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_100) ->
          -- prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50) =>
          -- prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=(Cyclegg_S cyclegg_b_100) =>
          -- (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=(Cyclegg_S cyclegg_b_100) =>
          -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          prop_25_no_cyclic cyclegg_a_50 cyclegg_b_100
          -- ih-equality-cyclegg_a=cyclegg_a_50,cyclegg_b=cyclegg_b_100 =>
          -- <= (cyclegg_leq (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50)
          -- <= prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=(Cyclegg_S cyclegg_b_100)
        (Cyclegg_Z ) ->
          -- prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_max ?x Cyclegg_Z) =>
          -- prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50) =>
          -- prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
          -- <= (cyclegg_leq (Cyclegg_S ?x) Cyclegg_Z)
          -- <= prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50)
          -- <= prop_25_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_50):cyclegg_b=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_80) ->
          -- prop_25_no_cyclic:cyclegg_a=Cyclegg_Z =>
          -- (cyclegg_max Cyclegg_Z ?y) =>
          -- prop_25_no_cyclic:cyclegg_a=Cyclegg_Z:cyclegg_b=(Cyclegg_S cyclegg_b_80) =>
          -- prop_25_no_cyclic:cyclegg_a=Cyclegg_Z:cyclegg_b=(Cyclegg_S cyclegg_b_80) =>
          -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- <= (cyclegg_max Cyclegg_Z ?y)
          prop_25_no_cyclic (Cyclegg_Z) cyclegg_b_80
          -- ih-equality-cyclegg_a=(Cyclegg_Z),cyclegg_b=cyclegg_b_80 =>
          -- (cyclegg_leq Cyclegg_Z ?y) =>
          -- <= (cyclegg_leq Cyclegg_Z ?y)
          -- <= prop_25_no_cyclic:cyclegg_a=Cyclegg_Z
        (Cyclegg_Z ) ->
          -- prop_25_no_cyclic:cyclegg_a=Cyclegg_Z =>
          -- (cyclegg_max Cyclegg_Z ?y) =>
          -- prop_25_no_cyclic:cyclegg_a=Cyclegg_Z:cyclegg_b=Cyclegg_Z =>
          -- prop_25_no_cyclic:cyclegg_a=Cyclegg_Z:cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
          -- <= (cyclegg_leq Cyclegg_Z ?y)
          -- <= prop_25_no_cyclic:cyclegg_a=Cyclegg_Z
          ()

