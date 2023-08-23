{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_23_no_cyclic: (cyclegg_max cyclegg_a cyclegg_b) = (cyclegg_max cyclegg_b cyclegg_a)
module Prop23NoCyclic where
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

{-@ prop_23_no_cyclic :: cyclegg_a: Cyclegg_Nat -> cyclegg_b: Cyclegg_Nat -> { (cyclegg_max cyclegg_a cyclegg_b) = (cyclegg_max cyclegg_b cyclegg_a) } @-}
prop_23_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> Proof
prop_23_no_cyclic cyclegg_a cyclegg_b =
  case cyclegg_a of
    (Cyclegg_S cyclegg_a_40) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_80) ->
          -- prop_23_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_40) =>
          -- prop_23_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=(Cyclegg_S cyclegg_b_80) =>
          -- (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          prop_23_no_cyclic cyclegg_a_40 cyclegg_b_80
          -- ih-equality-cyclegg_a=cyclegg_a_40,cyclegg_b=cyclegg_b_80 =>
          -- <= (cyclegg_max (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= prop_23_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=(Cyclegg_S cyclegg_b_80)
          -- <= prop_23_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_40)
        (Cyclegg_Z ) ->
          -- prop_23_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_max ?x Cyclegg_Z) =>
          -- <= (cyclegg_max Cyclegg_Z ?y)
          -- <= prop_23_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_40):cyclegg_b=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      (cyclegg_max cyclegg_a cyclegg_b)
      -- prop_23_no_cyclic:cyclegg_a=Cyclegg_Z =>
      ==. (cyclegg_max Cyclegg_Z cyclegg_b)
      -- (cyclegg_max Cyclegg_Z ?y) =>
      ==. cyclegg_b
      -- <= (cyclegg_max ?x Cyclegg_Z)
      ==. (cyclegg_max cyclegg_b Cyclegg_Z)
      -- <= prop_23_no_cyclic:cyclegg_a=Cyclegg_Z
      ==. (cyclegg_max cyclegg_b cyclegg_a)
      ***
      QED
