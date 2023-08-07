{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_31_no_cyclic: (cyclegg_min (cyclegg_min cyclegg_a cyclegg_b) cyclegg_c) = (cyclegg_min cyclegg_a (cyclegg_min cyclegg_b cyclegg_c))
module Prop31NoCyclic where
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

{-@ reflect cyclegg_min @-}
cyclegg_min :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_min Cyclegg_Z y = Cyclegg_Z
cyclegg_min x Cyclegg_Z = Cyclegg_Z
cyclegg_min (Cyclegg_S x) (Cyclegg_S y) = (Cyclegg_S (cyclegg_min x y))

{-@ prop_31_no_cyclic :: cyclegg_a: Cyclegg_Nat -> cyclegg_b: Cyclegg_Nat -> cyclegg_c: Cyclegg_Nat -> { (cyclegg_min (cyclegg_min cyclegg_a cyclegg_b) cyclegg_c) = (cyclegg_min cyclegg_a (cyclegg_min cyclegg_b cyclegg_c)) } @-}
prop_31_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat -> Proof
prop_31_no_cyclic cyclegg_a cyclegg_b cyclegg_c =
  case cyclegg_a of
    (Cyclegg_S cyclegg_a_70) ->
      case cyclegg_b of
        (Cyclegg_S cyclegg_b_120) ->
          case cyclegg_c of
            (Cyclegg_S cyclegg_c_220) ->
              -- prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70) =>
              -- prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=(Cyclegg_S cyclegg_b_120) =>
              -- (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
              -- prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=(Cyclegg_S cyclegg_b_120):cyclegg_c=(Cyclegg_S cyclegg_c_220) =>
              -- (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
              prop_31_no_cyclic cyclegg_a_70 cyclegg_b_120 cyclegg_c_220
              -- ih-equality-cyclegg_a=cyclegg_a_70,cyclegg_b=cyclegg_b_120,cyclegg_c=cyclegg_c_220 =>
              -- <= (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y))
              -- <= prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70)
              -- <= (cyclegg_min (Cyclegg_S ?x) (Cyclegg_S ?y))
              -- <= prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=(Cyclegg_S cyclegg_b_120)
              -- <= prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=(Cyclegg_S cyclegg_b_120):cyclegg_c=(Cyclegg_S cyclegg_c_220)
            (Cyclegg_Z ) ->
              -- prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=(Cyclegg_S cyclegg_b_120):cyclegg_c=Cyclegg_Z =>
              -- (cyclegg_min ?x Cyclegg_Z) =>
              -- <= (cyclegg_min ?x Cyclegg_Z)
              -- <= (cyclegg_min ?x Cyclegg_Z)
              -- <= prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=(Cyclegg_S cyclegg_b_120):cyclegg_c=Cyclegg_Z
              ()
        (Cyclegg_Z ) ->
          -- prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=Cyclegg_Z =>
          -- (cyclegg_min ?x Cyclegg_Z) =>
          -- (cyclegg_min Cyclegg_Z ?y) =>
          -- <= (cyclegg_min ?x Cyclegg_Z)
          -- <= (cyclegg_min Cyclegg_Z ?y)
          -- <= prop_31_no_cyclic:cyclegg_a=(Cyclegg_S cyclegg_a_70):cyclegg_b=Cyclegg_Z
          ()
    (Cyclegg_Z ) ->
      -- prop_31_no_cyclic:cyclegg_a=Cyclegg_Z =>
      -- (cyclegg_min Cyclegg_Z ?y) =>
      -- (cyclegg_min Cyclegg_Z ?y) =>
      -- <= (cyclegg_min Cyclegg_Z ?y)
      -- <= prop_31_no_cyclic:cyclegg_a=Cyclegg_Z
      ()

