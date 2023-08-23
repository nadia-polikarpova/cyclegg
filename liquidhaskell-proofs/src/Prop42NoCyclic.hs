{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_42_no_cyclic: (cyclegg_take (Cyclegg_S cyclegg_n) (Cyclegg_Cons cyclegg_x cyclegg_xs)) = (Cyclegg_Cons cyclegg_x (cyclegg_take cyclegg_n cyclegg_xs))
module Prop42NoCyclic where
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

{-@ reflect cyclegg_take @-}
cyclegg_take :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_take Cyclegg_Z xs = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) (Cyclegg_Cons x xs) = (Cyclegg_Cons x (cyclegg_take n xs))

{-@ prop_42_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_x: cyclegg_a -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_take (Cyclegg_S cyclegg_n) (Cyclegg_Cons cyclegg_x cyclegg_xs)) = (Cyclegg_Cons cyclegg_x (cyclegg_take cyclegg_n cyclegg_xs)) } @-}
prop_42_no_cyclic :: Cyclegg_Nat -> cyclegg_a -> (Cyclegg_List cyclegg_a) -> Proof
prop_42_no_cyclic cyclegg_n cyclegg_x cyclegg_xs =
  -- (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
  ()

