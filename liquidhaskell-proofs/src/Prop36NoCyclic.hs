{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_36_no_cyclic: (cyclegg_takeWhile ($ cyclegg_const Cyclegg_True) cyclegg_xs) = cyclegg_xs
module Prop36NoCyclic where
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

{-@ reflect cyclegg_takeWhile @-}
cyclegg_takeWhile :: ((cyclegg_a -> Cyclegg_Bool) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_takeWhile p Cyclegg_Nil = Cyclegg_Nil
cyclegg_takeWhile p (Cyclegg_Cons x xs) = (cyclegg_ite (($) p x) (Cyclegg_Cons x (cyclegg_takeWhile p xs)) Cyclegg_Nil)

{-@ reflect cyclegg_const @-}
cyclegg_const :: (cyclegg_a -> cyclegg_b -> cyclegg_a)
cyclegg_const x y = x

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ prop_36_no_cyclic :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_takeWhile (cyclegg_const Cyclegg_True) cyclegg_xs) = cyclegg_xs } @-}
prop_36_no_cyclic :: (Cyclegg_List cyclegg_a) -> Proof
prop_36_no_cyclic cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) ->
      -- prop_36_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
      -- (cyclegg_takeWhile ?p (Cyclegg_Cons ?x ?xs)) =>
      -- apply-cyclegg_const =>
      -- (cyclegg_const ?x ?y) =>
      prop_36_no_cyclic cyclegg_xs_51
      -- ih-equality-cyclegg_xs=cyclegg_xs_51 =>
      -- <= prop_36_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
    (Cyclegg_Nil ) ->
      -- prop_36_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_takeWhile ?p Cyclegg_Nil) =>
      -- <= prop_36_no_cyclic:cyclegg_xs=Cyclegg_Nil
      ()

