{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_45_no_cyclic: (cyclegg_zip (Cyclegg_Cons cyclegg_x cyclegg_xs) (Cyclegg_Cons cyclegg_y cyclegg_ys)) = (Cyclegg_Cons (Cyclegg_Pair cyclegg_x cyclegg_y) (cyclegg_zip cyclegg_xs cyclegg_ys))
module Prop45NoCyclic where
import Language.Haskell.Liquid.Equational

{-@ autosize Cyclegg_Expr @-}
data Cyclegg_Expr cyclegg_a where
  Cyclegg_MkExpr :: ((Cyclegg_Tm cyclegg_a) -> Cyclegg_Nat -> (Cyclegg_Expr cyclegg_a))

{-@ autosize Cyclegg_Tree @-}
data Cyclegg_Tree cyclegg_a where
  Cyclegg_Leaf :: (Cyclegg_Tree cyclegg_a)
  Cyclegg_Node :: ((Cyclegg_Tree cyclegg_a) -> cyclegg_a -> (Cyclegg_Tree cyclegg_a) -> (Cyclegg_Tree cyclegg_a))

-- {-@ autosize Cyclegg_List @-}
data Cyclegg_List cyclegg_a where
  Cyclegg_Nil :: (Cyclegg_List cyclegg_a)
  Cyclegg_Cons :: (cyclegg_a -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))

{-@ autosize Cyclegg_Tm @-}
data Cyclegg_Tm cyclegg_a where
  Cyclegg_Var :: (cyclegg_a -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_Cst :: (Cyclegg_Nat -> (Cyclegg_Tm cyclegg_a))
  Cyclegg_App :: ((Cyclegg_Expr cyclegg_a) -> (Cyclegg_Expr cyclegg_a) -> (Cyclegg_Tm cyclegg_a))

-- {-@ autosize Cyclegg_Nat @-}
data Cyclegg_Nat where
  Cyclegg_Z :: Cyclegg_Nat
  Cyclegg_S :: (Cyclegg_Nat -> Cyclegg_Nat)

{-@ autosize Cyclegg_Bool @-}
data Cyclegg_Bool where
  Cyclegg_True :: Cyclegg_Bool
  Cyclegg_False :: Cyclegg_Bool

-- {-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ reflect cyclegg_zip @-}
cyclegg_zip :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_b) -> (Cyclegg_List (Cyclegg_Pair cyclegg_a cyclegg_b)))
cyclegg_zip Cyclegg_Nil ys = Cyclegg_Nil
cyclegg_zip xs Cyclegg_Nil = Cyclegg_Nil
cyclegg_zip (Cyclegg_Cons x xs) (Cyclegg_Cons y ys) = (Cyclegg_Cons (Cyclegg_Pair x y) (cyclegg_zip xs ys))

{-@ prop_45_no_cyclic :: cyclegg_x: cyclegg_a -> cyclegg_y: cyclegg_b -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_b) -> { (cyclegg_zip (Cyclegg_Cons cyclegg_x cyclegg_xs) (Cyclegg_Cons cyclegg_y cyclegg_ys)) = (Cyclegg_Cons (Cyclegg_Pair cyclegg_x cyclegg_y) (cyclegg_zip cyclegg_xs cyclegg_ys)) } @-}
prop_45_no_cyclic :: cyclegg_a -> cyclegg_b -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_b) -> Proof
prop_45_no_cyclic cyclegg_x cyclegg_y cyclegg_xs cyclegg_ys = undefined
  -- (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys)) =>
  ()
