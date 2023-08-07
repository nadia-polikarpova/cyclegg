{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_39_no_cyclic: (cyclegg_add (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_x Cyclegg_Nil)) (cyclegg_count cyclegg_n cyclegg_xs)) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_x cyclegg_xs))
module Prop39NoCyclic where
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

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ prop_39_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_add (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_x Cyclegg_Nil)) (cyclegg_count cyclegg_n cyclegg_xs)) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_x cyclegg_xs)) } @-}
prop_39_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_39_no_cyclic cyclegg_n cyclegg_x cyclegg_xs =
  let g_10 = (cyclegg_eq cyclegg_n cyclegg_x) in
    case g_10 of
      (Cyclegg_False ) ->
        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
        -- add guard scrutinee =>
        -- prop_39_no_cyclic:g_10=Cyclegg_False =>
        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
        -- (cyclegg_count ?x Cyclegg_Nil) =>
        -- (cyclegg_add Cyclegg_Z ?y) =>
        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
        -- <= prop_39_no_cyclic:g_10=Cyclegg_False
        -- <= add guard scrutinee
        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
        ()
      (Cyclegg_True ) ->
        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
        -- add guard scrutinee =>
        -- prop_39_no_cyclic:g_10=Cyclegg_True =>
        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
        -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
        -- (cyclegg_count ?x Cyclegg_Nil) =>
        -- (cyclegg_add Cyclegg_Z ?y) =>
        -- <= (cyclegg_ite Cyclegg_True ?x ?y)
        -- <= prop_39_no_cyclic:g_10=Cyclegg_True
        -- <= add guard scrutinee
        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
        ()

