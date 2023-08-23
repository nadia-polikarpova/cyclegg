{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_14_no_cyclic: (cyclegg_filter cyclegg_p (cyclegg_append cyclegg_xs cyclegg_ys)) = (cyclegg_append (cyclegg_filter cyclegg_p cyclegg_xs) (cyclegg_filter cyclegg_p cyclegg_ys))
module Prop14NoCyclic where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_filter @-}
cyclegg_filter :: ((cyclegg_a -> Cyclegg_Bool) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_filter p Cyclegg_Nil = Cyclegg_Nil
cyclegg_filter p (Cyclegg_Cons x xs) = (cyclegg_ite (($) p x) (Cyclegg_Cons x (cyclegg_filter p xs)) (cyclegg_filter p xs))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ prop_14_no_cyclic :: cyclegg_p: (cyclegg_a -> Cyclegg_Bool) -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_a) -> { (cyclegg_filter cyclegg_p (cyclegg_append cyclegg_xs cyclegg_ys)) = (cyclegg_append (cyclegg_filter cyclegg_p cyclegg_xs) (cyclegg_filter cyclegg_p cyclegg_ys)) } @-}
prop_14_no_cyclic :: (cyclegg_a -> Cyclegg_Bool) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
prop_14_no_cyclic cyclegg_p cyclegg_xs cyclegg_ys =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) ->
      let g_16 = (($) cyclegg_p cyclegg_xs_80) in
        case g_16 of
          (Cyclegg_False ) ->
            -- prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            -- (cyclegg_filter ?p (Cyclegg_Cons ?x ?xs)) =>
            -- add guard scrutinee =>
            -- prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_16=Cyclegg_False =>
            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
            prop_14_no_cyclic cyclegg_p cyclegg_xs_81 cyclegg_ys
            -- ih-equality-cyclegg_p=cyclegg_p,cyclegg_xs=cyclegg_xs_81,cyclegg_ys=cyclegg_ys =>
            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
            -- <= prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_16=Cyclegg_False
            -- <= add guard scrutinee
            -- <= (cyclegg_filter ?p (Cyclegg_Cons ?x ?xs))
            -- <= prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81)
          (Cyclegg_True ) ->
            -- prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81) =>
            -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
            -- (cyclegg_filter ?p (Cyclegg_Cons ?x ?xs)) =>
            -- add guard scrutinee =>
            -- prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_16=Cyclegg_True =>
            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
            prop_14_no_cyclic cyclegg_p cyclegg_xs_81 cyclegg_ys
            -- ih-equality-cyclegg_p=cyclegg_p,cyclegg_xs=cyclegg_xs_81,cyclegg_ys=cyclegg_ys =>
            -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
            -- <= prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81):g_16=Cyclegg_True
            -- <= add guard scrutinee
            -- <= (cyclegg_filter ?p (Cyclegg_Cons ?x ?xs))
            -- <= prop_14_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_80 cyclegg_xs_81)
    (Cyclegg_Nil ) ->
      -- prop_14_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_append Cyclegg_Nil ?ys) =>
      -- <= (cyclegg_append Cyclegg_Nil ?ys)
      -- <= (cyclegg_filter ?p Cyclegg_Nil)
      -- <= prop_14_no_cyclic:cyclegg_xs=Cyclegg_Nil
      ()

