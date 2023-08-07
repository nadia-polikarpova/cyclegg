{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_84_no_cyclic: (cyclegg_zip cyclegg_xs (cyclegg_append cyclegg_ys cyclegg_zs)) = (cyclegg_append (cyclegg_zip (cyclegg_take (cyclegg_len cyclegg_ys) cyclegg_xs) cyclegg_ys) (cyclegg_zip (cyclegg_drop (cyclegg_len cyclegg_ys) cyclegg_xs) cyclegg_zs))
module Prop84NoCyclic where
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

{-@ reflect cyclegg_drop @-}
cyclegg_drop :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_drop Cyclegg_Z xs = xs
cyclegg_drop (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_drop (Cyclegg_S n) (Cyclegg_Cons x xs) = (cyclegg_drop n xs)

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_zip @-}
cyclegg_zip :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_b) -> (Cyclegg_List (Cyclegg_Pair cyclegg_a cyclegg_b)))
cyclegg_zip Cyclegg_Nil ys = Cyclegg_Nil
cyclegg_zip xs Cyclegg_Nil = Cyclegg_Nil
cyclegg_zip (Cyclegg_Cons x xs) (Cyclegg_Cons y ys) = (Cyclegg_Cons (Cyclegg_Pair x y) (cyclegg_zip xs ys))

{-@ prop_84_no_cyclic :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_a) -> cyclegg_zs: (Cyclegg_List cyclegg_a) -> { (cyclegg_zip cyclegg_xs (cyclegg_append cyclegg_ys cyclegg_zs)) = (cyclegg_append (cyclegg_zip (cyclegg_take (cyclegg_len cyclegg_ys) cyclegg_xs) cyclegg_ys) (cyclegg_zip (cyclegg_drop (cyclegg_len cyclegg_ys) cyclegg_xs) cyclegg_zs)) } @-}
prop_84_no_cyclic :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
prop_84_no_cyclic cyclegg_xs cyclegg_ys cyclegg_zs = undefined
  -- case cyclegg_xs of
  --   (Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) ->
  --     case cyclegg_ys of
  --       (Cyclegg_Cons cyclegg_ys_200 cyclegg_ys_201) ->
  --         -- prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
  --         -- prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_200 cyclegg_ys_201) =>
  --         -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
  --         -- (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys)) =>
  --         prop_84_no_cyclic cyclegg_xs_111 cyclegg_ys_201 cyclegg_zs
  --         -- ih-equality-cyclegg_xs=cyclegg_xs_111,cyclegg_ys=cyclegg_ys_201,cyclegg_zs=cyclegg_zs =>
  --         -- <= (cyclegg_drop (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
  --         -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_200 cyclegg_ys_201)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111)
  --         -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
  --         -- <= (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys))
  --         -- <= (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
  --         -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_200 cyclegg_ys_201)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_200 cyclegg_ys_201)
  --       (Cyclegg_Nil ) ->
  --         -- <= (cyclegg_drop Cyclegg_Z ?xs)
  --         -- <= (cyclegg_len Cyclegg_Nil)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil
  --         -- prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil =>
  --         -- (cyclegg_append Cyclegg_Nil ?ys) =>
  --         -- <= (cyclegg_append Cyclegg_Nil ?ys)
  --         -- <= (cyclegg_zip ?xs Cyclegg_Nil)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):cyclegg_ys=Cyclegg_Nil
  --         ()
  --   (Cyclegg_Nil ) ->
  --     case cyclegg_ys of
  --       (Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121) ->
  --         -- prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
  --         -- (cyclegg_zip Cyclegg_Nil ?ys) =>
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil
  --         -- <= (cyclegg_append Cyclegg_Nil ?ys)
  --         -- <= (cyclegg_zip Cyclegg_Nil ?ys)
  --         -- <= (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil)
  --         -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil
  --         -- prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
  --         -- <= (cyclegg_zip Cyclegg_Nil ?ys)
  --         -- <= (cyclegg_drop (Cyclegg_S ?n) Cyclegg_Nil)
  --         -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil
  --         ()
  --       (Cyclegg_Nil ) ->
  --         -- prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil
  --         -- <= (cyclegg_drop Cyclegg_Z ?xs)
  --         -- <= (cyclegg_len Cyclegg_Nil)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil
  --         -- prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil =>
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil
  --         -- prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil =>
  --         -- (cyclegg_append Cyclegg_Nil ?ys) =>
  --         -- <= (cyclegg_append Cyclegg_Nil ?ys)
  --         -- <= (cyclegg_zip ?xs Cyclegg_Nil)
  --         -- <= prop_84_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil
  --         ()
