{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_82_no_cyclic: (cyclegg_take cyclegg_n (cyclegg_zip cyclegg_xs cyclegg_ys)) = (cyclegg_zip (cyclegg_take cyclegg_n cyclegg_xs) (cyclegg_take cyclegg_n cyclegg_ys))
module Prop82NoCyclic where
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

{-@ reflect cyclegg_take @-}
cyclegg_take :: (Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_take Cyclegg_Z xs = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) Cyclegg_Nil = Cyclegg_Nil
cyclegg_take (Cyclegg_S n) (Cyclegg_Cons x xs) = (Cyclegg_Cons x (cyclegg_take n xs))

{-@ prop_82_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_a) -> { (cyclegg_take cyclegg_n (cyclegg_zip cyclegg_xs cyclegg_ys)) = (cyclegg_zip (cyclegg_take cyclegg_n cyclegg_xs) (cyclegg_take cyclegg_n cyclegg_ys)) } @-}
prop_82_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
prop_82_no_cyclic cyclegg_n cyclegg_xs cyclegg_ys =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_80) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) ->
          case cyclegg_ys of
            (Cyclegg_Cons cyclegg_ys_250 cyclegg_ys_251) ->
              -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
              -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141) =>
              -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_250 cyclegg_ys_251) =>
              -- (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys)) =>
              -- (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs)) =>
              prop_82_no_cyclic cyclegg_n_80 cyclegg_xs_141 cyclegg_ys_251
              -- ih-equality-cyclegg_n=cyclegg_n_80,cyclegg_xs=cyclegg_xs_141,cyclegg_ys=cyclegg_ys_251 =>
              -- <= (cyclegg_zip (Cyclegg_Cons ?x ?xs) (Cyclegg_Cons ?y ?ys))
              -- <= (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141)
              -- <= (cyclegg_take (Cyclegg_S ?n) (Cyclegg_Cons ?x ?xs))
              -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_250 cyclegg_ys_251)
            (Cyclegg_Nil ) ->
              -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
              -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):cyclegg_ys=Cyclegg_Nil =>
              -- (cyclegg_zip ?xs Cyclegg_Nil) =>
              -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
              -- <= (cyclegg_zip ?xs Cyclegg_Nil)
              -- <= (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil)
              -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80)
              -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_140 cyclegg_xs_141):cyclegg_ys=Cyclegg_Nil
              ()
        (Cyclegg_Nil ) ->
          -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80) =>
          -- prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_zip Cyclegg_Nil ?ys) =>
          -- (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil) =>
          -- <= (cyclegg_zip Cyclegg_Nil ?ys)
          -- <= (cyclegg_take (Cyclegg_S ?n) Cyclegg_Nil)
          -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80)
          -- <= prop_82_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_80):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      -- prop_82_no_cyclic:cyclegg_n=Cyclegg_Z =>
      -- (cyclegg_take Cyclegg_Z ?xs) =>
      -- <= (cyclegg_zip Cyclegg_Nil ?ys)
      -- <= (cyclegg_take Cyclegg_Z ?xs)
      -- <= prop_82_no_cyclic:cyclegg_n=Cyclegg_Z
      ()
