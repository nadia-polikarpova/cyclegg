{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_67_no_cyclic: (cyclegg_len (cyclegg_butlast cyclegg_xs)) = (cyclegg_sub (cyclegg_len cyclegg_xs) (Cyclegg_S Cyclegg_Z))
module Prop67NoCyclic where
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

{-@ reflect cyclegg_butlast @-}
cyclegg_butlast :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_butlast Cyclegg_Nil = Cyclegg_Nil
cyclegg_butlast (Cyclegg_Cons x Cyclegg_Nil) = Cyclegg_Nil
cyclegg_butlast (Cyclegg_Cons x (Cyclegg_Cons y ys)) = (Cyclegg_Cons x (cyclegg_butlast (Cyclegg_Cons y ys)))

{-@ reflect cyclegg_len @-}
cyclegg_len :: ((Cyclegg_List cyclegg_a) -> Cyclegg_Nat)
cyclegg_len Cyclegg_Nil = Cyclegg_Z
cyclegg_len (Cyclegg_Cons x xs) = (Cyclegg_S (cyclegg_len xs))

{-@ reflect cyclegg_sub @-}
cyclegg_sub :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_sub x Cyclegg_Z = x
cyclegg_sub Cyclegg_Z y = Cyclegg_Z
cyclegg_sub (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_sub x y)

{-@ prop_67_no_cyclic :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> { (cyclegg_len (cyclegg_butlast cyclegg_xs)) = (cyclegg_sub (cyclegg_len cyclegg_xs) (Cyclegg_S Cyclegg_Z)) } @-}
prop_67_no_cyclic :: (Cyclegg_List cyclegg_a) -> Proof
prop_67_no_cyclic cyclegg_xs =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) ->
      case cyclegg_xs_71 of
        (Cyclegg_Cons cyclegg_xs_71_160 cyclegg_xs_71_161) ->
          -- prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
          -- prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):cyclegg_xs_71=(Cyclegg_Cons cyclegg_xs_71_160 cyclegg_xs_71_161) =>
          -- (cyclegg_butlast (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys))) =>
          -- <= prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):cyclegg_xs_71=(Cyclegg_Cons cyclegg_xs_71_160 cyclegg_xs_71_161)
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          prop_67_no_cyclic cyclegg_xs_71
          -- ih-equality-cyclegg_xs=cyclegg_xs_71 =>
          -- prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):cyclegg_xs_71=(Cyclegg_Cons cyclegg_xs_71_160 cyclegg_xs_71_161) =>
          -- (cyclegg_len (Cyclegg_Cons ?x ?xs)) =>
          -- (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- (cyclegg_sub ?x Cyclegg_Z) =>
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):cyclegg_xs_71=(Cyclegg_Cons cyclegg_xs_71_160 cyclegg_xs_71_161)
          -- <= (cyclegg_sub ?x Cyclegg_Z)
          -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71)
        (Cyclegg_Nil ) ->
          -- prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
          -- prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):cyclegg_xs_71=Cyclegg_Nil =>
          -- (cyclegg_butlast (Cyclegg_Cons ?x Cyclegg_Nil)) =>
          -- <= prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):cyclegg_xs_71=Cyclegg_Nil
          -- <= (cyclegg_sub ?x Cyclegg_Z)
          -- <= (cyclegg_sub (Cyclegg_S ?x) (Cyclegg_S ?y))
          -- <= (cyclegg_len (Cyclegg_Cons ?x ?xs))
          -- <= prop_67_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71)
          ()
    (Cyclegg_Nil ) ->
      -- prop_67_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
      -- (cyclegg_butlast Cyclegg_Nil) =>
      -- (cyclegg_len Cyclegg_Nil) =>
      -- <= (cyclegg_sub Cyclegg_Z ?y)
      -- <= (cyclegg_len Cyclegg_Nil)
      -- <= prop_67_no_cyclic:cyclegg_xs=Cyclegg_Nil
      ()

