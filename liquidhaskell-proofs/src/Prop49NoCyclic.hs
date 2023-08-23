{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_49_no_cyclic: (cyclegg_butlast (cyclegg_append cyclegg_xs cyclegg_ys)) = (cyclegg_butlastConcat cyclegg_xs cyclegg_ys)
module Prop49NoCyclic where
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

{-@ reflect cyclegg_butlast @-}
cyclegg_butlast :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_butlast Cyclegg_Nil = Cyclegg_Nil
cyclegg_butlast (Cyclegg_Cons x Cyclegg_Nil) = Cyclegg_Nil
cyclegg_butlast (Cyclegg_Cons x (Cyclegg_Cons y ys)) = (Cyclegg_Cons x (cyclegg_butlast (Cyclegg_Cons y ys)))

{-@ reflect cyclegg_butlastConcat @-}
cyclegg_butlastConcat :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_butlastConcat xs Cyclegg_Nil = (cyclegg_butlast xs)
cyclegg_butlastConcat xs (Cyclegg_Cons y ys) = (cyclegg_append xs (cyclegg_butlast (Cyclegg_Cons y ys)))

{-@ prop_49_no_cyclic :: cyclegg_xs: (Cyclegg_List cyclegg_a) -> cyclegg_ys: (Cyclegg_List cyclegg_a) -> { (cyclegg_butlast (cyclegg_append cyclegg_xs cyclegg_ys)) = (cyclegg_butlastConcat cyclegg_xs cyclegg_ys) } @-}
prop_49_no_cyclic :: (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> Proof
prop_49_no_cyclic cyclegg_xs cyclegg_ys =
  case cyclegg_xs of
    (Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) ->
      case cyclegg_ys of
        (Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121) ->
          case cyclegg_xs_51 of
            (Cyclegg_Cons cyclegg_xs_51_260 cyclegg_xs_51_261) ->
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121):cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_260 cyclegg_xs_51_261) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- (cyclegg_butlast (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys))) =>
              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121):cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_260 cyclegg_xs_51_261)
              prop_49_no_cyclic cyclegg_xs_51 cyclegg_ys
              -- ih-equality-cyclegg_xs=cyclegg_xs_51,cyclegg_ys=cyclegg_ys =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121) =>
              -- (cyclegg_butlastConcat ?xs (Cyclegg_Cons ?y ?ys)) =>
              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
              -- <= (cyclegg_butlastConcat ?xs (Cyclegg_Cons ?y ?ys))
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121)
            (Cyclegg_Nil ) ->
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121):cyclegg_xs_51=Cyclegg_Nil =>
              -- (cyclegg_append Cyclegg_Nil ?ys) =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121) =>
              -- (cyclegg_butlast (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys))) =>
              -- <= (cyclegg_append Cyclegg_Nil ?ys)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121):cyclegg_xs_51=Cyclegg_Nil
              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
              -- <= (cyclegg_butlastConcat ?xs (Cyclegg_Cons ?y ?ys))
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=(Cyclegg_Cons cyclegg_ys_120 cyclegg_ys_121)
              ()
        (Cyclegg_Nil ) ->
          case cyclegg_xs_51 of
            (Cyclegg_Cons cyclegg_xs_51_150 cyclegg_xs_51_151) ->
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_150 cyclegg_xs_51_151) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- (cyclegg_butlast (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys))) =>
              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_150 cyclegg_xs_51_151)
              prop_49_no_cyclic cyclegg_xs_51 cyclegg_ys
              -- ih-equality-cyclegg_xs=cyclegg_xs_51,cyclegg_ys=cyclegg_ys =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil =>
              -- (cyclegg_butlastConcat ?xs Cyclegg_Nil) =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_150 cyclegg_xs_51_151) =>
              -- <= (cyclegg_butlast (Cyclegg_Cons ?x (Cyclegg_Cons ?y ?ys)))
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil:cyclegg_xs_51=(Cyclegg_Cons cyclegg_xs_51_150 cyclegg_xs_51_151)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
              -- <= (cyclegg_butlastConcat ?xs Cyclegg_Nil)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil
            (Cyclegg_Nil ) ->
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51) =>
              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil:cyclegg_xs_51=Cyclegg_Nil =>
              -- prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil =>
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil:cyclegg_xs_51=Cyclegg_Nil
              -- (cyclegg_append Cyclegg_Nil ?ys) =>
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51)
              -- <= (cyclegg_butlastConcat ?xs Cyclegg_Nil)
              -- <= prop_49_no_cyclic:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_50 cyclegg_xs_51):cyclegg_ys=Cyclegg_Nil
              ()
    (Cyclegg_Nil ) ->
      case cyclegg_ys of
        (Cyclegg_Cons cyclegg_ys_70 cyclegg_ys_71) ->
          -- <= (cyclegg_append Cyclegg_Nil ?ys)
          -- <= prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil
          -- prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=(Cyclegg_Cons cyclegg_ys_70 cyclegg_ys_71) =>
          -- <= (cyclegg_butlastConcat ?xs (Cyclegg_Cons ?y ?ys))
          -- <= prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=(Cyclegg_Cons cyclegg_ys_70 cyclegg_ys_71)
          ()
        (Cyclegg_Nil ) ->
          -- prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_append Cyclegg_Nil ?ys) =>
          -- <= (cyclegg_butlastConcat ?xs Cyclegg_Nil)
          -- prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil =>
          -- <= prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil
          -- <= prop_49_no_cyclic:cyclegg_xs=Cyclegg_Nil:cyclegg_ys=Cyclegg_Nil
          ()

