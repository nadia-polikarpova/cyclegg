{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_04_no_cyclic: (Cyclegg_S (cyclegg_count cyclegg_n cyclegg_xs)) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_n cyclegg_xs))
module Prop04NoCyclic where
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

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ prop_04_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (Cyclegg_S (cyclegg_count cyclegg_n cyclegg_xs)) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_n cyclegg_xs)) } @-}
prop_04_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_04_no_cyclic cyclegg_n cyclegg_xs =
  let g_6 = (cyclegg_eq cyclegg_n cyclegg_n) in
    case g_6 of
      (Cyclegg_False ) ->
        case cyclegg_n of
          (Cyclegg_S cyclegg_n_100) ->
            case cyclegg_xs of
              (Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) ->
                let g_38 = (cyclegg_eq (Cyclegg_S cyclegg_n_100) cyclegg_xs_200) in
                  case g_38 of
                    (Cyclegg_False ) ->
                      -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_38=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      prop_04_no_cyclic cyclegg_n cyclegg_xs_201
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_201 =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_04_no_cyclic:g_6=Cyclegg_False =>
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_38=Cyclegg_False
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_True ) ->
                      -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201) =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_38=Cyclegg_True =>
                      prop_04_no_cyclic cyclegg_n cyclegg_xs_201
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_201 =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_04_no_cyclic:g_6=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                      ? prop_04_no_cyclic cyclegg_n cyclegg_xs_201
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_201 =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_04_no_cyclic:g_6=Cyclegg_False =>
                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201):g_38=Cyclegg_True
                      -- <= add guard scrutinee
                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      ? prop_04_no_cyclic cyclegg_n cyclegg_xs_201
                      -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=cyclegg_xs_201
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_200 cyclegg_xs_201)
                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                      -- <= prop_04_no_cyclic:g_6=Cyclegg_False
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
              (Cyclegg_Nil ) ->
                -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil
                prop_04_no_cyclic cyclegg_n_100 cyclegg_xs
                -- ih-equality-cyclegg_n=cyclegg_n_100,cyclegg_xs=cyclegg_xs =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- <= (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y))
                -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100)
                -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100)
                -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil
                -- prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_100):cyclegg_xs=Cyclegg_Nil
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
          (Cyclegg_Z ) ->
            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
            -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
            -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=Cyclegg_Z
            -- <= prop_04_no_cyclic:g_6=Cyclegg_False:cyclegg_n=Cyclegg_Z
            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
            ()
      (Cyclegg_True ) ->
        -- <= (cyclegg_ite Cyclegg_True ?x ?y)
        -- <= prop_04_no_cyclic:g_6=Cyclegg_True
        -- <= add guard scrutinee
        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
        ()

