{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_29_no_cyclic: (cyclegg_elem cyclegg_x (cyclegg_ins1 cyclegg_x cyclegg_xs)) = Cyclegg_True
module Prop29NoCyclic where
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

{-@ autosize Cyclegg_Pair @-}
data Cyclegg_Pair cyclegg_a cyclegg_b where
  Cyclegg_Pair :: (cyclegg_a -> cyclegg_b -> (Cyclegg_Pair cyclegg_a cyclegg_b))

{-@ reflect cyclegg_eq @-}
cyclegg_eq :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Bool)
cyclegg_eq Cyclegg_Z Cyclegg_Z = Cyclegg_True
cyclegg_eq Cyclegg_Z (Cyclegg_S y) = Cyclegg_False
cyclegg_eq (Cyclegg_S x) Cyclegg_Z = Cyclegg_False
cyclegg_eq (Cyclegg_S x) (Cyclegg_S y) = (cyclegg_eq x y)

{-@ reflect cyclegg_elem @-}
cyclegg_elem :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Bool)
cyclegg_elem n Cyclegg_Nil = Cyclegg_False
cyclegg_elem n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) Cyclegg_True (cyclegg_elem n xs))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_ins1 @-}
cyclegg_ins1 :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_ins1 n Cyclegg_Nil = (Cyclegg_Cons n Cyclegg_Nil)
cyclegg_ins1 n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) (Cyclegg_Cons n (Cyclegg_Cons x xs)) (Cyclegg_Cons x (cyclegg_ins1 n xs)))

-- {-@ measure natSize @-}
-- {-@ natSize :: Cyclegg_Nat -> Int @-}
-- natSize :: Cyclegg_Nat -> Int
-- natSize Cyclegg_Z = 0
-- natSize (Cyclegg_S n) = 1 + natSize n

-- {-@ measure listSize @-}
-- {-@ listSize :: Cyclegg_List Cyclegg_Nat -> Int @-}
-- listSize :: Cyclegg_List Cyclegg_Nat -> Int
-- listSize Cyclegg_Nil = 0
-- listSize (Cyclegg_Cons x xs) = natSize x + listSize xs

{-@ prop_29_no_cyclic :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_elem cyclegg_x (cyclegg_ins1 cyclegg_x cyclegg_xs)) = Cyclegg_True } @-}
prop_29_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_29_no_cyclic cyclegg_x cyclegg_xs =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_50) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) ->
          let g_23 = (cyclegg_eq cyclegg_xs_90 cyclegg_xs_90) in
            case g_23 of
              (Cyclegg_False ) ->
                let g_33 = (cyclegg_eq cyclegg_x_50 cyclegg_xs_90) in
                  case g_33 of
                    (Cyclegg_False ) ->
                      let g_28 = (cyclegg_eq (Cyclegg_S cyclegg_x_50) cyclegg_xs_90) in
                        case g_28 of
                          (Cyclegg_False ) ->
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                            -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_False =>
                            prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                            -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                            ? prop_29_no_cyclic cyclegg_x cyclegg_xs_91
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_91 =>
                            ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                            -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                            -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
                          (Cyclegg_True ) ->
                            let g_56 = (cyclegg_eq cyclegg_x_50 cyclegg_x_50) in
                              case g_56 of
                                (Cyclegg_False ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_True:g_56=Cyclegg_False =>
                                  prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
                                (Cyclegg_True ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_True:g_56=Cyclegg_True =>
                                  prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
                    (Cyclegg_True ) ->
                      let g_51 = (cyclegg_eq cyclegg_x_50 cyclegg_x_50) in
                        case g_51 of
                          (Cyclegg_False ) ->
                            let g_28 = (cyclegg_eq (Cyclegg_S cyclegg_x_50) cyclegg_xs_90) in
                              case g_28 of
                                (Cyclegg_False ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_False:g_28=Cyclegg_False =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_False:g_28=Cyclegg_False =>
                                  prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  ? prop_29_no_cyclic cyclegg_x cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_91 =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
                                (Cyclegg_True ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_False =>
                                  prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_False:g_28=Cyclegg_True =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
                          (Cyclegg_True ) ->
                            let g_28 = (cyclegg_eq (Cyclegg_S cyclegg_x_50) cyclegg_xs_90) in
                              case g_28 of
                                (Cyclegg_False ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_True:g_28=Cyclegg_False =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_True:g_28=Cyclegg_False =>
                                  prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  ? prop_29_no_cyclic cyclegg_x cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_91 =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
                                (Cyclegg_True ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_True:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_False:g_33=Cyclegg_True:g_51=Cyclegg_True =>
                                  prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- <= ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  ? prop_29_no_cyclic cyclegg_xs_90 cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_xs_90,cyclegg_xs=cyclegg_xs_91 =>
              (Cyclegg_True ) ->
                let g_33 = (cyclegg_eq cyclegg_x_50 cyclegg_xs_90) in
                  case g_33 of
                    (Cyclegg_False ) ->
                      let g_28 = (cyclegg_eq (Cyclegg_S cyclegg_x_50) cyclegg_xs_90) in
                        case g_28 of
                          (Cyclegg_False ) ->
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                            -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_False =>
                            -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                            -- <= add guard scrutinee
                            prop_29_no_cyclic cyclegg_x cyclegg_xs_91
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_91 =>
                            -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                            -- <= add guard scrutinee
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- add guard scrutinee =>
                            -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                          (Cyclegg_True ) ->
                            let g_64 = (cyclegg_eq cyclegg_x_50 cyclegg_x_50) in
                              case g_64 of
                                (Cyclegg_False ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_True:g_64=Cyclegg_False =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                                  ()
                                (Cyclegg_True ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_True:g_64=Cyclegg_True =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                                  ()
                    (Cyclegg_True ) ->
                      let g_57 = (cyclegg_eq cyclegg_x_50 cyclegg_x_50) in
                        case g_57 of
                          (Cyclegg_False ) ->
                            let g_28 = (cyclegg_eq (Cyclegg_S cyclegg_x_50) cyclegg_xs_90) in
                              case g_28 of
                                (Cyclegg_False ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_False:g_28=Cyclegg_False =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_False:g_28=Cyclegg_False =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  prop_29_no_cyclic cyclegg_x cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_91 =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                                (Cyclegg_True ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_False =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_False:g_28=Cyclegg_True =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                                  ()
                          (Cyclegg_True ) ->
                            let g_28 = (cyclegg_eq (Cyclegg_S cyclegg_x_50) cyclegg_xs_90) in
                              case g_28 of
                                (Cyclegg_False ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_True:g_28=Cyclegg_False =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_True:g_28=Cyclegg_False =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  prop_29_no_cyclic cyclegg_x cyclegg_xs_91
                                  -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_91 =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                                (Cyclegg_True ) ->
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_True:g_28=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True:g_33=Cyclegg_True:g_57=Cyclegg_True =>
                                  -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True
                                  -- <= add guard scrutinee
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- add guard scrutinee =>
                                  -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_23=Cyclegg_True =>
                                  ()
        (Cyclegg_Nil ) ->
          -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_ins1 ?n Cyclegg_Nil) =>
          -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=Cyclegg_Nil
          -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
          -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
          -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50) =>
          -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
          -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_elem ?n Cyclegg_Nil) =>
          -- <= (cyclegg_elem ?n Cyclegg_Nil)
          -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=Cyclegg_Nil
          -- <= (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs))
          -- prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=Cyclegg_Nil =>
          -- <= (cyclegg_ins1 ?n Cyclegg_Nil)
          -- <= prop_29_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_50):cyclegg_xs=Cyclegg_Nil
          prop_29_no_cyclic cyclegg_x_50 cyclegg_xs
          -- ih-equality-cyclegg_x=cyclegg_x_50,cyclegg_xs=cyclegg_xs =>
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) ->
          let g_23 = (cyclegg_eq Cyclegg_Z cyclegg_xs_60) in
            case g_23 of
              (Cyclegg_False ) ->
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_23=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_23=Cyclegg_False =>
                prop_29_no_cyclic cyclegg_xs_60 cyclegg_xs_61
                -- <= ih-equality-cyclegg_x=cyclegg_xs_60,cyclegg_xs=cyclegg_xs_61
                ? prop_29_no_cyclic cyclegg_x cyclegg_xs_61
                -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_61 =>
                ? prop_29_no_cyclic cyclegg_xs_60 cyclegg_xs_61
                -- <= ih-equality-cyclegg_x=cyclegg_xs_60,cyclegg_xs=cyclegg_xs_61
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                ? prop_29_no_cyclic cyclegg_xs_60 cyclegg_xs_61
                -- ih-equality-cyclegg_x=cyclegg_xs_60,cyclegg_xs=cyclegg_xs_61 =>
              (Cyclegg_True ) ->
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                -- (cyclegg_ins1 ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_23=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- <= prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z =>
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z =>
                -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                -- <= prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_23=Cyclegg_True
                -- <= add guard scrutinee
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- add guard scrutinee =>
                -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_23=Cyclegg_True =>
                ()
        (Cyclegg_Nil ) ->
          -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_ins1 ?n Cyclegg_Nil) =>
          -- <= prop_29_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
          -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
          -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
          -- <= prop_29_no_cyclic:cyclegg_x=Cyclegg_Z
          -- <= prop_29_no_cyclic:cyclegg_x=Cyclegg_Z
          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
          -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- prop_29_no_cyclic:cyclegg_x=Cyclegg_Z =>
          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
          ()
