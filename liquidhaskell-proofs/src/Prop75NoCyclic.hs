{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_75_no_cyclic: (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m Cyclegg_Nil))) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m cyclegg_xs))
module Prop75NoCyclic where
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

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_add @-}
cyclegg_add :: (Cyclegg_Nat -> Cyclegg_Nat -> Cyclegg_Nat)
cyclegg_add Cyclegg_Z y = y
cyclegg_add (Cyclegg_S x) y = (Cyclegg_S (cyclegg_add x y))

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

{-@ prop_75_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_m: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_add (cyclegg_count cyclegg_n cyclegg_xs) (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m Cyclegg_Nil))) = (cyclegg_count cyclegg_n (Cyclegg_Cons cyclegg_m cyclegg_xs)) } @-}
prop_75_no_cyclic :: Cyclegg_Nat -> Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs =
  let g_10 = (cyclegg_eq cyclegg_n cyclegg_m) in
    case g_10 of
      (Cyclegg_False ) ->
        case cyclegg_n of
          (Cyclegg_S cyclegg_n_200) ->
            let g_27 = (cyclegg_eq cyclegg_n_200 cyclegg_m) in
              case g_27 of
                (Cyclegg_False ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_51 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_51 of
                          (Cyclegg_False ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            prop_75_no_cyclic cyclegg_n cyclegg_m_370 cyclegg_xs
                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_370,cyclegg_xs=cyclegg_xs =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_False =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          (Cyclegg_True ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) ->
                                let g_100 = (cyclegg_eq cyclegg_n_200 cyclegg_xs_560) in
                                  case g_100 of
                                    (Cyclegg_False ) ->
                                      let g_97 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) in
                                        case g_97 of
                                          (Cyclegg_False ) ->
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_False:g_97=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_561
                                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_561 =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_False:g_97=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                          (Cyclegg_True ) ->
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_False:g_97=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_561
                                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_561 =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_False:g_97=Cyclegg_True
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      let g_97 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) in
                                        case g_97 of
                                          (Cyclegg_False ) ->
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_True:g_97=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_561
                                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_561 =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_True:g_97=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                          (Cyclegg_True ) ->
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_True:g_97=Cyclegg_True =>
                                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_561
                                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_561 =>
                                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                            -- add guard scrutinee =>
                                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                            -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_True:g_97=Cyclegg_True
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                            -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                            -- <= add guard scrutinee
                                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_add Cyclegg_Z ?y) =>
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_51=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                                ()
                    (Cyclegg_Z ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) ->
                          let g_83 = (cyclegg_eq cyclegg_n_200 cyclegg_xs_410) in
                            case g_83 of
                              (Cyclegg_False ) ->
                                let g_80 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) in
                                  case g_80 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_False:g_80=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_False:g_80=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_False:g_80=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_False:g_80=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                let g_80 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) in
                                  case g_80 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_True:g_80=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_True:g_80=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_True:g_80=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_83=Cyclegg_True:g_80=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- (cyclegg_add Cyclegg_Z ?y) =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          ()
                (Cyclegg_True ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_55 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_55 of
                          (Cyclegg_False ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_False
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            prop_75_no_cyclic cyclegg_n cyclegg_m_370 cyclegg_xs
                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_370,cyclegg_xs=cyclegg_xs =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_False =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          (Cyclegg_True ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) ->
                                let g_103 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) in
                                  case g_103 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_103=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_581
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_581 =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_103=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_103=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_581
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_581 =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_103=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_add Cyclegg_Z ?y) =>
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_55=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                                ()
                    (Cyclegg_Z ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) ->
                          let g_86 = (cyclegg_eq cyclegg_n_200 cyclegg_xs_410) in
                            case g_86 of
                              (Cyclegg_False ) ->
                                let g_82 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) in
                                  case g_82 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_False:g_82=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_False:g_82=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_False:g_82=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_False:g_82=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                let g_82 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_410) in
                                  case g_82 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_True:g_82=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_True:g_82=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_True:g_82=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_411
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_411 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411):g_86=Cyclegg_True:g_82=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_410 cyclegg_xs_411)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- (cyclegg_add Cyclegg_Z ?y) =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_27=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          ()
          (Cyclegg_Z ) ->
            case cyclegg_m of
              (Cyclegg_S cyclegg_m_230) ->
                let g_33 = (cyclegg_eq Cyclegg_Z cyclegg_m_230) in
                  case g_33 of
                    (Cyclegg_False ) ->
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_False
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                      prop_75_no_cyclic cyclegg_n cyclegg_m_230 cyclegg_xs
                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_230,cyclegg_xs=cyclegg_xs =>
                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                      -- add guard scrutinee =>
                      -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_False =>
                      -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                      -- <= add guard scrutinee
                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_True ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361) ->
                          let g_66 = (cyclegg_eq Cyclegg_Z cyclegg_xs_360) in
                            case g_66 of
                              (Cyclegg_False ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_66=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_361
                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_361 =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_66=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_66=Cyclegg_True =>
                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                                -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_361
                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_361 =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361):g_66=Cyclegg_True
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_360 cyclegg_xs_361)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                          -- (cyclegg_add Cyclegg_Z ?y) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_230):g_33=Cyclegg_True:cyclegg_xs=Cyclegg_Nil
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          ()
              (Cyclegg_Z ) ->
                case cyclegg_xs of
                  (Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301) ->
                    let g_68 = (cyclegg_eq Cyclegg_Z cyclegg_xs_300) in
                      case g_68 of
                        (Cyclegg_False ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301):g_68=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_301
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_301 =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301):g_68=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301)
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_True ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301):g_68=Cyclegg_True =>
                          -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_301
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_301 =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301):g_68=Cyclegg_True
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_300 cyclegg_xs_301)
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  (Cyclegg_Nil ) ->
                    -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                    -- (cyclegg_count ?x Cyclegg_Nil) =>
                    -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                    -- add guard scrutinee =>
                    -- prop_75_no_cyclic:g_10=Cyclegg_False =>
                    -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                    -- (cyclegg_count ?x Cyclegg_Nil) =>
                    -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z
                    -- (cyclegg_add Cyclegg_Z ?y) =>
                    -- prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z =>
                    -- <= (cyclegg_count ?x Cyclegg_Nil)
                    -- <= prop_75_no_cyclic:g_10=Cyclegg_False:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                    -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                    -- <= prop_75_no_cyclic:g_10=Cyclegg_False
                    -- <= add guard scrutinee
                    -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    ()
      (Cyclegg_True ) ->
        case cyclegg_n of
          (Cyclegg_S cyclegg_n_200) ->
            let g_28 = (cyclegg_eq cyclegg_n_200 cyclegg_m) in
              case g_28 of
                (Cyclegg_False ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_56 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_56 of
                          (Cyclegg_False ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) ->
                                let g_101 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_580) in
                                  case g_101 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_101=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_581
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_581 =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_101=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_101=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_581
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_581 =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581):g_101=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_580 cyclegg_xs_581)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_add Cyclegg_Z ?y) =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                                ()
                          (Cyclegg_True ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_True
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            prop_75_no_cyclic cyclegg_n cyclegg_m_370 cyclegg_xs
                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_370,cyclegg_xs=cyclegg_xs =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_56=Cyclegg_True =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_Z ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471) ->
                          let g_98 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_470) in
                            case g_98 of
                              (Cyclegg_False ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471):g_98=Cyclegg_False =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_471
                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_471 =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471):g_98=Cyclegg_False
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471) =>
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471):g_98=Cyclegg_True =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                -- <= add guard scrutinee
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_471
                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_471 =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                                -- <= (cyclegg_count ?x Cyclegg_Nil)
                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z
                                -- add guard scrutinee =>
                                -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471):g_98=Cyclegg_True
                                -- <= add guard scrutinee
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_470 cyclegg_xs_471)
                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z
                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z =>
                          -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False
                          -- <= add guard scrutinee
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          prop_75_no_cyclic cyclegg_n_200 cyclegg_m cyclegg_xs
                          -- ih-equality-cyclegg_n=cyclegg_n_200,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_False:cyclegg_m=Cyclegg_Z
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                (Cyclegg_True ) ->
                  case cyclegg_m of
                    (Cyclegg_S cyclegg_m_370) ->
                      let g_52 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_m_370) in
                        case g_52 of
                          (Cyclegg_False ) ->
                            case cyclegg_xs of
                              (Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) ->
                                let g_100 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_560) in
                                  case g_100 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_561
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_561 =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_True =>
                                      -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                      -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_561
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_561 =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561):g_100=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_560 cyclegg_xs_561)
                                      -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_Nil ) ->
                                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=Cyclegg_Nil =>
                                -- (cyclegg_count ?x Cyclegg_Nil) =>
                                -- (cyclegg_add Cyclegg_Z ?y) =>
                                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_False:cyclegg_xs=Cyclegg_Nil
                                ()
                          (Cyclegg_True ) ->
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_True
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                            prop_75_no_cyclic cyclegg_n cyclegg_m_370 cyclegg_xs
                            -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_370,cyclegg_xs=cyclegg_xs =>
                            -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                            -- add guard scrutinee =>
                            -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=(Cyclegg_S cyclegg_m_370):g_52=Cyclegg_True =>
                            -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                            -- <= add guard scrutinee
                            -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                    (Cyclegg_Z ) ->
                      case cyclegg_xs of
                        (Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481) ->
                          let g_94 = (cyclegg_eq cyclegg_n_200 cyclegg_xs_480) in
                            case g_94 of
                              (Cyclegg_False ) ->
                                let g_98 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_480) in
                                  case g_98 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_False:g_98=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_481
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_481 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_False:g_98=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_False:g_98=Cyclegg_True =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_481
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_481 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_False:g_98=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              (Cyclegg_True ) ->
                                let g_98 = (cyclegg_eq (Cyclegg_S cyclegg_n_200) cyclegg_xs_480) in
                                  case g_98 of
                                    (Cyclegg_False ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_True:g_98=Cyclegg_False =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_481
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_481 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_True:g_98=Cyclegg_False
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                    (Cyclegg_True ) ->
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481) =>
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_True:g_98=Cyclegg_True =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200) =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                      -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                      prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_481
                                      -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_481 =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z =>
                                      -- <= (cyclegg_count ?x Cyclegg_Nil)
                                      -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                      -- (cyclegg_count ?x Cyclegg_Nil) =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                      -- add guard scrutinee =>
                                      -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481):g_94=Cyclegg_True:g_98=Cyclegg_True
                                      -- <= add guard scrutinee
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_480 cyclegg_xs_481)
                                      -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                      -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200)
                                      -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z
                                      -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        (Cyclegg_Nil ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True
                          -- <= add guard scrutinee
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          prop_75_no_cyclic cyclegg_n_200 cyclegg_m cyclegg_xs
                          -- ih-equality-cyclegg_n=cyclegg_n_200,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                          -- <= add guard scrutinee
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- (cyclegg_count ?x Cyclegg_Nil) =>
                          -- <= (cyclegg_count ?x Cyclegg_Nil)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=(Cyclegg_S cyclegg_n_200):g_28=Cyclegg_True:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          (Cyclegg_Z ) ->
            case cyclegg_m of
              (Cyclegg_S cyclegg_m_220) ->
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                -- <= (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y))
                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_220)
                -- add guard scrutinee =>
                -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- add guard scrutinee =>
                -- prop_75_no_cyclic:g_10=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                -- (cyclegg_count ?x Cyclegg_Nil) =>
                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_220) =>
                -- (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y)) =>
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                prop_75_no_cyclic cyclegg_n cyclegg_m_220 cyclegg_xs
                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m_220,cyclegg_xs=cyclegg_xs =>
                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                -- <= (cyclegg_eq (Cyclegg_S ?x) (Cyclegg_S ?y))
                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                -- <= (cyclegg_count ?x Cyclegg_Nil)
                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                -- <= add guard scrutinee
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                -- <= add guard scrutinee
                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_220) =>
                -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=(Cyclegg_S cyclegg_m_220)
                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
              (Cyclegg_Z ) ->
                case cyclegg_xs of
                  (Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251) ->
                    let g_51 = (cyclegg_eq Cyclegg_Z cyclegg_xs_250) in
                      case g_51 of
                        (Cyclegg_False ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_51=Cyclegg_False =>
                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                          prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_251
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_251 =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_51=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251)
                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_51=Cyclegg_False
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251)
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z
                        (Cyclegg_True ) ->
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251) =>
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- add guard scrutinee =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_51=Cyclegg_True =>
                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                          -- (cyclegg_add (Cyclegg_S ?x) ?y) =>
                          prop_75_no_cyclic cyclegg_n cyclegg_m cyclegg_xs_251
                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_m=cyclegg_m,cyclegg_xs=cyclegg_xs_251 =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z
                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z =>
                          -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251):g_51=Cyclegg_True
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_250 cyclegg_xs_251)
                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                          -- <= prop_75_no_cyclic:g_10=Cyclegg_True
                          -- <= add guard scrutinee
                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                  (Cyclegg_Nil ) ->
                    -- prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
                    -- (cyclegg_count ?x Cyclegg_Nil) =>
                    -- (cyclegg_add Cyclegg_Z ?y) =>
                    -- <= prop_75_no_cyclic:g_10=Cyclegg_True:cyclegg_n=Cyclegg_Z:cyclegg_m=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
                    ()

