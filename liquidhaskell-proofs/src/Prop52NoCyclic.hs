{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_52_no_cyclic: (cyclegg_count cyclegg_n cyclegg_xs) = (cyclegg_count cyclegg_n (cyclegg_rev cyclegg_xs))
module Prop52NoCyclic where
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

{-@ reflect cyclegg_append @-}
cyclegg_append :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_append Cyclegg_Nil ys = ys
cyclegg_append (Cyclegg_Cons x xs) ys = (Cyclegg_Cons x (cyclegg_append xs ys))

{-@ reflect cyclegg_rev @-}
cyclegg_rev :: ((Cyclegg_List cyclegg_a) -> (Cyclegg_List cyclegg_a))
cyclegg_rev Cyclegg_Nil = Cyclegg_Nil
cyclegg_rev (Cyclegg_Cons x xs) = (cyclegg_append xs (Cyclegg_Cons x Cyclegg_Nil))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

{-@ reflect cyclegg_count @-}
cyclegg_count :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Cyclegg_Nat)
cyclegg_count x Cyclegg_Nil = Cyclegg_Z
cyclegg_count x (Cyclegg_Cons y ys) = (cyclegg_ite (cyclegg_eq x y) (Cyclegg_S (cyclegg_count x ys)) (cyclegg_count x ys))

{-@ type Pos = {v: Int | v >= 1 } @-}

{-@ measure natSize @-}
{-@ natSize :: Cyclegg_Nat -> Pos @-}
natSize :: Cyclegg_Nat -> Int
natSize Cyclegg_Z = 1
natSize (Cyclegg_S n) = 1 + natSize n

{-@ measure listSum @-}
{-@ listSum :: Cyclegg_List Cyclegg_Nat -> Pos @-}
listSum :: Cyclegg_List Cyclegg_Nat -> Int
listSum Cyclegg_Nil = 1
listSum (Cyclegg_Cons n xs) = 1 + natSize n + listSum xs

{-@ prop_52_no_cyclic :: cyclegg_n: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_count cyclegg_n cyclegg_xs) = (cyclegg_count cyclegg_n (cyclegg_rev cyclegg_xs)) } / [listSum cyclegg_xs] @-}
prop_52_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_52_no_cyclic cyclegg_n cyclegg_xs =
  case cyclegg_n of
    (Cyclegg_S cyclegg_n_50) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) ->
          let g_28 = (cyclegg_eq cyclegg_n_50 cyclegg_xs_90) in
            case g_28 of
              (Cyclegg_False ) ->
                let g_24 = (cyclegg_eq (Cyclegg_S cyclegg_n_50) cyclegg_xs_90) in
                  case g_24 of
                    (Cyclegg_False ) ->
                      case cyclegg_n_50 of
                        (Cyclegg_S cyclegg_n_50_300) ->
                          let g_50 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_90) in
                            case g_50 of
                              (Cyclegg_False ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_78 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_78 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_640 cyclegg_xs_91_641) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_640 cyclegg_xs_91_641) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_640 cyclegg_xs_91_641)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                              (Cyclegg_True ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_75 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_75 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                        (Cyclegg_Z ) ->
                          case cyclegg_xs_90 of
                            (Cyclegg_S cyclegg_xs_90_310) ->
                              let g_52 = (cyclegg_eq (Cyclegg_S Cyclegg_Z) cyclegg_xs_90_310) in
                                case g_52 of
                                  (Cyclegg_False ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91) =>
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461) =>
                                        -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_461)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_461)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_461)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_461)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_461) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_460 cyclegg_xs_91_461)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                                  (Cyclegg_True ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_470 cyclegg_xs_91_471) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_470 cyclegg_xs_91_471) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_470 cyclegg_xs_91_471)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                            (Cyclegg_Z ) ->
                              case cyclegg_xs_91 of
                                (Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381) ->
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- add guard scrutinee =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False
                                  -- <= add guard scrutinee
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False
                                  -- <= add guard scrutinee
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381)
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                (Cyclegg_Nil ) ->
                                  -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  ()
                    (Cyclegg_True ) ->
                      case cyclegg_n_50 of
                        (Cyclegg_S cyclegg_n_50_300) ->
                          let g_51 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_90) in
                            case g_51 of
                              (Cyclegg_False ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_75 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_75 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) ->
                                              let g_163 = (cyclegg_eq (Cyclegg_S cyclegg_n_50_300) cyclegg_xs_91_660) in
                                                case g_163 of
                                                  (Cyclegg_False ) ->
                                                    let g_156 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_91_660) in
                                                      case g_156 of
                                                        (Cyclegg_False ) ->
                                                          let g_166 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_660) in
                                                            case g_166 of
                                                              (Cyclegg_False ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_False:g_166=Cyclegg_False =>
                                                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_False:g_166=Cyclegg_False
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                              (Cyclegg_True ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_False:g_166=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_False:g_166=Cyclegg_True =>
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          let g_166 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_660) in
                                                            case g_166 of
                                                              (Cyclegg_False ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_True:g_166=Cyclegg_False =>
                                                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_True:g_166=Cyclegg_False
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                              (Cyclegg_True ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_True:g_166=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_False:g_156=Cyclegg_True:g_166=Cyclegg_True =>
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                  (Cyclegg_True ) ->
                                                    let g_156 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_91_660) in
                                                      case g_156 of
                                                        (Cyclegg_False ) ->
                                                          let g_166 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_660) in
                                                            case g_166 of
                                                              (Cyclegg_False ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_False:g_166=Cyclegg_False =>
                                                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_False:g_166=Cyclegg_False
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                              (Cyclegg_True ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_False:g_166=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_False:g_166=Cyclegg_True =>
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          let g_166 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_660) in
                                                            case g_166 of
                                                              (Cyclegg_False ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_True:g_166=Cyclegg_False =>
                                                                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_True:g_166=Cyclegg_False
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                              (Cyclegg_True ) ->
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_True:g_166=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                                -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                                -- add guard scrutinee =>
                                                                -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_163=Cyclegg_True:g_156=Cyclegg_True:g_166=Cyclegg_True =>
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                                -- <= add guard scrutinee
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                                -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                                -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                                -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                                -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                                -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                                -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z =>
                                        -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                              (Cyclegg_True ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_75 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_75 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) ->
                                              let g_164 = (cyclegg_eq (Cyclegg_S cyclegg_n_50_300) cyclegg_xs_91_670) in
                                                case g_164 of
                                                  (Cyclegg_False ) ->
                                                    let g_167 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_670) in
                                                      case g_167 of
                                                        (Cyclegg_False ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_False:g_167=Cyclegg_False =>
                                                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_False:g_167=Cyclegg_False
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_False:g_167=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_False:g_167=Cyclegg_True =>
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                  (Cyclegg_True ) ->
                                                    let g_167 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_670) in
                                                      case g_167 of
                                                        (Cyclegg_False ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_True:g_167=Cyclegg_False =>
                                                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_True:g_167=Cyclegg_False
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_True:g_167=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671):g_164=Cyclegg_True:g_167=Cyclegg_True =>
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z =>
                                        -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                        (Cyclegg_Z ) ->
                          case cyclegg_xs_90 of
                            (Cyclegg_S cyclegg_xs_90_310) ->
                              let g_53 = (cyclegg_eq (Cyclegg_S Cyclegg_Z) cyclegg_xs_90_310) in
                                case g_53 of
                                  (Cyclegg_False ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481) ->
                                        let g_121 = (cyclegg_eq (Cyclegg_S Cyclegg_Z) cyclegg_xs_91_480) in
                                          case g_121 of
                                            (Cyclegg_False ) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                              -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481):g_121=Cyclegg_False =>
                                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481):g_121=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_481)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_481) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_True ) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                              -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                              -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481):g_121=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481):g_121=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_481)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_481) =>
                                              -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_481)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_481) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_480 cyclegg_xs_91_481)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                                  (Cyclegg_True ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_470 cyclegg_xs_91_471) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91) =>
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_470 cyclegg_xs_91_471) =>
                                        -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_471)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_471)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_471)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_471)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_471) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_470 cyclegg_xs_91_471)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                            (Cyclegg_Z ) ->
                              case cyclegg_xs_91 of
                                (Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381) ->
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- add guard scrutinee =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- add guard scrutinee =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381)
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                (Cyclegg_Nil ) ->
                                  -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_False:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  ()
              (Cyclegg_True ) ->
                let g_24 = (cyclegg_eq (Cyclegg_S cyclegg_n_50) cyclegg_xs_90) in
                  case g_24 of
                    (Cyclegg_False ) ->
                      case cyclegg_n_50 of
                        (Cyclegg_S cyclegg_n_50_300) ->
                          let g_51 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_90) in
                            case g_51 of
                              (Cyclegg_False ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_75 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_75 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_661)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_671) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_670 cyclegg_xs_91_671)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                              (Cyclegg_True ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_75 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_75 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_51=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                        (Cyclegg_Z ) ->
                          case cyclegg_xs_90 of
                            (Cyclegg_S cyclegg_xs_90_310) ->
                              let g_53 = (cyclegg_eq (Cyclegg_S Cyclegg_Z) cyclegg_xs_90_310) in
                                case g_53 of
                                  (Cyclegg_False ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91) =>
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                                  (Cyclegg_True ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                        -- <= (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310)
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91) =>
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310) =>
                                        -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310) =>
                                        -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_53=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                            (Cyclegg_Z ) ->
                              case cyclegg_xs_91 of
                                (Cyclegg_Cons cyclegg_xs_91_350 cyclegg_xs_91_351) ->
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- add guard scrutinee =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_350 cyclegg_xs_91_351) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_351)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_351) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_351)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_351) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_350 cyclegg_xs_91_351)
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                (Cyclegg_Nil ) ->
                                  -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_False:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  ()
                    (Cyclegg_True ) ->
                      case cyclegg_n_50 of
                        (Cyclegg_S cyclegg_n_50_300) ->
                          let g_50 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_90) in
                            case g_50 of
                              (Cyclegg_False ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_75 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_75 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) ->
                                              let g_160 = (cyclegg_eq (Cyclegg_S cyclegg_n_50_300) cyclegg_xs_91_660) in
                                                case g_160 of
                                                  (Cyclegg_False ) ->
                                                    let g_163 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_660) in
                                                      case g_163 of
                                                        (Cyclegg_False ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_False:g_163=Cyclegg_False =>
                                                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_False:g_163=Cyclegg_False
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_False:g_163=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_False:g_163=Cyclegg_True =>
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                  (Cyclegg_True ) ->
                                                    let g_163 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_660) in
                                                      case g_163 of
                                                        (Cyclegg_False ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_True:g_163=Cyclegg_False =>
                                                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_True:g_163=Cyclegg_False
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_True:g_163=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661):g_160=Cyclegg_True:g_163=Cyclegg_True =>
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_661) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_660 cyclegg_xs_91_661)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_651)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_75=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z =>
                                        -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_False:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                              (Cyclegg_True ) ->
                                case cyclegg_xs_90 of
                                  (Cyclegg_S cyclegg_xs_90_450) ->
                                    let g_78 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_90_450) in
                                      case g_78 of
                                        (Cyclegg_False ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) ->
                                              let g_166 = (cyclegg_eq cyclegg_n_50_300 cyclegg_xs_91_650) in
                                                case g_166 of
                                                  (Cyclegg_False ) ->
                                                    let g_157 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_650) in
                                                      case g_157 of
                                                        (Cyclegg_False ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_False:g_157=Cyclegg_False =>
                                                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_False:g_157=Cyclegg_False
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_False:g_157=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_False:g_157=Cyclegg_True =>
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                  (Cyclegg_True ) ->
                                                    let g_157 = (cyclegg_eq (Cyclegg_S (Cyclegg_S cyclegg_n_50_300)) cyclegg_xs_91_650) in
                                                      case g_157 of
                                                        (Cyclegg_False ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_True:g_157=Cyclegg_False =>
                                                          -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_True:g_157=Cyclegg_False
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                                        (Cyclegg_True ) ->
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                                          -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_True:g_157=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651) =>
                                                          -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                                          -- add guard scrutinee =>
                                                          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651):g_166=Cyclegg_True:g_157=Cyclegg_True =>
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                                          -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                                          -- <= add guard scrutinee
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651)
                                                          -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_651) =>
                                                          -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                                          -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                                          -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_650 cyclegg_xs_91_651)
                                                          -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                                          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                        (Cyclegg_True ) ->
                                          case cyclegg_xs_91 of
                                            (Cyclegg_Cons cyclegg_xs_91_640 cyclegg_xs_91_641) ->
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91) =>
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_640 cyclegg_xs_91_641) =>
                                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641) =>
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_450 cyclegg_xs_91_641)
                                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                              -- add guard scrutinee =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True =>
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                              -- <= add guard scrutinee
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641)
                                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_641) =>
                                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_640 cyclegg_xs_91_641)
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                            (Cyclegg_Nil ) ->
                                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                              -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_450):g_78=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                              -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                              ()
                                  (Cyclegg_Z ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z =>
                                        -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                        -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=(Cyclegg_S cyclegg_n_50_300):g_50=Cyclegg_True:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                        (Cyclegg_Z ) ->
                          case cyclegg_xs_90 of
                            (Cyclegg_S cyclegg_xs_90_310) ->
                              let g_52 = (cyclegg_eq (Cyclegg_S Cyclegg_Z) cyclegg_xs_90_310) in
                                case g_52 of
                                  (Cyclegg_False ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310) =>
                                        -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91) =>
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False =>
                                        -- <= (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310)
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False =>
                                        -- <= (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310)
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_False:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                                  (Cyclegg_True ) ->
                                    case cyclegg_xs_91 of
                                      (Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) ->
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91) =>
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501) =>
                                        -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90_310 cyclegg_xs_91_501)
                                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                        -- add guard scrutinee =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True =>
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True
                                        -- <= add guard scrutinee
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501)
                                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_501) =>
                                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_500 cyclegg_xs_91_501)
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                      (Cyclegg_Nil ) ->
                                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                        -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=(Cyclegg_S cyclegg_xs_90_310):g_52=Cyclegg_True:cyclegg_xs_91=Cyclegg_Nil =>
                                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                        -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                        ()
                            (Cyclegg_Z ) ->
                              case cyclegg_xs_91 of
                                (Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381) ->
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z) =>
                                  -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381) =>
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- add guard scrutinee =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381) =>
                                  -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                                  -- <= (cyclegg_eq (Cyclegg_S ?x) Cyclegg_Z)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- add guard scrutinee =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True =>
                                  -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381)
                                  -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91_381) =>
                                  -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z
                                  -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z =>
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z
                                  -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=(Cyclegg_Cons cyclegg_xs_91_380 cyclegg_xs_91_381)
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                (Cyclegg_Nil ) ->
                                  -- <= (cyclegg_append Cyclegg_Nil ?ys)
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91) =>
                                  -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91):g_28=Cyclegg_True:g_24=Cyclegg_True:cyclegg_n_50=Cyclegg_Z:cyclegg_xs_90=Cyclegg_Z:cyclegg_xs_91=Cyclegg_Nil =>
                                  -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                                  -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_90 cyclegg_xs_91)
                                  ()
        (Cyclegg_Nil ) ->
          -- prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=Cyclegg_Nil =>
          -- <= (cyclegg_rev Cyclegg_Nil)
          -- <= prop_52_no_cyclic:cyclegg_n=(Cyclegg_S cyclegg_n_50):cyclegg_xs=Cyclegg_Nil
          ()
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) ->
          let g_19 = (cyclegg_eq Cyclegg_Z cyclegg_xs_60) in
            case g_19 of
              (Cyclegg_False ) ->
                case cyclegg_xs_60 of
                  (Cyclegg_S cyclegg_xs_60_200) ->
                    let g_35 = (cyclegg_eq Cyclegg_Z cyclegg_xs_60_200) in
                      case g_35 of
                        (Cyclegg_False ) ->
                          case cyclegg_xs_61 of
                            (Cyclegg_Cons cyclegg_xs_61_310 cyclegg_xs_61_311) ->
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61) =>
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_310 cyclegg_xs_61_311) =>
                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_311)
                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_311)
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_311)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_311) =>
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_311)
                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_311)
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_311)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_311) =>
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_310 cyclegg_xs_61_311)
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                            (Cyclegg_Nil ) ->
                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=Cyclegg_Nil
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=Cyclegg_Nil =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                              ()
                        (Cyclegg_True ) ->
                          case cyclegg_xs_61 of
                            (Cyclegg_Cons cyclegg_xs_61_320 cyclegg_xs_61_321) ->
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False =>
                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_320 cyclegg_xs_61_321) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_321)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_321) =>
                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_321)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_321) =>
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_320 cyclegg_xs_61_321)
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                            (Cyclegg_Nil ) ->
                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=Cyclegg_Nil
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=Cyclegg_Nil =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                              ()
                  (Cyclegg_Z ) ->
                    case cyclegg_xs_61 of
                      (Cyclegg_Cons cyclegg_xs_61_250 cyclegg_xs_61_251) ->
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                        -- add guard scrutinee =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False =>
                        -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_250 cyclegg_xs_61_251) =>
                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False
                        -- <= add guard scrutinee
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z
                        prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_251)
                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_251) =>
                        -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False
                        -- <= add guard scrutinee
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                        -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- (cyclegg_eq Cyclegg_Z Cyclegg_Z) =>
                        -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z
                        ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_251)
                        -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_251) =>
                        -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                        -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z
                        -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_250 cyclegg_xs_61_251)
                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                      (Cyclegg_Nil ) ->
                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=Cyclegg_Nil
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_False:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=Cyclegg_Nil =>
                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                        ()
              (Cyclegg_True ) ->
                case cyclegg_xs_60 of
                  (Cyclegg_S cyclegg_xs_60_200) ->
                    let g_35 = (cyclegg_eq Cyclegg_Z cyclegg_xs_60_200) in
                      case g_35 of
                        (Cyclegg_False ) ->
                          case cyclegg_xs_61 of
                            (Cyclegg_Cons cyclegg_xs_61_340 cyclegg_xs_61_341) ->
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200) =>
                              -- (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y)) =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61) =>
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_340 cyclegg_xs_61_341) =>
                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False =>
                              -- <= (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200)
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341) =>
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False =>
                              -- <= (cyclegg_eq Cyclegg_Z (Cyclegg_S ?y))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200)
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341) =>
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_340 cyclegg_xs_61_341)
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                            (Cyclegg_Nil ) ->
                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=Cyclegg_Nil
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_False:cyclegg_xs_61=Cyclegg_Nil =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                              ()
                        (Cyclegg_True ) ->
                          case cyclegg_xs_61 of
                            (Cyclegg_Cons cyclegg_xs_61_340 cyclegg_xs_61_341) ->
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61) =>
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_340 cyclegg_xs_61_341) =>
                              -- (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys) =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341) =>
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- <= ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60_200 cyclegg_xs_61_341)
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True
                              -- <= add guard scrutinee
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_341) =>
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_340 cyclegg_xs_61_341)
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                            (Cyclegg_Nil ) ->
                              -- <= (cyclegg_append Cyclegg_Nil ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=Cyclegg_Nil
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=(Cyclegg_S cyclegg_xs_60_200):g_35=Cyclegg_True:cyclegg_xs_61=Cyclegg_Nil =>
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                              ()
                  (Cyclegg_Z ) ->
                    case cyclegg_xs_61 of
                      (Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231) ->
                        let g_66 = (cyclegg_eq Cyclegg_Z cyclegg_xs_61_230) in
                          case g_66 of
                            (Cyclegg_False ) ->
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True =>
                              -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231):g_66=Cyclegg_False =>
                              -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                              -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z
                              -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                              -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                              -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z
                              -- <= (cyclegg_ite Cyclegg_False ?x ?y)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231):g_66=Cyclegg_False
                              -- <= add guard scrutinee
                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_231)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_231) =>
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z
                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231)
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                            (Cyclegg_True ) ->
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True =>
                              -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231) =>
                              -- (cyclegg_count ?x (Cyclegg_Cons ?y ?ys)) =>
                              -- add guard scrutinee =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231):g_66=Cyclegg_True =>
                              -- <= (cyclegg_eq Cyclegg_Z Cyclegg_Z)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z
                              prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_231)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_231) =>
                              -- <= (cyclegg_ite Cyclegg_True ?x ?y)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231):g_66=Cyclegg_True
                              -- <= add guard scrutinee
                              ? prop_52_no_cyclic cyclegg_n (Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_231)
                              -- ih-equality-cyclegg_n=cyclegg_n,cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61_231) =>
                              -- <= (cyclegg_count ?x (Cyclegg_Cons ?y ?ys))
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z
                              -- (cyclegg_rev (Cyclegg_Cons ?x ?xs)) =>
                              -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z =>
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z
                              -- <= (cyclegg_append (Cyclegg_Cons ?x ?xs) ?ys)
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=(Cyclegg_Cons cyclegg_xs_61_230 cyclegg_xs_61_231)
                              -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                              -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                      (Cyclegg_Nil ) ->
                        -- <= (cyclegg_append Cyclegg_Nil ?ys)
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=Cyclegg_Nil
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61) =>
                        -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61):g_19=Cyclegg_True:cyclegg_xs_60=Cyclegg_Z:cyclegg_xs_61=Cyclegg_Nil =>
                        -- <= (cyclegg_rev (Cyclegg_Cons ?x ?xs))
                        -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_60 cyclegg_xs_61)
                        ()
        (Cyclegg_Nil ) ->
          -- prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- <= (cyclegg_rev Cyclegg_Nil)
          -- <= prop_52_no_cyclic:cyclegg_n=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil
          ()
