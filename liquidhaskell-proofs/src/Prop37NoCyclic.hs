{-# LANGUAGE GADTSyntax #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- prop_37_no_cyclic: (cyclegg_not (cyclegg_elem cyclegg_x (cyclegg_delete cyclegg_x cyclegg_xs))) = (Cyclegg_True)
module Prop37NoCyclic where
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

{-@ reflect cyclegg_delete @-}
cyclegg_delete :: (Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> (Cyclegg_List Cyclegg_Nat))
cyclegg_delete n Cyclegg_Nil = Cyclegg_Nil
cyclegg_delete n (Cyclegg_Cons x xs) = (cyclegg_ite (cyclegg_eq n x) (cyclegg_delete n xs) (Cyclegg_Cons x (cyclegg_delete n xs)))

{-@ reflect cyclegg_ite @-}
cyclegg_ite :: (Cyclegg_Bool -> cyclegg_a -> cyclegg_a -> cyclegg_a)
cyclegg_ite Cyclegg_True x y = x
cyclegg_ite Cyclegg_False x y = y

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

{-@ reflect cyclegg_not @-}
cyclegg_not :: (Cyclegg_Bool -> Cyclegg_Bool)
cyclegg_not Cyclegg_True = Cyclegg_False
cyclegg_not Cyclegg_False = Cyclegg_True

{-@ prop_37_no_cyclic :: cyclegg_x: Cyclegg_Nat -> cyclegg_xs: (Cyclegg_List Cyclegg_Nat) -> { (cyclegg_not (cyclegg_elem cyclegg_x (cyclegg_delete cyclegg_x cyclegg_xs))) = (Cyclegg_True) } @-}
prop_37_no_cyclic :: Cyclegg_Nat -> (Cyclegg_List Cyclegg_Nat) -> Proof
prop_37_no_cyclic cyclegg_x cyclegg_xs =
  case cyclegg_x of
    (Cyclegg_S cyclegg_x_60) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) ->
          let g_38 = (cyclegg_eq cyclegg_xs_110 cyclegg_xs_110) in
            case g_38 of
              (Cyclegg_False ) ->
                let g_34 = (cyclegg_eq cyclegg_x_60 cyclegg_xs_110) in
                  case g_34 of
                    (Cyclegg_False ) ->
                      let g_30 = (cyclegg_eq (Cyclegg_S cyclegg_x_60) cyclegg_xs_110) in
                        case g_30 of
                          (Cyclegg_False ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_False:g_30=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_False:g_30=Cyclegg_False =>
                            prop_37_no_cyclic cyclegg_xs_110 cyclegg_xs_111
                            -- <= ih-equality-cyclegg_x=cyclegg_xs_110,cyclegg_xs=cyclegg_xs_111
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            ? prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
                          (Cyclegg_True ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_False:g_30=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
                    (Cyclegg_True ) ->
                      let g_30 = (cyclegg_eq (Cyclegg_S cyclegg_x_60) cyclegg_xs_110) in
                        case g_30 of
                          (Cyclegg_False ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_True:g_30=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_True:g_30=Cyclegg_False =>
                            -- <= prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_True
                            -- <= add guard scrutinee
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
                          (Cyclegg_True ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_False:g_34=Cyclegg_True:g_30=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
              (Cyclegg_True ) ->
                let g_34 = (cyclegg_eq cyclegg_x_60 cyclegg_xs_110) in
                  case g_34 of
                    (Cyclegg_False ) ->
                      let g_30 = (cyclegg_eq (Cyclegg_S cyclegg_x_60) cyclegg_xs_110) in
                        case g_30 of
                          (Cyclegg_False ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_False:g_30=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_False:g_30=Cyclegg_False =>
                            -- <= prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True
                            -- <= add guard scrutinee
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
                          (Cyclegg_True ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_False:g_30=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
                    (Cyclegg_True ) ->
                      let g_30 = (cyclegg_eq (Cyclegg_S cyclegg_x_60) cyclegg_xs_110) in
                        case g_30 of
                          (Cyclegg_False ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_True:g_30=Cyclegg_False =>
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_True:g_30=Cyclegg_False =>
                            -- <= prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_True
                            -- <= add guard scrutinee
                            -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
                          (Cyclegg_True ) ->
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111) =>
                            -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                            -- add guard scrutinee =>
                            -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=(Cyclegg_Cons cyclegg_xs_110 cyclegg_xs_111):g_38=Cyclegg_True:g_34=Cyclegg_True:g_30=Cyclegg_True =>
                            -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                            prop_37_no_cyclic cyclegg_x cyclegg_xs_111
                            -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_111 =>
        (Cyclegg_Nil ) ->
          -- prop_37_no_cyclic:cyclegg_x=(Cyclegg_S cyclegg_x_60):cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_delete ?n Cyclegg_Nil) =>
          -- (cyclegg_elem ?n Cyclegg_Nil) =>
          -- (cyclegg_not Cyclegg_False) =>
          ()
    (Cyclegg_Z ) ->
      case cyclegg_xs of
        (Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) ->
          let g_27 = (cyclegg_eq Cyclegg_Z cyclegg_xs_70) in
            case g_27 of
              (Cyclegg_False ) ->
                -- prop_37_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
                -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_37_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_27=Cyclegg_False =>
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                -- (cyclegg_elem ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_37_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_27=Cyclegg_False =>
                prop_37_no_cyclic cyclegg_xs_70 cyclegg_xs_71
                -- <= ih-equality-cyclegg_x=cyclegg_xs_70,cyclegg_xs=cyclegg_xs_71
                -- (cyclegg_ite Cyclegg_False ?x ?y) =>
                ? prop_37_no_cyclic cyclegg_x cyclegg_xs_71
                -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_71 =>
              (Cyclegg_True ) ->
                -- prop_37_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71) =>
                -- (cyclegg_delete ?n (Cyclegg_Cons ?x ?xs)) =>
                -- add guard scrutinee =>
                -- prop_37_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=(Cyclegg_Cons cyclegg_xs_70 cyclegg_xs_71):g_27=Cyclegg_True =>
                -- (cyclegg_ite Cyclegg_True ?x ?y) =>
                prop_37_no_cyclic cyclegg_x cyclegg_xs_71
                -- ih-equality-cyclegg_x=cyclegg_x,cyclegg_xs=cyclegg_xs_71 =>
        (Cyclegg_Nil ) ->
          -- prop_37_no_cyclic:cyclegg_x=Cyclegg_Z:cyclegg_xs=Cyclegg_Nil =>
          -- (cyclegg_delete ?n Cyclegg_Nil) =>
          -- (cyclegg_elem ?n Cyclegg_Nil) =>
          -- (cyclegg_not Cyclegg_False) =>
          ()
