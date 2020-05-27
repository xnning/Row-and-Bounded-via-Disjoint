
Require Import Syntax_ott.
Require Import TypeSystems.
Require Import Metalib.Metatheory.

(* ********************************************************************** *)
(** * Well-known properties of System F *)

Definition halts t  :=
  exists t',  value t' /\ t ->* t'.

Axiom normalization : forall t T,
    typ nil nil t T ->
    halts t.

Axiom ty_absurd : forall e,
    typ nil nil e (ty_all (ty_var_b 0)) -> False.


(* ********************************************************************** *)
(** * Hairy Renaming due to locally-nameless encoding *)

Axiom has_typ_rename_var : forall D A G EE B ee X Y,
   has_type D ((X, A) :: G) (open_sexp_wrt_sexp EE (sexp_var_f X)) Inf B ee ->
   X `notin` fv_sexp_in_sexp EE \u fv_sty_in_sty B ->
   Y `notin` fv_sexp_in_sexp EE \u fv_sty_in_sty B ->
   has_type D ((Y, A) :: G) (open_sexp_wrt_sexp EE (sexp_var_f Y)) Inf B
                            (subst_exp_in_exp (exp_var_f Y) X ee).

Axiom has_typ_rename_tvar : forall X A D G EE C ee Y,
    has_type ((X, A) :: D) G (open_sexp_wrt_sty EE (sty_var_f X)) Inf
                             (open_sty_wrt_sty C (sty_var_f X)) ee ->
  X `notin` fv_sty_in_sexp EE \u fv_sexp_in_sexp EE \u fv_sty_in_sty C ->
  Y `notin` fv_sty_in_sexp EE \u fv_sexp_in_sexp EE \u fv_sty_in_sty C ->
  has_type ((Y, A) :: D) G (open_sexp_wrt_sty EE (sty_var_f Y)) Inf
                           (open_sty_wrt_sty C (sty_var_f Y))
                           (subst_ty_in_exp (ty_var_f Y) X ee).