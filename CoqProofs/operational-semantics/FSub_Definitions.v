
(** Definition of Fsub (System F with subtyping).

    Adapted from Metalib
*)

Require Export Metalib.Metatheory.


(* ********************************************************************** *)
(** * Syntax *)

Definition i := nat.

Inductive ftyp : Set :=
  | ftyp_top : ftyp
  | ftyp_nat : ftyp
  | ftyp_bvar : nat -> ftyp
  | ftyp_fvar : atom -> ftyp
  | ftyp_arrow : ftyp -> ftyp -> ftyp
  | ftyp_all : ftyp -> ftyp -> ftyp
  | ftyp_rcd_nil : ftyp
  | ftyp_rcd_cons : i -> ftyp -> ftyp -> ftyp
.

Inductive fexp : Set :=
  | fexp_top : fexp
  | fexp_lit : i -> fexp
  | fexp_bvar : nat -> fexp
  | fexp_fvar : atom -> fexp
  | fexp_abs : ftyp -> fexp -> fexp
  | fexp_app : fexp -> fexp -> fexp
  | fexp_tabs : ftyp -> fexp -> fexp
  | fexp_tapp : fexp -> ftyp -> fexp
  | fexp_rcd_nil : fexp
  | fexp_rcd_cons : i -> fexp -> fexp -> fexp
  | fexp_rcd_proj : fexp -> i -> fexp
.

Coercion ftyp_bvar : nat >-> ftyp.
Coercion ftyp_fvar : atom >-> ftyp.
Coercion fexp_bvar : nat >-> fexp.
Coercion fexp_fvar : atom >-> fexp.


(* ********************************************************************** *)
(** * Open *)

Fixpoint open_tt_rec (K : nat) (U : ftyp) (T : ftyp)  {struct T} : ftyp :=
  match T with
  | ftyp_top => ftyp_top
  | ftyp_rcd_nil => ftyp_rcd_nil
  | ftyp_rcd_cons i T1 T2  => ftyp_rcd_cons i (open_tt_rec K U T1) (open_tt_rec K U T2)
  | ftyp_nat => ftyp_nat
  | ftyp_bvar J => if K == J then U else (ftyp_bvar J)
  | ftyp_fvar X => ftyp_fvar X
  | ftyp_arrow T1 T2 => ftyp_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | ftyp_all T1 T2 => ftyp_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : ftyp) (e : fexp) {struct e} : fexp :=
  match e with
  | fexp_top => fexp_top
  | fexp_rcd_nil => fexp_rcd_nil
  | fexp_rcd_cons i e1 e2 => fexp_rcd_cons i (open_te_rec K U e1) (open_te_rec K U e2)
  | fexp_rcd_proj e1 i => fexp_rcd_proj (open_te_rec K U e1) i
  | fexp_lit i => fexp_lit i
  | fexp_bvar i => fexp_bvar i
  | fexp_fvar x => fexp_fvar x
  | fexp_abs V e1 => fexp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | fexp_app e1 e2 => fexp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | fexp_tabs V e1 => fexp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | fexp_tapp e1 V => fexp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Fixpoint open_ee_rec (k : nat) (f : fexp) (e : fexp)  {struct e} : fexp :=
  match e with
  | fexp_top => fexp_top
  | fexp_rcd_nil => fexp_rcd_nil
  | fexp_rcd_cons i e1 e2 => fexp_rcd_cons i (open_ee_rec k f e1) (open_ee_rec k f e2)
  | fexp_rcd_proj e1 i => fexp_rcd_proj (open_ee_rec k f e1) i
  | fexp_lit i => fexp_lit i
  | fexp_bvar i => if k == i then f else (fexp_bvar i)
  | fexp_fvar x => fexp_fvar x
  | fexp_abs V e1 => fexp_abs V (open_ee_rec (S k) f e1)
  | fexp_app e1 e2 => fexp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | fexp_tabs V e1 => fexp_tabs V (open_ee_rec k f e1)
  | fexp_tapp e1 V => fexp_tapp (open_ee_rec k f e1) V
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.


(* ********************************************************************** *)
(** * Closed Syntax *)

Inductive rt_type : ftyp -> Prop :=
  | rt_type_rcd_nil :
      rt_type ftyp_rcd_nil
  | rt_type_rcd_cons : forall i T1 T2,
      rt_type (ftyp_rcd_cons i T1 T2)
.

Inductive type : ftyp -> Prop :=
  | type_top :
      type ftyp_top
  | type_lit :
      type ftyp_nat
  | type_var : forall X,
      type (ftyp_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (ftyp_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (ftyp_all T1 T2)
  | type_rcd_nil :
      type ftyp_rcd_nil
  | type_rcd_cons : forall i T1 T2,
      type T1 ->
      type T2 ->
      rt_type T2 ->
      type (ftyp_rcd_cons i T1 T2)
.

Inductive rt_expr : fexp -> Prop :=
  | rt_expr_rcd_nil :
      rt_expr fexp_rcd_nil
  | rt_expr_rcd_cons : forall i e1 e2,
      rt_expr (fexp_rcd_cons i e1 e2)
.


Inductive expr : fexp -> Prop :=
  | expr_top :
      expr fexp_top
  | expr_lit : forall i,
      expr (fexp_lit i)
  | expr_var : forall x,
      expr (fexp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (fexp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (fexp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (fexp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (fexp_tapp e1 V)
  | expr_rcd_nil :
      expr fexp_rcd_nil
  | expr_rcd_cons : forall i e1 e2,
      expr e1 ->
      expr e2 ->
      rt_expr e2 ->
      expr (fexp_rcd_cons i e1 e2)
  | expr_rcd_proj : forall i e,
      expr e ->
      expr (fexp_rcd_proj e i)
.


Definition body_e (e : fexp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).


(* ********************************************************************** *)
(** * Environment *)


Inductive binding : Set :=
  | bind_sub : ftyp -> binding
  | bind_typ : ftyp -> binding.


Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Inductive fmono : env -> ftyp -> Prop :=
| fmono_nat : forall E,
    fmono E ftyp_nat
| fmono_top : forall E,
    fmono E ftyp_top
| fmono_var_f : forall E X U,
    binds X (bind_sub U) E ->
    fmono E U ->
    (fmono E (ftyp_fvar X))
| fmono_arrow : forall E (A B:ftyp),
    (fmono E A) ->
    (fmono E B) ->
    (fmono E (ftyp_arrow A B))
.



(* ********************************************************************** *)
(** * Well-formedness *)

Inductive wf_typ : env -> ftyp -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E ftyp_top
  | wf_typ_nat : forall E,
      wf_typ E ftyp_nat
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (ftyp_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (ftyp_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_sub T1 ++ E) (open_tt T2 X)) ->
      wf_typ E (ftyp_all T1 T2)
  | wf_typ_rcd_nil : forall E,
      wf_typ E ftyp_rcd_nil
  | wf_typ_rcd_cons : forall E i T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      rt_type T2 ->
      wf_typ E (ftyp_rcd_cons i T1 T2)
.


Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : ftyp),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : ftyp),
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).


(* ********************************************************************** *)
(** * Subtyping *)

Inductive fsub : env -> ftyp -> ftyp -> Prop :=
  | fsub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      fsub E S ftyp_top
  | fsub_nat : forall E,
      wf_env E ->
      fsub E ftyp_nat ftyp_nat
  | fsub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (ftyp_fvar X) ->
      fsub E (ftyp_fvar X) (ftyp_fvar X)
  | fsub_trans_tvar : forall U E X,
      wf_env E ->
      binds X (bind_sub U) E ->
      fsub E (ftyp_fvar X) U
  | fsub_trans : forall E A B C,
      fsub E A B ->
      fsub E B C ->
      fsub E A C
  | fsub_arrow : forall E S1 S2 T1 T2,
      fsub E T1 S1 ->
      fsub E S2 T2 ->
      fsub E (ftyp_arrow S1 S2) (ftyp_arrow T1 T2)
  (* Note: we use the kernel version *)
  | fsub_all : forall L E A B1 B2,
      fsub E A A ->
      (forall X : atom, X `notin` L ->
          fsub (X ~ bind_sub A ++ E) (open_tt B1 X) (open_tt B2 X)) ->
      fsub E (ftyp_all A B1) (ftyp_all A B2)
  | fsub_rcd_nil : forall E,
      wf_env E ->
      fsub E ftyp_rcd_nil ftyp_rcd_nil
  | fsub_rcd_width : forall E A B i,
      wf_env E ->
      wf_typ E A ->
      wf_typ E B ->
      rt_type B ->
      fsub E (ftyp_rcd_cons i A B) (ftyp_rcd_nil)
  | fsub_rcd_depth : forall E A1 B1 i A2 B2,
      fsub E A1 A2 ->
      fsub E B1 B2 ->
      rt_type B1 ->
      rt_type B2 ->
      fsub E (ftyp_rcd_cons i A1 B1) (ftyp_rcd_cons i A2 B2)
  | fsub_rcd_perm : forall E i j A1 A2 A3,
      wf_env E ->
      wf_typ E A1 ->
      wf_typ E A2 ->
      wf_typ E A3 ->
      rt_type A3 ->
      fsub E (ftyp_rcd_cons i A1 (ftyp_rcd_cons j A2 A3))
             (ftyp_rcd_cons j A2 (ftyp_rcd_cons i A1 A3))
.

(* ********************************************************************** *)
(** * Automation *)

Hint Constructors rt_type type rt_expr expr wf_typ wf_env.
Hint Resolve fsub_top fsub_nat fsub_refl_tvar fsub_arrow fsub_rcd_nil fsub_rcd_width fsub_rcd_depth fsub_rcd_perm.
