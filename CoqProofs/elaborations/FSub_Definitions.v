(** Definition of Fsub (System F with subtyping).

    Adapted from Metalib
*)

Require Export Metalib.Metatheory.

(* ********************************************************************** *)
(** * Syntax *)

Definition i := nat.
Inductive typ : Set :=
  | typ_top : typ
  | typ_nat : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_rcd_nil : typ
  | typ_rcd_cons : i -> typ -> typ -> typ
.

Inductive exp : Set :=
  | exp_top : exp
  | exp_lit : i -> exp
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_rcd_nil : exp
  | exp_rcd_cons : i -> exp -> exp -> exp
  | exp_rcd_proj : exp -> i -> exp
.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.

(* ********************************************************************** *)
(** * Open *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_rcd_nil => typ_rcd_nil
  | typ_rcd_cons i T1 T2  => typ_rcd_cons i (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_nat => typ_nat
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_top => exp_top
  | exp_rcd_nil => exp_rcd_nil
  | exp_rcd_cons i e1 e2 => exp_rcd_cons i (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_rcd_proj e1 i => exp_rcd_proj (open_te_rec K U e1) i
  | exp_lit i => exp_lit i
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_top => exp_top
  | exp_rcd_nil => exp_rcd_nil
  | exp_rcd_cons i e1 e2 => exp_rcd_cons i (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_rcd_proj e1 i => exp_rcd_proj (open_ee_rec k f e1) i
  | exp_lit i => exp_lit i
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs V e1 => exp_tabs V (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

(* ********************************************************************** *)
(** * Closed Syntax *)

Inductive rt_type : typ -> Prop :=
  | rt_type_rcd_nil :
      rt_type typ_rcd_nil
  | rt_type_rcd_cons : forall i T1 T2,
      rt_type (typ_rcd_cons i T1 T2)
.


Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_lit :
      type typ_nat
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_rcd_nil :
      type typ_rcd_nil
  | type_rcd_cons : forall i T1 T2,
      type T1 ->
      type T2 ->
      rt_type T2 ->
      type (typ_rcd_cons i T1 T2)
.

Inductive rt_expr : exp -> Prop :=
  | rt_expr_rcd_nil :
      rt_expr exp_rcd_nil
  | rt_expr_rcd_cons : forall i e1 e2,
      rt_expr (exp_rcd_cons i e1 e2)
.

Inductive expr : exp -> Prop :=
  | expr_top :
      expr exp_top
  | expr_lit : forall i,
      expr (exp_lit i)
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L T e1,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs T e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_rcd_nil :
      expr exp_rcd_nil
  | expr_rcd_cons : forall i e1 e2,
      expr e1 ->
      expr e2 ->
      rt_expr e2 ->
      expr (exp_rcd_cons i e1 e2)
  | expr_rcd_proj : forall i e,
      expr e ->
      expr (exp_rcd_proj e i)
.


Definition body_e (e : exp) :=
  exists L, forall x : atom, x `notin` L -> expr (open_ee e x).

(* ********************************************************************** *)
(** * Environment *)

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.


Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(* ********************************************************************** *)
(** * Well-formedness *)

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_nat : forall E,
      wf_typ E typ_nat
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ (X ~ bind_sub T1 ++ E) (open_tt T2 X)) ->
      wf_typ E (typ_all T1 T2)
  | wf_typ_rcd_nil : forall E,
      wf_typ E typ_rcd_nil
  | wf_typ_rcd_cons : forall E i T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      rt_type T2 ->
      wf_typ E (typ_rcd_cons i T1 T2)
.


Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env (X ~ bind_sub T ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env (x ~ bind_typ T ++ E).



(* ********************************************************************** *)
(** * Subtyping *)

Inductive fsub : env -> typ -> typ -> Prop :=
  | fsub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      fsub E S typ_top
  | fsub_nat : forall E,
      wf_env E ->
      fsub E typ_nat typ_nat
  | fsub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      fsub E (typ_fvar X) (typ_fvar X)
  | fsub_trans_tvar : forall U E X,
      wf_env E ->
      binds X (bind_sub U) E ->
      fsub E (typ_fvar X) U
  | fsub_trans : forall E A B C,
      fsub E A B ->
      fsub E B C ->
      fsub E A C
  | fsub_arrow : forall E S1 S2 T1 T2,
      fsub E T1 S1 ->
      fsub E S2 T2 ->
      fsub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  (* Note: we use the kernel version *)
  | fsub_all : forall L E A B1 B2,
      fsub E A A ->
      (forall X : atom, X `notin` L ->
          fsub (X ~ bind_sub A ++ E) (open_tt B1 X) (open_tt B2 X)) ->
      fsub E (typ_all A B1) (typ_all A B2)
  | fsub_rcd_nil : forall E,
      wf_env E ->
      fsub E typ_rcd_nil typ_rcd_nil
  | fsub_rcd_width : forall E A B i,
      wf_env E ->
      wf_typ E A ->
      wf_typ E B ->
      rt_type B ->
      fsub E (typ_rcd_cons i A B) (typ_rcd_nil)
  | fsub_rcd_depth : forall E A1 B1 i A2 B2,
      fsub E A1 A2 ->
      fsub E B1 B2 ->
      rt_type B1 ->
      rt_type B2 ->
      fsub E (typ_rcd_cons i A1 B1) (typ_rcd_cons i A2 B2)
  | fsub_rcd_perm : forall E i j A1 A2 A3,
      wf_env E ->
      wf_typ E A1 ->
      wf_typ E A2 ->
      wf_typ E A3 ->
      rt_type A3 ->
      fsub E (typ_rcd_cons i A1 (typ_rcd_cons j A2 A3))
             (typ_rcd_cons j A2 (typ_rcd_cons i A1 A3))
.


(* ********************************************************************** *)
(** * Automation *)

Hint Constructors rt_type type rt_expr expr wf_typ wf_env.
Hint Resolve fsub_top fsub_nat fsub_refl_tvar fsub_arrow fsub_rcd_nil fsub_rcd_width fsub_rcd_depth fsub_rcd_perm.
