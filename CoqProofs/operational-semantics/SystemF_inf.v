(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Syntax_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme ty_ind' := Induction for ty Sort Prop.

Definition ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  ty_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme ty_rec' := Induction for ty Sort Set.

Definition ty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  ty_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme co_ind' := Induction for co Sort Prop.

Definition co_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  co_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme co_rec' := Induction for co Sort Set.

Definition co_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  co_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_ty_wrt_ty_rec (n1 : nat) (X1 : typvar) (T1 : ty) {struct T1} : ty :=
  match T1 with
    | ty_nat => ty_nat
    | ty_unit => ty_unit
    | ty_var_f X2 => if (X1 == X2) then (ty_var_b n1) else (ty_var_f X2)
    | ty_var_b n2 => if (lt_ge_dec n2 n1) then (ty_var_b n2) else (ty_var_b (S n2))
    | ty_arrow T2 T3 => ty_arrow (close_ty_wrt_ty_rec n1 X1 T2) (close_ty_wrt_ty_rec n1 X1 T3)
    | ty_prod T2 T3 => ty_prod (close_ty_wrt_ty_rec n1 X1 T2) (close_ty_wrt_ty_rec n1 X1 T3)
    | ty_all T2 => ty_all (close_ty_wrt_ty_rec (S n1) X1 T2)
  end.

Definition close_ty_wrt_ty X1 T1 := close_ty_wrt_ty_rec 0 X1 T1.

Fixpoint close_exp_wrt_ty_rec (n1 : nat) (X1 : typvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_unit => exp_unit
    | exp_lit i1 => exp_lit i1
    | exp_abs e2 => exp_abs (close_exp_wrt_ty_rec n1 X1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_ty_rec n1 X1 e2) (close_exp_wrt_ty_rec n1 X1 e3)
    | exp_pair e2 e3 => exp_pair (close_exp_wrt_ty_rec n1 X1 e2) (close_exp_wrt_ty_rec n1 X1 e3)
    | exp_capp c1 e2 => exp_capp c1 (close_exp_wrt_ty_rec n1 X1 e2)
    | exp_tabs e2 => exp_tabs (close_exp_wrt_ty_rec (S n1) X1 e2)
    | exp_tapp e2 T1 => exp_tapp (close_exp_wrt_ty_rec n1 X1 e2) (close_ty_wrt_ty_rec n1 X1 T1)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : expvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_unit => exp_unit
    | exp_lit i1 => exp_lit i1
    | exp_abs e2 => exp_abs (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_pair e2 e3 => exp_pair (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_capp c1 e2 => exp_capp c1 (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_tabs e2 => exp_tabs (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_tapp e2 T1 => exp_tapp (close_exp_wrt_exp_rec n1 x1 e2) T1
  end.

Definition close_exp_wrt_ty X1 e1 := close_exp_wrt_ty_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_ty (T1 : ty) {struct T1} : nat :=
  match T1 with
    | ty_nat => 1
    | ty_unit => 1
    | ty_var_f X1 => 1
    | ty_var_b n1 => 1
    | ty_arrow T2 T3 => 1 + (size_ty T2) + (size_ty T3)
    | ty_prod T2 T3 => 1 + (size_ty T2) + (size_ty T3)
    | ty_all T2 => 1 + (size_ty T2)
  end.

Fixpoint size_co (c1 : co) {struct c1} : nat :=
  match c1 with
    | co_id => 1
    | co_trans c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_top => 1
    | co_bot => 1
    | co_arr c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_pair c2 c3 => 1 + (size_co c2) + (size_co c3)
    | co_proj1 => 1
    | co_proj2 => 1
    | co_forall c2 => 1 + (size_co c2)
    | co_distArr => 1
    | co_topArr => 1
    | co_topAll => 1
    | co_distPoly => 1
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_unit => 1
    | exp_lit i1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_pair e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_capp c1 e2 => 1 + (size_co c1) + (size_exp e2)
    | exp_tabs e2 => 1 + (size_exp e2)
    | exp_tapp e2 T1 => 1 + (size_exp e2) + (size_ty T1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_ty_wrt_ty : nat -> ty -> Prop :=
  | degree_wrt_ty_ty_nat : forall n1,
    degree_ty_wrt_ty n1 (ty_nat)
  | degree_wrt_ty_ty_unit : forall n1,
    degree_ty_wrt_ty n1 (ty_unit)
  | degree_wrt_ty_ty_var_f : forall n1 X1,
    degree_ty_wrt_ty n1 (ty_var_f X1)
  | degree_wrt_ty_ty_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_ty_wrt_ty n1 (ty_var_b n2)
  | degree_wrt_ty_ty_arrow : forall n1 T1 T2,
    degree_ty_wrt_ty n1 T1 ->
    degree_ty_wrt_ty n1 T2 ->
    degree_ty_wrt_ty n1 (ty_arrow T1 T2)
  | degree_wrt_ty_ty_prod : forall n1 T1 T2,
    degree_ty_wrt_ty n1 T1 ->
    degree_ty_wrt_ty n1 T2 ->
    degree_ty_wrt_ty n1 (ty_prod T1 T2)
  | degree_wrt_ty_ty_all : forall n1 T1,
    degree_ty_wrt_ty (S n1) T1 ->
    degree_ty_wrt_ty n1 (ty_all T1).

Scheme degree_ty_wrt_ty_ind' := Induction for degree_ty_wrt_ty Sort Prop.

Definition degree_ty_wrt_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  degree_ty_wrt_ty_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Hint Constructors degree_ty_wrt_ty : core lngen.

Inductive degree_exp_wrt_ty : nat -> exp -> Prop :=
  | degree_wrt_ty_exp_var_f : forall n1 x1,
    degree_exp_wrt_ty n1 (exp_var_f x1)
  | degree_wrt_ty_exp_var_b : forall n1 n2,
    degree_exp_wrt_ty n1 (exp_var_b n2)
  | degree_wrt_ty_exp_unit : forall n1,
    degree_exp_wrt_ty n1 (exp_unit)
  | degree_wrt_ty_exp_lit : forall n1 i1,
    degree_exp_wrt_ty n1 (exp_lit i1)
  | degree_wrt_ty_exp_abs : forall n1 e1,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 (exp_abs e1)
  | degree_wrt_ty_exp_app : forall n1 e1 e2,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 e2 ->
    degree_exp_wrt_ty n1 (exp_app e1 e2)
  | degree_wrt_ty_exp_pair : forall n1 e1 e2,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 e2 ->
    degree_exp_wrt_ty n1 (exp_pair e1 e2)
  | degree_wrt_ty_exp_capp : forall n1 c1 e1,
    degree_exp_wrt_ty n1 e1 ->
    degree_exp_wrt_ty n1 (exp_capp c1 e1)
  | degree_wrt_ty_exp_tabs : forall n1 e1,
    degree_exp_wrt_ty (S n1) e1 ->
    degree_exp_wrt_ty n1 (exp_tabs e1)
  | degree_wrt_ty_exp_tapp : forall n1 e1 T1,
    degree_exp_wrt_ty n1 e1 ->
    degree_ty_wrt_ty n1 T1 ->
    degree_exp_wrt_ty n1 (exp_tapp e1 T1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_unit : forall n1,
    degree_exp_wrt_exp n1 (exp_unit)
  | degree_wrt_exp_exp_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (exp_lit i1)
  | degree_wrt_exp_exp_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_pair : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_pair e1 e2)
  | degree_wrt_exp_exp_capp : forall n1 c1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_capp c1 e1)
  | degree_wrt_exp_exp_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tabs e1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 T1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 T1).

Scheme degree_exp_wrt_ty_ind' := Induction for degree_exp_wrt_ty Sort Prop.

Definition degree_exp_wrt_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_ty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Hint Constructors degree_exp_wrt_ty : core lngen.

Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_ty : ty -> Set :=
  | lc_set_ty_nat :
    lc_set_ty (ty_nat)
  | lc_set_ty_unit :
    lc_set_ty (ty_unit)
  | lc_set_ty_var_f : forall X1,
    lc_set_ty (ty_var_f X1)
  | lc_set_ty_arrow : forall T1 T2,
    lc_set_ty T1 ->
    lc_set_ty T2 ->
    lc_set_ty (ty_arrow T1 T2)
  | lc_set_ty_prod : forall T1 T2,
    lc_set_ty T1 ->
    lc_set_ty T2 ->
    lc_set_ty (ty_prod T1 T2)
  | lc_set_ty_all : forall T1,
    (forall X1 : typvar, lc_set_ty (open_ty_wrt_ty T1 (ty_var_f X1))) ->
    lc_set_ty (ty_all T1).

Scheme lc_ty_ind' := Induction for lc_ty Sort Prop.

Definition lc_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_ty_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme lc_set_ty_ind' := Induction for lc_set_ty Sort Prop.

Definition lc_set_ty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_set_ty_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme lc_set_ty_rec' := Induction for lc_set_ty Sort Set.

Definition lc_set_ty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 =>
  lc_set_ty_rec' H1 H2 H3 H4 H5 H6 H7.

Hint Constructors lc_ty : core lngen.

Hint Constructors lc_set_ty : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_unit :
    lc_set_exp (exp_unit)
  | lc_set_exp_lit : forall i1,
    lc_set_exp (exp_lit i1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_pair : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_pair e1 e2)
  | lc_set_exp_capp : forall c1 e1,
    lc_set_exp e1 ->
    lc_set_exp (exp_capp c1 e1)
  | lc_set_exp_tabs : forall e1,
    (forall X1 : typvar, lc_set_exp (open_exp_wrt_ty e1 (ty_var_f X1))) ->
    lc_set_exp (exp_tabs e1)
  | lc_set_exp_tapp : forall e1 T1,
    lc_set_exp e1 ->
    lc_set_ty T1 ->
    lc_set_exp (exp_tapp e1 T1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors lc_exp : core lngen.

Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_ty_wrt_ty T1 := forall X1, lc_ty (open_ty_wrt_ty T1 (ty_var_f X1)).

Hint Unfold body_ty_wrt_ty.

Definition body_exp_wrt_ty e1 := forall X1, lc_exp (open_exp_wrt_ty e1 (ty_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

Hint Unfold body_exp_wrt_ty.

Hint Unfold body_exp_wrt_exp.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_ty_min_mutual :
(forall T1, 1 <= size_ty T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ty_min :
forall T1, 1 <= size_ty T1.
Proof.
pose proof size_ty_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_ty_min : lngen.

(* begin hide *)

Lemma size_co_min_mutual :
(forall c1, 1 <= size_co c1).
Proof.
apply_mutual_ind co_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_co_min :
forall c1, 1 <= size_co c1.
Proof.
pose proof size_co_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_co_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_ty_close_ty_wrt_ty_rec_mutual :
(forall T1 X1 n1,
  size_ty (close_ty_wrt_ty_rec n1 X1 T1) = size_ty T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_close_ty_wrt_ty_rec :
forall T1 X1 n1,
  size_ty (close_ty_wrt_ty_rec n1 X1 T1) = size_ty T1.
Proof.
pose proof size_ty_close_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_ty_close_ty_wrt_ty_rec : lngen.
Hint Rewrite size_ty_close_ty_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_ty_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_ty_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_ty_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_ty_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_ty_close_ty_wrt_ty :
forall T1 X1,
  size_ty (close_ty_wrt_ty X1 T1) = size_ty T1.
Proof.
unfold close_ty_wrt_ty; default_simp.
Qed.

Hint Resolve size_ty_close_ty_wrt_ty : lngen.
Hint Rewrite size_ty_close_ty_wrt_ty using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_ty :
forall e1 X1,
  size_exp (close_exp_wrt_ty X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_ty : lngen.
Hint Rewrite size_exp_close_exp_wrt_ty using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_ty_open_ty_wrt_ty_rec_mutual :
(forall T1 T2 n1,
  size_ty T1 <= size_ty (open_ty_wrt_ty_rec n1 T2 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_open_ty_wrt_ty_rec :
forall T1 T2 n1,
  size_ty T1 <= size_ty (open_ty_wrt_ty_rec n1 T2 T1).
Proof.
pose proof size_ty_open_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_ty_open_ty_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ty_rec_mutual :
(forall e1 T1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_ty_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ty_rec :
forall e1 T1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_ty_rec n1 T1 e1).
Proof.
pose proof size_exp_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_ty_open_ty_wrt_ty :
forall T1 T2,
  size_ty T1 <= size_ty (open_ty_wrt_ty T1 T2).
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve size_ty_open_ty_wrt_ty : lngen.

Lemma size_exp_open_exp_wrt_ty :
forall e1 T1,
  size_exp e1 <= size_exp (open_exp_wrt_ty e1 T1).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_ty : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_ty_open_ty_wrt_ty_rec_var_mutual :
(forall T1 X1 n1,
  size_ty (open_ty_wrt_ty_rec n1 (ty_var_f X1) T1) = size_ty T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ty_open_ty_wrt_ty_rec_var :
forall T1 X1 n1,
  size_ty (open_ty_wrt_ty_rec n1 (ty_var_f X1) T1) = size_ty T1.
Proof.
pose proof size_ty_open_ty_wrt_ty_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_ty_open_ty_wrt_ty_rec_var : lngen.
Hint Rewrite size_ty_open_ty_wrt_ty_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ty_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_ty_rec n1 (ty_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ty_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_ty_rec n1 (ty_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_ty_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_ty_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_ty_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_ty_open_ty_wrt_ty_var :
forall T1 X1,
  size_ty (open_ty_wrt_ty T1 (ty_var_f X1)) = size_ty T1.
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve size_ty_open_ty_wrt_ty_var : lngen.
Hint Rewrite size_ty_open_ty_wrt_ty_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_ty_var :
forall e1 X1,
  size_exp (open_exp_wrt_ty e1 (ty_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_ty_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_ty_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_ty_wrt_ty_S_mutual :
(forall n1 T1,
  degree_ty_wrt_ty n1 T1 ->
  degree_ty_wrt_ty (S n1) T1).
Proof.
apply_mutual_ind degree_ty_wrt_ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ty_wrt_ty_S :
forall n1 T1,
  degree_ty_wrt_ty n1 T1 ->
  degree_ty_wrt_ty (S n1) T1.
Proof.
pose proof degree_ty_wrt_ty_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_ty_wrt_ty_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_ty_S_mutual :
(forall n1 e1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_ty_S :
forall n1 e1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty (S n1) e1.
Proof.
pose proof degree_exp_wrt_ty_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_ty_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_ty_wrt_ty_O :
forall n1 T1,
  degree_ty_wrt_ty O T1 ->
  degree_ty_wrt_ty n1 T1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_ty_wrt_ty_O : lngen.

Lemma degree_exp_wrt_ty_O :
forall n1 e1,
  degree_exp_wrt_ty O e1 ->
  degree_exp_wrt_ty n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_ty_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_ty_wrt_ty_close_ty_wrt_ty_rec_mutual :
(forall T1 X1 n1,
  degree_ty_wrt_ty n1 T1 ->
  degree_ty_wrt_ty (S n1) (close_ty_wrt_ty_rec n1 X1 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_wrt_ty_close_ty_wrt_ty_rec :
forall T1 X1 n1,
  degree_ty_wrt_ty n1 T1 ->
  degree_ty_wrt_ty (S n1) (close_ty_wrt_ty_rec n1 X1 T1).
Proof.
pose proof degree_ty_wrt_ty_close_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_ty_wrt_ty_close_ty_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty (S n1) (close_exp_wrt_ty_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_ty_rec :
forall e1 X1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty (S n1) (close_exp_wrt_ty_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_ty_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_ty_close_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_ty n2 e1 ->
  degree_exp_wrt_ty n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_ty n2 e1 ->
  degree_exp_wrt_ty n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_ty_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_ty_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_ty_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ty_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_ty_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_ty_wrt_ty_close_ty_wrt_ty :
forall T1 X1,
  degree_ty_wrt_ty 0 T1 ->
  degree_ty_wrt_ty 1 (close_ty_wrt_ty X1 T1).
Proof.
unfold close_ty_wrt_ty; default_simp.
Qed.

Hint Resolve degree_ty_wrt_ty_close_ty_wrt_ty : lngen.

Lemma degree_exp_wrt_ty_close_exp_wrt_ty :
forall e1 X1,
  degree_exp_wrt_ty 0 e1 ->
  degree_exp_wrt_ty 1 (close_exp_wrt_ty X1 e1).
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve degree_exp_wrt_ty_close_exp_wrt_ty : lngen.

Lemma degree_exp_wrt_ty_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_ty_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_ty :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_ty X1 e1).
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_ty : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_ty_wrt_ty_close_ty_wrt_ty_rec_inv_mutual :
(forall T1 X1 n1,
  degree_ty_wrt_ty (S n1) (close_ty_wrt_ty_rec n1 X1 T1) ->
  degree_ty_wrt_ty n1 T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_wrt_ty_close_ty_wrt_ty_rec_inv :
forall T1 X1 n1,
  degree_ty_wrt_ty (S n1) (close_ty_wrt_ty_rec n1 X1 T1) ->
  degree_ty_wrt_ty n1 T1.
Proof.
pose proof degree_ty_wrt_ty_close_ty_wrt_ty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_ty_wrt_ty_close_ty_wrt_ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_ty_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_ty (S n1) (close_exp_wrt_ty_rec n1 X1 e1) ->
  degree_exp_wrt_ty n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_ty_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_ty (S n1) (close_exp_wrt_ty_rec n1 X1 e1) ->
  degree_exp_wrt_ty n1 e1.
Proof.
pose proof degree_exp_wrt_ty_close_exp_wrt_ty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_ty_close_exp_wrt_ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_ty n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_ty n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_ty n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_ty n2 e1.
Proof.
pose proof degree_exp_wrt_ty_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_ty_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ty_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_ty_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ty_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_ty_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_ty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_ty_wrt_ty_close_ty_wrt_ty_inv :
forall T1 X1,
  degree_ty_wrt_ty 1 (close_ty_wrt_ty X1 T1) ->
  degree_ty_wrt_ty 0 T1.
Proof.
unfold close_ty_wrt_ty; eauto with lngen.
Qed.

Hint Immediate degree_ty_wrt_ty_close_ty_wrt_ty_inv : lngen.

Lemma degree_exp_wrt_ty_close_exp_wrt_ty_inv :
forall e1 X1,
  degree_exp_wrt_ty 1 (close_exp_wrt_ty X1 e1) ->
  degree_exp_wrt_ty 0 e1.
Proof.
unfold close_exp_wrt_ty; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_ty_close_exp_wrt_ty_inv : lngen.

Lemma degree_exp_wrt_ty_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_ty n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_ty n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_ty_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_ty_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_ty X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_ty; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_ty_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_ty_wrt_ty_open_ty_wrt_ty_rec_mutual :
(forall T1 T2 n1,
  degree_ty_wrt_ty (S n1) T1 ->
  degree_ty_wrt_ty n1 T2 ->
  degree_ty_wrt_ty n1 (open_ty_wrt_ty_rec n1 T2 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_wrt_ty_open_ty_wrt_ty_rec :
forall T1 T2 n1,
  degree_ty_wrt_ty (S n1) T1 ->
  degree_ty_wrt_ty n1 T2 ->
  degree_ty_wrt_ty n1 (open_ty_wrt_ty_rec n1 T2 T1).
Proof.
pose proof degree_ty_wrt_ty_open_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_ty_wrt_ty_open_ty_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_ty_rec_mutual :
(forall e1 T1 n1,
  degree_exp_wrt_ty (S n1) e1 ->
  degree_ty_wrt_ty n1 T1 ->
  degree_exp_wrt_ty n1 (open_exp_wrt_ty_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_ty_rec :
forall e1 T1 n1,
  degree_exp_wrt_ty (S n1) e1 ->
  degree_ty_wrt_ty n1 T1 ->
  degree_exp_wrt_ty n1 (open_exp_wrt_ty_rec n1 T1 e1).
Proof.
pose proof degree_exp_wrt_ty_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_ty_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty n1 e2 ->
  degree_exp_wrt_ty n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty n1 e2 ->
  degree_exp_wrt_ty n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_ty_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_ty_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ty_rec_mutual :
(forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_ty_rec n2 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ty_rec :
forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_ty_rec n2 T1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_ty_wrt_ty_open_ty_wrt_ty :
forall T1 T2,
  degree_ty_wrt_ty 1 T1 ->
  degree_ty_wrt_ty 0 T2 ->
  degree_ty_wrt_ty 0 (open_ty_wrt_ty T1 T2).
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve degree_ty_wrt_ty_open_ty_wrt_ty : lngen.

Lemma degree_exp_wrt_ty_open_exp_wrt_ty :
forall e1 T1,
  degree_exp_wrt_ty 1 e1 ->
  degree_ty_wrt_ty 0 T1 ->
  degree_exp_wrt_ty 0 (open_exp_wrt_ty e1 T1).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve degree_exp_wrt_ty_open_exp_wrt_ty : lngen.

Lemma degree_exp_wrt_ty_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty n1 e2 ->
  degree_exp_wrt_ty n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_ty_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_ty :
forall e1 T1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_ty e1 T1).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_ty : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_ty_wrt_ty_open_ty_wrt_ty_rec_inv_mutual :
(forall T1 T2 n1,
  degree_ty_wrt_ty n1 (open_ty_wrt_ty_rec n1 T2 T1) ->
  degree_ty_wrt_ty (S n1) T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ty_wrt_ty_open_ty_wrt_ty_rec_inv :
forall T1 T2 n1,
  degree_ty_wrt_ty n1 (open_ty_wrt_ty_rec n1 T2 T1) ->
  degree_ty_wrt_ty (S n1) T1.
Proof.
pose proof degree_ty_wrt_ty_open_ty_wrt_ty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_ty_wrt_ty_open_ty_wrt_ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_ty_rec_inv_mutual :
(forall e1 T1 n1,
  degree_exp_wrt_ty n1 (open_exp_wrt_ty_rec n1 T1 e1) ->
  degree_exp_wrt_ty (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_ty_rec_inv :
forall e1 T1 n1,
  degree_exp_wrt_ty n1 (open_exp_wrt_ty_rec n1 T1 e1) ->
  degree_exp_wrt_ty (S n1) e1.
Proof.
pose proof degree_exp_wrt_ty_open_exp_wrt_ty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_ty_open_exp_wrt_ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_ty n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_ty n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ty_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_ty n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_ty n1 e1.
Proof.
pose proof degree_exp_wrt_ty_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_ty_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ty_rec_inv_mutual :
(forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_ty_rec n2 T1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ty_rec_inv :
forall e1 T1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_ty_rec n2 T1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_ty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_ty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_ty_wrt_ty_open_ty_wrt_ty_inv :
forall T1 T2,
  degree_ty_wrt_ty 0 (open_ty_wrt_ty T1 T2) ->
  degree_ty_wrt_ty 1 T1.
Proof.
unfold open_ty_wrt_ty; eauto with lngen.
Qed.

Hint Immediate degree_ty_wrt_ty_open_ty_wrt_ty_inv : lngen.

Lemma degree_exp_wrt_ty_open_exp_wrt_ty_inv :
forall e1 T1,
  degree_exp_wrt_ty 0 (open_exp_wrt_ty e1 T1) ->
  degree_exp_wrt_ty 1 e1.
Proof.
unfold open_exp_wrt_ty; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_ty_open_exp_wrt_ty_inv : lngen.

Lemma degree_exp_wrt_ty_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_ty n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_ty n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_ty_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_ty_inv :
forall e1 T1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_ty e1 T1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_ty; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_ty_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ty_wrt_ty_rec_inj_mutual :
(forall T1 T2 X1 n1,
  close_ty_wrt_ty_rec n1 X1 T1 = close_ty_wrt_ty_rec n1 X1 T2 ->
  T1 = T2).
Proof.
apply_mutual_ind ty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_wrt_ty_rec_inj :
forall T1 T2 X1 n1,
  close_ty_wrt_ty_rec n1 X1 T1 = close_ty_wrt_ty_rec n1 X1 T2 ->
  T1 = T2.
Proof.
pose proof close_ty_wrt_ty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_ty_wrt_ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ty_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_ty_rec n1 X1 e1 = close_exp_wrt_ty_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ty_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_ty_rec n1 X1 e1 = close_exp_wrt_ty_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_ty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_ty_wrt_ty_inj :
forall T1 T2 X1,
  close_ty_wrt_ty X1 T1 = close_ty_wrt_ty X1 T2 ->
  T1 = T2.
Proof.
unfold close_ty_wrt_ty; eauto with lngen.
Qed.

Hint Immediate close_ty_wrt_ty_inj : lngen.

Lemma close_exp_wrt_ty_inj :
forall e1 e2 X1,
  close_exp_wrt_ty X1 e1 = close_exp_wrt_ty X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_ty; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_ty_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_ty_wrt_ty_rec_open_ty_wrt_ty_rec_mutual :
(forall T1 X1 n1,
  X1 `notin` fv_ty_in_ty T1 ->
  close_ty_wrt_ty_rec n1 X1 (open_ty_wrt_ty_rec n1 (ty_var_f X1) T1) = T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_wrt_ty_rec_open_ty_wrt_ty_rec :
forall T1 X1 n1,
  X1 `notin` fv_ty_in_ty T1 ->
  close_ty_wrt_ty_rec n1 X1 (open_ty_wrt_ty_rec n1 (ty_var_f X1) T1) = T1.
Proof.
pose proof close_ty_wrt_ty_rec_open_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_ty_wrt_ty_rec_open_ty_wrt_ty_rec : lngen.
Hint Rewrite close_ty_wrt_ty_rec_open_ty_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ty_rec_open_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` fv_ty_in_exp e1 ->
  close_exp_wrt_ty_rec n1 X1 (open_exp_wrt_ty_rec n1 (ty_var_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ty_rec_open_exp_wrt_ty_rec :
forall e1 X1 n1,
  X1 `notin` fv_ty_in_exp e1 ->
  close_exp_wrt_ty_rec n1 X1 (open_exp_wrt_ty_rec n1 (ty_var_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_ty_rec_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_ty_rec_open_exp_wrt_ty_rec : lngen.
Hint Rewrite close_exp_wrt_ty_rec_open_exp_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_ty_wrt_ty_open_ty_wrt_ty :
forall T1 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  close_ty_wrt_ty X1 (open_ty_wrt_ty T1 (ty_var_f X1)) = T1.
Proof.
unfold close_ty_wrt_ty; unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve close_ty_wrt_ty_open_ty_wrt_ty : lngen.
Hint Rewrite close_ty_wrt_ty_open_ty_wrt_ty using solve [auto] : lngen.

Lemma close_exp_wrt_ty_open_exp_wrt_ty :
forall e1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  close_exp_wrt_ty X1 (open_exp_wrt_ty e1 (ty_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_ty; unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve close_exp_wrt_ty_open_exp_wrt_ty : lngen.
Hint Rewrite close_exp_wrt_ty_open_exp_wrt_ty using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ty_wrt_ty_rec_close_ty_wrt_ty_rec_mutual :
(forall T1 X1 n1,
  open_ty_wrt_ty_rec n1 (ty_var_f X1) (close_ty_wrt_ty_rec n1 X1 T1) = T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_wrt_ty_rec_close_ty_wrt_ty_rec :
forall T1 X1 n1,
  open_ty_wrt_ty_rec n1 (ty_var_f X1) (close_ty_wrt_ty_rec n1 X1 T1) = T1.
Proof.
pose proof open_ty_wrt_ty_rec_close_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_ty_wrt_ty_rec_close_ty_wrt_ty_rec : lngen.
Hint Rewrite open_ty_wrt_ty_rec_close_ty_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ty_rec_close_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_ty_rec n1 (ty_var_f X1) (close_exp_wrt_ty_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ty_rec_close_exp_wrt_ty_rec :
forall e1 X1 n1,
  open_exp_wrt_ty_rec n1 (ty_var_f X1) (close_exp_wrt_ty_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_ty_rec_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_ty_rec_close_exp_wrt_ty_rec : lngen.
Hint Rewrite open_exp_wrt_ty_rec_close_exp_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_ty_wrt_ty_close_ty_wrt_ty :
forall T1 X1,
  open_ty_wrt_ty (close_ty_wrt_ty X1 T1) (ty_var_f X1) = T1.
Proof.
unfold close_ty_wrt_ty; unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve open_ty_wrt_ty_close_ty_wrt_ty : lngen.
Hint Rewrite open_ty_wrt_ty_close_ty_wrt_ty using solve [auto] : lngen.

Lemma open_exp_wrt_ty_close_exp_wrt_ty :
forall e1 X1,
  open_exp_wrt_ty (close_exp_wrt_ty X1 e1) (ty_var_f X1) = e1.
Proof.
unfold close_exp_wrt_ty; unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve open_exp_wrt_ty_close_exp_wrt_ty : lngen.
Hint Rewrite open_exp_wrt_ty_close_exp_wrt_ty using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ty_wrt_ty_rec_inj_mutual :
(forall T2 T1 X1 n1,
  X1 `notin` fv_ty_in_ty T2 ->
  X1 `notin` fv_ty_in_ty T1 ->
  open_ty_wrt_ty_rec n1 (ty_var_f X1) T2 = open_ty_wrt_ty_rec n1 (ty_var_f X1) T1 ->
  T2 = T1).
Proof.
apply_mutual_ind ty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_wrt_ty_rec_inj :
forall T2 T1 X1 n1,
  X1 `notin` fv_ty_in_ty T2 ->
  X1 `notin` fv_ty_in_ty T1 ->
  open_ty_wrt_ty_rec n1 (ty_var_f X1) T2 = open_ty_wrt_ty_rec n1 (ty_var_f X1) T1 ->
  T2 = T1.
Proof.
pose proof open_ty_wrt_ty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_ty_wrt_ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ty_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp e1 ->
  open_exp_wrt_ty_rec n1 (ty_var_f X1) e2 = open_exp_wrt_ty_rec n1 (ty_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ty_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp e1 ->
  open_exp_wrt_ty_rec n1 (ty_var_f X1) e2 = open_exp_wrt_ty_rec n1 (ty_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_ty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_ty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_ty_wrt_ty_inj :
forall T2 T1 X1,
  X1 `notin` fv_ty_in_ty T2 ->
  X1 `notin` fv_ty_in_ty T1 ->
  open_ty_wrt_ty T2 (ty_var_f X1) = open_ty_wrt_ty T1 (ty_var_f X1) ->
  T2 = T1.
Proof.
unfold open_ty_wrt_ty; eauto with lngen.
Qed.

Hint Immediate open_ty_wrt_ty_inj : lngen.

Lemma open_exp_wrt_ty_inj :
forall e2 e1 X1,
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp e1 ->
  open_exp_wrt_ty e2 (ty_var_f X1) = open_exp_wrt_ty e1 (ty_var_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_ty; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_ty_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp e2 (exp_var_f x1) = open_exp_wrt_exp e1 (exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_ty_wrt_ty_of_lc_ty_mutual :
(forall T1,
  lc_ty T1 ->
  degree_ty_wrt_ty 0 T1).
Proof.
apply_mutual_ind lc_ty_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ty_wrt_ty_of_lc_ty :
forall T1,
  lc_ty T1 ->
  degree_ty_wrt_ty 0 T1.
Proof.
pose proof degree_ty_wrt_ty_of_lc_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_ty_wrt_ty_of_lc_ty : lngen.

(* begin hide *)

Lemma degree_exp_wrt_ty_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_ty 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_ty_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_ty 0 e1.
Proof.
pose proof degree_exp_wrt_ty_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_ty_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_ty_of_degree_size_mutual :
forall i1,
(forall T1,
  size_ty T1 = i1 ->
  degree_ty_wrt_ty 0 T1 ->
  lc_ty T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_of_degree :
forall T1,
  degree_ty_wrt_ty 0 T1 ->
  lc_ty T1.
Proof.
intros T1; intros;
pose proof (lc_ty_of_degree_size_mutual (size_ty T1));
intuition eauto.
Qed.

Hint Resolve lc_ty_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_ty 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_ty 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_exp_of_degree : lngen.

Ltac ty_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ty_wrt_ty_of_lc_ty in J1; clear H
          end).

Ltac co_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_ty_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Lemma lc_ty_all_exists :
forall X1 T1,
  lc_ty (open_ty_wrt_ty T1 (ty_var_f X1)) ->
  lc_ty (ty_all T1).
Proof.
intros; ty_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_abs_exists :
forall x1 e1,
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_exp_tabs_exists :
forall X1 e1,
  lc_exp (open_exp_wrt_ty e1 (ty_var_f X1)) ->
  lc_exp (exp_tabs e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_ty (ty_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_ty_all_exists X1).

Hint Extern 1 (lc_exp (exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1).

Hint Extern 1 (lc_exp (exp_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_exp_tabs_exists X1).

Lemma lc_body_ty_wrt_ty :
forall T1 T2,
  body_ty_wrt_ty T1 ->
  lc_ty T2 ->
  lc_ty (open_ty_wrt_ty T1 T2).
Proof.
unfold body_ty_wrt_ty;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
ty_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_ty_wrt_ty : lngen.

Lemma lc_body_exp_wrt_ty :
forall e1 T1,
  body_exp_wrt_ty e1 ->
  lc_ty T1 ->
  lc_exp (open_exp_wrt_ty e1 T1).
Proof.
unfold body_exp_wrt_ty;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_ty : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_ty_all_1 :
forall T1,
  lc_ty (ty_all T1) ->
  body_ty_wrt_ty T1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ty_all_1 : lngen.

Lemma lc_body_exp_abs_1 :
forall e1,
  lc_exp (exp_abs e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_abs_1 : lngen.

Lemma lc_body_exp_tabs_1 :
forall e1,
  lc_exp (exp_tabs e1) ->
  body_exp_wrt_ty e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_exp_tabs_1 : lngen.

(* begin hide *)

Lemma lc_ty_unique_mutual :
(forall T1 (proof2 proof3 : lc_ty T1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ty_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ty_unique :
forall T1 (proof2 proof3 : lc_ty T1), proof2 = proof3.
Proof.
pose proof lc_ty_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_ty_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_ty_of_lc_set_ty_mutual :
(forall T1, lc_set_ty T1 -> lc_ty T1).
Proof.
apply_mutual_ind lc_set_ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ty_of_lc_set_ty :
forall T1, lc_set_ty T1 -> lc_ty T1.
Proof.
pose proof lc_ty_of_lc_set_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_ty_of_lc_set_ty : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_ty_of_lc_ty_size_mutual :
forall i1,
(forall T1,
  size_ty T1 = i1 ->
  lc_ty T1 ->
  lc_set_ty T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ty_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ty_of_lc_ty];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_ty_of_lc_ty :
forall T1,
  lc_ty T1 ->
  lc_set_ty T1.
Proof.
intros T1; intros;
pose proof (lc_set_ty_of_lc_ty_size_mutual (size_ty T1));
intuition eauto.
Qed.

Hint Resolve lc_set_ty_of_lc_ty : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ty_of_lc_ty
 | apply lc_set_co_of_lc_co
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_exp_of_lc_exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ty_wrt_ty_rec_degree_ty_wrt_ty_mutual :
(forall T1 X1 n1,
  degree_ty_wrt_ty n1 T1 ->
  X1 `notin` fv_ty_in_ty T1 ->
  close_ty_wrt_ty_rec n1 X1 T1 = T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ty_wrt_ty_rec_degree_ty_wrt_ty :
forall T1 X1 n1,
  degree_ty_wrt_ty n1 T1 ->
  X1 `notin` fv_ty_in_ty T1 ->
  close_ty_wrt_ty_rec n1 X1 T1 = T1.
Proof.
pose proof close_ty_wrt_ty_rec_degree_ty_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve close_ty_wrt_ty_rec_degree_ty_wrt_ty : lngen.
Hint Rewrite close_ty_wrt_ty_rec_degree_ty_wrt_ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ty_rec_degree_exp_wrt_ty_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_ty n1 e1 ->
  X1 `notin` fv_ty_in_exp e1 ->
  close_exp_wrt_ty_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ty_rec_degree_exp_wrt_ty :
forall e1 X1 n1,
  degree_exp_wrt_ty n1 e1 ->
  X1 `notin` fv_ty_in_exp e1 ->
  close_exp_wrt_ty_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_ty_rec_degree_exp_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_ty_rec_degree_exp_wrt_ty : lngen.
Hint Rewrite close_exp_wrt_ty_rec_degree_exp_wrt_ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_ty_wrt_ty_lc_ty :
forall T1 X1,
  lc_ty T1 ->
  X1 `notin` fv_ty_in_ty T1 ->
  close_ty_wrt_ty X1 T1 = T1.
Proof.
unfold close_ty_wrt_ty; default_simp.
Qed.

Hint Resolve close_ty_wrt_ty_lc_ty : lngen.
Hint Rewrite close_ty_wrt_ty_lc_ty using solve [auto] : lngen.

Lemma close_exp_wrt_ty_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` fv_ty_in_exp e1 ->
  close_exp_wrt_ty X1 e1 = e1.
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve close_exp_wrt_ty_lc_exp : lngen.
Hint Rewrite close_exp_wrt_ty_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ty_wrt_ty_rec_degree_ty_wrt_ty_mutual :
(forall T2 T1 n1,
  degree_ty_wrt_ty n1 T2 ->
  open_ty_wrt_ty_rec n1 T1 T2 = T2).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ty_wrt_ty_rec_degree_ty_wrt_ty :
forall T2 T1 n1,
  degree_ty_wrt_ty n1 T2 ->
  open_ty_wrt_ty_rec n1 T1 T2 = T2.
Proof.
pose proof open_ty_wrt_ty_rec_degree_ty_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve open_ty_wrt_ty_rec_degree_ty_wrt_ty : lngen.
Hint Rewrite open_ty_wrt_ty_rec_degree_ty_wrt_ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ty_rec_degree_exp_wrt_ty_mutual :
(forall e1 T1 n1,
  degree_exp_wrt_ty n1 e1 ->
  open_exp_wrt_ty_rec n1 T1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ty_rec_degree_exp_wrt_ty :
forall e1 T1 n1,
  degree_exp_wrt_ty n1 e1 ->
  open_exp_wrt_ty_rec n1 T1 e1 = e1.
Proof.
pose proof open_exp_wrt_ty_rec_degree_exp_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_ty_rec_degree_exp_wrt_ty : lngen.
Hint Rewrite open_exp_wrt_ty_rec_degree_exp_wrt_ty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_ty_wrt_ty_lc_ty :
forall T2 T1,
  lc_ty T2 ->
  open_ty_wrt_ty T2 T1 = T2.
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve open_ty_wrt_ty_lc_ty : lngen.
Hint Rewrite open_ty_wrt_ty_lc_ty using solve [auto] : lngen.

Lemma open_exp_wrt_ty_lc_exp :
forall e1 T1,
  lc_exp e1 ->
  open_exp_wrt_ty e1 T1 = e1.
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve open_exp_wrt_ty_lc_exp : lngen.
Hint Rewrite open_exp_wrt_ty_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_ty_in_ty_close_ty_wrt_ty_rec_mutual :
(forall T1 X1 n1,
  fv_ty_in_ty (close_ty_wrt_ty_rec n1 X1 T1) [=] remove X1 (fv_ty_in_ty T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_ty_close_ty_wrt_ty_rec :
forall T1 X1 n1,
  fv_ty_in_ty (close_ty_wrt_ty_rec n1 X1 T1) [=] remove X1 (fv_ty_in_ty T1).
Proof.
pose proof fv_ty_in_ty_close_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_close_ty_wrt_ty_rec : lngen.
Hint Rewrite fv_ty_in_ty_close_ty_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_close_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1,
  fv_ty_in_exp (close_exp_wrt_ty_rec n1 X1 e1) [=] remove X1 (fv_ty_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_close_exp_wrt_ty_rec :
forall e1 X1 n1,
  fv_ty_in_exp (close_exp_wrt_ty_rec n1 X1 e1) [=] remove X1 (fv_ty_in_exp e1).
Proof.
pose proof fv_ty_in_exp_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_close_exp_wrt_ty_rec : lngen.
Hint Rewrite fv_ty_in_exp_close_exp_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_ty_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] fv_ty_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_ty_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] fv_ty_in_exp e1.
Proof.
pose proof fv_ty_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_ty_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_ty_rec_mutual :
(forall e1 X1 n1,
  fv_exp_in_exp (close_exp_wrt_ty_rec n1 X1 e1) [=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_ty_rec :
forall e1 X1 n1,
  fv_exp_in_exp (close_exp_wrt_ty_rec n1 X1 e1) [=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_ty_rec : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_ty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_exp_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_exp_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_exp_in_exp e1).
Proof.
pose proof fv_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_ty_in_ty_close_ty_wrt_ty :
forall T1 X1,
  fv_ty_in_ty (close_ty_wrt_ty X1 T1) [=] remove X1 (fv_ty_in_ty T1).
Proof.
unfold close_ty_wrt_ty; default_simp.
Qed.

Hint Resolve fv_ty_in_ty_close_ty_wrt_ty : lngen.
Hint Rewrite fv_ty_in_ty_close_ty_wrt_ty using solve [auto] : lngen.

Lemma fv_ty_in_exp_close_exp_wrt_ty :
forall e1 X1,
  fv_ty_in_exp (close_exp_wrt_ty X1 e1) [=] remove X1 (fv_ty_in_exp e1).
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve fv_ty_in_exp_close_exp_wrt_ty : lngen.
Hint Rewrite fv_ty_in_exp_close_exp_wrt_ty using solve [auto] : lngen.

Lemma fv_ty_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_ty_in_exp (close_exp_wrt_exp x1 e1) [=] fv_ty_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_ty_in_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_ty_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fv_exp_in_exp_close_exp_wrt_ty :
forall e1 X1,
  fv_exp_in_exp (close_exp_wrt_ty X1 e1) [=] fv_exp_in_exp e1.
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_ty : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_ty using solve [auto] : lngen.

Lemma fv_exp_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_exp_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_exp_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_ty_in_ty_open_ty_wrt_ty_rec_lower_mutual :
(forall T1 T2 n1,
  fv_ty_in_ty T1 [<=] fv_ty_in_ty (open_ty_wrt_ty_rec n1 T2 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_ty_open_ty_wrt_ty_rec_lower :
forall T1 T2 n1,
  fv_ty_in_ty T1 [<=] fv_ty_in_ty (open_ty_wrt_ty_rec n1 T2 T1).
Proof.
pose proof fv_ty_in_ty_open_ty_wrt_ty_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_open_ty_wrt_ty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_ty_rec_lower_mutual :
(forall e1 T1 n1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (open_exp_wrt_ty_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_ty_rec_lower :
forall e1 T1 n1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (open_exp_wrt_ty_rec n1 T1 e1).
Proof.
pose proof fv_ty_in_exp_open_exp_wrt_ty_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_ty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fv_ty_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_ty_rec_lower_mutual :
(forall e1 T1 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_ty_rec n1 T1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_ty_rec_lower :
forall e1 T1 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_ty_rec n1 T1 e1).
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_ty_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_ty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma fv_ty_in_ty_open_ty_wrt_ty_lower :
forall T1 T2,
  fv_ty_in_ty T1 [<=] fv_ty_in_ty (open_ty_wrt_ty T1 T2).
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve fv_ty_in_ty_open_ty_wrt_ty_lower : lngen.

Lemma fv_ty_in_exp_open_exp_wrt_ty_lower :
forall e1 T1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (open_exp_wrt_ty e1 T1).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_ty_lower : lngen.

Lemma fv_ty_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_ty_lower :
forall e1 T1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_ty e1 T1).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_ty_lower : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma fv_ty_in_ty_open_ty_wrt_ty_rec_upper_mutual :
(forall T1 T2 n1,
  fv_ty_in_ty (open_ty_wrt_ty_rec n1 T2 T1) [<=] fv_ty_in_ty T2 `union` fv_ty_in_ty T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_ty_open_ty_wrt_ty_rec_upper :
forall T1 T2 n1,
  fv_ty_in_ty (open_ty_wrt_ty_rec n1 T2 T1) [<=] fv_ty_in_ty T2 `union` fv_ty_in_ty T1.
Proof.
pose proof fv_ty_in_ty_open_ty_wrt_ty_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_open_ty_wrt_ty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_ty_rec_upper_mutual :
(forall e1 T1 n1,
  fv_ty_in_exp (open_exp_wrt_ty_rec n1 T1 e1) [<=] fv_ty_in_ty T1 `union` fv_ty_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_ty_rec_upper :
forall e1 T1 n1,
  fv_ty_in_exp (open_exp_wrt_ty_rec n1 T1 e1) [<=] fv_ty_in_ty T1 `union` fv_ty_in_exp e1.
Proof.
pose proof fv_ty_in_exp_open_exp_wrt_ty_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_ty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_ty_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_ty_in_exp e2 `union` fv_ty_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_ty_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_ty_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_ty_in_exp e2 `union` fv_ty_in_exp e1.
Proof.
pose proof fv_ty_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_ty_rec_upper_mutual :
(forall e1 T1 n1,
  fv_exp_in_exp (open_exp_wrt_ty_rec n1 T1 e1) [<=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_ty_rec_upper :
forall e1 T1 n1,
  fv_exp_in_exp (open_exp_wrt_ty_rec n1 T1 e1) [<=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_ty_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_ty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp_in_exp e2 `union` fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_exp_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fv_exp_in_exp e2 `union` fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma fv_ty_in_ty_open_ty_wrt_ty_upper :
forall T1 T2,
  fv_ty_in_ty (open_ty_wrt_ty T1 T2) [<=] fv_ty_in_ty T2 `union` fv_ty_in_ty T1.
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve fv_ty_in_ty_open_ty_wrt_ty_upper : lngen.

Lemma fv_ty_in_exp_open_exp_wrt_ty_upper :
forall e1 T1,
  fv_ty_in_exp (open_exp_wrt_ty e1 T1) [<=] fv_ty_in_ty T1 `union` fv_ty_in_exp e1.
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_ty_upper : lngen.

Lemma fv_ty_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_ty_in_exp (open_exp_wrt_exp e1 e2) [<=] fv_ty_in_exp e2 `union` fv_ty_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_ty_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_ty_upper :
forall e1 T1,
  fv_exp_in_exp (open_exp_wrt_ty e1 T1) [<=] fv_exp_in_exp e1.
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_ty_upper : lngen.

Lemma fv_exp_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp_in_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp_in_exp e2 `union` fv_exp_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_in_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_fresh_mutual :
(forall T1 T2 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  fv_ty_in_ty (subst_ty_in_ty T2 X1 T1) [=] fv_ty_in_ty T1).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_fresh :
forall T1 T2 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  fv_ty_in_ty (subst_ty_in_ty T2 X1 T1) [=] fv_ty_in_ty T1.
Proof.
pose proof fv_ty_in_ty_subst_ty_in_ty_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_subst_ty_in_ty_fresh : lngen.
Hint Rewrite fv_ty_in_ty_subst_ty_in_ty_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_fresh_mutual :
(forall e1 T1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  fv_ty_in_exp (subst_ty_in_exp T1 X1 e1) [=] fv_ty_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_fresh :
forall e1 T1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  fv_ty_in_exp (subst_ty_in_exp T1 X1 e1) [=] fv_ty_in_exp e1.
Proof.
pose proof fv_ty_in_exp_subst_ty_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_ty_in_exp_fresh : lngen.
Hint Rewrite fv_ty_in_exp_subst_ty_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 T1 X1,
  fv_exp_in_exp (subst_ty_in_exp T1 X1 e1) [=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_fresh :
forall e1 T1 X1,
  fv_exp_in_exp (subst_ty_in_exp T1 X1 e1) [=] fv_exp_in_exp e1.
Proof.
pose proof fv_ty_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_exp_in_exp_fresh : lngen.
Hint Rewrite fv_ty_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_fresh : lngen.
Hint Rewrite fv_exp_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_lower_mutual :
(forall T1 T2 X1,
  remove X1 (fv_ty_in_ty T1) [<=] fv_ty_in_ty (subst_ty_in_ty T2 X1 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_lower :
forall T1 T2 X1,
  remove X1 (fv_ty_in_ty T1) [<=] fv_ty_in_ty (subst_ty_in_ty T2 X1 T1).
Proof.
pose proof fv_ty_in_ty_subst_ty_in_ty_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_subst_ty_in_ty_lower : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_lower_mutual :
(forall e1 T1 X1,
  remove X1 (fv_ty_in_exp e1) [<=] fv_ty_in_exp (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_lower :
forall e1 T1 X1,
  remove X1 (fv_ty_in_exp e1) [<=] fv_ty_in_exp (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof fv_ty_in_exp_subst_ty_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_ty_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  fv_ty_in_exp e1 [<=] fv_ty_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_ty_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_ty_in_exp_lower_mutual :
(forall e1 T1 X1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_ty_in_exp_lower :
forall e1 T1 X1,
  fv_exp_in_exp e1 [<=] fv_exp_in_exp (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof fv_exp_in_exp_subst_ty_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_ty_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_exp_in_exp e1) [<=] fv_exp_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_exp_in_exp e1) [<=] fv_exp_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_notin_mutual :
(forall T1 T2 X1 X2,
  X2 `notin` fv_ty_in_ty T1 ->
  X2 `notin` fv_ty_in_ty T2 ->
  X2 `notin` fv_ty_in_ty (subst_ty_in_ty T2 X1 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_notin :
forall T1 T2 X1 X2,
  X2 `notin` fv_ty_in_ty T1 ->
  X2 `notin` fv_ty_in_ty T2 ->
  X2 `notin` fv_ty_in_ty (subst_ty_in_ty T2 X1 T1).
Proof.
pose proof fv_ty_in_ty_subst_ty_in_ty_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_subst_ty_in_ty_notin : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_notin_mutual :
(forall e1 T1 X1 X2,
  X2 `notin` fv_ty_in_exp e1 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 `notin` fv_ty_in_exp (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_notin :
forall e1 T1 X1 X2,
  X2 `notin` fv_ty_in_exp e1 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 `notin` fv_ty_in_exp (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof fv_ty_in_exp_subst_ty_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_ty_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_ty_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_ty_in_exp_notin_mutual :
(forall e1 T1 X1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_ty_in_exp_notin :
forall e1 T1 X1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof fv_exp_in_exp_subst_ty_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_ty_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_exp_in_exp e1 ->
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_exp_in_exp e1 ->
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_upper_mutual :
(forall T1 T2 X1,
  fv_ty_in_ty (subst_ty_in_ty T2 X1 T1) [<=] fv_ty_in_ty T2 `union` remove X1 (fv_ty_in_ty T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_ty_subst_ty_in_ty_upper :
forall T1 T2 X1,
  fv_ty_in_ty (subst_ty_in_ty T2 X1 T1) [<=] fv_ty_in_ty T2 `union` remove X1 (fv_ty_in_ty T1).
Proof.
pose proof fv_ty_in_ty_subst_ty_in_ty_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_ty_subst_ty_in_ty_upper : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_upper_mutual :
(forall e1 T1 X1,
  fv_ty_in_exp (subst_ty_in_exp T1 X1 e1) [<=] fv_ty_in_ty T1 `union` remove X1 (fv_ty_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_ty_in_exp_upper :
forall e1 T1 X1,
  fv_ty_in_exp (subst_ty_in_exp T1 X1 e1) [<=] fv_ty_in_ty T1 `union` remove X1 (fv_ty_in_exp e1).
Proof.
pose proof fv_ty_in_exp_subst_ty_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_ty_in_exp_upper : lngen.

(* begin hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  fv_ty_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_ty_in_exp e2 `union` fv_ty_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_ty_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  fv_ty_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_ty_in_exp e2 `union` fv_ty_in_exp e1.
Proof.
pose proof fv_ty_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_ty_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_ty_in_exp_upper_mutual :
(forall e1 T1 X1,
  fv_exp_in_exp (subst_ty_in_exp T1 X1 e1) [<=] fv_exp_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_ty_in_exp_upper :
forall e1 T1 X1,
  fv_exp_in_exp (subst_ty_in_exp T1 X1 e1) [<=] fv_exp_in_exp e1.
Proof.
pose proof fv_exp_in_exp_subst_ty_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_ty_in_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_exp_in_exp e2 `union` remove x1 (fv_exp_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  fv_exp_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fv_exp_in_exp e2 `union` remove x1 (fv_exp_in_exp e1).
Proof.
pose proof fv_exp_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_in_exp_subst_exp_in_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_ty_in_ty_close_ty_wrt_ty_rec_mutual :
(forall T2 T1 X1 X2 n1,
  degree_ty_wrt_ty n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  subst_ty_in_ty T1 X1 (close_ty_wrt_ty_rec n1 X2 T2) = close_ty_wrt_ty_rec n1 X2 (subst_ty_in_ty T1 X1 T2)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_close_ty_wrt_ty_rec :
forall T2 T1 X1 X2 n1,
  degree_ty_wrt_ty n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  subst_ty_in_ty T1 X1 (close_ty_wrt_ty_rec n1 X2 T2) = close_ty_wrt_ty_rec n1 X2 (subst_ty_in_ty T1 X1 T2).
Proof.
pose proof subst_ty_in_ty_close_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_close_ty_wrt_ty_rec : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_close_exp_wrt_ty_rec_mutual :
(forall e1 T1 X1 X2 n1,
  degree_ty_wrt_ty n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  subst_ty_in_exp T1 X1 (close_exp_wrt_ty_rec n1 X2 e1) = close_exp_wrt_ty_rec n1 X2 (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_close_exp_wrt_ty_rec :
forall e1 T1 X1 X2 n1,
  degree_ty_wrt_ty n1 T1 ->
  X1 <> X2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  subst_ty_in_exp T1 X1 (close_exp_wrt_ty_rec n1 X2 e1) = close_exp_wrt_ty_rec n1 X2 (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_ty_rec : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 T1 x1 X1 n1,
  subst_ty_in_exp T1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_ty_in_exp T1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_close_exp_wrt_exp_rec :
forall e1 T1 x1 X1 n1,
  subst_ty_in_exp T1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_ty_in_exp T1 x1 e1).
Proof.
pose proof subst_ty_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ty_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_ty n1 e1 ->
  x1 `notin` fv_ty_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_ty_rec n1 x1 e2) = close_exp_wrt_ty_rec n1 x1 (subst_exp_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ty_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_ty n1 e1 ->
  x1 `notin` fv_ty_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_ty_rec n1 x1 e2) = close_exp_wrt_ty_rec n1 x1 (subst_exp_in_exp e1 X1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_ty_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec : lngen.

Lemma subst_ty_in_ty_close_ty_wrt_ty :
forall T2 T1 X1 X2,
  lc_ty T1 ->  X1 <> X2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  subst_ty_in_ty T1 X1 (close_ty_wrt_ty X2 T2) = close_ty_wrt_ty X2 (subst_ty_in_ty T1 X1 T2).
Proof.
unfold close_ty_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_ty_close_ty_wrt_ty : lngen.

Lemma subst_ty_in_exp_close_exp_wrt_ty :
forall e1 T1 X1 X2,
  lc_ty T1 ->  X1 <> X2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  subst_ty_in_exp T1 X1 (close_exp_wrt_ty X2 e1) = close_exp_wrt_ty X2 (subst_ty_in_exp T1 X1 e1).
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_ty : lngen.

Lemma subst_ty_in_exp_close_exp_wrt_exp :
forall e1 T1 x1 X1,
  lc_ty T1 ->  subst_ty_in_exp T1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_ty_in_exp T1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_ty :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` fv_ty_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_ty x1 e2) = close_exp_wrt_ty x1 (subst_exp_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_ty : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_degree_ty_wrt_ty_mutual :
(forall T1 T2 X1 n1,
  degree_ty_wrt_ty n1 T1 ->
  degree_ty_wrt_ty n1 T2 ->
  degree_ty_wrt_ty n1 (subst_ty_in_ty T2 X1 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_degree_ty_wrt_ty :
forall T1 T2 X1 n1,
  degree_ty_wrt_ty n1 T1 ->
  degree_ty_wrt_ty n1 T2 ->
  degree_ty_wrt_ty n1 (subst_ty_in_ty T2 X1 T1).
Proof.
pose proof subst_ty_in_ty_degree_ty_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_degree_ty_wrt_ty : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_degree_exp_wrt_ty_mutual :
(forall e1 T1 X1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_ty_wrt_ty n1 T1 ->
  degree_exp_wrt_ty n1 (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_degree_exp_wrt_ty :
forall e1 T1 X1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_ty_wrt_ty n1 T1 ->
  degree_exp_wrt_ty n1 (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_degree_exp_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_degree_exp_wrt_ty : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 T1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_degree_exp_wrt_exp :
forall e1 T1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_ty_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty n1 e2 ->
  degree_exp_wrt_ty n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_ty :
forall e1 e2 x1 n1,
  degree_exp_wrt_ty n1 e1 ->
  degree_exp_wrt_ty n1 e2 ->
  degree_exp_wrt_ty n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_degree_exp_wrt_ty : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_fresh_eq_mutual :
(forall T2 T1 X1,
  X1 `notin` fv_ty_in_ty T2 ->
  subst_ty_in_ty T1 X1 T2 = T2).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_fresh_eq :
forall T2 T1 X1,
  X1 `notin` fv_ty_in_ty T2 ->
  subst_ty_in_ty T1 X1 T2 = T2.
Proof.
pose proof subst_ty_in_ty_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_fresh_eq : lngen.
Hint Rewrite subst_ty_in_ty_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_fresh_eq_mutual :
(forall e1 T1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  subst_ty_in_exp T1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_fresh_eq :
forall e1 T1 X1,
  X1 `notin` fv_ty_in_exp e1 ->
  subst_ty_in_exp T1 X1 e1 = e1.
Proof.
pose proof subst_ty_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_fresh_eq : lngen.
Hint Rewrite subst_ty_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_fresh_same_mutual :
(forall T2 T1 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_ty (subst_ty_in_ty T1 X1 T2)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_fresh_same :
forall T2 T1 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_ty (subst_ty_in_ty T1 X1 T2).
Proof.
pose proof subst_ty_in_ty_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_fresh_same : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_fresh_same_mutual :
(forall e1 T1 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_exp (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_fresh_same :
forall e1 T1 X1,
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_exp (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_fresh_mutual :
(forall T2 T1 X1 X2,
  X1 `notin` fv_ty_in_ty T2 ->
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_ty (subst_ty_in_ty T1 X2 T2)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_fresh :
forall T2 T1 X1 X2,
  X1 `notin` fv_ty_in_ty T2 ->
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_ty (subst_ty_in_ty T1 X2 T2).
Proof.
pose proof subst_ty_in_ty_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_fresh : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_fresh_mutual :
(forall e1 T1 X1 X2,
  X1 `notin` fv_ty_in_exp e1 ->
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_exp (subst_ty_in_exp T1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_fresh :
forall e1 T1 X1 X2,
  X1 `notin` fv_ty_in_exp e1 ->
  X1 `notin` fv_ty_in_ty T1 ->
  X1 `notin` fv_ty_in_exp (subst_ty_in_exp T1 X2 e1).
Proof.
pose proof subst_ty_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_exp_in_exp e2 ->
  x1 `notin` fv_exp_in_exp e1 ->
  x1 `notin` fv_exp_in_exp (subst_exp_in_exp e1 x2 e2).
Proof.
pose proof subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_fresh : lngen.

Lemma subst_ty_in_ty_lc_ty :
forall T1 T2 X1,
  lc_ty T1 ->
  lc_ty T2 ->
  lc_ty (subst_ty_in_ty T2 X1 T1).
Proof.
default_simp.
Qed.

Hint Resolve subst_ty_in_ty_lc_ty : lngen.

Lemma subst_ty_in_exp_lc_exp :
forall e1 T1 X1,
  lc_exp e1 ->
  lc_ty T1 ->
  lc_exp (subst_ty_in_exp T1 X1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_ty_in_exp_lc_exp : lngen.

Lemma subst_exp_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_lc_exp : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_open_ty_wrt_ty_rec_mutual :
(forall T3 T1 T2 X1 n1,
  lc_ty T1 ->
  subst_ty_in_ty T1 X1 (open_ty_wrt_ty_rec n1 T2 T3) = open_ty_wrt_ty_rec n1 (subst_ty_in_ty T1 X1 T2) (subst_ty_in_ty T1 X1 T3)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_ty_open_ty_wrt_ty_rec :
forall T3 T1 T2 X1 n1,
  lc_ty T1 ->
  subst_ty_in_ty T1 X1 (open_ty_wrt_ty_rec n1 T2 T3) = open_ty_wrt_ty_rec n1 (subst_ty_in_ty T1 X1 T2) (subst_ty_in_ty T1 X1 T3).
Proof.
pose proof subst_ty_in_ty_open_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_open_ty_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_open_exp_wrt_ty_rec_mutual :
(forall e1 T1 T2 X1 n1,
  lc_ty T1 ->
  subst_ty_in_exp T1 X1 (open_exp_wrt_ty_rec n1 T2 e1) = open_exp_wrt_ty_rec n1 (subst_ty_in_ty T1 X1 T2) (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_open_exp_wrt_ty_rec :
forall e1 T1 T2 X1 n1,
  lc_ty T1 ->
  subst_ty_in_exp T1 X1 (open_exp_wrt_ty_rec n1 T2 e1) = open_exp_wrt_ty_rec n1 (subst_ty_in_ty T1 X1 T2) (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 T1 e1 X1 n1,
  subst_ty_in_exp T1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_ty_in_exp T1 X1 e1) (subst_ty_in_exp T1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_open_exp_wrt_exp_rec :
forall e2 T1 e1 X1 n1,
  subst_ty_in_exp T1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_ty_in_exp T1 X1 e1) (subst_ty_in_exp T1 X1 e2).
Proof.
pose proof subst_ty_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_ty_rec_mutual :
(forall e2 e1 T1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_ty_rec n1 T1 e2) = open_exp_wrt_ty_rec n1 T1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_ty_rec :
forall e2 e1 T1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_ty_rec n1 T1 e2) = open_exp_wrt_ty_rec n1 T1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_ty_in_ty_open_ty_wrt_ty :
forall T3 T1 T2 X1,
  lc_ty T1 ->
  subst_ty_in_ty T1 X1 (open_ty_wrt_ty T3 T2) = open_ty_wrt_ty (subst_ty_in_ty T1 X1 T3) (subst_ty_in_ty T1 X1 T2).
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_ty_open_ty_wrt_ty : lngen.

Lemma subst_ty_in_exp_open_exp_wrt_ty :
forall e1 T1 T2 X1,
  lc_ty T1 ->
  subst_ty_in_exp T1 X1 (open_exp_wrt_ty e1 T2) = open_exp_wrt_ty (subst_ty_in_exp T1 X1 e1) (subst_ty_in_ty T1 X1 T2).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_open_exp_wrt_ty : lngen.

Lemma subst_ty_in_exp_open_exp_wrt_exp :
forall e2 T1 e1 X1,
  subst_ty_in_exp T1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_ty_in_exp T1 X1 e2) (subst_ty_in_exp T1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_ty :
forall e2 e1 T1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_ty e2 T1) = open_exp_wrt_ty (subst_exp_in_exp e1 x1 e2) T1.
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_ty : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_ty_in_ty_open_ty_wrt_ty_var :
forall T2 T1 X1 X2,
  X1 <> X2 ->
  lc_ty T1 ->
  open_ty_wrt_ty (subst_ty_in_ty T1 X1 T2) (ty_var_f X2) = subst_ty_in_ty T1 X1 (open_ty_wrt_ty T2 (ty_var_f X2)).
Proof.
intros; rewrite subst_ty_in_ty_open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_ty_open_ty_wrt_ty_var : lngen.

Lemma subst_ty_in_exp_open_exp_wrt_ty_var :
forall e1 T1 X1 X2,
  X1 <> X2 ->
  lc_ty T1 ->
  open_exp_wrt_ty (subst_ty_in_exp T1 X1 e1) (ty_var_f X2) = subst_ty_in_exp T1 X1 (open_exp_wrt_ty e1 (ty_var_f X2)).
Proof.
intros; rewrite subst_ty_in_exp_open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_open_exp_wrt_ty_var : lngen.

Lemma subst_ty_in_exp_open_exp_wrt_exp_var :
forall e1 T1 X1 x1,
  open_exp_wrt_exp (subst_ty_in_exp T1 X1 e1) (exp_var_f x1) = subst_ty_in_exp T1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_ty_in_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_ty_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_ty (subst_exp_in_exp e1 x1 e2) (ty_var_f X1) = subst_exp_in_exp e1 x1 (open_exp_wrt_ty e2 (ty_var_f X1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_ty_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp_in_exp e1 x1 e2) (exp_var_f x2) = subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_spec_rec_mutual :
(forall T1 T2 X1 n1,
  subst_ty_in_ty T2 X1 T1 = open_ty_wrt_ty_rec n1 T2 (close_ty_wrt_ty_rec n1 X1 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_ty_spec_rec :
forall T1 T2 X1 n1,
  subst_ty_in_ty T2 X1 T1 = open_ty_wrt_ty_rec n1 T2 (close_ty_wrt_ty_rec n1 X1 T1).
Proof.
pose proof subst_ty_in_ty_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_spec_rec_mutual :
(forall e1 T1 X1 n1,
  subst_ty_in_exp T1 X1 e1 = open_exp_wrt_ty_rec n1 T1 (close_exp_wrt_ty_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_spec_rec :
forall e1 T1 X1 n1,
  subst_ty_in_exp T1 X1 e1 = open_exp_wrt_ty_rec n1 T1 (close_exp_wrt_ty_rec n1 X1 e1).
Proof.
pose proof subst_ty_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_spec_rec : lngen.

(* end hide *)

Lemma subst_ty_in_ty_spec :
forall T1 T2 X1,
  subst_ty_in_ty T2 X1 T1 = open_ty_wrt_ty (close_ty_wrt_ty X1 T1) T2.
Proof.
unfold close_ty_wrt_ty; unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_ty_spec : lngen.

Lemma subst_ty_in_exp_spec :
forall e1 T1 X1,
  subst_ty_in_exp T1 X1 e1 = open_exp_wrt_ty (close_exp_wrt_ty X1 e1) T1.
Proof.
unfold close_exp_wrt_ty; unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_spec : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_subst_ty_in_ty_mutual :
(forall T1 T2 T3 X2 X1,
  X2 `notin` fv_ty_in_ty T2 ->
  X2 <> X1 ->
  subst_ty_in_ty T2 X1 (subst_ty_in_ty T3 X2 T1) = subst_ty_in_ty (subst_ty_in_ty T2 X1 T3) X2 (subst_ty_in_ty T2 X1 T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_subst_ty_in_ty :
forall T1 T2 T3 X2 X1,
  X2 `notin` fv_ty_in_ty T2 ->
  X2 <> X1 ->
  subst_ty_in_ty T2 X1 (subst_ty_in_ty T3 X2 T1) = subst_ty_in_ty (subst_ty_in_ty T2 X1 T3) X2 (subst_ty_in_ty T2 X1 T1).
Proof.
pose proof subst_ty_in_ty_subst_ty_in_ty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_subst_ty_in_ty : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_subst_ty_in_exp_mutual :
(forall e1 T1 T2 X2 X1,
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  subst_ty_in_exp T1 X1 (subst_ty_in_exp T2 X2 e1) = subst_ty_in_exp (subst_ty_in_ty T1 X1 T2) X2 (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_subst_ty_in_exp :
forall e1 T1 T2 X2 X1,
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  subst_ty_in_exp T1 X1 (subst_ty_in_exp T2 X2 e1) = subst_ty_in_exp (subst_ty_in_ty T1 X1 T2) X2 (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_subst_ty_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_subst_ty_in_exp : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_subst_exp_in_exp_mutual :
(forall e1 T1 e2 x1 X1,
  subst_ty_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_ty_in_exp T1 X1 e2) x1 (subst_ty_in_exp T1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_subst_exp_in_exp :
forall e1 T1 e2 x1 X1,
  subst_ty_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_ty_in_exp T1 X1 e2) x1 (subst_ty_in_exp T1 X1 e1).
Proof.
pose proof subst_ty_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_ty_in_exp_mutual :
(forall e1 e2 T1 X1 x1,
  X1 `notin` fv_ty_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_ty_in_exp T1 X1 e1) = subst_ty_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_ty_in_exp :
forall e1 e2 T1 X1 x1,
  X1 `notin` fv_ty_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_ty_in_exp T1 X1 e1) = subst_ty_in_exp T1 X1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_ty_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_subst_ty_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_close_ty_wrt_ty_rec_open_ty_wrt_ty_rec_mutual :
(forall T2 T1 X1 X2 n1,
  X2 `notin` fv_ty_in_ty T2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  degree_ty_wrt_ty n1 T1 ->
  subst_ty_in_ty T1 X1 T2 = close_ty_wrt_ty_rec n1 X2 (subst_ty_in_ty T1 X1 (open_ty_wrt_ty_rec n1 (ty_var_f X2) T2))).
Proof.
apply_mutual_ind ty_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_ty_close_ty_wrt_ty_rec_open_ty_wrt_ty_rec :
forall T2 T1 X1 X2 n1,
  X2 `notin` fv_ty_in_ty T2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  degree_ty_wrt_ty n1 T1 ->
  subst_ty_in_ty T1 X1 T2 = close_ty_wrt_ty_rec n1 X2 (subst_ty_in_ty T1 X1 (open_ty_wrt_ty_rec n1 (ty_var_f X2) T2)).
Proof.
pose proof subst_ty_in_ty_close_ty_wrt_ty_rec_open_ty_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_close_ty_wrt_ty_rec_open_ty_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec_mutual :
(forall e1 T1 X1 X2 n1,
  X2 `notin` fv_ty_in_exp e1 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  degree_ty_wrt_ty n1 T1 ->
  subst_ty_in_exp T1 X1 e1 = close_exp_wrt_ty_rec n1 X2 (subst_ty_in_exp T1 X1 (open_exp_wrt_ty_rec n1 (ty_var_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec :
forall e1 T1 X1 X2 n1,
  X2 `notin` fv_ty_in_exp e1 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  degree_ty_wrt_ty n1 T1 ->
  subst_ty_in_exp T1 X1 e1 = close_exp_wrt_ty_rec n1 X2 (subst_ty_in_exp T1 X1 (open_exp_wrt_ty_rec n1 (ty_var_f X2) e1)).
Proof.
pose proof subst_ty_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 T1 X1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  subst_ty_in_exp T1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_ty_in_exp T1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ty_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 T1 X1 x1 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  subst_ty_in_exp T1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_ty_in_exp T1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_ty_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp e1 ->
  degree_exp_wrt_ty n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_ty_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ty_rec n1 (ty_var_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp e1 ->
  degree_exp_wrt_ty n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_ty_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ty_rec n1 (ty_var_f X1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_ty_rec_open_exp_wrt_ty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_ty_in_ty_close_ty_wrt_ty_open_ty_wrt_ty :
forall T2 T1 X1 X2,
  X2 `notin` fv_ty_in_ty T2 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  lc_ty T1 ->
  subst_ty_in_ty T1 X1 T2 = close_ty_wrt_ty X2 (subst_ty_in_ty T1 X1 (open_ty_wrt_ty T2 (ty_var_f X2))).
Proof.
unfold close_ty_wrt_ty; unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_ty_close_ty_wrt_ty_open_ty_wrt_ty : lngen.

Lemma subst_ty_in_exp_close_exp_wrt_ty_open_exp_wrt_ty :
forall e1 T1 X1 X2,
  X2 `notin` fv_ty_in_exp e1 ->
  X2 `notin` fv_ty_in_ty T1 ->
  X2 <> X1 ->
  lc_ty T1 ->
  subst_ty_in_exp T1 X1 e1 = close_exp_wrt_ty X2 (subst_ty_in_exp T1 X1 (open_exp_wrt_ty e1 (ty_var_f X2))).
Proof.
unfold close_exp_wrt_ty; unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_ty_open_exp_wrt_ty : lngen.

Lemma subst_ty_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 T1 X1 x1,
  x1 `notin` fv_exp_in_exp e1 ->
  lc_ty T1 ->
  subst_ty_in_exp T1 X1 e1 = close_exp_wrt_exp x1 (subst_ty_in_exp T1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_ty_open_exp_wrt_ty :
forall e2 e1 x1 X1,
  X1 `notin` fv_ty_in_exp e2 ->
  X1 `notin` fv_ty_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_ty X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ty e2 (ty_var_f X1))).
Proof.
unfold close_exp_wrt_ty; unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_ty_open_exp_wrt_ty : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fv_exp_in_exp e2 ->
  x2 `notin` fv_exp_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_ty_in_ty_ty_all :
forall X2 T2 T1 X1,
  lc_ty T1 ->
  X2 `notin` fv_ty_in_ty T1 `union` fv_ty_in_ty T2 `union` singleton X1 ->
  subst_ty_in_ty T1 X1 (ty_all T2) = ty_all (close_ty_wrt_ty X2 (subst_ty_in_ty T1 X1 (open_ty_wrt_ty T2 (ty_var_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_ty_in_ty_ty_all : lngen.

Lemma subst_ty_in_exp_exp_abs :
forall x1 e1 T1 X1,
  lc_ty T1 ->
  x1 `notin` fv_exp_in_exp e1 ->
  subst_ty_in_exp T1 X1 (exp_abs e1) = exp_abs (close_exp_wrt_exp x1 (subst_ty_in_exp T1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_ty_in_exp_exp_abs : lngen.

Lemma subst_ty_in_exp_exp_tabs :
forall X2 e1 T1 X1,
  lc_ty T1 ->
  X2 `notin` fv_ty_in_ty T1 `union` fv_ty_in_exp e1 `union` singleton X1 ->
  subst_ty_in_exp T1 X1 (exp_tabs e1) = exp_tabs (close_exp_wrt_ty X2 (subst_ty_in_exp T1 X1 (open_exp_wrt_ty e1 (ty_var_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_ty_in_exp_exp_tabs : lngen.

Lemma subst_exp_in_exp_exp_abs :
forall x2 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fv_exp_in_exp e1 `union` fv_exp_in_exp e2 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_abs e2) = exp_abs (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_exp_abs : lngen.

Lemma subst_exp_in_exp_exp_tabs :
forall X1 e2 e1 x1,
  lc_exp e1 ->
  X1 `notin` fv_ty_in_exp e1 `union` fv_ty_in_exp e2 ->
  subst_exp_in_exp e1 x1 (exp_tabs e2) = exp_tabs (close_exp_wrt_ty X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ty e2 (ty_var_f X1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_in_exp_exp_tabs : lngen.

(* begin hide *)

Lemma subst_ty_in_ty_intro_rec_mutual :
(forall T1 X1 T2 n1,
  X1 `notin` fv_ty_in_ty T1 ->
  open_ty_wrt_ty_rec n1 T2 T1 = subst_ty_in_ty T2 X1 (open_ty_wrt_ty_rec n1 (ty_var_f X1) T1)).
Proof.
apply_mutual_ind ty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_ty_intro_rec :
forall T1 X1 T2 n1,
  X1 `notin` fv_ty_in_ty T1 ->
  open_ty_wrt_ty_rec n1 T2 T1 = subst_ty_in_ty T2 X1 (open_ty_wrt_ty_rec n1 (ty_var_f X1) T1).
Proof.
pose proof subst_ty_in_ty_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_ty_intro_rec : lngen.
Hint Rewrite subst_ty_in_ty_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ty_in_exp_intro_rec_mutual :
(forall e1 X1 T1 n1,
  X1 `notin` fv_ty_in_exp e1 ->
  open_exp_wrt_ty_rec n1 T1 e1 = subst_ty_in_exp T1 X1 (open_exp_wrt_ty_rec n1 (ty_var_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ty_in_exp_intro_rec :
forall e1 X1 T1 n1,
  X1 `notin` fv_ty_in_exp e1 ->
  open_exp_wrt_ty_rec n1 T1 e1 = subst_ty_in_exp T1 X1 (open_exp_wrt_ty_rec n1 (ty_var_f X1) e1).
Proof.
pose proof subst_ty_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_ty_in_exp_intro_rec : lngen.
Hint Rewrite subst_ty_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof subst_exp_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_in_exp_intro_rec : lngen.
Hint Rewrite subst_exp_in_exp_intro_rec using solve [auto] : lngen.

Lemma subst_ty_in_ty_intro :
forall X1 T1 T2,
  X1 `notin` fv_ty_in_ty T1 ->
  open_ty_wrt_ty T1 T2 = subst_ty_in_ty T2 X1 (open_ty_wrt_ty T1 (ty_var_f X1)).
Proof.
unfold open_ty_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_ty_intro : lngen.

Lemma subst_ty_in_exp_intro :
forall X1 e1 T1,
  X1 `notin` fv_ty_in_exp e1 ->
  open_exp_wrt_ty e1 T1 = subst_ty_in_exp T1 X1 (open_exp_wrt_ty e1 (ty_var_f X1)).
Proof.
unfold open_exp_wrt_ty; default_simp.
Qed.

Hint Resolve subst_ty_in_exp_intro : lngen.

Lemma subst_exp_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_exp_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_in_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
