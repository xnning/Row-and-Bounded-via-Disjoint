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

Scheme sty_ind' := Induction for sty Sort Prop.

Definition sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme sty_rec' := Induction for sty Sort Set.

Definition sty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  sty_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme sexp_ind' := Induction for sexp Sort Prop.

Definition sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme sexp_rec' := Induction for sexp Sort Set.

Definition sexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  sexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_sty_wrt_sty_rec (n1 : nat) (X1 : typvar) (A1 : sty) {struct A1} : sty :=
  match A1 with
    | sty_nat => sty_nat
    | sty_top => sty_top
    | sty_bot => sty_bot
    | sty_var_f X2 => if (X1 == X2) then (sty_var_b n1) else (sty_var_f X2)
    | sty_var_b n2 => if (lt_ge_dec n2 n1) then (sty_var_b n2) else (sty_var_b (S n2))
    | sty_arrow A2 B1 => sty_arrow (close_sty_wrt_sty_rec n1 X1 A2) (close_sty_wrt_sty_rec n1 X1 B1)
    | sty_and A2 B1 => sty_and (close_sty_wrt_sty_rec n1 X1 A2) (close_sty_wrt_sty_rec n1 X1 B1)
    | sty_all A2 B1 => sty_all (close_sty_wrt_sty_rec n1 X1 A2) (close_sty_wrt_sty_rec (S n1) X1 B1)
    | sty_rcd l1 A2 => sty_rcd l1 (close_sty_wrt_sty_rec n1 X1 A2)
  end.

Definition close_sty_wrt_sty X1 A1 := close_sty_wrt_sty_rec 0 X1 A1.

Fixpoint close_sexp_wrt_sty_rec (n1 : nat) (X1 : typvar) (ee1 : sexp) {struct ee1} : sexp :=
  match ee1 with
    | sexp_var_f x1 => sexp_var_f x1
    | sexp_var_b n2 => sexp_var_b n2
    | sexp_top => sexp_top
    | sexp_lit i1 => sexp_lit i1
    | sexp_abs ee2 => sexp_abs (close_sexp_wrt_sty_rec n1 X1 ee2)
    | sexp_app ee2 ee3 => sexp_app (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sexp_wrt_sty_rec n1 X1 ee3)
    | sexp_merge ee2 ee3 => sexp_merge (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sexp_wrt_sty_rec n1 X1 ee3)
    | sexp_tabs A1 ee2 => sexp_tabs (close_sty_wrt_sty_rec n1 X1 A1) (close_sexp_wrt_sty_rec (S n1) X1 ee2)
    | sexp_tapp ee2 A1 => sexp_tapp (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sty_wrt_sty_rec n1 X1 A1)
    | sexp_anno ee2 A1 => sexp_anno (close_sexp_wrt_sty_rec n1 X1 ee2) (close_sty_wrt_sty_rec n1 X1 A1)
    | sexp_rcd l1 ee2 => sexp_rcd l1 (close_sexp_wrt_sty_rec n1 X1 ee2)
    | sexp_proj ee2 l1 => sexp_proj (close_sexp_wrt_sty_rec n1 X1 ee2) l1
  end.

Fixpoint close_sexp_wrt_sexp_rec (n1 : nat) (x1 : expvar) (ee1 : sexp) {struct ee1} : sexp :=
  match ee1 with
    | sexp_var_f x2 => if (x1 == x2) then (sexp_var_b n1) else (sexp_var_f x2)
    | sexp_var_b n2 => if (lt_ge_dec n2 n1) then (sexp_var_b n2) else (sexp_var_b (S n2))
    | sexp_top => sexp_top
    | sexp_lit i1 => sexp_lit i1
    | sexp_abs ee2 => sexp_abs (close_sexp_wrt_sexp_rec (S n1) x1 ee2)
    | sexp_app ee2 ee3 => sexp_app (close_sexp_wrt_sexp_rec n1 x1 ee2) (close_sexp_wrt_sexp_rec n1 x1 ee3)
    | sexp_merge ee2 ee3 => sexp_merge (close_sexp_wrt_sexp_rec n1 x1 ee2) (close_sexp_wrt_sexp_rec n1 x1 ee3)
    | sexp_tabs A1 ee2 => sexp_tabs A1 (close_sexp_wrt_sexp_rec n1 x1 ee2)
    | sexp_tapp ee2 A1 => sexp_tapp (close_sexp_wrt_sexp_rec n1 x1 ee2) A1
    | sexp_anno ee2 A1 => sexp_anno (close_sexp_wrt_sexp_rec n1 x1 ee2) A1
    | sexp_rcd l1 ee2 => sexp_rcd l1 (close_sexp_wrt_sexp_rec n1 x1 ee2)
    | sexp_proj ee2 l1 => sexp_proj (close_sexp_wrt_sexp_rec n1 x1 ee2) l1
  end.

Definition close_sexp_wrt_sty X1 ee1 := close_sexp_wrt_sty_rec 0 X1 ee1.

Definition close_sexp_wrt_sexp x1 ee1 := close_sexp_wrt_sexp_rec 0 x1 ee1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_sty (A1 : sty) {struct A1} : nat :=
  match A1 with
    | sty_nat => 1
    | sty_top => 1
    | sty_bot => 1
    | sty_var_f X1 => 1
    | sty_var_b n1 => 1
    | sty_arrow A2 B1 => 1 + (size_sty A2) + (size_sty B1)
    | sty_and A2 B1 => 1 + (size_sty A2) + (size_sty B1)
    | sty_all A2 B1 => 1 + (size_sty A2) + (size_sty B1)
    | sty_rcd l1 A2 => 1 + (size_sty A2)
  end.

Fixpoint size_sexp (ee1 : sexp) {struct ee1} : nat :=
  match ee1 with
    | sexp_var_f x1 => 1
    | sexp_var_b n1 => 1
    | sexp_top => 1
    | sexp_lit i1 => 1
    | sexp_abs ee2 => 1 + (size_sexp ee2)
    | sexp_app ee2 ee3 => 1 + (size_sexp ee2) + (size_sexp ee3)
    | sexp_merge ee2 ee3 => 1 + (size_sexp ee2) + (size_sexp ee3)
    | sexp_tabs A1 ee2 => 1 + (size_sty A1) + (size_sexp ee2)
    | sexp_tapp ee2 A1 => 1 + (size_sexp ee2) + (size_sty A1)
    | sexp_anno ee2 A1 => 1 + (size_sexp ee2) + (size_sty A1)
    | sexp_rcd l1 ee2 => 1 + (size_sexp ee2)
    | sexp_proj ee2 l1 => 1 + (size_sexp ee2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_sty_wrt_sty : nat -> sty -> Prop :=
  | degree_wrt_sty_sty_nat : forall n1,
    degree_sty_wrt_sty n1 (sty_nat)
  | degree_wrt_sty_sty_top : forall n1,
    degree_sty_wrt_sty n1 (sty_top)
  | degree_wrt_sty_sty_bot : forall n1,
    degree_sty_wrt_sty n1 (sty_bot)
  | degree_wrt_sty_sty_var_f : forall n1 X1,
    degree_sty_wrt_sty n1 (sty_var_f X1)
  | degree_wrt_sty_sty_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_sty_wrt_sty n1 (sty_var_b n2)
  | degree_wrt_sty_sty_arrow : forall n1 A1 B1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty n1 B1 ->
    degree_sty_wrt_sty n1 (sty_arrow A1 B1)
  | degree_wrt_sty_sty_and : forall n1 A1 B1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty n1 B1 ->
    degree_sty_wrt_sty n1 (sty_and A1 B1)
  | degree_wrt_sty_sty_all : forall n1 A1 B1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty (S n1) B1 ->
    degree_sty_wrt_sty n1 (sty_all A1 B1)
  | degree_wrt_sty_sty_rcd : forall n1 l1 A1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sty_wrt_sty n1 (sty_rcd l1 A1).

Scheme degree_sty_wrt_sty_ind' := Induction for degree_sty_wrt_sty Sort Prop.

Definition degree_sty_wrt_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_sty_wrt_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors degree_sty_wrt_sty : core lngen.

Inductive degree_sexp_wrt_sty : nat -> sexp -> Prop :=
  | degree_wrt_sty_sexp_var_f : forall n1 x1,
    degree_sexp_wrt_sty n1 (sexp_var_f x1)
  | degree_wrt_sty_sexp_var_b : forall n1 n2,
    degree_sexp_wrt_sty n1 (sexp_var_b n2)
  | degree_wrt_sty_sexp_top : forall n1,
    degree_sexp_wrt_sty n1 (sexp_top)
  | degree_wrt_sty_sexp_lit : forall n1 i1,
    degree_sexp_wrt_sty n1 (sexp_lit i1)
  | degree_wrt_sty_sexp_abs : forall n1 ee1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 (sexp_abs ee1)
  | degree_wrt_sty_sexp_app : forall n1 ee1 ee2,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 ee2 ->
    degree_sexp_wrt_sty n1 (sexp_app ee1 ee2)
  | degree_wrt_sty_sexp_merge : forall n1 ee1 ee2,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 ee2 ->
    degree_sexp_wrt_sty n1 (sexp_merge ee1 ee2)
  | degree_wrt_sty_sexp_tabs : forall n1 A1 ee1,
    degree_sty_wrt_sty n1 A1 ->
    degree_sexp_wrt_sty (S n1) ee1 ->
    degree_sexp_wrt_sty n1 (sexp_tabs A1 ee1)
  | degree_wrt_sty_sexp_tapp : forall n1 ee1 A1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sty_wrt_sty n1 A1 ->
    degree_sexp_wrt_sty n1 (sexp_tapp ee1 A1)
  | degree_wrt_sty_sexp_anno : forall n1 ee1 A1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sty_wrt_sty n1 A1 ->
    degree_sexp_wrt_sty n1 (sexp_anno ee1 A1)
  | degree_wrt_sty_sexp_rcd : forall n1 l1 ee1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 (sexp_rcd l1 ee1)
  | degree_wrt_sty_sexp_proj : forall n1 ee1 l1,
    degree_sexp_wrt_sty n1 ee1 ->
    degree_sexp_wrt_sty n1 (sexp_proj ee1 l1).

Inductive degree_sexp_wrt_sexp : nat -> sexp -> Prop :=
  | degree_wrt_sexp_sexp_var_f : forall n1 x1,
    degree_sexp_wrt_sexp n1 (sexp_var_f x1)
  | degree_wrt_sexp_sexp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_sexp_wrt_sexp n1 (sexp_var_b n2)
  | degree_wrt_sexp_sexp_top : forall n1,
    degree_sexp_wrt_sexp n1 (sexp_top)
  | degree_wrt_sexp_sexp_lit : forall n1 i1,
    degree_sexp_wrt_sexp n1 (sexp_lit i1)
  | degree_wrt_sexp_sexp_abs : forall n1 ee1,
    degree_sexp_wrt_sexp (S n1) ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_abs ee1)
  | degree_wrt_sexp_sexp_app : forall n1 ee1 ee2,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 ee2 ->
    degree_sexp_wrt_sexp n1 (sexp_app ee1 ee2)
  | degree_wrt_sexp_sexp_merge : forall n1 ee1 ee2,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 ee2 ->
    degree_sexp_wrt_sexp n1 (sexp_merge ee1 ee2)
  | degree_wrt_sexp_sexp_tabs : forall n1 A1 ee1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_tabs A1 ee1)
  | degree_wrt_sexp_sexp_tapp : forall n1 ee1 A1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_tapp ee1 A1)
  | degree_wrt_sexp_sexp_anno : forall n1 ee1 A1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_anno ee1 A1)
  | degree_wrt_sexp_sexp_rcd : forall n1 l1 ee1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_rcd l1 ee1)
  | degree_wrt_sexp_sexp_proj : forall n1 ee1 l1,
    degree_sexp_wrt_sexp n1 ee1 ->
    degree_sexp_wrt_sexp n1 (sexp_proj ee1 l1).

Scheme degree_sexp_wrt_sty_ind' := Induction for degree_sexp_wrt_sty Sort Prop.

Definition degree_sexp_wrt_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  degree_sexp_wrt_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Scheme degree_sexp_wrt_sexp_ind' := Induction for degree_sexp_wrt_sexp Sort Prop.

Definition degree_sexp_wrt_sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  degree_sexp_wrt_sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.

Hint Constructors degree_sexp_wrt_sty : core lngen.

Hint Constructors degree_sexp_wrt_sexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_sty : sty -> Set :=
  | lc_set_sty_nat :
    lc_set_sty (sty_nat)
  | lc_set_sty_top :
    lc_set_sty (sty_top)
  | lc_set_sty_bot :
    lc_set_sty (sty_bot)
  | lc_set_sty_var_f : forall X1,
    lc_set_sty (sty_var_f X1)
  | lc_set_sty_arrow : forall A1 B1,
    lc_set_sty A1 ->
    lc_set_sty B1 ->
    lc_set_sty (sty_arrow A1 B1)
  | lc_set_sty_and : forall A1 B1,
    lc_set_sty A1 ->
    lc_set_sty B1 ->
    lc_set_sty (sty_and A1 B1)
  | lc_set_sty_all : forall A1 B1,
    lc_set_sty A1 ->
    (forall X1 : typvar, lc_set_sty (open_sty_wrt_sty B1 (sty_var_f X1))) ->
    lc_set_sty (sty_all A1 B1)
  | lc_set_sty_rcd : forall l1 A1,
    lc_set_sty A1 ->
    lc_set_sty (sty_rcd l1 A1).

Scheme lc_sty_ind' := Induction for lc_sty Sort Prop.

Definition lc_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_sty_ind' := Induction for lc_set_sty Sort Prop.

Definition lc_set_sty_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_sty_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_sty_rec' := Induction for lc_set_sty Sort Set.

Definition lc_set_sty_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_sty_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors lc_sty : core lngen.

Hint Constructors lc_set_sty : core lngen.

Inductive lc_set_sexp : sexp -> Set :=
  | lc_set_sexp_var_f : forall x1,
    lc_set_sexp (sexp_var_f x1)
  | lc_set_sexp_top :
    lc_set_sexp (sexp_top)
  | lc_set_sexp_lit : forall i1,
    lc_set_sexp (sexp_lit i1)
  | lc_set_sexp_abs : forall ee1,
    (forall x1 : expvar, lc_set_sexp (open_sexp_wrt_sexp ee1 (sexp_var_f x1))) ->
    lc_set_sexp (sexp_abs ee1)
  | lc_set_sexp_app : forall ee1 ee2,
    lc_set_sexp ee1 ->
    lc_set_sexp ee2 ->
    lc_set_sexp (sexp_app ee1 ee2)
  | lc_set_sexp_merge : forall ee1 ee2,
    lc_set_sexp ee1 ->
    lc_set_sexp ee2 ->
    lc_set_sexp (sexp_merge ee1 ee2)
  | lc_set_sexp_tabs : forall A1 ee1,
    lc_set_sty A1 ->
    (forall X1 : typvar, lc_set_sexp (open_sexp_wrt_sty ee1 (sty_var_f X1))) ->
    lc_set_sexp (sexp_tabs A1 ee1)
  | lc_set_sexp_tapp : forall ee1 A1,
    lc_set_sexp ee1 ->
    lc_set_sty A1 ->
    lc_set_sexp (sexp_tapp ee1 A1)
  | lc_set_sexp_anno : forall ee1 A1,
    lc_set_sexp ee1 ->
    lc_set_sty A1 ->
    lc_set_sexp (sexp_anno ee1 A1)
  | lc_set_sexp_rcd : forall l1 ee1,
    lc_set_sexp ee1 ->
    lc_set_sexp (sexp_rcd l1 ee1)
  | lc_set_sexp_proj : forall ee1 l1,
    lc_set_sexp ee1 ->
    lc_set_sexp (sexp_proj ee1 l1).

Scheme lc_sexp_ind' := Induction for lc_sexp Sort Prop.

Definition lc_sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  lc_sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme lc_set_sexp_ind' := Induction for lc_set_sexp Sort Prop.

Definition lc_set_sexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  lc_set_sexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme lc_set_sexp_rec' := Induction for lc_set_sexp Sort Set.

Definition lc_set_sexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  lc_set_sexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Hint Constructors lc_sexp : core lngen.

Hint Constructors lc_set_sexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_sty_wrt_sty A1 := forall X1, lc_sty (open_sty_wrt_sty A1 (sty_var_f X1)).

Hint Unfold body_sty_wrt_sty.

Definition body_sexp_wrt_sty ee1 := forall X1, lc_sexp (open_sexp_wrt_sty ee1 (sty_var_f X1)).

Definition body_sexp_wrt_sexp ee1 := forall x1, lc_sexp (open_sexp_wrt_sexp ee1 (sexp_var_f x1)).

Hint Unfold body_sexp_wrt_sty.

Hint Unfold body_sexp_wrt_sexp.


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

Lemma size_sty_min_mutual :
(forall A1, 1 <= size_sty A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_sty_min :
forall A1, 1 <= size_sty A1.
Proof.
pose proof size_sty_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sty_min : lngen.

(* begin hide *)

Lemma size_sexp_min_mutual :
(forall ee1, 1 <= size_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_sexp_min :
forall ee1, 1 <= size_sexp ee1.
Proof.
pose proof size_sexp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_min : lngen.

(* begin hide *)

Lemma size_sty_close_sty_wrt_sty_rec_mutual :
(forall A1 X1 n1,
  size_sty (close_sty_wrt_sty_rec n1 X1 A1) = size_sty A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sty_close_sty_wrt_sty_rec :
forall A1 X1 n1,
  size_sty (close_sty_wrt_sty_rec n1 X1 A1) = size_sty A1.
Proof.
pose proof size_sty_close_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sty_close_sty_wrt_sty_rec : lngen.
Hint Rewrite size_sty_close_sty_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_sexp_close_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1,
  size_sexp (close_sexp_wrt_sty_rec n1 X1 ee1) = size_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sexp_close_sexp_wrt_sty_rec :
forall ee1 X1 n1,
  size_sexp (close_sexp_wrt_sty_rec n1 X1 ee1) = size_sexp ee1.
Proof.
pose proof size_sexp_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_close_sexp_wrt_sty_rec : lngen.
Hint Rewrite size_sexp_close_sexp_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_sexp_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1,
  size_sexp (close_sexp_wrt_sexp_rec n1 x1 ee1) = size_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sexp_close_sexp_wrt_sexp_rec :
forall ee1 x1 n1,
  size_sexp (close_sexp_wrt_sexp_rec n1 x1 ee1) = size_sexp ee1.
Proof.
pose proof size_sexp_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_close_sexp_wrt_sexp_rec : lngen.
Hint Rewrite size_sexp_close_sexp_wrt_sexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_sty_close_sty_wrt_sty :
forall A1 X1,
  size_sty (close_sty_wrt_sty X1 A1) = size_sty A1.
Proof.
unfold close_sty_wrt_sty; default_simp.
Qed.

Hint Resolve size_sty_close_sty_wrt_sty : lngen.
Hint Rewrite size_sty_close_sty_wrt_sty using solve [auto] : lngen.

Lemma size_sexp_close_sexp_wrt_sty :
forall ee1 X1,
  size_sexp (close_sexp_wrt_sty X1 ee1) = size_sexp ee1.
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve size_sexp_close_sexp_wrt_sty : lngen.
Hint Rewrite size_sexp_close_sexp_wrt_sty using solve [auto] : lngen.

Lemma size_sexp_close_sexp_wrt_sexp :
forall ee1 x1,
  size_sexp (close_sexp_wrt_sexp x1 ee1) = size_sexp ee1.
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve size_sexp_close_sexp_wrt_sexp : lngen.
Hint Rewrite size_sexp_close_sexp_wrt_sexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_sty_open_sty_wrt_sty_rec_mutual :
(forall A1 A2 n1,
  size_sty A1 <= size_sty (open_sty_wrt_sty_rec n1 A2 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sty_open_sty_wrt_sty_rec :
forall A1 A2 n1,
  size_sty A1 <= size_sty (open_sty_wrt_sty_rec n1 A2 A1).
Proof.
pose proof size_sty_open_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sty_open_sty_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sty_rec_mutual :
(forall ee1 A1 n1,
  size_sexp ee1 <= size_sexp (open_sexp_wrt_sty_rec n1 A1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sty_rec :
forall ee1 A1 n1,
  size_sexp ee1 <= size_sexp (open_sexp_wrt_sty_rec n1 A1 ee1).
Proof.
pose proof size_sexp_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sexp_rec_mutual :
(forall ee1 ee2 n1,
  size_sexp ee1 <= size_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sexp_rec :
forall ee1 ee2 n1,
  size_sexp ee1 <= size_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1).
Proof.
pose proof size_sexp_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

Lemma size_sty_open_sty_wrt_sty :
forall A1 A2,
  size_sty A1 <= size_sty (open_sty_wrt_sty A1 A2).
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve size_sty_open_sty_wrt_sty : lngen.

Lemma size_sexp_open_sexp_wrt_sty :
forall ee1 A1,
  size_sexp ee1 <= size_sexp (open_sexp_wrt_sty ee1 A1).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sty : lngen.

Lemma size_sexp_open_sexp_wrt_sexp :
forall ee1 ee2,
  size_sexp ee1 <= size_sexp (open_sexp_wrt_sexp ee1 ee2).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sexp : lngen.

(* begin hide *)

Lemma size_sty_open_sty_wrt_sty_rec_var_mutual :
(forall A1 X1 n1,
  size_sty (open_sty_wrt_sty_rec n1 (sty_var_f X1) A1) = size_sty A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sty_open_sty_wrt_sty_rec_var :
forall A1 X1 n1,
  size_sty (open_sty_wrt_sty_rec n1 (sty_var_f X1) A1) = size_sty A1.
Proof.
pose proof size_sty_open_sty_wrt_sty_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sty_open_sty_wrt_sty_rec_var : lngen.
Hint Rewrite size_sty_open_sty_wrt_sty_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sty_rec_var_mutual :
(forall ee1 X1 n1,
  size_sexp (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1) = size_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sty_rec_var :
forall ee1 X1 n1,
  size_sexp (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1) = size_sexp ee1.
Proof.
pose proof size_sexp_open_sexp_wrt_sty_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sty_rec_var : lngen.
Hint Rewrite size_sexp_open_sexp_wrt_sty_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sexp_rec_var_mutual :
(forall ee1 x1 n1,
  size_sexp (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1) = size_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_sexp_open_sexp_wrt_sexp_rec_var :
forall ee1 x1 n1,
  size_sexp (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1) = size_sexp ee1.
Proof.
pose proof size_sexp_open_sexp_wrt_sexp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sexp_rec_var : lngen.
Hint Rewrite size_sexp_open_sexp_wrt_sexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_sty_open_sty_wrt_sty_var :
forall A1 X1,
  size_sty (open_sty_wrt_sty A1 (sty_var_f X1)) = size_sty A1.
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve size_sty_open_sty_wrt_sty_var : lngen.
Hint Rewrite size_sty_open_sty_wrt_sty_var using solve [auto] : lngen.

Lemma size_sexp_open_sexp_wrt_sty_var :
forall ee1 X1,
  size_sexp (open_sexp_wrt_sty ee1 (sty_var_f X1)) = size_sexp ee1.
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sty_var : lngen.
Hint Rewrite size_sexp_open_sexp_wrt_sty_var using solve [auto] : lngen.

Lemma size_sexp_open_sexp_wrt_sexp_var :
forall ee1 x1,
  size_sexp (open_sexp_wrt_sexp ee1 (sexp_var_f x1)) = size_sexp ee1.
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve size_sexp_open_sexp_wrt_sexp_var : lngen.
Hint Rewrite size_sexp_open_sexp_wrt_sexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_sty_wrt_sty_S_mutual :
(forall n1 A1,
  degree_sty_wrt_sty n1 A1 ->
  degree_sty_wrt_sty (S n1) A1).
Proof.
apply_mutual_ind degree_sty_wrt_sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_sty_wrt_sty_S :
forall n1 A1,
  degree_sty_wrt_sty n1 A1 ->
  degree_sty_wrt_sty (S n1) A1.
Proof.
pose proof degree_sty_wrt_sty_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sty_wrt_sty_S : lngen.

(* begin hide *)

Lemma degree_sexp_wrt_sty_S_mutual :
(forall n1 ee1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty (S n1) ee1).
Proof.
apply_mutual_ind degree_sexp_wrt_sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_sexp_wrt_sty_S :
forall n1 ee1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty (S n1) ee1.
Proof.
pose proof degree_sexp_wrt_sty_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sty_S : lngen.

(* begin hide *)

Lemma degree_sexp_wrt_sexp_S_mutual :
(forall n1 ee1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp (S n1) ee1).
Proof.
apply_mutual_ind degree_sexp_wrt_sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_sexp_wrt_sexp_S :
forall n1 ee1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp (S n1) ee1.
Proof.
pose proof degree_sexp_wrt_sexp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sexp_S : lngen.

Lemma degree_sty_wrt_sty_O :
forall n1 A1,
  degree_sty_wrt_sty O A1 ->
  degree_sty_wrt_sty n1 A1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_sty_wrt_sty_O : lngen.

Lemma degree_sexp_wrt_sty_O :
forall n1 ee1,
  degree_sexp_wrt_sty O ee1 ->
  degree_sexp_wrt_sty n1 ee1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sty_O : lngen.

Lemma degree_sexp_wrt_sexp_O :
forall n1 ee1,
  degree_sexp_wrt_sexp O ee1 ->
  degree_sexp_wrt_sexp n1 ee1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sexp_O : lngen.

(* begin hide *)

Lemma degree_sty_wrt_sty_close_sty_wrt_sty_rec_mutual :
(forall A1 X1 n1,
  degree_sty_wrt_sty n1 A1 ->
  degree_sty_wrt_sty (S n1) (close_sty_wrt_sty_rec n1 X1 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sty_wrt_sty_close_sty_wrt_sty_rec :
forall A1 X1 n1,
  degree_sty_wrt_sty n1 A1 ->
  degree_sty_wrt_sty (S n1) (close_sty_wrt_sty_rec n1 X1 A1).
Proof.
pose proof degree_sty_wrt_sty_close_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sty_wrt_sty_close_sty_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty (S n1) (close_sexp_wrt_sty_rec n1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sty_rec :
forall ee1 X1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty (S n1) (close_sexp_wrt_sty_rec n1 X1 ee1).
Proof.
pose proof degree_sexp_wrt_sty_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sty_close_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1 n2,
  degree_sexp_wrt_sty n2 ee1 ->
  degree_sexp_wrt_sty n2 (close_sexp_wrt_sexp_rec n1 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec :
forall ee1 x1 n1 n2,
  degree_sexp_wrt_sty n2 ee1 ->
  degree_sexp_wrt_sty n2 (close_sexp_wrt_sexp_rec n1 x1 ee1).
Proof.
pose proof degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1 n2,
  degree_sexp_wrt_sexp n2 ee1 ->
  degree_sexp_wrt_sexp n2 (close_sexp_wrt_sty_rec n1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec :
forall ee1 X1 n1 n2,
  degree_sexp_wrt_sexp n2 ee1 ->
  degree_sexp_wrt_sexp n2 (close_sexp_wrt_sty_rec n1 X1 ee1).
Proof.
pose proof degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp (S n1) (close_sexp_wrt_sexp_rec n1 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec :
forall ee1 x1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp (S n1) (close_sexp_wrt_sexp_rec n1 x1 ee1).
Proof.
pose proof degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec : lngen.

(* end hide *)

Lemma degree_sty_wrt_sty_close_sty_wrt_sty :
forall A1 X1,
  degree_sty_wrt_sty 0 A1 ->
  degree_sty_wrt_sty 1 (close_sty_wrt_sty X1 A1).
Proof.
unfold close_sty_wrt_sty; default_simp.
Qed.

Hint Resolve degree_sty_wrt_sty_close_sty_wrt_sty : lngen.

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sty :
forall ee1 X1,
  degree_sexp_wrt_sty 0 ee1 ->
  degree_sexp_wrt_sty 1 (close_sexp_wrt_sty X1 ee1).
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sty_close_sexp_wrt_sty : lngen.

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sexp :
forall ee1 x1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty n1 (close_sexp_wrt_sexp x1 ee1).
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sty_close_sexp_wrt_sexp : lngen.

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sty :
forall ee1 X1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 (close_sexp_wrt_sty X1 ee1).
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sexp_close_sexp_wrt_sty : lngen.

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sexp :
forall ee1 x1,
  degree_sexp_wrt_sexp 0 ee1 ->
  degree_sexp_wrt_sexp 1 (close_sexp_wrt_sexp x1 ee1).
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sexp_close_sexp_wrt_sexp : lngen.

(* begin hide *)

Lemma degree_sty_wrt_sty_close_sty_wrt_sty_rec_inv_mutual :
(forall A1 X1 n1,
  degree_sty_wrt_sty (S n1) (close_sty_wrt_sty_rec n1 X1 A1) ->
  degree_sty_wrt_sty n1 A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sty_wrt_sty_close_sty_wrt_sty_rec_inv :
forall A1 X1 n1,
  degree_sty_wrt_sty (S n1) (close_sty_wrt_sty_rec n1 X1 A1) ->
  degree_sty_wrt_sty n1 A1.
Proof.
pose proof degree_sty_wrt_sty_close_sty_wrt_sty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sty_wrt_sty_close_sty_wrt_sty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sty_rec_inv_mutual :
(forall ee1 X1 n1,
  degree_sexp_wrt_sty (S n1) (close_sexp_wrt_sty_rec n1 X1 ee1) ->
  degree_sexp_wrt_sty n1 ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sty_rec_inv :
forall ee1 X1 n1,
  degree_sexp_wrt_sty (S n1) (close_sexp_wrt_sty_rec n1 X1 ee1) ->
  degree_sexp_wrt_sty n1 ee1.
Proof.
pose proof degree_sexp_wrt_sty_close_sexp_wrt_sty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sty_close_sexp_wrt_sty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec_inv_mutual :
(forall ee1 x1 n1 n2,
  degree_sexp_wrt_sty n2 (close_sexp_wrt_sexp_rec n1 x1 ee1) ->
  degree_sexp_wrt_sty n2 ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec_inv :
forall ee1 x1 n1 n2,
  degree_sexp_wrt_sty n2 (close_sexp_wrt_sexp_rec n1 x1 ee1) ->
  degree_sexp_wrt_sty n2 ee1.
Proof.
pose proof degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sty_close_sexp_wrt_sexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec_inv_mutual :
(forall ee1 X1 n1 n2,
  degree_sexp_wrt_sexp n2 (close_sexp_wrt_sty_rec n1 X1 ee1) ->
  degree_sexp_wrt_sexp n2 ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec_inv :
forall ee1 X1 n1 n2,
  degree_sexp_wrt_sexp n2 (close_sexp_wrt_sty_rec n1 X1 ee1) ->
  degree_sexp_wrt_sexp n2 ee1.
Proof.
pose proof degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sexp_close_sexp_wrt_sty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec_inv_mutual :
(forall ee1 x1 n1,
  degree_sexp_wrt_sexp (S n1) (close_sexp_wrt_sexp_rec n1 x1 ee1) ->
  degree_sexp_wrt_sexp n1 ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec_inv :
forall ee1 x1 n1,
  degree_sexp_wrt_sexp (S n1) (close_sexp_wrt_sexp_rec n1 x1 ee1) ->
  degree_sexp_wrt_sexp n1 ee1.
Proof.
pose proof degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sexp_close_sexp_wrt_sexp_rec_inv : lngen.

(* end hide *)

Lemma degree_sty_wrt_sty_close_sty_wrt_sty_inv :
forall A1 X1,
  degree_sty_wrt_sty 1 (close_sty_wrt_sty X1 A1) ->
  degree_sty_wrt_sty 0 A1.
Proof.
unfold close_sty_wrt_sty; eauto with lngen.
Qed.

Hint Immediate degree_sty_wrt_sty_close_sty_wrt_sty_inv : lngen.

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sty_inv :
forall ee1 X1,
  degree_sexp_wrt_sty 1 (close_sexp_wrt_sty X1 ee1) ->
  degree_sexp_wrt_sty 0 ee1.
Proof.
unfold close_sexp_wrt_sty; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sty_close_sexp_wrt_sty_inv : lngen.

Lemma degree_sexp_wrt_sty_close_sexp_wrt_sexp_inv :
forall ee1 x1 n1,
  degree_sexp_wrt_sty n1 (close_sexp_wrt_sexp x1 ee1) ->
  degree_sexp_wrt_sty n1 ee1.
Proof.
unfold close_sexp_wrt_sexp; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sty_close_sexp_wrt_sexp_inv : lngen.

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sty_inv :
forall ee1 X1 n1,
  degree_sexp_wrt_sexp n1 (close_sexp_wrt_sty X1 ee1) ->
  degree_sexp_wrt_sexp n1 ee1.
Proof.
unfold close_sexp_wrt_sty; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sexp_close_sexp_wrt_sty_inv : lngen.

Lemma degree_sexp_wrt_sexp_close_sexp_wrt_sexp_inv :
forall ee1 x1,
  degree_sexp_wrt_sexp 1 (close_sexp_wrt_sexp x1 ee1) ->
  degree_sexp_wrt_sexp 0 ee1.
Proof.
unfold close_sexp_wrt_sexp; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sexp_close_sexp_wrt_sexp_inv : lngen.

(* begin hide *)

Lemma degree_sty_wrt_sty_open_sty_wrt_sty_rec_mutual :
(forall A1 A2 n1,
  degree_sty_wrt_sty (S n1) A1 ->
  degree_sty_wrt_sty n1 A2 ->
  degree_sty_wrt_sty n1 (open_sty_wrt_sty_rec n1 A2 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sty_wrt_sty_open_sty_wrt_sty_rec :
forall A1 A2 n1,
  degree_sty_wrt_sty (S n1) A1 ->
  degree_sty_wrt_sty n1 A2 ->
  degree_sty_wrt_sty n1 (open_sty_wrt_sty_rec n1 A2 A1).
Proof.
pose proof degree_sty_wrt_sty_open_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sty_wrt_sty_open_sty_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sty_rec_mutual :
(forall ee1 A1 n1,
  degree_sexp_wrt_sty (S n1) ee1 ->
  degree_sty_wrt_sty n1 A1 ->
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sty_rec n1 A1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sty_rec :
forall ee1 A1 n1,
  degree_sexp_wrt_sty (S n1) ee1 ->
  degree_sty_wrt_sty n1 A1 ->
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sty_rec n1 A1 ee1).
Proof.
pose proof degree_sexp_wrt_sty_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sty_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec_mutual :
(forall ee1 ee2 n1 n2,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty n1 ee2 ->
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sexp_rec n2 ee2 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec :
forall ee1 ee2 n1 n2,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty n1 ee2 ->
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sexp_rec n2 ee2 ee1).
Proof.
pose proof degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec_mutual :
(forall ee1 A1 n1 n2,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sty_rec n2 A1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec :
forall ee1 A1 n1 n2,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sty_rec n2 A1 ee1).
Proof.
pose proof degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec_mutual :
(forall ee1 ee2 n1,
  degree_sexp_wrt_sexp (S n1) ee1 ->
  degree_sexp_wrt_sexp n1 ee2 ->
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec :
forall ee1 ee2 n1,
  degree_sexp_wrt_sexp (S n1) ee1 ->
  degree_sexp_wrt_sexp n1 ee2 ->
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sexp_rec n1 ee2 ee1).
Proof.
pose proof degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

Lemma degree_sty_wrt_sty_open_sty_wrt_sty :
forall A1 A2,
  degree_sty_wrt_sty 1 A1 ->
  degree_sty_wrt_sty 0 A2 ->
  degree_sty_wrt_sty 0 (open_sty_wrt_sty A1 A2).
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve degree_sty_wrt_sty_open_sty_wrt_sty : lngen.

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sty :
forall ee1 A1,
  degree_sexp_wrt_sty 1 ee1 ->
  degree_sty_wrt_sty 0 A1 ->
  degree_sexp_wrt_sty 0 (open_sexp_wrt_sty ee1 A1).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sty_open_sexp_wrt_sty : lngen.

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sexp :
forall ee1 ee2 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty n1 ee2 ->
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sexp ee1 ee2).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sty_open_sexp_wrt_sexp : lngen.

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sty :
forall ee1 A1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sty ee1 A1).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sexp_open_sexp_wrt_sty : lngen.

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sexp :
forall ee1 ee2,
  degree_sexp_wrt_sexp 1 ee1 ->
  degree_sexp_wrt_sexp 0 ee2 ->
  degree_sexp_wrt_sexp 0 (open_sexp_wrt_sexp ee1 ee2).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve degree_sexp_wrt_sexp_open_sexp_wrt_sexp : lngen.

(* begin hide *)

Lemma degree_sty_wrt_sty_open_sty_wrt_sty_rec_inv_mutual :
(forall A1 A2 n1,
  degree_sty_wrt_sty n1 (open_sty_wrt_sty_rec n1 A2 A1) ->
  degree_sty_wrt_sty (S n1) A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sty_wrt_sty_open_sty_wrt_sty_rec_inv :
forall A1 A2 n1,
  degree_sty_wrt_sty n1 (open_sty_wrt_sty_rec n1 A2 A1) ->
  degree_sty_wrt_sty (S n1) A1.
Proof.
pose proof degree_sty_wrt_sty_open_sty_wrt_sty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sty_wrt_sty_open_sty_wrt_sty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sty_rec_inv_mutual :
(forall ee1 A1 n1,
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sty_rec n1 A1 ee1) ->
  degree_sexp_wrt_sty (S n1) ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sty_rec_inv :
forall ee1 A1 n1,
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sty_rec n1 A1 ee1) ->
  degree_sexp_wrt_sty (S n1) ee1.
Proof.
pose proof degree_sexp_wrt_sty_open_sexp_wrt_sty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sty_open_sexp_wrt_sty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec_inv_mutual :
(forall ee1 ee2 n1 n2,
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sexp_rec n2 ee2 ee1) ->
  degree_sexp_wrt_sty n1 ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec_inv :
forall ee1 ee2 n1 n2,
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sexp_rec n2 ee2 ee1) ->
  degree_sexp_wrt_sty n1 ee1.
Proof.
pose proof degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sty_open_sexp_wrt_sexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec_inv_mutual :
(forall ee1 A1 n1 n2,
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sty_rec n2 A1 ee1) ->
  degree_sexp_wrt_sexp n1 ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec_inv :
forall ee1 A1 n1 n2,
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sty_rec n2 A1 ee1) ->
  degree_sexp_wrt_sexp n1 ee1.
Proof.
pose proof degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sexp_open_sexp_wrt_sty_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec_inv_mutual :
(forall ee1 ee2 n1,
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sexp_rec n1 ee2 ee1) ->
  degree_sexp_wrt_sexp (S n1) ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec_inv :
forall ee1 ee2 n1,
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sexp_rec n1 ee2 ee1) ->
  degree_sexp_wrt_sexp (S n1) ee1.
Proof.
pose proof degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_sexp_wrt_sexp_open_sexp_wrt_sexp_rec_inv : lngen.

(* end hide *)

Lemma degree_sty_wrt_sty_open_sty_wrt_sty_inv :
forall A1 A2,
  degree_sty_wrt_sty 0 (open_sty_wrt_sty A1 A2) ->
  degree_sty_wrt_sty 1 A1.
Proof.
unfold open_sty_wrt_sty; eauto with lngen.
Qed.

Hint Immediate degree_sty_wrt_sty_open_sty_wrt_sty_inv : lngen.

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sty_inv :
forall ee1 A1,
  degree_sexp_wrt_sty 0 (open_sexp_wrt_sty ee1 A1) ->
  degree_sexp_wrt_sty 1 ee1.
Proof.
unfold open_sexp_wrt_sty; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sty_open_sexp_wrt_sty_inv : lngen.

Lemma degree_sexp_wrt_sty_open_sexp_wrt_sexp_inv :
forall ee1 ee2 n1,
  degree_sexp_wrt_sty n1 (open_sexp_wrt_sexp ee1 ee2) ->
  degree_sexp_wrt_sty n1 ee1.
Proof.
unfold open_sexp_wrt_sexp; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sty_open_sexp_wrt_sexp_inv : lngen.

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sty_inv :
forall ee1 A1 n1,
  degree_sexp_wrt_sexp n1 (open_sexp_wrt_sty ee1 A1) ->
  degree_sexp_wrt_sexp n1 ee1.
Proof.
unfold open_sexp_wrt_sty; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sexp_open_sexp_wrt_sty_inv : lngen.

Lemma degree_sexp_wrt_sexp_open_sexp_wrt_sexp_inv :
forall ee1 ee2,
  degree_sexp_wrt_sexp 0 (open_sexp_wrt_sexp ee1 ee2) ->
  degree_sexp_wrt_sexp 1 ee1.
Proof.
unfold open_sexp_wrt_sexp; eauto with lngen.
Qed.

Hint Immediate degree_sexp_wrt_sexp_open_sexp_wrt_sexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_sty_wrt_sty_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_sty_wrt_sty_rec n1 X1 A1 = close_sty_wrt_sty_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind sty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sty_wrt_sty_rec_inj :
forall A1 A2 X1 n1,
  close_sty_wrt_sty_rec n1 X1 A1 = close_sty_wrt_sty_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_sty_wrt_sty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_sty_wrt_sty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sty_rec_inj_mutual :
(forall ee1 ee2 X1 n1,
  close_sexp_wrt_sty_rec n1 X1 ee1 = close_sexp_wrt_sty_rec n1 X1 ee2 ->
  ee1 = ee2).
Proof.
apply_mutual_ind sexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sty_rec_inj :
forall ee1 ee2 X1 n1,
  close_sexp_wrt_sty_rec n1 X1 ee1 = close_sexp_wrt_sty_rec n1 X1 ee2 ->
  ee1 = ee2.
Proof.
pose proof close_sexp_wrt_sty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_sexp_wrt_sty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sexp_rec_inj_mutual :
(forall ee1 ee2 x1 n1,
  close_sexp_wrt_sexp_rec n1 x1 ee1 = close_sexp_wrt_sexp_rec n1 x1 ee2 ->
  ee1 = ee2).
Proof.
apply_mutual_ind sexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sexp_rec_inj :
forall ee1 ee2 x1 n1,
  close_sexp_wrt_sexp_rec n1 x1 ee1 = close_sexp_wrt_sexp_rec n1 x1 ee2 ->
  ee1 = ee2.
Proof.
pose proof close_sexp_wrt_sexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_sexp_wrt_sexp_rec_inj : lngen.

(* end hide *)

Lemma close_sty_wrt_sty_inj :
forall A1 A2 X1,
  close_sty_wrt_sty X1 A1 = close_sty_wrt_sty X1 A2 ->
  A1 = A2.
Proof.
unfold close_sty_wrt_sty; eauto with lngen.
Qed.

Hint Immediate close_sty_wrt_sty_inj : lngen.

Lemma close_sexp_wrt_sty_inj :
forall ee1 ee2 X1,
  close_sexp_wrt_sty X1 ee1 = close_sexp_wrt_sty X1 ee2 ->
  ee1 = ee2.
Proof.
unfold close_sexp_wrt_sty; eauto with lngen.
Qed.

Hint Immediate close_sexp_wrt_sty_inj : lngen.

Lemma close_sexp_wrt_sexp_inj :
forall ee1 ee2 x1,
  close_sexp_wrt_sexp x1 ee1 = close_sexp_wrt_sexp x1 ee2 ->
  ee1 = ee2.
Proof.
unfold close_sexp_wrt_sexp; eauto with lngen.
Qed.

Hint Immediate close_sexp_wrt_sexp_inj : lngen.

(* begin hide *)

Lemma close_sty_wrt_sty_rec_open_sty_wrt_sty_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` fv_sty_in_sty A1 ->
  close_sty_wrt_sty_rec n1 X1 (open_sty_wrt_sty_rec n1 (sty_var_f X1) A1) = A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sty_wrt_sty_rec_open_sty_wrt_sty_rec :
forall A1 X1 n1,
  X1 `notin` fv_sty_in_sty A1 ->
  close_sty_wrt_sty_rec n1 X1 (open_sty_wrt_sty_rec n1 (sty_var_f X1) A1) = A1.
Proof.
pose proof close_sty_wrt_sty_rec_open_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_sty_wrt_sty_rec_open_sty_wrt_sty_rec : lngen.
Hint Rewrite close_sty_wrt_sty_rec_open_sty_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  close_sexp_wrt_sty_rec n1 X1 (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1) = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec :
forall ee1 X1 n1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  close_sexp_wrt_sty_rec n1 X1 (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1) = ee1.
Proof.
pose proof close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec : lngen.
Hint Rewrite close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  close_sexp_wrt_sexp_rec n1 x1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1) = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec :
forall ee1 x1 n1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  close_sexp_wrt_sexp_rec n1 x1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1) = ee1.
Proof.
pose proof close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec : lngen.
Hint Rewrite close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_sty_wrt_sty_open_sty_wrt_sty :
forall A1 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  close_sty_wrt_sty X1 (open_sty_wrt_sty A1 (sty_var_f X1)) = A1.
Proof.
unfold close_sty_wrt_sty; unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve close_sty_wrt_sty_open_sty_wrt_sty : lngen.
Hint Rewrite close_sty_wrt_sty_open_sty_wrt_sty using solve [auto] : lngen.

Lemma close_sexp_wrt_sty_open_sexp_wrt_sty :
forall ee1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  close_sexp_wrt_sty X1 (open_sexp_wrt_sty ee1 (sty_var_f X1)) = ee1.
Proof.
unfold close_sexp_wrt_sty; unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve close_sexp_wrt_sty_open_sexp_wrt_sty : lngen.
Hint Rewrite close_sexp_wrt_sty_open_sexp_wrt_sty using solve [auto] : lngen.

Lemma close_sexp_wrt_sexp_open_sexp_wrt_sexp :
forall ee1 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  close_sexp_wrt_sexp x1 (open_sexp_wrt_sexp ee1 (sexp_var_f x1)) = ee1.
Proof.
unfold close_sexp_wrt_sexp; unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve close_sexp_wrt_sexp_open_sexp_wrt_sexp : lngen.
Hint Rewrite close_sexp_wrt_sexp_open_sexp_wrt_sexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_sty_wrt_sty_rec_close_sty_wrt_sty_rec_mutual :
(forall A1 X1 n1,
  open_sty_wrt_sty_rec n1 (sty_var_f X1) (close_sty_wrt_sty_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sty_wrt_sty_rec_close_sty_wrt_sty_rec :
forall A1 X1 n1,
  open_sty_wrt_sty_rec n1 (sty_var_f X1) (close_sty_wrt_sty_rec n1 X1 A1) = A1.
Proof.
pose proof open_sty_wrt_sty_rec_close_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_sty_wrt_sty_rec_close_sty_wrt_sty_rec : lngen.
Hint Rewrite open_sty_wrt_sty_rec_close_sty_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sty_rec_close_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1,
  open_sexp_wrt_sty_rec n1 (sty_var_f X1) (close_sexp_wrt_sty_rec n1 X1 ee1) = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sty_rec_close_sexp_wrt_sty_rec :
forall ee1 X1 n1,
  open_sexp_wrt_sty_rec n1 (sty_var_f X1) (close_sexp_wrt_sty_rec n1 X1 ee1) = ee1.
Proof.
pose proof open_sexp_wrt_sty_rec_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_sexp_wrt_sty_rec_close_sexp_wrt_sty_rec : lngen.
Hint Rewrite open_sexp_wrt_sty_rec_close_sexp_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sexp_rec_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1,
  open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) (close_sexp_wrt_sexp_rec n1 x1 ee1) = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sexp_rec_close_sexp_wrt_sexp_rec :
forall ee1 x1 n1,
  open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) (close_sexp_wrt_sexp_rec n1 x1 ee1) = ee1.
Proof.
pose proof open_sexp_wrt_sexp_rec_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_sexp_wrt_sexp_rec_close_sexp_wrt_sexp_rec : lngen.
Hint Rewrite open_sexp_wrt_sexp_rec_close_sexp_wrt_sexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_sty_wrt_sty_close_sty_wrt_sty :
forall A1 X1,
  open_sty_wrt_sty (close_sty_wrt_sty X1 A1) (sty_var_f X1) = A1.
Proof.
unfold close_sty_wrt_sty; unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve open_sty_wrt_sty_close_sty_wrt_sty : lngen.
Hint Rewrite open_sty_wrt_sty_close_sty_wrt_sty using solve [auto] : lngen.

Lemma open_sexp_wrt_sty_close_sexp_wrt_sty :
forall ee1 X1,
  open_sexp_wrt_sty (close_sexp_wrt_sty X1 ee1) (sty_var_f X1) = ee1.
Proof.
unfold close_sexp_wrt_sty; unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve open_sexp_wrt_sty_close_sexp_wrt_sty : lngen.
Hint Rewrite open_sexp_wrt_sty_close_sexp_wrt_sty using solve [auto] : lngen.

Lemma open_sexp_wrt_sexp_close_sexp_wrt_sexp :
forall ee1 x1,
  open_sexp_wrt_sexp (close_sexp_wrt_sexp x1 ee1) (sexp_var_f x1) = ee1.
Proof.
unfold close_sexp_wrt_sexp; unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve open_sexp_wrt_sexp_close_sexp_wrt_sexp : lngen.
Hint Rewrite open_sexp_wrt_sexp_close_sexp_wrt_sexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_sty_wrt_sty_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` fv_sty_in_sty A2 ->
  X1 `notin` fv_sty_in_sty A1 ->
  open_sty_wrt_sty_rec n1 (sty_var_f X1) A2 = open_sty_wrt_sty_rec n1 (sty_var_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind sty_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sty_wrt_sty_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` fv_sty_in_sty A2 ->
  X1 `notin` fv_sty_in_sty A1 ->
  open_sty_wrt_sty_rec n1 (sty_var_f X1) A2 = open_sty_wrt_sty_rec n1 (sty_var_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_sty_wrt_sty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_sty_wrt_sty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sty_rec_inj_mutual :
(forall ee2 ee1 X1 n1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee2 = open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1 ->
  ee2 = ee1).
Proof.
apply_mutual_ind sexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sty_rec_inj :
forall ee2 ee1 X1 n1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee2 = open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1 ->
  ee2 = ee1.
Proof.
pose proof open_sexp_wrt_sty_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_sexp_wrt_sty_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sexp_rec_inj_mutual :
(forall ee2 ee1 x1 n1,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee2 = open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1 ->
  ee2 = ee1).
Proof.
apply_mutual_ind sexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sexp_rec_inj :
forall ee2 ee1 x1 n1,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee2 = open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1 ->
  ee2 = ee1.
Proof.
pose proof open_sexp_wrt_sexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_sexp_wrt_sexp_rec_inj : lngen.

(* end hide *)

Lemma open_sty_wrt_sty_inj :
forall A2 A1 X1,
  X1 `notin` fv_sty_in_sty A2 ->
  X1 `notin` fv_sty_in_sty A1 ->
  open_sty_wrt_sty A2 (sty_var_f X1) = open_sty_wrt_sty A1 (sty_var_f X1) ->
  A2 = A1.
Proof.
unfold open_sty_wrt_sty; eauto with lngen.
Qed.

Hint Immediate open_sty_wrt_sty_inj : lngen.

Lemma open_sexp_wrt_sty_inj :
forall ee2 ee1 X1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  open_sexp_wrt_sty ee2 (sty_var_f X1) = open_sexp_wrt_sty ee1 (sty_var_f X1) ->
  ee2 = ee1.
Proof.
unfold open_sexp_wrt_sty; eauto with lngen.
Qed.

Hint Immediate open_sexp_wrt_sty_inj : lngen.

Lemma open_sexp_wrt_sexp_inj :
forall ee2 ee1 x1,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  open_sexp_wrt_sexp ee2 (sexp_var_f x1) = open_sexp_wrt_sexp ee1 (sexp_var_f x1) ->
  ee2 = ee1.
Proof.
unfold open_sexp_wrt_sexp; eauto with lngen.
Qed.

Hint Immediate open_sexp_wrt_sexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_sty_wrt_sty_of_lc_sty_mutual :
(forall A1,
  lc_sty A1 ->
  degree_sty_wrt_sty 0 A1).
Proof.
apply_mutual_ind lc_sty_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_sty_wrt_sty_of_lc_sty :
forall A1,
  lc_sty A1 ->
  degree_sty_wrt_sty 0 A1.
Proof.
pose proof degree_sty_wrt_sty_of_lc_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sty_wrt_sty_of_lc_sty : lngen.

(* begin hide *)

Lemma degree_sexp_wrt_sty_of_lc_sexp_mutual :
(forall ee1,
  lc_sexp ee1 ->
  degree_sexp_wrt_sty 0 ee1).
Proof.
apply_mutual_ind lc_sexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_sexp_wrt_sty_of_lc_sexp :
forall ee1,
  lc_sexp ee1 ->
  degree_sexp_wrt_sty 0 ee1.
Proof.
pose proof degree_sexp_wrt_sty_of_lc_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sty_of_lc_sexp : lngen.

(* begin hide *)

Lemma degree_sexp_wrt_sexp_of_lc_sexp_mutual :
(forall ee1,
  lc_sexp ee1 ->
  degree_sexp_wrt_sexp 0 ee1).
Proof.
apply_mutual_ind lc_sexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_sexp_wrt_sexp_of_lc_sexp :
forall ee1,
  lc_sexp ee1 ->
  degree_sexp_wrt_sexp 0 ee1.
Proof.
pose proof degree_sexp_wrt_sexp_of_lc_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_sexp_wrt_sexp_of_lc_sexp : lngen.

(* begin hide *)

Lemma lc_sty_of_degree_size_mutual :
forall i1,
(forall A1,
  size_sty A1 = i1 ->
  degree_sty_wrt_sty 0 A1 ->
  lc_sty A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind sty_mutind;
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

Lemma lc_sty_of_degree :
forall A1,
  degree_sty_wrt_sty 0 A1 ->
  lc_sty A1.
Proof.
intros A1; intros;
pose proof (lc_sty_of_degree_size_mutual (size_sty A1));
intuition eauto.
Qed.

Hint Resolve lc_sty_of_degree : lngen.

(* begin hide *)

Lemma lc_sexp_of_degree_size_mutual :
forall i1,
(forall ee1,
  size_sexp ee1 = i1 ->
  degree_sexp_wrt_sty 0 ee1 ->
  degree_sexp_wrt_sexp 0 ee1 ->
  lc_sexp ee1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind sexp_mutind;
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

Lemma lc_sexp_of_degree :
forall ee1,
  degree_sexp_wrt_sty 0 ee1 ->
  degree_sexp_wrt_sexp 0 ee1 ->
  lc_sexp ee1.
Proof.
intros ee1; intros;
pose proof (lc_sexp_of_degree_size_mutual (size_sexp ee1));
intuition eauto.
Qed.

Hint Resolve lc_sexp_of_degree : lngen.

Ltac sty_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_sty_wrt_sty_of_lc_sty in J1; clear H
          end).

Ltac sexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_sexp_wrt_sty_of_lc_sexp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_sexp_wrt_sexp_of_lc_sexp in J2; clear H
          end).

Lemma lc_sty_all_exists :
forall X1 A1 B1,
  lc_sty A1 ->
  lc_sty (open_sty_wrt_sty B1 (sty_var_f X1)) ->
  lc_sty (sty_all A1 B1).
Proof.
intros; sty_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_sexp_abs_exists :
forall x1 ee1,
  lc_sexp (open_sexp_wrt_sexp ee1 (sexp_var_f x1)) ->
  lc_sexp (sexp_abs ee1).
Proof.
intros; sexp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_sexp_tabs_exists :
forall X1 A1 ee1,
  lc_sty A1 ->
  lc_sexp (open_sexp_wrt_sty ee1 (sty_var_f X1)) ->
  lc_sexp (sexp_tabs A1 ee1).
Proof.
intros; sexp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_sty (sty_all _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_sty_all_exists X1).

Hint Extern 1 (lc_sexp (sexp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_sexp_abs_exists x1).

Hint Extern 1 (lc_sexp (sexp_tabs _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_sexp_tabs_exists X1).

Lemma lc_body_sty_wrt_sty :
forall A1 A2,
  body_sty_wrt_sty A1 ->
  lc_sty A2 ->
  lc_sty (open_sty_wrt_sty A1 A2).
Proof.
unfold body_sty_wrt_sty;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
sty_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_sty_wrt_sty : lngen.

Lemma lc_body_sexp_wrt_sty :
forall ee1 A1,
  body_sexp_wrt_sty ee1 ->
  lc_sty A1 ->
  lc_sexp (open_sexp_wrt_sty ee1 A1).
Proof.
unfold body_sexp_wrt_sty;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
sexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_sexp_wrt_sty : lngen.

Lemma lc_body_sexp_wrt_sexp :
forall ee1 ee2,
  body_sexp_wrt_sexp ee1 ->
  lc_sexp ee2 ->
  lc_sexp (open_sexp_wrt_sexp ee1 ee2).
Proof.
unfold body_sexp_wrt_sexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
sexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_sexp_wrt_sexp : lngen.

Lemma lc_body_sty_all_2 :
forall A1 B1,
  lc_sty (sty_all A1 B1) ->
  body_sty_wrt_sty B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_sty_all_2 : lngen.

Lemma lc_body_sexp_abs_1 :
forall ee1,
  lc_sexp (sexp_abs ee1) ->
  body_sexp_wrt_sexp ee1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_sexp_abs_1 : lngen.

Lemma lc_body_sexp_tabs_2 :
forall A1 ee1,
  lc_sexp (sexp_tabs A1 ee1) ->
  body_sexp_wrt_sty ee1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_sexp_tabs_2 : lngen.

(* begin hide *)

Lemma lc_sty_unique_mutual :
(forall A1 (proof2 proof3 : lc_sty A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_sty_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_sty_unique :
forall A1 (proof2 proof3 : lc_sty A1), proof2 = proof3.
Proof.
pose proof lc_sty_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_sty_unique : lngen.

(* begin hide *)

Lemma lc_sexp_unique_mutual :
(forall ee1 (proof2 proof3 : lc_sexp ee1), proof2 = proof3).
Proof.
apply_mutual_ind lc_sexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_sexp_unique :
forall ee1 (proof2 proof3 : lc_sexp ee1), proof2 = proof3.
Proof.
pose proof lc_sexp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_sexp_unique : lngen.

(* begin hide *)

Lemma lc_sty_of_lc_set_sty_mutual :
(forall A1, lc_set_sty A1 -> lc_sty A1).
Proof.
apply_mutual_ind lc_set_sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_sty_of_lc_set_sty :
forall A1, lc_set_sty A1 -> lc_sty A1.
Proof.
pose proof lc_sty_of_lc_set_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_sty_of_lc_set_sty : lngen.

(* begin hide *)

Lemma lc_sexp_of_lc_set_sexp_mutual :
(forall ee1, lc_set_sexp ee1 -> lc_sexp ee1).
Proof.
apply_mutual_ind lc_set_sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_sexp_of_lc_set_sexp :
forall ee1, lc_set_sexp ee1 -> lc_sexp ee1.
Proof.
pose proof lc_sexp_of_lc_set_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_sexp_of_lc_set_sexp : lngen.

(* begin hide *)

Lemma lc_set_sty_of_lc_sty_size_mutual :
forall i1,
(forall A1,
  size_sty A1 = i1 ->
  lc_sty A1 ->
  lc_set_sty A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind sty_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_sty_of_lc_sty];
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

Lemma lc_set_sty_of_lc_sty :
forall A1,
  lc_sty A1 ->
  lc_set_sty A1.
Proof.
intros A1; intros;
pose proof (lc_set_sty_of_lc_sty_size_mutual (size_sty A1));
intuition eauto.
Qed.

Hint Resolve lc_set_sty_of_lc_sty : lngen.

(* begin hide *)

Lemma lc_set_sexp_of_lc_sexp_size_mutual :
forall i1,
(forall ee1,
  size_sexp ee1 = i1 ->
  lc_sexp ee1 ->
  lc_set_sexp ee1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind sexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_sty_of_lc_sty
 | apply lc_set_sexp_of_lc_sexp];
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

Lemma lc_set_sexp_of_lc_sexp :
forall ee1,
  lc_sexp ee1 ->
  lc_set_sexp ee1.
Proof.
intros ee1; intros;
pose proof (lc_set_sexp_of_lc_sexp_size_mutual (size_sexp ee1));
intuition eauto.
Qed.

Hint Resolve lc_set_sexp_of_lc_sexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_sty_wrt_sty_rec_degree_sty_wrt_sty_mutual :
(forall A1 X1 n1,
  degree_sty_wrt_sty n1 A1 ->
  X1 `notin` fv_sty_in_sty A1 ->
  close_sty_wrt_sty_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sty_wrt_sty_rec_degree_sty_wrt_sty :
forall A1 X1 n1,
  degree_sty_wrt_sty n1 A1 ->
  X1 `notin` fv_sty_in_sty A1 ->
  close_sty_wrt_sty_rec n1 X1 A1 = A1.
Proof.
pose proof close_sty_wrt_sty_rec_degree_sty_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve close_sty_wrt_sty_rec_degree_sty_wrt_sty : lngen.
Hint Rewrite close_sty_wrt_sty_rec_degree_sty_wrt_sty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sty_rec_degree_sexp_wrt_sty_mutual :
(forall ee1 X1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  close_sexp_wrt_sty_rec n1 X1 ee1 = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sty_rec_degree_sexp_wrt_sty :
forall ee1 X1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  close_sexp_wrt_sty_rec n1 X1 ee1 = ee1.
Proof.
pose proof close_sexp_wrt_sty_rec_degree_sexp_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve close_sexp_wrt_sty_rec_degree_sexp_wrt_sty : lngen.
Hint Rewrite close_sexp_wrt_sty_rec_degree_sexp_wrt_sty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp_mutual :
(forall ee1 x1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  close_sexp_wrt_sexp_rec n1 x1 ee1 = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp :
forall ee1 x1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  close_sexp_wrt_sexp_rec n1 x1 ee1 = ee1.
Proof.
pose proof close_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp : lngen.
Hint Rewrite close_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp using solve [auto] : lngen.

(* end hide *)

Lemma close_sty_wrt_sty_lc_sty :
forall A1 X1,
  lc_sty A1 ->
  X1 `notin` fv_sty_in_sty A1 ->
  close_sty_wrt_sty X1 A1 = A1.
Proof.
unfold close_sty_wrt_sty; default_simp.
Qed.

Hint Resolve close_sty_wrt_sty_lc_sty : lngen.
Hint Rewrite close_sty_wrt_sty_lc_sty using solve [auto] : lngen.

Lemma close_sexp_wrt_sty_lc_sexp :
forall ee1 X1,
  lc_sexp ee1 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  close_sexp_wrt_sty X1 ee1 = ee1.
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve close_sexp_wrt_sty_lc_sexp : lngen.
Hint Rewrite close_sexp_wrt_sty_lc_sexp using solve [auto] : lngen.

Lemma close_sexp_wrt_sexp_lc_sexp :
forall ee1 x1,
  lc_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  close_sexp_wrt_sexp x1 ee1 = ee1.
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve close_sexp_wrt_sexp_lc_sexp : lngen.
Hint Rewrite close_sexp_wrt_sexp_lc_sexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_sty_wrt_sty_rec_degree_sty_wrt_sty_mutual :
(forall A2 A1 n1,
  degree_sty_wrt_sty n1 A2 ->
  open_sty_wrt_sty_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sty_wrt_sty_rec_degree_sty_wrt_sty :
forall A2 A1 n1,
  degree_sty_wrt_sty n1 A2 ->
  open_sty_wrt_sty_rec n1 A1 A2 = A2.
Proof.
pose proof open_sty_wrt_sty_rec_degree_sty_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve open_sty_wrt_sty_rec_degree_sty_wrt_sty : lngen.
Hint Rewrite open_sty_wrt_sty_rec_degree_sty_wrt_sty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sty_rec_degree_sexp_wrt_sty_mutual :
(forall ee1 A1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  open_sexp_wrt_sty_rec n1 A1 ee1 = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sty_rec_degree_sexp_wrt_sty :
forall ee1 A1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  open_sexp_wrt_sty_rec n1 A1 ee1 = ee1.
Proof.
pose proof open_sexp_wrt_sty_rec_degree_sexp_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve open_sexp_wrt_sty_rec_degree_sexp_wrt_sty : lngen.
Hint Rewrite open_sexp_wrt_sty_rec_degree_sexp_wrt_sty using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp_mutual :
(forall ee2 ee1 n1,
  degree_sexp_wrt_sexp n1 ee2 ->
  open_sexp_wrt_sexp_rec n1 ee1 ee2 = ee2).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp :
forall ee2 ee1 n1,
  degree_sexp_wrt_sexp n1 ee2 ->
  open_sexp_wrt_sexp_rec n1 ee1 ee2 = ee2.
Proof.
pose proof open_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp : lngen.
Hint Rewrite open_sexp_wrt_sexp_rec_degree_sexp_wrt_sexp using solve [auto] : lngen.

(* end hide *)

Lemma open_sty_wrt_sty_lc_sty :
forall A2 A1,
  lc_sty A2 ->
  open_sty_wrt_sty A2 A1 = A2.
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve open_sty_wrt_sty_lc_sty : lngen.
Hint Rewrite open_sty_wrt_sty_lc_sty using solve [auto] : lngen.

Lemma open_sexp_wrt_sty_lc_sexp :
forall ee1 A1,
  lc_sexp ee1 ->
  open_sexp_wrt_sty ee1 A1 = ee1.
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve open_sexp_wrt_sty_lc_sexp : lngen.
Hint Rewrite open_sexp_wrt_sty_lc_sexp using solve [auto] : lngen.

Lemma open_sexp_wrt_sexp_lc_sexp :
forall ee2 ee1,
  lc_sexp ee2 ->
  open_sexp_wrt_sexp ee2 ee1 = ee2.
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve open_sexp_wrt_sexp_lc_sexp : lngen.
Hint Rewrite open_sexp_wrt_sexp_lc_sexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_sty_in_sty_close_sty_wrt_sty_rec_mutual :
(forall A1 X1 n1,
  fv_sty_in_sty (close_sty_wrt_sty_rec n1 X1 A1) [=] remove X1 (fv_sty_in_sty A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sty_close_sty_wrt_sty_rec :
forall A1 X1 n1,
  fv_sty_in_sty (close_sty_wrt_sty_rec n1 X1 A1) [=] remove X1 (fv_sty_in_sty A1).
Proof.
pose proof fv_sty_in_sty_close_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_close_sty_wrt_sty_rec : lngen.
Hint Rewrite fv_sty_in_sty_close_sty_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_close_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1,
  fv_sty_in_sexp (close_sexp_wrt_sty_rec n1 X1 ee1) [=] remove X1 (fv_sty_in_sexp ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_close_sexp_wrt_sty_rec :
forall ee1 X1 n1,
  fv_sty_in_sexp (close_sexp_wrt_sty_rec n1 X1 ee1) [=] remove X1 (fv_sty_in_sexp ee1).
Proof.
pose proof fv_sty_in_sexp_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_close_sexp_wrt_sty_rec : lngen.
Hint Rewrite fv_sty_in_sexp_close_sexp_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1,
  fv_sty_in_sexp (close_sexp_wrt_sexp_rec n1 x1 ee1) [=] fv_sty_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_close_sexp_wrt_sexp_rec :
forall ee1 x1 n1,
  fv_sty_in_sexp (close_sexp_wrt_sexp_rec n1 x1 ee1) [=] fv_sty_in_sexp ee1.
Proof.
pose proof fv_sty_in_sexp_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_close_sexp_wrt_sexp_rec : lngen.
Hint Rewrite fv_sty_in_sexp_close_sexp_wrt_sexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_close_sexp_wrt_sty_rec_mutual :
(forall ee1 X1 n1,
  fv_sexp_in_sexp (close_sexp_wrt_sty_rec n1 X1 ee1) [=] fv_sexp_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_close_sexp_wrt_sty_rec :
forall ee1 X1 n1,
  fv_sexp_in_sexp (close_sexp_wrt_sty_rec n1 X1 ee1) [=] fv_sexp_in_sexp ee1.
Proof.
pose proof fv_sexp_in_sexp_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_close_sexp_wrt_sty_rec : lngen.
Hint Rewrite fv_sexp_in_sexp_close_sexp_wrt_sty_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 x1 n1,
  fv_sexp_in_sexp (close_sexp_wrt_sexp_rec n1 x1 ee1) [=] remove x1 (fv_sexp_in_sexp ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_close_sexp_wrt_sexp_rec :
forall ee1 x1 n1,
  fv_sexp_in_sexp (close_sexp_wrt_sexp_rec n1 x1 ee1) [=] remove x1 (fv_sexp_in_sexp ee1).
Proof.
pose proof fv_sexp_in_sexp_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_close_sexp_wrt_sexp_rec : lngen.
Hint Rewrite fv_sexp_in_sexp_close_sexp_wrt_sexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_sty_in_sty_close_sty_wrt_sty :
forall A1 X1,
  fv_sty_in_sty (close_sty_wrt_sty X1 A1) [=] remove X1 (fv_sty_in_sty A1).
Proof.
unfold close_sty_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sty_in_sty_close_sty_wrt_sty : lngen.
Hint Rewrite fv_sty_in_sty_close_sty_wrt_sty using solve [auto] : lngen.

Lemma fv_sty_in_sexp_close_sexp_wrt_sty :
forall ee1 X1,
  fv_sty_in_sexp (close_sexp_wrt_sty X1 ee1) [=] remove X1 (fv_sty_in_sexp ee1).
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sty_in_sexp_close_sexp_wrt_sty : lngen.
Hint Rewrite fv_sty_in_sexp_close_sexp_wrt_sty using solve [auto] : lngen.

Lemma fv_sty_in_sexp_close_sexp_wrt_sexp :
forall ee1 x1,
  fv_sty_in_sexp (close_sexp_wrt_sexp x1 ee1) [=] fv_sty_in_sexp ee1.
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve fv_sty_in_sexp_close_sexp_wrt_sexp : lngen.
Hint Rewrite fv_sty_in_sexp_close_sexp_wrt_sexp using solve [auto] : lngen.

Lemma fv_sexp_in_sexp_close_sexp_wrt_sty :
forall ee1 X1,
  fv_sexp_in_sexp (close_sexp_wrt_sty X1 ee1) [=] fv_sexp_in_sexp ee1.
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sexp_in_sexp_close_sexp_wrt_sty : lngen.
Hint Rewrite fv_sexp_in_sexp_close_sexp_wrt_sty using solve [auto] : lngen.

Lemma fv_sexp_in_sexp_close_sexp_wrt_sexp :
forall ee1 x1,
  fv_sexp_in_sexp (close_sexp_wrt_sexp x1 ee1) [=] remove x1 (fv_sexp_in_sexp ee1).
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve fv_sexp_in_sexp_close_sexp_wrt_sexp : lngen.
Hint Rewrite fv_sexp_in_sexp_close_sexp_wrt_sexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_sty_in_sty_open_sty_wrt_sty_rec_lower_mutual :
(forall A1 A2 n1,
  fv_sty_in_sty A1 [<=] fv_sty_in_sty (open_sty_wrt_sty_rec n1 A2 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sty_open_sty_wrt_sty_rec_lower :
forall A1 A2 n1,
  fv_sty_in_sty A1 [<=] fv_sty_in_sty (open_sty_wrt_sty_rec n1 A2 A1).
Proof.
pose proof fv_sty_in_sty_open_sty_wrt_sty_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_open_sty_wrt_sty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sty_rec_lower_mutual :
(forall ee1 A1 n1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sty_rec_lower :
forall ee1 A1 n1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1).
Proof.
pose proof fv_sty_in_sexp_open_sexp_wrt_sty_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sexp_rec_lower_mutual :
(forall ee1 ee2 n1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sexp_rec_lower :
forall ee1 ee2 n1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1).
Proof.
pose proof fv_sty_in_sexp_open_sexp_wrt_sexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sty_rec_lower_mutual :
(forall ee1 A1 n1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sty_rec_lower :
forall ee1 A1 n1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1).
Proof.
pose proof fv_sexp_in_sexp_open_sexp_wrt_sty_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sty_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_lower_mutual :
(forall ee1 ee2 n1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_lower :
forall ee1 ee2 n1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1).
Proof.
pose proof fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_lower : lngen.

(* end hide *)

Lemma fv_sty_in_sty_open_sty_wrt_sty_lower :
forall A1 A2,
  fv_sty_in_sty A1 [<=] fv_sty_in_sty (open_sty_wrt_sty A1 A2).
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sty_in_sty_open_sty_wrt_sty_lower : lngen.

Lemma fv_sty_in_sexp_open_sexp_wrt_sty_lower :
forall ee1 A1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (open_sexp_wrt_sty ee1 A1).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sty_lower : lngen.

Lemma fv_sty_in_sexp_open_sexp_wrt_sexp_lower :
forall ee1 ee2,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (open_sexp_wrt_sexp ee1 ee2).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sexp_lower : lngen.

Lemma fv_sexp_in_sexp_open_sexp_wrt_sty_lower :
forall ee1 A1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (open_sexp_wrt_sty ee1 A1).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sty_lower : lngen.

Lemma fv_sexp_in_sexp_open_sexp_wrt_sexp_lower :
forall ee1 ee2,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (open_sexp_wrt_sexp ee1 ee2).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sexp_lower : lngen.

(* begin hide *)

Lemma fv_sty_in_sty_open_sty_wrt_sty_rec_upper_mutual :
(forall A1 A2 n1,
  fv_sty_in_sty (open_sty_wrt_sty_rec n1 A2 A1) [<=] fv_sty_in_sty A2 `union` fv_sty_in_sty A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sty_open_sty_wrt_sty_rec_upper :
forall A1 A2 n1,
  fv_sty_in_sty (open_sty_wrt_sty_rec n1 A2 A1) [<=] fv_sty_in_sty A2 `union` fv_sty_in_sty A1.
Proof.
pose proof fv_sty_in_sty_open_sty_wrt_sty_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_open_sty_wrt_sty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sty_rec_upper_mutual :
(forall ee1 A1 n1,
  fv_sty_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1) [<=] fv_sty_in_sty A1 `union` fv_sty_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sty_rec_upper :
forall ee1 A1 n1,
  fv_sty_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1) [<=] fv_sty_in_sty A1 `union` fv_sty_in_sexp ee1.
Proof.
pose proof fv_sty_in_sexp_open_sexp_wrt_sty_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sexp_rec_upper_mutual :
(forall ee1 ee2 n1,
  fv_sty_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1) [<=] fv_sty_in_sexp ee2 `union` fv_sty_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sty_in_sexp_open_sexp_wrt_sexp_rec_upper :
forall ee1 ee2 n1,
  fv_sty_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1) [<=] fv_sty_in_sexp ee2 `union` fv_sty_in_sexp ee1.
Proof.
pose proof fv_sty_in_sexp_open_sexp_wrt_sexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sty_rec_upper_mutual :
(forall ee1 A1 n1,
  fv_sexp_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1) [<=] fv_sexp_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sty_rec_upper :
forall ee1 A1 n1,
  fv_sexp_in_sexp (open_sexp_wrt_sty_rec n1 A1 ee1) [<=] fv_sexp_in_sexp ee1.
Proof.
pose proof fv_sexp_in_sexp_open_sexp_wrt_sty_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sty_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_upper_mutual :
(forall ee1 ee2 n1,
  fv_sexp_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1) [<=] fv_sexp_in_sexp ee2 `union` fv_sexp_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_upper :
forall ee1 ee2 n1,
  fv_sexp_in_sexp (open_sexp_wrt_sexp_rec n1 ee2 ee1) [<=] fv_sexp_in_sexp ee2 `union` fv_sexp_in_sexp ee1.
Proof.
pose proof fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sexp_rec_upper : lngen.

(* end hide *)

Lemma fv_sty_in_sty_open_sty_wrt_sty_upper :
forall A1 A2,
  fv_sty_in_sty (open_sty_wrt_sty A1 A2) [<=] fv_sty_in_sty A2 `union` fv_sty_in_sty A1.
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sty_in_sty_open_sty_wrt_sty_upper : lngen.

Lemma fv_sty_in_sexp_open_sexp_wrt_sty_upper :
forall ee1 A1,
  fv_sty_in_sexp (open_sexp_wrt_sty ee1 A1) [<=] fv_sty_in_sty A1 `union` fv_sty_in_sexp ee1.
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sty_upper : lngen.

Lemma fv_sty_in_sexp_open_sexp_wrt_sexp_upper :
forall ee1 ee2,
  fv_sty_in_sexp (open_sexp_wrt_sexp ee1 ee2) [<=] fv_sty_in_sexp ee2 `union` fv_sty_in_sexp ee1.
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve fv_sty_in_sexp_open_sexp_wrt_sexp_upper : lngen.

Lemma fv_sexp_in_sexp_open_sexp_wrt_sty_upper :
forall ee1 A1,
  fv_sexp_in_sexp (open_sexp_wrt_sty ee1 A1) [<=] fv_sexp_in_sexp ee1.
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sty_upper : lngen.

Lemma fv_sexp_in_sexp_open_sexp_wrt_sexp_upper :
forall ee1 ee2,
  fv_sexp_in_sexp (open_sexp_wrt_sexp ee1 ee2) [<=] fv_sexp_in_sexp ee2 `union` fv_sexp_in_sexp ee1.
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve fv_sexp_in_sexp_open_sexp_wrt_sexp_upper : lngen.

(* begin hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  fv_sty_in_sty (subst_sty_in_sty A2 X1 A1) [=] fv_sty_in_sty A1).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_fresh :
forall A1 A2 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  fv_sty_in_sty (subst_sty_in_sty A2 X1 A1) [=] fv_sty_in_sty A1.
Proof.
pose proof fv_sty_in_sty_subst_sty_in_sty_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_subst_sty_in_sty_fresh : lngen.
Hint Rewrite fv_sty_in_sty_subst_sty_in_sty_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_fresh_mutual :
(forall ee1 A1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1) [=] fv_sty_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_fresh :
forall ee1 A1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1) [=] fv_sty_in_sexp ee1.
Proof.
pose proof fv_sty_in_sexp_subst_sty_in_sexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sty_in_sexp_fresh : lngen.
Hint Rewrite fv_sty_in_sexp_subst_sty_in_sexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_fresh_mutual :
(forall ee1 A1 X1,
  fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1) [=] fv_sexp_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_fresh :
forall ee1 A1 X1,
  fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1) [=] fv_sexp_in_sexp ee1.
Proof.
pose proof fv_sty_in_sexp_subst_sexp_in_sexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sexp_in_sexp_fresh : lngen.
Hint Rewrite fv_sty_in_sexp_subst_sexp_in_sexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_fresh_mutual :
(forall ee1 ee2 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1) [=] fv_sexp_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_fresh :
forall ee1 ee2 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1) [=] fv_sexp_in_sexp ee1.
Proof.
pose proof fv_sexp_in_sexp_subst_sexp_in_sexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sexp_in_sexp_fresh : lngen.
Hint Rewrite fv_sexp_in_sexp_subst_sexp_in_sexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_lower_mutual :
(forall A1 A2 X1,
  remove X1 (fv_sty_in_sty A1) [<=] fv_sty_in_sty (subst_sty_in_sty A2 X1 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_lower :
forall A1 A2 X1,
  remove X1 (fv_sty_in_sty A1) [<=] fv_sty_in_sty (subst_sty_in_sty A2 X1 A1).
Proof.
pose proof fv_sty_in_sty_subst_sty_in_sty_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_subst_sty_in_sty_lower : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_lower_mutual :
(forall ee1 A1 X1,
  remove X1 (fv_sty_in_sexp ee1) [<=] fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_lower :
forall ee1 A1 X1,
  remove X1 (fv_sty_in_sexp ee1) [<=] fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof fv_sty_in_sexp_subst_sty_in_sexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sty_in_sexp_lower : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_lower_mutual :
(forall ee1 ee2 x1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_lower :
forall ee1 ee2 x1,
  fv_sty_in_sexp ee1 [<=] fv_sty_in_sexp (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof fv_sty_in_sexp_subst_sexp_in_sexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sexp_in_sexp_lower : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sty_in_sexp_lower_mutual :
(forall ee1 A1 X1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sty_in_sexp_lower :
forall ee1 A1 X1,
  fv_sexp_in_sexp ee1 [<=] fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof fv_sexp_in_sexp_subst_sty_in_sexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sty_in_sexp_lower : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_lower_mutual :
(forall ee1 ee2 x1,
  remove x1 (fv_sexp_in_sexp ee1) [<=] fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_lower :
forall ee1 ee2 x1,
  remove x1 (fv_sexp_in_sexp ee1) [<=] fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof fv_sexp_in_sexp_subst_sexp_in_sexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sexp_in_sexp_lower : lngen.

(* begin hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` fv_sty_in_sty A1 ->
  X2 `notin` fv_sty_in_sty A2 ->
  X2 `notin` fv_sty_in_sty (subst_sty_in_sty A2 X1 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_notin :
forall A1 A2 X1 X2,
  X2 `notin` fv_sty_in_sty A1 ->
  X2 `notin` fv_sty_in_sty A2 ->
  X2 `notin` fv_sty_in_sty (subst_sty_in_sty A2 X1 A1).
Proof.
pose proof fv_sty_in_sty_subst_sty_in_sty_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_subst_sty_in_sty_notin : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_notin_mutual :
(forall ee1 A1 X1 X2,
  X2 `notin` fv_sty_in_sexp ee1 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 `notin` fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_notin :
forall ee1 A1 X1 X2,
  X2 `notin` fv_sty_in_sexp ee1 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 `notin` fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof fv_sty_in_sexp_subst_sty_in_sexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sty_in_sexp_notin : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_notin_mutual :
(forall ee1 ee2 x1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_notin :
forall ee1 ee2 x1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof fv_sty_in_sexp_subst_sexp_in_sexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sexp_in_sexp_notin : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sty_in_sexp_notin_mutual :
(forall ee1 A1 X1 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sty_in_sexp_notin :
forall ee1 A1 X1 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof fv_sexp_in_sexp_subst_sty_in_sexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sty_in_sexp_notin : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_notin_mutual :
(forall ee1 ee2 x1 x2,
  x2 `notin` fv_sexp_in_sexp ee1 ->
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 `notin` fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_notin :
forall ee1 ee2 x1 x2,
  x2 `notin` fv_sexp_in_sexp ee1 ->
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 `notin` fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof fv_sexp_in_sexp_subst_sexp_in_sexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sexp_in_sexp_notin : lngen.

(* begin hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_upper_mutual :
(forall A1 A2 X1,
  fv_sty_in_sty (subst_sty_in_sty A2 X1 A1) [<=] fv_sty_in_sty A2 `union` remove X1 (fv_sty_in_sty A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sty_subst_sty_in_sty_upper :
forall A1 A2 X1,
  fv_sty_in_sty (subst_sty_in_sty A2 X1 A1) [<=] fv_sty_in_sty A2 `union` remove X1 (fv_sty_in_sty A1).
Proof.
pose proof fv_sty_in_sty_subst_sty_in_sty_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sty_subst_sty_in_sty_upper : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_upper_mutual :
(forall ee1 A1 X1,
  fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1) [<=] fv_sty_in_sty A1 `union` remove X1 (fv_sty_in_sexp ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sty_in_sexp_upper :
forall ee1 A1 X1,
  fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1) [<=] fv_sty_in_sty A1 `union` remove X1 (fv_sty_in_sexp ee1).
Proof.
pose proof fv_sty_in_sexp_subst_sty_in_sexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sty_in_sexp_upper : lngen.

(* begin hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_upper_mutual :
(forall ee1 ee2 x1,
  fv_sty_in_sexp (subst_sexp_in_sexp ee2 x1 ee1) [<=] fv_sty_in_sexp ee2 `union` fv_sty_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sty_in_sexp_subst_sexp_in_sexp_upper :
forall ee1 ee2 x1,
  fv_sty_in_sexp (subst_sexp_in_sexp ee2 x1 ee1) [<=] fv_sty_in_sexp ee2 `union` fv_sty_in_sexp ee1.
Proof.
pose proof fv_sty_in_sexp_subst_sexp_in_sexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sty_in_sexp_subst_sexp_in_sexp_upper : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sty_in_sexp_upper_mutual :
(forall ee1 A1 X1,
  fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1) [<=] fv_sexp_in_sexp ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sty_in_sexp_upper :
forall ee1 A1 X1,
  fv_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee1) [<=] fv_sexp_in_sexp ee1.
Proof.
pose proof fv_sexp_in_sexp_subst_sty_in_sexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sty_in_sexp_upper : lngen.

(* begin hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_upper_mutual :
(forall ee1 ee2 x1,
  fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1) [<=] fv_sexp_in_sexp ee2 `union` remove x1 (fv_sexp_in_sexp ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_sexp_in_sexp_subst_sexp_in_sexp_upper :
forall ee1 ee2 x1,
  fv_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee1) [<=] fv_sexp_in_sexp ee2 `union` remove x1 (fv_sexp_in_sexp ee1).
Proof.
pose proof fv_sexp_in_sexp_subst_sexp_in_sexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_sexp_in_sexp_subst_sexp_in_sexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_sty_in_sty_close_sty_wrt_sty_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_sty_wrt_sty n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  subst_sty_in_sty A1 X1 (close_sty_wrt_sty_rec n1 X2 A2) = close_sty_wrt_sty_rec n1 X2 (subst_sty_in_sty A1 X1 A2)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_close_sty_wrt_sty_rec :
forall A2 A1 X1 X2 n1,
  degree_sty_wrt_sty n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  subst_sty_in_sty A1 X1 (close_sty_wrt_sty_rec n1 X2 A2) = close_sty_wrt_sty_rec n1 X2 (subst_sty_in_sty A1 X1 A2).
Proof.
pose proof subst_sty_in_sty_close_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_close_sty_wrt_sty_rec : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sty_rec_mutual :
(forall ee1 A1 X1 X2 n1,
  degree_sty_wrt_sty n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  subst_sty_in_sexp A1 X1 (close_sexp_wrt_sty_rec n1 X2 ee1) = close_sexp_wrt_sty_rec n1 X2 (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sty_rec :
forall ee1 A1 X1 X2 n1,
  degree_sty_wrt_sty n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  subst_sty_in_sexp A1 X1 (close_sexp_wrt_sty_rec n1 X2 ee1) = close_sexp_wrt_sty_rec n1 X2 (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sty_rec : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sexp_rec_mutual :
(forall ee1 A1 x1 X1 n1,
  subst_sty_in_sexp A1 x1 (close_sexp_wrt_sexp_rec n1 X1 ee1) = close_sexp_wrt_sexp_rec n1 X1 (subst_sty_in_sexp A1 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sexp_rec :
forall ee1 A1 x1 X1 n1,
  subst_sty_in_sexp A1 x1 (close_sexp_wrt_sexp_rec n1 X1 ee1) = close_sexp_wrt_sexp_rec n1 X1 (subst_sty_in_sexp A1 x1 ee1).
Proof.
pose proof subst_sty_in_sexp_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sexp_rec : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sty_rec_mutual :
(forall ee2 ee1 X1 x1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  x1 `notin` fv_sty_in_sexp ee1 ->
  subst_sexp_in_sexp ee1 X1 (close_sexp_wrt_sty_rec n1 x1 ee2) = close_sexp_wrt_sty_rec n1 x1 (subst_sexp_in_sexp ee1 X1 ee2)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sty_rec :
forall ee2 ee1 X1 x1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  x1 `notin` fv_sty_in_sexp ee1 ->
  subst_sexp_in_sexp ee1 X1 (close_sexp_wrt_sty_rec n1 x1 ee2) = close_sexp_wrt_sty_rec n1 x1 (subst_sexp_in_sexp ee1 X1 ee2).
Proof.
pose proof subst_sexp_in_sexp_close_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sty_rec : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sexp_rec_mutual :
(forall ee2 ee1 x1 x2 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  x1 <> x2 ->
  x2 `notin` fv_sexp_in_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (close_sexp_wrt_sexp_rec n1 x2 ee2) = close_sexp_wrt_sexp_rec n1 x2 (subst_sexp_in_sexp ee1 x1 ee2)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sexp_rec :
forall ee2 ee1 x1 x2 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  x1 <> x2 ->
  x2 `notin` fv_sexp_in_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (close_sexp_wrt_sexp_rec n1 x2 ee2) = close_sexp_wrt_sexp_rec n1 x2 (subst_sexp_in_sexp ee1 x1 ee2).
Proof.
pose proof subst_sexp_in_sexp_close_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sexp_rec : lngen.

Lemma subst_sty_in_sty_close_sty_wrt_sty :
forall A2 A1 X1 X2,
  lc_sty A1 ->  X1 <> X2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  subst_sty_in_sty A1 X1 (close_sty_wrt_sty X2 A2) = close_sty_wrt_sty X2 (subst_sty_in_sty A1 X1 A2).
Proof.
unfold close_sty_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sty_close_sty_wrt_sty : lngen.

Lemma subst_sty_in_sexp_close_sexp_wrt_sty :
forall ee1 A1 X1 X2,
  lc_sty A1 ->  X1 <> X2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  subst_sty_in_sexp A1 X1 (close_sexp_wrt_sty X2 ee1) = close_sexp_wrt_sty X2 (subst_sty_in_sexp A1 X1 ee1).
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sty : lngen.

Lemma subst_sty_in_sexp_close_sexp_wrt_sexp :
forall ee1 A1 x1 X1,
  lc_sty A1 ->  subst_sty_in_sexp A1 x1 (close_sexp_wrt_sexp X1 ee1) = close_sexp_wrt_sexp X1 (subst_sty_in_sexp A1 x1 ee1).
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sexp : lngen.

Lemma subst_sexp_in_sexp_close_sexp_wrt_sty :
forall ee2 ee1 X1 x1,
  lc_sexp ee1 ->  x1 `notin` fv_sty_in_sexp ee1 ->
  subst_sexp_in_sexp ee1 X1 (close_sexp_wrt_sty x1 ee2) = close_sexp_wrt_sty x1 (subst_sexp_in_sexp ee1 X1 ee2).
Proof.
unfold close_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sty : lngen.

Lemma subst_sexp_in_sexp_close_sexp_wrt_sexp :
forall ee2 ee1 x1 x2,
  lc_sexp ee1 ->  x1 <> x2 ->
  x2 `notin` fv_sexp_in_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (close_sexp_wrt_sexp x2 ee2) = close_sexp_wrt_sexp x2 (subst_sexp_in_sexp ee1 x1 ee2).
Proof.
unfold close_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sexp : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_degree_sty_wrt_sty_mutual :
(forall A1 A2 X1 n1,
  degree_sty_wrt_sty n1 A1 ->
  degree_sty_wrt_sty n1 A2 ->
  degree_sty_wrt_sty n1 (subst_sty_in_sty A2 X1 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_degree_sty_wrt_sty :
forall A1 A2 X1 n1,
  degree_sty_wrt_sty n1 A1 ->
  degree_sty_wrt_sty n1 A2 ->
  degree_sty_wrt_sty n1 (subst_sty_in_sty A2 X1 A1).
Proof.
pose proof subst_sty_in_sty_degree_sty_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_degree_sty_wrt_sty : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_degree_sexp_wrt_sty_mutual :
(forall ee1 A1 X1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sty_wrt_sty n1 A1 ->
  degree_sexp_wrt_sty n1 (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_degree_sexp_wrt_sty :
forall ee1 A1 X1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sty_wrt_sty n1 A1 ->
  degree_sexp_wrt_sty n1 (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_degree_sexp_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_degree_sexp_wrt_sty : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_degree_sexp_wrt_sexp_mutual :
(forall ee1 A1 X1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_degree_sexp_wrt_sexp :
forall ee1 A1 X1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_degree_sexp_wrt_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_degree_sexp_wrt_sexp : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_degree_sexp_wrt_sty_mutual :
(forall ee1 ee2 x1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty n1 ee2 ->
  degree_sexp_wrt_sty n1 (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_degree_sexp_wrt_sty :
forall ee1 ee2 x1 n1,
  degree_sexp_wrt_sty n1 ee1 ->
  degree_sexp_wrt_sty n1 ee2 ->
  degree_sexp_wrt_sty n1 (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof subst_sexp_in_sexp_degree_sexp_wrt_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_degree_sexp_wrt_sty : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_degree_sexp_wrt_sexp_mutual :
(forall ee1 ee2 x1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 ee2 ->
  degree_sexp_wrt_sexp n1 (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_degree_sexp_wrt_sexp :
forall ee1 ee2 x1 n1,
  degree_sexp_wrt_sexp n1 ee1 ->
  degree_sexp_wrt_sexp n1 ee2 ->
  degree_sexp_wrt_sexp n1 (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof subst_sexp_in_sexp_degree_sexp_wrt_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_degree_sexp_wrt_sexp : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` fv_sty_in_sty A2 ->
  subst_sty_in_sty A1 X1 A2 = A2).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_fresh_eq :
forall A2 A1 X1,
  X1 `notin` fv_sty_in_sty A2 ->
  subst_sty_in_sty A1 X1 A2 = A2.
Proof.
pose proof subst_sty_in_sty_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_fresh_eq : lngen.
Hint Rewrite subst_sty_in_sty_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_fresh_eq_mutual :
(forall ee1 A1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  subst_sty_in_sexp A1 X1 ee1 = ee1).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_fresh_eq :
forall ee1 A1 X1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  subst_sty_in_sexp A1 X1 ee1 = ee1.
Proof.
pose proof subst_sty_in_sexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_fresh_eq : lngen.
Hint Rewrite subst_sty_in_sexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_fresh_eq_mutual :
(forall ee2 ee1 x1,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  subst_sexp_in_sexp ee1 x1 ee2 = ee2).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_fresh_eq :
forall ee2 ee1 x1,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  subst_sexp_in_sexp ee1 x1 ee2 = ee2.
Proof.
pose proof subst_sexp_in_sexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_fresh_eq : lngen.
Hint Rewrite subst_sexp_in_sexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sty (subst_sty_in_sty A1 X1 A2)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_fresh_same :
forall A2 A1 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sty (subst_sty_in_sty A1 X1 A2).
Proof.
pose proof subst_sty_in_sty_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_fresh_same : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_fresh_same_mutual :
(forall ee1 A1 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_fresh_same :
forall ee1 A1 X1,
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sexp (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_fresh_same_mutual :
(forall ee2 ee1 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp (subst_sexp_in_sexp ee1 x1 ee2)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_fresh_same :
forall ee2 ee1 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp (subst_sexp_in_sexp ee1 x1 ee2).
Proof.
pose proof subst_sexp_in_sexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` fv_sty_in_sty A2 ->
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sty (subst_sty_in_sty A1 X2 A2)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_fresh :
forall A2 A1 X1 X2,
  X1 `notin` fv_sty_in_sty A2 ->
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sty (subst_sty_in_sty A1 X2 A2).
Proof.
pose proof subst_sty_in_sty_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_fresh : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_fresh_mutual :
(forall ee1 A1 X1 X2,
  X1 `notin` fv_sty_in_sexp ee1 ->
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sexp (subst_sty_in_sexp A1 X2 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_fresh :
forall ee1 A1 X1 X2,
  X1 `notin` fv_sty_in_sexp ee1 ->
  X1 `notin` fv_sty_in_sty A1 ->
  X1 `notin` fv_sty_in_sexp (subst_sty_in_sexp A1 X2 ee1).
Proof.
pose proof subst_sty_in_sexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_fresh : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_fresh_mutual :
(forall ee2 ee1 x1 x2,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp (subst_sexp_in_sexp ee1 x2 ee2)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_fresh :
forall ee2 ee1 x1 x2,
  x1 `notin` fv_sexp_in_sexp ee2 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  x1 `notin` fv_sexp_in_sexp (subst_sexp_in_sexp ee1 x2 ee2).
Proof.
pose proof subst_sexp_in_sexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_fresh : lngen.

Lemma subst_sty_in_sty_lc_sty :
forall A1 A2 X1,
  lc_sty A1 ->
  lc_sty A2 ->
  lc_sty (subst_sty_in_sty A2 X1 A1).
Proof.
default_simp.
Qed.

Hint Resolve subst_sty_in_sty_lc_sty : lngen.

Lemma subst_sty_in_sexp_lc_sexp :
forall ee1 A1 X1,
  lc_sexp ee1 ->
  lc_sty A1 ->
  lc_sexp (subst_sty_in_sexp A1 X1 ee1).
Proof.
default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_lc_sexp : lngen.

Lemma subst_sexp_in_sexp_lc_sexp :
forall ee1 ee2 x1,
  lc_sexp ee1 ->
  lc_sexp ee2 ->
  lc_sexp (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_lc_sexp : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_open_sty_wrt_sty_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_sty A1 ->
  subst_sty_in_sty A1 X1 (open_sty_wrt_sty_rec n1 A2 A3) = open_sty_wrt_sty_rec n1 (subst_sty_in_sty A1 X1 A2) (subst_sty_in_sty A1 X1 A3)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sty_open_sty_wrt_sty_rec :
forall A3 A1 A2 X1 n1,
  lc_sty A1 ->
  subst_sty_in_sty A1 X1 (open_sty_wrt_sty_rec n1 A2 A3) = open_sty_wrt_sty_rec n1 (subst_sty_in_sty A1 X1 A2) (subst_sty_in_sty A1 X1 A3).
Proof.
pose proof subst_sty_in_sty_open_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_open_sty_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_open_sexp_wrt_sty_rec_mutual :
(forall ee1 A1 A2 X1 n1,
  lc_sty A1 ->
  subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty_rec n1 A2 ee1) = open_sexp_wrt_sty_rec n1 (subst_sty_in_sty A1 X1 A2) (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_open_sexp_wrt_sty_rec :
forall ee1 A1 A2 X1 n1,
  lc_sty A1 ->
  subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty_rec n1 A2 ee1) = open_sexp_wrt_sty_rec n1 (subst_sty_in_sty A1 X1 A2) (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_open_sexp_wrt_sexp_rec_mutual :
(forall ee2 A1 ee1 X1 n1,
  subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp_rec n1 ee1 ee2) = open_sexp_wrt_sexp_rec n1 (subst_sty_in_sexp A1 X1 ee1) (subst_sty_in_sexp A1 X1 ee2)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_open_sexp_wrt_sexp_rec :
forall ee2 A1 ee1 X1 n1,
  subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp_rec n1 ee1 ee2) = open_sexp_wrt_sexp_rec n1 (subst_sty_in_sexp A1 X1 ee1) (subst_sty_in_sexp A1 X1 ee2).
Proof.
pose proof subst_sty_in_sexp_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_open_sexp_wrt_sty_rec_mutual :
(forall ee2 ee1 A1 x1 n1,
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty_rec n1 A1 ee2) = open_sexp_wrt_sty_rec n1 A1 (subst_sexp_in_sexp ee1 x1 ee2)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_open_sexp_wrt_sty_rec :
forall ee2 ee1 A1 x1 n1,
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty_rec n1 A1 ee2) = open_sexp_wrt_sty_rec n1 A1 (subst_sexp_in_sexp ee1 x1 ee2).
Proof.
pose proof subst_sexp_in_sexp_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_open_sexp_wrt_sexp_rec_mutual :
(forall ee3 ee1 ee2 x1 n1,
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp_rec n1 ee2 ee3) = open_sexp_wrt_sexp_rec n1 (subst_sexp_in_sexp ee1 x1 ee2) (subst_sexp_in_sexp ee1 x1 ee3)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_open_sexp_wrt_sexp_rec :
forall ee3 ee1 ee2 x1 n1,
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp_rec n1 ee2 ee3) = open_sexp_wrt_sexp_rec n1 (subst_sexp_in_sexp ee1 x1 ee2) (subst_sexp_in_sexp ee1 x1 ee3).
Proof.
pose proof subst_sexp_in_sexp_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

Lemma subst_sty_in_sty_open_sty_wrt_sty :
forall A3 A1 A2 X1,
  lc_sty A1 ->
  subst_sty_in_sty A1 X1 (open_sty_wrt_sty A3 A2) = open_sty_wrt_sty (subst_sty_in_sty A1 X1 A3) (subst_sty_in_sty A1 X1 A2).
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sty_open_sty_wrt_sty : lngen.

Lemma subst_sty_in_sexp_open_sexp_wrt_sty :
forall ee1 A1 A2 X1,
  lc_sty A1 ->
  subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty ee1 A2) = open_sexp_wrt_sty (subst_sty_in_sexp A1 X1 ee1) (subst_sty_in_sty A1 X1 A2).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_open_sexp_wrt_sty : lngen.

Lemma subst_sty_in_sexp_open_sexp_wrt_sexp :
forall ee2 A1 ee1 X1,
  subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp ee2 ee1) = open_sexp_wrt_sexp (subst_sty_in_sexp A1 X1 ee2) (subst_sty_in_sexp A1 X1 ee1).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_open_sexp_wrt_sexp : lngen.

Lemma subst_sexp_in_sexp_open_sexp_wrt_sty :
forall ee2 ee1 A1 x1,
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty ee2 A1) = open_sexp_wrt_sty (subst_sexp_in_sexp ee1 x1 ee2) A1.
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_open_sexp_wrt_sty : lngen.

Lemma subst_sexp_in_sexp_open_sexp_wrt_sexp :
forall ee3 ee1 ee2 x1,
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp ee3 ee2) = open_sexp_wrt_sexp (subst_sexp_in_sexp ee1 x1 ee3) (subst_sexp_in_sexp ee1 x1 ee2).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_open_sexp_wrt_sexp : lngen.

Lemma subst_sty_in_sty_open_sty_wrt_sty_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_sty A1 ->
  open_sty_wrt_sty (subst_sty_in_sty A1 X1 A2) (sty_var_f X2) = subst_sty_in_sty A1 X1 (open_sty_wrt_sty A2 (sty_var_f X2)).
Proof.
intros; rewrite subst_sty_in_sty_open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sty_open_sty_wrt_sty_var : lngen.

Lemma subst_sty_in_sexp_open_sexp_wrt_sty_var :
forall ee1 A1 X1 X2,
  X1 <> X2 ->
  lc_sty A1 ->
  open_sexp_wrt_sty (subst_sty_in_sexp A1 X1 ee1) (sty_var_f X2) = subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty ee1 (sty_var_f X2)).
Proof.
intros; rewrite subst_sty_in_sexp_open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_open_sexp_wrt_sty_var : lngen.

Lemma subst_sty_in_sexp_open_sexp_wrt_sexp_var :
forall ee1 A1 X1 x1,
  open_sexp_wrt_sexp (subst_sty_in_sexp A1 X1 ee1) (sexp_var_f x1) = subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp ee1 (sexp_var_f x1)).
Proof.
intros; rewrite subst_sty_in_sexp_open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_open_sexp_wrt_sexp_var : lngen.

Lemma subst_sexp_in_sexp_open_sexp_wrt_sty_var :
forall ee2 ee1 x1 X1,
  lc_sexp ee1 ->
  open_sexp_wrt_sty (subst_sexp_in_sexp ee1 x1 ee2) (sty_var_f X1) = subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty ee2 (sty_var_f X1)).
Proof.
intros; rewrite subst_sexp_in_sexp_open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_open_sexp_wrt_sty_var : lngen.

Lemma subst_sexp_in_sexp_open_sexp_wrt_sexp_var :
forall ee2 ee1 x1 x2,
  x1 <> x2 ->
  lc_sexp ee1 ->
  open_sexp_wrt_sexp (subst_sexp_in_sexp ee1 x1 ee2) (sexp_var_f x2) = subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp ee2 (sexp_var_f x2)).
Proof.
intros; rewrite subst_sexp_in_sexp_open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_open_sexp_wrt_sexp_var : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_sty_in_sty A2 X1 A1 = open_sty_wrt_sty_rec n1 A2 (close_sty_wrt_sty_rec n1 X1 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sty_spec_rec :
forall A1 A2 X1 n1,
  subst_sty_in_sty A2 X1 A1 = open_sty_wrt_sty_rec n1 A2 (close_sty_wrt_sty_rec n1 X1 A1).
Proof.
pose proof subst_sty_in_sty_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_spec_rec_mutual :
(forall ee1 A1 X1 n1,
  subst_sty_in_sexp A1 X1 ee1 = open_sexp_wrt_sty_rec n1 A1 (close_sexp_wrt_sty_rec n1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_spec_rec :
forall ee1 A1 X1 n1,
  subst_sty_in_sexp A1 X1 ee1 = open_sexp_wrt_sty_rec n1 A1 (close_sexp_wrt_sty_rec n1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_spec_rec_mutual :
(forall ee1 ee2 x1 n1,
  subst_sexp_in_sexp ee2 x1 ee1 = open_sexp_wrt_sexp_rec n1 ee2 (close_sexp_wrt_sexp_rec n1 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_spec_rec :
forall ee1 ee2 x1 n1,
  subst_sexp_in_sexp ee2 x1 ee1 = open_sexp_wrt_sexp_rec n1 ee2 (close_sexp_wrt_sexp_rec n1 x1 ee1).
Proof.
pose proof subst_sexp_in_sexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_spec_rec : lngen.

(* end hide *)

Lemma subst_sty_in_sty_spec :
forall A1 A2 X1,
  subst_sty_in_sty A2 X1 A1 = open_sty_wrt_sty (close_sty_wrt_sty X1 A1) A2.
Proof.
unfold close_sty_wrt_sty; unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sty_spec : lngen.

Lemma subst_sty_in_sexp_spec :
forall ee1 A1 X1,
  subst_sty_in_sexp A1 X1 ee1 = open_sexp_wrt_sty (close_sexp_wrt_sty X1 ee1) A1.
Proof.
unfold close_sexp_wrt_sty; unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_spec : lngen.

Lemma subst_sexp_in_sexp_spec :
forall ee1 ee2 x1,
  subst_sexp_in_sexp ee2 x1 ee1 = open_sexp_wrt_sexp (close_sexp_wrt_sexp x1 ee1) ee2.
Proof.
unfold close_sexp_wrt_sexp; unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_spec : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_subst_sty_in_sty_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` fv_sty_in_sty A2 ->
  X2 <> X1 ->
  subst_sty_in_sty A2 X1 (subst_sty_in_sty A3 X2 A1) = subst_sty_in_sty (subst_sty_in_sty A2 X1 A3) X2 (subst_sty_in_sty A2 X1 A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_subst_sty_in_sty :
forall A1 A2 A3 X2 X1,
  X2 `notin` fv_sty_in_sty A2 ->
  X2 <> X1 ->
  subst_sty_in_sty A2 X1 (subst_sty_in_sty A3 X2 A1) = subst_sty_in_sty (subst_sty_in_sty A2 X1 A3) X2 (subst_sty_in_sty A2 X1 A1).
Proof.
pose proof subst_sty_in_sty_subst_sty_in_sty_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_subst_sty_in_sty : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_subst_sty_in_sexp_mutual :
(forall ee1 A1 A2 X2 X1,
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  subst_sty_in_sexp A1 X1 (subst_sty_in_sexp A2 X2 ee1) = subst_sty_in_sexp (subst_sty_in_sty A1 X1 A2) X2 (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_subst_sty_in_sexp :
forall ee1 A1 A2 X2 X1,
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  subst_sty_in_sexp A1 X1 (subst_sty_in_sexp A2 X2 ee1) = subst_sty_in_sexp (subst_sty_in_sty A1 X1 A2) X2 (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_subst_sty_in_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_subst_sty_in_sexp : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_subst_sexp_in_sexp_mutual :
(forall ee1 A1 ee2 x1 X1,
  subst_sty_in_sexp A1 X1 (subst_sexp_in_sexp ee2 x1 ee1) = subst_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee2) x1 (subst_sty_in_sexp A1 X1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_subst_sexp_in_sexp :
forall ee1 A1 ee2 x1 X1,
  subst_sty_in_sexp A1 X1 (subst_sexp_in_sexp ee2 x1 ee1) = subst_sexp_in_sexp (subst_sty_in_sexp A1 X1 ee2) x1 (subst_sty_in_sexp A1 X1 ee1).
Proof.
pose proof subst_sty_in_sexp_subst_sexp_in_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_subst_sexp_in_sexp : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_subst_sty_in_sexp_mutual :
(forall ee1 ee2 A1 X1 x1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  subst_sexp_in_sexp ee2 x1 (subst_sty_in_sexp A1 X1 ee1) = subst_sty_in_sexp A1 X1 (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_subst_sty_in_sexp :
forall ee1 ee2 A1 X1 x1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  subst_sexp_in_sexp ee2 x1 (subst_sty_in_sexp A1 X1 ee1) = subst_sty_in_sexp A1 X1 (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof subst_sexp_in_sexp_subst_sty_in_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_subst_sty_in_sexp : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_subst_sexp_in_sexp_mutual :
(forall ee1 ee2 ee3 x2 x1,
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 <> x1 ->
  subst_sexp_in_sexp ee2 x1 (subst_sexp_in_sexp ee3 x2 ee1) = subst_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee3) x2 (subst_sexp_in_sexp ee2 x1 ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_subst_sexp_in_sexp :
forall ee1 ee2 ee3 x2 x1,
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 <> x1 ->
  subst_sexp_in_sexp ee2 x1 (subst_sexp_in_sexp ee3 x2 ee1) = subst_sexp_in_sexp (subst_sexp_in_sexp ee2 x1 ee3) x2 (subst_sexp_in_sexp ee2 x1 ee1).
Proof.
pose proof subst_sexp_in_sexp_subst_sexp_in_sexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_subst_sexp_in_sexp : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_close_sty_wrt_sty_rec_open_sty_wrt_sty_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` fv_sty_in_sty A2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  degree_sty_wrt_sty n1 A1 ->
  subst_sty_in_sty A1 X1 A2 = close_sty_wrt_sty_rec n1 X2 (subst_sty_in_sty A1 X1 (open_sty_wrt_sty_rec n1 (sty_var_f X2) A2))).
Proof.
apply_mutual_ind sty_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sty_close_sty_wrt_sty_rec_open_sty_wrt_sty_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` fv_sty_in_sty A2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  degree_sty_wrt_sty n1 A1 ->
  subst_sty_in_sty A1 X1 A2 = close_sty_wrt_sty_rec n1 X2 (subst_sty_in_sty A1 X1 (open_sty_wrt_sty_rec n1 (sty_var_f X2) A2)).
Proof.
pose proof subst_sty_in_sty_close_sty_wrt_sty_rec_open_sty_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_close_sty_wrt_sty_rec_open_sty_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec_mutual :
(forall ee1 A1 X1 X2 n1,
  X2 `notin` fv_sty_in_sexp ee1 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  degree_sty_wrt_sty n1 A1 ->
  subst_sty_in_sexp A1 X1 ee1 = close_sexp_wrt_sty_rec n1 X2 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty_rec n1 (sty_var_f X2) ee1))).
Proof.
apply_mutual_ind sexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec :
forall ee1 A1 X1 X2 n1,
  X2 `notin` fv_sty_in_sexp ee1 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  degree_sty_wrt_sty n1 A1 ->
  subst_sty_in_sexp A1 X1 ee1 = close_sexp_wrt_sty_rec n1 X2 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty_rec n1 (sty_var_f X2) ee1)).
Proof.
pose proof subst_sty_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec_mutual :
(forall ee1 A1 X1 x1 n1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  subst_sty_in_sexp A1 X1 ee1 = close_sexp_wrt_sexp_rec n1 x1 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1))).
Proof.
apply_mutual_ind sexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sty_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec :
forall ee1 A1 X1 x1 n1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  subst_sty_in_sexp A1 X1 ee1 = close_sexp_wrt_sexp_rec n1 x1 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1)).
Proof.
pose proof subst_sty_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec_mutual :
(forall ee2 ee1 x1 X1 n1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  degree_sexp_wrt_sty n1 ee1 ->
  subst_sexp_in_sexp ee1 x1 ee2 = close_sexp_wrt_sty_rec n1 X1 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee2))).
Proof.
apply_mutual_ind sexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec :
forall ee2 ee1 x1 X1 n1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  degree_sexp_wrt_sty n1 ee1 ->
  subst_sexp_in_sexp ee1 x1 ee2 = close_sexp_wrt_sty_rec n1 X1 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee2)).
Proof.
pose proof subst_sexp_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sty_rec_open_sexp_wrt_sty_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec_mutual :
(forall ee2 ee1 x1 x2 n1,
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 `notin` fv_sexp_in_sexp ee1 ->
  x2 <> x1 ->
  degree_sexp_wrt_sexp n1 ee1 ->
  subst_sexp_in_sexp ee1 x1 ee2 = close_sexp_wrt_sexp_rec n1 x2 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x2) ee2))).
Proof.
apply_mutual_ind sexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_sexp_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec :
forall ee2 ee1 x1 x2 n1,
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 `notin` fv_sexp_in_sexp ee1 ->
  x2 <> x1 ->
  degree_sexp_wrt_sexp n1 ee1 ->
  subst_sexp_in_sexp ee1 x1 ee2 = close_sexp_wrt_sexp_rec n1 x2 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x2) ee2)).
Proof.
pose proof subst_sexp_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sexp_rec_open_sexp_wrt_sexp_rec : lngen.

(* end hide *)

Lemma subst_sty_in_sty_close_sty_wrt_sty_open_sty_wrt_sty :
forall A2 A1 X1 X2,
  X2 `notin` fv_sty_in_sty A2 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  lc_sty A1 ->
  subst_sty_in_sty A1 X1 A2 = close_sty_wrt_sty X2 (subst_sty_in_sty A1 X1 (open_sty_wrt_sty A2 (sty_var_f X2))).
Proof.
unfold close_sty_wrt_sty; unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sty_close_sty_wrt_sty_open_sty_wrt_sty : lngen.

Lemma subst_sty_in_sexp_close_sexp_wrt_sty_open_sexp_wrt_sty :
forall ee1 A1 X1 X2,
  X2 `notin` fv_sty_in_sexp ee1 ->
  X2 `notin` fv_sty_in_sty A1 ->
  X2 <> X1 ->
  lc_sty A1 ->
  subst_sty_in_sexp A1 X1 ee1 = close_sexp_wrt_sty X2 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty ee1 (sty_var_f X2))).
Proof.
unfold close_sexp_wrt_sty; unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sty_open_sexp_wrt_sty : lngen.

Lemma subst_sty_in_sexp_close_sexp_wrt_sexp_open_sexp_wrt_sexp :
forall ee1 A1 X1 x1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  lc_sty A1 ->
  subst_sty_in_sexp A1 X1 ee1 = close_sexp_wrt_sexp x1 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp ee1 (sexp_var_f x1))).
Proof.
unfold close_sexp_wrt_sexp; unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_close_sexp_wrt_sexp_open_sexp_wrt_sexp : lngen.

Lemma subst_sexp_in_sexp_close_sexp_wrt_sty_open_sexp_wrt_sty :
forall ee2 ee1 x1 X1,
  X1 `notin` fv_sty_in_sexp ee2 ->
  X1 `notin` fv_sty_in_sexp ee1 ->
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 ee2 = close_sexp_wrt_sty X1 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty ee2 (sty_var_f X1))).
Proof.
unfold close_sexp_wrt_sty; unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sty_open_sexp_wrt_sty : lngen.

Lemma subst_sexp_in_sexp_close_sexp_wrt_sexp_open_sexp_wrt_sexp :
forall ee2 ee1 x1 x2,
  x2 `notin` fv_sexp_in_sexp ee2 ->
  x2 `notin` fv_sexp_in_sexp ee1 ->
  x2 <> x1 ->
  lc_sexp ee1 ->
  subst_sexp_in_sexp ee1 x1 ee2 = close_sexp_wrt_sexp x2 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp ee2 (sexp_var_f x2))).
Proof.
unfold close_sexp_wrt_sexp; unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_close_sexp_wrt_sexp_open_sexp_wrt_sexp : lngen.

Lemma subst_sty_in_sty_sty_all :
forall X2 A2 B1 A1 X1,
  lc_sty A1 ->
  X2 `notin` fv_sty_in_sty A1 `union` fv_sty_in_sty B1 `union` singleton X1 ->
  subst_sty_in_sty A1 X1 (sty_all A2 B1) = sty_all (subst_sty_in_sty A1 X1 A2) (close_sty_wrt_sty X2 (subst_sty_in_sty A1 X1 (open_sty_wrt_sty B1 (sty_var_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_sty_in_sty_sty_all : lngen.

Lemma subst_sty_in_sexp_sexp_abs :
forall x1 ee1 A1 X1,
  lc_sty A1 ->
  x1 `notin` fv_sexp_in_sexp ee1 ->
  subst_sty_in_sexp A1 X1 (sexp_abs ee1) = sexp_abs (close_sexp_wrt_sexp x1 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sexp ee1 (sexp_var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_sexp_abs : lngen.

Lemma subst_sty_in_sexp_sexp_tabs :
forall X2 A2 ee1 A1 X1,
  lc_sty A1 ->
  X2 `notin` fv_sty_in_sty A1 `union` fv_sty_in_sexp ee1 `union` singleton X1 ->
  subst_sty_in_sexp A1 X1 (sexp_tabs A2 ee1) = sexp_tabs (subst_sty_in_sty A1 X1 A2) (close_sexp_wrt_sty X2 (subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty ee1 (sty_var_f X2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_sexp_tabs : lngen.

Lemma subst_sexp_in_sexp_sexp_abs :
forall x2 ee2 ee1 x1,
  lc_sexp ee1 ->
  x2 `notin` fv_sexp_in_sexp ee1 `union` fv_sexp_in_sexp ee2 `union` singleton x1 ->
  subst_sexp_in_sexp ee1 x1 (sexp_abs ee2) = sexp_abs (close_sexp_wrt_sexp x2 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sexp ee2 (sexp_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_sexp_abs : lngen.

Lemma subst_sexp_in_sexp_sexp_tabs :
forall X1 A1 ee2 ee1 x1,
  lc_sexp ee1 ->
  X1 `notin` fv_sty_in_sexp ee1 `union` fv_sty_in_sexp ee2 ->
  subst_sexp_in_sexp ee1 x1 (sexp_tabs A1 ee2) = sexp_tabs (A1) (close_sexp_wrt_sty X1 (subst_sexp_in_sexp ee1 x1 (open_sexp_wrt_sty ee2 (sty_var_f X1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_sexp_tabs : lngen.

(* begin hide *)

Lemma subst_sty_in_sty_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` fv_sty_in_sty A1 ->
  open_sty_wrt_sty_rec n1 A2 A1 = subst_sty_in_sty A2 X1 (open_sty_wrt_sty_rec n1 (sty_var_f X1) A1)).
Proof.
apply_mutual_ind sty_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sty_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` fv_sty_in_sty A1 ->
  open_sty_wrt_sty_rec n1 A2 A1 = subst_sty_in_sty A2 X1 (open_sty_wrt_sty_rec n1 (sty_var_f X1) A1).
Proof.
pose proof subst_sty_in_sty_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sty_intro_rec : lngen.
Hint Rewrite subst_sty_in_sty_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_sty_in_sexp_intro_rec_mutual :
(forall ee1 X1 A1 n1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  open_sexp_wrt_sty_rec n1 A1 ee1 = subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sty_in_sexp_intro_rec :
forall ee1 X1 A1 n1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  open_sexp_wrt_sty_rec n1 A1 ee1 = subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty_rec n1 (sty_var_f X1) ee1).
Proof.
pose proof subst_sty_in_sexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sty_in_sexp_intro_rec : lngen.
Hint Rewrite subst_sty_in_sexp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_sexp_in_sexp_intro_rec_mutual :
(forall ee1 x1 ee2 n1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  open_sexp_wrt_sexp_rec n1 ee2 ee1 = subst_sexp_in_sexp ee2 x1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1)).
Proof.
apply_mutual_ind sexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_sexp_in_sexp_intro_rec :
forall ee1 x1 ee2 n1,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  open_sexp_wrt_sexp_rec n1 ee2 ee1 = subst_sexp_in_sexp ee2 x1 (open_sexp_wrt_sexp_rec n1 (sexp_var_f x1) ee1).
Proof.
pose proof subst_sexp_in_sexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_sexp_in_sexp_intro_rec : lngen.
Hint Rewrite subst_sexp_in_sexp_intro_rec using solve [auto] : lngen.

Lemma subst_sty_in_sty_intro :
forall X1 A1 A2,
  X1 `notin` fv_sty_in_sty A1 ->
  open_sty_wrt_sty A1 A2 = subst_sty_in_sty A2 X1 (open_sty_wrt_sty A1 (sty_var_f X1)).
Proof.
unfold open_sty_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sty_intro : lngen.

Lemma subst_sty_in_sexp_intro :
forall X1 ee1 A1,
  X1 `notin` fv_sty_in_sexp ee1 ->
  open_sexp_wrt_sty ee1 A1 = subst_sty_in_sexp A1 X1 (open_sexp_wrt_sty ee1 (sty_var_f X1)).
Proof.
unfold open_sexp_wrt_sty; default_simp.
Qed.

Hint Resolve subst_sty_in_sexp_intro : lngen.

Lemma subst_sexp_in_sexp_intro :
forall x1 ee1 ee2,
  x1 `notin` fv_sexp_in_sexp ee1 ->
  open_sexp_wrt_sexp ee1 ee2 = subst_sexp_in_sexp ee2 x1 (open_sexp_wrt_sexp ee1 (sexp_var_f x1)).
Proof.
unfold open_sexp_wrt_sexp; default_simp.
Qed.

Hint Resolve subst_sexp_in_sexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
