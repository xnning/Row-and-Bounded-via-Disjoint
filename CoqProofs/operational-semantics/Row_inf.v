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

Scheme rlist_ind' := Induction for rlist Sort Prop
  with rt_ind' := Induction for rt Sort Prop
  with rtyp_ind' := Induction for rtyp Sort Prop.

Definition rlist_rt_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (conj (rlist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  ((conj (rt_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)))).

Scheme rlist_rec' := Induction for rlist Sort Set
  with rt_rec' := Induction for rt Sort Set
  with rtyp_rec' := Induction for rtyp Sort Set.

Definition rlist_rt_rtyp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (pair ((pair (rlist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (rt_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)))
  (rtyp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)).

Scheme rexp_ind' := Induction for rexp Sort Prop.

Definition rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme rexp_rec' := Induction for rexp Sort Set.

Definition rexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  rexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_rlist_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (R1 : rlist) {struct R1} : rlist :=
  match R1 with
    | R_Empty => R_Empty
    | R_Cons r1 R2 => R_Cons (close_rtyp_wrt_rtyp_rec n1 a1 r1) (close_rlist_wrt_rtyp_rec n1 a1 R2)
  end

with close_rt_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (u1 : rt) {struct u1} : rt :=
  match u1 with
    | rt_Base => rt_Base
    | rt_Fun rt1 rt2 => rt_Fun (close_rt_wrt_rtyp_rec n1 a1 rt1) (close_rt_wrt_rtyp_rec n1 a1 rt2)
    | rt_ConQuan R1 rt1 => rt_ConQuan (close_rlist_wrt_rtyp_rec n1 a1 R1) (close_rt_wrt_rtyp_rec (S n1) a1 rt1)
    | rt_Record r1 => rt_Record (close_rtyp_wrt_rtyp_rec n1 a1 r1)
  end

with close_rtyp_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (r1 : rtyp) {struct r1} : rtyp :=
  match r1 with
    | r_TyVar_f a2 => if (a1 == a2) then (r_TyVar_b n1) else (r_TyVar_f a2)
    | r_TyVar_b n2 => if (lt_ge_dec n2 n1) then (r_TyVar_b n2) else (r_TyVar_b (S n2))
    | r_Empty => r_Empty
    | r_SingleField l1 rt1 => r_SingleField l1 (close_rt_wrt_rtyp_rec n1 a1 rt1)
    | r_Merge r2 r3 => r_Merge (close_rtyp_wrt_rtyp_rec n1 a1 r2) (close_rtyp_wrt_rtyp_rec n1 a1 r3)
  end.

Definition close_rlist_wrt_rtyp a1 R1 := close_rlist_wrt_rtyp_rec 0 a1 R1.

Definition close_rt_wrt_rtyp a1 u1 := close_rt_wrt_rtyp_rec 0 a1 u1.

Definition close_rtyp_wrt_rtyp a1 r1 := close_rtyp_wrt_rtyp_rec 0 a1 r1.

Fixpoint close_rexp_wrt_rtyp_rec (n1 : nat) (a1 : typvar) (re1 : rexp) {struct re1} : rexp :=
  match re1 with
    | re_Var_f x1 => re_Var_f x1
    | re_Var_b n2 => re_Var_b n2
    | re_Lit x1 => re_Lit x1
    | re_Abs rt1 re2 => re_Abs (close_rt_wrt_rtyp_rec n1 a1 rt1) (close_rexp_wrt_rtyp_rec n1 a1 re2)
    | re_App re2 re3 => re_App (close_rexp_wrt_rtyp_rec n1 a1 re2) (close_rexp_wrt_rtyp_rec n1 a1 re3)
    | re_Empty => re_Empty
    | re_SingleField l1 re2 => re_SingleField l1 (close_rexp_wrt_rtyp_rec n1 a1 re2)
    | re_Res re2 l1 => re_Res (close_rexp_wrt_rtyp_rec n1 a1 re2) l1
    | re_Merge re2 re3 => re_Merge (close_rexp_wrt_rtyp_rec n1 a1 re2) (close_rexp_wrt_rtyp_rec n1 a1 re3)
    | re_Selection re2 l1 => re_Selection (close_rexp_wrt_rtyp_rec n1 a1 re2) l1
    | re_ConTyAbs R1 re2 => re_ConTyAbs (close_rlist_wrt_rtyp_rec n1 a1 R1) (close_rexp_wrt_rtyp_rec (S n1) a1 re2)
    | re_ConTyApp re2 r1 => re_ConTyApp (close_rexp_wrt_rtyp_rec n1 a1 re2) (close_rtyp_wrt_rtyp_rec n1 a1 r1)
  end.

Fixpoint close_rexp_wrt_rexp_rec (n1 : nat) (x1 : expvar) (re1 : rexp) {struct re1} : rexp :=
  match re1 with
    | re_Var_f x2 => if (x1 == x2) then (re_Var_b n1) else (re_Var_f x2)
    | re_Var_b n2 => if (lt_ge_dec n2 n1) then (re_Var_b n2) else (re_Var_b (S n2))
    | re_Lit x2 => re_Lit x2
    | re_Abs rt1 re2 => re_Abs rt1 (close_rexp_wrt_rexp_rec (S n1) x1 re2)
    | re_App re2 re3 => re_App (close_rexp_wrt_rexp_rec n1 x1 re2) (close_rexp_wrt_rexp_rec n1 x1 re3)
    | re_Empty => re_Empty
    | re_SingleField l1 re2 => re_SingleField l1 (close_rexp_wrt_rexp_rec n1 x1 re2)
    | re_Res re2 l1 => re_Res (close_rexp_wrt_rexp_rec n1 x1 re2) l1
    | re_Merge re2 re3 => re_Merge (close_rexp_wrt_rexp_rec n1 x1 re2) (close_rexp_wrt_rexp_rec n1 x1 re3)
    | re_Selection re2 l1 => re_Selection (close_rexp_wrt_rexp_rec n1 x1 re2) l1
    | re_ConTyAbs R1 re2 => re_ConTyAbs R1 (close_rexp_wrt_rexp_rec n1 x1 re2)
    | re_ConTyApp re2 r1 => re_ConTyApp (close_rexp_wrt_rexp_rec n1 x1 re2) r1
  end.

Definition close_rexp_wrt_rtyp a1 re1 := close_rexp_wrt_rtyp_rec 0 a1 re1.

Definition close_rexp_wrt_rexp x1 re1 := close_rexp_wrt_rexp_rec 0 x1 re1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_rlist (R1 : rlist) {struct R1} : nat :=
  match R1 with
    | R_Empty => 1
    | R_Cons r1 R2 => 1 + (size_rtyp r1) + (size_rlist R2)
  end

with size_rt (u1 : rt) {struct u1} : nat :=
  match u1 with
    | rt_Base => 1
    | rt_Fun rt1 rt2 => 1 + (size_rt rt1) + (size_rt rt2)
    | rt_ConQuan R1 rt1 => 1 + (size_rlist R1) + (size_rt rt1)
    | rt_Record r1 => 1 + (size_rtyp r1)
  end

with size_rtyp (r1 : rtyp) {struct r1} : nat :=
  match r1 with
    | r_TyVar_f a1 => 1
    | r_TyVar_b n1 => 1
    | r_Empty => 1
    | r_SingleField l1 rt1 => 1 + (size_rt rt1)
    | r_Merge r2 r3 => 1 + (size_rtyp r2) + (size_rtyp r3)
  end.

Fixpoint size_rexp (re1 : rexp) {struct re1} : nat :=
  match re1 with
    | re_Var_f x1 => 1
    | re_Var_b n1 => 1
    | re_Lit x1 => 1
    | re_Abs rt1 re2 => 1 + (size_rt rt1) + (size_rexp re2)
    | re_App re2 re3 => 1 + (size_rexp re2) + (size_rexp re3)
    | re_Empty => 1
    | re_SingleField l1 re2 => 1 + (size_rexp re2)
    | re_Res re2 l1 => 1 + (size_rexp re2)
    | re_Merge re2 re3 => 1 + (size_rexp re2) + (size_rexp re3)
    | re_Selection re2 l1 => 1 + (size_rexp re2)
    | re_ConTyAbs R1 re2 => 1 + (size_rlist R1) + (size_rexp re2)
    | re_ConTyApp re2 r1 => 1 + (size_rexp re2) + (size_rtyp r1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_rlist_wrt_rtyp : nat -> rlist -> Prop :=
  | degree_wrt_rtyp_R_Empty : forall n1,
    degree_rlist_wrt_rtyp n1 (R_Empty)
  | degree_wrt_rtyp_R_Cons : forall n1 r1 R1,
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rlist_wrt_rtyp n1 R1 ->
    degree_rlist_wrt_rtyp n1 (R_Cons r1 R1)

with degree_rt_wrt_rtyp : nat -> rt -> Prop :=
  | degree_wrt_rtyp_rt_Base : forall n1,
    degree_rt_wrt_rtyp n1 (rt_Base)
  | degree_wrt_rtyp_rt_Fun : forall n1 rt1 rt2,
    degree_rt_wrt_rtyp n1 rt1 ->
    degree_rt_wrt_rtyp n1 rt2 ->
    degree_rt_wrt_rtyp n1 (rt_Fun rt1 rt2)
  | degree_wrt_rtyp_rt_ConQuan : forall n1 R1 rt1,
    degree_rlist_wrt_rtyp n1 R1 ->
    degree_rt_wrt_rtyp (S n1) rt1 ->
    degree_rt_wrt_rtyp n1 (rt_ConQuan R1 rt1)
  | degree_wrt_rtyp_rt_Record : forall n1 r1,
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rt_wrt_rtyp n1 (rt_Record r1)

with degree_rtyp_wrt_rtyp : nat -> rtyp -> Prop :=
  | degree_wrt_rtyp_r_TyVar_f : forall n1 a1,
    degree_rtyp_wrt_rtyp n1 (r_TyVar_f a1)
  | degree_wrt_rtyp_r_TyVar_b : forall n1 n2,
    lt n2 n1 ->
    degree_rtyp_wrt_rtyp n1 (r_TyVar_b n2)
  | degree_wrt_rtyp_r_Empty : forall n1,
    degree_rtyp_wrt_rtyp n1 (r_Empty)
  | degree_wrt_rtyp_r_SingleField : forall n1 l1 rt1,
    degree_rt_wrt_rtyp n1 rt1 ->
    degree_rtyp_wrt_rtyp n1 (r_SingleField l1 rt1)
  | degree_wrt_rtyp_r_Merge : forall n1 r1 r2,
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rtyp_wrt_rtyp n1 r2 ->
    degree_rtyp_wrt_rtyp n1 (r_Merge r1 r2).

Scheme degree_rlist_wrt_rtyp_ind' := Induction for degree_rlist_wrt_rtyp Sort Prop
  with degree_rt_wrt_rtyp_ind' := Induction for degree_rt_wrt_rtyp Sort Prop
  with degree_rtyp_wrt_rtyp_ind' := Induction for degree_rtyp_wrt_rtyp Sort Prop.

Definition degree_rlist_wrt_rtyp_degree_rt_wrt_rtyp_degree_rtyp_wrt_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 =>
  (conj (degree_rlist_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  ((conj (degree_rt_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)
  (degree_rtyp_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)))).

Hint Constructors degree_rlist_wrt_rtyp : core lngen.

Hint Constructors degree_rt_wrt_rtyp : core lngen.

Hint Constructors degree_rtyp_wrt_rtyp : core lngen.

Inductive degree_rexp_wrt_rtyp : nat -> rexp -> Prop :=
  | degree_wrt_rtyp_re_Var_f : forall n1 x1,
    degree_rexp_wrt_rtyp n1 (re_Var_f x1)
  | degree_wrt_rtyp_re_Var_b : forall n1 n2,
    degree_rexp_wrt_rtyp n1 (re_Var_b n2)
  | degree_wrt_rtyp_re_Lit : forall n1 n2,
    degree_rexp_wrt_rtyp n1 (re_Lit n2)
  | degree_wrt_rtyp_re_Abs : forall n1 rt1 re1,
    degree_rt_wrt_rtyp n1 rt1 ->
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_Abs rt1 re1)
  | degree_wrt_rtyp_re_App : forall n1 re1 re2,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 re2 ->
    degree_rexp_wrt_rtyp n1 (re_App re1 re2)
  | degree_wrt_rtyp_re_Empty : forall n1,
    degree_rexp_wrt_rtyp n1 (re_Empty)
  | degree_wrt_rtyp_re_SingleField : forall n1 l1 re1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_SingleField l1 re1)
  | degree_wrt_rtyp_re_Res : forall n1 re1 l1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_Res re1 l1)
  | degree_wrt_rtyp_re_Merge : forall n1 re1 re2,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 re2 ->
    degree_rexp_wrt_rtyp n1 (re_Merge re1 re2)
  | degree_wrt_rtyp_re_Selection : forall n1 re1 l1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rexp_wrt_rtyp n1 (re_Selection re1 l1)
  | degree_wrt_rtyp_re_ConTyAbs : forall n1 R1 re1,
    degree_rlist_wrt_rtyp n1 R1 ->
    degree_rexp_wrt_rtyp (S n1) re1 ->
    degree_rexp_wrt_rtyp n1 (re_ConTyAbs R1 re1)
  | degree_wrt_rtyp_re_ConTyApp : forall n1 re1 r1,
    degree_rexp_wrt_rtyp n1 re1 ->
    degree_rtyp_wrt_rtyp n1 r1 ->
    degree_rexp_wrt_rtyp n1 (re_ConTyApp re1 r1).

Inductive degree_rexp_wrt_rexp : nat -> rexp -> Prop :=
  | degree_wrt_rexp_re_Var_f : forall n1 x1,
    degree_rexp_wrt_rexp n1 (re_Var_f x1)
  | degree_wrt_rexp_re_Var_b : forall n1 n2,
    lt n2 n1 ->
    degree_rexp_wrt_rexp n1 (re_Var_b n2)
  | degree_wrt_rexp_re_Lit : forall n1 x1,
    degree_rexp_wrt_rexp n1 (re_Lit x1)
  | degree_wrt_rexp_re_Abs : forall n1 rt1 re1,
    degree_rexp_wrt_rexp (S n1) re1 ->
    degree_rexp_wrt_rexp n1 (re_Abs rt1 re1)
  | degree_wrt_rexp_re_App : forall n1 re1 re2,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 re2 ->
    degree_rexp_wrt_rexp n1 (re_App re1 re2)
  | degree_wrt_rexp_re_Empty : forall n1,
    degree_rexp_wrt_rexp n1 (re_Empty)
  | degree_wrt_rexp_re_SingleField : forall n1 l1 re1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_SingleField l1 re1)
  | degree_wrt_rexp_re_Res : forall n1 re1 l1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_Res re1 l1)
  | degree_wrt_rexp_re_Merge : forall n1 re1 re2,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 re2 ->
    degree_rexp_wrt_rexp n1 (re_Merge re1 re2)
  | degree_wrt_rexp_re_Selection : forall n1 re1 l1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_Selection re1 l1)
  | degree_wrt_rexp_re_ConTyAbs : forall n1 R1 re1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_ConTyAbs R1 re1)
  | degree_wrt_rexp_re_ConTyApp : forall n1 re1 r1,
    degree_rexp_wrt_rexp n1 re1 ->
    degree_rexp_wrt_rexp n1 (re_ConTyApp re1 r1).

Scheme degree_rexp_wrt_rtyp_ind' := Induction for degree_rexp_wrt_rtyp Sort Prop.

Definition degree_rexp_wrt_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  degree_rexp_wrt_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme degree_rexp_wrt_rexp_ind' := Induction for degree_rexp_wrt_rexp Sort Prop.

Definition degree_rexp_wrt_rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  degree_rexp_wrt_rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Hint Constructors degree_rexp_wrt_rtyp : core lngen.

Hint Constructors degree_rexp_wrt_rexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_rlist : rlist -> Set :=
  | lc_set_R_Empty :
    lc_set_rlist (R_Empty)
  | lc_set_R_Cons : forall r1 R1,
    lc_set_rtyp r1 ->
    lc_set_rlist R1 ->
    lc_set_rlist (R_Cons r1 R1)

with lc_set_rt : rt -> Set :=
  | lc_set_rt_Base :
    lc_set_rt (rt_Base)
  | lc_set_rt_Fun : forall rt1 rt2,
    lc_set_rt rt1 ->
    lc_set_rt rt2 ->
    lc_set_rt (rt_Fun rt1 rt2)
  | lc_set_rt_ConQuan : forall R1 rt1,
    lc_set_rlist R1 ->
    (forall a1 : typvar, lc_set_rt (open_rt_wrt_rtyp rt1 (r_TyVar_f a1))) ->
    lc_set_rt (rt_ConQuan R1 rt1)
  | lc_set_rt_Record : forall r1,
    lc_set_rtyp r1 ->
    lc_set_rt (rt_Record r1)

with lc_set_rtyp : rtyp -> Set :=
  | lc_set_r_TyVar_f : forall a1,
    lc_set_rtyp (r_TyVar_f a1)
  | lc_set_r_Empty :
    lc_set_rtyp (r_Empty)
  | lc_set_r_SingleField : forall l1 rt1,
    lc_set_rt rt1 ->
    lc_set_rtyp (r_SingleField l1 rt1)
  | lc_set_r_Merge : forall r1 r2,
    lc_set_rtyp r1 ->
    lc_set_rtyp r2 ->
    lc_set_rtyp (r_Merge r1 r2).

Scheme lc_rlist_ind' := Induction for lc_rlist Sort Prop
  with lc_rt_ind' := Induction for lc_rt Sort Prop
  with lc_rtyp_ind' := Induction for lc_rtyp Sort Prop.

Definition lc_rlist_lc_rt_lc_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  (conj (lc_rlist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  ((conj (lc_rt_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  (lc_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)))).

Scheme lc_set_rlist_ind' := Induction for lc_set_rlist Sort Prop
  with lc_set_rt_ind' := Induction for lc_set_rt Sort Prop
  with lc_set_rtyp_ind' := Induction for lc_set_rtyp Sort Prop.

Definition lc_set_rlist_lc_set_rt_lc_set_rtyp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  (conj (lc_set_rlist_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  ((conj (lc_set_rt_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  (lc_set_rtyp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)))).

Scheme lc_set_rlist_rec' := Induction for lc_set_rlist Sort Set
  with lc_set_rt_rec' := Induction for lc_set_rt Sort Set
  with lc_set_rtyp_rec' := Induction for lc_set_rtyp Sort Set.

Definition lc_set_rlist_lc_set_rt_lc_set_rtyp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 =>
  (pair ((pair (lc_set_rlist_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
  (lc_set_rt_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)))
  (lc_set_rtyp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)).

Hint Constructors lc_rlist : core lngen.

Hint Constructors lc_rt : core lngen.

Hint Constructors lc_rtyp : core lngen.

Hint Constructors lc_set_rlist : core lngen.

Hint Constructors lc_set_rt : core lngen.

Hint Constructors lc_set_rtyp : core lngen.

Inductive lc_set_rexp : rexp -> Set :=
  | lc_set_re_Var_f : forall x1,
    lc_set_rexp (re_Var_f x1)
  | lc_set_re_Abs : forall rt1 re1,
    lc_set_rt rt1 ->
    (forall x1 : expvar, lc_set_rexp (open_rexp_wrt_rexp re1 (re_Var_f x1))) ->
    lc_set_rexp (re_Abs rt1 re1)
  | lc_set_re_Lit : forall x1,
    lc_set_rexp (re_Lit x1)
  | lc_set_re_App : forall re1 re2,
    lc_set_rexp re1 ->
    lc_set_rexp re2 ->
    lc_set_rexp (re_App re1 re2)
  | lc_set_re_Empty :
    lc_set_rexp (re_Empty)
  | lc_set_re_SingleField : forall l1 re1,
    lc_set_rexp re1 ->
    lc_set_rexp (re_SingleField l1 re1)
  | lc_set_re_Res : forall re1 l1,
    lc_set_rexp re1 ->
    lc_set_rexp (re_Res re1 l1)
  | lc_set_re_Merge : forall re1 re2,
    lc_set_rexp re1 ->
    lc_set_rexp re2 ->
    lc_set_rexp (re_Merge re1 re2)
  | lc_set_re_Selection : forall re1 l1,
    lc_set_rexp re1 ->
    lc_set_rexp (re_Selection re1 l1)
  | lc_set_re_ConTyAbs : forall R1 re1,
    lc_set_rlist R1 ->
    (forall a1 : typvar, lc_set_rexp (open_rexp_wrt_rtyp re1 (r_TyVar_f a1))) ->
    lc_set_rexp (re_ConTyAbs R1 re1)
  | lc_set_re_ConTyApp : forall re1 r1,
    lc_set_rexp re1 ->
    lc_set_rtyp r1 ->
    lc_set_rexp (re_ConTyApp re1 r1).

Scheme lc_rexp_ind' := Induction for lc_rexp Sort Prop.

Definition lc_rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_rexp_ind' := Induction for lc_set_rexp Sort Prop.

Definition lc_set_rexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_rexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_rexp_rec' := Induction for lc_set_rexp Sort Set.

Definition lc_set_rexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_rexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Hint Constructors lc_rexp : core lngen.

Hint Constructors lc_set_rexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_rlist_wrt_rtyp R1 := forall a1, lc_rlist (open_rlist_wrt_rtyp R1 (r_TyVar_f a1)).

Definition body_rt_wrt_rtyp u1 := forall a1, lc_rt (open_rt_wrt_rtyp u1 (r_TyVar_f a1)).

Definition body_rtyp_wrt_rtyp r1 := forall a1, lc_rtyp (open_rtyp_wrt_rtyp r1 (r_TyVar_f a1)).

Hint Unfold body_rlist_wrt_rtyp.

Hint Unfold body_rt_wrt_rtyp.

Hint Unfold body_rtyp_wrt_rtyp.

Definition body_rexp_wrt_rtyp re1 := forall a1, lc_rexp (open_rexp_wrt_rtyp re1 (r_TyVar_f a1)).

Definition body_rexp_wrt_rexp re1 := forall x1, lc_rexp (open_rexp_wrt_rexp re1 (re_Var_f x1)).

Hint Unfold body_rexp_wrt_rtyp.

Hint Unfold body_rexp_wrt_rexp.


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

Lemma size_rlist_min_size_rt_min_size_rtyp_min_mutual :
(forall R1, 1 <= size_rlist R1) /\
(forall u1, 1 <= size_rt u1) /\
(forall r1, 1 <= size_rtyp r1).
Proof.
  apply rlist_rt_rtyp_mutind; default_simp.
Qed.

(* end hide *)

Lemma size_rlist_min :
forall R1, 1 <= size_rlist R1.
Proof.
pose proof size_rlist_min_size_rt_min_size_rtyp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rlist_min : lngen.

Lemma size_rt_min :
forall u1, 1 <= size_rt u1.
Proof.
pose proof size_rlist_min_size_rt_min_size_rtyp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rt_min : lngen.

Lemma size_rtyp_min :
forall r1, 1 <= size_rtyp r1.
Proof.
pose proof size_rlist_min_size_rt_min_size_rtyp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rtyp_min : lngen.

(* begin hide *)

Lemma size_rexp_min_mutual :
(forall re1, 1 <= size_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_rexp_min :
forall re1, 1 <= size_rexp re1.
Proof.
pose proof size_rexp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_min : lngen.

(* begin hide *)

Lemma size_rlist_close_rlist_wrt_rtyp_rec_size_rt_close_rt_wrt_rtyp_rec_size_rtyp_close_rtyp_wrt_rtyp_rec_mutual :
(forall R1 a1 n1,
  size_rlist (close_rlist_wrt_rtyp_rec n1 a1 R1) = size_rlist R1) /\
(forall u1 a1 n1,
  size_rt (close_rt_wrt_rtyp_rec n1 a1 u1) = size_rt u1) /\
(forall r1 a1 n1,
  size_rtyp (close_rtyp_wrt_rtyp_rec n1 a1 r1) = size_rtyp r1).
Proof.
apply rlist_rt_rtyp_mutind; default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rlist_close_rlist_wrt_rtyp_rec :
forall R1 a1 n1,
  size_rlist (close_rlist_wrt_rtyp_rec n1 a1 R1) = size_rlist R1.
Proof.
pose proof size_rlist_close_rlist_wrt_rtyp_rec_size_rt_close_rt_wrt_rtyp_rec_size_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rlist_close_rlist_wrt_rtyp_rec : lngen.
Hint Rewrite size_rlist_close_rlist_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rt_close_rt_wrt_rtyp_rec :
forall u1 a1 n1,
  size_rt (close_rt_wrt_rtyp_rec n1 a1 u1) = size_rt u1.
Proof.
pose proof size_rlist_close_rlist_wrt_rtyp_rec_size_rt_close_rt_wrt_rtyp_rec_size_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rt_close_rt_wrt_rtyp_rec : lngen.
Hint Rewrite size_rt_close_rt_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rtyp_close_rtyp_wrt_rtyp_rec :
forall r1 a1 n1,
  size_rtyp (close_rtyp_wrt_rtyp_rec n1 a1 r1) = size_rtyp r1.
Proof.
pose proof size_rlist_close_rlist_wrt_rtyp_rec_size_rt_close_rt_wrt_rtyp_rec_size_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rtyp_close_rtyp_wrt_rtyp_rec : lngen.
Hint Rewrite size_rtyp_close_rtyp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rexp_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1,
  size_rexp (close_rexp_wrt_rtyp_rec n1 a1 re1) = size_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rexp_close_rexp_wrt_rtyp_rec :
forall re1 a1 n1,
  size_rexp (close_rexp_wrt_rtyp_rec n1 a1 re1) = size_rexp re1.
Proof.
pose proof size_rexp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_close_rexp_wrt_rtyp_rec : lngen.
Hint Rewrite size_rexp_close_rexp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rexp_close_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1,
  size_rexp (close_rexp_wrt_rexp_rec n1 x1 re1) = size_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rexp_close_rexp_wrt_rexp_rec :
forall re1 x1 n1,
  size_rexp (close_rexp_wrt_rexp_rec n1 x1 re1) = size_rexp re1.
Proof.
pose proof size_rexp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_close_rexp_wrt_rexp_rec : lngen.
Hint Rewrite size_rexp_close_rexp_wrt_rexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_rlist_close_rlist_wrt_rtyp :
forall R1 a1,
  size_rlist (close_rlist_wrt_rtyp a1 R1) = size_rlist R1.
Proof.
unfold close_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rlist_close_rlist_wrt_rtyp : lngen.
Hint Rewrite size_rlist_close_rlist_wrt_rtyp using solve [auto] : lngen.

Lemma size_rt_close_rt_wrt_rtyp :
forall u1 a1,
  size_rt (close_rt_wrt_rtyp a1 u1) = size_rt u1.
Proof.
unfold close_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rt_close_rt_wrt_rtyp : lngen.
Hint Rewrite size_rt_close_rt_wrt_rtyp using solve [auto] : lngen.

Lemma size_rtyp_close_rtyp_wrt_rtyp :
forall r1 a1,
  size_rtyp (close_rtyp_wrt_rtyp a1 r1) = size_rtyp r1.
Proof.
unfold close_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rtyp_close_rtyp_wrt_rtyp : lngen.
Hint Rewrite size_rtyp_close_rtyp_wrt_rtyp using solve [auto] : lngen.

Lemma size_rexp_close_rexp_wrt_rtyp :
forall re1 a1,
  size_rexp (close_rexp_wrt_rtyp a1 re1) = size_rexp re1.
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rexp_close_rexp_wrt_rtyp : lngen.
Hint Rewrite size_rexp_close_rexp_wrt_rtyp using solve [auto] : lngen.

Lemma size_rexp_close_rexp_wrt_rexp :
forall re1 x1,
  size_rexp (close_rexp_wrt_rexp x1 re1) = size_rexp re1.
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve size_rexp_close_rexp_wrt_rexp : lngen.
Hint Rewrite size_rexp_close_rexp_wrt_rexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_rlist_open_rlist_wrt_rtyp_rec_size_rt_open_rt_wrt_rtyp_rec_size_rtyp_open_rtyp_wrt_rtyp_rec_mutual :
(forall R1 r1 n1,
  size_rlist R1 <= size_rlist (open_rlist_wrt_rtyp_rec n1 r1 R1)) /\
(forall u1 r1 n1,
  size_rt u1 <= size_rt (open_rt_wrt_rtyp_rec n1 r1 u1)) /\
(forall r1 r2 n1,
  size_rtyp r1 <= size_rtyp (open_rtyp_wrt_rtyp_rec n1 r2 r1)).
Proof.
apply rlist_rt_rtyp_mutind; default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rlist_open_rlist_wrt_rtyp_rec :
forall R1 r1 n1,
  size_rlist R1 <= size_rlist (open_rlist_wrt_rtyp_rec n1 r1 R1).
Proof.
pose proof size_rlist_open_rlist_wrt_rtyp_rec_size_rt_open_rt_wrt_rtyp_rec_size_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rlist_open_rlist_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rt_open_rt_wrt_rtyp_rec :
forall u1 r1 n1,
  size_rt u1 <= size_rt (open_rt_wrt_rtyp_rec n1 r1 u1).
Proof.
pose proof size_rlist_open_rlist_wrt_rtyp_rec_size_rt_open_rt_wrt_rtyp_rec_size_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rt_open_rt_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rtyp_open_rtyp_wrt_rtyp_rec :
forall r1 r2 n1,
  size_rtyp r1 <= size_rtyp (open_rtyp_wrt_rtyp_rec n1 r2 r1).
Proof.
pose proof size_rlist_open_rlist_wrt_rtyp_rec_size_rt_open_rt_wrt_rtyp_rec_size_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rtyp_open_rtyp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rtyp_rec_mutual :
(forall re1 r1 n1,
  size_rexp re1 <= size_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rtyp_rec :
forall re1 r1 n1,
  size_rexp re1 <= size_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1).
Proof.
pose proof size_rexp_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rexp_rec_mutual :
(forall re1 re2 n1,
  size_rexp re1 <= size_rexp (open_rexp_wrt_rexp_rec n1 re2 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rexp_rec :
forall re1 re2 n1,
  size_rexp re1 <= size_rexp (open_rexp_wrt_rexp_rec n1 re2 re1).
Proof.
pose proof size_rexp_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

Lemma size_rlist_open_rlist_wrt_rtyp :
forall R1 r1,
  size_rlist R1 <= size_rlist (open_rlist_wrt_rtyp R1 r1).
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rlist_open_rlist_wrt_rtyp : lngen.

Lemma size_rt_open_rt_wrt_rtyp :
forall u1 r1,
  size_rt u1 <= size_rt (open_rt_wrt_rtyp u1 r1).
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rt_open_rt_wrt_rtyp : lngen.

Lemma size_rtyp_open_rtyp_wrt_rtyp :
forall r1 r2,
  size_rtyp r1 <= size_rtyp (open_rtyp_wrt_rtyp r1 r2).
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rtyp_open_rtyp_wrt_rtyp : lngen.

Lemma size_rexp_open_rexp_wrt_rtyp :
forall re1 r1,
  size_rexp re1 <= size_rexp (open_rexp_wrt_rtyp re1 r1).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rtyp : lngen.

Lemma size_rexp_open_rexp_wrt_rexp :
forall re1 re2,
  size_rexp re1 <= size_rexp (open_rexp_wrt_rexp re1 re2).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rexp : lngen.

(* begin hide *)

Lemma size_rlist_open_rlist_wrt_rtyp_rec_var_size_rt_open_rt_wrt_rtyp_rec_var_size_rtyp_open_rtyp_wrt_rtyp_rec_var_mutual :
(forall R1 a1 n1,
  size_rlist (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1) = size_rlist R1) /\
(forall u1 a1 n1,
  size_rt (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1) = size_rt u1) /\
(forall r1 a1 n1,
  size_rtyp (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1) = size_rtyp r1).
Proof.
apply rlist_rt_rtyp_mutind; default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rlist_open_rlist_wrt_rtyp_rec_var :
forall R1 a1 n1,
  size_rlist (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1) = size_rlist R1.
Proof.
pose proof size_rlist_open_rlist_wrt_rtyp_rec_var_size_rt_open_rt_wrt_rtyp_rec_var_size_rtyp_open_rtyp_wrt_rtyp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rlist_open_rlist_wrt_rtyp_rec_var : lngen.
Hint Rewrite size_rlist_open_rlist_wrt_rtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rt_open_rt_wrt_rtyp_rec_var :
forall u1 a1 n1,
  size_rt (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1) = size_rt u1.
Proof.
pose proof size_rlist_open_rlist_wrt_rtyp_rec_var_size_rt_open_rt_wrt_rtyp_rec_var_size_rtyp_open_rtyp_wrt_rtyp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rt_open_rt_wrt_rtyp_rec_var : lngen.
Hint Rewrite size_rt_open_rt_wrt_rtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rtyp_open_rtyp_wrt_rtyp_rec_var :
forall r1 a1 n1,
  size_rtyp (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1) = size_rtyp r1.
Proof.
pose proof size_rlist_open_rlist_wrt_rtyp_rec_var_size_rt_open_rt_wrt_rtyp_rec_var_size_rtyp_open_rtyp_wrt_rtyp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rtyp_open_rtyp_wrt_rtyp_rec_var : lngen.
Hint Rewrite size_rtyp_open_rtyp_wrt_rtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rtyp_rec_var_mutual :
(forall re1 a1 n1,
  size_rexp (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1) = size_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rtyp_rec_var :
forall re1 a1 n1,
  size_rexp (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1) = size_rexp re1.
Proof.
pose proof size_rexp_open_rexp_wrt_rtyp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rtyp_rec_var : lngen.
Hint Rewrite size_rexp_open_rexp_wrt_rtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rexp_rec_var_mutual :
(forall re1 x1 n1,
  size_rexp (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1) = size_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_rexp_open_rexp_wrt_rexp_rec_var :
forall re1 x1 n1,
  size_rexp (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1) = size_rexp re1.
Proof.
pose proof size_rexp_open_rexp_wrt_rexp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rexp_rec_var : lngen.
Hint Rewrite size_rexp_open_rexp_wrt_rexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_rlist_open_rlist_wrt_rtyp_var :
forall R1 a1,
  size_rlist (open_rlist_wrt_rtyp R1 (r_TyVar_f a1)) = size_rlist R1.
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rlist_open_rlist_wrt_rtyp_var : lngen.
Hint Rewrite size_rlist_open_rlist_wrt_rtyp_var using solve [auto] : lngen.

Lemma size_rt_open_rt_wrt_rtyp_var :
forall u1 a1,
  size_rt (open_rt_wrt_rtyp u1 (r_TyVar_f a1)) = size_rt u1.
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rt_open_rt_wrt_rtyp_var : lngen.
Hint Rewrite size_rt_open_rt_wrt_rtyp_var using solve [auto] : lngen.

Lemma size_rtyp_open_rtyp_wrt_rtyp_var :
forall r1 a1,
  size_rtyp (open_rtyp_wrt_rtyp r1 (r_TyVar_f a1)) = size_rtyp r1.
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rtyp_open_rtyp_wrt_rtyp_var : lngen.
Hint Rewrite size_rtyp_open_rtyp_wrt_rtyp_var using solve [auto] : lngen.

Lemma size_rexp_open_rexp_wrt_rtyp_var :
forall re1 a1,
  size_rexp (open_rexp_wrt_rtyp re1 (r_TyVar_f a1)) = size_rexp re1.
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rtyp_var : lngen.
Hint Rewrite size_rexp_open_rexp_wrt_rtyp_var using solve [auto] : lngen.

Lemma size_rexp_open_rexp_wrt_rexp_var :
forall re1 x1,
  size_rexp (open_rexp_wrt_rexp re1 (re_Var_f x1)) = size_rexp re1.
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve size_rexp_open_rexp_wrt_rexp_var : lngen.
Hint Rewrite size_rexp_open_rexp_wrt_rexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_S_degree_rt_wrt_rtyp_S_degree_rtyp_wrt_rtyp_S_mutual :
(forall n1 R1,
  degree_rlist_wrt_rtyp n1 R1 ->
  degree_rlist_wrt_rtyp (S n1) R1) /\
(forall n1 u1,
  degree_rt_wrt_rtyp n1 u1 ->
  degree_rt_wrt_rtyp (S n1) u1) /\
(forall n1 r1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rtyp_wrt_rtyp (S n1) r1).
Proof.
apply degree_rlist_wrt_rtyp_degree_rt_wrt_rtyp_degree_rtyp_wrt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_rlist_wrt_rtyp_S :
forall n1 R1,
  degree_rlist_wrt_rtyp n1 R1 ->
  degree_rlist_wrt_rtyp (S n1) R1.
Proof.
pose proof degree_rlist_wrt_rtyp_S_degree_rt_wrt_rtyp_S_degree_rtyp_wrt_rtyp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_S : lngen.

Lemma degree_rt_wrt_rtyp_S :
forall n1 u1,
  degree_rt_wrt_rtyp n1 u1 ->
  degree_rt_wrt_rtyp (S n1) u1.
Proof.
pose proof degree_rlist_wrt_rtyp_S_degree_rt_wrt_rtyp_S_degree_rtyp_wrt_rtyp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rt_wrt_rtyp_S : lngen.

Lemma degree_rtyp_wrt_rtyp_S :
forall n1 r1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rtyp_wrt_rtyp (S n1) r1.
Proof.
pose proof degree_rlist_wrt_rtyp_S_degree_rt_wrt_rtyp_S_degree_rtyp_wrt_rtyp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_S : lngen.

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_S_mutual :
(forall n1 re1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp (S n1) re1).
Proof.
apply_mutual_ind degree_rexp_wrt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_rexp_wrt_rtyp_S :
forall n1 re1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp (S n1) re1.
Proof.
pose proof degree_rexp_wrt_rtyp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_S : lngen.

(* begin hide *)

Lemma degree_rexp_wrt_rexp_S_mutual :
(forall n1 re1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp (S n1) re1).
Proof.
apply_mutual_ind degree_rexp_wrt_rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_rexp_wrt_rexp_S :
forall n1 re1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp (S n1) re1.
Proof.
pose proof degree_rexp_wrt_rexp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rexp_S : lngen.

Lemma degree_rlist_wrt_rtyp_O :
forall n1 R1,
  degree_rlist_wrt_rtyp O R1 ->
  degree_rlist_wrt_rtyp n1 R1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_O : lngen.

Lemma degree_rt_wrt_rtyp_O :
forall n1 u1,
  degree_rt_wrt_rtyp O u1 ->
  degree_rt_wrt_rtyp n1 u1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_rt_wrt_rtyp_O : lngen.

Lemma degree_rtyp_wrt_rtyp_O :
forall n1 r1,
  degree_rtyp_wrt_rtyp O r1 ->
  degree_rtyp_wrt_rtyp n1 r1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_O : lngen.

Lemma degree_rexp_wrt_rtyp_O :
forall n1 re1,
  degree_rexp_wrt_rtyp O re1 ->
  degree_rexp_wrt_rtyp n1 re1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_O : lngen.

Lemma degree_rexp_wrt_rexp_O :
forall n1 re1,
  degree_rexp_wrt_rexp O re1 ->
  degree_rexp_wrt_rexp n1 re1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rexp_O : lngen.

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_mutual :
(forall R1 a1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  degree_rlist_wrt_rtyp (S n1) (close_rlist_wrt_rtyp_rec n1 a1 R1)) /\
(forall u1 a1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  degree_rt_wrt_rtyp (S n1) (close_rt_wrt_rtyp_rec n1 a1 u1)) /\
(forall r1 a1 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rtyp_wrt_rtyp (S n1) (close_rtyp_wrt_rtyp_rec n1 a1 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec :
forall R1 a1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  degree_rlist_wrt_rtyp (S n1) (close_rlist_wrt_rtyp_rec n1 a1 R1).
Proof.
pose proof degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec :
forall u1 a1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  degree_rt_wrt_rtyp (S n1) (close_rt_wrt_rtyp_rec n1 a1 u1).
Proof.
pose proof degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec :
forall r1 a1 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rtyp_wrt_rtyp (S n1) (close_rtyp_wrt_rtyp_rec n1 a1 r1).
Proof.
pose proof degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp (S n1) (close_rexp_wrt_rtyp_rec n1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec :
forall re1 a1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp (S n1) (close_rexp_wrt_rtyp_rec n1 a1 re1).
Proof.
pose proof degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1 n2,
  degree_rexp_wrt_rtyp n2 re1 ->
  degree_rexp_wrt_rtyp n2 (close_rexp_wrt_rexp_rec n1 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec :
forall re1 x1 n1 n2,
  degree_rexp_wrt_rtyp n2 re1 ->
  degree_rexp_wrt_rtyp n2 (close_rexp_wrt_rexp_rec n1 x1 re1).
Proof.
pose proof degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1 n2,
  degree_rexp_wrt_rexp n2 re1 ->
  degree_rexp_wrt_rexp n2 (close_rexp_wrt_rtyp_rec n1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec :
forall re1 a1 n1 n2,
  degree_rexp_wrt_rexp n2 re1 ->
  degree_rexp_wrt_rexp n2 (close_rexp_wrt_rtyp_rec n1 a1 re1).
Proof.
pose proof degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp (S n1) (close_rexp_wrt_rexp_rec n1 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec :
forall re1 x1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp (S n1) (close_rexp_wrt_rexp_rec n1 x1 re1).
Proof.
pose proof degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec : lngen.

(* end hide *)

Lemma degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp :
forall R1 a1,
  degree_rlist_wrt_rtyp 0 R1 ->
  degree_rlist_wrt_rtyp 1 (close_rlist_wrt_rtyp a1 R1).
Proof.
unfold close_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp : lngen.

Lemma degree_rt_wrt_rtyp_close_rt_wrt_rtyp :
forall u1 a1,
  degree_rt_wrt_rtyp 0 u1 ->
  degree_rt_wrt_rtyp 1 (close_rt_wrt_rtyp a1 u1).
Proof.
unfold close_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rt_wrt_rtyp_close_rt_wrt_rtyp : lngen.

Lemma degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp :
forall r1 a1,
  degree_rtyp_wrt_rtyp 0 r1 ->
  degree_rtyp_wrt_rtyp 1 (close_rtyp_wrt_rtyp a1 r1).
Proof.
unfold close_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp : lngen.

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp :
forall re1 a1,
  degree_rexp_wrt_rtyp 0 re1 ->
  degree_rexp_wrt_rtyp 1 (close_rexp_wrt_rtyp a1 re1).
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp : lngen.

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rexp :
forall re1 x1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp n1 (close_rexp_wrt_rexp x1 re1).
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_close_rexp_wrt_rexp : lngen.

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rtyp :
forall re1 a1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 (close_rexp_wrt_rtyp a1 re1).
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rexp_close_rexp_wrt_rtyp : lngen.

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rexp :
forall re1 x1,
  degree_rexp_wrt_rexp 0 re1 ->
  degree_rexp_wrt_rexp 1 (close_rexp_wrt_rexp x1 re1).
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rexp_close_rexp_wrt_rexp : lngen.

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_inv_mutual :
(forall R1 a1 n1,
  degree_rlist_wrt_rtyp (S n1) (close_rlist_wrt_rtyp_rec n1 a1 R1) ->
  degree_rlist_wrt_rtyp n1 R1) /\
(forall u1 a1 n1,
  degree_rt_wrt_rtyp (S n1) (close_rt_wrt_rtyp_rec n1 a1 u1) ->
  degree_rt_wrt_rtyp n1 u1) /\
(forall r1 a1 n1,
  degree_rtyp_wrt_rtyp (S n1) (close_rtyp_wrt_rtyp_rec n1 a1 r1) ->
  degree_rtyp_wrt_rtyp n1 r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_inv :
forall R1 a1 n1,
  degree_rlist_wrt_rtyp (S n1) (close_rlist_wrt_rtyp_rec n1 a1 R1) ->
  degree_rlist_wrt_rtyp n1 R1.
Proof.
pose proof degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_inv :
forall u1 a1 n1,
  degree_rt_wrt_rtyp (S n1) (close_rt_wrt_rtyp_rec n1 a1 u1) ->
  degree_rt_wrt_rtyp n1 u1.
Proof.
pose proof degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_inv :
forall r1 a1 n1,
  degree_rtyp_wrt_rtyp (S n1) (close_rtyp_wrt_rtyp_rec n1 a1 r1) ->
  degree_rtyp_wrt_rtyp n1 r1.
Proof.
pose proof degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_close_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec_inv_mutual :
(forall re1 a1 n1,
  degree_rexp_wrt_rtyp (S n1) (close_rexp_wrt_rtyp_rec n1 a1 re1) ->
  degree_rexp_wrt_rtyp n1 re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec_inv :
forall re1 a1 n1,
  degree_rexp_wrt_rtyp (S n1) (close_rexp_wrt_rtyp_rec n1 a1 re1) ->
  degree_rexp_wrt_rtyp n1 re1.
Proof.
pose proof degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec_inv_mutual :
(forall re1 x1 n1 n2,
  degree_rexp_wrt_rtyp n2 (close_rexp_wrt_rexp_rec n1 x1 re1) ->
  degree_rexp_wrt_rtyp n2 re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec_inv :
forall re1 x1 n1 n2,
  degree_rexp_wrt_rtyp n2 (close_rexp_wrt_rexp_rec n1 x1 re1) ->
  degree_rexp_wrt_rtyp n2 re1.
Proof.
pose proof degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec_inv_mutual :
(forall re1 a1 n1 n2,
  degree_rexp_wrt_rexp n2 (close_rexp_wrt_rtyp_rec n1 a1 re1) ->
  degree_rexp_wrt_rexp n2 re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec_inv :
forall re1 a1 n1 n2,
  degree_rexp_wrt_rexp n2 (close_rexp_wrt_rtyp_rec n1 a1 re1) ->
  degree_rexp_wrt_rexp n2 re1.
Proof.
pose proof degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec_inv_mutual :
(forall re1 x1 n1,
  degree_rexp_wrt_rexp (S n1) (close_rexp_wrt_rexp_rec n1 x1 re1) ->
  degree_rexp_wrt_rexp n1 re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec_inv :
forall re1 x1 n1,
  degree_rexp_wrt_rexp (S n1) (close_rexp_wrt_rexp_rec n1 x1 re1) ->
  degree_rexp_wrt_rexp n1 re1.
Proof.
pose proof degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rexp_close_rexp_wrt_rexp_rec_inv : lngen.

(* end hide *)

Lemma degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_inv :
forall R1 a1,
  degree_rlist_wrt_rtyp 1 (close_rlist_wrt_rtyp a1 R1) ->
  degree_rlist_wrt_rtyp 0 R1.
Proof.
unfold close_rlist_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rlist_wrt_rtyp_close_rlist_wrt_rtyp_inv : lngen.

Lemma degree_rt_wrt_rtyp_close_rt_wrt_rtyp_inv :
forall u1 a1,
  degree_rt_wrt_rtyp 1 (close_rt_wrt_rtyp a1 u1) ->
  degree_rt_wrt_rtyp 0 u1.
Proof.
unfold close_rt_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rt_wrt_rtyp_close_rt_wrt_rtyp_inv : lngen.

Lemma degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_inv :
forall r1 a1,
  degree_rtyp_wrt_rtyp 1 (close_rtyp_wrt_rtyp a1 r1) ->
  degree_rtyp_wrt_rtyp 0 r1.
Proof.
unfold close_rtyp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp_inv : lngen.

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_inv :
forall re1 a1,
  degree_rexp_wrt_rtyp 1 (close_rexp_wrt_rtyp a1 re1) ->
  degree_rexp_wrt_rtyp 0 re1.
Proof.
unfold close_rexp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_close_rexp_wrt_rtyp_inv : lngen.

Lemma degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_inv :
forall re1 x1 n1,
  degree_rexp_wrt_rtyp n1 (close_rexp_wrt_rexp x1 re1) ->
  degree_rexp_wrt_rtyp n1 re1.
Proof.
unfold close_rexp_wrt_rexp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_close_rexp_wrt_rexp_inv : lngen.

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_inv :
forall re1 a1 n1,
  degree_rexp_wrt_rexp n1 (close_rexp_wrt_rtyp a1 re1) ->
  degree_rexp_wrt_rexp n1 re1.
Proof.
unfold close_rexp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rexp_close_rexp_wrt_rtyp_inv : lngen.

Lemma degree_rexp_wrt_rexp_close_rexp_wrt_rexp_inv :
forall re1 x1,
  degree_rexp_wrt_rexp 1 (close_rexp_wrt_rexp x1 re1) ->
  degree_rexp_wrt_rexp 0 re1.
Proof.
unfold close_rexp_wrt_rexp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rexp_close_rexp_wrt_rexp_inv : lngen.

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_mutual :
(forall R1 r1 n1,
  degree_rlist_wrt_rtyp (S n1) R1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rlist_wrt_rtyp n1 (open_rlist_wrt_rtyp_rec n1 r1 R1)) /\
(forall u1 r1 n1,
  degree_rt_wrt_rtyp (S n1) u1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rt_wrt_rtyp n1 (open_rt_wrt_rtyp_rec n1 r1 u1)) /\
(forall r1 r2 n1,
  degree_rtyp_wrt_rtyp (S n1) r1 ->
  degree_rtyp_wrt_rtyp n1 r2 ->
  degree_rtyp_wrt_rtyp n1 (open_rtyp_wrt_rtyp_rec n1 r2 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec :
forall R1 r1 n1,
  degree_rlist_wrt_rtyp (S n1) R1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rlist_wrt_rtyp n1 (open_rlist_wrt_rtyp_rec n1 r1 R1).
Proof.
pose proof degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec :
forall u1 r1 n1,
  degree_rt_wrt_rtyp (S n1) u1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rt_wrt_rtyp n1 (open_rt_wrt_rtyp_rec n1 r1 u1).
Proof.
pose proof degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec :
forall r1 r2 n1,
  degree_rtyp_wrt_rtyp (S n1) r1 ->
  degree_rtyp_wrt_rtyp n1 r2 ->
  degree_rtyp_wrt_rtyp n1 (open_rtyp_wrt_rtyp_rec n1 r2 r1).
Proof.
pose proof degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec_mutual :
(forall re1 r1 n1,
  degree_rexp_wrt_rtyp (S n1) re1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rtyp_rec n1 r1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec :
forall re1 r1 n1,
  degree_rexp_wrt_rtyp (S n1) re1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rtyp_rec n1 r1 re1).
Proof.
pose proof degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec_mutual :
(forall re1 re2 n1 n2,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp n1 re2 ->
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rexp_rec n2 re2 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec :
forall re1 re2 n1 n2,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp n1 re2 ->
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rexp_rec n2 re2 re1).
Proof.
pose proof degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec_mutual :
(forall re1 r1 n1 n2,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rtyp_rec n2 r1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec :
forall re1 r1 n1 n2,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rtyp_rec n2 r1 re1).
Proof.
pose proof degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec_mutual :
(forall re1 re2 n1,
  degree_rexp_wrt_rexp (S n1) re1 ->
  degree_rexp_wrt_rexp n1 re2 ->
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rexp_rec n1 re2 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec :
forall re1 re2 n1,
  degree_rexp_wrt_rexp (S n1) re1 ->
  degree_rexp_wrt_rexp n1 re2 ->
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rexp_rec n1 re2 re1).
Proof.
pose proof degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

Lemma degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp :
forall R1 r1,
  degree_rlist_wrt_rtyp 1 R1 ->
  degree_rtyp_wrt_rtyp 0 r1 ->
  degree_rlist_wrt_rtyp 0 (open_rlist_wrt_rtyp R1 r1).
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp : lngen.

Lemma degree_rt_wrt_rtyp_open_rt_wrt_rtyp :
forall u1 r1,
  degree_rt_wrt_rtyp 1 u1 ->
  degree_rtyp_wrt_rtyp 0 r1 ->
  degree_rt_wrt_rtyp 0 (open_rt_wrt_rtyp u1 r1).
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rt_wrt_rtyp_open_rt_wrt_rtyp : lngen.

Lemma degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp :
forall r1 r2,
  degree_rtyp_wrt_rtyp 1 r1 ->
  degree_rtyp_wrt_rtyp 0 r2 ->
  degree_rtyp_wrt_rtyp 0 (open_rtyp_wrt_rtyp r1 r2).
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp : lngen.

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp :
forall re1 r1,
  degree_rexp_wrt_rtyp 1 re1 ->
  degree_rtyp_wrt_rtyp 0 r1 ->
  degree_rexp_wrt_rtyp 0 (open_rexp_wrt_rtyp re1 r1).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp : lngen.

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rexp :
forall re1 re2 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp n1 re2 ->
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rexp re1 re2).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_open_rexp_wrt_rexp : lngen.

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rtyp :
forall re1 r1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rtyp re1 r1).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rexp_open_rexp_wrt_rtyp : lngen.

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rexp :
forall re1 re2,
  degree_rexp_wrt_rexp 1 re1 ->
  degree_rexp_wrt_rexp 0 re2 ->
  degree_rexp_wrt_rexp 0 (open_rexp_wrt_rexp re1 re2).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve degree_rexp_wrt_rexp_open_rexp_wrt_rexp : lngen.

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_inv_mutual :
(forall R1 r1 n1,
  degree_rlist_wrt_rtyp n1 (open_rlist_wrt_rtyp_rec n1 r1 R1) ->
  degree_rlist_wrt_rtyp (S n1) R1) /\
(forall u1 r1 n1,
  degree_rt_wrt_rtyp n1 (open_rt_wrt_rtyp_rec n1 r1 u1) ->
  degree_rt_wrt_rtyp (S n1) u1) /\
(forall r1 r2 n1,
  degree_rtyp_wrt_rtyp n1 (open_rtyp_wrt_rtyp_rec n1 r2 r1) ->
  degree_rtyp_wrt_rtyp (S n1) r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_inv :
forall R1 r1 n1,
  degree_rlist_wrt_rtyp n1 (open_rlist_wrt_rtyp_rec n1 r1 R1) ->
  degree_rlist_wrt_rtyp (S n1) R1.
Proof.
pose proof degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_inv :
forall u1 r1 n1,
  degree_rt_wrt_rtyp n1 (open_rt_wrt_rtyp_rec n1 r1 u1) ->
  degree_rt_wrt_rtyp (S n1) u1.
Proof.
pose proof degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_inv :
forall r1 r2 n1,
  degree_rtyp_wrt_rtyp n1 (open_rtyp_wrt_rtyp_rec n1 r2 r1) ->
  degree_rtyp_wrt_rtyp (S n1) r1.
Proof.
pose proof degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_rec_inv_degree_rt_wrt_rtyp_open_rt_wrt_rtyp_rec_inv_degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec_inv_mutual :
(forall re1 r1 n1,
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rtyp_rec n1 r1 re1) ->
  degree_rexp_wrt_rtyp (S n1) re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec_inv :
forall re1 r1 n1,
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rtyp_rec n1 r1 re1) ->
  degree_rexp_wrt_rtyp (S n1) re1.
Proof.
pose proof degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec_inv_mutual :
(forall re1 re2 n1 n2,
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rexp_rec n2 re2 re1) ->
  degree_rexp_wrt_rtyp n1 re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec_inv :
forall re1 re2 n1 n2,
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rexp_rec n2 re2 re1) ->
  degree_rexp_wrt_rtyp n1 re1.
Proof.
pose proof degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec_inv_mutual :
(forall re1 r1 n1 n2,
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rtyp_rec n2 r1 re1) ->
  degree_rexp_wrt_rexp n1 re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec_inv :
forall re1 r1 n1 n2,
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rtyp_rec n2 r1 re1) ->
  degree_rexp_wrt_rexp n1 re1.
Proof.
pose proof degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec_inv_mutual :
(forall re1 re2 n1,
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rexp_rec n1 re2 re1) ->
  degree_rexp_wrt_rexp (S n1) re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec_inv :
forall re1 re2 n1,
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rexp_rec n1 re2 re1) ->
  degree_rexp_wrt_rexp (S n1) re1.
Proof.
pose proof degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_rexp_wrt_rexp_open_rexp_wrt_rexp_rec_inv : lngen.

(* end hide *)

Lemma degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_inv :
forall R1 r1,
  degree_rlist_wrt_rtyp 0 (open_rlist_wrt_rtyp R1 r1) ->
  degree_rlist_wrt_rtyp 1 R1.
Proof.
unfold open_rlist_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rlist_wrt_rtyp_open_rlist_wrt_rtyp_inv : lngen.

Lemma degree_rt_wrt_rtyp_open_rt_wrt_rtyp_inv :
forall u1 r1,
  degree_rt_wrt_rtyp 0 (open_rt_wrt_rtyp u1 r1) ->
  degree_rt_wrt_rtyp 1 u1.
Proof.
unfold open_rt_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rt_wrt_rtyp_open_rt_wrt_rtyp_inv : lngen.

Lemma degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_inv :
forall r1 r2,
  degree_rtyp_wrt_rtyp 0 (open_rtyp_wrt_rtyp r1 r2) ->
  degree_rtyp_wrt_rtyp 1 r1.
Proof.
unfold open_rtyp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp_inv : lngen.

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_inv :
forall re1 r1,
  degree_rexp_wrt_rtyp 0 (open_rexp_wrt_rtyp re1 r1) ->
  degree_rexp_wrt_rtyp 1 re1.
Proof.
unfold open_rexp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_open_rexp_wrt_rtyp_inv : lngen.

Lemma degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_inv :
forall re1 re2 n1,
  degree_rexp_wrt_rtyp n1 (open_rexp_wrt_rexp re1 re2) ->
  degree_rexp_wrt_rtyp n1 re1.
Proof.
unfold open_rexp_wrt_rexp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rtyp_open_rexp_wrt_rexp_inv : lngen.

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_inv :
forall re1 r1 n1,
  degree_rexp_wrt_rexp n1 (open_rexp_wrt_rtyp re1 r1) ->
  degree_rexp_wrt_rexp n1 re1.
Proof.
unfold open_rexp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rexp_open_rexp_wrt_rtyp_inv : lngen.

Lemma degree_rexp_wrt_rexp_open_rexp_wrt_rexp_inv :
forall re1 re2,
  degree_rexp_wrt_rexp 0 (open_rexp_wrt_rexp re1 re2) ->
  degree_rexp_wrt_rexp 1 re1.
Proof.
unfold open_rexp_wrt_rexp; eauto with lngen.
Qed.

Hint Immediate degree_rexp_wrt_rexp_open_rexp_wrt_rexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_rlist_wrt_rtyp_rec_inj_close_rt_wrt_rtyp_rec_inj_close_rtyp_wrt_rtyp_rec_inj_mutual :
(forall R1 R2 a1 n1,
  close_rlist_wrt_rtyp_rec n1 a1 R1 = close_rlist_wrt_rtyp_rec n1 a1 R2 ->
  R1 = R2) /\
(forall u1 u2 a1 n1,
  close_rt_wrt_rtyp_rec n1 a1 u1 = close_rt_wrt_rtyp_rec n1 a1 u2 ->
  u1 = u2) /\
(forall r1 r2 a1 n1,
  close_rtyp_wrt_rtyp_rec n1 a1 r1 = close_rtyp_wrt_rtyp_rec n1 a1 r2 ->
  r1 = r2).
Proof.
apply rlist_rt_rtyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rlist_wrt_rtyp_rec_inj :
forall R1 R2 a1 n1,
  close_rlist_wrt_rtyp_rec n1 a1 R1 = close_rlist_wrt_rtyp_rec n1 a1 R2 ->
  R1 = R2.
Proof.
pose proof close_rlist_wrt_rtyp_rec_inj_close_rt_wrt_rtyp_rec_inj_close_rtyp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_rlist_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rt_wrt_rtyp_rec_inj :
forall u1 u2 a1 n1,
  close_rt_wrt_rtyp_rec n1 a1 u1 = close_rt_wrt_rtyp_rec n1 a1 u2 ->
  u1 = u2.
Proof.
pose proof close_rlist_wrt_rtyp_rec_inj_close_rt_wrt_rtyp_rec_inj_close_rtyp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_rt_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rtyp_wrt_rtyp_rec_inj :
forall r1 r2 a1 n1,
  close_rtyp_wrt_rtyp_rec n1 a1 r1 = close_rtyp_wrt_rtyp_rec n1 a1 r2 ->
  r1 = r2.
Proof.
pose proof close_rlist_wrt_rtyp_rec_inj_close_rt_wrt_rtyp_rec_inj_close_rtyp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_rtyp_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rtyp_rec_inj_mutual :
(forall re1 re2 a1 n1,
  close_rexp_wrt_rtyp_rec n1 a1 re1 = close_rexp_wrt_rtyp_rec n1 a1 re2 ->
  re1 = re2).
Proof.
apply_mutual_ind rexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rtyp_rec_inj :
forall re1 re2 a1 n1,
  close_rexp_wrt_rtyp_rec n1 a1 re1 = close_rexp_wrt_rtyp_rec n1 a1 re2 ->
  re1 = re2.
Proof.
pose proof close_rexp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_rexp_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rexp_rec_inj_mutual :
(forall re1 re2 x1 n1,
  close_rexp_wrt_rexp_rec n1 x1 re1 = close_rexp_wrt_rexp_rec n1 x1 re2 ->
  re1 = re2).
Proof.
apply_mutual_ind rexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rexp_rec_inj :
forall re1 re2 x1 n1,
  close_rexp_wrt_rexp_rec n1 x1 re1 = close_rexp_wrt_rexp_rec n1 x1 re2 ->
  re1 = re2.
Proof.
pose proof close_rexp_wrt_rexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_rexp_wrt_rexp_rec_inj : lngen.

(* end hide *)

Lemma close_rlist_wrt_rtyp_inj :
forall R1 R2 a1,
  close_rlist_wrt_rtyp a1 R1 = close_rlist_wrt_rtyp a1 R2 ->
  R1 = R2.
Proof.
unfold close_rlist_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate close_rlist_wrt_rtyp_inj : lngen.

Lemma close_rt_wrt_rtyp_inj :
forall u1 u2 a1,
  close_rt_wrt_rtyp a1 u1 = close_rt_wrt_rtyp a1 u2 ->
  u1 = u2.
Proof.
unfold close_rt_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate close_rt_wrt_rtyp_inj : lngen.

Lemma close_rtyp_wrt_rtyp_inj :
forall r1 r2 a1,
  close_rtyp_wrt_rtyp a1 r1 = close_rtyp_wrt_rtyp a1 r2 ->
  r1 = r2.
Proof.
unfold close_rtyp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate close_rtyp_wrt_rtyp_inj : lngen.

Lemma close_rexp_wrt_rtyp_inj :
forall re1 re2 a1,
  close_rexp_wrt_rtyp a1 re1 = close_rexp_wrt_rtyp a1 re2 ->
  re1 = re2.
Proof.
unfold close_rexp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate close_rexp_wrt_rtyp_inj : lngen.

Lemma close_rexp_wrt_rexp_inj :
forall re1 re2 x1,
  close_rexp_wrt_rexp x1 re1 = close_rexp_wrt_rexp x1 re2 ->
  re1 = re2.
Proof.
unfold close_rexp_wrt_rexp; eauto with lngen.
Qed.

Hint Immediate close_rexp_wrt_rexp_inj : lngen.

(* begin hide *)

Lemma close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual :
(forall R1 a1 n1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  close_rlist_wrt_rtyp_rec n1 a1 (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1) = R1) /\
(forall u1 a1 n1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  close_rt_wrt_rtyp_rec n1 a1 (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1) = u1) /\
(forall r1 a1 n1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  close_rtyp_wrt_rtyp_rec n1 a1 (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1) = r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec :
forall R1 a1 n1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  close_rlist_wrt_rtyp_rec n1 a1 (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1) = R1.
Proof.
pose proof close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec : lngen.
Hint Rewrite close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec :
forall u1 a1 n1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  close_rt_wrt_rtyp_rec n1 a1 (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1) = u1.
Proof.
pose proof close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec : lngen.
Hint Rewrite close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec :
forall r1 a1 n1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  close_rtyp_wrt_rtyp_rec n1 a1 (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1) = r1.
Proof.
pose proof close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec : lngen.
Hint Rewrite close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  close_rexp_wrt_rtyp_rec n1 a1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1) = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec :
forall re1 a1 n1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  close_rexp_wrt_rtyp_rec n1 a1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1) = re1.
Proof.
pose proof close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec : lngen.
Hint Rewrite close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  close_rexp_wrt_rexp_rec n1 x1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1) = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec :
forall re1 x1 n1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  close_rexp_wrt_rexp_rec n1 x1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1) = re1.
Proof.
pose proof close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec : lngen.
Hint Rewrite close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_rlist_wrt_rtyp_open_rlist_wrt_rtyp :
forall R1 a1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  close_rlist_wrt_rtyp a1 (open_rlist_wrt_rtyp R1 (r_TyVar_f a1)) = R1.
Proof.
unfold close_rlist_wrt_rtyp; unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rlist_wrt_rtyp_open_rlist_wrt_rtyp : lngen.
Hint Rewrite close_rlist_wrt_rtyp_open_rlist_wrt_rtyp using solve [auto] : lngen.

Lemma close_rt_wrt_rtyp_open_rt_wrt_rtyp :
forall u1 a1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  close_rt_wrt_rtyp a1 (open_rt_wrt_rtyp u1 (r_TyVar_f a1)) = u1.
Proof.
unfold close_rt_wrt_rtyp; unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rt_wrt_rtyp_open_rt_wrt_rtyp : lngen.
Hint Rewrite close_rt_wrt_rtyp_open_rt_wrt_rtyp using solve [auto] : lngen.

Lemma close_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp :
forall r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  close_rtyp_wrt_rtyp a1 (open_rtyp_wrt_rtyp r1 (r_TyVar_f a1)) = r1.
Proof.
unfold close_rtyp_wrt_rtyp; unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp : lngen.
Hint Rewrite close_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp using solve [auto] : lngen.

Lemma close_rexp_wrt_rtyp_open_rexp_wrt_rtyp :
forall re1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  close_rexp_wrt_rtyp a1 (open_rexp_wrt_rtyp re1 (r_TyVar_f a1)) = re1.
Proof.
unfold close_rexp_wrt_rtyp; unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rexp_wrt_rtyp_open_rexp_wrt_rtyp : lngen.
Hint Rewrite close_rexp_wrt_rtyp_open_rexp_wrt_rtyp using solve [auto] : lngen.

Lemma close_rexp_wrt_rexp_open_rexp_wrt_rexp :
forall re1 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  close_rexp_wrt_rexp x1 (open_rexp_wrt_rexp re1 (re_Var_f x1)) = re1.
Proof.
unfold close_rexp_wrt_rexp; unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve close_rexp_wrt_rexp_open_rexp_wrt_rexp : lngen.
Hint Rewrite close_rexp_wrt_rexp_open_rexp_wrt_rexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_mutual :
(forall R1 a1 n1,
  open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rlist_wrt_rtyp_rec n1 a1 R1) = R1) /\
(forall u1 a1 n1,
  open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rt_wrt_rtyp_rec n1 a1 u1) = u1) /\
(forall r1 a1 n1,
  open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rtyp_wrt_rtyp_rec n1 a1 r1) = r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec :
forall R1 a1 n1,
  open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rlist_wrt_rtyp_rec n1 a1 R1) = R1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec : lngen.
Hint Rewrite open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec :
forall u1 a1 n1,
  open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rt_wrt_rtyp_rec n1 a1 u1) = u1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec : lngen.
Hint Rewrite open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec :
forall r1 a1 n1,
  open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rtyp_wrt_rtyp_rec n1 a1 r1) = r1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_close_rlist_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_close_rt_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec : lngen.
Hint Rewrite open_rtyp_wrt_rtyp_rec_close_rtyp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rtyp_rec_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1,
  open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rexp_wrt_rtyp_rec n1 a1 re1) = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rtyp_rec_close_rexp_wrt_rtyp_rec :
forall re1 a1 n1,
  open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) (close_rexp_wrt_rtyp_rec n1 a1 re1) = re1.
Proof.
pose proof open_rexp_wrt_rtyp_rec_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rexp_wrt_rtyp_rec_close_rexp_wrt_rtyp_rec : lngen.
Hint Rewrite open_rexp_wrt_rtyp_rec_close_rexp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rexp_rec_close_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1,
  open_rexp_wrt_rexp_rec n1 (re_Var_f x1) (close_rexp_wrt_rexp_rec n1 x1 re1) = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rexp_rec_close_rexp_wrt_rexp_rec :
forall re1 x1 n1,
  open_rexp_wrt_rexp_rec n1 (re_Var_f x1) (close_rexp_wrt_rexp_rec n1 x1 re1) = re1.
Proof.
pose proof open_rexp_wrt_rexp_rec_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rexp_wrt_rexp_rec_close_rexp_wrt_rexp_rec : lngen.
Hint Rewrite open_rexp_wrt_rexp_rec_close_rexp_wrt_rexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_rlist_wrt_rtyp_close_rlist_wrt_rtyp :
forall R1 a1,
  open_rlist_wrt_rtyp (close_rlist_wrt_rtyp a1 R1) (r_TyVar_f a1) = R1.
Proof.
unfold close_rlist_wrt_rtyp; unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rlist_wrt_rtyp_close_rlist_wrt_rtyp : lngen.
Hint Rewrite open_rlist_wrt_rtyp_close_rlist_wrt_rtyp using solve [auto] : lngen.

Lemma open_rt_wrt_rtyp_close_rt_wrt_rtyp :
forall u1 a1,
  open_rt_wrt_rtyp (close_rt_wrt_rtyp a1 u1) (r_TyVar_f a1) = u1.
Proof.
unfold close_rt_wrt_rtyp; unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rt_wrt_rtyp_close_rt_wrt_rtyp : lngen.
Hint Rewrite open_rt_wrt_rtyp_close_rt_wrt_rtyp using solve [auto] : lngen.

Lemma open_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp :
forall r1 a1,
  open_rtyp_wrt_rtyp (close_rtyp_wrt_rtyp a1 r1) (r_TyVar_f a1) = r1.
Proof.
unfold close_rtyp_wrt_rtyp; unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp : lngen.
Hint Rewrite open_rtyp_wrt_rtyp_close_rtyp_wrt_rtyp using solve [auto] : lngen.

Lemma open_rexp_wrt_rtyp_close_rexp_wrt_rtyp :
forall re1 a1,
  open_rexp_wrt_rtyp (close_rexp_wrt_rtyp a1 re1) (r_TyVar_f a1) = re1.
Proof.
unfold close_rexp_wrt_rtyp; unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rexp_wrt_rtyp_close_rexp_wrt_rtyp : lngen.
Hint Rewrite open_rexp_wrt_rtyp_close_rexp_wrt_rtyp using solve [auto] : lngen.

Lemma open_rexp_wrt_rexp_close_rexp_wrt_rexp :
forall re1 x1,
  open_rexp_wrt_rexp (close_rexp_wrt_rexp x1 re1) (re_Var_f x1) = re1.
Proof.
unfold close_rexp_wrt_rexp; unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve open_rexp_wrt_rexp_close_rexp_wrt_rexp : lngen.
Hint Rewrite open_rexp_wrt_rexp_close_rexp_wrt_rexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_rlist_wrt_rtyp_rec_inj_open_rt_wrt_rtyp_rec_inj_open_rtyp_wrt_rtyp_rec_inj_mutual :
(forall R2 R1 a1 n1,
  a1 `notin` fv_rtyp_in_rlist R2 ->
  a1 `notin` fv_rtyp_in_rlist R1 ->
  open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R2 = open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1 ->
  R2 = R1) /\
(forall u2 u1 a1 n1,
  a1 `notin` fv_rtyp_in_rt u2 ->
  a1 `notin` fv_rtyp_in_rt u1 ->
  open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u2 = open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1 ->
  u2 = u1) /\
(forall r2 r1 a1 n1,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r2 = open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1 ->
  r2 = r1).
Proof.
apply rlist_rt_rtyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rlist_wrt_rtyp_rec_inj :
forall R2 R1 a1 n1,
  a1 `notin` fv_rtyp_in_rlist R2 ->
  a1 `notin` fv_rtyp_in_rlist R1 ->
  open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R2 = open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1 ->
  R2 = R1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_inj_open_rt_wrt_rtyp_rec_inj_open_rtyp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_rlist_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rt_wrt_rtyp_rec_inj :
forall u2 u1 a1 n1,
  a1 `notin` fv_rtyp_in_rt u2 ->
  a1 `notin` fv_rtyp_in_rt u1 ->
  open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u2 = open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1 ->
  u2 = u1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_inj_open_rt_wrt_rtyp_rec_inj_open_rtyp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_rt_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rtyp_wrt_rtyp_rec_inj :
forall r2 r1 a1 n1,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r2 = open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1 ->
  r2 = r1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_inj_open_rt_wrt_rtyp_rec_inj_open_rtyp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_rtyp_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rtyp_rec_inj_mutual :
(forall re2 re1 a1 n1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re2 = open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1 ->
  re2 = re1).
Proof.
apply_mutual_ind rexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rtyp_rec_inj :
forall re2 re1 a1 n1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re2 = open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1 ->
  re2 = re1.
Proof.
pose proof open_rexp_wrt_rtyp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_rexp_wrt_rtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rexp_rec_inj_mutual :
(forall re2 re1 x1 n1,
  x1 `notin` fv_rexp_in_rexp re2 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re2 = open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1 ->
  re2 = re1).
Proof.
apply_mutual_ind rexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rexp_rec_inj :
forall re2 re1 x1 n1,
  x1 `notin` fv_rexp_in_rexp re2 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re2 = open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1 ->
  re2 = re1.
Proof.
pose proof open_rexp_wrt_rexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_rexp_wrt_rexp_rec_inj : lngen.

(* end hide *)

Lemma open_rlist_wrt_rtyp_inj :
forall R2 R1 a1,
  a1 `notin` fv_rtyp_in_rlist R2 ->
  a1 `notin` fv_rtyp_in_rlist R1 ->
  open_rlist_wrt_rtyp R2 (r_TyVar_f a1) = open_rlist_wrt_rtyp R1 (r_TyVar_f a1) ->
  R2 = R1.
Proof.
unfold open_rlist_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate open_rlist_wrt_rtyp_inj : lngen.

Lemma open_rt_wrt_rtyp_inj :
forall u2 u1 a1,
  a1 `notin` fv_rtyp_in_rt u2 ->
  a1 `notin` fv_rtyp_in_rt u1 ->
  open_rt_wrt_rtyp u2 (r_TyVar_f a1) = open_rt_wrt_rtyp u1 (r_TyVar_f a1) ->
  u2 = u1.
Proof.
unfold open_rt_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate open_rt_wrt_rtyp_inj : lngen.

Lemma open_rtyp_wrt_rtyp_inj :
forall r2 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  open_rtyp_wrt_rtyp r2 (r_TyVar_f a1) = open_rtyp_wrt_rtyp r1 (r_TyVar_f a1) ->
  r2 = r1.
Proof.
unfold open_rtyp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate open_rtyp_wrt_rtyp_inj : lngen.

Lemma open_rexp_wrt_rtyp_inj :
forall re2 re1 a1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  open_rexp_wrt_rtyp re2 (r_TyVar_f a1) = open_rexp_wrt_rtyp re1 (r_TyVar_f a1) ->
  re2 = re1.
Proof.
unfold open_rexp_wrt_rtyp; eauto with lngen.
Qed.

Hint Immediate open_rexp_wrt_rtyp_inj : lngen.

Lemma open_rexp_wrt_rexp_inj :
forall re2 re1 x1,
  x1 `notin` fv_rexp_in_rexp re2 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  open_rexp_wrt_rexp re2 (re_Var_f x1) = open_rexp_wrt_rexp re1 (re_Var_f x1) ->
  re2 = re1.
Proof.
unfold open_rexp_wrt_rexp; eauto with lngen.
Qed.

Hint Immediate open_rexp_wrt_rexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_rlist_wrt_rtyp_of_lc_rlist_degree_rt_wrt_rtyp_of_lc_rt_degree_rtyp_wrt_rtyp_of_lc_rtyp_mutual :
(forall R1,
  lc_rlist R1 ->
  degree_rlist_wrt_rtyp 0 R1) /\
(forall u1,
  lc_rt u1 ->
  degree_rt_wrt_rtyp 0 u1) /\
(forall r1,
  lc_rtyp r1 ->
  degree_rtyp_wrt_rtyp 0 r1).
Proof.
apply lc_rlist_lc_rt_lc_rtyp_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_rlist_wrt_rtyp_of_lc_rlist :
forall R1,
  lc_rlist R1 ->
  degree_rlist_wrt_rtyp 0 R1.
Proof.
pose proof degree_rlist_wrt_rtyp_of_lc_rlist_degree_rt_wrt_rtyp_of_lc_rt_degree_rtyp_wrt_rtyp_of_lc_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rlist_wrt_rtyp_of_lc_rlist : lngen.

Lemma degree_rt_wrt_rtyp_of_lc_rt :
forall u1,
  lc_rt u1 ->
  degree_rt_wrt_rtyp 0 u1.
Proof.
pose proof degree_rlist_wrt_rtyp_of_lc_rlist_degree_rt_wrt_rtyp_of_lc_rt_degree_rtyp_wrt_rtyp_of_lc_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rt_wrt_rtyp_of_lc_rt : lngen.

Lemma degree_rtyp_wrt_rtyp_of_lc_rtyp :
forall r1,
  lc_rtyp r1 ->
  degree_rtyp_wrt_rtyp 0 r1.
Proof.
pose proof degree_rlist_wrt_rtyp_of_lc_rlist_degree_rt_wrt_rtyp_of_lc_rt_degree_rtyp_wrt_rtyp_of_lc_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rtyp_wrt_rtyp_of_lc_rtyp : lngen.

(* begin hide *)

Lemma degree_rexp_wrt_rtyp_of_lc_rexp_mutual :
(forall re1,
  lc_rexp re1 ->
  degree_rexp_wrt_rtyp 0 re1).
Proof.
apply_mutual_ind lc_rexp_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_rexp_wrt_rtyp_of_lc_rexp :
forall re1,
  lc_rexp re1 ->
  degree_rexp_wrt_rtyp 0 re1.
Proof.
pose proof degree_rexp_wrt_rtyp_of_lc_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rtyp_of_lc_rexp : lngen.

(* begin hide *)

Lemma degree_rexp_wrt_rexp_of_lc_rexp_mutual :
(forall re1,
  lc_rexp re1 ->
  degree_rexp_wrt_rexp 0 re1).
Proof.
apply_mutual_ind lc_rexp_mutind;
intros;
let a1 := fresh "a1" in pick_fresh a1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_rexp_wrt_rexp_of_lc_rexp :
forall re1,
  lc_rexp re1 ->
  degree_rexp_wrt_rexp 0 re1.
Proof.
pose proof degree_rexp_wrt_rexp_of_lc_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_rexp_wrt_rexp_of_lc_rexp : lngen.

(* begin hide *)

Lemma lc_rlist_of_degree_lc_rt_of_degree_lc_rtyp_of_degree_size_mutual :
forall i1,
(forall R1,
  size_rlist R1 = i1 ->
  degree_rlist_wrt_rtyp 0 R1 ->
  lc_rlist R1) /\
(forall u1,
  size_rt u1 = i1 ->
  degree_rt_wrt_rtyp 0 u1 ->
  lc_rt u1) /\
(forall r1,
  size_rtyp r1 = i1 ->
  degree_rtyp_wrt_rtyp 0 r1 ->
  lc_rtyp r1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply rlist_rt_rtyp_mutind;
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

Lemma lc_rlist_of_degree :
forall R1,
  degree_rlist_wrt_rtyp 0 R1 ->
  lc_rlist R1.
Proof.
intros R1; intros;
pose proof (lc_rlist_of_degree_lc_rt_of_degree_lc_rtyp_of_degree_size_mutual (size_rlist R1));
intuition eauto.
Qed.

Hint Resolve lc_rlist_of_degree : lngen.

Lemma lc_rt_of_degree :
forall u1,
  degree_rt_wrt_rtyp 0 u1 ->
  lc_rt u1.
Proof.
intros u1; intros;
pose proof (lc_rlist_of_degree_lc_rt_of_degree_lc_rtyp_of_degree_size_mutual (size_rt u1));
intuition eauto.
Qed.

Hint Resolve lc_rt_of_degree : lngen.

Lemma lc_rtyp_of_degree :
forall r1,
  degree_rtyp_wrt_rtyp 0 r1 ->
  lc_rtyp r1.
Proof.
intros r1; intros;
pose proof (lc_rlist_of_degree_lc_rt_of_degree_lc_rtyp_of_degree_size_mutual (size_rtyp r1));
intuition eauto.
Qed.

Hint Resolve lc_rtyp_of_degree : lngen.

(* begin hide *)

Lemma lc_rexp_of_degree_size_mutual :
forall i1,
(forall re1,
  size_rexp re1 = i1 ->
  degree_rexp_wrt_rtyp 0 re1 ->
  degree_rexp_wrt_rexp 0 re1 ->
  lc_rexp re1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind rexp_mutind;
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

Lemma lc_rexp_of_degree :
forall re1,
  degree_rexp_wrt_rtyp 0 re1 ->
  degree_rexp_wrt_rexp 0 re1 ->
  lc_rexp re1.
Proof.
intros re1; intros;
pose proof (lc_rexp_of_degree_size_mutual (size_rexp re1));
intuition eauto.
Qed.

Hint Resolve lc_rexp_of_degree : lngen.

Ltac rlist_rt_rtyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_rlist_wrt_rtyp_of_lc_rlist in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_rt_wrt_rtyp_of_lc_rt in J1; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_rtyp_wrt_rtyp_of_lc_rtyp in J1; clear H
          end).

Ltac rexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_rexp_wrt_rtyp_of_lc_rexp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_rexp_wrt_rexp_of_lc_rexp in J2; clear H
          end).

Lemma lc_rt_ConQuan_exists :
forall a1 R1 rt1,
  lc_rlist R1 ->
  lc_rt (open_rt_wrt_rtyp rt1 (r_TyVar_f a1)) ->
  lc_rt (rt_ConQuan R1 rt1).
Proof.
intros; rlist_rt_rtyp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_re_Abs_exists :
forall x1 rt1 re1,
  lc_rt rt1 ->
  lc_rexp (open_rexp_wrt_rexp re1 (re_Var_f x1)) ->
  lc_rexp (re_Abs rt1 re1).
Proof.
intros; rexp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_re_ConTyAbs_exists :
forall a1 R1 re1,
  lc_rlist R1 ->
  lc_rexp (open_rexp_wrt_rtyp re1 (r_TyVar_f a1)) ->
  lc_rexp (re_ConTyAbs R1 re1).
Proof.
intros; rexp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_rt (rt_ConQuan _ _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_rt_ConQuan_exists a1).

Hint Extern 1 (lc_rexp (re_Abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_re_Abs_exists x1).

Hint Extern 1 (lc_rexp (re_ConTyAbs _ _)) =>
  let a1 := fresh in
  pick_fresh a1;
  apply (lc_re_ConTyAbs_exists a1).

Lemma lc_body_rlist_wrt_rtyp :
forall R1 r1,
  body_rlist_wrt_rtyp R1 ->
  lc_rtyp r1 ->
  lc_rlist (open_rlist_wrt_rtyp R1 r1).
Proof.
unfold body_rlist_wrt_rtyp;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
rlist_rt_rtyp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_rlist_wrt_rtyp : lngen.

Lemma lc_body_rt_wrt_rtyp :
forall u1 r1,
  body_rt_wrt_rtyp u1 ->
  lc_rtyp r1 ->
  lc_rt (open_rt_wrt_rtyp u1 r1).
Proof.
unfold body_rt_wrt_rtyp;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
rlist_rt_rtyp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_rt_wrt_rtyp : lngen.

Lemma lc_body_rtyp_wrt_rtyp :
forall r1 r2,
  body_rtyp_wrt_rtyp r1 ->
  lc_rtyp r2 ->
  lc_rtyp (open_rtyp_wrt_rtyp r1 r2).
Proof.
unfold body_rtyp_wrt_rtyp;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
rlist_rt_rtyp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_rtyp_wrt_rtyp : lngen.

Lemma lc_body_rexp_wrt_rtyp :
forall re1 r1,
  body_rexp_wrt_rtyp re1 ->
  lc_rtyp r1 ->
  lc_rexp (open_rexp_wrt_rtyp re1 r1).
Proof.
unfold body_rexp_wrt_rtyp;
default_simp;
let a1 := fresh "x" in
pick_fresh a1;
specialize_all a1;
rexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_rexp_wrt_rtyp : lngen.

Lemma lc_body_rexp_wrt_rexp :
forall re1 re2,
  body_rexp_wrt_rexp re1 ->
  lc_rexp re2 ->
  lc_rexp (open_rexp_wrt_rexp re1 re2).
Proof.
unfold body_rexp_wrt_rexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
rexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_rexp_wrt_rexp : lngen.

Lemma lc_body_rt_ConQuan_2 :
forall R1 rt1,
  lc_rt (rt_ConQuan R1 rt1) ->
  body_rt_wrt_rtyp rt1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_rt_ConQuan_2 : lngen.

Lemma lc_body_re_Abs_2 :
forall rt1 re1,
  lc_rexp (re_Abs rt1 re1) ->
  body_rexp_wrt_rexp re1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_re_Abs_2 : lngen.

Lemma lc_body_re_ConTyAbs_2 :
forall R1 re1,
  lc_rexp (re_ConTyAbs R1 re1) ->
  body_rexp_wrt_rtyp re1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_re_ConTyAbs_2 : lngen.

(* begin hide *)

Lemma lc_rlist_unique_lc_rt_unique_lc_rtyp_unique_mutual :
(forall R1 (proof2 proof3 : lc_rlist R1), proof2 = proof3) /\
(forall u1 (proof2 proof3 : lc_rt u1), proof2 = proof3) /\
(forall r1 (proof2 proof3 : lc_rtyp r1), proof2 = proof3).
Proof.
apply lc_rlist_lc_rt_lc_rtyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_rlist_unique :
forall R1 (proof2 proof3 : lc_rlist R1), proof2 = proof3.
Proof.
pose proof lc_rlist_unique_lc_rt_unique_lc_rtyp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rlist_unique : lngen.

Lemma lc_rt_unique :
forall u1 (proof2 proof3 : lc_rt u1), proof2 = proof3.
Proof.
pose proof lc_rlist_unique_lc_rt_unique_lc_rtyp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rt_unique : lngen.

Lemma lc_rtyp_unique :
forall r1 (proof2 proof3 : lc_rtyp r1), proof2 = proof3.
Proof.
pose proof lc_rlist_unique_lc_rt_unique_lc_rtyp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rtyp_unique : lngen.

(* begin hide *)

Lemma lc_rexp_unique_mutual :
(forall re1 (proof2 proof3 : lc_rexp re1), proof2 = proof3).
Proof.
apply_mutual_ind lc_rexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_rexp_unique :
forall re1 (proof2 proof3 : lc_rexp re1), proof2 = proof3.
Proof.
pose proof lc_rexp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rexp_unique : lngen.

(* begin hide *)

Lemma lc_rlist_of_lc_set_rlist_lc_rt_of_lc_set_rt_lc_rtyp_of_lc_set_rtyp_mutual :
(forall R1, lc_set_rlist R1 -> lc_rlist R1) /\
(forall u1, lc_set_rt u1 -> lc_rt u1) /\
(forall r1, lc_set_rtyp r1 -> lc_rtyp r1).
Proof.
apply lc_set_rlist_lc_set_rt_lc_set_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_rlist_of_lc_set_rlist :
forall R1, lc_set_rlist R1 -> lc_rlist R1.
Proof.
pose proof lc_rlist_of_lc_set_rlist_lc_rt_of_lc_set_rt_lc_rtyp_of_lc_set_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rlist_of_lc_set_rlist : lngen.

Lemma lc_rt_of_lc_set_rt :
forall u1, lc_set_rt u1 -> lc_rt u1.
Proof.
pose proof lc_rlist_of_lc_set_rlist_lc_rt_of_lc_set_rt_lc_rtyp_of_lc_set_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rt_of_lc_set_rt : lngen.

Lemma lc_rtyp_of_lc_set_rtyp :
forall r1, lc_set_rtyp r1 -> lc_rtyp r1.
Proof.
pose proof lc_rlist_of_lc_set_rlist_lc_rt_of_lc_set_rt_lc_rtyp_of_lc_set_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rtyp_of_lc_set_rtyp : lngen.

(* begin hide *)

Lemma lc_rexp_of_lc_set_rexp_mutual :
(forall re1, lc_set_rexp re1 -> lc_rexp re1).
Proof.
apply_mutual_ind lc_set_rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_rexp_of_lc_set_rexp :
forall re1, lc_set_rexp re1 -> lc_rexp re1.
Proof.
pose proof lc_rexp_of_lc_set_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_rexp_of_lc_set_rexp : lngen.

(* begin hide *)

Lemma lc_set_rlist_of_lc_rlist_lc_set_rt_of_lc_rt_lc_set_rtyp_of_lc_rtyp_size_mutual :
forall i1,
(forall R1,
  size_rlist R1 = i1 ->
  lc_rlist R1 ->
  lc_set_rlist R1) *
(forall u1,
  size_rt u1 = i1 ->
  lc_rt u1 ->
  lc_set_rt u1) *
(forall r1,
  size_rtyp r1 = i1 ->
  lc_rtyp r1 ->
  lc_set_rtyp r1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply rlist_rt_rtyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_rlist_of_lc_rlist
 | apply lc_set_rtyp_of_lc_rtyp
 | apply lc_set_rt_of_lc_rt
 | apply lc_set_rlist_of_lc_rlist
 | apply lc_set_rtyp_of_lc_rtyp
 | apply lc_set_rt_of_lc_rt
 | apply lc_set_rlist_of_lc_rlist
 | apply lc_set_rtyp_of_lc_rtyp
 | apply lc_set_rt_of_lc_rt];
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

Lemma lc_set_rlist_of_lc_rlist :
forall R1,
  lc_rlist R1 ->
  lc_set_rlist R1.
Proof.
intros R1; intros;
pose proof (lc_set_rlist_of_lc_rlist_lc_set_rt_of_lc_rt_lc_set_rtyp_of_lc_rtyp_size_mutual (size_rlist R1));
intuition eauto.
Qed.

Hint Resolve lc_set_rlist_of_lc_rlist : lngen.

Lemma lc_set_rt_of_lc_rt :
forall u1,
  lc_rt u1 ->
  lc_set_rt u1.
Proof.
intros u1; intros;
pose proof (lc_set_rlist_of_lc_rlist_lc_set_rt_of_lc_rt_lc_set_rtyp_of_lc_rtyp_size_mutual (size_rt u1));
intuition eauto.
Qed.

Hint Resolve lc_set_rt_of_lc_rt : lngen.

Lemma lc_set_rtyp_of_lc_rtyp :
forall r1,
  lc_rtyp r1 ->
  lc_set_rtyp r1.
Proof.
intros r1; intros;
pose proof (lc_set_rlist_of_lc_rlist_lc_set_rt_of_lc_rt_lc_set_rtyp_of_lc_rtyp_size_mutual (size_rtyp r1));
intuition eauto.
Qed.

Hint Resolve lc_set_rtyp_of_lc_rtyp : lngen.

(* begin hide *)

Lemma lc_set_rexp_of_lc_rexp_size_mutual :
forall i1,
(forall re1,
  size_rexp re1 = i1 ->
  lc_rexp re1 ->
  lc_set_rexp re1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind rexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_rlist_of_lc_rlist
 | apply lc_set_rtyp_of_lc_rtyp
 | apply lc_set_rexp_of_lc_rexp
 | apply lc_set_rt_of_lc_rt];
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

Lemma lc_set_rexp_of_lc_rexp :
forall re1,
  lc_rexp re1 ->
  lc_set_rexp re1.
Proof.
intros re1; intros;
pose proof (lc_set_rexp_of_lc_rexp_size_mutual (size_rexp re1));
intuition eauto.
Qed.

Hint Resolve lc_set_rexp_of_lc_rexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual :
(forall R1 a1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  a1 `notin` fv_rtyp_in_rlist R1 ->
  close_rlist_wrt_rtyp_rec n1 a1 R1 = R1) /\
(forall u1 a1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  a1 `notin` fv_rtyp_in_rt u1 ->
  close_rt_wrt_rtyp_rec n1 a1 u1 = u1) /\
(forall r1 a1 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  close_rtyp_wrt_rtyp_rec n1 a1 r1 = r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp :
forall R1 a1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  a1 `notin` fv_rtyp_in_rlist R1 ->
  close_rlist_wrt_rtyp_rec n1 a1 R1 = R1.
Proof.
pose proof close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp : lngen.
Hint Rewrite close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp :
forall u1 a1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  a1 `notin` fv_rtyp_in_rt u1 ->
  close_rt_wrt_rtyp_rec n1 a1 u1 = u1.
Proof.
pose proof close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp : lngen.
Hint Rewrite close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp :
forall r1 a1 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  close_rtyp_wrt_rtyp_rec n1 a1 r1 = r1.
Proof.
pose proof close_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_close_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp : lngen.
Hint Rewrite close_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp_mutual :
(forall re1 a1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  close_rexp_wrt_rtyp_rec n1 a1 re1 = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp :
forall re1 a1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  close_rexp_wrt_rtyp_rec n1 a1 re1 = re1.
Proof.
pose proof close_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp : lngen.
Hint Rewrite close_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp_mutual :
(forall re1 x1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  close_rexp_wrt_rexp_rec n1 x1 re1 = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp :
forall re1 x1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  close_rexp_wrt_rexp_rec n1 x1 re1 = re1.
Proof.
pose proof close_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp : lngen.
Hint Rewrite close_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp using solve [auto] : lngen.

(* end hide *)

Lemma close_rlist_wrt_rtyp_lc_rlist :
forall R1 a1,
  lc_rlist R1 ->
  a1 `notin` fv_rtyp_in_rlist R1 ->
  close_rlist_wrt_rtyp a1 R1 = R1.
Proof.
unfold close_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rlist_wrt_rtyp_lc_rlist : lngen.
Hint Rewrite close_rlist_wrt_rtyp_lc_rlist using solve [auto] : lngen.

Lemma close_rt_wrt_rtyp_lc_rt :
forall u1 a1,
  lc_rt u1 ->
  a1 `notin` fv_rtyp_in_rt u1 ->
  close_rt_wrt_rtyp a1 u1 = u1.
Proof.
unfold close_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rt_wrt_rtyp_lc_rt : lngen.
Hint Rewrite close_rt_wrt_rtyp_lc_rt using solve [auto] : lngen.

Lemma close_rtyp_wrt_rtyp_lc_rtyp :
forall r1 a1,
  lc_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  close_rtyp_wrt_rtyp a1 r1 = r1.
Proof.
unfold close_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rtyp_wrt_rtyp_lc_rtyp : lngen.
Hint Rewrite close_rtyp_wrt_rtyp_lc_rtyp using solve [auto] : lngen.

Lemma close_rexp_wrt_rtyp_lc_rexp :
forall re1 a1,
  lc_rexp re1 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  close_rexp_wrt_rtyp a1 re1 = re1.
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve close_rexp_wrt_rtyp_lc_rexp : lngen.
Hint Rewrite close_rexp_wrt_rtyp_lc_rexp using solve [auto] : lngen.

Lemma close_rexp_wrt_rexp_lc_rexp :
forall re1 x1,
  lc_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  close_rexp_wrt_rexp x1 re1 = re1.
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve close_rexp_wrt_rexp_lc_rexp : lngen.
Hint Rewrite close_rexp_wrt_rexp_lc_rexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual :
(forall R1 r1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  open_rlist_wrt_rtyp_rec n1 r1 R1 = R1) /\
(forall u1 r1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  open_rt_wrt_rtyp_rec n1 r1 u1 = u1) /\
(forall r2 r1 n1,
  degree_rtyp_wrt_rtyp n1 r2 ->
  open_rtyp_wrt_rtyp_rec n1 r1 r2 = r2).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp :
forall R1 r1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  open_rlist_wrt_rtyp_rec n1 r1 R1 = R1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp : lngen.
Hint Rewrite open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp :
forall u1 r1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  open_rt_wrt_rtyp_rec n1 r1 u1 = u1.
Proof.
pose proof open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp : lngen.
Hint Rewrite open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp :
forall r2 r1 n1,
  degree_rtyp_wrt_rtyp n1 r2 ->
  open_rtyp_wrt_rtyp_rec n1 r1 r2 = r2.
Proof.
pose proof open_rlist_wrt_rtyp_rec_degree_rlist_wrt_rtyp_open_rt_wrt_rtyp_rec_degree_rt_wrt_rtyp_open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp : lngen.
Hint Rewrite open_rtyp_wrt_rtyp_rec_degree_rtyp_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp_mutual :
(forall re1 r1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  open_rexp_wrt_rtyp_rec n1 r1 re1 = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp :
forall re1 r1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  open_rexp_wrt_rtyp_rec n1 r1 re1 = re1.
Proof.
pose proof open_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp : lngen.
Hint Rewrite open_rexp_wrt_rtyp_rec_degree_rexp_wrt_rtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp_mutual :
(forall re2 re1 n1,
  degree_rexp_wrt_rexp n1 re2 ->
  open_rexp_wrt_rexp_rec n1 re1 re2 = re2).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp :
forall re2 re1 n1,
  degree_rexp_wrt_rexp n1 re2 ->
  open_rexp_wrt_rexp_rec n1 re1 re2 = re2.
Proof.
pose proof open_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp : lngen.
Hint Rewrite open_rexp_wrt_rexp_rec_degree_rexp_wrt_rexp using solve [auto] : lngen.

(* end hide *)

Lemma open_rlist_wrt_rtyp_lc_rlist :
forall R1 r1,
  lc_rlist R1 ->
  open_rlist_wrt_rtyp R1 r1 = R1.
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rlist_wrt_rtyp_lc_rlist : lngen.
Hint Rewrite open_rlist_wrt_rtyp_lc_rlist using solve [auto] : lngen.

Lemma open_rt_wrt_rtyp_lc_rt :
forall u1 r1,
  lc_rt u1 ->
  open_rt_wrt_rtyp u1 r1 = u1.
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rt_wrt_rtyp_lc_rt : lngen.
Hint Rewrite open_rt_wrt_rtyp_lc_rt using solve [auto] : lngen.

Lemma open_rtyp_wrt_rtyp_lc_rtyp :
forall r2 r1,
  lc_rtyp r2 ->
  open_rtyp_wrt_rtyp r2 r1 = r2.
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rtyp_wrt_rtyp_lc_rtyp : lngen.
Hint Rewrite open_rtyp_wrt_rtyp_lc_rtyp using solve [auto] : lngen.

Lemma open_rexp_wrt_rtyp_lc_rexp :
forall re1 r1,
  lc_rexp re1 ->
  open_rexp_wrt_rtyp re1 r1 = re1.
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve open_rexp_wrt_rtyp_lc_rexp : lngen.
Hint Rewrite open_rexp_wrt_rtyp_lc_rexp using solve [auto] : lngen.

Lemma open_rexp_wrt_rexp_lc_rexp :
forall re2 re1,
  lc_rexp re2 ->
  open_rexp_wrt_rexp re2 re1 = re2.
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve open_rexp_wrt_rexp_lc_rexp : lngen.
Hint Rewrite open_rexp_wrt_rexp_lc_rexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_fv_rtyp_in_rt_close_rt_wrt_rtyp_rec_fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual :
(forall R1 a1 n1,
  fv_rtyp_in_rlist (close_rlist_wrt_rtyp_rec n1 a1 R1) [=] remove a1 (fv_rtyp_in_rlist R1)) /\
(forall u1 a1 n1,
  fv_rtyp_in_rt (close_rt_wrt_rtyp_rec n1 a1 u1) [=] remove a1 (fv_rtyp_in_rt u1)) /\
(forall r1 a1 n1,
  fv_rtyp_in_rtyp (close_rtyp_wrt_rtyp_rec n1 a1 r1) [=] remove a1 (fv_rtyp_in_rtyp r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec :
forall R1 a1 n1,
  fv_rtyp_in_rlist (close_rlist_wrt_rtyp_rec n1 a1 R1) [=] remove a1 (fv_rtyp_in_rlist R1).
Proof.
pose proof fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_fv_rtyp_in_rt_close_rt_wrt_rtyp_rec_fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec : lngen.
Hint Rewrite fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rt_close_rt_wrt_rtyp_rec :
forall u1 a1 n1,
  fv_rtyp_in_rt (close_rt_wrt_rtyp_rec n1 a1 u1) [=] remove a1 (fv_rtyp_in_rt u1).
Proof.
pose proof fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_fv_rtyp_in_rt_close_rt_wrt_rtyp_rec_fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_close_rt_wrt_rtyp_rec : lngen.
Hint Rewrite fv_rtyp_in_rt_close_rt_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec :
forall r1 a1 n1,
  fv_rtyp_in_rtyp (close_rtyp_wrt_rtyp_rec n1 a1 r1) [=] remove a1 (fv_rtyp_in_rtyp r1).
Proof.
pose proof fv_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_fv_rtyp_in_rt_close_rt_wrt_rtyp_rec_fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec : lngen.
Hint Rewrite fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1,
  fv_rtyp_in_rexp (close_rexp_wrt_rtyp_rec n1 a1 re1) [=] remove a1 (fv_rtyp_in_rexp re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_close_rexp_wrt_rtyp_rec :
forall re1 a1 n1,
  fv_rtyp_in_rexp (close_rexp_wrt_rtyp_rec n1 a1 re1) [=] remove a1 (fv_rtyp_in_rexp re1).
Proof.
pose proof fv_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_close_rexp_wrt_rtyp_rec : lngen.
Hint Rewrite fv_rtyp_in_rexp_close_rexp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_close_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1,
  fv_rtyp_in_rexp (close_rexp_wrt_rexp_rec n1 x1 re1) [=] fv_rtyp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_close_rexp_wrt_rexp_rec :
forall re1 x1 n1,
  fv_rtyp_in_rexp (close_rexp_wrt_rexp_rec n1 x1 re1) [=] fv_rtyp_in_rexp re1.
Proof.
pose proof fv_rtyp_in_rexp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_close_rexp_wrt_rexp_rec : lngen.
Hint Rewrite fv_rtyp_in_rexp_close_rexp_wrt_rexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 a1 n1,
  fv_rexp_in_rexp (close_rexp_wrt_rtyp_rec n1 a1 re1) [=] fv_rexp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_close_rexp_wrt_rtyp_rec :
forall re1 a1 n1,
  fv_rexp_in_rexp (close_rexp_wrt_rtyp_rec n1 a1 re1) [=] fv_rexp_in_rexp re1.
Proof.
pose proof fv_rexp_in_rexp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_close_rexp_wrt_rtyp_rec : lngen.
Hint Rewrite fv_rexp_in_rexp_close_rexp_wrt_rtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_close_rexp_wrt_rexp_rec_mutual :
(forall re1 x1 n1,
  fv_rexp_in_rexp (close_rexp_wrt_rexp_rec n1 x1 re1) [=] remove x1 (fv_rexp_in_rexp re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_close_rexp_wrt_rexp_rec :
forall re1 x1 n1,
  fv_rexp_in_rexp (close_rexp_wrt_rexp_rec n1 x1 re1) [=] remove x1 (fv_rexp_in_rexp re1).
Proof.
pose proof fv_rexp_in_rexp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_close_rexp_wrt_rexp_rec : lngen.
Hint Rewrite fv_rexp_in_rexp_close_rexp_wrt_rexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_rtyp_in_rlist_close_rlist_wrt_rtyp :
forall R1 a1,
  fv_rtyp_in_rlist (close_rlist_wrt_rtyp a1 R1) [=] remove a1 (fv_rtyp_in_rlist R1).
Proof.
unfold close_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rlist_close_rlist_wrt_rtyp : lngen.
Hint Rewrite fv_rtyp_in_rlist_close_rlist_wrt_rtyp using solve [auto] : lngen.

Lemma fv_rtyp_in_rt_close_rt_wrt_rtyp :
forall u1 a1,
  fv_rtyp_in_rt (close_rt_wrt_rtyp a1 u1) [=] remove a1 (fv_rtyp_in_rt u1).
Proof.
unfold close_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rt_close_rt_wrt_rtyp : lngen.
Hint Rewrite fv_rtyp_in_rt_close_rt_wrt_rtyp using solve [auto] : lngen.

Lemma fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp :
forall r1 a1,
  fv_rtyp_in_rtyp (close_rtyp_wrt_rtyp a1 r1) [=] remove a1 (fv_rtyp_in_rtyp r1).
Proof.
unfold close_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp : lngen.
Hint Rewrite fv_rtyp_in_rtyp_close_rtyp_wrt_rtyp using solve [auto] : lngen.

Lemma fv_rtyp_in_rexp_close_rexp_wrt_rtyp :
forall re1 a1,
  fv_rtyp_in_rexp (close_rexp_wrt_rtyp a1 re1) [=] remove a1 (fv_rtyp_in_rexp re1).
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rexp_close_rexp_wrt_rtyp : lngen.
Hint Rewrite fv_rtyp_in_rexp_close_rexp_wrt_rtyp using solve [auto] : lngen.

Lemma fv_rtyp_in_rexp_close_rexp_wrt_rexp :
forall re1 x1,
  fv_rtyp_in_rexp (close_rexp_wrt_rexp x1 re1) [=] fv_rtyp_in_rexp re1.
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rexp_close_rexp_wrt_rexp : lngen.
Hint Rewrite fv_rtyp_in_rexp_close_rexp_wrt_rexp using solve [auto] : lngen.

Lemma fv_rexp_in_rexp_close_rexp_wrt_rtyp :
forall re1 a1,
  fv_rexp_in_rexp (close_rexp_wrt_rtyp a1 re1) [=] fv_rexp_in_rexp re1.
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rexp_in_rexp_close_rexp_wrt_rtyp : lngen.
Hint Rewrite fv_rexp_in_rexp_close_rexp_wrt_rtyp using solve [auto] : lngen.

Lemma fv_rexp_in_rexp_close_rexp_wrt_rexp :
forall re1 x1,
  fv_rexp_in_rexp (close_rexp_wrt_rexp x1 re1) [=] remove x1 (fv_rexp_in_rexp re1).
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve fv_rexp_in_rexp_close_rexp_wrt_rexp : lngen.
Hint Rewrite fv_rexp_in_rexp_close_rexp_wrt_rexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_lower_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_lower_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_lower_mutual :
(forall R1 r1 n1,
  fv_rtyp_in_rlist R1 [<=] fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n1 r1 R1)) /\
(forall u1 r1 n1,
  fv_rtyp_in_rt u1 [<=] fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n1 r1 u1)) /\
(forall r1 r2 n1,
  fv_rtyp_in_rtyp r1 [<=] fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n1 r2 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_lower :
forall R1 r1 n1,
  fv_rtyp_in_rlist R1 [<=] fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n1 r1 R1).
Proof.
pose proof fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_lower_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_lower_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_lower :
forall u1 r1 n1,
  fv_rtyp_in_rt u1 [<=] fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n1 r1 u1).
Proof.
pose proof fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_lower_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_lower_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_lower :
forall r1 r2 n1,
  fv_rtyp_in_rtyp r1 [<=] fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n1 r2 r1).
Proof.
pose proof fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_lower_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_lower_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_lower_mutual :
(forall re1 r1 n1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_lower :
forall re1 r1 n1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1).
Proof.
pose proof fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_lower_mutual :
(forall re1 re2 n1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_lower :
forall re1 re2 n1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1).
Proof.
pose proof fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_lower_mutual :
(forall re1 r1 n1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_lower :
forall re1 r1 n1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1).
Proof.
pose proof fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_lower_mutual :
(forall re1 re2 n1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_lower :
forall re1 re2 n1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1).
Proof.
pose proof fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_lower : lngen.

(* end hide *)

Lemma fv_rtyp_in_rlist_open_rlist_wrt_rtyp_lower :
forall R1 r1,
  fv_rtyp_in_rlist R1 [<=] fv_rtyp_in_rlist (open_rlist_wrt_rtyp R1 r1).
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rlist_open_rlist_wrt_rtyp_lower : lngen.

Lemma fv_rtyp_in_rt_open_rt_wrt_rtyp_lower :
forall u1 r1,
  fv_rtyp_in_rt u1 [<=] fv_rtyp_in_rt (open_rt_wrt_rtyp u1 r1).
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rt_open_rt_wrt_rtyp_lower : lngen.

Lemma fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_lower :
forall r1 r2,
  fv_rtyp_in_rtyp r1 [<=] fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp r1 r2).
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_lower : lngen.

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rtyp_lower :
forall re1 r1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (open_rexp_wrt_rtyp re1 r1).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rtyp_lower : lngen.

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rexp_lower :
forall re1 re2,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (open_rexp_wrt_rexp re1 re2).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rexp_lower : lngen.

Lemma fv_rexp_in_rexp_open_rexp_wrt_rtyp_lower :
forall re1 r1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (open_rexp_wrt_rtyp re1 r1).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rtyp_lower : lngen.

Lemma fv_rexp_in_rexp_open_rexp_wrt_rexp_lower :
forall re1 re2,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (open_rexp_wrt_rexp re1 re2).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rexp_lower : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_upper_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_upper_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_upper_mutual :
(forall R1 r1 n1,
  fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n1 r1 R1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rlist R1) /\
(forall u1 r1 n1,
  fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n1 r1 u1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rt u1) /\
(forall r1 r2 n1,
  fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n1 r2 r1) [<=] fv_rtyp_in_rtyp r2 `union` fv_rtyp_in_rtyp r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_upper :
forall R1 r1 n1,
  fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n1 r1 R1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rlist R1.
Proof.
pose proof fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_upper_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_upper_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_upper :
forall u1 r1 n1,
  fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n1 r1 u1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rt u1.
Proof.
pose proof fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_upper_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_upper_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_upper :
forall r1 r2 n1,
  fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n1 r2 r1) [<=] fv_rtyp_in_rtyp r2 `union` fv_rtyp_in_rtyp r1.
Proof.
pose proof fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_upper_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec_upper_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_upper_mutual :
(forall re1 r1 n1,
  fv_rtyp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_upper :
forall re1 r1 n1,
  fv_rtyp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rexp re1.
Proof.
pose proof fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_upper_mutual :
(forall re1 re2 n1,
  fv_rtyp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1) [<=] fv_rtyp_in_rexp re2 `union` fv_rtyp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_upper :
forall re1 re2 n1,
  fv_rtyp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1) [<=] fv_rtyp_in_rexp re2 `union` fv_rtyp_in_rexp re1.
Proof.
pose proof fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_upper_mutual :
(forall re1 r1 n1,
  fv_rexp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1) [<=] fv_rexp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_upper :
forall re1 r1 n1,
  fv_rexp_in_rexp (open_rexp_wrt_rtyp_rec n1 r1 re1) [<=] fv_rexp_in_rexp re1.
Proof.
pose proof fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_upper_mutual :
(forall re1 re2 n1,
  fv_rexp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1) [<=] fv_rexp_in_rexp re2 `union` fv_rexp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_upper :
forall re1 re2 n1,
  fv_rexp_in_rexp (open_rexp_wrt_rexp_rec n1 re2 re1) [<=] fv_rexp_in_rexp re2 `union` fv_rexp_in_rexp re1.
Proof.
pose proof fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rexp_rec_upper : lngen.

(* end hide *)

Lemma fv_rtyp_in_rlist_open_rlist_wrt_rtyp_upper :
forall R1 r1,
  fv_rtyp_in_rlist (open_rlist_wrt_rtyp R1 r1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rlist R1.
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rlist_open_rlist_wrt_rtyp_upper : lngen.

Lemma fv_rtyp_in_rt_open_rt_wrt_rtyp_upper :
forall u1 r1,
  fv_rtyp_in_rt (open_rt_wrt_rtyp u1 r1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rt u1.
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rt_open_rt_wrt_rtyp_upper : lngen.

Lemma fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_upper :
forall r1 r2,
  fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp r1 r2) [<=] fv_rtyp_in_rtyp r2 `union` fv_rtyp_in_rtyp r1.
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_upper : lngen.

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rtyp_upper :
forall re1 r1,
  fv_rtyp_in_rexp (open_rexp_wrt_rtyp re1 r1) [<=] fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rexp re1.
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rtyp_upper : lngen.

Lemma fv_rtyp_in_rexp_open_rexp_wrt_rexp_upper :
forall re1 re2,
  fv_rtyp_in_rexp (open_rexp_wrt_rexp re1 re2) [<=] fv_rtyp_in_rexp re2 `union` fv_rtyp_in_rexp re1.
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve fv_rtyp_in_rexp_open_rexp_wrt_rexp_upper : lngen.

Lemma fv_rexp_in_rexp_open_rexp_wrt_rtyp_upper :
forall re1 r1,
  fv_rexp_in_rexp (open_rexp_wrt_rtyp re1 r1) [<=] fv_rexp_in_rexp re1.
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rtyp_upper : lngen.

Lemma fv_rexp_in_rexp_open_rexp_wrt_rexp_upper :
forall re1 re2,
  fv_rexp_in_rexp (open_rexp_wrt_rexp re1 re2) [<=] fv_rexp_in_rexp re2 `union` fv_rexp_in_rexp re1.
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve fv_rexp_in_rexp_open_rexp_wrt_rexp_upper : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh_fv_rtyp_in_rt_subst_rtyp_in_rt_fresh_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh_mutual :
(forall R1 r1 a1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1) [=] fv_rtyp_in_rlist R1) /\
(forall u1 r1 a1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1) [=] fv_rtyp_in_rt u1) /\
(forall r1 r2 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1) [=] fv_rtyp_in_rtyp r1).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh :
forall R1 r1 a1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1) [=] fv_rtyp_in_rlist R1.
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh_fv_rtyp_in_rt_subst_rtyp_in_rt_fresh_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh : lngen.
Hint Rewrite fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh using solve [auto] : lngen.

Lemma fv_rtyp_in_rt_subst_rtyp_in_rt_fresh :
forall u1 r1 a1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1) [=] fv_rtyp_in_rt u1.
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh_fv_rtyp_in_rt_subst_rtyp_in_rt_fresh_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_subst_rtyp_in_rt_fresh : lngen.
Hint Rewrite fv_rtyp_in_rt_subst_rtyp_in_rt_fresh using solve [auto] : lngen.

Lemma fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh :
forall r1 r2 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1) [=] fv_rtyp_in_rtyp r1.
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_fresh_fv_rtyp_in_rt_subst_rtyp_in_rt_fresh_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh : lngen.
Hint Rewrite fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_fresh_mutual :
(forall re1 r1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [=] fv_rtyp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_fresh :
forall re1 r1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [=] fv_rtyp_in_rexp re1.
Proof.
pose proof fv_rtyp_in_rexp_subst_rtyp_in_rexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rtyp_in_rexp_fresh : lngen.
Hint Rewrite fv_rtyp_in_rexp_subst_rtyp_in_rexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_fresh_mutual :
(forall re1 r1 a1,
  fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [=] fv_rexp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_fresh :
forall re1 r1 a1,
  fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [=] fv_rexp_in_rexp re1.
Proof.
pose proof fv_rtyp_in_rexp_subst_rexp_in_rexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rexp_in_rexp_fresh : lngen.
Hint Rewrite fv_rtyp_in_rexp_subst_rexp_in_rexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_fresh_mutual :
(forall re1 re2 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1) [=] fv_rexp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_fresh :
forall re1 re2 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1) [=] fv_rexp_in_rexp re1.
Proof.
pose proof fv_rexp_in_rexp_subst_rexp_in_rexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rexp_in_rexp_fresh : lngen.
Hint Rewrite fv_rexp_in_rexp_subst_rexp_in_rexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_lower_fv_rtyp_in_rt_subst_rtyp_in_rt_lower_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_lower_mutual :
(forall R1 r1 a1,
  remove a1 (fv_rtyp_in_rlist R1) [<=] fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 a1,
  remove a1 (fv_rtyp_in_rt u1) [<=] fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r1 r2 a1,
  remove a1 (fv_rtyp_in_rtyp r1) [<=] fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_lower :
forall R1 r1 a1,
  remove a1 (fv_rtyp_in_rlist R1) [<=] fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_lower_fv_rtyp_in_rt_subst_rtyp_in_rt_lower_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_subst_rtyp_in_rlist_lower : lngen.

Lemma fv_rtyp_in_rt_subst_rtyp_in_rt_lower :
forall u1 r1 a1,
  remove a1 (fv_rtyp_in_rt u1) [<=] fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_lower_fv_rtyp_in_rt_subst_rtyp_in_rt_lower_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_subst_rtyp_in_rt_lower : lngen.

Lemma fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_lower :
forall r1 r2 a1,
  remove a1 (fv_rtyp_in_rtyp r1) [<=] fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_lower_fv_rtyp_in_rt_subst_rtyp_in_rt_lower_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_lower : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_lower_mutual :
(forall re1 r1 a1,
  remove a1 (fv_rtyp_in_rexp re1) [<=] fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_lower :
forall re1 r1 a1,
  remove a1 (fv_rtyp_in_rexp re1) [<=] fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof fv_rtyp_in_rexp_subst_rtyp_in_rexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rtyp_in_rexp_lower : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_lower_mutual :
(forall re1 re2 x1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_lower :
forall re1 re2 x1,
  fv_rtyp_in_rexp re1 [<=] fv_rtyp_in_rexp (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof fv_rtyp_in_rexp_subst_rexp_in_rexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rexp_in_rexp_lower : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rtyp_in_rexp_lower_mutual :
(forall re1 r1 a1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rtyp_in_rexp_lower :
forall re1 r1 a1,
  fv_rexp_in_rexp re1 [<=] fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof fv_rexp_in_rexp_subst_rtyp_in_rexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rtyp_in_rexp_lower : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_lower_mutual :
(forall re1 re2 x1,
  remove x1 (fv_rexp_in_rexp re1) [<=] fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_lower :
forall re1 re2 x1,
  remove x1 (fv_rexp_in_rexp re1) [<=] fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof fv_rexp_in_rexp_subst_rexp_in_rexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rexp_in_rexp_lower : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_notin_fv_rtyp_in_rt_subst_rtyp_in_rt_notin_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_notin_mutual :
(forall R1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rlist R1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rt u1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r1 r2 a1 a2,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 `notin` fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_notin :
forall R1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rlist R1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_notin_fv_rtyp_in_rt_subst_rtyp_in_rt_notin_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_subst_rtyp_in_rlist_notin : lngen.

Lemma fv_rtyp_in_rt_subst_rtyp_in_rt_notin :
forall u1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rt u1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_notin_fv_rtyp_in_rt_subst_rtyp_in_rt_notin_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_subst_rtyp_in_rt_notin : lngen.

Lemma fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_notin :
forall r1 r2 a1 a2,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 `notin` fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_notin_fv_rtyp_in_rt_subst_rtyp_in_rt_notin_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_notin : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_notin_mutual :
(forall re1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rexp re1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_notin :
forall re1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rexp re1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof fv_rtyp_in_rexp_subst_rtyp_in_rexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rtyp_in_rexp_notin : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_notin_mutual :
(forall re1 re2 x1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_notin :
forall re1 re2 x1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof fv_rtyp_in_rexp_subst_rexp_in_rexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rexp_in_rexp_notin : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rtyp_in_rexp_notin_mutual :
(forall re1 r1 a1 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rtyp_in_rexp_notin :
forall re1 r1 a1 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof fv_rexp_in_rexp_subst_rtyp_in_rexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rtyp_in_rexp_notin : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_notin_mutual :
(forall re1 re2 x1 x2,
  x2 `notin` fv_rexp_in_rexp re1 ->
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 `notin` fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_notin :
forall re1 re2 x1 x2,
  x2 `notin` fv_rexp_in_rexp re1 ->
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 `notin` fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof fv_rexp_in_rexp_subst_rexp_in_rexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rexp_in_rexp_notin : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_upper_fv_rtyp_in_rt_subst_rtyp_in_rt_upper_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_upper_mutual :
(forall R1 r1 a1,
  fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1) [<=] fv_rtyp_in_rtyp r1 `union` remove a1 (fv_rtyp_in_rlist R1)) /\
(forall u1 r1 a1,
  fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1) [<=] fv_rtyp_in_rtyp r1 `union` remove a1 (fv_rtyp_in_rt u1)) /\
(forall r1 r2 a1,
  fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1) [<=] fv_rtyp_in_rtyp r2 `union` remove a1 (fv_rtyp_in_rtyp r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rlist_subst_rtyp_in_rlist_upper :
forall R1 r1 a1,
  fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1) [<=] fv_rtyp_in_rtyp r1 `union` remove a1 (fv_rtyp_in_rlist R1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_upper_fv_rtyp_in_rt_subst_rtyp_in_rt_upper_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rlist_subst_rtyp_in_rlist_upper : lngen.

Lemma fv_rtyp_in_rt_subst_rtyp_in_rt_upper :
forall u1 r1 a1,
  fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1) [<=] fv_rtyp_in_rtyp r1 `union` remove a1 (fv_rtyp_in_rt u1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_upper_fv_rtyp_in_rt_subst_rtyp_in_rt_upper_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rt_subst_rtyp_in_rt_upper : lngen.

Lemma fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_upper :
forall r1 r2 a1,
  fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r1) [<=] fv_rtyp_in_rtyp r2 `union` remove a1 (fv_rtyp_in_rtyp r1).
Proof.
pose proof fv_rtyp_in_rlist_subst_rtyp_in_rlist_upper_fv_rtyp_in_rt_subst_rtyp_in_rt_upper_fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rtyp_subst_rtyp_in_rtyp_upper : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_upper_mutual :
(forall re1 r1 a1,
  fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [<=] fv_rtyp_in_rtyp r1 `union` remove a1 (fv_rtyp_in_rexp re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rtyp_in_rexp_upper :
forall re1 r1 a1,
  fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [<=] fv_rtyp_in_rtyp r1 `union` remove a1 (fv_rtyp_in_rexp re1).
Proof.
pose proof fv_rtyp_in_rexp_subst_rtyp_in_rexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rtyp_in_rexp_upper : lngen.

(* begin hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_upper_mutual :
(forall re1 re2 x1,
  fv_rtyp_in_rexp (subst_rexp_in_rexp re2 x1 re1) [<=] fv_rtyp_in_rexp re2 `union` fv_rtyp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rtyp_in_rexp_subst_rexp_in_rexp_upper :
forall re1 re2 x1,
  fv_rtyp_in_rexp (subst_rexp_in_rexp re2 x1 re1) [<=] fv_rtyp_in_rexp re2 `union` fv_rtyp_in_rexp re1.
Proof.
pose proof fv_rtyp_in_rexp_subst_rexp_in_rexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rtyp_in_rexp_subst_rexp_in_rexp_upper : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rtyp_in_rexp_upper_mutual :
(forall re1 r1 a1,
  fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [<=] fv_rexp_in_rexp re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rtyp_in_rexp_upper :
forall re1 r1 a1,
  fv_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re1) [<=] fv_rexp_in_rexp re1.
Proof.
pose proof fv_rexp_in_rexp_subst_rtyp_in_rexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rtyp_in_rexp_upper : lngen.

(* begin hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_upper_mutual :
(forall re1 re2 x1,
  fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1) [<=] fv_rexp_in_rexp re2 `union` remove x1 (fv_rexp_in_rexp re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_rexp_in_rexp_subst_rexp_in_rexp_upper :
forall re1 re2 x1,
  fv_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re1) [<=] fv_rexp_in_rexp re2 `union` remove x1 (fv_rexp_in_rexp re1).
Proof.
pose proof fv_rexp_in_rexp_subst_rexp_in_rexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_rexp_in_rexp_subst_rexp_in_rexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual :
(forall R1 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 (close_rlist_wrt_rtyp_rec n1 a2 R1) = close_rlist_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 (close_rt_wrt_rtyp_rec n1 a2 u1) = close_rt_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r2 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 (close_rtyp_wrt_rtyp_rec n1 a2 r2) = close_rtyp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rtyp r1 a1 r2)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec :
forall R1 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 (close_rlist_wrt_rtyp_rec n1 a2 R1) = close_rlist_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec : lngen.

Lemma subst_rtyp_in_rt_close_rt_wrt_rtyp_rec :
forall u1 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 (close_rt_wrt_rtyp_rec n1 a2 u1) = close_rt_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_close_rt_wrt_rtyp_rec : lngen.

Lemma subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec :
forall r2 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 (close_rtyp_wrt_rtyp_rec n1 a2 r2) = close_rtyp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
pose proof subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_mutual :
(forall re1 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 (close_rexp_wrt_rtyp_rec n1 a2 re1) = close_rexp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec :
forall re1 r1 a1 a2 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 (close_rexp_wrt_rtyp_rec n1 a2 re1) = close_rexp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec_mutual :
(forall re1 r1 x1 a1 n1,
  subst_rtyp_in_rexp r1 x1 (close_rexp_wrt_rexp_rec n1 a1 re1) = close_rexp_wrt_rexp_rec n1 a1 (subst_rtyp_in_rexp r1 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec :
forall re1 r1 x1 a1 n1,
  subst_rtyp_in_rexp r1 x1 (close_rexp_wrt_rexp_rec n1 a1 re1) = close_rexp_wrt_rexp_rec n1 a1 (subst_rtyp_in_rexp r1 x1 re1).
Proof.
pose proof subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec_mutual :
(forall re2 re1 a1 x1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  x1 `notin` fv_rtyp_in_rexp re1 ->
  subst_rexp_in_rexp re1 a1 (close_rexp_wrt_rtyp_rec n1 x1 re2) = close_rexp_wrt_rtyp_rec n1 x1 (subst_rexp_in_rexp re1 a1 re2)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec :
forall re2 re1 a1 x1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  x1 `notin` fv_rtyp_in_rexp re1 ->
  subst_rexp_in_rexp re1 a1 (close_rexp_wrt_rtyp_rec n1 x1 re2) = close_rexp_wrt_rtyp_rec n1 x1 (subst_rexp_in_rexp re1 a1 re2).
Proof.
pose proof subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rexp_rec_mutual :
(forall re2 re1 x1 x2 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  x1 <> x2 ->
  x2 `notin` fv_rexp_in_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (close_rexp_wrt_rexp_rec n1 x2 re2) = close_rexp_wrt_rexp_rec n1 x2 (subst_rexp_in_rexp re1 x1 re2)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rexp_rec :
forall re2 re1 x1 x2 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  x1 <> x2 ->
  x2 `notin` fv_rexp_in_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (close_rexp_wrt_rexp_rec n1 x2 re2) = close_rexp_wrt_rexp_rec n1 x2 (subst_rexp_in_rexp re1 x1 re2).
Proof.
pose proof subst_rexp_in_rexp_close_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rexp_rec : lngen.

Lemma subst_rtyp_in_rlist_close_rlist_wrt_rtyp :
forall R1 r1 a1 a2,
  lc_rtyp r1 ->  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 (close_rlist_wrt_rtyp a2 R1) = close_rlist_wrt_rtyp a2 (subst_rtyp_in_rlist r1 a1 R1).
Proof.
unfold close_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_close_rlist_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rt_close_rt_wrt_rtyp :
forall u1 r1 a1 a2,
  lc_rtyp r1 ->  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 (close_rt_wrt_rtyp a2 u1) = close_rt_wrt_rtyp a2 (subst_rtyp_in_rt r1 a1 u1).
Proof.
unfold close_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_close_rt_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp :
forall r2 r1 a1 a2,
  lc_rtyp r1 ->  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 (close_rtyp_wrt_rtyp a2 r2) = close_rtyp_wrt_rtyp a2 (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
unfold close_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rtyp :
forall re1 r1 a1 a2,
  lc_rtyp r1 ->  a1 <> a2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 (close_rexp_wrt_rtyp a2 re1) = close_rexp_wrt_rtyp a2 (subst_rtyp_in_rexp r1 a1 re1).
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rexp :
forall re1 r1 x1 a1,
  lc_rtyp r1 ->  subst_rtyp_in_rexp r1 x1 (close_rexp_wrt_rexp a1 re1) = close_rexp_wrt_rexp a1 (subst_rtyp_in_rexp r1 x1 re1).
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rexp : lngen.

Lemma subst_rexp_in_rexp_close_rexp_wrt_rtyp :
forall re2 re1 a1 x1,
  lc_rexp re1 ->  x1 `notin` fv_rtyp_in_rexp re1 ->
  subst_rexp_in_rexp re1 a1 (close_rexp_wrt_rtyp x1 re2) = close_rexp_wrt_rtyp x1 (subst_rexp_in_rexp re1 a1 re2).
Proof.
unfold close_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rtyp : lngen.

Lemma subst_rexp_in_rexp_close_rexp_wrt_rexp :
forall re2 re1 x1 x2,
  lc_rexp re1 ->  x1 <> x2 ->
  x2 `notin` fv_rexp_in_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (close_rexp_wrt_rexp x2 re2) = close_rexp_wrt_rexp x2 (subst_rexp_in_rexp re1 x1 re2).
Proof.
unfold close_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rexp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_degree_rlist_wrt_rtyp_subst_rtyp_in_rt_degree_rt_wrt_rtyp_subst_rtyp_in_rtyp_degree_rtyp_wrt_rtyp_mutual :
(forall R1 r1 a1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rlist_wrt_rtyp n1 (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 a1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rt_wrt_rtyp n1 (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r1 r2 a1 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rtyp_wrt_rtyp n1 r2 ->
  degree_rtyp_wrt_rtyp n1 (subst_rtyp_in_rtyp r2 a1 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_degree_rlist_wrt_rtyp :
forall R1 r1 a1 n1,
  degree_rlist_wrt_rtyp n1 R1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rlist_wrt_rtyp n1 (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof subst_rtyp_in_rlist_degree_rlist_wrt_rtyp_subst_rtyp_in_rt_degree_rt_wrt_rtyp_subst_rtyp_in_rtyp_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_degree_rlist_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rt_degree_rt_wrt_rtyp :
forall u1 r1 a1 n1,
  degree_rt_wrt_rtyp n1 u1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rt_wrt_rtyp n1 (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof subst_rtyp_in_rlist_degree_rlist_wrt_rtyp_subst_rtyp_in_rt_degree_rt_wrt_rtyp_subst_rtyp_in_rtyp_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_degree_rt_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rtyp_degree_rtyp_wrt_rtyp :
forall r1 r2 a1 n1,
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rtyp_wrt_rtyp n1 r2 ->
  degree_rtyp_wrt_rtyp n1 (subst_rtyp_in_rtyp r2 a1 r1).
Proof.
pose proof subst_rtyp_in_rlist_degree_rlist_wrt_rtyp_subst_rtyp_in_rt_degree_rt_wrt_rtyp_subst_rtyp_in_rtyp_degree_rtyp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_degree_rtyp_wrt_rtyp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_degree_rexp_wrt_rtyp_mutual :
(forall re1 r1 a1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rexp_wrt_rtyp n1 (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_degree_rexp_wrt_rtyp :
forall re1 r1 a1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  degree_rexp_wrt_rtyp n1 (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_degree_rexp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_degree_rexp_wrt_rtyp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_degree_rexp_wrt_rexp_mutual :
(forall re1 r1 a1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_degree_rexp_wrt_rexp :
forall re1 r1 a1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_degree_rexp_wrt_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_degree_rexp_wrt_rexp : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_degree_rexp_wrt_rtyp_mutual :
(forall re1 re2 x1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp n1 re2 ->
  degree_rexp_wrt_rtyp n1 (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_degree_rexp_wrt_rtyp :
forall re1 re2 x1 n1,
  degree_rexp_wrt_rtyp n1 re1 ->
  degree_rexp_wrt_rtyp n1 re2 ->
  degree_rexp_wrt_rtyp n1 (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof subst_rexp_in_rexp_degree_rexp_wrt_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_degree_rexp_wrt_rtyp : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_degree_rexp_wrt_rexp_mutual :
(forall re1 re2 x1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 re2 ->
  degree_rexp_wrt_rexp n1 (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_degree_rexp_wrt_rexp :
forall re1 re2 x1 n1,
  degree_rexp_wrt_rexp n1 re1 ->
  degree_rexp_wrt_rexp n1 re2 ->
  degree_rexp_wrt_rexp n1 (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof subst_rexp_in_rexp_degree_rexp_wrt_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_degree_rexp_wrt_rexp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_fresh_eq_subst_rtyp_in_rt_fresh_eq_subst_rtyp_in_rtyp_fresh_eq_mutual :
(forall R1 r1 a1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  subst_rtyp_in_rlist r1 a1 R1 = R1) /\
(forall u1 r1 a1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  subst_rtyp_in_rt r1 a1 u1 = u1) /\
(forall r2 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  subst_rtyp_in_rtyp r1 a1 r2 = r2).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_fresh_eq :
forall R1 r1 a1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  subst_rtyp_in_rlist r1 a1 R1 = R1.
Proof.
pose proof subst_rtyp_in_rlist_fresh_eq_subst_rtyp_in_rt_fresh_eq_subst_rtyp_in_rtyp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_fresh_eq : lngen.
Hint Rewrite subst_rtyp_in_rlist_fresh_eq using solve [auto] : lngen.

Lemma subst_rtyp_in_rt_fresh_eq :
forall u1 r1 a1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  subst_rtyp_in_rt r1 a1 u1 = u1.
Proof.
pose proof subst_rtyp_in_rlist_fresh_eq_subst_rtyp_in_rt_fresh_eq_subst_rtyp_in_rtyp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_fresh_eq : lngen.
Hint Rewrite subst_rtyp_in_rt_fresh_eq using solve [auto] : lngen.

Lemma subst_rtyp_in_rtyp_fresh_eq :
forall r2 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  subst_rtyp_in_rtyp r1 a1 r2 = r2.
Proof.
pose proof subst_rtyp_in_rlist_fresh_eq_subst_rtyp_in_rt_fresh_eq_subst_rtyp_in_rtyp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_fresh_eq : lngen.
Hint Rewrite subst_rtyp_in_rtyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_fresh_eq_mutual :
(forall re1 r1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  subst_rtyp_in_rexp r1 a1 re1 = re1).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_fresh_eq :
forall re1 r1 a1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  subst_rtyp_in_rexp r1 a1 re1 = re1.
Proof.
pose proof subst_rtyp_in_rexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_fresh_eq : lngen.
Hint Rewrite subst_rtyp_in_rexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_fresh_eq_mutual :
(forall re2 re1 x1,
  x1 `notin` fv_rexp_in_rexp re2 ->
  subst_rexp_in_rexp re1 x1 re2 = re2).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_fresh_eq :
forall re2 re1 x1,
  x1 `notin` fv_rexp_in_rexp re2 ->
  subst_rexp_in_rexp re1 x1 re2 = re2.
Proof.
pose proof subst_rexp_in_rexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_fresh_eq : lngen.
Hint Rewrite subst_rexp_in_rexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_fresh_same_subst_rtyp_in_rt_fresh_same_subst_rtyp_in_rtyp_fresh_same_mutual :
(forall R1 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r2 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r1 a1 r2)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_fresh_same :
forall R1 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof subst_rtyp_in_rlist_fresh_same_subst_rtyp_in_rt_fresh_same_subst_rtyp_in_rtyp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_fresh_same : lngen.

Lemma subst_rtyp_in_rt_fresh_same :
forall u1 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rt (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof subst_rtyp_in_rlist_fresh_same_subst_rtyp_in_rt_fresh_same_subst_rtyp_in_rtyp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_fresh_same : lngen.

Lemma subst_rtyp_in_rtyp_fresh_same :
forall r2 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
pose proof subst_rtyp_in_rlist_fresh_same_subst_rtyp_in_rt_fresh_same_subst_rtyp_in_rtyp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_fresh_same_mutual :
(forall re1 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_fresh_same :
forall re1 r1 a1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_fresh_same_mutual :
(forall re2 re1 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp (subst_rexp_in_rexp re1 x1 re2)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_fresh_same :
forall re2 re1 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp (subst_rexp_in_rexp re1 x1 re2).
Proof.
pose proof subst_rexp_in_rexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_fresh_subst_rtyp_in_rt_fresh_subst_rtyp_in_rtyp_fresh_mutual :
(forall R1 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a2 R1)) /\
(forall u1 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rt u1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rt (subst_rtyp_in_rt r1 a2 u1)) /\
(forall r2 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r1 a2 r2)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_fresh :
forall R1 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rlist (subst_rtyp_in_rlist r1 a2 R1).
Proof.
pose proof subst_rtyp_in_rlist_fresh_subst_rtyp_in_rt_fresh_subst_rtyp_in_rtyp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_fresh : lngen.

Lemma subst_rtyp_in_rt_fresh :
forall u1 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rt u1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rt (subst_rtyp_in_rt r1 a2 u1).
Proof.
pose proof subst_rtyp_in_rlist_fresh_subst_rtyp_in_rt_fresh_subst_rtyp_in_rtyp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_fresh : lngen.

Lemma subst_rtyp_in_rtyp_fresh :
forall r2 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rtyp r2 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rtyp (subst_rtyp_in_rtyp r1 a2 r2).
Proof.
pose proof subst_rtyp_in_rlist_fresh_subst_rtyp_in_rt_fresh_subst_rtyp_in_rtyp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_fresh : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_fresh_mutual :
(forall re1 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a2 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_fresh :
forall re1 r1 a1 a2,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  a1 `notin` fv_rtyp_in_rexp (subst_rtyp_in_rexp r1 a2 re1).
Proof.
pose proof subst_rtyp_in_rexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_fresh : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_fresh_mutual :
(forall re2 re1 x1 x2,
  x1 `notin` fv_rexp_in_rexp re2 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp (subst_rexp_in_rexp re1 x2 re2)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_fresh :
forall re2 re1 x1 x2,
  x1 `notin` fv_rexp_in_rexp re2 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  x1 `notin` fv_rexp_in_rexp (subst_rexp_in_rexp re1 x2 re2).
Proof.
pose proof subst_rexp_in_rexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_fresh : lngen.

Lemma subst_rtyp_in_rlist_lc_rlist :
forall R1 r1 a1,
  lc_rlist R1 ->
  lc_rtyp r1 ->
  lc_rlist (subst_rtyp_in_rlist r1 a1 R1).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_lc_rlist : lngen.

Lemma subst_rtyp_in_rt_lc_rt :
forall u1 r1 a1,
  lc_rt u1 ->
  lc_rtyp r1 ->
  lc_rt (subst_rtyp_in_rt r1 a1 u1).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_lc_rt : lngen.

Lemma subst_rtyp_in_rtyp_lc_rtyp :
forall r1 r2 a1,
  lc_rtyp r1 ->
  lc_rtyp r2 ->
  lc_rtyp (subst_rtyp_in_rtyp r2 a1 r1).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_lc_rtyp : lngen.

Lemma subst_rtyp_in_rexp_lc_rexp :
forall re1 r1 a1,
  lc_rexp re1 ->
  lc_rtyp r1 ->
  lc_rexp (subst_rtyp_in_rexp r1 a1 re1).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_lc_rexp : lngen.

Lemma subst_rexp_in_rexp_lc_rexp :
forall re1 re2 x1,
  lc_rexp re1 ->
  lc_rexp re2 ->
  lc_rexp (subst_rexp_in_rexp re2 x1 re1).
Proof.
default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_lc_rexp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_mutual :
(forall R1 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp_rec n1 r2 R1) = open_rlist_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp_rec n1 r2 u1) = open_rt_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r3 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp_rec n1 r2 r3) = open_rtyp_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rtyp r1 a1 r3)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rlist_open_rlist_wrt_rtyp_rec :
forall R1 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp_rec n1 r2 R1) = open_rlist_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof subst_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_open_rlist_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rt_open_rt_wrt_rtyp_rec :
forall u1 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp_rec n1 r2 u1) = open_rt_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof subst_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_open_rt_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec :
forall r3 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp_rec n1 r2 r3) = open_rtyp_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rtyp r1 a1 r3).
Proof.
pose proof subst_rtyp_in_rlist_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_mutual :
(forall re1 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp_rec n1 r2 re1) = open_rexp_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rtyp_rec :
forall re1 r1 r2 a1 n1,
  lc_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp_rec n1 r2 re1) = open_rexp_wrt_rtyp_rec n1 (subst_rtyp_in_rtyp r1 a1 r2) (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rexp_rec_mutual :
(forall re2 r1 re1 a1 n1,
  subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp_rec n1 re1 re2) = open_rexp_wrt_rexp_rec n1 (subst_rtyp_in_rexp r1 a1 re1) (subst_rtyp_in_rexp r1 a1 re2)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rexp_rec :
forall re2 r1 re1 a1 n1,
  subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp_rec n1 re1 re2) = open_rexp_wrt_rexp_rec n1 (subst_rtyp_in_rexp r1 a1 re1) (subst_rtyp_in_rexp r1 a1 re2).
Proof.
pose proof subst_rtyp_in_rexp_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_open_rexp_wrt_rtyp_rec_mutual :
(forall re2 re1 r1 x1 n1,
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp_rec n1 r1 re2) = open_rexp_wrt_rtyp_rec n1 r1 (subst_rexp_in_rexp re1 x1 re2)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_open_rexp_wrt_rtyp_rec :
forall re2 re1 r1 x1 n1,
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp_rec n1 r1 re2) = open_rexp_wrt_rtyp_rec n1 r1 (subst_rexp_in_rexp re1 x1 re2).
Proof.
pose proof subst_rexp_in_rexp_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_open_rexp_wrt_rexp_rec_mutual :
(forall re3 re1 re2 x1 n1,
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp_rec n1 re2 re3) = open_rexp_wrt_rexp_rec n1 (subst_rexp_in_rexp re1 x1 re2) (subst_rexp_in_rexp re1 x1 re3)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_open_rexp_wrt_rexp_rec :
forall re3 re1 re2 x1 n1,
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp_rec n1 re2 re3) = open_rexp_wrt_rexp_rec n1 (subst_rexp_in_rexp re1 x1 re2) (subst_rexp_in_rexp re1 x1 re3).
Proof.
pose proof subst_rexp_in_rexp_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

Lemma subst_rtyp_in_rlist_open_rlist_wrt_rtyp :
forall R1 r1 r2 a1,
  lc_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp R1 r2) = open_rlist_wrt_rtyp (subst_rtyp_in_rlist r1 a1 R1) (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_open_rlist_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rt_open_rt_wrt_rtyp :
forall u1 r1 r2 a1,
  lc_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp u1 r2) = open_rt_wrt_rtyp (subst_rtyp_in_rt r1 a1 u1) (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_open_rt_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp :
forall r3 r1 r2 a1,
  lc_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp r3 r2) = open_rtyp_wrt_rtyp (subst_rtyp_in_rtyp r1 a1 r3) (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rtyp :
forall re1 r1 r2 a1,
  lc_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp re1 r2) = open_rexp_wrt_rtyp (subst_rtyp_in_rexp r1 a1 re1) (subst_rtyp_in_rtyp r1 a1 r2).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_open_rexp_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rexp :
forall re2 r1 re1 a1,
  subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp re2 re1) = open_rexp_wrt_rexp (subst_rtyp_in_rexp r1 a1 re2) (subst_rtyp_in_rexp r1 a1 re1).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_open_rexp_wrt_rexp : lngen.

Lemma subst_rexp_in_rexp_open_rexp_wrt_rtyp :
forall re2 re1 r1 x1,
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp re2 r1) = open_rexp_wrt_rtyp (subst_rexp_in_rexp re1 x1 re2) r1.
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_open_rexp_wrt_rtyp : lngen.

Lemma subst_rexp_in_rexp_open_rexp_wrt_rexp :
forall re3 re1 re2 x1,
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp re3 re2) = open_rexp_wrt_rexp (subst_rexp_in_rexp re1 x1 re3) (subst_rexp_in_rexp re1 x1 re2).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_open_rexp_wrt_rexp : lngen.

Lemma subst_rtyp_in_rlist_open_rlist_wrt_rtyp_var :
forall R1 r1 a1 a2,
  a1 <> a2 ->
  lc_rtyp r1 ->
  open_rlist_wrt_rtyp (subst_rtyp_in_rlist r1 a1 R1) (r_TyVar_f a2) = subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp R1 (r_TyVar_f a2)).
Proof.
intros; rewrite subst_rtyp_in_rlist_open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_open_rlist_wrt_rtyp_var : lngen.

Lemma subst_rtyp_in_rt_open_rt_wrt_rtyp_var :
forall u1 r1 a1 a2,
  a1 <> a2 ->
  lc_rtyp r1 ->
  open_rt_wrt_rtyp (subst_rtyp_in_rt r1 a1 u1) (r_TyVar_f a2) = subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp u1 (r_TyVar_f a2)).
Proof.
intros; rewrite subst_rtyp_in_rt_open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_open_rt_wrt_rtyp_var : lngen.

Lemma subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_var :
forall r2 r1 a1 a2,
  a1 <> a2 ->
  lc_rtyp r1 ->
  open_rtyp_wrt_rtyp (subst_rtyp_in_rtyp r1 a1 r2) (r_TyVar_f a2) = subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp r2 (r_TyVar_f a2)).
Proof.
intros; rewrite subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_open_rtyp_wrt_rtyp_var : lngen.

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rtyp_var :
forall re1 r1 a1 a2,
  a1 <> a2 ->
  lc_rtyp r1 ->
  open_rexp_wrt_rtyp (subst_rtyp_in_rexp r1 a1 re1) (r_TyVar_f a2) = subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp re1 (r_TyVar_f a2)).
Proof.
intros; rewrite subst_rtyp_in_rexp_open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_open_rexp_wrt_rtyp_var : lngen.

Lemma subst_rtyp_in_rexp_open_rexp_wrt_rexp_var :
forall re1 r1 a1 x1,
  open_rexp_wrt_rexp (subst_rtyp_in_rexp r1 a1 re1) (re_Var_f x1) = subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp re1 (re_Var_f x1)).
Proof.
intros; rewrite subst_rtyp_in_rexp_open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_open_rexp_wrt_rexp_var : lngen.

Lemma subst_rexp_in_rexp_open_rexp_wrt_rtyp_var :
forall re2 re1 x1 a1,
  lc_rexp re1 ->
  open_rexp_wrt_rtyp (subst_rexp_in_rexp re1 x1 re2) (r_TyVar_f a1) = subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp re2 (r_TyVar_f a1)).
Proof.
intros; rewrite subst_rexp_in_rexp_open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_open_rexp_wrt_rtyp_var : lngen.

Lemma subst_rexp_in_rexp_open_rexp_wrt_rexp_var :
forall re2 re1 x1 x2,
  x1 <> x2 ->
  lc_rexp re1 ->
  open_rexp_wrt_rexp (subst_rexp_in_rexp re1 x1 re2) (re_Var_f x2) = subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp re2 (re_Var_f x2)).
Proof.
intros; rewrite subst_rexp_in_rexp_open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_open_rexp_wrt_rexp_var : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_spec_rec_subst_rtyp_in_rt_spec_rec_subst_rtyp_in_rtyp_spec_rec_mutual :
(forall R1 r1 a1 n1,
  subst_rtyp_in_rlist r1 a1 R1 = open_rlist_wrt_rtyp_rec n1 r1 (close_rlist_wrt_rtyp_rec n1 a1 R1)) /\
(forall u1 r1 a1 n1,
  subst_rtyp_in_rt r1 a1 u1 = open_rt_wrt_rtyp_rec n1 r1 (close_rt_wrt_rtyp_rec n1 a1 u1)) /\
(forall r1 r2 a1 n1,
  subst_rtyp_in_rtyp r2 a1 r1 = open_rtyp_wrt_rtyp_rec n1 r2 (close_rtyp_wrt_rtyp_rec n1 a1 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rlist_spec_rec :
forall R1 r1 a1 n1,
  subst_rtyp_in_rlist r1 a1 R1 = open_rlist_wrt_rtyp_rec n1 r1 (close_rlist_wrt_rtyp_rec n1 a1 R1).
Proof.
pose proof subst_rtyp_in_rlist_spec_rec_subst_rtyp_in_rt_spec_rec_subst_rtyp_in_rtyp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rt_spec_rec :
forall u1 r1 a1 n1,
  subst_rtyp_in_rt r1 a1 u1 = open_rt_wrt_rtyp_rec n1 r1 (close_rt_wrt_rtyp_rec n1 a1 u1).
Proof.
pose proof subst_rtyp_in_rlist_spec_rec_subst_rtyp_in_rt_spec_rec_subst_rtyp_in_rtyp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rtyp_spec_rec :
forall r1 r2 a1 n1,
  subst_rtyp_in_rtyp r2 a1 r1 = open_rtyp_wrt_rtyp_rec n1 r2 (close_rtyp_wrt_rtyp_rec n1 a1 r1).
Proof.
pose proof subst_rtyp_in_rlist_spec_rec_subst_rtyp_in_rt_spec_rec_subst_rtyp_in_rtyp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_spec_rec_mutual :
(forall re1 r1 a1 n1,
  subst_rtyp_in_rexp r1 a1 re1 = open_rexp_wrt_rtyp_rec n1 r1 (close_rexp_wrt_rtyp_rec n1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_spec_rec :
forall re1 r1 a1 n1,
  subst_rtyp_in_rexp r1 a1 re1 = open_rexp_wrt_rtyp_rec n1 r1 (close_rexp_wrt_rtyp_rec n1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_spec_rec_mutual :
(forall re1 re2 x1 n1,
  subst_rexp_in_rexp re2 x1 re1 = open_rexp_wrt_rexp_rec n1 re2 (close_rexp_wrt_rexp_rec n1 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_spec_rec :
forall re1 re2 x1 n1,
  subst_rexp_in_rexp re2 x1 re1 = open_rexp_wrt_rexp_rec n1 re2 (close_rexp_wrt_rexp_rec n1 x1 re1).
Proof.
pose proof subst_rexp_in_rexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_spec_rec : lngen.

(* end hide *)

Lemma subst_rtyp_in_rlist_spec :
forall R1 r1 a1,
  subst_rtyp_in_rlist r1 a1 R1 = open_rlist_wrt_rtyp (close_rlist_wrt_rtyp a1 R1) r1.
Proof.
unfold close_rlist_wrt_rtyp; unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_spec : lngen.

Lemma subst_rtyp_in_rt_spec :
forall u1 r1 a1,
  subst_rtyp_in_rt r1 a1 u1 = open_rt_wrt_rtyp (close_rt_wrt_rtyp a1 u1) r1.
Proof.
unfold close_rt_wrt_rtyp; unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_spec : lngen.

Lemma subst_rtyp_in_rtyp_spec :
forall r1 r2 a1,
  subst_rtyp_in_rtyp r2 a1 r1 = open_rtyp_wrt_rtyp (close_rtyp_wrt_rtyp a1 r1) r2.
Proof.
unfold close_rtyp_wrt_rtyp; unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_spec : lngen.

Lemma subst_rtyp_in_rexp_spec :
forall re1 r1 a1,
  subst_rtyp_in_rexp r1 a1 re1 = open_rexp_wrt_rtyp (close_rexp_wrt_rtyp a1 re1) r1.
Proof.
unfold close_rexp_wrt_rtyp; unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_spec : lngen.

Lemma subst_rexp_in_rexp_spec :
forall re1 re2 x1,
  subst_rexp_in_rexp re2 x1 re1 = open_rexp_wrt_rexp (close_rexp_wrt_rexp x1 re1) re2.
Proof.
unfold close_rexp_wrt_rexp; unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_spec : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_subst_rtyp_in_rlist_subst_rtyp_in_rt_subst_rtyp_in_rt_subst_rtyp_in_rtyp_subst_rtyp_in_rtyp_mutual :
(forall R1 r1 r2 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  subst_rtyp_in_rlist r1 a1 (subst_rtyp_in_rlist r2 a2 R1) = subst_rtyp_in_rlist (subst_rtyp_in_rtyp r1 a1 r2) a2 (subst_rtyp_in_rlist r1 a1 R1)) /\
(forall u1 r1 r2 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  subst_rtyp_in_rt r1 a1 (subst_rtyp_in_rt r2 a2 u1) = subst_rtyp_in_rt (subst_rtyp_in_rtyp r1 a1 r2) a2 (subst_rtyp_in_rt r1 a1 u1)) /\
(forall r1 r2 r3 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 <> a1 ->
  subst_rtyp_in_rtyp r2 a1 (subst_rtyp_in_rtyp r3 a2 r1) = subst_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r3) a2 (subst_rtyp_in_rtyp r2 a1 r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_subst_rtyp_in_rlist :
forall R1 r1 r2 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  subst_rtyp_in_rlist r1 a1 (subst_rtyp_in_rlist r2 a2 R1) = subst_rtyp_in_rlist (subst_rtyp_in_rtyp r1 a1 r2) a2 (subst_rtyp_in_rlist r1 a1 R1).
Proof.
pose proof subst_rtyp_in_rlist_subst_rtyp_in_rlist_subst_rtyp_in_rt_subst_rtyp_in_rt_subst_rtyp_in_rtyp_subst_rtyp_in_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_subst_rtyp_in_rlist : lngen.

Lemma subst_rtyp_in_rt_subst_rtyp_in_rt :
forall u1 r1 r2 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  subst_rtyp_in_rt r1 a1 (subst_rtyp_in_rt r2 a2 u1) = subst_rtyp_in_rt (subst_rtyp_in_rtyp r1 a1 r2) a2 (subst_rtyp_in_rt r1 a1 u1).
Proof.
pose proof subst_rtyp_in_rlist_subst_rtyp_in_rlist_subst_rtyp_in_rt_subst_rtyp_in_rt_subst_rtyp_in_rtyp_subst_rtyp_in_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_subst_rtyp_in_rt : lngen.

Lemma subst_rtyp_in_rtyp_subst_rtyp_in_rtyp :
forall r1 r2 r3 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 <> a1 ->
  subst_rtyp_in_rtyp r2 a1 (subst_rtyp_in_rtyp r3 a2 r1) = subst_rtyp_in_rtyp (subst_rtyp_in_rtyp r2 a1 r3) a2 (subst_rtyp_in_rtyp r2 a1 r1).
Proof.
pose proof subst_rtyp_in_rlist_subst_rtyp_in_rlist_subst_rtyp_in_rt_subst_rtyp_in_rt_subst_rtyp_in_rtyp_subst_rtyp_in_rtyp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_subst_rtyp_in_rtyp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_subst_rtyp_in_rexp_mutual :
(forall re1 r1 r2 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  subst_rtyp_in_rexp r1 a1 (subst_rtyp_in_rexp r2 a2 re1) = subst_rtyp_in_rexp (subst_rtyp_in_rtyp r1 a1 r2) a2 (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_subst_rtyp_in_rexp :
forall re1 r1 r2 a2 a1,
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  subst_rtyp_in_rexp r1 a1 (subst_rtyp_in_rexp r2 a2 re1) = subst_rtyp_in_rexp (subst_rtyp_in_rtyp r1 a1 r2) a2 (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_subst_rtyp_in_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_subst_rtyp_in_rexp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_subst_rexp_in_rexp_mutual :
(forall re1 r1 re2 x1 a1,
  subst_rtyp_in_rexp r1 a1 (subst_rexp_in_rexp re2 x1 re1) = subst_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re2) x1 (subst_rtyp_in_rexp r1 a1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_subst_rexp_in_rexp :
forall re1 r1 re2 x1 a1,
  subst_rtyp_in_rexp r1 a1 (subst_rexp_in_rexp re2 x1 re1) = subst_rexp_in_rexp (subst_rtyp_in_rexp r1 a1 re2) x1 (subst_rtyp_in_rexp r1 a1 re1).
Proof.
pose proof subst_rtyp_in_rexp_subst_rexp_in_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_subst_rexp_in_rexp : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_subst_rtyp_in_rexp_mutual :
(forall re1 re2 r1 a1 x1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  subst_rexp_in_rexp re2 x1 (subst_rtyp_in_rexp r1 a1 re1) = subst_rtyp_in_rexp r1 a1 (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_subst_rtyp_in_rexp :
forall re1 re2 r1 a1 x1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  subst_rexp_in_rexp re2 x1 (subst_rtyp_in_rexp r1 a1 re1) = subst_rtyp_in_rexp r1 a1 (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof subst_rexp_in_rexp_subst_rtyp_in_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_subst_rtyp_in_rexp : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_subst_rexp_in_rexp_mutual :
(forall re1 re2 re3 x2 x1,
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 <> x1 ->
  subst_rexp_in_rexp re2 x1 (subst_rexp_in_rexp re3 x2 re1) = subst_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re3) x2 (subst_rexp_in_rexp re2 x1 re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_subst_rexp_in_rexp :
forall re1 re2 re3 x2 x1,
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 <> x1 ->
  subst_rexp_in_rexp re2 x1 (subst_rexp_in_rexp re3 x2 re1) = subst_rexp_in_rexp (subst_rexp_in_rexp re2 x1 re3) x2 (subst_rexp_in_rexp re2 x1 re1).
Proof.
pose proof subst_rexp_in_rexp_subst_rexp_in_rexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_subst_rexp_in_rexp : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual :
(forall R1 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rlist R1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rlist r1 a1 R1 = close_rlist_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a2) R1))) *
(forall u1 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rt u1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rt r1 a1 u1 = close_rt_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a2) u1))) *
(forall r2 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rtyp r1 a1 r2 = close_rtyp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a2) r2))).
Proof.
apply rlist_rt_rtyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec :
forall R1 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rlist R1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rlist r1 a1 R1 = close_rlist_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a2) R1)).
Proof.
pose proof subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec :
forall u1 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rt u1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rt r1 a1 u1 = close_rt_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a2) u1)).
Proof.
pose proof subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec :
forall r2 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rtyp r1 a1 r2 = close_rtyp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a2) r2)).
Proof.
pose proof subst_rtyp_in_rlist_close_rlist_wrt_rtyp_rec_open_rlist_wrt_rtyp_rec_subst_rtyp_in_rt_close_rt_wrt_rtyp_rec_open_rt_wrt_rtyp_rec_subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_rec_open_rtyp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec_mutual :
(forall re1 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rexp re1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rexp r1 a1 re1 = close_rexp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a2) re1))).
Proof.
apply_mutual_ind rexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec :
forall re1 r1 a1 a2 n1,
  a2 `notin` fv_rtyp_in_rexp re1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  degree_rtyp_wrt_rtyp n1 r1 ->
  subst_rtyp_in_rexp r1 a1 re1 = close_rexp_wrt_rtyp_rec n1 a2 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a2) re1)).
Proof.
pose proof subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec_mutual :
(forall re1 r1 a1 x1 n1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  subst_rtyp_in_rexp r1 a1 re1 = close_rexp_wrt_rexp_rec n1 x1 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1))).
Proof.
apply_mutual_ind rexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec :
forall re1 r1 a1 x1 n1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  subst_rtyp_in_rexp r1 a1 re1 = close_rexp_wrt_rexp_rec n1 x1 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1)).
Proof.
pose proof subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec_mutual :
(forall re2 re1 x1 a1 n1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  degree_rexp_wrt_rtyp n1 re1 ->
  subst_rexp_in_rexp re1 x1 re2 = close_rexp_wrt_rtyp_rec n1 a1 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re2))).
Proof.
apply_mutual_ind rexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec :
forall re2 re1 x1 a1 n1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  degree_rexp_wrt_rtyp n1 re1 ->
  subst_rexp_in_rexp re1 x1 re2 = close_rexp_wrt_rtyp_rec n1 a1 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re2)).
Proof.
pose proof subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rtyp_rec_open_rexp_wrt_rtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec_mutual :
(forall re2 re1 x1 x2 n1,
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 `notin` fv_rexp_in_rexp re1 ->
  x2 <> x1 ->
  degree_rexp_wrt_rexp n1 re1 ->
  subst_rexp_in_rexp re1 x1 re2 = close_rexp_wrt_rexp_rec n1 x2 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x2) re2))).
Proof.
apply_mutual_ind rexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_rexp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec :
forall re2 re1 x1 x2 n1,
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 `notin` fv_rexp_in_rexp re1 ->
  x2 <> x1 ->
  degree_rexp_wrt_rexp n1 re1 ->
  subst_rexp_in_rexp re1 x1 re2 = close_rexp_wrt_rexp_rec n1 x2 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x2) re2)).
Proof.
pose proof subst_rexp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rexp_rec_open_rexp_wrt_rexp_rec : lngen.

(* end hide *)

Lemma subst_rtyp_in_rlist_close_rlist_wrt_rtyp_open_rlist_wrt_rtyp :
forall R1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rlist R1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  lc_rtyp r1 ->
  subst_rtyp_in_rlist r1 a1 R1 = close_rlist_wrt_rtyp a2 (subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp R1 (r_TyVar_f a2))).
Proof.
unfold close_rlist_wrt_rtyp; unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_close_rlist_wrt_rtyp_open_rlist_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rt_close_rt_wrt_rtyp_open_rt_wrt_rtyp :
forall u1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rt u1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  lc_rtyp r1 ->
  subst_rtyp_in_rt r1 a1 u1 = close_rt_wrt_rtyp a2 (subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp u1 (r_TyVar_f a2))).
Proof.
unfold close_rt_wrt_rtyp; unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_close_rt_wrt_rtyp_open_rt_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp :
forall r2 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rtyp r2 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  lc_rtyp r1 ->
  subst_rtyp_in_rtyp r1 a1 r2 = close_rtyp_wrt_rtyp a2 (subst_rtyp_in_rtyp r1 a1 (open_rtyp_wrt_rtyp r2 (r_TyVar_f a2))).
Proof.
unfold close_rtyp_wrt_rtyp; unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_close_rtyp_wrt_rtyp_open_rtyp_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rtyp_open_rexp_wrt_rtyp :
forall re1 r1 a1 a2,
  a2 `notin` fv_rtyp_in_rexp re1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 ->
  a2 <> a1 ->
  lc_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 re1 = close_rexp_wrt_rtyp a2 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp re1 (r_TyVar_f a2))).
Proof.
unfold close_rexp_wrt_rtyp; unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rtyp_open_rexp_wrt_rtyp : lngen.

Lemma subst_rtyp_in_rexp_close_rexp_wrt_rexp_open_rexp_wrt_rexp :
forall re1 r1 a1 x1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  lc_rtyp r1 ->
  subst_rtyp_in_rexp r1 a1 re1 = close_rexp_wrt_rexp x1 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp re1 (re_Var_f x1))).
Proof.
unfold close_rexp_wrt_rexp; unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_close_rexp_wrt_rexp_open_rexp_wrt_rexp : lngen.

Lemma subst_rexp_in_rexp_close_rexp_wrt_rtyp_open_rexp_wrt_rtyp :
forall re2 re1 x1 a1,
  a1 `notin` fv_rtyp_in_rexp re2 ->
  a1 `notin` fv_rtyp_in_rexp re1 ->
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 re2 = close_rexp_wrt_rtyp a1 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp re2 (r_TyVar_f a1))).
Proof.
unfold close_rexp_wrt_rtyp; unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rtyp_open_rexp_wrt_rtyp : lngen.

Lemma subst_rexp_in_rexp_close_rexp_wrt_rexp_open_rexp_wrt_rexp :
forall re2 re1 x1 x2,
  x2 `notin` fv_rexp_in_rexp re2 ->
  x2 `notin` fv_rexp_in_rexp re1 ->
  x2 <> x1 ->
  lc_rexp re1 ->
  subst_rexp_in_rexp re1 x1 re2 = close_rexp_wrt_rexp x2 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp re2 (re_Var_f x2))).
Proof.
unfold close_rexp_wrt_rexp; unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_close_rexp_wrt_rexp_open_rexp_wrt_rexp : lngen.

Lemma subst_rtyp_in_rt_rt_ConQuan :
forall a2 R1 rt1 r1 a1,
  lc_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rt rt1 `union` singleton a1 ->
  subst_rtyp_in_rt r1 a1 (rt_ConQuan R1 rt1) = rt_ConQuan (subst_rtyp_in_rlist r1 a1 R1) (close_rt_wrt_rtyp a2 (subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp rt1 (r_TyVar_f a2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_rt_ConQuan : lngen.

Lemma subst_rtyp_in_rexp_re_Abs :
forall x1 rt1 re1 r1 a1,
  lc_rtyp r1 ->
  x1 `notin` fv_rexp_in_rexp re1 ->
  subst_rtyp_in_rexp r1 a1 (re_Abs rt1 re1) = re_Abs (subst_rtyp_in_rt r1 a1 rt1) (close_rexp_wrt_rexp x1 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rexp re1 (re_Var_f x1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_re_Abs : lngen.

Lemma subst_rtyp_in_rexp_re_ConTyAbs :
forall a2 R1 re1 r1 a1,
  lc_rtyp r1 ->
  a2 `notin` fv_rtyp_in_rtyp r1 `union` fv_rtyp_in_rexp re1 `union` singleton a1 ->
  subst_rtyp_in_rexp r1 a1 (re_ConTyAbs R1 re1) = re_ConTyAbs (subst_rtyp_in_rlist r1 a1 R1) (close_rexp_wrt_rtyp a2 (subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp re1 (r_TyVar_f a2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_re_ConTyAbs : lngen.

Lemma subst_rexp_in_rexp_re_Abs :
forall x2 rt1 re2 re1 x1,
  lc_rexp re1 ->
  x2 `notin` fv_rexp_in_rexp re1 `union` fv_rexp_in_rexp re2 `union` singleton x1 ->
  subst_rexp_in_rexp re1 x1 (re_Abs rt1 re2) = re_Abs (rt1) (close_rexp_wrt_rexp x2 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rexp re2 (re_Var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_re_Abs : lngen.

Lemma subst_rexp_in_rexp_re_ConTyAbs :
forall a1 R1 re2 re1 x1,
  lc_rexp re1 ->
  a1 `notin` fv_rtyp_in_rexp re1 `union` fv_rtyp_in_rexp re2 ->
  subst_rexp_in_rexp re1 x1 (re_ConTyAbs R1 re2) = re_ConTyAbs (R1) (close_rexp_wrt_rtyp a1 (subst_rexp_in_rexp re1 x1 (open_rexp_wrt_rtyp re2 (r_TyVar_f a1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_re_ConTyAbs : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rlist_intro_rec_subst_rtyp_in_rt_intro_rec_subst_rtyp_in_rtyp_intro_rec_mutual :
(forall R1 a1 r1 n1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  open_rlist_wrt_rtyp_rec n1 r1 R1 = subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1)) /\
(forall u1 a1 r1 n1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  open_rt_wrt_rtyp_rec n1 r1 u1 = subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1)) /\
(forall r1 a1 r2 n1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  open_rtyp_wrt_rtyp_rec n1 r2 r1 = subst_rtyp_in_rtyp r2 a1 (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1)).
Proof.
apply rlist_rt_rtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rlist_intro_rec :
forall R1 a1 r1 n1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  open_rlist_wrt_rtyp_rec n1 r1 R1 = subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp_rec n1 (r_TyVar_f a1) R1).
Proof.
pose proof subst_rtyp_in_rlist_intro_rec_subst_rtyp_in_rt_intro_rec_subst_rtyp_in_rtyp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rlist_intro_rec : lngen.
Hint Rewrite subst_rtyp_in_rlist_intro_rec using solve [auto] : lngen.

Lemma subst_rtyp_in_rt_intro_rec :
forall u1 a1 r1 n1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  open_rt_wrt_rtyp_rec n1 r1 u1 = subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp_rec n1 (r_TyVar_f a1) u1).
Proof.
pose proof subst_rtyp_in_rlist_intro_rec_subst_rtyp_in_rt_intro_rec_subst_rtyp_in_rtyp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rt_intro_rec : lngen.
Hint Rewrite subst_rtyp_in_rt_intro_rec using solve [auto] : lngen.

Lemma subst_rtyp_in_rtyp_intro_rec :
forall r1 a1 r2 n1,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  open_rtyp_wrt_rtyp_rec n1 r2 r1 = subst_rtyp_in_rtyp r2 a1 (open_rtyp_wrt_rtyp_rec n1 (r_TyVar_f a1) r1).
Proof.
pose proof subst_rtyp_in_rlist_intro_rec_subst_rtyp_in_rt_intro_rec_subst_rtyp_in_rtyp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rtyp_intro_rec : lngen.
Hint Rewrite subst_rtyp_in_rtyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_rtyp_in_rexp_intro_rec_mutual :
(forall re1 a1 r1 n1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  open_rexp_wrt_rtyp_rec n1 r1 re1 = subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rtyp_in_rexp_intro_rec :
forall re1 a1 r1 n1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  open_rexp_wrt_rtyp_rec n1 r1 re1 = subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp_rec n1 (r_TyVar_f a1) re1).
Proof.
pose proof subst_rtyp_in_rexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rtyp_in_rexp_intro_rec : lngen.
Hint Rewrite subst_rtyp_in_rexp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_rexp_in_rexp_intro_rec_mutual :
(forall re1 x1 re2 n1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  open_rexp_wrt_rexp_rec n1 re2 re1 = subst_rexp_in_rexp re2 x1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1)).
Proof.
apply_mutual_ind rexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_rexp_in_rexp_intro_rec :
forall re1 x1 re2 n1,
  x1 `notin` fv_rexp_in_rexp re1 ->
  open_rexp_wrt_rexp_rec n1 re2 re1 = subst_rexp_in_rexp re2 x1 (open_rexp_wrt_rexp_rec n1 (re_Var_f x1) re1).
Proof.
pose proof subst_rexp_in_rexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_rexp_in_rexp_intro_rec : lngen.
Hint Rewrite subst_rexp_in_rexp_intro_rec using solve [auto] : lngen.

Lemma subst_rtyp_in_rlist_intro :
forall a1 R1 r1,
  a1 `notin` fv_rtyp_in_rlist R1 ->
  open_rlist_wrt_rtyp R1 r1 = subst_rtyp_in_rlist r1 a1 (open_rlist_wrt_rtyp R1 (r_TyVar_f a1)).
Proof.
unfold open_rlist_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rlist_intro : lngen.

Lemma subst_rtyp_in_rt_intro :
forall a1 u1 r1,
  a1 `notin` fv_rtyp_in_rt u1 ->
  open_rt_wrt_rtyp u1 r1 = subst_rtyp_in_rt r1 a1 (open_rt_wrt_rtyp u1 (r_TyVar_f a1)).
Proof.
unfold open_rt_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rt_intro : lngen.

Lemma subst_rtyp_in_rtyp_intro :
forall a1 r1 r2,
  a1 `notin` fv_rtyp_in_rtyp r1 ->
  open_rtyp_wrt_rtyp r1 r2 = subst_rtyp_in_rtyp r2 a1 (open_rtyp_wrt_rtyp r1 (r_TyVar_f a1)).
Proof.
unfold open_rtyp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rtyp_intro : lngen.

Lemma subst_rtyp_in_rexp_intro :
forall a1 re1 r1,
  a1 `notin` fv_rtyp_in_rexp re1 ->
  open_rexp_wrt_rtyp re1 r1 = subst_rtyp_in_rexp r1 a1 (open_rexp_wrt_rtyp re1 (r_TyVar_f a1)).
Proof.
unfold open_rexp_wrt_rtyp; default_simp.
Qed.

Hint Resolve subst_rtyp_in_rexp_intro : lngen.

Lemma subst_rexp_in_rexp_intro :
forall x1 re1 re2,
  x1 `notin` fv_rexp_in_rexp re1 ->
  open_rexp_wrt_rexp re1 re2 = subst_rexp_in_rexp re2 x1 (open_rexp_wrt_rexp re1 (re_Var_f x1)).
Proof.
unfold open_rexp_wrt_rexp; default_simp.
Qed.

Hint Resolve subst_rexp_in_rexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
