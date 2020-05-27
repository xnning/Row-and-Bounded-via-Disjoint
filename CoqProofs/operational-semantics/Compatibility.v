
Require Import Infrastructure.
Require Import SourceProperty.
Require Import LR.
Require Import Assumed.
Require Import TargetProperty.
Require Import Disjoint.




(* ********************************************************************** *)
(** * Coercion Compatibility *)


Lemma E_coercion2 : forall A1 A2 A0 c p d d' e1 e2,
    sub d' A1 A2 c ->
    same_stctx d d' ->
    swfte d ->
    rel_d d p ->
    E A0 (mtsubst_in_sty p A1) e2 e1 ->
    E A0 (mtsubst_in_sty p A2) e2 (exp_capp c e1).
Proof with eauto.
  introv ? ? ? ? EH.
  apply E_sym in EH.
  apply E_sym.
  eapply E_coercion1...
Qed.

Lemma coercion_compatibility1 : forall A0 A1 A2 c D G e1 e2,
    sub D A1 A2 c ->
    swfte D ->
    E_open D G e1 e2 A1 A0 ->
    E_open D G (exp_capp c e1) e2 A2 A0.
Proof with eauto using subtype_well_type, swft_wft, E_coercion1.
  introv Sub Uniq H.
  destruct H as (? & ? & ? & ? & EH).

  lets (? & ?): sub_regular Sub.

  splits...
  introv RelD RelG.
  specializes EH RelD RelG.
  autorewrite with lr_rewrite...
Qed.


Lemma coercion_compatibility2 : forall A0 A1 A2 c D G e1 e2,
    sub D A1 A2 c ->
    swfte D ->
    E_open D G e1 e2 A0 A1 ->
    E_open D G e1 (exp_capp c e2) A0 A2.
Proof with eauto using subtype_well_type, swft_wft, E_coercion2.
  introv Sub Uniq H.
  destruct H as (? & ? & ? & ? & EH).

  lets (? & ?): sub_regular Sub.

  splits...
  introv RelD RelG.
  specializes EH RelD RelG.
  autorewrite with lr_rewrite...
Qed.




Hint Extern 1 (swfte ?E) =>
  match goal with
  | H: has_type _ _ _ _ _ _ |- _ => apply (proj2 (proj2 (proj2 (styping_regular _ _ _ _ _ _ H))))
  end.


Hint Extern 1 (swft ?A ?B) =>
  match goal with
  | H: has_type _ _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 (styping_regular _ _ _ _ _ _ H))))
  end.


Lemma disjoint_compatibility : forall Δ Γ E1 e1 A1 E2 e2 A2 dir dir',
    has_type Δ Γ E1 dir A1 e1 ->
    has_type Δ Γ E2 dir' A2 e2 ->
    disjoint Δ A1 A2 ->
    E_open Δ Γ e1 e2 A1 A2.
Proof with eauto using swft_wft, swfe_wfe, elaboration_well_type, swft_from_swfe, mtsubst_swft, uniq_from_swfte.
  introv Ty1 Ty2 Dis.
  splits...
  introv RelD RelG.
  forwards (? & ?): rel_d_uniq RelD.
  forwards : rel_d_same RelD...
  forwards Ty3 : elaboration_well_type Ty1...
  forwards Ty4 : elaboration_well_type Ty2...
  forwards (Ty5 & ?) : subst_close RelD RelG Ty3.
  forwards (? & Ty6) : subst_close RelD RelG Ty4.
  splits...
  lets (v1 & ? & ?) : normalization Ty5.
  lets (v2 & ? & ?) : normalization Ty6.
  exists v1 v2.
  splits...
  eapply disjoint_value...
  apply preservation_multi_step with (e := msubst_in_exp g1 (mtsubst_in_exp p e1))...
  apply preservation_multi_step with (e := msubst_in_exp g2 (mtsubst_in_exp p e2))...
Qed.


(* ********************************************************************** *)
(** * Pair compatibility *)

Lemma pair_compatibility : forall D G e1 e2 e1' e2' A B A' B',
    E_open D G e1 e1' A A' ->
    E_open D G e2 e2' B B' ->
    swfte D ->
    disjoint D A B' ->
    disjoint D A' B ->
    E_open D G (exp_pair e1 e2) (exp_pair e1' e2') (sty_and A B) (sty_and A' B').
Proof with eauto using preservation_multi_step.
  introv EH1 EH2 Wfte Dis1 Dis2.

  destruct EH1 as (? & ? & ? & ? & EH1).
  destruct EH2 as (? & ? & ? & ? & EH2).

  splits; simpls...
  introv RelD RelG.
  specializes EH1 RelD RelG.
  specializes EH2 RelD RelG.

  destruct EH1 as (? & ? & ? & ? & v1 & v1' & ? & ? & ? & ? & VH1).
  destruct EH2 as (? & ? & ? & ? & v2 & v2' & ? & ? & ? & ? & VH2).

  splits; autorewrite with lr_rewrite; simpls...

  exists (exp_pair v1 v2) (exp_pair v1' v2').
  splits...

  apply V_andl...
  splits...
  apply V_andr...
  splits...
  eapply disjoint_value...
  apply V_andr...
  splits...
  eapply disjoint_value...
  eapply disjoint_symmetric...
Qed.

