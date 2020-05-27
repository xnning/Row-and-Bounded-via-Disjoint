Require Export LibTactics.
Require Export Metalib.Metatheory.
Require Import Syntax_ott.
Require Import Row_inf.
Require Import Fii_inf.
Require Import Infrastructure.

Set Implicit Arguments.



Fixpoint fv_Gtx (Gtx : GContext) {struct Gtx} : vars :=
  match Gtx with
  | nil            => {}
  | cons (x, y) P' => fv_rtyp_in_rt y \u fv_Gtx P'
  end.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C3 := gather_atoms_with (fun x : stctx => dom x) in
  let C4 := gather_atoms_with (fun x : sctx => dom x) in
  let D4 := gather_atoms_with (fun x => fv_sty_in_sty x) in
  let D5 := gather_atoms_with (fun x => fv_sty_in_sexp x) in
  let D6 := gather_atoms_with (fun x => fv_sexp_in_sexp x) in
  let D8 := gather_atoms_with (fun x => fv_rtyp_in_rtyp x) in
  let D9 := gather_atoms_with (fun x => fv_rtyp_in_rlist x) in
  let D10 := gather_atoms_with (fun x => fv_rtyp_in_rt x) in
  let D11 := gather_atoms_with (fun x => fv_rexp_in_rexp x) in
  let D12 := gather_atoms_with (fun x => fv_rtyp_in_rexp x) in
  let D13 := gather_atoms_with (fun x : GContext => dom x) in
  let D14 := gather_atoms_with (fun x : PContext => dom x) in
  let D15 := gather_atoms_with (fun x => fv_rtyp_in_rt x) in
  let D16 := gather_atoms_with (fun x : TContext => dom x) in
  let D17 := gather_atoms_with (fun x : GContext => fv_Gtx x) in
  let D18 := gather_atoms_with (fun x : PContext => fv_Ptx x) in
  let D19 := gather_atoms_with (fun x : stctx => fv_stctx x) in
  constr:(A \u B \u C3 \u C4 \u D4 \u D5 \u D6 \u D8 \u D9 \u D10 \u D11 \u D12 \u D13 \u D14 \u D15 \u D16 \u D17 \u D18 \u D19).

Lemma fv_notin_open_sty_wrt_sty_rec : forall B X i A,
    X \notin fv_sty_in_sty A  ->
    X \notin fv_sty_in_sty B  ->
    X \notin fv_sty_in_sty (open_sty_wrt_sty_rec i A B).
Proof with eauto.
  intro B. inductions B; introv H1 H2; simpls...
  destruct (lt_eq_lt_dec n i); simpls...
  destruct s; simpls...
Qed.

(* ********************************************************************** *)
(** * Locally Closed *)

Lemma lc_rt_from_wfrt : forall Ttx rt,
    wfrt Ttx rt ->
    lc_rt rt
with lc_rtyp_from_wfr : forall Ttx r,
    wfr Ttx r ->
    lc_rtyp r
with lc_rlist_from_wfcl : forall Ttx R,
    wfcl Ttx R ->
    lc_rlist R.
Proof with eauto.
  -
  induction 1; constructor; auto.
  + eapply lc_rlist_from_wfcl...
  + introv.
    pick_fresh X.
    forwards ~ : H1 X.
    rewrite subst_rtyp_in_rt_intro with (r1:=r_TyVar_f a) (a1:=X)...
    apply subst_rtyp_in_rt_lc_rt...
  + eapply lc_rtyp_from_wfr...

  -
    induction 1; constructor; auto.
    eapply lc_rt_from_wfrt...

  -
    induction 1; constructor; auto.
    eapply lc_rtyp_from_wfr...
Qed.

Lemma lc_sty_from_swft : forall DD B,
    swft DD B ->
    lc_sty B.
Proof with eauto.
  induction 1...
Qed.
Hint Resolve lc_rt_from_wfrt lc_rt_from_wfrt lc_rlist_from_wfcl lc_sty_from_swft : lngen.


(* ********************************************************************** *)
(** * Wellformedness *)

Lemma wfrt_from_binds_wfc: forall Ttx Gtx x rt,
    wfc Ttx Gtx ->
    binds x rt Gtx ->
    wfrt Ttx rt.
Proof.
  introv H BD. induction H.
  false.
  apply binds_cons_1 in BD.
  destruct BD as [ [I1 I2] | I3 ];
  substs; auto.
Qed.

Lemma uniq_from_wfc : forall T G,
    wfc T G ->
    uniq G.
Proof with eauto.
  induction 1...
Qed.

Ltac destruct_hypo :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Ltac invert_wfrt :=
  match goal with
  | H : wfrt _ (rt_Record _) |- _ => inverts H
  end.


Lemma cmp_regular : forall Ttx r1 r2,
    cmp Ttx r1 r2 ->
    wfr Ttx r1 /\ wfr Ttx r2
with teq_regular : forall Ttx rt1 rt2,
    teq Ttx rt1 rt2 ->
    wfrt Ttx rt1 /\ wfrt Ttx rt2
with ceq_regular : forall Ttx R1 R2,
    ceq Ttx R1 R2 ->
    wfcl Ttx R1 /\ wfcl Ttx R2.
Proof with eauto.
  -
  induction 1; repeat destruct_hypo; splits...
  + apply teq_regular in H0. destruct_hypo. repeat invert_wfrt...
  + apply teq_regular in H1. destruct_hypo. repeat invert_wfrt...
  + inversions H1...
  + inversions H1...

  -
  induction 1; repeat destruct_hypo; splits; try (solve[repeat invert_wfrt; eauto])...
  + pick fresh X and apply wfrt_All.
    apply ceq_regular in H. destruct_hypo...
    forwards ~ [? ?] : H1 X.
  + pick fresh X and apply wfrt_All.
    apply ceq_regular in H. destruct_hypo...
    forwards ~ : H3 X. destruct_hypo...
  + lets: cmp_regular H. lets: cmp_regular H0.
  repeat destruct_hypo...
  + lets: cmp_regular H. lets: cmp_regular H0.
  repeat destruct_hypo...
  constructor...
  constructor...
  + lets: cmp_regular H. repeat destruct_hypo...
  + lets: cmp_regular H. repeat destruct_hypo...

  -
  induction 1; repeat destruct_hypo; splits...
  + lets: teq_regular H0. destruct_hypo... repeat invert_wfrt...
  + lets: teq_regular H0. destruct_hypo... repeat invert_wfrt...
  + inversions H...
Qed.

Lemma cmpList_wfr: forall Ttx r R,
    cmpList Ttx r R ->
    wfr Ttx r.
Proof with eauto.
  induction 1...
Qed.

Lemma wftc_from_wfc : forall T G,
    wfc T G ->
    wftc T.
Proof with eauto.
  introv WFC.
  induction WFC; simpls...
Qed.


Lemma wftc_uniq : forall Ttx,
    wftc Ttx ->
    uniq Ttx.
Proof with eauto.
  introv WFTC.
  induction WFTC; simpls...
Qed.

Hint Resolve wftc_uniq.



Lemma empty_cmp : forall Ttx R,
    wfcl Ttx R ->
    cmpList Ttx r_Empty R.
Proof with eauto.
  introv WFCL.
  induction WFCL; simpls...
Qed.


Hint Resolve empty_cmp.

Lemma wftc_strength: forall E G,
    wftc (E ++ G) ->
    wftc G.
Proof with eauto.
  intros E.
  alist induction E; introv WFTC; simpls...
  inverts WFTC.
  eapply IHE...
Qed.


Lemma map_subst_rtyp_in_binding_id : forall G Z P,
  Z `notin` fv_Gtx G ->
  G = map (subst_rtyp_in_rt P Z) G.
Proof with eauto.
  intros G.
  induction G; intros...

  destruct a.
  rewrite map_cons.
  simpls.
  f_equal; simpls...

  rewrite subst_rtyp_in_rt_fresh_eq; simpls...
Qed.




Hint Extern 1 (wfr ?E ?t) =>
  match goal with
  | H: cmpList E t _ |- _ => apply (cmpList_wfr H)
  end.

Hint Extern 1 (wfr ?E ?t) =>
  match goal with
  | H: cmp E t _ |- _ => apply (proj1 (cmp_regular H))
  | H: cmp E _ t |- _ => apply (proj2 (cmp_regular H))
  end.

Hint Extern 1 (wfrt ?E ?t) =>
  match goal with
  | H: teq E t _ |- _ => apply (proj1 (teq_regular H))
  | H: teq E _ t |- _ => apply (proj2 (teq_regular H))
  end.

Hint Extern 1 (wfcl ?E ?t) =>
  match goal with
  | H: ceq E t _ |- _ => apply (proj1 (ceq_regular H))
  | H: ceq E _ t |- _ => apply (proj2 (ceq_regular H))
  end.

Lemma cmpList_wfcl: forall Ttx r R,
    cmpList Ttx r R ->
    wftc Ttx ->
    wfcl Ttx R.
Proof with eauto.
  introv H1 H2. inductions H1...
Qed.


Hint Extern 1 (wfcl ?E ?t) =>
  match goal with
  | H: cmpList E _ t |- _ => apply (cmpList_wfcl H)
  end.

(* ********************************************************************** *)
(** * WEAKENING *)

Scheme wfcl_ind := Induction for wfcl Sort Prop
  with wfrt_ind := Induction for wfrt Sort Prop
  with wfr_ind  := Induction for wfr Sort Prop
  with cmp_ind  := Induction for cmp Sort Prop
  with ceq_ind  := Induction for ceq Sort Prop
  with teq_ind  := Induction for teq Sort Prop.

Combined Scheme wfrt_mutind from wfcl_ind, wfrt_ind, wfr_ind, cmp_ind, ceq_ind, teq_ind.

Lemma wf_general_weakening :
  (forall T R,
      wfcl T R ->
        forall G E F,
          T = G ++ E ->
          wftc (G ++ F ++ E) ->
          wfcl (G ++ F ++ E) R)
  /\ (
    forall T R,
      wfrt T R ->
      forall G E F,
        T = G ++ E ->
        wftc (G ++ F ++ E) ->
        wfrt (G ++ F ++ E) R)
  /\ (
    forall T R,
      wfr T R ->
      forall G E F,
          T = G ++ E ->
          wftc (G ++ F ++ E) ->
          wfr (G ++ F ++ E) R)
  /\ (
    forall T R1 R2,
      cmp T R1 R2 ->
      wfr T R1 /\ wfr T R2 /\
      forall G E F,
          T = G ++ E ->
          wftc (G ++ F ++ E) ->
          cmp (G ++ F ++ E) R1 R2)
  /\ (
    forall T R1 R2,
      ceq T R1 R2 ->
      wfcl T R1 /\ wfcl T R2 /\
      forall G E F,
          T = G ++ E ->
          wftc (G ++ F ++ E) ->
          ceq (G ++ F ++ E) R1 R2)
  /\(
    forall T R1 R2,
      teq T R1 R2 ->
      wfrt T R1 /\ wfrt T R2 /\
      forall G E F,
          T = G ++ E ->
          wftc (G ++ F ++ E) ->
          teq (G ++ F ++ E) R1 R2)
.
Proof with eauto.
  apply wfrt_mutind; intros; repeat destruct_hypo; substs; try splits;
    intros; substs;
    repeat invert_wfrt...
  -
  pick fresh X and apply wfrt_All...
  rewrite_env ((([(X, R)] ++ G) ++ F ++ E)).
  apply H0...
  simpl_env...
  - inverts H0...
  - inverts H0...
  - inverts w...
  - pick fresh X and apply wfrt_All...
    forwards ~ : H0 X.
    repeat destruct_hypo...
  - pick fresh X and apply wfrt_All...
    forwards ~ : H1 X.
    repeat destruct_hypo...
  - pick fresh X and apply teq_CongAll...
    rewrite_env ((([(X, R)] ++ G) ++ F ++ E)).
    apply H0... simpl. constructor...
    forwards ~ : H3 G E F...
    rewrite_env ((([(X, R')] ++ G) ++ F ++ E)).
    apply H1... simpl. constructor...
    forwards ~ : H3 G E F...
  - intros. subst...
    apply teq_CongMerge...
  - apply wfrt_Rec.
    constructor...
Qed.

Lemma wfcl_weakening : forall R G E F,
    wfcl (G ++ E) R ->
    wftc (G ++ F ++ E) ->
    wfcl (G ++ F ++ E) R.
Proof.
  intros.
  pose (proj1 wf_general_weakening) as I.
  eapply I; eauto.
Qed.

Lemma wfcl_weakening_head : forall R E F,
    wfcl E R ->
    wftc (F ++ E) ->
    wfcl (F ++ E) R.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply wfcl_weakening; eauto.
Qed.

Lemma wfcl_weakening_tail : forall R E G,
    wfcl G R ->
    wftc (G ++ E) ->
    wfcl (G ++ E) R.
Proof with eauto.
  intros.
  rewrite_env (G ++ E ++ nil).
  apply wfcl_weakening; simpl_env...
Qed.


Lemma wfcl_from_binds_wftc: forall Ttx a A,
  wftc Ttx ->
  binds a A Ttx ->
  wfcl Ttx A.
Proof with eauto.
  introv H BD. induction H.
  false.
  apply binds_cons_1 in BD.
  destruct BD as [ [I1 I2] | I3 ];
  substs;
  apply wfcl_weakening_head...
Qed.

Lemma wfr_weakening : forall R G E F,
    wfr (G ++ E) R ->
    wftc (G ++ F ++ E) ->
    wfr (G ++ F ++ E) R.
Proof.
  intros.
  pose (proj1 (proj2 (proj2 wf_general_weakening))) as I.
  eapply I; eauto.
Qed.

Lemma wfr_weakening_head : forall R E F,
    wfr E R ->
    wftc (F ++ E) ->
    wfr (F ++ E) R.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply wfr_weakening; eauto.
Qed.

Lemma wfr_weakening_tail : forall R E G,
    wfr G R ->
    wftc (G ++ E) ->
    wfr (G ++ E) R.
Proof with eauto.
  intros.
  rewrite_env (G ++ E ++ nil).
  apply wfr_weakening; simpl_env...
Qed.

Lemma wfrt_weakening : forall R G E F,
    wfrt (G ++ E) R ->
    wftc (G ++ F ++ E) ->
    wfrt (G ++ F ++ E) R.
Proof.
  intros.
  pose ((proj1 (proj2 wf_general_weakening))) as I.
  eapply I; eauto.
Qed.

Lemma wfrt_weakening_head : forall R E F,
    wfrt E R ->
    wftc (F ++ E) ->
    wfrt (F ++ E) R.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply wfrt_weakening; eauto.
Qed.

Lemma wfrt_weakening_tail : forall R E G,
    wfrt G R ->
    wftc (G ++ E) ->
    wfrt (G ++ E) R.
Proof with eauto.
  intros.
  rewrite_env (G ++ E ++ nil).
  apply wfrt_weakening; simpl_env...
Qed.

Lemma cmp_weakening : forall G E F A B,
    cmp (G ++ E) A B ->
    wftc (G ++ F ++ E) ->
    cmp (G ++ F ++ E) A B.
Proof.
  intros.
  pose (proj1 (proj2 (proj2 (proj2 wf_general_weakening))))  as I.
  eapply I; eauto.
Qed.

Lemma cmp_weakening_head : forall E F A B,
    cmp E A B ->
    wftc (F ++ E) ->
    cmp (F ++ E) A B.
Proof.
  intros. rewrite_env (nil ++ F ++ E).
  apply cmp_weakening; eauto.
Qed.

Lemma ceq_weakening : forall G E F R1 R2,
    ceq (G ++ E)  R1 R2 ->
    wftc (G ++ F ++ E) ->
    ceq (G ++ F ++ E) R1 R2.
Proof.
  intros.
  pose (proj1 (proj2 (proj2 (proj2 (proj2 wf_general_weakening))))) as I.
  eapply I; eauto.
Qed.

Lemma ceq_weakening_head : forall E F R1 R2,
    ceq E  R1 R2 ->
    wftc (F ++ E) ->
    ceq (F ++ E) R1 R2.
Proof.
  intros.
  rewrite_env (nil ++ F ++E).
  eapply ceq_weakening; simpl_env; auto.
Qed.

(* ********************************************************************** *)
(** * SAME TCTX *)


Inductive same_tctx : TContext -> TContext -> Prop :=
| same_empty : same_tctx nil nil
| same_cons : forall X A B s1 s2,
    ceq s1 A B ->
    ceq s2 A B ->
    wfcl s1 A ->
    wfcl s2 B ->
    same_tctx s1 s2 ->  same_tctx ([(X , A)] ++ s1) ([(X , B)] ++ s2).

Lemma same_tctx_dom : forall ctxa ctxb,
    same_tctx ctxa ctxb ->
    dom ctxa [=] dom ctxb.
Proof with eauto; try fsetdec.
  induction 1; simpls...
Qed.

Lemma same_tctx_var : forall s1 s2 X A,
    same_tctx s1 s2 ->
    binds X A s1 ->
    exists B, binds X B s2.
Proof with eauto.
  introv Eq.
  gen X A.
  induction Eq; introv I.

  analyze_binds I.

  analyze_binds I...
  lets (B0 & ?) : IHEq BindsTac.

  exists B0...
Qed.

Hint Constructors same_tctx.

Lemma same_tctx_refl : forall T,
    wftc T ->
    same_tctx T T.
Proof with eauto.
  introv WF. inductions WF...
Qed.

Lemma same_tctx_symm : forall T1 T2,
    same_tctx T1 T2 ->
    same_tctx T2 T1.
Proof with eauto.
  introv SA. inductions SA...
Qed.

Hint Immediate same_tctx_refl.
Lemma same_tctx_uniq: forall T1 T2,
    same_tctx T1 T2 ->
    uniq T1 ->
    uniq T2.
Proof.
  introv SA UN.
  inductions SA; auto.
  inverts UN.
  constructor; auto.
  rewrite same_tctx_dom; eauto.
  apply same_tctx_symm; auto.
Qed.

Lemma same_tctx_binds_ceq: forall T1 T2 R1 R2 a,
    wftc T1 ->
    wftc T2 ->
    same_tctx T1 T2 ->
    binds a R1 T1 ->
    binds a R2 T2 ->
    ceq T1 R1 R2 /\ ceq T2 R1 R2.
Proof.
  introv UNI1 UNI2 SA BD1 BD2.
  inductions SA.
  apply binds_nil_iff in BD1. contradiction.
  inverts UNI1.
  analyze_binds BD1.
  analyze_binds BD2.
  splits...
  apply ceq_weakening_head; auto...
  apply ceq_weakening_head; auto...
  rewrite same_tctx_dom in H8; eauto.
  forwards ~ : binds_dom_contradiction BindsTac H8. contradiction.
  analyze_binds BD2.
  forwards ~ : binds_dom_contradiction BindsTac H8. contradiction.
  inverts UNI2.
  forwards ~ [? ?]: IHSA; auto. 
  splits...
  apply ceq_weakening_head; auto...
  apply ceq_weakening_head; auto...
Qed.




(* ********************************************************************** *)
(** * FV *)

Scheme rlist_ind := Induction for wfcl Sort Prop
  with rt_ind    := Induction for wfrt Sort Prop
  with rtyp_ind  := Induction for wfr  Sort Prop.
Combined Scheme rlist_rt_mutind from rlist_ind, rt_ind, rtyp_ind.

Lemma notin_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec: forall A a B n,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rt A ->
    a `notin` fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n B A)
with  notin_fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec: forall A a B n,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rlist A ->
    a `notin` fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n B A)
with  notin_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec: forall A a B n,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rtyp A ->
    a `notin` fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n B A).
Proof.
  -
  intro A. induction A; introv NOT1 NOT2 ; simpls; auto.
  -
  intro A. induction A; introv NOT1 NOT2 ; simpls; auto.
  -
  intro A. induction A. introv I1; introv I2 . simpl.
  destruct (lt_eq_lt_dec n n0). destruct s; simpl; auto...
  simpl; auto.

  introv I1; introv I2 . simpl; auto.
  introv I1; introv I2 . simpl; auto.
  introv I1; introv I2 . simpl; auto.
  introv I1; introv I2 . simpl; auto.
  simpl in I2.
  apply notin_union.
  apply IHA1; auto.
  apply IHA2; auto.
Qed.

Lemma notin_fv_rtyp_in_rt_open_rt_wrt_rtyp: forall A a B,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rt A ->
    a `notin` fv_rtyp_in_rt (open_rt_wrt_rtyp A B).
Proof.
  introv I1 I2.
  unfold open_rt_wrt_rtyp.
  apply notin_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec; eauto.
Qed.

Lemma notin_fv_rtyp_in_rlist_open_rlist_wrt_rtyp: forall A a B,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rlist A ->
    a `notin` fv_rtyp_in_rlist (open_rlist_wrt_rtyp A B).
Proof.
  introv I1 I2.
  unfold open_rlist_wrt_rtyp.
  apply notin_fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec; eauto.
Qed.

Lemma  notin_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp: forall A a B,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rtyp A ->
    a `notin` fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp A B).
Proof.
  introv I1 I2.
  unfold open_rlist_wrt_rtyp.
  apply notin_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec; eauto.
Qed.

Lemma notin_Fv_rtyp_in_rt_open_rt_wrt_rtyp_inverse: forall A B a n,
    a `notin` fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n B A) ->
    a `notin` fv_rtyp_in_rt A
with notin_Fv_rtyp_in_rlist_open_rlist_wrt_rtyp_inverse: forall A B a n,
    a `notin` fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n B A) ->
    a `notin` fv_rtyp_in_rlist A
with notin_Fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_inverse: forall A B a n,
    a `notin` fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n B A) ->
    a `notin` fv_rtyp_in_rtyp A.
Proof with auto.
  -
    induction A; introv NOTIN; simpls...
    forwards ~ : IHA1. forwards ~ : IHA2.
    apply notin_union.
    apply notin_Fv_rtyp_in_rlist_open_rlist_wrt_rtyp_inverse with B n...
    apply IHA with B (S n)...
    apply notin_Fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_inverse with B n...
  -
    induction A; introv NOTIN; simpls...
    apply notin_union.
    apply notin_Fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_inverse with B n...
    apply IHA with B (n)...
  -
    induction A; introv NOTIN; simpls...
    apply notin_Fv_rtyp_in_rt_open_rt_wrt_rtyp_inverse with B n...
    apply notin_union.
    apply IHA1 with B n... apply IHA2 with B n...
Qed.

Lemma wfr_fresh : forall F r a,
    wfr F r ->
    a `notin` dom F ->
    a `notin` fv_rtyp_in_rtyp r
with wfrt_fresh : forall F r a,
    wfrt F r ->
    a `notin` dom F ->
    a `notin` fv_rtyp_in_rt r
with wfcl_fresh : forall F r a,
    wfcl F r ->
    a `notin` dom F ->
    a `notin` fv_rtyp_in_rlist r.
Proof.
  -
    induction 1; introv NOTIN; simpl; auto.
    apply test_solve_notin_3. introv I. substs.
    false binds_dom_contradiction; eauto.
    apply wfrt_fresh with Ttx; auto...
  -
    induction 1; introv NOTIN; simpl; auto.
    apply notin_union. apply wfcl_fresh with Ttx; auto.
    pick_fresh X. forwards ~ : H1 X; auto.

    eapply notin_Fv_rtyp_in_rt_open_rt_wrt_rtyp_inverse. eassumption.
    apply wfr_fresh with Ttx; auto.
  -
    induction 1; introv NOTIN; simpl; auto.
    apply notin_union. apply wfr_fresh with Ttx; auto.
    apply IHwfcl; auto.
Qed.


(* ********************************************************************** *)
(** * CMP *)

Lemma cmp_from_cmpList : forall F B R r,
    cmpList F B R ->
    rtyp_in_rlist r R ->
    cmp F B r.
Proof.
  induction 1; introv Rin; simpls.
  inverts Rin.
  inverts Rin; auto.
Qed.

(* ********************************************************************** *)
(** * SUBSTITUTION *)

Lemma subst_rtyp_rtyp_in_rlist: forall r R a B,
    rtyp_in_rlist r R ->
    rtyp_in_rlist (subst_rtyp_in_rtyp B a r) (subst_rtyp_in_rlist B a R).
Proof.
  induction 1; simpls.
  apply ti_head...
  apply ti_cons; auto...
Qed.

Scheme wftc_ind1 := Induction for wftc Sort Prop
  with wfcl_ind1 := Induction for wfcl Sort Prop
  with wfrt_ind1 := Induction for wfrt Sort Prop
  with wfr_ind1 := Induction for wfr Sort Prop
  with cmp_ind1 := Induction for cmp Sort Prop
  with ceq_ind1 := Induction for ceq Sort Prop
  with teq_ind1 := Induction for teq Sort Prop.

Combined Scheme wfrt_mutind' from wftc_ind1, wfcl_ind1, wfrt_ind1, wfr_ind1, cmp_ind1, ceq_ind1, teq_ind1.

Lemma wf_general_subst :
  ( forall T,
      wftc T ->
      forall E F B a R,
        T = (E ++ [(a, R)] ++ F) ->
        cmpList F B R ->
        wfr F B ->
        wftc (map (subst_rtyp_in_rlist B a) E ++ F)
  ) /\ (
   forall T A,
    wfcl T A ->
    forall E F B a R,
      wftc T ->
      wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
      T = (E ++ [(a, R)] ++ F) ->
      cmpList F B R ->
      wfr F B ->
      wfcl (map (subst_rtyp_in_rlist B a) E ++ F)
           (subst_rtyp_in_rlist B a A)
  ) /\ (
    forall T A,
    wfrt T A ->
    forall E F B a R,
      wftc T ->
      wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
      T = (E ++ [(a, R)] ++ F) ->
      cmpList F B R ->
      wfr F B ->
      wfrt (map ( subst_rtyp_in_rlist B a ) E ++ F)
           (subst_rtyp_in_rt B a A)
  ) /\ (
    forall T A,
    wfr T A ->
    forall E F B a R,
      wftc T ->
      wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
      T = (E ++ [(a, R)] ++ F) ->
      cmpList F B R ->
      wfr F B ->
      wfr (map (subst_rtyp_in_rlist B a) E ++ F)
          (subst_rtyp_in_rtyp B a A)
  ) /\ (
    forall T A C,
      cmp T A C ->
      forall E F B a R,
      wftc T ->
      wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
      T = (E ++ [(a, R)] ++ F) ->
      cmpList F B R ->
      wfr F B ->
      cmp (map (subst_rtyp_in_rlist B a) E ++ F)
          (subst_rtyp_in_rtyp B a A)
          (subst_rtyp_in_rtyp B a C)
  ) /\ (
    forall T A C,
      ceq T A C ->
      forall E F B a R,
      wftc T ->
      wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
      T = (E ++ [(a, R)] ++ F) ->
      cmpList F B R ->
      wfr F B ->
      ceq (map (subst_rtyp_in_rlist B a) E ++ F)
          (subst_rtyp_in_rlist B a A)
          (subst_rtyp_in_rlist B a C)
  ) /\ (
    forall T A C,
      teq T A C ->
      forall E F B a R,
      wftc T ->
      wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
      T = (E ++ [(a, R)] ++ F) ->
      cmpList F B R ->
      wfr F B ->
      teq (map (subst_rtyp_in_rlist B a) E ++ F)
          (subst_rtyp_in_rt B a A)
          (subst_rtyp_in_rt B a C)
  )
.
Proof with eauto.
  apply wfrt_mutind'; try solve [intros; substs; simpl; eauto].
  - intros. false nil_neq_one_mid...
  - introv WF IH1 WF2 IH2 NEQ EQ CMP WFR; substs.
    analyze_binds EQ.
    apply one_eq_app in EQ.
    destruct EQ as [ (qs & [I1 I2]) | [I1 I2]]; substs.
    simpl. constructor...
    simpl. simpl in I2.
    invert I2. intros. substs...
  - introv WFCL IH1 IH2 IH3 WFTC1 WFTC2 EQ CMP WFR. substs.
    simpl.
    pick fresh X and apply wfrt_All...
    forwards ~ : IH3 X ([(X, R)] ++ E) B a R0...
    simpl. constructor...
    simpl... simpl in H.
    unfold open_rt_wrt_rtyp in H.
    rewrite subst_rtyp_in_rt_open_rt_wrt_rtyp_rec in H...
    rewrite subst_rtyp_in_rtyp_fresh_eq in H...
    apply lc_rtyp_from_wfr with F...
  - introv BD WFTC1 WFTC2 EQ CMP WFR. substs... simpl.
    case_if...
    eapply wfr_weakening_head...
    analyze_binds BD...
  - introv WFCL IH1 WFR IH2 BD RTY WFR1 WFR3 EQ CMP. introv WFR2. substs.
    simpl. case_if; subst.
    +
    apply binds_mid_eq in BD; auto. substs.
    apply cmp_weakening_head; auto.
    forwards ~ : cmp_from_cmpList CMP RTY.
    rewrite subst_rtyp_in_rtyp_fresh_eq; auto.
    apply wfr_fresh with F...
    apply fresh_mid_tail with R0 E...
    +
    analyze_binds BD.
    apply subst_rtyp_rtyp_in_rlist with (a:=a0) (B:=B) in RTY.
    apply binds_map_2 with(f:=subst_rtyp_in_rlist B a0) in BindsTac.
    apply cmp_Tvar with (subst_rtyp_in_rlist B a0 R)...

    apply subst_rtyp_rtyp_in_rlist with (a:=a0) (B:=B) in RTY.
    apply cmp_Tvar with (subst_rtyp_in_rlist B a0 R)...
    rewrite subst_rtyp_in_rlist_fresh_eq; auto.
    apply wfcl_fresh with F...
    eapply wfcl_from_binds_wftc...
    apply wftc_strength with (E ++ [(a0, R0)]);
    rewrite_env (E ++ [(a0, R0)] ++ F)...
    apply fresh_mid_tail with R0 E...
  - introv CMP IH1 WFRT IH2 WFTC WFTC2 EQ CMP2 WFR2. subst.
    simpl.
    apply cmp_Base with (subst_rtyp_in_rt B a rt5)...
  - introv CMP IH1 WFTC WFTC2 EQ CMP2 WFR. subst.
    apply cmp_MergeE1 with (subst_rtyp_in_rtyp B a s2)...
  - introv CMP IH1 WFTC WFTC2 EQ CMP2 WFR. subst.
    apply cmp_MergeE2 with (subst_rtyp_in_rtyp B a s1)...
  - intros. simpls. substs.
    pick fresh X and apply teq_CongAll...
    specialize (H0 X).
    forwards ~ : H0 ((X, R) :: E) F B a R0.
    constructor...
    simpls...
    constructor... forwards ~ : H H2 H3 .
    simpls...
    unfold open_rt_wrt_rtyp in H4.
    do 2 rewrite subst_rtyp_in_rt_open_rt_wrt_rtyp_rec in H4...
    rewrite subst_rtyp_in_rtyp_fresh_eq in H4...
    apply lc_rtyp_from_wfr with F...
    apply lc_rtyp_from_wfr with F...
    apply lc_rtyp_from_wfr with F...
    specialize (H1 X).
    forwards ~ : H1 ((X, R') :: E) F B a R0.
    constructor...
    simpls...
    constructor... forwards ~ : H H2 H3 .
    simpls...
    constructor... forwards ~ : H H2 H3. 
    simpls...
    unfold open_rt_wrt_rtyp in H4.
    unfold open_rt_wrt_rtyp in H4.
    do 2 rewrite subst_rtyp_in_rt_open_rt_wrt_rtyp_rec in H4...
    rewrite subst_rtyp_in_rtyp_fresh_eq in H4...
    apply lc_rtyp_from_wfr with F...
    apply lc_rtyp_from_wfr with F...
    apply lc_rtyp_from_wfr with F...
  - intros. simpl... apply teq_CongMerge...
Qed.

Lemma teq_subst: forall  A C E F B a R,
    wftc (E ++ [(a, R)] ++ F) ->
    teq (E ++ [(a, R)] ++ F) A C ->
    wftc (map ( subst_rtyp_in_rlist B a ) E ++ F) ->
    cmpList F B R ->
    wfr F B ->
    teq (map (subst_rtyp_in_rlist B a) E ++ F)
        (subst_rtyp_in_rt B a A)
        (subst_rtyp_in_rt B a C).
Proof.
  lets [_ [_ [_ [_ [_ [_ I]]]]]] : wf_general_subst.
  intros.
  eapply I; eauto.
Qed.

Lemma teq_subst_empty: forall  A C F B a R,
    wftc ([(a, R)] ++ F) ->
    teq ([(a, R)] ++ F) A C ->
    cmpList F B R ->
    wfr F B ->
    teq F
        (subst_rtyp_in_rt B a A)
        (subst_rtyp_in_rt B a C).
Proof.
  intros.
  assert (F = map (subst_rtyp_in_rlist B a) nil ++ F) by auto.
  rewrite H3.
  eapply teq_subst; simpl_env; eauto.
  inverts H; auto.
Qed.


Lemma wfrt_subst : forall A E F B a R,
    wfrt (E ++ [(a, R)] ++ F) A ->
    wftc (E ++ [(a, R)] ++ F) ->
    cmpList F B R ->
    wfr F B ->
    wfrt (map ( subst_rtyp_in_rlist B a ) E ++ F)
         (subst_rtyp_in_rt B a A).
Proof.
  intros.
  pose (proj1 (proj2 (proj2 wf_general_subst))) as I.
  eapply I; eauto.
  pose (proj1 wf_general_subst) as I2.
  eapply I2; eauto.
Qed.


Lemma wfcl_subst : forall A E F B a R,
    wfcl (E ++ [(a, R)] ++ F) A ->
    wftc (E ++ [(a, R)] ++ F) ->
    cmpList F B R ->
    wfr F B ->
    wfcl (map ( subst_rtyp_in_rlist B a ) E ++ F)
         (subst_rtyp_in_rlist B a A).
Proof.
  intros.
  pose (proj1 (proj2 wf_general_subst)) as I.
  eapply I; eauto.
  pose (proj1 wf_general_subst) as I2.
  eapply I2; eauto.
Qed.


Lemma wfc_subst_tb : forall F E Z P T B,
  wfc (F ++ Z ~ B ++ E) T ->
  wfr E P ->
  cmpList E P B ->
  wftc (map (subst_rtyp_in_rlist P Z) F ++ E) ->
  wfc (map (subst_rtyp_in_rlist P Z) F ++ E) (map (subst_rtyp_in_rt P Z) T).
Proof with eauto using wftc_from_wfc.
  introv WFC.
  remember (F ++ Z ~ B ++ E) as G.
  generalize dependent F.
  induction WFC; introv EQ WFR CMP Ok; subst; simpls...

  constructor...
  simpl_env in *.
  eapply wfrt_subst...
Qed.

Lemma wftc_subst_tb : forall Q Z P E F,
  wftc (F ++ Z ~ Q ++ E) ->
  wfr E P ->
  cmpList E P Q ->
  wftc (map (subst_rtyp_in_rlist P Z) F ++ E).
Proof with eauto.
  introv WFTC.
  alist induction F; introv WFR CMP; simpls...

  inverts WFTC...

  inverts WFTC...

  constructor...
  simpl_env in *.
  eapply wfcl_subst...
Qed.


Lemma wfc_strengthen : forall X R Ttx Gtx,
      wfc ([(X, R)] ++ Ttx) Gtx ->
      wftc Ttx ->
      wfcl Ttx R ->
      X \notin fv_Gtx Gtx ->
      wfc Ttx Gtx.
Proof with eauto.
  introv WFC WFTC WFCL NOTIN.

  rewrite_env (nil ++ [(X, R)] ++ Ttx) in WFC.
  forwards IMP : wfc_subst_tb WFC...
  simpls.
  rewrite <- map_subst_rtyp_in_binding_id in IMP...
Qed.


(* ********************************************************************** *)
(** * BINDING *)

Lemma wfp_binds : forall a R Ttx Ptx,
  binds a R Ttx ->
  wfp Ttx Ptx   ->
  exists b, binds a b Ptx.
Proof with auto.
  induction 2...
  false.
  apply binds_cons_1 in H.
  destruct H as [[I1 I2]| I3].
    subst. exists b...
    forwards ~ (? & ?) : IHwfp I3.
    exists x...
Qed.

Lemma binds_ptx_fv: forall a b Ptx,
      binds a b Ptx ->
      b `in` fv_Ptx Ptx.
Proof with eauto.
  introv BD. inductions Ptx...
  false. destruct a0. analyze_binds BD; simpl...
Qed.

Lemma wfp_binds_neq : forall Ttx Ptx a1 a2 b1 b2,
    wfp Ttx Ptx ->
    binds a1 b1 Ptx ->
    binds a2 b2 Ptx ->
    b1 <> a2.
Proof with eauto.
  induction 1; introv BD1 BD2; eauto.
  analyze_binds BD1; analyze_binds BD2.
  forwards ~ : binds_In BindsTac...
  introv I. subst. false H5...
  forwards ~ : binds_ptx_fv BindsTac.
  introv I. subst. false H3...
Qed.

Lemma wfp_binds_range_neq : forall Ttx Ptx a1 a2 b1 b2,
    wfp Ttx Ptx ->
    binds a1 b1 Ptx ->
    binds a2 b2 Ptx ->
    a1 <> a2 ->
    b1 <> b2.
Proof with eauto.
  induction 1; introv BD1 BD2 NEQ; eauto.
  analyze_binds BD1; analyze_binds BD2.
  forwards ~ : binds_ptx_fv BindsTac.
  introv I. subst. false H6...
  forwards ~ : binds_ptx_fv BindsTac.
  introv I. subst. false H6...
Qed.

Lemma wfp_uniq : forall Ttx Ptx,
  wfp Ttx Ptx ->
  uniq Ptx.
Proof.
  induction 1; eauto.
Qed.
Hint Resolve wfp_binds_neq wfp_uniq.

Lemma fv_Ptx_union : forall G P,
    fv_Ptx (G ++ P) [=] fv_Ptx G \u fv_Ptx P.
Proof with eauto.
  intros G.
  induction G; intros; simpls...

  fsetdec.

  destruct a.
  specializes IHG P.
  rewrite IHG.
  fsetdec.
Qed.


Lemma wfp_mid_inv : forall Ptx1 Ptx2 a0 b0 Ttx,
    wfp Ttx (Ptx1 ++ [(a0, b0)] ++ Ptx2) ->
    b0 \notin dom (Ptx1 ++ Ptx2) /\ b0 \notin fv_Ptx (Ptx1 ++ Ptx2 ).
Proof with eauto.
  introv WFP. inductions WFP.
  assert (binds a0 b0 nil).
  rewrite x...
  false.

  apply one_eq_app in x.
  destruct x as [ (P' & [I1 I2]) | [I1 I2]]; substs.
  forwards ~ : IHWFP.
  destruct_hypo. simpl_env in *.
  repeat rewrite fv_Ptx_union in *.
  simpls. splits...

  simpl in I2. simpl_env.
  inverts I2...
Qed.


(* ********************************************************************** *)
(** * TEQ *)

Lemma teq_record_r : forall Ttx rt r,
    teq Ttx rt (rt_Record r) ->
    exists r2, rt = rt_Record r2
with teq_record_l : forall Ttx rt r,
    teq Ttx (rt_Record r) rt ->
    exists r2, rt = rt_Record r2.
Proof with auto.
  -
    introv EQ. inductions EQ.
    + exists r...
    + forwards : teq_record_l EQ.
      destruct_exists.
      exists x...
    + forwards ~ : IHEQ2. destruct_exists.
      forwards : IHEQ1 H. destruct_exists.
      exists x0...
    + exists (r_SingleField l rt5)...
    + exists (r_Merge r1 r2)...
    + exists (r_Merge r r_Empty)...
    + exists (r_Merge r1 (r_Merge r2 r3))...
    + exists (r_Merge r1 r2)...
  -
    introv EQ. inductions EQ.
    + exists r...
    + forwards : teq_record_r EQ.
      destruct_exists.
      exists x...
    + forwards ~ : IHEQ1. destruct_exists.
      forwards : IHEQ2 H. destruct_exists.
      exists x0...
    + exists (r_SingleField l rt')...
    + exists (r_Merge r1' r2')...
    + exists (r0)...
    + exists (r_Merge (r_Merge r1 r2) r3)...
    + exists (r_Merge r2 r1)...
Qed.

Hint Constructors teq.
Lemma teq_rt_Fun_inv' : forall A B Ttx,
    teq Ttx A B ->
    (forall A1 A2, A = rt_Fun A1 A2 -> exists D1 D2, B = rt_Fun D1 D2) /\
    (forall B1 B2, B = rt_Fun B1 B2 -> exists C1 C2, A = rt_Fun C1 C2).
Proof with eauto.
  introv EQ. inductions EQ; repeat destruct_hypo; intros;
               splits; intros;
                 try solve [inverts H0];
                 try solve [inverts H1];
                 try solve [inverts H2];
                 try solve [inverts H3];
                 try solve [inverts H4];
                 try solve [inverts H5]...
  apply H1 in H3. destruct H3 as (? & ? & ?).
  eapply H...

  apply H0 in H3. destruct H3 as (? & ? & ?).
  eapply H2...
Qed.

Lemma teq_rt_Fun_inv_l : forall A B Ttx C D,
    teq Ttx (rt_Fun A B) (rt_Fun C D) ->
    teq Ttx A C.
Proof with eauto.
  introv EQ.
  inductions EQ...
  inverts H...
  apply teq_rt_Fun_inv' in EQ1.
  destruct_hypo.
  forwards  ~ : H.
  destruct H1 as (? & ? & ?).
  substs.
  forwards ~ : IHEQ1.
  forwards ~ : IHEQ2.
  eauto.
Qed.

Lemma teq_rt_Fun_inv_r : forall A B Ttx C D,
    teq Ttx (rt_Fun A B) (rt_Fun C D) ->
    teq Ttx B D.
Proof with eauto.
  introv EQ.
  inductions EQ...
  inverts H...
  apply teq_rt_Fun_inv' in EQ1.
  destruct_hypo.
  forwards  ~ : H.
  destruct H1 as (? & ? & ?).
  substs.
  forwards ~ : IHEQ1.
  forwards ~ : IHEQ2.
  eauto.
Qed.

Lemma teq_rt_Record_inv' : forall A B Ttx,
    teq Ttx A B ->
    (forall A1, A = rt_Record A1 -> exists D1, B = rt_Record D1) /\
    (forall B1, B = rt_Record B1 -> exists C1, A = rt_Record C1).
Proof with eauto.
  introv EQ. inductions EQ; repeat destruct_hypo; intros;
               splits; intros;
                 try solve [inverts H0];
                 try solve [inverts H1];
                 try solve [inverts H2];
                 try solve [inverts H3];
                 try solve [inverts H4];
                 try solve [inverts H5]...
  apply H1 in H3. destruct H3 as (? & ?).
  eapply H...

  apply H0 in H3. destruct H3 as (? & ?).
  eapply H2...
Qed.

Lemma teq_rt_Record_inv_l : forall A B Ttx,
    teq Ttx (rt_Record A) B ->
    exists D1, B = rt_Record D1.
Proof.
  introv I.
  forwards ~ : teq_rt_Record_inv' I.
  destruct_hypo.
  eapply H; auto.
Qed.

Lemma teq_rt_Record_inv_r : forall A B Ttx,
    teq Ttx A (rt_Record B) ->
    exists C1, A = rt_Record C1.
Proof.
  introv I.
  forwards ~ : teq_rt_Record_inv' I.
  destruct_hypo.
  eapply H0; auto.
Qed.

Lemma teq_rt_ConQuan_inv' : forall A B Ttx,
    teq Ttx A B ->
    (forall R1 A1, A = rt_ConQuan R1 A1 -> exists R2 D1, B = rt_ConQuan R2 D1) /\
    (forall R1 B1, B = rt_ConQuan R1 B1 -> exists R2 C1, A = rt_ConQuan R2 C1).
Proof with eauto.
  introv EQ. inductions EQ; repeat destruct_hypo; intros;
               splits; intros; substs;
                 try solve [inverts H0];
                 try solve [inverts H1];
                 try solve [inverts H2];
                 try solve [inverts H3];
                 try solve [inverts H4];
                 try solve [inverts H5]...

  destruct (H1 R1 A1) as (? & ? & ?)...
  destruct (H0 R1 B1) as (? & ? & ?)...
Qed.

Lemma teq_rt_ConQuan_inv_l : forall R A B Ttx,
    teq Ttx (rt_ConQuan R A) B ->
    exists R1 D1, B = rt_ConQuan R1 D1.
Proof.
  introv I.
  forwards ~ : teq_rt_ConQuan_inv' I.
  destruct_hypo.
  eapply H; auto.
Qed.


Lemma teq_rt_ConQuan_inv_r : forall A B Ttx R,
    teq Ttx A (rt_ConQuan R B) ->
    exists R1 C1, A = rt_ConQuan R1 C1.
Proof.
  introv I.
  forwards ~ : teq_rt_ConQuan_inv' I.
  destruct_hypo.
  eapply H0; auto.
Qed.
