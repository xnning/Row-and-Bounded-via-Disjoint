Require Export LibTactics.
Require Export Metalib.Metatheory.
Require Export Assumed.
Require Import Syntax_ott.
Require Import Fii_inf.
Require Import Infrastructure.
Require Import SourceProperty.
Require Import LR.
Require Import Compatibility.
Require Import Row_inf.
Require Import Row_Properties.
Require Import Row_Elaboration.

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
  let N1 := gather_atoms_with (fun x : ctx => dom x) in
  let N2 := gather_atoms_with (fun x : tctx => dom x) in
  let N3 := gather_atoms_with (fun x => fv_ty_in_ty x) in
  let N4 := gather_atoms_with (fun x => fv_ty_in_exp x) in
  let N5 := gather_atoms_with (fun x => fv_exp_in_exp x) in
  let N6 := gather_atoms_with (fun x => seqs_vars x) in
  let N7 := gather_atoms_with (fun x : atoms => x) in
  let N8 := gather_atoms_with (fun x : atom => singleton x) in
  constr:(A \u B \u C3 \u C4 \u D4 \u D5 \u D6 \u D8 \u D9 \u D10 \u D11 \u D12 \u D13 \u D14 \u D15 \u D16 \u D17 \u D18 \u D19 \u N1 \u N2 \u N3 \u N4 \u N5 \u N6 \u N7 \u N8).

Hint Extern 1 (wfrt ?TT ?A) =>
match goal with
| H : wtt _ _ _ _ _ _ _ |- _ => apply (proj2 (proj2 (proj2 (wtt_regular H))))
end.

Lemma typing_inference_unique : forall e A EE n DD GG B ee PP FF TT,
    wtt PP TT FF e A EE n ->
    trans_Ttx PP TT DD ->
    trans_Gtx PP FF GG ->
    has_type DD GG EE Inf B ee ->
    trans_rt PP A B.
Proof with eauto.
  introv TY TRD TRG HT.
  forwards ~ (T & I1): trans_rt_exists TT PP A...
  forwards ~ (ee' & I2) : translation_well_formed TY TRD TRG I1.
  forwards ~ : inference_unique HT I2. substs; auto.
Qed.

Lemma uniq_from_trans_Ttx : forall T G P,
    trans_Ttx P T G ->
    uniq G.
Proof with eauto.
  induction 1...
Qed.
Hint Extern 1 (uniq ?P) =>
match goal with
| H : wfc _ P  |- _ => apply (uniq_from_wfc H)
| H : trans_Ttx _ _ P  |- _ => apply (uniq_from_trans_Ttx _ _ _ H)
end.
Hint Constructors wtt.

(** * label ty in rtyp*)

Inductive label_ty_in_rtyp : i -> rt -> rtyp -> Prop :=
  | label_ty_in_rtyp_rcd : forall l rt,
      label_ty_in_rtyp l rt (r_SingleField l rt)
  | label_ty_in_rtyp_merge_l : forall l rt rt1 rt2,
      label_ty_in_rtyp l rt rt1 ->
      label_ty_in_rtyp l rt (r_Merge rt1 rt2)
  | label_ty_in_rtyp_merge_r : forall l rt rt1 rt2,
      label_ty_in_rtyp l rt rt2 ->
      label_ty_in_rtyp l rt (r_Merge rt1 rt2)
.


Lemma wfrt_from_label_ty_in_rtyp: forall l rt r2 Ttx,
   wfr Ttx r2 ->
   label_ty_in_rtyp l rt r2 ->
   wfrt Ttx rt.
Proof with eauto.
  introv I1 I2.
  inductions I2...
  inverts I1...
  inverts I1...
  inverts I1...
Qed.

Hint Constructors label_ty_in_rtyp.
Lemma label_ty_in_teq: forall l Ttx r1 r2 rt,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    (label_ty_in_rtyp l rt r1 ->
    exists rt', label_ty_in_rtyp l rt' r2
           /\ teq Ttx rt rt')
    /\
    (label_ty_in_rtyp l rt r2 ->
    exists rt', label_ty_in_rtyp l rt' r1
           /\ teq Ttx rt rt').
Proof with eauto.
  introv HH.
  generalize dependent rt.
  inductions HH; introv; split; introv I; repeat destruct_hypo; simpls;
    try solve [inverts I; eauto].
  - inverts H.
    forwards ~ : wfrt_from_label_ty_in_rtyp H2 I.
    eexists...
  - inverts H.
    forwards ~ : wfrt_from_label_ty_in_rtyp H2 I.
    eexists...
  - forwards ~ : IHHH. destruct_hypo...
  - forwards ~ : IHHH. destruct_hypo...
  - forwards ~ (x & I1): teq_rt_Record_inv_l HH1.
    substs.
    forwards ~ I1 : IHHH1 rt.
    destruct I1 as [I2 _].
    forwards ~ (y & [I3 I4]): I2 I.
    forwards ~ I5 : IHHH2 y.
    destruct I5 as [I6 _].
    forwards ~ I7 : I6.
    forwards ~ (z & [I8 I9]): I7.
    exists z. splits...
  - forwards ~ (x & I1): teq_rt_Record_inv_l HH1.
    substs.
    forwards ~ I5 : IHHH2 rt.
    destruct I5 as [_ I6].
    forwards ~ I7 : I6.
    forwards ~ (z & [I8 I9]): I7.
    forwards ~ I1 : IHHH1 z.
    destruct I1 as [_ I2].
    forwards ~ (y & [I3 I4]): I2 I8.
    exists y. splits...
  - inverts I...
    forwards ~ [I1 _ ]: IHHH1 rt.
    forwards ~ [x [I2 I3]] : I1 H4.
    exists x...
    forwards ~ [I1 _ ]: IHHH2 rt.
    forwards ~ [x [I2 I3]] : I1 H4.
    exists x...
  - inverts I...
    forwards ~ [_ I1 ]: IHHH1 rt.
    forwards ~ [x [I2 I3]] : I1 H4.
    exists x...
    forwards ~ [_ I1 ]: IHHH2 rt.
    forwards ~ [x [I2 I3]] : I1 H4.
    exists x...
  - inverts I...
    forwards ~ : wfrt_from_label_ty_in_rtyp H H3.
    eexists...
    inverts H3.
  - forwards ~ : wfrt_from_label_ty_in_rtyp H I.
    eexists...
  - forwards ~[ I1 I2] : cmp_regular H0.
    forwards ~[ I3 _] : cmp_regular H1.
    inverts I as I...
    forwards ~ : wfrt_from_label_ty_in_rtyp I1 I...
    exists rt...
    inverts I as I...
    forwards ~ : wfrt_from_label_ty_in_rtyp I3 I.
    exists rt...
    forwards ~ : wfrt_from_label_ty_in_rtyp I2 I.
    exists rt...
  - forwards ~[ I1 I2] : cmp_regular H0.
    forwards ~[ I3 _] : cmp_regular H1.
    inverts I as I...
    inverts I as I...
    forwards ~ : wfrt_from_label_ty_in_rtyp I1 I...
    forwards ~ : wfrt_from_label_ty_in_rtyp I3 I...
    exists rt...
    forwards ~ : wfrt_from_label_ty_in_rtyp I2 I.
    exists rt...
  - inverts I.
    forwards ~[ I1 I2] : cmp_regular H.
    forwards ~ : wfrt_from_label_ty_in_rtyp I1 H3...
    forwards ~[ I1 I2] : cmp_regular H.
    forwards ~ : wfrt_from_label_ty_in_rtyp I2 H3...
  - inverts I.
    forwards ~[ I1 I2] : cmp_regular H.
    forwards ~ : wfrt_from_label_ty_in_rtyp I2 H3...
    forwards ~[ I1 I2] : cmp_regular H.
    forwards ~ : wfrt_from_label_ty_in_rtyp I1 H3...
Qed.

Lemma label_ty_in_label_in : forall l r rt,
    label_ty_in_rtyp l rt r ->
    label_in_rtyp l r.
Proof with eauto.
  induction 1...
Qed.

Lemma label_ty_in_uniq : forall l Ttx r rt rt',
    wfr Ttx r ->
    label_ty_in_rtyp l rt r ->
    label_ty_in_rtyp l rt' r ->
    rt = rt'.
Proof with eauto.
  introv HH.
  inductions HH; introv IN1 IN2; simpls;
    try solve [inverts IN1].
    inverts IN1. inverts IN2...
    inverts IN1.
    forwards ~ I : label_ty_in_label_in H3.
    forwards ~ I2: label_in_cmp_l H I.
    inverts IN2.
    forwards ~ : IHHH1 H3 H4.
    forwards ~ I3 : label_ty_in_label_in H4.
    forwards ~ : label_in_false I3 I2. false...

    forwards ~ I : label_ty_in_label_in H3.
    forwards ~ I2: label_in_cmp_r H I.
    inverts IN2.
    forwards ~ I3 : label_ty_in_label_in H4.
    forwards ~ : label_in_false I3 I2. false...
    forwards ~ : IHHH2 H3 H4.
Qed.

Lemma teq_label_ty_in_teq: forall l Ttx r1 r2 rt rt',
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    label_ty_in_rtyp l rt r1 ->
    label_ty_in_rtyp l rt' r2 ->
    teq Ttx rt rt'.
Proof with eauto.
  introv I1 I2 I3.
  forwards ~ : label_ty_in_teq I1.
  destruct H as [I4 I5].
  forwards ~ (? & [? ?]): I4 I2.
  forwards ~ [I6 I7]: teq_regular I1.
  inverts I7...
  forwards ~ : label_ty_in_uniq I3 H...
  substs...
Qed.

(** * perm *)

Inductive perm : rtyp -> i -> rt -> rtyp -> Prop :=
  | perm_rcd : forall l rt,
      perm (r_SingleField l rt) l rt r_Empty
  | perm_merge_l : forall l rt rt1 rt2 A,
      perm rt1 l rt A ->
      perm (r_Merge rt1 rt2) l rt (r_Merge A rt2)
  | perm_merge_r : forall l rt rt1 rt2 A,
      perm rt2 l rt A ->
      perm (r_Merge rt1 rt2) l rt (r_Merge rt1 A)
.

Lemma perm_label_in : forall A l B1 C1,
    perm A l B1 C1 ->
    label_in_rtyp l A.
Proof.
  introv PM. inductions PM; auto.
Qed.

Lemma perm_unique : forall Ttx A l B1 B2 C1 C2,
    wfr Ttx A ->
    perm A l B1 C1 ->
    perm A l B2 C2 ->
    B1 = B2 /\ C1 = C2.
Proof with auto.
  introv WF PM1 PM2.
  generalize dependent B2.
  generalize dependent C2.
  inductions PM1; introv PM2.

  inverts PM2; splits; auto.

  inverts WF.
  inverts PM2.
  forwards ~ [? ?] : IHPM1 H7. substs...
  forwards ~ : perm_label_in PM1.
  forwards ~ : perm_label_in H7.
  forwards ~ : cmp_label_in_false H4 H H0. false...

  inverts WF.
  inverts PM2.
  forwards ~ : perm_label_in PM1.
  forwards ~ : perm_label_in H7.
  forwards ~ : cmp_label_in_false H4 H0. false...
  forwards ~ [? ?] : IHPM1 H7. substs...
Qed.


Lemma perm_cmp : forall r1 l A1 A r2 Ttx,
    perm r1 l A1 A ->
    cmp Ttx r1 r2 ->
    cmp Ttx A r2 .
Proof with auto.
  introv PM CM.
  generalize dependent r2.
  inductions PM; introv CM; auto.
  apply cmp_Symm in CM.
  forwards ~ : cmp_MergeE1 CM.
  forwards ~ : cmp_MergeE2 CM.
  apply cmp_Symm.
  apply cmp_MergeI; auto.
  apply IHPM.
  forwards ~ [_ I] : cmp_regular CM...
  inverts I...

  apply cmp_Symm in CM.
  forwards ~ : cmp_MergeE1 CM.
  forwards ~ : cmp_MergeE2 CM.
  apply cmp_Symm.
  apply cmp_MergeI; auto.
  apply cmp_Symm.
  apply IHPM.
  forwards ~ [_ I] : cmp_regular CM...
  inverts I...
Qed.

Lemma perm_cmp_single : forall r1 l A1 A r2 Ttx,
    perm r1 l A1 A ->
    cmp Ttx r1 r2 ->
    cmp Ttx (r_SingleField l A1) r2 .
Proof with auto.
  introv PM CM.
  generalize dependent r2.
  inductions PM; introv CM; auto.
  apply cmp_Symm in CM.
  forwards ~ : cmp_MergeE1 CM.
  apply cmp_Symm in CM.
  forwards ~ : cmp_MergeE2 CM.
Qed.

Lemma perm_cmp_components: forall Ttx rt1 l rt A,
    wfr Ttx rt1 ->
    perm rt1 l rt A ->
    cmp Ttx (r_SingleField l rt) A.
Proof with auto.
  introv WF PM.
  inductions PM; auto.
  inverts WF.
  forwards ~ : IHPM.
  apply cmp_MergeI...
  eapply perm_cmp; eauto.
  eapply perm_cmp_single; eauto.
  inverts WF.
  forwards ~ : IHPM.
  apply cmp_MergeI...
  apply cmp_Symm...
  apply cmp_Symm in H4...
  eapply perm_cmp; eauto.
  apply cmp_Symm in H4...
  eapply perm_cmp_single; eauto.
Qed.

Lemma perm_wfr : forall A l rt B Ttx,
    wfr Ttx A ->
    perm A l rt B ->
    wfrt Ttx rt /\ wfr Ttx B .
Proof with auto.
  introv WF PM.
  inductions PM.
  inverts WF...
  inverts WF...
  destruct IHPM...
  splits...
  constructor...
  eapply perm_cmp; eauto...
  inverts WF...
  destruct IHPM...
  splits...
  constructor...
  apply cmp_Symm.
  eapply perm_cmp; eauto...
Qed.

Lemma perm_wfr_l : forall A l rt B Ttx,
    wfr Ttx A ->
    perm A l rt B ->
    wfrt Ttx rt.
Proof.
  introv I1 I2.
  forwards ~ [? ?] : perm_wfr I1 I2.
Qed.

Lemma perm_wfr_r : forall A l rt B Ttx,
    wfr Ttx A ->
    perm A l rt B ->
    wfr Ttx B.
Proof.
  introv I1 I2.
  forwards ~ [? ?] : perm_wfr I1 I2.
Qed.


Lemma perm_teq : forall A l rt B Ttx,
    wfr Ttx A ->
    perm A l rt B ->
    teq Ttx (rt_Record A) (rt_Record (r_Merge (r_SingleField l rt) B)).
Proof with auto.
  introv WF PM.
  inductions PM; auto.
  -
  inverts WF.
  forwards ~ : IHPM.
  apply teq_Trans
  with (rt_Record (r_Merge (r_Merge (r_SingleField l rt) A) rt2))...
  *
  apply teq_CongMerge; auto.
  apply cmp_Symm.
  apply cmp_MergeI...
  apply perm_cmp_components with rt1; eauto.
  apply cmp_Symm.
  eapply perm_cmp_single; eauto.
  apply cmp_Symm.
  eapply perm_cmp; eauto.
  *
  apply teq_Symm.
  apply teq_MergeAssoc...
  apply perm_cmp_components with rt1; eauto.
  eapply perm_cmp_single; eauto.
  eapply perm_cmp; eauto.

  -
  inverts WF.
  forwards ~ : IHPM.
  apply teq_Trans
  with (rt_Record (r_Merge rt1 (r_Merge (r_SingleField l rt) A) ))...
  *
  apply teq_CongMerge; auto.
  apply cmp_MergeI...
  apply perm_cmp_components with rt2; eauto.
  apply cmp_Symm.
  eapply perm_cmp_single; eauto.
  apply cmp_Symm.
  eapply perm_cmp; eauto.
  *
  apply teq_Trans
  with (rt_Record (r_Merge (r_Merge rt1 (r_SingleField l rt)) A ))...
  +
  apply teq_MergeAssoc...
  apply cmp_Symm.
  eapply perm_cmp_single; eauto.
  apply cmp_Symm.
  apply cmp_Symm in H4.
  eapply perm_cmp; eauto.
  eapply perm_cmp_components; eauto.
  +
  apply teq_Symm.
  apply teq_Trans with
    (rt_Record
       (r_Merge (r_Merge (r_SingleField l rt) rt1) A)).
  apply teq_MergeAssoc.
  apply cmp_Symm in H4.
  eapply perm_cmp_single; eauto.
  eapply perm_cmp_components;eauto.
  apply cmp_Symm.
  apply cmp_Symm in H4.
  eapply perm_cmp; eauto...
  apply teq_CongMerge; auto.
  apply teq_MergeComm; auto.
  apply cmp_Symm in H4.
  eapply perm_cmp_single; eauto.
  apply perm_wfr_r with (Ttx:=Ttx) in PM...
  apply cmp_Symm.
  apply cmp_MergeI...
  apply cmp_Symm in H4.
  eapply perm_cmp_single; eauto.
  apply cmp_Symm.
  eapply perm_cmp_components; eauto.
  apply cmp_Symm in H4.
  eapply perm_cmp; eauto.
  apply cmp_Symm.
  apply cmp_MergeI...
  apply cmp_Symm.
  apply cmp_Symm in H4.
  eapply perm_cmp_single; eauto.
  apply cmp_Symm in H4.
  eapply perm_cmp; eauto.
  apply cmp_Symm.
  apply cmp_Symm in H4.
  eapply perm_cmp_components; eauto.
Qed.


Hint Constructors perm.
Lemma teq_r_merge_single : forall Ttx A B l,
    teq Ttx (rt_Record A) (rt_Record B) ->
    (forall A1 A2, perm A l A1 A2 -> exists B1 B2, perm B l B1 B2 /\ teq Ttx (rt_Record A2) (rt_Record B2)) /\
    (forall B1 B2, perm B l B1 B2 -> exists A1 A2, perm A l A1 A2 /\ teq Ttx (rt_Record A2) (rt_Record B2))
.
Proof with eauto using perm_cmp.
  introv EQ.
  inductions EQ; splits; introv PM...
  -
  exists A1 A2. inverts H. splits...
  apply teq_Refl.
  constructor.
  eapply perm_wfr_r...
  -
  exists B1 B2. inverts H. splits...
  apply teq_Refl.
  constructor.
  eapply perm_wfr_r...
  -
  forwards ~ : IHEQ.
  destruct H as [I1 I2].
  forwards ~ (? & ? & [? ?]): I2 PM...
  -
  forwards ~ : IHEQ.
  destruct H as [I1 I2].
  forwards ~ (? & ? & [? ?]): I1 PM...
  -
  forwards ~ (D1 & I1): teq_rt_Record_inv_l EQ1.
  forwards ~ (D2 & I2): teq_rt_Record_inv_r EQ2.
  substs. inverts I2.
  forwards ~ I3 : IHEQ1. clear IHEQ1.
  forwards ~ I4 : IHEQ2. clear IHEQ2.
  destruct I3 as [I31 I32].
  destruct I4 as [I41 I42].
  forwards ~ (D3 & D4 & [I5 I6]) : I31 PM.
  forwards ~ (D5 & D6 & [I7 I8]) : I41 I5.
  exists D5 D6. splits...
  -
  forwards ~ (D1 & I1): teq_rt_Record_inv_l EQ1.
  forwards ~ (D2 & I2): teq_rt_Record_inv_r EQ2.
  substs. inverts I2.
  forwards ~ I3 : IHEQ1. clear IHEQ1.
  forwards ~ I4 : IHEQ2. clear IHEQ2.
  destruct I3 as [I31 I32].
  destruct I4 as [I41 I42].
  forwards ~ (D3 & D4 & [I5 I6]) : I42 PM.
  forwards ~ (D5 & D6 & [I7 I8]) : I32 I5.
  exists D5 D6. splits...
  -
  inverts PM.
  exists rt' r_Empty.
  splits...
  -
  inverts PM.
  exists rt5 r_Empty.
  splits...
  -
  forwards ~ [I1 I2]: IHEQ1. clear IHEQ1.
  forwards ~ [I3 I4]: IHEQ2. clear IHEQ2.
  inverts PM as PM.
  +
  forwards ~ (B1 & B2 & [M1 M2])  : I1 PM.
  forwards ~ (B3 & B4 & [M3 M4])  : I2 M1.
  exists B1 (r_Merge B2 r2').
  splits; auto.
  apply teq_CongMerge; auto.
  eapply perm_cmp...
  eapply perm_cmp...
  +
  forwards ~ (B1 & B2 & [M1 M2])  : I3 PM.
  forwards ~ (B3 & B4 & [M3 M4])  : I4 M1.
  exists B1 (r_Merge r1' B2).
  splits; auto.
  apply teq_CongMerge; auto.
  apply cmp_Symm.
  apply cmp_Symm in H.
  eapply perm_cmp...
  apply cmp_Symm.
  apply cmp_Symm in H.
  eapply perm_cmp...
  -
  forwards ~ [I1 I2]: IHEQ1. clear IHEQ1.
  forwards ~ [I3 I4]: IHEQ2. clear IHEQ2.
  inverts PM as PM.
  +
  forwards ~ (B2 & B3 & [M1 M2])  : I2 PM.
  forwards ~ (B4 & B5 & [M3 M4])  : I1 M1.
  exists B2 (r_Merge B3 r2).
  splits; auto.
  apply teq_CongMerge; auto.
  eapply perm_cmp...
  eapply perm_cmp...
  +
  forwards ~ (B2 & B3 & [M1 M2])  : I4 PM.
  forwards ~ (B4 & B5 & [M3 M4])  : I3 M1.
  exists B2 (r_Merge r1 B3).
  splits; auto.
  apply teq_CongMerge; auto.
  apply cmp_Symm.
  apply cmp_Symm in H.
  eapply perm_cmp...
  apply cmp_Symm.
  apply cmp_Symm in H.
  eapply perm_cmp...

  -
  inverts PM as PM; [|inverts PM].
  exists A1 A.
  splits; auto.
  apply teq_MergeUnit.
  eapply perm_wfr_r...
  -
  exists B1 (r_Merge B2 r_Empty).
  splits; auto.
  apply teq_MergeUnit.
  eapply perm_wfr_r...
  -
  inverts PM as PM.
  *
  exists A1 (r_Merge (r_Merge A r2) r3).
  splits; auto.
  apply teq_MergeAssoc; auto.
  eapply perm_cmp...
  eapply perm_cmp...
  *
  inverts PM as PM.
  +
  exists A1 (r_Merge (r_Merge r1 A0) r3).
  splits; auto.
  apply teq_MergeAssoc; auto.
  apply cmp_Symm.
  apply cmp_Symm in H.
  eapply perm_cmp...
  eapply perm_cmp...
  +
  exists A1 (r_Merge (r_Merge r1 r2) A0).
  splits; auto.
  apply teq_MergeAssoc; auto.
  apply cmp_Symm.
  apply cmp_Symm in H0.
  eapply perm_cmp...
  apply cmp_Symm.
  apply cmp_Symm in H1.
  eapply perm_cmp...

  -
  inverts PM as PM.
  *
  inverts PM as PM.
  +
  exists B1 (r_Merge A0 (r_Merge r2 r3)).
  splits; auto.
  apply teq_MergeAssoc; auto.
  eapply perm_cmp...
  eapply perm_cmp...
  +
  exists B1 (r_Merge r1 (r_Merge A0 r3)).
  splits; auto.
  apply teq_MergeAssoc; auto.
  apply cmp_Symm.
  apply cmp_Symm in H.
  eapply perm_cmp...
  eapply perm_cmp...
  *
  exists B1 (r_Merge r1 (r_Merge r2 A)).
  splits; auto.
  apply teq_MergeAssoc; auto.
  apply cmp_Symm.
  apply cmp_Symm in H0.
  eapply perm_cmp...
  apply cmp_Symm.
  apply cmp_Symm in H1.
  eapply perm_cmp...

  -
  inverts PM as PM.
  *
  exists A1 (r_Merge r2 A).
  splits; auto.
  apply teq_MergeComm; auto.
  eapply perm_cmp...
  *
  exists A1 (r_Merge A r1).
  splits; auto.
  apply teq_MergeComm; auto.
  apply cmp_Symm.
  eapply perm_cmp...

  -
  inverts PM as PM.
  *
  exists B1 (r_Merge r1 A).
  splits; auto.
  apply teq_MergeComm; auto.
  apply cmp_Symm in H.
  apply cmp_Symm.
  eapply perm_cmp...
  *
  exists B1 (r_Merge A r2).
  splits; auto.
  apply teq_MergeComm; auto.
  eapply perm_cmp...
Qed.

Lemma teq_merge_inv: forall Ttx l rt5 r rt0 r0,
   teq Ttx (rt_Record (r_Merge (r_SingleField l rt5) r))
         (rt_Record (r_Merge (r_SingleField l rt0) r0)) ->
  teq Ttx (rt_Record r) (rt_Record r0).
Proof with auto.
  introv EQ.
  forwards ~ I : teq_r_merge_single l EQ.
  destruct I as [I1 I2].
  forwards ~ (B1 & B2 & [I3 I4]) : I1. clear I1.
  forwards ~ (B3 & B4 & [I5 I6]) : I2. clear I2.
  assert (M1 : perm (r_Merge (r_SingleField l rt0) r0) l rt0 (r_Merge r_Empty r0)) by auto.
  forwards ~ [? ?] : perm_unique Ttx I3 M1...
  forwards ~ [N1 N2] : teq_regular EQ.
  inverts N2... substs.
  assert (M2 : perm (r_Merge (r_SingleField l rt5) r) l rt5 (r_Merge r_Empty r)) by auto.
  forwards ~ [? ?] : perm_unique Ttx I5 M2...
  forwards ~ [N1 N2] : teq_regular EQ.
  inverts N1... substs.
  clear I3 I5 M1 M2.
  assert (N1: teq Ttx (rt_Record r) (rt_Record (r_Merge r_Empty r))).
    apply teq_Trans with (rt_Record (r_Merge r r_Empty )).
    apply teq_Symm.
    apply teq_MergeUnit.
    forwards ~ [N1 N2] : teq_regular I4.
    inverts N1... inverts H1...
    apply teq_MergeComm; auto.
    apply cmp_Empty.
    forwards ~ [N1 N2] : teq_regular I4.
    inverts N1... inverts H1...
  assert (N2: teq Ttx (rt_Record r0) (rt_Record (r_Merge r_Empty r0))).
    apply teq_Trans with (rt_Record (r_Merge r0 r_Empty )).
    apply teq_Symm.
    apply teq_MergeUnit.
    forwards ~ [M1 M2] : teq_regular I4.
    inverts M2... inverts H1...
    apply teq_MergeComm; auto.
    apply cmp_Empty.
    forwards ~ [M1 M2] : teq_regular I4.
    inverts M2... inverts H1...
  apply teq_Trans with (rt_Record (r_Merge r_Empty r))...
  apply teq_Trans with (rt_Record (r_Merge r_Empty r0))...
Qed.

(** * rtyp_label_in_rslit *)

Hint Constructors rtyp_in_rlist.

Inductive rtyp_label_in_rlist : rtyp -> rlist -> Prop :=
| rtyp_label_in_rlist_empty : forall R,
    rtyp_label_in_rlist r_Empty R
| rtyp_label_in_rlist_var_l : forall r R a,
    tvar_in_rtyp a r ->
    rtyp_label_in_rlist (r_TyVar_f a)
                        (R_Cons r R)
| rtyp_label_in_rlist_var_r : forall r R a,
    rtyp_label_in_rlist (r_TyVar_f a) R ->
    rtyp_label_in_rlist (r_TyVar_f a) (R_Cons r R)

| rtyp_label_in_rlist_single_l : forall r R l rt,
    label_in_rtyp l r ->
    rtyp_label_in_rlist (r_SingleField l rt) (R_Cons r R)
| rtyp_label_in_rlist_single_r : forall r R l rt,
    rtyp_label_in_rlist (r_SingleField l rt) R ->
    rtyp_label_in_rlist (r_SingleField l rt) (R_Cons r R)
| rtyp_label_in_rlist_merge : forall R r1 r2,
    rtyp_label_in_rlist r1 R ->
    rtyp_label_in_rlist r2 R ->
    rtyp_label_in_rlist (r_Merge r1 r2) R
.

Hint Constructors rtyp_label_in_rlist.

Inductive rtyp_in_rtyp : rtyp -> rtyp -> Prop :=
| rtyp_in_rtyp_refl : forall r,
    rtyp_in_rtyp r r
| rtyp_in_rtyp_l : forall r1 r2,
    rtyp_in_rtyp r1 (r_Merge r1 r2)
| rtyp_in_rtyp_r : forall r1 r2,
    rtyp_in_rtyp r2 (r_Merge r1 r2).

Lemma label_in_rtyp_in_rtyp : forall l r1 r2,
    label_in_rtyp l r1 ->
    rtyp_in_rtyp r1 r2 ->
    label_in_rtyp l r2.
Proof.
  introv IN1 IN2.
  inductions IN2; auto.
Qed.

Lemma tvar_in_rtyp_in_rtyp : forall a r1 r2,
    tvar_in_rtyp a r1 ->
    rtyp_in_rtyp r1 r2 ->
    tvar_in_rtyp a r2.
Proof.
  introv IN1 IN2.
  inductions IN2; auto.
Qed.

Lemma rtyp_label_in_rlist_head_refl': forall rl r1 r2 r,
    rtyp_label_in_rlist r (R_Cons r1 rl) ->
    rtyp_in_rtyp r1 r2 ->
    rtyp_label_in_rlist r (R_Cons r2 rl).
Proof.
  introv IN1 IN2.
  inductions IN1; auto.

  apply rtyp_label_in_rlist_var_l.

  eapply tvar_in_rtyp_in_rtyp; eauto.


  apply rtyp_label_in_rlist_single_l.

  eapply label_in_rtyp_in_rtyp; eauto.
  constructor; eauto.
Qed.


Lemma rtyp_label_in_rlist_head_refl: forall r rl,
  lc_rtyp r ->
  rtyp_label_in_rlist r (R_Cons r rl).
Proof.
  induction 1; introv; auto.
  constructor.
  apply rtyp_label_in_rlist_head_refl' with (r1); auto.
  constructor.
  apply rtyp_label_in_rlist_head_refl' with (r2); auto.
  constructor.
Qed.

Lemma rtyp_label_in_rlist_tail : forall r rl r',
  rtyp_label_in_rlist r rl ->
  rtyp_label_in_rlist r (R_Cons r' rl).
Proof.
  induction 1; introv; auto.
Qed.

Lemma rtyp_in_rlist_rtyp_label_in_rlist: forall R r,
    lc_rtyp r ->
    rtyp_in_rlist r R ->
    rtyp_label_in_rlist r R.
Proof with auto.
  introv LC IN.
  inductions IN.
  apply rtyp_label_in_rlist_head_refl...
  apply rtyp_label_in_rlist_tail...
Qed.

Lemma label_in_rlist_ceq: forall R1 R2 l Ttx,
    ceq Ttx R1 R2 ->
    (label_in_rlist l R1 -> label_in_rlist l R2)
    /\
    (label_in_rlist l R2 -> label_in_rlist l R1).
Proof with auto.
  Hint Constructors label_in_rlist.
  introv EQ.
  inductions EQ; repeat destruct_hypo...
  
  -
    splits; introv IN...
    +
      inverts IN...
      constructor.
      eapply label_in_teq_l; eauto.
    +
      inverts IN...
      constructor...
      eapply label_in_teq_r; eauto.

  -
    splits; introv IN...
    +
      inverts IN as IN...
      inverts IN as IN...
    +
      inverts IN as IN...
      inverts IN as IN...

  -
    splits; introv IN...
    inverts IN as IN...
    inverts IN as IN.

  -
    splits; introv IN.
    +
      inverts IN as IN...
      inverts IN as IN...
    +
      inverts IN as IN...
      inverts IN as IN...

  -
    splits; introv IN.
    +
      inverts IN as IN...
    +
      inverts IN as IN...

  -
    splits; introv IN.
    +
      inverts IN as IN...
      inverts IN as IN...
    +
      inverts IN as IN...
      inverts IN as IN...
Qed.

Lemma label_in_rlist_ceq_l: forall R1 R2 l Ttx,
    ceq Ttx R1 R2 ->
    label_in_rlist l R1 -> label_in_rlist l R2.
Proof.
  introv I1 I2.
  forwards ~ : label_in_rlist_ceq I1.
  destruct_hypo.
  eapply H; eauto...
Qed.

Lemma label_in_rlist_single : forall R l rt,
    rtyp_label_in_rlist (r_SingleField l rt) R <->
    label_in_rlist l R.
Proof with auto.
  introv.
  split; introv IN.
  inductions IN...
  forwards ~ : IHIN...
  inductions IN...
Qed.

(** * tvar in rlist *)

Inductive tvar_in_rlist : typvar -> rlist -> Prop :=
  | tvar_in_rlist_head : forall a r R,
      tvar_in_rtyp a r ->
      tvar_in_rlist a (R_Cons r R)
  | tvar_in_rlist_tail : forall a r R,
      tvar_in_rlist a R ->
      tvar_in_rlist a (R_Cons r R)
.

Lemma tvar_in_rlist_ceq: forall R1 R2 a Ttx,
    ceq Ttx R1 R2 ->
    (tvar_in_rlist a R1 -> tvar_in_rlist a R2)
    /\
    (tvar_in_rlist a R2 -> tvar_in_rlist a R1).
Proof with auto.
  Hint Constructors tvar_in_rlist.
  introv EQ.
  inductions EQ; repeat destruct_hypo...
  
  -
    splits; introv IN...
    +
      inverts IN...
      constructor.
      eapply tvar_in_teq_l; eauto.
    +
      inverts IN...
      constructor...
      eapply tvar_in_teq_r; eauto.

  -
    splits; introv IN...
    +
      inverts IN as IN...
      inverts IN as IN...
    +
      inverts IN as IN...
      inverts IN as IN...

  -
    splits; introv IN...
    inverts IN as IN...
    inverts IN as IN.

  -
    splits; introv IN.
    +
      inverts IN as IN...
      inverts IN as IN...
    +
      inverts IN as IN...
      inverts IN as IN...

  -
    splits; introv IN.
    +
      inverts IN as IN...
    +
      inverts IN as IN...

  -
    splits; introv IN.
    +
      inverts IN as IN...
      inverts IN as IN...
    +
      inverts IN as IN...
      inverts IN as IN...
Qed.

Lemma tvar_in_rlist_ceq_l: forall R1 R2 l Ttx,
    ceq Ttx R1 R2 ->
    tvar_in_rlist l R1 -> tvar_in_rlist l R2.
Proof.
  introv I1 I2.
  forwards ~ : tvar_in_rlist_ceq I1.
  destruct_hypo.
  eapply H; eauto...
Qed.

Lemma tvar_in_rlist_single : forall R a,
    rtyp_label_in_rlist (r_TyVar_f a) R <->
    tvar_in_rlist a R.
Proof with auto.
  introv.
  split; introv IN.
  inductions IN...
  inductions IN...
Qed.


Lemma ceq_rtyp_label_in_rlist: forall T R1 R2 r,
    ceq T R1 R2 ->
    rtyp_label_in_rlist r R1 ->
    rtyp_label_in_rlist r R2.
Proof with auto.
  inductions r; introv EQ IN...
  inverts IN...

  apply tvar_in_rlist_single in IN.
  apply tvar_in_rlist_single.
  eapply tvar_in_rlist_ceq_l; eauto.

  apply label_in_rlist_single in IN.
  apply label_in_rlist_single.
  eapply label_in_rlist_ceq_l; eauto.

  inverts IN...
Qed.

(** * rlist in rlist *)

Inductive rlist_in_rlist : rlist -> rlist -> Prop :=
| rlist_in_head : forall rl,
    rlist_in_rlist rl rl
| rlist_in_cons : forall r' rl rl2,
    rlist_in_rlist rl rl2 ->
    rlist_in_rlist rl (R_Cons r' rl2).

Lemma cmp_tvar_in_rtyp : forall T r1 r2 a,
    cmp T r1 r2 ->
    tvar_in_rtyp a r2 ->
    cmp T r1 (r_TyVar_f a).
Proof with eauto.
  introv CMP IN.
  inductions IN...
Qed.

Lemma rtyp_in_rlist_rlist : forall r R1 R2,
    rtyp_in_rlist r R1 ->
    rlist_in_rlist R1 R2 ->
    rtyp_in_rlist r R2.
Proof with eauto.
  introv TY LI.
  inductions LI...
Qed.

Lemma wfcl_from_rlist_in_rlist : forall Ttx R1 R2,
    rlist_in_rlist R1 R2 ->
    wfcl Ttx R2 ->
    wfcl Ttx R1.
Proof.
  introv IN WFCL. inductions IN; auto.
  inverts WFCL; auto.
Qed.

Hint Constructors rlist_in_rlist.
Lemma rlist_in_rlist_tail : forall R1 R2 r,
    rlist_in_rlist (R_Cons r R1) R2 ->
    rlist_in_rlist R1 R2.
Proof.
  introv IN.
  inductions IN; eauto.
Qed.

Lemma rlist_in_rlist_head : forall R1 R2 r,
    rlist_in_rlist (R_Cons r R1) R2 ->
    rtyp_in_rlist r R2.
Proof.
  introv IN.
  inductions IN; eauto.
Qed.


Lemma cmp_label_in_rtyp : forall l r rt A Ttx,
    cmp Ttx A r ->
    label_in_rtyp l r ->
    wfrt Ttx rt ->
    cmp Ttx A (r_SingleField l rt).
Proof with auto.
  introv CMP IN WF.
  inductions IN; auto.
  eapply cmp_Base; eauto.
  forwards ~ : cmp_MergeE1 CMP.
  forwards ~ : cmp_MergeE2 CMP.
Qed.

Lemma binds_rtyp_label_in_rlist : forall Ttx R1 R2 r a,
    wftc Ttx ->
    wfr Ttx r ->
    binds a R2 Ttx ->
    rlist_in_rlist R1 R2 ->
    rtyp_label_in_rlist r R1 ->
    cmp Ttx (r_TyVar_f a) r.
Proof with auto.
  introv WF WR BD RLIST IN.
  inductions IN...
  apply cmp_Empty; eauto.


  apply cmp_tvar_in_rtyp with (r2:=r)...
  apply cmp_Tvar with (R:=R2); auto.
  eapply wfcl_from_binds_wftc; eauto.
  forwards ~  I: wfcl_from_rlist_in_rlist RLIST.
  eapply wfcl_from_binds_wftc; eauto.
  inverts I...
  eapply rtyp_in_rlist_rlist; eauto.

  forwards ~ I : rlist_in_rlist_tail RLIST.

  forwards ~ I : rlist_in_rlist_head RLIST.

  apply cmp_label_in_rtyp with (r:=r)...
  apply cmp_Tvar with (R:=R2)...
  eapply wfcl_from_binds_wftc; eauto.
  forwards ~ I2 : wfcl_from_rlist_in_rlist RLIST.
  eapply wfcl_from_binds_wftc; eauto.
  inverts I2...
  inverts WR...
 
  forwards ~ I : rlist_in_rlist_tail RLIST.

  inverts WR...
Qed.


Lemma same_tctx_general: 
  (forall T1 R,
      wfcl T1 R ->
        forall T2,
          wftc T1 ->
          wftc T2 ->
          same_tctx T1 T2 ->
          wfcl T2 R)
  /\ (
    forall T1 R,
      wfrt T1 R ->
      forall T2,
        wftc T1 ->
        wftc T2 ->
        same_tctx T1 T2 ->
        wfrt T2 R)
  /\ (
    forall T1 R,
      wfr T1 R ->
      forall T2,
        wftc T1 ->
        wftc T2 ->
        same_tctx T1 T2 ->
        wfr T2 R)
  /\ (
    forall T1 R1 R2,
      cmp T1 R1 R2 ->
      forall T2,
          wftc T1 ->
          wftc T2 ->
          same_tctx T1 T2 ->
          cmp T2 R1 R2)
  /\ (
    forall T1 R1 R2,
      ceq T1 R1 R2 ->
      forall T2,
          wftc T1 ->
          wftc T2 ->
          same_tctx T1 T2 ->
          ceq T2 R1 R2)
  /\(
    forall T1 R1 R2,
      teq T1 R1 R2 ->
      forall T2,
        wftc T1 ->
        wftc T2 ->
        same_tctx T1 T2 ->
        teq T2 R1 R2)
.
Proof with auto.
Scheme wfcl_ind := Induction for wfcl Sort Prop
  with wfrt_ind := Induction for wfrt Sort Prop
  with wfr_ind  := Induction for wfr Sort Prop
  with cmp_ind  := Induction for cmp Sort Prop
  with ceq_ind  := Induction for ceq Sort Prop
  with teq_ind  := Induction for teq Sort Prop.

Combined Scheme wfrt_mutind from wfcl_ind, wfrt_ind, wfr_ind, cmp_ind, ceq_ind, teq_ind.
  apply wfrt_mutind; intros; substs; 
    intros; substs; auto.
  - pick fresh X and apply wfrt_All...
  - forwards ~ (? & ?) : same_tctx_var H1 b.
    econstructor; eauto...
  - forwards ~ : H0 H2; eauto...
  - forwards ~ (R' & I1) : same_tctx_var H3 b.
    forwards ~ [I2 I3]: same_tctx_binds_ceq H3 b I1.
    forwards ~ I4 : rtyp_in_rlist_rtyp_label_in_rlist r0; auto.
    forwards ~ : H0...
    auto.
    eapply lc_rtyp_from_wfr; eauto...
    forwards ~ I5 : ceq_rtyp_label_in_rlist I2 I4.
    eapply binds_rtyp_label_in_rlist; eauto.
  - forwards ~ : H...
    eapply cmp_Base...
  - forwards ~ : H H0...
    eapply cmp_MergeE1...
  - forwards ~ : H H0...
    eapply cmp_MergeE2...
  - forwards ~ : H H1...
    forwards ~ : H0 H1...
    eauto.
  - forwards ~ : H H1...
    forwards ~ : H0 H1...
    eauto.
  - forwards ~ : H H2...
    pick fresh X and apply teq_CongAll; auto.
    apply H1...
    constructor...
    forwards ~ : H T2...
    constructor...
    forwards ~ : H T2...
    apply H0...
    constructor...
    forwards ~ : H T2...
    constructor...
    forwards ~ : H T2...
Qed.

Lemma same_tctx_teq : forall T1 A B T2,
    wftc T1 ->
    wftc T2 ->
    teq T1 A B ->
    same_tctx T1 T2 ->
    teq T2 A B.
Proof with eauto.
  introv I1 I2 I3 I4.
  pose (proj2 (proj2 (proj2 (proj2 (proj2 same_tctx_general ))))) as I.
  eauto.
Qed.

Lemma teq_rt_ConQuan_inv: forall Ttx R rt5 R0 rt0,
    wftc Ttx ->
    teq Ttx (rt_ConQuan R rt5) (rt_ConQuan R0 rt0) ->
    ( ceq Ttx R R0
      /\
      (
        exists L,
          forall a : atom,
            a `notin` L ->
            teq ([(a, R)] ++ Ttx) (open_rt_wrt_rtyp rt5 (r_TyVar_f a))
                (open_rt_wrt_rtyp rt0 (r_TyVar_f a))
      ) /\
      (
        exists L,
          forall a : atom,
            a `notin` L ->
            teq ([(a, R0)] ++ Ttx) (open_rt_wrt_rtyp rt5 (r_TyVar_f a))
                (open_rt_wrt_rtyp rt0 (r_TyVar_f a))
      )
    ).
Proof with eauto.
  introv WF EQ.
  inductions EQ.

  inverts H...
  splits...

  forwards ~ [EQ' [(L1 & ?) (L2 & ?)]]: IHEQ.
  splits...

  forwards ~ (R1 & D1 & ?): teq_rt_ConQuan_inv_l EQ1. substs.
  forwards ~ [N1  [(L1 & ?) (L2 & ?)]]: IHEQ1. clear IHEQ1.
  forwards ~ [N2  [(L3 & ?) (L4 & ?)]]: IHEQ2. clear IHEQ2.
  splits...
  exists (L1 \u L2 \u L3 \u L4 \u dom Ttx). intros.
  assert (same_tctx ([(a, R)] ++ Ttx) ([(a, R1)] ++ Ttx)).
    constructor...
  forwards ~ : H0 a.
  forwards ~ : H1 a.
  apply same_tctx_teq with (T1:=([(a, R1)] ++ Ttx))...

  exists (L1 \u L2 \u L3 \u L4 \u dom Ttx). intros.
  assert (same_tctx ([(a, R0)] ++ Ttx) ([(a, R1)] ++ Ttx)).
    constructor...
  forwards ~ : H0 a.
  forwards ~ : H1 a.
  apply same_tctx_teq with (T1:=([(a, R1)] ++ Ttx))...

  splits...
Qed.


Lemma wtt_teq : forall m PP TT FF e A EE1 n1 B EE2 n2,
  n1 + n2 < m ->
  wtt PP TT FF e A EE1 n1 ->
  wtt PP TT FF e B EE2 n2 ->
  teq TT A B.
Proof with eauto.
  intro m. induction m.
  introv LEN. inverts LEN.
  introv LEN TY1 TY2.
  generalize dependent B.
  generalize dependent EE2.
  generalize dependent n2.
  inductions TY1; introv LEN TY2.
  - Case "sub".
    forwards ~ : IHTY1 TY2. Omega.omega.
    apply teq_Trans with rt5...
  - Case "var".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Var_f x) 1 H3... Omega.omega.
    + SCase "var".
      assert (rt5 = B).
      eapply binds_unique...
      substs...
      apply teq_Refl...
      eapply wfrt_from_binds_wfc...
  - Case "nat".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Lit x) 1 H2... Omega.omega.
    + SCase "nat".
      apply teq_Refl...
  - Case "abs".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Abs rt5 re) (1+n1) H4... Omega.omega.
    + SCase "abs".
      pick fresh X.
      forwards ~ I1 : H0 X.
      forwards ~ I2 : H7 X.
      forwards ~ : IHm I1 I2. Omega.omega.
  - Case "app".
    inversions TY2.
    + SCase "sub".
      pick fresh X.
      forwards : IHm (re_App re1 re2) rt' (sexp_app ee1 ee2) (1+n1+n2) H... Omega.omega.
      eapply wtt_ArrowE...
    + SCase "app".
      forwards ~ I1 : IHTY1_1  H4. Omega.omega.
      eapply teq_rt_Fun_inv_r...
  - Case "base".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_SingleField l re) (1+n) H... Omega.omega.
    + SCase "base".
      forwards ~ I1 : IHTY1  H7. Omega.omega.
  - Case "empty".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Empty) 1 H2... Omega.omega.
    + SCase "empty".
      constructor...
  - Case "Merge".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Merge re1 re2) (1+n1+n2) H0... Omega.omega.
      constructor...
    + SCase "Merge".
      forwards ~ I1 : IHTY1_1  H2. Omega.omega.
      forwards ~ I2 : IHTY1_2  H6. Omega.omega.
  - Case "Res".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Res re l) (1+n) H0... Omega.omega.
    + SCase "Res".
      forwards ~ I1 : IHTY1  H5. Omega.omega.
      eapply teq_merge_inv...
  - Case "Selection".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_Selection re l) (1+n) H0... Omega.omega.
    + SCase "Selection".
      forwards ~ I1 : IHTY1  H5. Omega.omega.
      assert (label_ty_in_rtyp l rt5 (r_Merge (r_SingleField l rt5) r)) by auto.
      assert (label_ty_in_rtyp l B (r_Merge (r_SingleField l B) r)) by auto.
      forwards ~ : teq_label_ty_in_teq I1 H0.
  - Case "tabs".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_ConTyAbs R re) (1+n) H3... Omega.omega.
    + SCase "tabs".
      pick fresh X and apply teq_CongAll; auto.
      pick fresh Y.
      forwards ~ I1 : H1 X Y.
      forwards ~ I2 : H13 X Y.
      forwards ~ : IHm I1 I2. Omega.omega.
      pick fresh Y.
      forwards ~ I1 : H1 X Y.
      forwards ~ I2 : H13 X Y.
      forwards ~ : IHm I1 I2. Omega.omega.
  - Case "tapp".
    inversions TY2.
    + SCase "sub".
      forwards : IHm (re_ConTyApp re r) (1+n) H4... Omega.omega.
    + SCase "tapp".
      forwards ~ I1 : IHTY1  H6. Omega.omega.
      forwards ~ [_ [(L & I2) _]] : teq_rt_ConQuan_inv I1; auto.
      lets [? _ ]: wtt_regular TY1...
      pick fresh x.
      forwards ~ I3: I2 x.
      apply teq_subst_empty with (B:=r) in I3; auto.
      rewrite <- subst_rtyp_in_rt_intro in I3; auto.
      rewrite <- subst_rtyp_in_rt_intro in I3; auto.
      constructor...
      lets [? _]: wtt_regular TY1...
      lets [? ?]: wtt_regular TY1...
Qed.


Theorem translation_coherence': forall m e A B EE1 EE2 DD GG T1 T2 ee1 ee2 n1 n2 TT FF PP,
  n1 + n2 < m ->
  wtt PP TT FF e A EE1 n1 ->
  wtt PP TT FF e B EE2 n2 ->
  trans_Ttx PP TT DD ->
  trans_Gtx PP FF GG ->
  trans_rt PP A T1 ->
  trans_rt PP B T2 ->
  has_type DD GG EE1 Inf T1 ee1 ->
  has_type DD GG EE2 Inf T2 ee2 ->
  E_open DD GG ee1 ee2 T1 T2.
Proof with eauto.
  intro m. induction m.

  introv LEN. inverts LEN.

  introv LEN TY1 TY2 TRD TRG TRT1 TRT2 HT1 HT2.
  inverts TY1.

  + Case "sub".
    inverts HT1 as HT1.
    inverts HT1 as HT1 WFT SUB; [inverts H|].
    eapply coercion_compatibility1...
    forwards ~ I2 : typing_inference_unique H HT1.
    forwards ~ I3 : typing_inference_unique TY2 HT2.
    specialize IHm with (e:=e) (A:=rt5) (EE2:=EE2) (n1:=n)
                        (ee1:=e0) (B:=B).
    forwards ~ : IHm TY2 HT2... Omega.omega.
  + Case "var".
    inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "var x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      specialize IHm with (e := re_Var_f x) (A:=A) (EE1:=sexp_var_f x) (n1:=1)
                          (ee1 := exp_var_f x) (B:=rt5).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
      constructor...
      eapply coercion_compatibility2...
    - SCase "var x var".
      inverts HT2.
      assert (I: A = B).
        apply binds_unique with x FF...
      substs.
      forwards ~ : trans_rt_uniq TRT1 TRT2. substs.
      apply var_compatibility...

  + Case "nat".
    inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "nat x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      specialize IHm with (e := re_Lit x) (A:=rt_Base) (EE1:=sexp_lit x) (n1:=1)
                          (ee1 := exp_lit x) (B:=rt5).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
      eapply coercion_compatibility2...
    - SCase "nat x nat".
      inverts HT2.
      apply lit_compatibility...

  + Case "abs".
    inverts TRT1 as I00 I0.
    inverts TY2 as I1 I2 I3.
    - SCase "abs x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3. inverts I1.
      forwards ~ : trans_rt_uniq I00 H1. substs.
      forwards ~ : trans_rt_uniq I0 H2. substs.
      forwards ~ I6 : typing_inference_unique I1 M1.
      eapply coercion_compatibility2...
      specialize IHm with (e := re_Abs rt5 re)
                          (EE1 := (sexp_anno (sexp_abs ee) (sty_arrow A0 B0)))
                          (n1:=1+n0)
                          (T1:=sty_arrow A0 B0)
                          (A:=rt_Fun rt5 rt')
                          (ee1 := ee1) (B:=rt0).
      forwards ~ : IHm I1 TRD TRG M1. Omega.omega.
      pick fresh Y and apply wtt_ArrowI...
    - SCase "abs x abs".
      forwards ~ : trans_rt_uniq I00 H1. substs.
      forwards ~ : trans_rt_uniq I0 H2. substs.
      forwards ~ : trans_rt_uniq I00 I3... substs. clear H1 H2.
      inverts HT1 as HT1. inverts HT1 as WFT HT1; [ | inverts WFT].
      inverts HT2 as HT2. inverts HT2 as WFT2 HT2; [ | inverts WFT2].
      pick fresh X.
      apply abs_compatibility with X...
      forwards ~ HT1' : HT1 X.  clear HT1.
      forwards ~ HT2' : HT2 X.  clear HT2.
      forwards ~ I22 : H0 X.
      forwards ~ I33 : I2 X.
      inverts HT1' as M1 M2 M3.
        rewrite <- M3 in I22. inverts I22.
      inverts HT2' as M4 M5 M6 M7.
        rewrite <- M6 in I33. inverts I33.
      forwards ~ II1: typing_inference_unique I22 M1.
        constructor...
      forwards ~ II2: typing_inference_unique I33 M4.
        constructor...
      forwards ~ I4 : IHm I22 I33 M1 M4. Omega.omega.
      constructor...
      eapply coercion_compatibility1...
      eapply coercion_compatibility2...

  + Case "app".
    inverts HT1 as HT11 HT12.
    inverts HT12 as HT12 WFT SUB; [inverts H0 |].
    forwards I1 : typing_inference_unique H0 HT12...
    forwards I2 : typing_inference_unique H HT11... inverts I2 as I2 I3.
    forwards ~ : trans_rt_uniq I1 I2. substs. clear I2. clear I3.
    inverts TY2.
    - SCase "app x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3; [inverts H1 |].
      forwards I6 : typing_inference_unique H1 M1...
      eapply coercion_compatibility2...
      specialize IHm with (e := re_App re1 re2) (A:=A)
                          (EE1:=sexp_app ee0 ee3) (n1:=1+n0+n3)
                          (ee1 := exp_app e1 (exp_capp c e)) (B:=rt0).
      forwards ~ : IHm H1 M1... Omega.omega.
    - SCase "app x app".
      inverts HT2 as HT21 HT22.
      inverts HT22 as HT22 WFT SUB; [inverts H10 |].
      forwards I4 : typing_inference_unique H10 HT22...
      forwards I6 : typing_inference_unique H6 HT21...
      inverts I6 as I6 I7.
      forwards ~ : trans_rt_uniq I4 I6. substs. clear I6 I7.
      apply app_compatibility' with (A1:=A1) (A1':=A0)...
      forwards ~ : IHm H H6 HT11 HT21. Omega.omega.
      eapply coercion_compatibility1...
      eapply coercion_compatibility2...
      forwards ~ : IHm H0 H10 HT12 HT22. Omega.omega.

  + Case "base".
    inverts TRT1. inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "base x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := (re_SingleField l0 re))
                          (A:= rt_Record (r_SingleField l0 rt5))
                          (EE1:=sexp_rcd l0 ee) (n1:=1+n)
                          (ee1 := ee1) (B:=rt0).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "base x base".
      inverts TRT2.
      inverts H3.
      inverts HT2.
      inverts H2.
      apply record_compatibility...
      eapply IHm with (n1:=n)(n2:=n0)... Omega.omega.

  + Case "top".
    inverts TRT1. inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "top x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := re_Empty) (A:=rt_Record r_Empty) (EE1:=sexp_top) (n1:=1)
                          (ee1 := exp_unit) (B:=rt5).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "top x top".
      inverts TRT2.
      apply top_compatibility...
      eapply elaboration_well_type...

  + Case "merge".
    inverts TRT1. inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "merge x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := (re_Merge re1 re2))
                          (A:= rt_Record (r_Merge r1 r2))
                          (EE1:=sexp_merge ee0 ee3) (n1:=1+n0+n3)
                          (ee1 := exp_pair e1 e2) (B:=rt5).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "merge x merge".
      inverts TRT2.
      inverts H4.
      inverts HT2.
      inverts H6.
      forwards ~ : IHm H I1 H5 H4. Omega.omega.
      forwards ~ : IHm H0 I2 H8 H12. Omega.omega.
      assert (disjoint DD A1 A3).
        forwards ~ N1 : wtt_teq H I1.
        forwards ~ (co1 & co2 & [N2 N3]) : trans_teq N1 TRD...
        apply Disjoint.disjoint_symmetric...
        eapply Disjoint.disjoint_sub with (B:=A0)...
        apply Disjoint.disjoint_symmetric...
      assert (disjoint DD A0 A2).
        forwards ~ N1 : wtt_teq H0 I2.
        forwards ~ (co1 & co2 & [N2 N3]) : trans_teq N1 TRD...
        eapply Disjoint.disjoint_sub with (B:=A3)...
      apply pair_compatibility...

  + Case "Restr".
    inverts TRT1. inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "Restr x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      inverts H5 as M1 M2 M3; [inverts H |].
      specialize IHm with (e := (re_Res re l0))
                          (A:= rt_Record r)
                          (EE1 := sexp_anno ee T1) (n1:=1+n)
                          (ee1 := exp_capp c0 e0 ) (B:=rt0).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "Restr x Restr".
      inverts TRT2.
      inverts HT2.
      inverts H7; [inverts I1|].
      inverts H5; [inverts H|].
      forwards ~ : IHm H I1 H7 H1. Omega.omega.
      eapply typing_inference_unique ...
      eapply typing_inference_unique ...
      eapply coercion_compatibility2...
      eapply coercion_compatibility1...

  + Case "Select".
    inverts HT1 as HT1.
    inverts HT1 as HT1.
    inverts HT1 as HT1 WFT1 SUB1.
    inverts TY2 as I1 I2 I3.
    - SCase "Select x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2 WF2 SUB2;[inverts I1|].
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := (re_Selection re l0))
                          (A:= A)
                          (EE1 := sexp_proj (sexp_anno (ee) (sty_rcd l0 T1)) l0) (n1:=1+n)
                          (B:=rt5).
      forwards ~ I7 : IHm I1 HT2... Omega.omega.
    - SCase "Select x Select".
      inverts HT2 as HT2.
      inverts HT2 as HT2.
      inverts HT2 as HT2 WFT2 SUB2.
      forwards ~ : IHm H I1 HT1 HT2. Omega.omega.
      eapply typing_inference_unique ...
      eapply typing_inference_unique ...
      apply <- record_compatibility.
      eapply coercion_compatibility2...
      eapply coercion_compatibility1...

  + Case "tabs".
    inverts HT1 as HT11 HT12 WFE1.
    inverts TY2.
    - SCase "tabs x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3; [inverts H2 |].
      inverts TRT1 as WF TRT1.
      specialize IHm with (e := re_ConTyAbs R re) (A:=rt_ConQuan R rt5)
                          (EE1:= sexp_tabs A0 (sexp_tabs A0 ee)) (n1:=1+n)
                          (ee1 := exp_tabs e) (B:=rt0)
                          (T1:=sty_all A0 (sty_all A0 A)).
      eapply coercion_compatibility2...
      forwards ~ I4 : typing_inference_unique H2 M1.
      forwards ~ : IHm H2 M1...  Omega.omega.
    - SCase "tabs x tabs".
      inverts HT2 as _ HT22 WFE2.
      inverts TRT1 as TRT11 TRT12.
      inverts TRT2 as TRT21 TRT22.
      pick fresh X.
      forwards ~ I1 : HT12 X.
      forwards ~ M2 : HT22 X...
      inverts M2 as NN1 M2 NN2 NN3 NN4.
      unfold open_sexp_wrt_sty in I1.
      simpl in I1 .
      inverts I1 as I11 I12 I13 I14 I15.
      pick fresh Y.
      forwards ~ I1: I12 Y.
      forwards ~ I2 : H1 X Y.
      clear HT12 H1.
      assert (MM1: open_sty_wrt_sty_rec 0 (sty_var_f X) A0 = A0). apply open_sty_wrt_sty_lc_sty...
      assert (MM2: open_sty_wrt_sty_rec 0 (sty_var_f X) A = A). apply open_sty_wrt_sty_lc_sty...
      rewrite MM1 in * .
      rewrite MM2 in * .
      forwards ~ I3 : typing_inference_unique I2 I1.
        constructor...
        apply trans_Gtx_fresh_head_Eq...
      forwards ~ : trans_rlist_uniq TRT11 TRT21.
      substs.
      simpls.
      apply tabs_compatibility with X...
         forwards ~ [_ [_ [_ I4] ]] : styping_regular I1.
         inverts I4...
         inverts H5...
      forwards ~ M1 : H12 X Y...
      forwards ~ M22 : M2 Y...
      unfold open_sexp_wrt_sty in M22.
      forwards ~ I4 : typing_inference_unique M1 M22.
        constructor...
        apply trans_Gtx_fresh_head_Eq...
      specialize IHm with (DD:=((Y, A) :: (X, A) :: DD)) (GG:=GG).
      forwards ~ : IHm I2 M1 I1 M22... Omega.omega.
        constructor...
        apply trans_Gtx_fresh_head_Eq...
      rewrite <- I14.
      rewrite <- NN3.
      unfold open_sty_wrt_sty.
      simpls.
      apply tabs_compatibility with (X:=Y)...
      rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_upper_mutual.
      simpls...
      rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_upper_mutual.
      simpls...
      forwards ~ [_ [_ [_ NNN]]] : styping_regular M22.
      inverts NNN...
      rewrite MM1...
      rewrite MM1...

  + Case "tapp".
    inverts HT1 as HT1 MONO1 DIS1.
    inverts HT1 as HT1 MONO2 DIS2 EQ.
    forwards ~ I1 : typing_inference_unique H HT1.
    inverts I1 as TR2 I1.
    inverts TY2.
    - SCase "tapp x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3; [inverts H5 |].
      eapply coercion_compatibility2...
      forwards ~ I2 : typing_inference_unique H5 M1.
      specialize IHm with (e := (re_ConTyApp re r))
                          (A := (open_rt_wrt_rtyp rt5 r))
                          (EE1:= sexp_tapp (sexp_tapp ee A0) B0)
                          (n1:=1+n)
                          (ee1 := (exp_tapp (exp_tapp e0 (| A0 |)) (| B0 |))).
      forwards ~ : IHm H5 M1... Omega.omega.
      unfold open_sty_wrt_sty in EQ.
      simpl in EQ.
      inverts EQ.
      apply T_tapp with (B:=B2)...
      assert (NN: sty_all B2 (open_sty_wrt_sty_rec 1 A0 A) =
                                   (open_sty_wrt_sty  (sty_all B2 A)) A0).
        unfold open_sty_wrt_sty.
        simpls...
        change (open_sty_wrt_sty_rec 0 A0 B2) with (open_sty_wrt_sty B2 A0).
        rewrite open_sty_wrt_sty_lc_sty...
      rewrite NN...
      change (open_sty_wrt_sty_rec 0 A0 B2) with (open_sty_wrt_sty B2 A0) in DIS1.
        rewrite open_sty_wrt_sty_lc_sty in DIS1...
    - SCase "tapp x tapp".
      inverts HT2 as HT2 MONO1 DIS1.
      inverts HT2 as HT2 MONO2 DIS2.
      forwards ~ : trans_r_uniq H1 H9. substs.
      forwards ~ : bot_trans_r_uniq H2 H10. substs.
      unfold open_sty_wrt_sty in EQ.
      simpls. inverts EQ.
      forwards ~ I2 : typing_inference_unique H7 HT2.
      inverts I2.
      unfold open_sty_wrt_sty in H11.
      simpl in H11. inverts H11.
      apply tapp_compatibility' with (A1:=B2) (A2:=B4)...
      forwards ~ : IHm H H7 HT1 HT2. Omega.omega.
      apply trans_rt_all with (L:=L)...
      apply trans_rt_all with (L:=L0)...
      assert (NN1:(sty_all B2 (open_sty_wrt_sty_rec 1 A1 A))
              =(open_sty_wrt_sty (sty_all B2 A) A1)).
        unfold open_sty_wrt_sty.
        simpl.
        change (open_sty_wrt_sty_rec 0 A1 B2) with (open_sty_wrt_sty B2 A1).
        rewrite open_sty_wrt_sty_lc_sty...
        rewrite NN1.
      assert (NN2:(sty_all B4 (open_sty_wrt_sty_rec 1 A1 A0))
              =(open_sty_wrt_sty (sty_all B4 A0) A1)).
        unfold open_sty_wrt_sty.
        simpl.
        change (open_sty_wrt_sty_rec 0 A1 B4) with (open_sty_wrt_sty B4 A1).
        rewrite open_sty_wrt_sty_lc_sty...
        rewrite NN2.
     apply tapp_compatibility' with (A1:=B2) (A2:=B4)...
     forwards ~ (? & ?) : disjoint_regular H20.
     change (open_sty_wrt_sty_rec 0 A1 B2) with (open_sty_wrt_sty B2 A1) in DIS1.
        rewrite open_sty_wrt_sty_lc_sty in DIS1...
     change (open_sty_wrt_sty_rec 0 A1 B4) with (open_sty_wrt_sty B4 A1) in H16.
        rewrite open_sty_wrt_sty_lc_sty in H16...
     forwards ~ (? & ?) : disjoint_regular H16.

Qed.

Theorem translation_coherence'': forall e A B EE1 EE2 DD GG T1 T2 ee1 ee2 n1 n2 TT FF PP,
  wtt PP TT FF e A EE1 n1 ->
  wtt PP TT FF e B EE2 n2 ->
  trans_Ttx PP TT DD ->
  trans_Gtx PP FF GG ->
  trans_rt PP A T1 ->
  trans_rt PP B T2 ->
  has_type DD GG EE1 Inf T1 ee1 ->
  has_type DD GG EE2 Inf T2 ee2 ->
  E_open DD GG ee1 ee2 T1 T2.
Proof with eauto.
  introv H1 H2 H3 H4 H5 H6 H7 H8.
  forwards ~ : translation_coherence' H1 H2 H5 H6 H7...
Qed.

Theorem translation_coherence''': forall e A EE1 EE2 DD GG T ee1 ee2 n1 n2 TT FF PP,
  wtt PP TT FF e A EE1 n1 ->
  wtt PP TT FF e A EE2 n2 ->
  trans_Ttx PP TT DD ->
  trans_Gtx PP FF GG ->
  trans_rt PP A T ->
  has_type DD GG EE1 Inf T ee1 ->
  has_type DD GG EE2 Inf T ee2 ->
  E_open DD GG ee1 ee2 T T.
Proof with eauto.
  introv H1 H2 H3 H4 H5 H6 H7.
  forwards ~ : translation_coherence' H1 H2 H5 H6 H7.
Qed.

Theorem translation_coherence: forall e A EE1 EE2 T ee1 ee2 n1 n2,
  wtt nil nil nil e A EE1 n1 ->
  wtt nil nil nil e A EE2 n2 ->
  trans_rt nil A T ->
  has_type nil nil EE1 Inf T ee1 ->
  has_type nil nil EE2 Inf T ee2 ->
  E T T ee1 ee2.
Proof with eauto.
  introv H1 H2 H3 H4 H5.
  forwards ~ I : translation_coherence''' H1 H2 H3 H4 H5.
  constructor...
  constructor...
  unfold E_open in I.
  destructs I.
  forwards ~ : H8 (nil:sctx) (nil:list (atom * exp)) (nil:list (atom * exp)).
Qed.