Require Export LibTactics.
Require Export Metalib.Metatheory.
Require Export Assumed.
Require Import FSub_Definitions.
Require Import FSub_Infrastructure.
Require Import FSub_Lemmas.
Require Import Syntax_ott.
Require Import Fii_inf.
Require Import Infrastructure.
Require Import SourceProperty.
Require Import LR.
Require Import Compatibility.
Require Import FSub_Elaboration.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C1 := gather_atoms_with (fun x : ctx => dom x) in
  let C2 := gather_atoms_with (fun x : tctx => dom x) in
  let C3 := gather_atoms_with (fun x : stctx => dom x) in
  let C4 := gather_atoms_with (fun x : sctx => dom x) in
  let D1 := gather_atoms_with (fun x => fv_ty_in_ty x) in
  let D2 := gather_atoms_with (fun x => fv_ty_in_exp x) in
  let D3 := gather_atoms_with (fun x => fv_exp_in_exp x) in
  let D4 := gather_atoms_with (fun x => fv_sty_in_sty x) in
  let D5 := gather_atoms_with (fun x => fv_sty_in_sexp x) in
  let D6 := gather_atoms_with (fun x => fv_sexp_in_sexp x) in
  let D7 := gather_atoms_with (fun x => seqs_vars x) in
  let E1 := gather_atoms_with (fun x : atoms => x) in
  let E2 := gather_atoms_with (fun x : atom => singleton x) in
  let E3 := gather_atoms_with (fun x : fexp => fv_te x) in
  let E4 := gather_atoms_with (fun x : fexp => fv_ee x) in
  let E5 := gather_atoms_with (fun x : ftyp => fv_tt x) in
  let E6 := gather_atoms_with (fun x : env => dom x) in
  constr:(A \u B \u C1 \u C2 \u C3 \u C4 \u D1 \u D2 \u D3 \u D4 \u D5 \u D6 \u D7 \u E1 \u E2 \u E3 \u E4 \u E5 \u E6).

Hint Constructors typing.
Hint Constructors fsub_trans_D fsub_trans_G.

Lemma typing_inference_unique : forall F e A EE n DD GG B ee,
    typing F e A EE n ->
    fsub_trans_D F DD ->
    fsub_trans_G F GG ->
    has_type DD GG EE Inf B ee ->
    fsub_trans_typ F A B.
Proof.
  introv TY TRD TRG HT.
  forwards ~ (T & I1): fsub_trans_typ_exists F A.
  forwards ~ (ee' & I2) : trans_typing TY TRD TRG I1.
  forwards ~ : inference_unique HT I2. substs; auto.
Qed.

Theorem translation_coherence1: forall m F e A B EE1 EE2 DD GG T1 T2 ee1 ee2 n1 n2,
  n1 + n2 < m ->
  typing F e A EE1 n1 ->
  typing F e B EE2 n2 ->
  fsub_trans_D F DD ->
  fsub_trans_G F GG ->
  has_type DD GG EE1 Inf T1 ee1 ->
  has_type DD GG EE2 Inf T2 ee2 ->
  E_open DD GG ee1 ee2 T1 T2.
Proof with eauto.
  intro m. induction m.

  introv LEN. inverts LEN.

  introv LEN TY1 TY2 TRD TRG HT1 HT2.
  inverts TY1.

  + Case "top".
    inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "top x top".
      apply top_compatibility...
      eapply elaboration_well_type...
    - SCase "top x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := fexp_top) (A:=ftyp_top) (EE1:=sexp_top) (n1:=1)
                          (ee1 := exp_unit) (B:=S).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.

  + Case "nat".
    inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "nat x nat".
      inverts HT2.
      apply lit_compatibility...
    - SCase "nat x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~  I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := fexp_lit i) (A:=ftyp_nat) (EE1:=sexp_lit i) (n1:=1)
                          (ee1 := exp_lit i) (B:=S).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.

  + Case "var".
    forwards ~ TRT1 : typing_inference_unique HT1...
    inverts HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "var x var".
      forwards ~ TRT2 : typing_inference_unique HT2...
      inverts HT2.
      assert (I: bind_typ A = bind_typ B).
        apply binds_unique with x F...
      inverts I.
      forwards ~ : fsub_trans_typ_uniq TRT1 TRT2. substs.
      apply var_compatibility...
    - SCase "var x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      specialize IHm with (e := fexp_fvar x) (A:=A) (EE1:=sexp_var_f x) (n1:=1)
                          (ee1 := exp_var_f x) (B:=S).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
      eapply coercion_compatibility2...

  + Case "abs".
    lets I00 : typing_inference_unique HT1...
    inverts I00 as I01 I02.
    inverts TY2 as I1 I2 I3.
    - SCase "abs x abs".
      inverts I2 as TRT3 TRT4.
      inverts H0 as TRT5 TRT6.
      assert (I' : uniq F).
        pick fresh X. forwards ~ : I1 X.
        assert (II: uniq ((X, bind_typ V) :: F)) by auto. inverts II...
      forwards ~ : fsub_trans_typ_uniq I01 TRT3... substs.
      forwards ~ : fsub_trans_typ_uniq TRT3 TRT5... substs. clear TRT5.
      inverts HT1 as HT1. inverts HT1 as WFT HT1; [ | inverts WFT].
      inverts HT2 as HT2. inverts HT2 as WFT2 HT2; [ | inverts WFT2].
      pick fresh X.
      apply abs_compatibility with X...
      forwards ~ HT1' : HT1 X.  clear HT1.
      forwards ~ HT2' : HT2 X.  clear HT2.
      forwards ~ I2 : H X.
      forwards ~ I3 : I1 X.
      inverts HT1' as M1 M2 M3.
        rewrite <- M3 in I2. inverts I2.
      inverts HT2' as M4 M5 M6.
        forwards ~ I4 : I1 X.
        rewrite <- M6 in I4. inverts I4.
      forwards ~ II1: typing_inference_unique I2 M1.
        constructor...
        constructor...
      forwards ~ II2: typing_inference_unique I3 M4.
        constructor...
        constructor...
      forwards ~ I4 : IHm I2 I3 M1 M4. Omega.omega.
        constructor...
        constructor...
      eapply coercion_compatibility1...
      eapply coercion_compatibility2...
    - SCase "abs x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3. inverts I1.
      inverts H0 as TRT3 TRT4.
      forwards ~ : fsub_trans_typ_uniq I01 TRT3. substs. clear TRT3.
      forwards ~ : fsub_trans_typ_uniq I02 TRT4. substs. clear TRT4.
      forwards ~ I6 : typing_inference_unique I1 M1.
      specialize IHm with (e := fexp_abs V e1) (A:=ftyp_arrow V T0)
                          (EE1 := (sexp_anno (sexp_abs EE) (sty_arrow A'0 B'0)))
                          (n1:=1+n)
                          (T1:=sty_arrow A'0 B'0)
                          (ee1 := ee1) (B:=S).
      forwards ~ : IHm I1 TRD TRG M1. Omega.omega.
      pick fresh Y and apply typing_abs...
      eapply coercion_compatibility2...

  + Case "app".
    inverts HT1 as HT11 HT12.
    inverts HT12 as HT12 WFT SUB; [inverts H0 |].
    forwards I1 : typing_inference_unique H0 HT12...
    forwards I2 : typing_inference_unique H HT11... inverts I2 as I2 I3.
    forwards ~ : fsub_trans_typ_uniq I1 I2. substs. clear I2. clear I3.
    inverts TY2.
    - SCase "app x app".
      inverts HT2 as HT21 HT22.
      inverts HT22 as HT22 WFT SUB; [inverts H8 |].
      forwards I4 : typing_inference_unique H8 HT22...
      forwards I6 : typing_inference_unique H4 HT21...
      inverts I6 as I6 I7.
      forwards ~ : fsub_trans_typ_uniq I4 I6. substs. clear I6 I7.
      apply app_compatibility' with (A1:=A1) (A1':=A0)...
      forwards ~ : IHm H H4 HT11 HT21. Omega.omega.
      eapply coercion_compatibility1...
      eapply coercion_compatibility2...
      forwards ~ : IHm H0 H8 HT12 HT22. Omega.omega.
    - SCase "app x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3; [inverts H1 |].
      forwards I6 : typing_inference_unique H1 M1...
      eapply coercion_compatibility2...
      specialize IHm with (e := fexp_app e1 e2) (A:=A) (EE1:=sexp_app EE0 EE3) (n1:=1+n0+n3)
                          (ee1 := exp_app e0 (exp_capp c e)) (B:=S).
      forwards ~ : IHm H1 M1... Omega.omega.

  + Case "tabs".
    inverts HT1 as HT11 HT12 WFE1.
    inverts TY2.
    - SCase "tabs x tabs".
      inverts HT2 as _ HT22 WFE2.
      pick fresh X.
      forwards ~ I1 : HT12 X.
      forwards ~ I2 : H0 X.
      clear HT12 H0.
      forwards ~ I3 : typing_inference_unique I2 I1.
        constructor...
        constructor...
      apply tabs_compatibility with X...
         forwards ~ [_ [_ [_ I4] ]] : styping_regular I1.
         inverts I4...
      forwards ~ M1 : H8 X...
      forwards ~ M2 : HT22 X...
      clear H8 HT22.
      forwards ~ I4 : typing_inference_unique M1 M2.
        constructor...
        constructor...
      specialize IHm with (DD:=(X ~ sty_top ++ DD)) (GG:=GG).
      forwards ~ : IHm I2 M1 I1 M2. Omega.omega.
        constructor...
        constructor...
    - SCase "tabs x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3; [inverts H1 |].
      specialize IHm with (e := fexp_tabs V e1) (A:=ftyp_all V T0)
                          (EE1:= sexp_tabs sty_top EE) (n1:=1+n)
                          (ee1 := exp_tabs e) (B:=S).
      eapply coercion_compatibility2...
      forwards ~ I4 : typing_inference_unique H1 M1.
      forwards ~ : IHm H1 M1... Omega.omega.

  + Case "tapp".
    inverts HT1 as HT1.
    inverts HT1 as HT1 WFT1 SUB1.
    inverts HT1 as HT1 MN DIS.
    forwards ~ I1 : typing_inference_unique H HT1.
    inverts I1 as WFT2 I1.
    inverts TY2.
    - SCase "tapp x tapp".
      inverts HT2 as HT2.
      inverts HT2 as HT2 WFT3 SUB2. inverts HT2 as HT2 MN2 DIS2.
      apply coercion_compatibility1 with (open_sty_wrt_sty C A1)...
      apply coercion_compatibility2 with (open_sty_wrt_sty C0 A0)...
      forwards ~ : fsub_trans_typ_uniq H2 H10. substs.
      apply tapp_compatibility' with (A1:=sty_top) (A2:=B0)...
      clear H3.
      forwards ~ I4 : typing_inference_unique H6 HT2.
      forwards ~ : IHm H H6 HT1 HT2. Omega.omega.
    - SCase "tapp x sub".
      inverts HT2 as HT2.
      inverts HT2 as M1 M2 M3; [inverts H4 |].
      eapply coercion_compatibility2...
      forwards ~ I2 : typing_inference_unique H4 M1.
      specialize IHm with (e := fexp_tapp e1 T) (A:=open_tt T3 T)
                          (EE1:= sexp_anno (sexp_tapp EE A1) T1)
                          (n1:=1+n) (ee1 := exp_capp c (exp_tapp e0 (| A1 |))).
      forwards ~ : IHm H4 M1... Omega.omega.

  + Case "sub".
    inverts HT1 as HT1.
    inverts HT1 as HT1 WFT SUB; [inverts H|].
    eapply coercion_compatibility1...
    forwards ~ I2 : typing_inference_unique H HT1.
    specialize IHm with (e:=e) (A:=S) (EE1:=EE) (n1:=n)
                        (ee1:=e0) (B:=B).
    forwards ~ : IHm TY2 HT2... Omega.omega.

  + Case "nil".
    inverts HT1 as HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "nil x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := fexp_rcd_nil) (A:=ftyp_rcd_nil) (EE1:=sexp_top) (n1:=1)
                          (ee1 := exp_unit) (B:=S).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "nil x nil".
      apply top_compatibility...
      eapply elaboration_well_type...

  + Case "cons".
    inverts HT1 as HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "cons x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      specialize IHm with (e := fexp_rcd_cons i e1 e2) (A:=ftyp_rcd_cons i T0 T3)
                          (EE1:= sexp_merge (sexp_rcd i EE0) EE3) (n1:=1+n0+n3)
                          (B:=S).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "cons x cons".
      inverts HT2.
      inverts HT1 as I0 I1 I2 I3.
      inverts H6 as I4.
      forwards ~ I5 : typing_inference_unique H I0.
      forwards ~ I6 : typing_inference_unique I1 I4.
      forwards ~ I7 : IHm H I1 I0 I4. Omega.omega.
      forwards ~ I8 : typing_inference_unique H0 H9.
      forwards ~ I9 : typing_inference_unique I2 H11.
      forwards ~ I10 : IHm H0 I2 H9 H11. Omega.omega.
      apply pair_compatibility...
      apply record_compatibility...
      eapply trans_label_notin; eauto.
      eapply trans_label_notin with (A:=T3); eauto.
  + Case "proj".
    inverts HT1 as HT1.
    inverts TY2 as I1 I2 I3.
    - SCase "proj x sub".
      inverts HT2 as HT2.
      inverts HT2 as HT2. inverts I1.
      forwards ~ I4 : typing_inference_unique I1 HT2.
      eapply coercion_compatibility2...
      inverts HT1...
      specialize IHm with (e := fexp_rcd_proj e1 i) (A:=A)
                          (EE1:= sexp_proj (sexp_anno EE0 (sty_rcd i T1)) i)
                          (n1:=1+n)
                          (B:=S)
                          (ee1:= ee1).
      forwards ~ I7 : IHm I1 TRD TRG HT2... Omega.omega.
    - SCase "proj x proj".
      inverts HT2 as I0 .
      inverts I0 as I0.
      inverts I0 as I0.
      inverts HT1 as I1 I2.
      inverts H8 as I3 I4 I5.
      forwards ~ I10 : typing_inference_unique H I3.
      forwards ~ I11 : typing_inference_unique I1 I0.
      forwards ~ : IHm H I1 I3 I0... Omega.omega.
      apply <- record_compatibility.
      eapply coercion_compatibility2...
      eapply coercion_compatibility1...
Qed.

Theorem translation_coherence2: forall F e A B EE1 EE2 DD GG T1 T2 ee1 ee2 n1 n2,
  typing F e A EE1 n1 ->
  typing F e B EE2 n2 ->
  fsub_trans_D F DD ->
  fsub_trans_G F GG ->
  has_type DD GG EE1 Inf T1 ee1 ->
  has_type DD GG EE2 Inf T2 ee2 ->
  E_open DD GG ee1 ee2 T1 T2.
Proof with eauto.
  introv H1 H2 H3 H4 H5 H6.
  forwards ~ : translation_coherence1 H1 H2 H5 H6 ...
Qed.

Theorem translation_coherence3: forall F e A EE1 EE2 DD GG T ee1 ee2 n1 n2,
  typing F e A EE1 n1 ->
  typing F e A EE2 n2 ->
  fsub_trans_D F DD ->
  fsub_trans_G F GG ->
  has_type DD GG EE1 Inf T ee1 ->
  has_type DD GG EE2 Inf T ee2 ->
  E_open DD GG ee1 ee2 T T.
Proof with eauto.
  introv H1 H2 H3 H4 H5 H6.
  forwards ~ : translation_coherence1 H1 H2 H5 H6 .
Qed.

Theorem translation_coherence: forall e A EE1 EE2 T ee1 ee2 n1 n2,
  typing nil e A EE1 n1 ->
  typing nil e A EE2 n2 ->
  has_type nil nil EE1 Inf T ee1 ->
  has_type nil nil EE2 Inf T ee2 ->
  E T T ee1 ee2.
Proof with eauto.
  introv H1 H2 H3 H4.
  forwards ~ I : translation_coherence3 H1 H2 H3 H4.
  unfold E_open in I.
  destructs I.
  forwards ~ : H7 (nil:sctx) (nil:list (atom * exp)) (nil:list (atom * exp)).
Qed.

Inductive fvalue : fexp -> Prop :=
| fvalue_lit : forall i,
    fvalue (fexp_lit i)
| fvalue_abs : forall t e,
    fvalue (fexp_abs t e)
| fvalue_rcd_nil:
    fvalue (fexp_rcd_nil)
| fvalue_rcd_cons : forall e1 e2 i,
    fvalue e1 ->
    fvalue e2 ->
    fvalue (fexp_rcd_cons i e1 e2)
.


Inductive freduce  : fexp -> fexp -> Prop :=
| freduce_app1 : forall e1 e2 e1',
    freduce e1 e1' ->
    freduce (fexp_app e1 e2) (fexp_app e1' e2)
| freduce_app2 : forall e1 e2 e2',
    freduce e2 e2' ->
    freduce (fexp_app e1 e2) (fexp_app e1 e2')
| freduce_app : forall t e v,
    fvalue v ->
    freduce (fexp_app (fexp_abs t e) v) (open_ee e v)
| freduce_proj_here : forall i v1 v2,
    fvalue (fexp_rcd_cons i v1 v2) ->
    freduce (fexp_rcd_proj (fexp_rcd_cons i v1 v2) i) v1
| freduce_proj_there : forall i v1 v2 v3 j,
    fvalue (fexp_rcd_cons j v1 v2) ->
    i <> j ->
    freduce (fexp_rcd_proj v2 i) v3 ->
    freduce (fexp_rcd_proj (fexp_rcd_cons j v1 v2) i) v3
.

Theorem translation_coherence4: forall e A B EE1 EE2 T1 T2 ee1 ee2 n1 n2,
  typing nil e A EE1 n1 ->
  typing nil e B EE2 n2 ->
  has_type nil nil EE1 Inf T1 ee1 ->
  has_type nil nil EE2 Inf T2 ee2 ->
  E_open nil nil ee1 ee2 T1 T2.
Proof with eauto.
  introv H1 H2 H3 H4.
  forwards ~ I : translation_coherence2 H1 H2 H3 H4...
Qed.
