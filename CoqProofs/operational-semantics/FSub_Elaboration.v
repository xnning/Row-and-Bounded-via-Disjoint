Require Export LibTactics.
Require Export Metalib.Metatheory.
Require Export Assumed.
Require Import FSub_Definitions.
Require Import FSub_Infrastructure.
Require Import FSub_Lemmas.
Require Import Syntax_ott.
Require Import Fii_inf.
Require Import Infrastructure.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C3 := gather_atoms_with (fun x : stctx => dom x) in
  let C4 := gather_atoms_with (fun x : sctx => dom x) in
  let D4 := gather_atoms_with (fun x => fv_sty_in_sty x) in
  let D5 := gather_atoms_with (fun x => fv_sty_in_sexp x) in
  let D6 := gather_atoms_with (fun x => fv_sexp_in_sexp x) in
  let D19 := gather_atoms_with (fun x : stctx => fv_stctx x) in
  let E1 := gather_atoms_with (fun x : atoms => x) in
  let E2 := gather_atoms_with (fun x : atom => singleton x) in
  let E3 := gather_atoms_with (fun x : fexp => fv_te x) in
  let E4 := gather_atoms_with (fun x : fexp => fv_ee x) in
  let E5 := gather_atoms_with (fun x : ftyp => fv_tt x) in
  let E6 := gather_atoms_with (fun x : env => dom x) in
  constr:(A \u B \u C3 \u C4 \u D4 \u D5 \u D6 \u D19 \u E1 \u E2 \u E3 \u E4 \u E5 \u E6).

Inductive fsub_trans_typ : env -> ftyp -> sty -> Prop :=
| fsub_trans_typ_top : forall FF,
    fsub_trans_typ FF ftyp_top sty_top
| fsub_trans_typ_nat : forall FF,
    fsub_trans_typ FF ftyp_nat sty_nat
| fsub_trans_typ_fvar_bind_sub_eq : forall FF a A B,
    binds a (bind_sub A) FF ->
    fsub_trans_typ FF A B ->
    fsub_trans_typ FF (ftyp_fvar a) (sty_and (sty_var_f a) B)
| fsub_trans_typ_arrow : forall FF A A' B B',
    fsub_trans_typ FF A A' ->
    fsub_trans_typ FF B B' ->
    fsub_trans_typ FF (ftyp_arrow A B) (sty_arrow A' B')
| fsub_trans_typ_all : forall L FF A B C,
    wf_typ FF A ->
    (forall X , X `notin` L ->
           fsub_trans_typ (X ~ bind_sub A ++ FF)
                          (open_tt B X)
                          (open_sty_wrt_sty C (sty_var_f X))) ->
    fsub_trans_typ FF (ftyp_all A B) (sty_all sty_top C)
| fsub_trans_typ_rcd_nil : forall FF,
    fsub_trans_typ FF (ftyp_rcd_nil) (sty_top)
| fsub_trans_typ_rcd_cons : forall FF i A' B' A B,
    fsub_trans_typ FF A A' ->
    fsub_trans_typ FF B B' ->
    rt_type B ->
    fsub_trans_typ FF (ftyp_rcd_cons i A B) (sty_and (sty_rcd i A') B')
.

Hint Constructors fsub_trans_typ.

Inductive fsub_trans_D : env -> stctx -> Prop :=
| fsub_trans_D_empty :
    fsub_trans_D empty nil
| fsub_trans_D_bind_sub : forall a FF Ttx A,
    fsub_trans_D FF Ttx ->
    a \notin dom FF \u dom Ttx ->
    fsub_trans_D (a ~ bind_sub A ++ FF) (a ~ sty_top ++ Ttx)
| fsub_trans_D_bind_typ : forall x FF Ttx A,
    fsub_trans_D FF Ttx ->
    fsub_trans_D (x ~ bind_typ A ++ FF) Ttx
.

Inductive fsub_trans_G : env -> sctx -> Prop :=
| fsub_trans_G_empty :
    fsub_trans_G empty nil
| fsub_trans_G_bind_sub : forall a FF Ttx A,
    fsub_trans_G FF Ttx ->
    a `notin` dom Ttx ->
    fsub_trans_G (a ~ bind_sub A ++ FF) Ttx
| fsub_trans_G_bind_typ : forall x FF Ttx A B,
    fsub_trans_G FF Ttx ->
    fsub_trans_typ FF A B ->
    x `notin` dom FF \u dom Ttx ->
    fsub_trans_G (x ~ bind_typ A ++ FF) (x ~ B ++ Ttx)
.
Hint Constructors fsub_trans_typ fsub_trans_D fsub_trans_G.

Inductive label_notin : i -> ftyp -> Prop :=
| label_notin_nil : forall i,
    label_notin i (ftyp_rcd_nil)
| label_notin_cons : forall i j A B,
    i <> j ->
    label_notin i B ->
    label_notin i (ftyp_rcd_cons j A B)
.

Inductive typing : env -> fexp -> ftyp -> sexp -> nat -> Prop :=
  | typing_top : forall E,
      wf_env E ->
      typing E fexp_top ftyp_top sexp_top 1
  | typing_lit : forall i E,
      wf_env E ->
      typing E (fexp_lit i) ftyp_nat (sexp_lit i) 1
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E (fexp_fvar x) T (sexp_var_f x) 1
  | typing_abs : forall L E V e1 T1 EE A n,
      (forall x : atom, x `notin` L ->
        typing (x ~ bind_typ V ++ E) (open_ee e1 x) T1 (open_sexp_wrt_sexp EE (sexp_var_f x)) n) ->
      fsub_trans_typ E (ftyp_arrow V T1) A ->
      typing E (fexp_abs V e1) (ftyp_arrow V T1) (sexp_anno (sexp_abs EE) A) (1+n)
  | typing_app : forall T1 E e1 e2 T2 EE1 EE2 n1 n2,
      typing E e1 (ftyp_arrow T1 T2) EE1 n1 ->
      typing E e2 T1 EE2 n2 ->
      typing E (fexp_app e1 e2) T2 (sexp_app EE1 EE2) (1 + n1 + n2)
  | typing_tabs : forall L E V e1 T1 EE A n,
      fsub_trans_typ E V A ->
      (forall X : atom, X `notin` L ->
                   typing (X ~ bind_sub V ++ E) (open_te e1 X)
                          (open_tt T1 X)
                          (open_sexp_wrt_sty EE (sty_var_f X)) n) ->
      typing E (fexp_tabs V e1) (ftyp_all V T1) (sexp_tabs sty_top EE) (1+n)
  | typing_tapp : forall T1 E e1 T T2 EE A1 A2 n,
      typing E e1 (ftyp_all T1 T2) EE n ->
      fmono E T ->
      fsub E T T1 ->
      fsub_trans_typ E T A1 ->
      fsub_trans_typ E (open_tt T2 T) A2 ->
      typing E (fexp_tapp e1 T) (open_tt T2 T) (sexp_anno (sexp_tapp EE A1) A2) (1+n)
  | typing_sub : forall S E e T EE A n,
      typing E e S EE n ->
      fsub E S T ->
      fsub_trans_typ E T A ->
      typing E e T (sexp_anno EE A) (1+n)
  | typing_rcd_nil : forall E,
      wf_env E ->
      typing E (fexp_rcd_nil) ftyp_rcd_nil (sexp_top) 1
  | typing_rcd_cons : forall E i e1 e2 T1 T2 EE1 EE2 n1 n2,
      typing E e1 T1 EE1 n1 ->
      typing E e2 T2 EE2 n2 ->
      rt_expr e2 ->
      rt_type T2 ->
      label_notin i T2 ->
      typing E (fexp_rcd_cons i e1 e2) (ftyp_rcd_cons i T1 T2)
             (sexp_merge (sexp_rcd i EE1) EE2)
             (1 +n1 + n2)
  | typing_rcd_proj : forall E i e1 T1 T2 EE1 A n,
      typing E e1 (ftyp_rcd_cons i T1 T2) EE1 n ->
      fsub_trans_typ E T1 A ->
      typing E (fexp_rcd_proj e1 i) T1
               (sexp_proj (sexp_anno EE1 (sty_rcd i A)) i) (1 + n)
.

(* ********************************************************************** *)
(** * Unicity *)

Lemma fsub_trans_typ_uniq : forall EE T A B,
    uniq EE ->
    fsub_trans_typ EE T A ->
    fsub_trans_typ EE T B ->
    A = B.
Proof with auto.
  introv UNIQ TR1 TR2.
  generalize dependent B.
  inductions TR1; introv TR2; inverts TR2; repeat f_equal; eauto.
  forwards ~ : binds_unique H H1. inverts H0...

  pick_fresh X.
  forwards ~ I : H7 X.
  forwards ~ I2: H1 I.
  apply open_sty_wrt_sty_inj in I2...
Qed.

Lemma fsub_trans_G_uniq : forall EE A B,
    uniq EE ->
    fsub_trans_G EE A ->
    fsub_trans_G EE B ->
    A = B.
Proof with eauto.
  introv UNI TR1 TR2.
  generalize dependent B.
  inductions TR1; introv TR2; inverts TR2; try inverts UNI; f_equal; eauto.
  assert (B = B1).
    eapply fsub_trans_typ_uniq...
  substs...
Qed.

Lemma fsub_trans_D_uniq : forall EE A B,
    uniq EE ->
    fsub_trans_D EE A ->
    fsub_trans_D EE B ->
    A = B.
Proof with eauto.
  introv UNI TR1 TR2.
  generalize dependent B.
  inductions TR1; introv TR2; inverts TR2; try inverts UNI; f_equal; eauto.
Qed.

(* ********************************************************************** *)
(** * WEAKENING *)

Lemma fsub_trans_typ_weakening : forall FF A B EE1 EE2,
    fsub_trans_typ (EE1 ++ EE2) A B ->
    uniq (EE1 ++ FF ++ EE2) ->
    fsub_trans_typ (EE1 ++ FF ++ EE2) A B.
Proof with eauto.
  introv TR UNIQ. inductions TR...
  pick fresh X and apply fsub_trans_typ_all.
  apply wf_typ_weakening...
  rewrite_env (([(X, bind_sub A)] ++ EE1) ++ FF ++ EE2).
  apply H1...
  simpl_env...
Qed.

Lemma fsub_trans_typ_weakening_head : forall FF A B EE,
    fsub_trans_typ EE A B ->
    uniq (FF ++ EE) ->
    fsub_trans_typ (FF ++ EE) A B.
Proof with eauto.
  intros.
  rewrite_env (nil ++ FF ++ EE).
  apply fsub_trans_typ_weakening...
Qed.


(* ********************************************************************** *)
(** * BINDING AND FV *)

Lemma fsub_trans_G_typ_exists : forall x T E G,
  uniq E ->
  binds x (bind_typ T) E ->
  fsub_trans_G E G ->
  exists A, binds x A G /\ fsub_trans_typ E T A.
Proof with eauto.
  introv UNIQ BD TRG.
  induction TRG.
  +
  false BD.
  +
  analyze_binds BD.
  inverts UNIQ.
  forwards ~ (B & [I1 I2]) : IHTRG.
  exists B. splits...
  apply fsub_trans_typ_weakening_head...
  +
  analyze_binds BD.
  inverts BindsTacVal...
  exists B.
  split...
  apply fsub_trans_typ_weakening_head...
  inverts UNIQ.
  forwards ~ (C & [I1 I2]) : IHTRG.
  exists C.
  split...
  apply fsub_trans_typ_weakening_head...
Qed.

Lemma fsub_trans_G_typ : forall x T E A G,
  uniq E ->
  binds x (bind_typ T) E ->
  fsub_trans_typ E T A ->
  fsub_trans_G E G ->
  binds x A G.
Proof with eauto.
  introv UNIQ BD TR TRG.
  forwards ~ (B & [I1 I2]): fsub_trans_G_typ_exists UNIQ BD TRG.
  forwards ~ : fsub_trans_typ_uniq TR I2.
  substs...
Qed.

Lemma fsub_trans_D_sub : forall x T E G,
  binds x (bind_sub T) E ->
  fsub_trans_D E G ->
  binds x sty_top G.
Proof with eauto.
  introv BD TR.
  inductions TR...
  analyze_binds BD.
  analyze_binds BD.
Qed.

Lemma fsub_trans_typ_preserve_notin : forall E T A a,
  fsub_trans_typ E T A ->
  a `notin` dom E ->
  a `notin` fv_sty_in_sty A.
Proof with eauto.
  introv TR. inductions TR; simpls; introv NOTIN...
  forwards ~ : IHTR...
  assert (a <> a0).
  introv EQ. substs.
  eapply binds_dom_contradiction...
  eauto.
  pick fresh X.
  forwards ~ : H0 X.
  rewrite fv_sty_in_sty_open_sty_wrt_sty_lower...
Qed.

Lemma fsub_trans_D_preserve_notin : forall FF D x,
  fsub_trans_D FF D ->
  x `notin` dom FF ->
  x `notin` dom D.
Proof.
  introv tr notin.
  inductions tr; simpls; eauto.
Qed.

Lemma fsub_trans_G_preserve_notin : forall FF D x,
  fsub_trans_G FF D ->
  x `notin` dom FF ->
  x `notin` dom D.
Proof.
  introv tr notin.
  inductions tr; simpls; eauto.
Qed.

(* ********************************************************************** *)
(** * Well-formedness *)

Ltac destruct_hypo :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Lemma fsub_trans_typ_regular : forall E T A,
    fsub_trans_typ E T A ->
    type T /\ lc_sty A /\ wf_typ E T.
Proof with eauto.
  introv TR. inductions TR; repeat destruct_hypo; splits...
  +
  pick fresh X and apply type_all...
  eapply type_from_wf_typ...
  forwards ~ : H1 X.
  destruct_hypo...
  +
  pick fresh X.
  forwards ~ : H1 X.
  repeat destruct_hypo...
  eapply lc_sty_all_exists...
  +
  pick fresh X and apply wf_typ_all...
  apply H1...
Qed.

Hint Extern 1 (type ?T) =>
   match goal with
  | H: fsub_trans_typ _ T _ |- _ => apply (proj1 (fsub_trans_typ_regular _ _ _ H))
   end.

Hint Extern 1 (lc_sty ?A) =>
   match goal with
  | H: fsub_trans_typ _ _ A |- _ => apply (proj1 (proj2 (fsub_trans_typ_regular _ _ _ H)))
   end.

Hint Extern 1 (wf_typ ?E ?A) =>
   match goal with
  | H: fsub_trans_typ E A _ |- _ => apply (proj2 (proj2 (fsub_trans_typ_regular _ _ _ H)))
   end.

Lemma fsub_trans_typ_swft : forall E D T A,
    fsub_trans_D E D ->
    fsub_trans_typ E T A ->
    wf_typ E T ->
    swft D A.
Proof with eauto.
  introv TRD TR WFE.
  generalize dependent D.
  inductions TR; introv TRD; simpls...
  +
  constructor...
  inverts WFE...
  forwards ~ : fsub_trans_D_sub H2 TRD...
  +
  inverts WFE.
  pick fresh X and apply swft_all...
  apply H1...
  apply H6...
  constructor...
Qed.

Lemma fsub_trans_D_swfte : forall E D,
    fsub_trans_D E D ->
    wf_env E ->
    swfte D.
Proof with eauto.
  introv TRT WFE. inductions TRT; simpls...
  inverts WFE...
  constructor...
  inverts WFE...
Qed.

Lemma fsub_trans_G_swfe : forall E D G,
    fsub_trans_D E D ->
    fsub_trans_G E G ->
    wf_env E ->
    swfe D G.
Proof with eauto.
  introv TRD TRG WFE.
  generalize dependent D.
  inductions TRG; introv TRD; simpls...
  +
  inverts WFE...
  inverts TRD...
  forwards ~ : IHTRG H7.
  apply swfe_fresh_head...

  +
  inverts TRD.
  inverts WFE.
  constructor...
  eapply fsub_trans_typ_swft...
  eapply fsub_trans_D_preserve_notin...
Qed.


Hint Resolve fsub_trans_D_swfte fsub_trans_G_swfe fsub_trans_typ_swft.

Lemma typing_regular : forall E e T EE n,
  typing E e T EE n ->
  wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E e T EE n H; induction H...
  - Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  - Case "typing_abs".
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    SCase "Second of original three conjuncts".
      pick fresh x and apply expr_abs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
        destruct (H0 x)...
    SCase "Third of original three conjuncts".
      apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  - Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ K]].
    inversion K...
  - Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh X and apply expr_tabs.
        eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
        destruct (H1 X)...
    SCase "Third of original three conjuncts".
      pick fresh Z and apply wf_typ_all...
      destruct (H1 Z)...
Qed.

Hint Resolve typing_regular.
Hint Extern 1 (wf_env ?E) =>
   match goal with
   | H: typing _ _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ _ H))
   end.
 
Hint Extern 1 (wf_typ ?E ?T) =>
   match goal with
  | H: typing E _ T _ _ |- _ => apply (proj2 (proj2 (typing_regular _ _ _ _ _ H)))
   end.

Hint Extern 1 (type ?T) =>
   let go E := apply (type_from_wf_typ E); auto in
   match goal with
   | H: typing ?E _ T _ _ |- _ => go E
   end.
 
Hint Extern 1 (expr ?e) =>
match goal with
| H: typing _ ?e _ _ _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ _ H)))
end.

(* ********************************************************************** *)
(** * STRENGTHENING *)

Lemma wf_typ_from_binds_sub : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma fsub_trans_typ_strengthening : forall FF A B EE1 EE2,
    uniq (EE1 ++ FF ++ EE2) ->
    fsub_trans_typ (EE1 ++ FF ++ EE2) A B ->
    wf_env (EE1 ++ EE2) ->
    wf_typ (EE1 ++ EE2) A ->
    fsub_trans_typ (EE1 ++ EE2) A B.
Proof with eauto.
  introv UNIQ TR WFE WFT.
  inductions TR...
  inverts WFT.
  assert (I1:binds a (bind_sub U) (EE1 ++ FF ++ EE2)). auto.
  assert (I2: A = U).
    forwards ~ : binds_unique H I1...
    inverts H0...
  substs.
  forwards ~ : IHTR UNIQ WFE.
  eapply wf_typ_from_binds_sub...
  apply fsub_trans_typ_fvar_bind_sub_eq with (A:=U)...

  inverts WFT...

  inverts WFT.
  pick fresh X and apply fsub_trans_typ_all; auto.
  rewrite_env (([(X, bind_sub A)] ++ EE1) ++ EE2).
  eapply H1; simpl_env...

  inverts WFT...
Qed.

Lemma fsub_trans_typ_strengthening_head : forall FF A B EE,
    uniq (FF ++ EE) ->
    fsub_trans_typ (FF ++ EE) A B ->
    wf_env EE ->
    wf_typ EE A ->
    fsub_trans_typ EE A B.
Proof with eauto.
  intros.
  rewrite_env (nil ++ EE).
  apply fsub_trans_typ_strengthening with FF; simpl_env...
Qed.

(* ********************************************************************** *)
(** * Size *)

Fixpoint ftyp_size (t:ftyp) :=
  match t with
    | ftyp_top => 1
    | ftyp_nat => 1
    | ftyp_bvar _ => 1
    | ftyp_fvar _ => 1
    | ftyp_arrow a b => 1 + ftyp_size a + ftyp_size b
    | ftyp_all a b => 1 + ftyp_size a + ftyp_size b
    | ftyp_rcd_nil => 1
    | ftyp_rcd_cons i a b => 1 + ftyp_size a + ftyp_size b
  end.

Fixpoint env_size (e:env) :=
  match e with
  | nil => 0
  | ( (X, bind_sub T) :: E) => ftyp_size T + env_size E
  | ( (X, bind_typ T) :: E) => ftyp_size T + env_size E
  end.

Lemma binds_inv: forall X (U:binding) E,
  binds X U E ->
  exists EE1 EE2,
    E = EE1 ++ X ~ U ++ EE2.
Proof with eauto.
  induction E; introv BD.
  analyze_binds BD.
  destruct a.
  analyze_binds BD.
  exists empty E...
  destruct IHE as (EE1& EE2 & I)... substs.
  exists ((a,b)::EE1) EE2. simpl_env...
Qed.

Lemma ftyp_size_open_tt_rec : forall T n X,
 ftyp_size (open_tt_rec n (ftyp_fvar X) T) = ftyp_size T.
Proof with eauto.
  induction T; introv; simpls...
  case_if...
Qed.

Lemma ftyp_size_open_tt : forall T X,
 ftyp_size (open_tt T (ftyp_fvar X)) = ftyp_size T.
Proof with eauto.
  unfold open_tt.
  intros.
  apply ftyp_size_open_tt_rec...
Qed.

Lemma env_size_append : forall EE FF,
 env_size (EE ++ FF) = env_size EE + env_size FF.
Proof with eauto.
  induction EE; introv; simpls...
  rewrite IHEE...
  destruct a...
  destruct b; Omega.omega.
Qed.

(* ********************************************************************** *)
(** * Renaming *)

Lemma wf_typ_renaming : forall F Q E Z T Y,
  wf_typ (F ++ Z ~ bind_sub Q ++ E) T ->
  Y \notin dom F \u dom E ->
  wf_typ (map (subst_tb Z (ftyp_fvar Y)) F ++ Y ~ bind_sub Q ++ E)
         (subst_tt Z (ftyp_fvar Y) T).
Proof with eauto.
  introv WF NOTIN.
  inductions WF; simpls...
  +
  case_if...
  analyze_binds H...
  apply wf_typ_var with (subst_tt Z Y U)...
  +
  pick fresh X and apply wf_typ_all...
  specialize H0 with (X:=X) (E0:=E) (Q0:=Q) (Z0:=Z) (F0:=(X, bind_sub T1) :: F).
  forwards ~ I : H0...
  simpl_env...
  assert (X <> Z). apply notin_singleton_1'...
  rewrite subst_tt_open_tt in I...
  simpl in I.
  case_if...
Qed.

Lemma fsub_trans_typ_renaming : forall F Z Q E T A Y,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  Y \notin dom F \u dom E ->
  fsub_trans_typ (F ++ Z ~ bind_sub Q ++ E) T A ->
  fsub_trans_typ (map (subst_tb Z (ftyp_fvar Y)) F ++ Y ~ bind_sub Q ++ E)
                 (subst_tt Z (ftyp_fvar Y) T)
                 (subst_sty_in_sty (sty_var_f Y) Z A).
Proof with eauto.
  introv WFE NOTIN TR.
  inductions TR; simpls...
  +
  case_if...
  -
  case_if... substs.
  forwards ~ I1 : IHTR...
  assert (A = Q).
    assert (I2 : binds Z (bind_sub Q) (F ++ (Z, bind_sub Q) :: E)) by auto.
    forwards ~ I3 :binds_unique H I2.
    inverts I3...
  substs.
  rewrite <- subst_tt_fresh in I1.
  apply fsub_trans_typ_fvar_bind_sub_eq with Q...
  apply wf_env_append_invert in WFE. inverts WFE.

  apply notin_fv_wf_typ with E...
  -
  case_if.
  analyze_binds H...
    *
      assert (I: binds a (subst_tb Z Y (bind_sub A)) (map (subst_tb Z Y) F)).
        apply binds_map...
      simpl in I.
      apply fsub_trans_typ_fvar_bind_sub_eq with ((subst_tt Z Y A))...
    *
      assert (I1: fsub_trans_typ E A B).
        rewrite_env ((F ++ (Z ~ bind_sub Q)) ++ E) in TR.
        apply fsub_trans_typ_strengthening_head in TR...
        simpl_env...
        apply wf_env_append_invert in WFE. inverts WFE...
        apply wf_typ_from_binds_sub with a...
        apply wf_env_append_invert in WFE. inverts WFE...
      rewrite subst_sty_in_sty_fresh_eq.
      rewrite_env ((map (subst_tb Z Y) F ++ (Y~ bind_sub Q)) ++ E).
      apply fsub_trans_typ_weakening_head...
      simpl_env.
      apply uniq_map_app_l.
      apply uniq_insert_mid...
      apply uniq_remove_mid with (Z ~ bind_sub Q)...
      apply fsub_trans_typ_preserve_notin with E A...
      apply wf_env_append_invert in WFE. inverts WFE...

  +
    pick fresh X and apply fsub_trans_typ_all...
    eapply wf_typ_renaming...
    specialize H1 with (X:=X) (E0:=E) (Q0:=Q) (Z0:=Z) (F0:=(X, bind_sub A) :: F).
    forwards ~ I : H1...
    simpl_env...
    assert (X <> Z). apply notin_singleton_1'...
    rewrite subst_sty_in_sty_open_sty_wrt_sty in I...
    rewrite subst_tt_open_tt in I...
    simpl in I.
    case_if... case_if...
Qed.

Lemma fsub_trans_typ_renaming_head : forall Z Q E T A Y,
  wf_env (Z ~ bind_sub Q ++ E) ->
  Y \notin dom E ->
  fsub_trans_typ (Z ~ bind_sub Q ++ E) T A ->
  fsub_trans_typ (Y ~ bind_sub Q ++ E)
                 (subst_tt Z (ftyp_fvar Y) T)
                 (subst_sty_in_sty (sty_var_f Y) Z A).
Proof.
  intros.
  rewrite_env (map (subst_tb Z (ftyp_fvar Y)) nil ++ Y ~ bind_sub Q ++ E).
  apply fsub_trans_typ_renaming; auto.
Qed.


(* ********************************************************************** *)
(** * Existence *)

Lemma fsub_trans_typ_exists_general : forall m EE T,
    env_size EE + ftyp_size T < m ->
    wf_env EE ->
    wf_typ EE T ->
    exists A, fsub_trans_typ EE T A.
Proof with auto.
  intro m. induction m.
  introv len. inverts len.
  introv LEN WFE WFT.
  inductions WFT; eauto.
  -
    forwards ~ (EE1 & EE2 & I): binds_inv H.
    substs.
    assert (I1 : wf_env EE2). apply wf_env_append_invert in WFE. inverts WFE...
    assert (I2 : wf_typ EE2 U). apply wf_env_append_invert in WFE. inverts WFE...
    forwards ~ (A & I3) : IHm I1 I2.
      rewrite env_size_append in LEN... simpl in LEN...
      Omega.omega.
    exists (sty_and (sty_var_f X) A).
    apply fsub_trans_typ_fvar_bind_sub_eq with U...
    apply fsub_trans_typ_weakening_head...
    apply fsub_trans_typ_weakening_head...
    apply wf_env_append_invert in WFE...
  -
    simpl in LEN.
    destruct (IHWFT1) as (A1 & I1)... Omega.omega.
    destruct (IHWFT2) as (A2 & I2)... Omega.omega.
    exists (sty_arrow A1 A2)...
  -
    simpl in LEN.
    destruct IHWFT as (B & I2)... Omega.omega.
    pick_fresh X.
    assert (I1: wf_env ((X, bind_sub T1) :: E)).
    constructor...
    forwards ~ (A & I3) : H0 X... rewrite ftyp_size_open_tt. Omega.omega.
    exists (sty_all sty_top (close_sty_wrt_sty X A)).
    pick fresh Y and apply fsub_trans_typ_all...
    forwards ~ : fsub_trans_typ_renaming_head Y I1 I3.
    rewrite subst_sty_in_sty_intro with (X1:=X)...
    rewrite open_sty_wrt_sty_close_sty_wrt_sty...
    rewrite subst_tt_open_tt in H1...
    simpl in H1. case_if...
    rewrite <- subst_tt_fresh in H1...
    rewrite fv_sty_in_sty_close_sty_wrt_sty...

  -
    simpl in LEN.
    destruct (IHWFT1) as (A1 & I1)... Omega.omega.
    destruct (IHWFT2) as (A2 & I2)... Omega.omega.
    exists (sty_and (sty_rcd i A1) A2)...
Qed.

Lemma fsub_trans_typ_exists : forall EE T,
    wf_env EE ->
    wf_typ EE T ->
    exists A, fsub_trans_typ EE T A.
Proof with auto.
  intros.
  eapply fsub_trans_typ_exists_general...
Qed.


Lemma fsub_trans_D_exists : forall EE,
    wf_env EE ->
    exists D, fsub_trans_D EE D.
Proof with auto.
  introv WF. inductions WF; auto.
  exists (nil:sctx)...

  -
  forwards (Ttx & I) : IHWF.
  forwards ~ : fsub_trans_D_preserve_notin I H0...
  exists (X ~ sty_top ++ Ttx)...

  -
  forwards (Ttx & I) : IHWF.
  forwards ~ : fsub_trans_D_preserve_notin I H0...
  exists (Ttx)...
Qed.

Lemma fsub_trans_G_exists : forall EE,
    wf_env EE ->
    exists G, fsub_trans_G EE G.
Proof with auto.
  introv WF. inductions WF; auto.
  exists (nil:sctx)...

  -
  forwards (Ttx & I) : IHWF.
  forwards ~ : fsub_trans_G_preserve_notin I H0...
  exists (Ttx)...

  -
  forwards (Ttx & I) : IHWF.
  forwards (A & I2) : fsub_trans_typ_exists WF H.
  forwards ~ : fsub_trans_G_preserve_notin I H0...
  exists (x ~ A ++ Ttx)...
Qed.

(* ********************************************************************** *)
(** * Theorems *)

Lemma fsub_trans_D_ctx_uniq : forall E F,
    fsub_trans_D E F ->
    uniq F.
Proof with eauto.
  induction 1...
Qed.
Hint Resolve fsub_trans_D_ctx_uniq.

Lemma trans_fsub: forall E S T D A B,
    fsub E S T ->
    fsub_trans_D E D ->
    fsub_trans_typ E S B ->
    fsub_trans_typ E T A ->
    exists co, sub D B A co.
Proof with eauto.
  introv SUB. generalize dependent D.
  generalize dependent B.
  generalize dependent A.
  induction SUB; introv TRD TRS TRT.
  -
  inverts TRT...
  -
  inverts TRT.
  inverts TRS...
  -
  forwards ~ : fsub_trans_typ_uniq TRS TRT.
  substs...
  -
  inverts TRS.
  assert (U=A0).
    forwards ~ I : binds_unique H0 H2...
    inverts I...
  substs.
  forwards ~ : fsub_trans_typ_uniq TRT H4.
  substs.
  assert (swft D (sty_var_f X)).
    forwards : fsub_trans_D_sub H2 TRD...
  eexists. 
  apply S_andr...

  -
  forwards ~ (I1 & I2) : fsub_trans_typ_exists E B.
  forwards ~ (co1 & I3) : IHSUB1 TRS...
  forwards ~ (co2 & I4) : IHSUB2 TRT...

  -

  inverts TRS as I1 I2.
  inverts TRT as I3 I4.
  forwards ~ (co1 & II1) : IHSUB1 TRD I3 I1.
  forwards ~ (co2 & II2) : IHSUB2 TRD I2 I4.
  exists (co_arr co1 co2).
  constructor...

  -
  inverts TRS.
  inverts TRT.
  pick fresh X.
  specialize H0 with (X:=X) (D:=X ~ sty_top ++ D).
  forwards ~ (co & SU): H0...
  exists (co_forall co).
  pick fresh Y and apply S_forall; auto.
  apply sub_renaming with (X:=X); auto.
  constructor...

  -
  inverts TRS.
  inverts TRT.
  eexists...

  -
  inverts TRS.
  inverts TRT.
  eexists ...

  -
  inverts TRS as I1 I2 I3.
  inverts TRT as I4 I5 I6.
  forwards ~ (co1 & I7) : IHSUB1 I1 I4...
  forwards ~ (co2 & I8) : IHSUB2 I2 I5...
  eexists.
  apply sub_and...

  -
  inverts TRS as I1 I2 I3.
  inverts TRT as I4 I5 I6.
  inverts I2 as I7 I8 I9.
  inverts I5 as I10 I11 I12.
  forwards ~ : fsub_trans_typ_uniq I8 I11. substs.
  forwards ~ : fsub_trans_typ_uniq I4 I7. substs.
  forwards ~ : fsub_trans_typ_uniq I1 I10. substs.
  eexists.
  apply S_and; auto.
  apply S_trans with (sty_and (sty_rcd j A'1) B'); auto.
  apply S_andl...
  apply S_andr...
  apply S_and; auto.
  apply S_andl...
  apply S_trans with (sty_and (sty_rcd j A'1) B'); auto.
  apply S_andr...
  apply S_andr...
Qed.

Lemma trans_subst_fsub_general : forall τ2 E σ τ A1 A2 D a DD F,
    wf_env (F ++ [(a, bind_sub τ)] ++ E) ->
    fsub_trans_D ((map (subst_tb a σ) F) ++ E) DD ->
    fsub ((map (subst_tb a σ) F) ++ E) σ τ ->
    fsub_trans_typ ((map (subst_tb a σ) F) ++ E) σ D ->
    fsub_trans_typ (F ++ [(a, bind_sub τ)] ++ E) τ2 A1 ->
    fsub_trans_typ ((map (subst_tb a σ) F) ++ E) (subst_tt a σ τ2) A2 ->
    (exists co, sub DD (subst_sty_in_sty D a A1) A2 co)
    /\ (exists co, sub DD A2 (subst_sty_in_sty D a A1) co).
Proof with eauto.
  introv WFE TRDD SUB TRD TR1 TR2.
  generalize dependent σ.
  generalize dependent A2.
  generalize dependent DD.
  generalize dependent D.
  inductions TR1; introv TRDD SUB TRD TR2.

  - Case "top".
  simpls. inverts TR2.
  splits...

  - Case "nat".
  simpls. inverts TR2.
  splits...

  - Case "fvar".
  simpls. case_if.

  + SCase "a0 = a".
  substs. case_if. clear C.
  assert (A = τ).
    assert (I : binds a (bind_sub τ) (F ++ (a, bind_sub τ) :: E)). auto.
    forwards ~ I2 : binds_unique H I.
    inverts I2...
  substs.
  assert (D = A2).
    forwards ~ : fsub_trans_typ_uniq TRD TR2.
  substs.
  assert (wf_typ E τ).
    apply wf_env_append_invert in WFE.
    eapply wf_typ_from_wf_env_sub...
    simpls...
  rewrite subst_sty_in_sty_fresh_eq.
  assert (I1 : fsub_trans_typ (map (subst_tb a σ) F ++ E) τ B).
    apply fsub_trans_typ_weakening_head...
    apply fsub_trans_typ_strengthening_head with (F ++ a ~ bind_sub τ);
    simpl_env...
    apply wf_env_append_invert in WFE...
    inverts WFE...
  forwards ~ (co & I2): trans_fsub SUB...
  splits...
  assert(I3: fsub_trans_typ E τ B).
    apply fsub_trans_typ_strengthening_head with (F ++ a ~ bind_sub τ);
    simpl_env...
    apply wf_env_append_invert in WFE...
    inverts WFE...
  eapply fsub_trans_typ_preserve_notin...
  assert (uniq (((a, bind_sub τ) :: E))).
    apply wf_env_append_invert in WFE...
  eapply uniq_cons_2...

  + SCase "a0 <> a".
  case_if.
  inverts TR2.
  forwards ~ I : IHTR1 TRDD SUB TRD.
  ++
  analyze_binds H.
  *
  assert (binds a0 (subst_tb a σ (bind_sub A)) (map (subst_tb a σ) F)).
    apply binds_map...
  assert (I1: binds a0 (subst_tb a σ (bind_sub A)) (map (subst_tb a σ) F ++ E)).
    auto.
  simpl in I1.
  assert (A0 = subst_tt a σ A).
    forwards ~ : binds_unique H1 I1.
    inverts H0...
  substs.
  exact H3.
  *
  assert (A = A0).
    assert (I1: binds a0 (bind_sub A) (map (subst_tb a σ) F ++ E)) by auto.
    forwards ~ : binds_unique H1 I1.
    inverts H...
  substs.
  rewrite <- subst_tt_fresh...
  apply notin_fv_wf_typ with E...
  apply wf_typ_from_binds_sub with a0...
  apply wf_env_append_invert in WFE... inverts WFE...
  apply wf_env_append_invert in WFE...
  eapply uniq_cons_2...
  ++ destruct I as [(co1 & I1) (co2 & I2)].
  clear IHTR1. split.
  * exists (co_pair (co_trans co_id co_proj1)
               (co_trans co1 co_proj2)).
  apply sub_and...
  apply S_refl.
  apply swft_var with sty_top...
  apply fsub_trans_D_sub
    with (T:=A0)
         (E:=(map (subst_tb a σ) F ++ E))...
  *
  exists (co_pair (co_trans co_id co_proj1)
               (co_trans co2 co_proj2)).
  apply sub_and...
  apply S_refl.
  apply swft_var with sty_top...
  apply fsub_trans_D_sub
    with (T:=A0)
         (E:=(map (subst_tb a σ) F ++ E))...

  -
  simpls. inverts TR2.
  forwards ~ [(co1 & I1) (co2 & I2)] : IHTR1_1 WFE TRDD SUB TRD H2.
  forwards ~ [(co3 & I3) (co4 & I4)] : IHTR1_2 WFE TRDD SUB TRD H4.
  split...

  -
  simpls.
  inverts TR2.
  split.

  *
  pick fresh X.
  specialize H1 with (X:=X) (F0:=(X, bind_sub A) :: F)
                     (a0:=a) (τ0 :=τ) (E0:=E)
                     (D:=D)
                     (DD:=X ~ sty_top ++ DD)
                     (A2:=(open_sty_wrt_sty C0 (sty_var_f X)))
                     (σ:=σ).
  forwards ~ I : H1...
  + constructor...
  + constructor...
  +
  rewrite_env (nil ++ X ~ bind_sub (subst_tt a σ A)  ++ (map (subst_tb a σ) F ++ E)).
  apply fsub_weakening;
  simpl_env...
  + rewrite_env (X ~ bind_sub (subst_tt a σ A) ++ map (subst_tb a σ) F ++ E).
      apply fsub_trans_typ_weakening_head...
  + rewrite subst_tt_open_tt... simpls.
    assert (X <> a).
    apply notin_singleton_1'...
    case_if...
  + rewrite subst_sty_in_sty_open_sty_wrt_sty in I; auto.
    simpls.
    assert (X <> a). apply notin_singleton_1'...
    case_if...
    destruct I as [(co1 & I1) (co2 & I2)]...
    exists (co_forall co1).
    pick fresh Y and apply S_forall; auto.
    apply sub_renaming with (X:=X); auto.
    constructor...
    apply fv_sty_in_sty_subst_sty_in_sty_notin...
    apply fv_sty_in_sty_subst_sty_in_sty_notin...

  *
  pick fresh X.
  specialize H1 with (X:=X) (F0:=(X, bind_sub A) :: F)
                     (a0:=a) (τ0 :=τ) (E0:=E)
                     (D:=D)
                     (DD:=X ~ sty_top ++ DD)
                     (A2:=(open_sty_wrt_sty C0 (sty_var_f X)))
                     (σ:=σ).
  forwards ~ I : H1...
  + constructor...
  + constructor...
  +
  rewrite_env (nil ++ X ~ bind_sub (subst_tt a σ A)  ++ (map (subst_tb a σ) F ++ E)).
  apply fsub_weakening;
  simpl_env...
  + rewrite_env (X ~ bind_sub (subst_tt a σ A) ++ map (subst_tb a σ) F ++ E).
      apply fsub_trans_typ_weakening_head...
  + rewrite subst_tt_open_tt... simpls.
    assert (X <> a).
    apply notin_singleton_1'...
    case_if...
  + rewrite subst_sty_in_sty_open_sty_wrt_sty in I; auto.
    simpls.
    assert (X <> a). apply notin_singleton_1'...
    case_if...
    destruct I as [(co1 & I1) (co2 & I2)]...
    exists (co_forall co2).
    pick fresh Y and apply S_forall; auto.
    apply sub_renaming with (X:=X); auto.
    constructor...
    apply fv_sty_in_sty_subst_sty_in_sty_notin...
    apply fv_sty_in_sty_subst_sty_in_sty_notin...

  - Case "sub width".
    inverts TR2...
    split; simpls; eexists...

  - Case "sub depth".
    simpls.
    inverts TR2 as I1 I2 I3...
  forwards ~ [(co1 & I4) (co2 & I5)] : IHTR1_1 WFE TRDD SUB I1...
  forwards ~ [(co3 & I6) (co4 & I7)] : IHTR1_2 WFE TRDD SUB TRD I2.
  splits; eexists; apply sub_and...
Qed.


Lemma trans_subst_fsub_head : forall τ2 E σ τ A1 A2 D a DD,
    wf_env ([(a, bind_sub τ)] ++ E) ->
    fsub_trans_D E DD ->
    fsub E σ τ ->
    fsub_trans_typ E σ D ->
    fsub_trans_typ ([(a, bind_sub τ)] ++ E) τ2 A1 ->
    fsub_trans_typ E (subst_tt a σ τ2) A2 ->
    (exists co, sub DD (subst_sty_in_sty D a A1) A2 co)
    /\ (exists co, sub DD A2 (subst_sty_in_sty D a A1) co).
Proof.
  intros.
  eapply trans_subst_fsub_general with (F:=nil); eauto.
Qed.

Lemma trans_subst_fsub : forall E τ2 σ τ A1 A2 C D a,
    a `notin` fv_sty_in_sty A1 \u fv_sty_in_sty C \u fv_sty_in_sty A2 \u fv_sty_in_sty A1 \u fv_tt τ2 \u dom E ->
    fsub_trans_D E D ->
    fsub E σ τ ->
    fsub_trans_typ E σ A1 ->
    fsub_trans_typ ([(a, bind_sub τ)] ++ E) (open_tt τ2 a) (open_sty_wrt_sty C (sty_var_f a)) ->
    fsub_trans_typ E (open_tt τ2 σ) A2 ->
    exists co, sub D (open_sty_wrt_sty C A1) A2 co.
Proof with eauto.
  introv NOTIN TRDD SUB TR1 TR2 TR3.
  rewrite subst_tt_intro with (X:=a) in TR3; auto.
  forwards ~ I : trans_subst_fsub_head TRDD SUB TR1 TR2 TR3.
  destruct I.
  rewrite subst_sty_in_sty_intro with (X1:=a); auto.
Qed.

Lemma trans_fmono : forall E T A,
    uniq E ->
    fmono E T ->
    fsub_trans_typ E T A ->
    mono A.
Proof with eauto.
  introv UNI MN TR. generalize dependent A.
  inductions MN; introv TR; inverts TR...
  assert (I : bind_sub U = bind_sub A0).
  apply binds_unique with X E...
  inverts I.
  constructor...
Qed.

Lemma trans_label_notin : forall i A FF D B C,
    label_notin i A ->
    fsub_trans_D FF D ->
    fsub_trans_typ FF A B ->
    swft D C ->
    disjoint D (sty_rcd i C) B.
Proof.
  introv NOTIN TRD TRT WFT.
  generalize dependent B.
  inductions NOTIN; introv TRT.
  inverts TRT. apply D_topR; auto.
  inverts TRT.
  forwards ~ : IHNOTIN TRD WFT H6.
  apply D_andR; auto.
  apply D_rcdNeq; auto.
  eapply fsub_trans_typ_swft; eauto.
Qed.

Lemma trans_typing : forall FF e T EE A D G n,
    typing FF e T EE n ->
    fsub_trans_D FF D ->
    fsub_trans_G FF G ->
    fsub_trans_typ FF T A ->
    exists ee, has_type D G EE Inf A ee.
Proof with eauto.
  introv TY.
  generalize dependent D.
  generalize dependent G.
  generalize dependent A.
  induction TY; introv TRD TRG TRA.

  - Case "sexp_top". inverts TRA.
    exists exp_unit.
    apply T_top...

  - Case "sexp_nat". inverts TRA.
    exists (exp_lit i).
    apply T_nat...

  - Case "sexp_var_f".
    exists (exp_var_f x).
    apply T_var...
    forwards ~ : fsub_trans_G_typ H0 TRA TRG.

  - Case "sexp_abs".
    forwards ~ : fsub_trans_typ_uniq H1 TRA...
      pick fresh X.
      forwards ~ : H X.
      forwards [I _] : typing_regular H2.
      inverts I...
    substs.
    inverts TRA.
    pick fresh X.
    specialize H0 with (x:=X)
                       (D:=D)
                       (G:= X ~ A' ++ G)
                       (A:=B').
    forwards ~ (ee & I1) : H0...
    constructor...
    constructor...
    rewrite_env (X ~ bind_typ V ++ E).
    apply fsub_trans_typ_weakening_head...
    forwards ~ : H X.
    exists (exp_abs (exp_capp co_id (close_exp_wrt_exp X ee))).
    apply T_anno.
    pick fresh Y and apply T_abs...
    unfold open_exp_wrt_exp. simpl.
    apply T_sub with B'...
    pose subst_exp_in_exp_spec as I.
    unfold open_exp_wrt_exp in  I.
    rewrite <- I. clear I.
    apply has_typ_rename_var...

  - Case "sexp_app".
    forwards ~ (B & I) : fsub_trans_typ_exists E T1.
    assert (I2 : swft D B).
      forwards ~ [_ [_ I2]]: typing_regular TY1.
      inverts I2...
    forwards ~ (ee1 & I3) : IHTY1...
    forwards ~ (ee2 & I4) : IHTY2...

  - Case "sexp_tabs".
    inverts TRA.
    pick fresh X.
    forwards ~ (ee & I) : H1 X (open_sty_wrt_sty C (sty_var_f X)) G (X ~ sty_top ++ D)...
    constructor...
    constructor...
    apply H7...
                             
    exists (exp_tabs (close_exp_wrt_ty X ee)).
    pick fresh Y and apply T_tabs...
      rewrite <- subst_ty_in_exp_spec.
      apply has_typ_rename_tvar...
      forwards ~ I1 : H0 X.
      forwards ~ [I' _] : typing_regular I1.
      inverts I'...

  - Case "sexp_tapp".
    forwards ~ (B & I) : fsub_trans_typ_exists E (ftyp_all T1 T2).
    forwards ~ : fsub_trans_typ_uniq TRA H2. substs.
    
    forwards ~ (ee & I1) : IHTY TRD TRG I.
    inverts I.

    pick_fresh X.
    forwards ~ (co & I2) : trans_subst_fsub TRD H0 H1 H2.
    exists (exp_capp co  (exp_tapp ee (sty2ty A1))).
    apply T_anno.
    apply T_sub with (open_sty_wrt_sty C A1)...
    apply T_tapp with (B:=sty_top)...
    apply trans_fmono with E T...

  - Case "sexp_sub".
    forwards ~ : fsub_trans_typ_uniq H0 TRA. substs.
    forwards ~ (B & I) : fsub_trans_typ_exists E S.
    forwards ~ (co & I2): trans_fsub H I TRA...
    forwards ~ (ee & I3): IHTY TRD TRG I.
    exists (exp_capp co ee).
    apply T_anno.
    apply T_sub with B...
  - Case "rcd nil".
    inverts TRA...
  - Case "rcd cons".
    inverts TRA...
    forwards ~ (co1 & I1): IHTY1 H6...
    forwards ~ (co2 & I2): IHTY2 H8...
    eexists.
    constructor...
    eapply trans_label_notin; eauto.
  - Case "rcd perm".
    forwards ~ : fsub_trans_typ_uniq H TRA.
    substs.
    lets ~ [_ [_ I2]]  : typing_regular TY.
    inverts I2 as I21 I22 I23...
    forwards ~ (B & I1): fsub_trans_typ_exists E T2.
    forwards ~ (ee & I2) : IHTY (sty_and (sty_rcd i A0) B) TRD TRG.
    eexists.
    constructor...
    constructor...
    apply T_sub with (sty_and (sty_rcd i A0) B)...
Qed.
