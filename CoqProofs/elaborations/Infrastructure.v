Set Implicit Arguments.
Require Export Metalib.Metatheory.
Require Export LibTactics.
Require Export Fii_inf.

Fixpoint fv_stctx (GG : stctx) {struct GG} : vars :=
  match GG with
  | nil            => {}
  | cons (x, A) P' => fv_sty_in_sty A \u fv_stctx P'
  end.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C3 := gather_atoms_with (fun x : stctx => dom x) in
  let C4 := gather_atoms_with (fun x : sctx => dom x) in
  let D4 := gather_atoms_with (fun x => fv_sty_in_sty x) in
  let D5 := gather_atoms_with (fun x => fv_sty_in_sexp x) in
  let D6 := gather_atoms_with (fun x => fv_sexp_in_sexp x) in
  constr:(A \u B \u C3 \u C4 \u D4 \u D5 \u D6).

(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)

Lemma fv_sty_dom : forall D A,
    swft D A -> fv_sty_in_sty A [<=] dom D.
Proof.
  introv H.
  induction H; simpls; try fsetdec.

  apply binds_In in H.
  fsetdec.

  pick fresh X.
  assert (fv_sty_in_sty (open_sty_wrt_sty B (sty_var_f X)) [<=] add X (dom DD)) by eauto.
  assert (fv_sty_in_sty B [<=] fv_sty_in_sty (open_sty_wrt_sty B (sty_var_f X))) by eapply fv_sty_in_sty_open_sty_wrt_sty_lower.
  fsetdec.
Qed.

Lemma fv_sty_nil : forall A,
    swft nil A ->
    fv_sty_in_sty A [=] {}.
Proof.
  introv H.
  forwards~  : fv_sty_dom H.
  fsetdec.
Qed.


Lemma uniq_from_swfe : forall D E,
  swfe D E ->
  uniq E.
Proof with eauto.
  intros D E H; induction H...
Qed.


Lemma uniq_from_swfte : forall D,
  swfte D ->
  uniq D.
Proof with eauto.
  intros D H; induction H...
Qed.

Lemma uniq_from_swfte_push : forall X A D,
  swfte ([(X, A)] ++ D) ->
  uniq D.
Proof with eauto.
  introv WFTE; inversions WFTE. apply uniq_from_swfte...
Qed.

Lemma swft_type : forall E T,
  swft E T -> lc_sty T.
Proof.
  induction 1; eauto.
Qed.

Lemma swfe_notin : forall D G x A,
    swfe D G ->
    binds x A G ->
    x `notin` dom D.
Proof with eauto.
  induction 1; introv Bind; simpls...
  analyze_binds Bind...
Qed.


Lemma swft_weaken : forall T E F G,
  swft (G ++ E) T ->
  swft (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Heq; subst...
  Case "ty_all".
    pick fresh Y and apply swft_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma swfe_weaken : forall DD FF GG X A,
    swfe (DD ++ FF) GG ->
    X \notin dom GG ->
    swfe (DD ++ [(X, A)] ++ FF) GG.
Proof with eauto using swft_weaken.
  introv WFE NOTIN.
  inductions WFE...
Qed.

Lemma swfe_fresh_head : forall FF GG X A,
    swfe (FF) GG ->
    X \notin dom GG ->
    swfe ([(X, A)] ++ FF) GG.
Proof.
  intros.
  rewrite_env (nil ++[(X,A)]++FF).
  apply swfe_weaken; eauto.
Qed.



Lemma swft_weaken_head : forall T E F,
  swft E T ->
  swft (F ++ E) T.
Proof.
  intros.
  rewrite_env (nil ++ F++ E).
  auto using swft_weaken.
Qed.

Lemma  swft_weaken_tail : forall FF EE B, 
    swft FF B ->
    swft (FF ++ EE) B.
Proof with eauto.
  introv WF.
  rewrite_env (FF ++ EE ++ nil).
  apply swft_weaken;
  rewrite app_nil_2 in *...
Qed.

Lemma swft_from_swfte : forall Y A D,
    swfte D ->
    binds Y A D ->
    swft D A.
Proof with eauto using uniq_from_swfte.
  induction 1; intros J; analyze_binds J...
  eapply swft_weaken_head...
  apply IHswfte in BindsTac.
  eapply swft_weaken_head...
Qed.


Lemma swft_subst_tb : forall F E Z P T B,
  swft (F ++ Z ~ B ++ E) T ->
  swft E P ->
  uniq (map (subst_sty_in_sty P Z) F ++ E) ->
  swft (map (subst_sty_in_sty P Z) F ++ E) (subst_sty_in_sty P Z T).
Proof with simpl_env; eauto using swft_weaken_head, swft_type.
  intros F E Z P T B WT WP.
  remember (F ++ Z ~ B ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_sty_in_sty...
  - Case "swft_var".
    case_if...
    analyze_binds H...
  - Case "swft_all".
    pick fresh Y and apply swft_all...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
    rewrite_env (map (subst_sty_in_sty P Z) (Y ~ A ++ F) ++ E).
    apply H0...
Qed.

Lemma swft_subst_sty : forall E Z P T B,
  swft ([(Z, B)] ++ E) T ->
  swft E P ->
  uniq E ->
  swft E (subst_sty_in_sty P Z T).
Proof.
  introv HY WTF UNI.
  rewrite_env (nil ++ Z ~ B ++ E) in HY.
  forwards I : swft_subst_tb HY WTF UNI.
  simpl_alist in I; auto.
Qed.

Lemma swft_open : forall E U T1 T2,
  uniq E ->
  swft E (sty_all T1 T2) ->
  swft E U ->
  swft E (open_sty_wrt_sty T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_sty_in_sty_intro X)...
  rewrite_env (map (subst_sty_in_sty U X) nil ++ E).
  eapply swft_subst_tb...
Qed.



(* *********************************************************************************** *)
(** * Relations between well-formed environment and well-formed  types in environments *)

Lemma swft_tvar : forall D X A,
    swft D A ->
    X `notin` dom D ->
    X `notin` fv_sty_in_sty A.
Proof with eauto.
  introv H.
  gen X.
  induction H; introv W; simpls...
  lets : binds_In H.
  fsetdec.

  pick_fresh Y.

  forwards~ : H1 Y X.
  lets : IHswft W.
  lets : fv_sty_in_sty_open_sty_wrt_sty_lower B (sty_var_f Y).
  fsetdec.

Qed.


Lemma swfte_tvar : forall X A D,
    swfte D ->
    binds X A D ->
    X `notin` fv_sty_in_sty A.
Proof with eauto.
  introv H.
  gen X A.
  induction H; introv B.
  analyze_binds B.

  analyze_binds B.
  eapply swft_tvar...

Qed.


Inductive same_stctx {a b} : list (atom * a) -> list (atom * b) -> Prop :=
| same_empty : same_stctx nil nil
| same_cons : forall X A B s1 s2,
    same_stctx s1 s2 ->  same_stctx ([(X , A)] ++ s1) ([(X , B)] ++ s2).

Hint Constructors same_stctx.

Lemma same_stctx_dom : forall a b (ctxa : list (atom * a))  (ctxb : list (atom * b)),
    same_stctx ctxa ctxb ->
    dom ctxa [=] dom ctxb.
Proof with eauto; try fsetdec.
  induction 1; simpls...
Qed.


Lemma same_eq : forall a (s1 : list (atom * a)),
    same_stctx s1 s1.
Proof with eauto.
  alist induction s1...
Qed.


Lemma same_map : forall a b (s1 : list (atom * a)) (f : a -> b),
    same_stctx s1 (map f s1).
Proof with eauto; simpl_env.
  alist induction s1...
  intros.
  simpls...

  intros.
  simpls...
  constructor...
Qed.


Lemma same_sym : forall a b (s1 : list (atom * a)) (s2 : list (atom * b)),
    same_stctx s1 s2 -> same_stctx s2 s1.
Proof with eauto.
  introv H.
  induction H...
Qed.


Lemma same_var : forall a b (s1 : list (atom * a)) (s2 : list (atom * b)) X A,
    same_stctx s1 s2 ->
    binds X A s1 ->
    exists B, binds X B s2.
Proof with eauto.
  introv Eq.
  gen X A.
  induction Eq; introv H.

  analyze_binds H.

  analyze_binds H...
  lets (B0 & ?) : IHEq BindsTac.

  exists B0...
Qed.


Lemma swft_change : forall Δ Δ' A,
    swft Δ A ->
    same_stctx Δ Δ' ->
    swft Δ' A.
Proof with eauto.
  introv H.
  gen Δ'.
  induction H; introv Eq...

  lets (B & ?): same_var Eq H...
Qed.
  
Lemma swft_from_swfe : forall x U E D,
  swfe D E ->
  binds x U E ->
  swft D U.
Proof.
  induction 1; intros J; analyze_binds J.
Qed.


(* ******************************************************************************* *)
(** *Regularity of relations *)


Lemma sub_regular : forall Δ A B,
    sub Δ A B ->
    swft Δ A /\ swft Δ B.
Proof with eauto using same_eq, same_sym.
  introv Sub.
  induction* Sub.

  (* Case 1 *)
  destruct IHSub.
  splits.

  pick fresh Y and apply swft_all...
  forwards (? & ?) : H0...
  apply swft_change with (Δ := ([(Y , A2)] ++ DD))...

  pick fresh Y and apply swft_all...
  forwards (? & ?) : H0...

  (* Case 2 *)
  splits...

  pick fresh Y and apply swft_all...
  unfold open_sty_wrt_sty.
  simpls...


  Unshelve.
  exact (dom DD).
Qed.




Lemma disjoint_regular : forall Δ A B,
    disjoint Δ A B ->
    swft Δ A /\ swft Δ B.
Proof with eauto using same_eq.
  introv Dis.
  induction* Dis.

  splits...
  eapply sub_regular...

  splits...
  eapply sub_regular...

  splits...

  pick fresh X and apply swft_all...
  apply swft_change with (Δ := ([(X , sty_and A1 A2)] ++ DD))...
  eapply H0...

  pick fresh X and apply swft_all...
  apply swft_change with (Δ := ([(X , sty_and A1 A2)] ++ DD))...
  eapply H0...
Qed.

Hint Extern 1 (swft ?E ?A) =>
  match goal with
  | H: sub E A _ |- _ => apply (proj1 (sub_regular H))
  | H: sub E _ A |- _ => apply (proj2 (sub_regular H))
  | H: disjoint E A _ |- _ => apply (proj1 (disjoint_regular H))
  | H: disjoint E _ A |- _ => apply (proj2 (disjoint_regular H))
  end.

Lemma styping_regular : forall D G E dir A,
  has_type D G E dir A ->
  lc_sexp E /\ swfe D G /\ swft D A /\ swfte D.
Proof with simpl_env; try solve [auto | intuition auto].
  introv H.
  induction H...

  - Case "var".
    splits...
    eauto using swft_from_swfe.

  - Case "app".
    splits...
    destruct IHhas_type1 as (_ & _ & K & _).
    inverts K...

  - Case "anno".
    splits...
    destructs IHhas_type...
    lets :  swft_type H2.
    constructor~.

  - Case "tabs".
    pick_fresh Y.
    destructs (H1 Y)...
    inverts H6.
    splits...
    + SCase "lc_sexp".
      apply (lc_sexp_tabs_exists Y).
      destructs (H1 Y)...
      eauto using  swft_type.
      eauto using  swft_type.
    + SCase "wft".
      pick fresh Z and apply swft_all...
      destructs (H1 Z)...

  - Case "tapp".
    splits...
    + SCase "lc_exp".
      forwards (? & ?) : disjoint_regular H0.
      apply lc_sexp_tapp...
      eauto using swft_type.
    + SCase "wft".
      forwards (? & ?) : disjoint_regular H0.
      destructs IHhas_type.
      eapply swft_open; eauto.
      apply uniq_from_swfte...


  - Case "proj".
    destructs IHhas_type.
    inverts H2.
    splits...

  - Case "abs".
    pick_fresh y.
    destructs (H1 y)...
    inverts H3.
    splits...
    + SCase "lc_exp".
      apply (lc_sexp_abs_exists y).
      destructs (H1 y)...
Qed.

(* Automations to the resue *)


Hint Extern 1 (uniq ?E) =>
  match goal with
  | H: swfe _ E |- _ => apply (uniq_from_swfe H)
  | H: swfte E |- _ => apply (uniq_from_swfte H)
  end.


(* ********************************************************************** *)
(** * Properties of subtyping *)

Lemma sub_subst : forall Z E F C A B P,
  sub (F ++ Z ~ C ++ E) A B ->
  swft E P ->
  uniq (map (subst_sty_in_sty P Z) F ++ E) ->
  sub (map (subst_sty_in_sty P Z) F ++ E) (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B).
Proof with eauto using swft_subst_tb, swft_type.
  introv WT WP.
  remember (F ++ Z ~ C ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_sty_in_sty...

  (* Case 1 *)
  pick fresh Y and apply S_forall...
  repeat rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
  rewrite_env (map (subst_sty_in_sty P Z) (Y ~ A2 ++ F) ++ E).
  apply H0...
  simpls...

  (* Case 2 *)
  pick fresh Y and apply S_distPoly...
  repeat rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
  rewrite_env (map (subst_sty_in_sty P Z) (Y ~ A ++ F) ++ E).
  eapply swft_subst_tb; simpls...

  repeat rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
  rewrite_env (map (subst_sty_in_sty P Z) (Y ~ A ++ F) ++ E).
  eapply swft_subst_tb; simpls...

Qed.

Lemma sub_subst_push : forall Z E C A B P,
  sub (Z ~ C ++ E) A B ->
  swft E P ->
  uniq E ->
  sub E (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B).
Proof with auto.
  introv SUB WFT UNI.
  rewrite_env (nil ++ Z ~ C ++ E) in SUB.
  forwards : sub_subst SUB WFT...
Qed.

Lemma sub_change : forall Δ Δ' A B,
    sub Δ A B ->
    same_stctx Δ Δ' ->
    sub Δ' A B.
Proof with eauto using swft_change.
  introv Sub.
  gen Δ'.
  induction Sub; introv Eq...

  eapply S_distPoly...

Qed.
  


Lemma sub_andr : forall Δ A B C,
    sub Δ A (sty_and B C) ->
    sub Δ A B /\ sub Δ A C.
Proof.
  introv SUB. inductions SUB.

  inversions H.
  splits~. 

  forwards ~ (c1' & c2' ) : IHSUB1.
  splits*.

  inverts H.
  splits*.

  splits*.

  inversions H.
  splits*. 

  inversions H0.
  splits*. 
Qed.

Lemma sub_and : forall DD A1 A2 B1 B2,
    sub DD A1 A2 ->
    sub DD B1 B2 ->
    sub DD (sty_and A1 B1) (sty_and A2 B2).
Proof with auto.
  introv S1 S2.
  apply S_and.
  apply S_trans with A1; auto.
  apply S_trans with B1; auto.
Qed.

Lemma sub_weakening : forall G F E A B,
  sub (G ++ E) A B ->
  sub (G ++ F ++ E) A B.
Proof with eauto using swft_weaken.
  introv Sub.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; introv EQ; subst...

  pick fresh X and apply S_forall...
  rewrite_env (([(X, A2)] ++ G) ++ F ++ E).
  eapply H0...

  pick fresh X and apply S_distPoly...
  rewrite_env (([(X, A)] ++ G) ++ F ++ E).
  eapply swft_weaken...
  eapply H0...
  rewrite_env (([(X, A)] ++ G) ++ F ++ E).
  eapply swft_weaken...
  eapply H1...
Qed.



Lemma topArr : forall Δ A,
    swft Δ A ->
    sub Δ A (sty_arrow sty_top sty_top).
Proof with eauto.
  introv Wft.
  eapply S_trans...
Qed.


Lemma rcdTop : forall Δ l A,
    swft Δ A ->
    sub Δ A (sty_rcd l sty_top).
Proof with eauto.
  introv Wft.
  eapply S_trans...
Qed.



Lemma same_mid : forall a (F E : list (atom * a)) X V U,
    same_stctx (F ++ [(X, V)] ++ E) (F ++ [(X, U)] ++ E).
Proof with eauto using same_eq.
  intros a F.
  alist induction F; intros; simpls...
  constructor...
  constructor...

Qed.


Lemma swft_narrow : forall V F U T E X,
  swft (F ++ X ~ V ++ E) T ->
  swft (F ++ X ~ U ++ E) T.
Proof with eauto using same_mid.
  intros.
  eapply swft_change...
Qed.


Lemma sub_narrow : forall Q F E Z P S T,
  sub (F ++ Z ~ Q ++ E) S T ->
  sub (F ++ Z ~ P ++ E) S T.
Proof with eauto using same_mid.
  intros.
  eapply sub_change...
Qed.

Lemma sub_strengthen : forall Z E C A B,
    sub (Z ~ C ++ E) A B ->
    Z \notin fv_sty_in_sty A \u fv_sty_in_sty B ->
    uniq E ->
    sub E A B.
Proof with auto.
  introv SUB WFT UNI.
  rewrite_env (nil ++ Z ~ C ++ E) in SUB.
  apply sub_subst with (P:=sty_top) in SUB...
  simpl_env in SUB.
  do 2 rewrite subst_sty_in_sty_fresh_eq in SUB...
Qed.

Lemma swfte_subst_tb : forall Q Z P E F,
  swfte (F ++ Z ~ Q ++ E) ->
  swft E P ->
  swfte (map (subst_sty_in_sty P Z) F ++ E).
Proof with eauto.
  introv Wfte.
  alist induction F; introv Wft; simpls...

  inverts Wfte...

  inverts Wfte as Wfte.

  constructor...
  simpl_env in *.
  eapply swft_subst_tb...
  lets Imp: uniq_from_swfte Wfte.
  solve_uniq.
Qed.


Lemma swfte_strength: forall E G,
    swfte (E ++ G) ->
    swfte G.
Proof with eauto.
  intros E.
  alist induction E; introv Wfte; simpls...
  inverts Wfte...
Qed.


(* ********************************************************************** *)
(** ** Renaming lemmas . *)

Lemma sub_renaming : forall X Y A D B B',
    uniq ([(X, A)] ++ D) ->
    sub ([(X, A)] ++ D) (open_sty_wrt_sty B (sty_var_f X)) (open_sty_wrt_sty B' (sty_var_f X)) ->
    X `notin` fv_sty_in_sty B ->
    X `notin` fv_sty_in_sty B' ->
    Y `notin` fv_sty_in_sty B ->
    Y `notin` fv_sty_in_sty B' ->
    Y `notin` dom D ->
    sub ([(Y, A)] ++ D) (open_sty_wrt_sty B (sty_var_f Y)) (open_sty_wrt_sty B' (sty_var_f Y)).
Proof with eauto.
  introv Uniq Sub ? ? ? ? ?.
  destruct (X == Y); substs...

  assert (Eq1 : (open_sty_wrt_sty B (sty_var_f Y)) = (subst_sty_in_sty (sty_var_f Y) X (open_sty_wrt_sty B (sty_var_f X)))).
    rewrite (subst_sty_in_sty_intro X)...

  assert (Eq2 : (open_sty_wrt_sty B' (sty_var_f Y)) = (subst_sty_in_sty (sty_var_f Y) X (open_sty_wrt_sty B' (sty_var_f X)))).
    rewrite (subst_sty_in_sty_intro X)...


  rewrite Eq1.
  rewrite Eq2.

  simpls.

  eapply sub_subst_push...
  simpl_env in *.
  eapply sub_weakening...
  solve_uniq.
Qed.


Lemma swft_renaming : forall X Y A D B,
    uniq ([(X, A)] ++ D) ->
    swft ([(X, A)] ++ D) (open_sty_wrt_sty B (sty_var_f X)) ->
    X `notin` fv_sty_in_sty B ->
    Y `notin` fv_sty_in_sty B ->
    Y `notin` dom D ->
    swft ([(Y, A)] ++ D) (open_sty_wrt_sty B (sty_var_f Y)).
Proof with eauto.
  introv Uniq Wft Frx Fry Fry'.
  destruct (X == Y); substs...
  rewrite (subst_sty_in_sty_intro X)...
  rewrite_env ((map (subst_sty_in_sty (sty_var_f Y) X) nil) ++ [(Y, A)] ++ D).
  apply swft_subst_tb with (B := A); simpls...
  simpl_env.
  eapply swft_weaken...
  solve_uniq.
Qed.

(* ********************************************************************** *)
(** * Enhance auto *)


Hint Resolve swft_type fv_sty_nil same_eq same_sym swft_change swft_from_swfte swft_from_swfe.
