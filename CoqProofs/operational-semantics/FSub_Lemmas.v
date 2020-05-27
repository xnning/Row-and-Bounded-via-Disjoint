(** Administrative lemmas for Fsub.

    Adapted from Metalib *)

Require Export FSub_Infrastructure.


(* ********************************************************************** *)
(** * Properties of [wf_typ] *)


Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  intros E T H; induction H; eauto.
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ X ~ bind_sub V ++ E) T ->
  wf_typ (F ++ X ~ bind_sub U ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ.
  remember (F ++ X ~ bind_sub V ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
 wf_typ (F ++ x ~ bind_typ U ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H1...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ Z ~ bind_sub Q ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      analyze_binds H...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (Y ~ bind_sub T1 ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  uniq E ->
  wf_typ E (ftyp_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  eapply wf_typ_subst_tb...
Qed.


(* ********************************************************************** *)
(** * Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Hint Resolve uniq_from_wf_env.

Lemma wf_env_append_invert : forall E F,
    wf_env (E ++ F) ->
    wf_env F.
Proof with eauto.
  induction E; intros F WFE; simpl_env...
  inversion WFE...
Qed.


Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_typ_from_binds_sub : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env (x ~ bind_sub T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** * Properties of [wf_env] *)


Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ X ~ bind_sub V ++ E) ->
  wf_typ E U ->
  wf_env (F ++ X ~ bind_sub U ++ E).
Proof with eauto using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ Z ~ bind_sub Q ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.


Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_wf_typ : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto.
    assert (X <> X0) by fsetdec. fsetdec.
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf_typ; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf_typ; eauto.
Qed.


(* ********************************************************************** *)
(** * Regularity of relations *)

Lemma fsub_regular : forall E S T,
  fsub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  intros E S T H.
  induction H...
  Case "sub_trans_tvar".
    intuition eauto.
    eapply wf_typ_from_binds_sub; eauto.
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
Qed.

(* *********************************************************************** *)
(** *  Automation *)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: fsub _ _ _ |- _ => apply (proj1 (fsub_regular _ _ _ H))
  end.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: fsub E T _ |- _ => apply (proj1 (proj2 (fsub_regular _ _ _ H)))
  | H: fsub E _ T |- _ => apply (proj2 (proj2 (fsub_regular _ _ _ H)))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: fsub ?E T _ |- _ => go E
  | H: fsub ?E _ T |- _ => go E
  end.



(* ********************************************************************** *)
(** * Properties of subtyping *)


Lemma fsub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  fsub E T T.
Proof with eauto.
  intros E T Ok Wf.
  induction Wf...
  pick fresh Y and apply fsub_all...
Qed.


Lemma fsub_weakening : forall E F G S T,
  fsub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  fsub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "sub_trans_tvar".
    apply (fsub_trans_tvar U)...
  Case "sub_trans".
    apply (fsub_trans _ _ B)...
  Case "sub_all".
    pick fresh Y and apply fsub_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


Lemma fsub_narrowing_aux : forall Q F E Z P S T,
  fsub (F ++ Z ~ bind_sub Q ++ E) S T ->
  fsub E P Q ->
  fsub (F ++ Z ~ bind_sub P ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing.
  intros Q F E Z P S T SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      analyze_binds_uniq H0. inversion BindsTacVal. subst.
      apply (fsub_trans _ _ P); [ eauto using fresh_mid_head | ].
      SSCase "Z <: P".
        apply (fsub_trans_tvar P)...
        rewrite_env (empty ++ (F ++ Z ~ bind_sub P) ++ E).
        apply fsub_weakening...
    SCase "X <> Z".
      apply (fsub_trans_tvar U)...
  - Case "sub_trans".
    apply (fsub_trans _ _ B)...
  - Case "sub_all".
    pick fresh Y and apply fsub_all...
    rewrite <- app_assoc.
    apply H0...
  - Case "sub_rcd_cons".
    constructor...
Qed.

Lemma fsub_narrowing : forall Q E F Z P S T,
  fsub E P Q ->
  fsub (F ++ Z ~ bind_sub Q ++ E) S T ->
  fsub (F ++ Z ~ bind_sub P ++ E) S T.
Proof.
  intros.
  eapply fsub_narrowing_aux; eauto.
Qed.


Lemma fsub_through_subst_tt : forall Q E F Z S T P,
  fsub (F ++ Z ~ bind_sub Q ++ E) S T ->
  fsub E P Q ->
  fsub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  remember (F ++ Z ~ bind_sub Q ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  Case "sub_top".
    apply fsub_top...
  Case "sub_refl_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      apply fsub_reflexivity...
    SCase "X <> Z".
      apply fsub_reflexivity...
      inversion H0; subst.
      analyze_binds H3...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "sub_trans_tvar".
    destruct (X == Z); subst.
    SCase "X = Z".
      analyze_binds_uniq H0. inversion BindsTacVal. subst.
      apply (fsub_trans _ _ Q).
      SSCase "left branch".
        rewrite_env (empty ++ map (subst_tb Z P) G ++ E).
        apply fsub_weakening...
      SSCase "right branch".
        rewrite (subst_tt_fresh Z P Q) at 1...
        apply fsub_reflexivity...
          apply wf_typ_subst_tb with (Q:=Q)...
          apply (notin_fv_wf_typ E); eauto using fresh_mid_tail.
    SCase "X <> Z".
      apply (fsub_trans_tvar (subst_tt Z P U))...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      analyze_binds H0...
  - Case "sub_trans".
    apply fsub_trans with (subst_tt Z P B)...
  - Case "sub_all".
    pick fresh X and apply fsub_all...
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (X ~ bind_sub A ++ G) ++ E).
    apply H0...
  - Case "sub_rcd_depth".
    constructor...
  - Case "rcd_width".
    constructor...
  - Case "rcd_perm".
    constructor...
Qed.


Lemma fsub_strengthening : forall x U E F S T,
  fsub (F ++ x ~ bind_typ U ++ E) S T ->
  fsub (F ++ E) S T.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  - Case "sub_trans_tvar".
    apply (fsub_trans_tvar U0)...
    analyze_binds H0...
  - Case "sub_trans".
    apply (fsub_trans _ _ B)...
  - Case "sub_all".
    pick fresh X and apply fsub_all...
    rewrite <- app_assoc.
    apply H0...
  - Case "sub_cons_perm".
    constructor...
Qed.
