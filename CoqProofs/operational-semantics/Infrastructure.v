
Require Export Metalib.Metatheory.
Require Export LibTactics.
Require Export SystemF_inf.
Require Export Fii_inf.
Require Export TypeSystems.

Coercion ty_var_b : nat >-> ty.
Coercion ty_var_f : typvar >-> ty.
Coercion exp_var_b : nat >-> exp.
Coercion exp_var_f : expvar >-> exp.

Definition fv_qs (B : qs) : vars :=
  match B with
  | qs_arr A => fv_sty_in_sty A
  | qs_rcd l => {}
  | qs_all X A => singleton X `union` fv_sty_in_sty A
  end.

Fixpoint fv_stctx (GG : stctx) {struct GG} : vars :=
  match GG with
  | nil            => {}
  | cons (x, A) P' => fv_sty_in_sty A \u fv_stctx P'
  end.


Definition seqs_vars (fs : seqs) : vars :=
  fold_right (fun qs acc => fv_qs qs \u acc) empty fs.

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
  constr:(A \u B \u C1 \u C2 \u C3 \u C4 \u D1 \u D2 \u D3 \u D4 \u D5 \u D6 \u D7).


(* ********************************************************************** *)
(** * Notations *)

Notation "'|' A '|'" := (sty2ty A) (at level 60).

Notation "'∥' Γ '∥'" := (map sty2ty Γ) (at level 60).


Lemma trans_open_sty_rec : forall A B n,
    | open_sty_wrt_sty_rec n B A | = open_ty_wrt_ty_rec n (| B |) (| A |).
Proof with eauto.
  intros A.
  induction A; intros B m; simpls...

  destruct (lt_eq_lt_dec n m)...
  destruct s...

  rewrite IHA2.
  rewrite IHA1...

  rewrite IHA2.
  rewrite IHA1...

  rewrite IHA2...
Qed.


Lemma trans_open_sty : forall A B,
    | open_sty_wrt_sty B A | = open_ty_wrt_ty (| B |) (| A |).
Proof.
  intros.
  unfold open_sty_wrt_sty.
  unfold open_ty_wrt_ty.
  rewrite trans_open_sty_rec.
  reflexivity.
Qed.

Lemma trans_subst_sty : forall B A X,
    | subst_sty_in_sty A X B | = subst_ty_in_ty (| A |) X (| B |).
Proof with eauto.
  intros B.
  induction B; intros; simpls...
  case_if...

  rewrite IHB1...
  rewrite IHB2...

  rewrite IHB1...
  rewrite IHB2...

  rewrite IHB2...
Qed.


Lemma lc_sty_ty : forall A,
    lc_sty A -> lc_ty (| A |).
Proof with eauto.
  intros A H.
  induction H; simpls...

  pick fresh X.
  apply (lc_ty_all_exists X).
  unfold open_ty_wrt_ty.
  simpls...

  pick_fresh X.
  apply (lc_ty_all_exists X).
  asserts_rewrite (ty_var_f X = | sty_var_f X |)...
  rewrite <- trans_open_sty...
Qed.


Lemma notin_sty_ty : forall X A,
    X `notin` fv_sty_in_sty A -> X `notin` fv_ty_in_ty (| A |).
Proof with eauto.
  intros.
  induction A; simpls...
Qed.


(* ********************************************************************** *)
(** * Properties of monotype  *)


Hint Constructors mono.

Lemma sty_mono_or_not : forall A,
    lc_sty A ->
    mono A \/ ~mono A.
Proof with eauto.
  introv LC.
  induction LC; try solve [left; constructor].

  destruct IHLC1.
  destruct IHLC2.
  left; constructor...
  right.
  introv Bad.
  inverts Bad.
  tryfalse.
  destruct IHLC2.
  right.
  introv Bad.
  inverts Bad.
  tryfalse.
  right.
  introv Bad.
  inverts Bad.
  tryfalse.

  destruct IHLC1.
  destruct IHLC2.
  left; constructor...
  right.
  introv Bad.
  inverts Bad.
  tryfalse.
  destruct IHLC2.
  right.
  introv Bad.
  inverts Bad.
  tryfalse.
  right.
  introv Bad.
  inverts Bad.
  tryfalse.

  right.
  introv Bad.
  inverts Bad.

  destruct IHLC.
  left; constructor...
  right.
  introv Bad.
  inverts Bad.
  tryfalse.
Qed.


Inductive poly : sty -> Prop :=
| poly_p : forall A B,
    lc_sty (sty_all A B) ->
    poly (sty_all A B)
| poly_and1 : forall A B,
    poly A ->
    mono B ->
    poly (sty_and A B)
| poly_and2 : forall A B,
    poly B ->
    mono A ->
    poly (sty_and A B)
| poly_and3 : forall A B,
    poly A ->
    poly B ->
    poly (sty_and A B)
| poly_arr1 : forall (A B:sty),
    poly A ->
    mono B ->
    poly (sty_arrow A B)
| poly_arr2 : forall (A B:sty),
    poly B ->
    mono A ->
    poly (sty_arrow A B)
| poly_arr3 : forall (A B:sty),
    poly A ->
    poly B ->
    poly (sty_arrow A B)
| poly_rcd : forall (l:i) (A:sty),
    poly A ->
    poly (sty_rcd l A).

Hint Constructors poly.


Lemma mono_lc : forall t,
    mono t -> lc_sty t.
Proof with eauto.
  induction 1...

Qed.

Lemma poly_lc : forall t,
    poly t -> lc_sty t.
Proof with eauto using mono_lc.
  induction 1...
Qed.



Lemma not_mono_arrow : forall A B,
    lc_sty A ->
    lc_sty B ->
    ~mono (sty_arrow A B) ->
    ~mono A \/ ~mono B.
Proof with eauto.
  introv HA HB H.
  apply sty_mono_or_not in HA.
  apply sty_mono_or_not in HB.
  destruct HA.
  destruct HB.
  false.
  apply H...
  right...
  destruct HB.
  left...
  left...
Qed.


Lemma not_mono_and : forall A B,
    lc_sty A ->
    lc_sty B ->
    ~mono (sty_and A B) ->
    ~mono A \/ ~mono B.
Proof with eauto.
  introv HA HB H.
  apply sty_mono_or_not in HA.
  apply sty_mono_or_not in HB.
  destruct HA.
  destruct HB.
  false.
  apply H...
  right...
  destruct HB.
  left...
  left...
Qed.

Lemma not_mono_is_poly : forall A,
    lc_sty A -> ~mono A -> poly A.
Proof with eauto.
  introv LC.
  induction LC; introv Mono; try solve [false; apply Mono; eauto]...

  - Case "arrow".
    apply not_mono_arrow in Mono...
    destruct Mono as [Mono1 | Mono2].
    forwards HB : sty_mono_or_not B...
    destruct HB as [HB1 | HB2].
    apply IHLC1 in Mono1...
    apply IHLC1 in Mono1...
    forwards HA : sty_mono_or_not A...
    destruct HA as [HA1 | HA2].
    apply IHLC2 in Mono2...
    apply IHLC1 in HA2...


  - Case "and".
    apply not_mono_and in Mono...
    destruct Mono as [Mono1 | Mono2].
    forwards HB : sty_mono_or_not B...
    destruct HB as [HB1 | HB2].
    apply IHLC1 in Mono1...
    apply IHLC1 in Mono1...
    forwards HA : sty_mono_or_not A...
    destruct HA as [HA1 | HA2].
    apply IHLC2 in Mono2...
    apply IHLC1 in HA2...


  - Case "record".
    constructor...

Qed.



Lemma subst_mono: forall x t t',
    mono t' ->
    mono t ->
    mono (subst_sty_in_sty t x t').
Proof with eauto.
  introv Mono.
  gen t x.
  induction Mono; introv M; simpls; try constructor...
  case_if...
Qed.




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


Lemma swft_wft : forall Δ A,
    swft Δ A -> wft (map (const tt) Δ) (| A |).
Proof with eauto.
  introv H.
  induction H; simpls...


  pick fresh X and apply wft_all...
  unfold open_ty_wrt_ty.
  simpls...

  constructor...
  apply binds_map_2 with (f := const tt) (a := A)...

  pick fresh X and apply wft_all...
  asserts_rewrite (ty_var_f X = | sty_var_f X |)...
  rewrite <- trans_open_sty...
  apply (H1 X)...
Qed.


Lemma swft_wft_nil : forall A,
    swft nil A -> wft nil (| A |).
Proof with eauto.
  introv H.
  apply swft_wft in H.
  simpls...
Qed.

Lemma swfe_wfe : forall Δ Γ,
    uniq Δ ->
    swfe Δ Γ ->
    wfe (map (const tt) Δ) (∥ Γ ∥).
Proof with eauto using swft_wft.
  introv W H.
  induction H; simpls...

  constructor...
Qed.


Lemma wft_type : forall E T,
  wft E T -> lc_ty T.
Proof.
  induction 1; eauto.
Qed.


Lemma wft_weaken : forall T E F G,
  wft (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wft (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "ty_all".
    pick fresh Y and apply wft_all...
    rewrite <- app_assoc.
    apply H0...
Qed.



Lemma wft_weaken_head : forall T E F,
  wft E T ->
  uniq (F ++ E) ->
  wft (F ++ E) T.
Proof.
  intros.
  rewrite_env (nil ++ F++ E).
  auto using wft_weaken.
Qed.

Lemma wft_subst_tb : forall F E Z P T,
  wft (F ++ Z ~ tt ++ E) T ->
  wft E P ->
  uniq (F ++ E) ->
  wft (F ++ E) (subst_ty_in_ty P Z T).
Proof with simpl_env; eauto using wft_weaken_head, wft_type.
  intros F E Z P T WT WP.
  remember (F ++ Z ~ tt ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_ty_in_ty...
  - Case "ty_var".
    case_if...
  - Case "ty_all".
    pick fresh Y and apply wft_all...
    rewrite subst_ty_in_ty_open_ty_wrt_ty_var...
    rewrite_env (([(Y, tt)] ++ F) ++ E).
    apply H0...
Qed.


Lemma wft_open : forall E U T2,
  uniq E ->
  wft E (ty_all T2) ->
  wft E U ->
  wft E (open_ty_wrt_ty T2 U).
Proof with simpl_env; eauto.
  intros E U T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_ty_in_ty_intro X)...
  rewrite_env (nil ++ E).
  eapply wft_subst_tb...
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
  

(* ******************************************************************************* *)
(** *Properties of [wfe]  *)

Lemma uniq_from_wfe : forall D E,
  wfe D E ->
  uniq E /\ uniq D.
Proof with eauto.
  intros D E H; induction H...
  invert IHwfe...
Qed.

Lemma wft_from_wfe : forall x U E D,
  wfe D E ->
  binds x U E ->
  wft D U.
Proof.
  induction 1; intros J; analyze_binds J.
Qed.


Lemma swft_from_swfe : forall x U E D,
  swfe D E ->
  binds x U E ->
  swft D U.
Proof.
  induction 1; intros J; analyze_binds J.
Qed.


Lemma wfe_weaken : forall T E G X,
  wfe (G ++ E) T ->
  uniq (G ++ [(X, tt)] ++ E) ->
  X `notin` dom T ->
  wfe (G ++ [(X, tt)] ++ E) T.
Proof with simpl_env; eauto.
  introv Hwf_typ Hk Notin.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  constructor...
  apply wft_weaken...
Qed.


Lemma wfe_subst_tb : forall Z P E F D,
  wfe (F ++ Z ~ tt ++ E) D ->
  wft E P ->
  uniq (F ++ E) ->
  wfe (F ++ E) (map (subst_ty_in_ty P Z) D).
Proof with eauto using wft_subst_tb.
  introv WFE WFT.
  remember (F ++ Z ~ tt ++ E) as G.
  generalize dependent F.
  induction WFE; introv EQ Uniq; subst; simpl...
  constructor...
Qed.


Lemma notin_fv_typ_in_typ_open : forall (Y X : typvar)  T,
  X `notin` fv_ty_in_ty (open_ty_wrt_ty T Y) ->
  X `notin` fv_ty_in_ty T.
Proof.
 intros Y X T. unfold open_ty_wrt_ty.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
Qed.


Lemma notin_fv_wf : forall E (X : typvar) T,
  wft E T ->
  X `notin` dom E ->
  X `notin` fv_ty_in_ty T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom dd))...
    eapply binds_In; eauto. fsetdec.
  Case "wft_all".
    pick fresh Y.
    apply (notin_fv_typ_in_typ_open Y)...
Qed.


Lemma map_subst_typ_in_binding_id : forall G Z P D,
  wfe D G ->
  Z `notin` dom D ->
  G = map (subst_ty_in_ty P Z) G.
Proof with eauto.
  introv H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwfe...
  rewrite subst_ty_in_ty_fresh_eq...
  eapply notin_fv_wf...
Qed.


Lemma wfe_strengthen : forall E F x U T,
 wfe T (F ++ x ~ U ++ E) ->
 wfe T (F ++ E).
Proof with eauto.
  induction F;
  introv Wfe; inversion Wfe; subst; simpl_env in *...
Qed.



(* ******************************************************************************* *)
(** *Regularity of relations *)


Lemma sub_regular : forall Δ A B c,
    sub Δ A B c ->
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
  | H: sub E A _ _ |- _ => apply (proj1 (sub_regular _ _ _ _ H))
  | H: sub E _ A _ |- _ => apply (proj2 (sub_regular _ _ _ _ H))
  | H: disjoint E A _ _ |- _ => apply (proj1 (disjoint_regular _ _ _ H))
  | H: disjoint E _ A _ |- _ => apply (proj2 (disjoint_regular _ _ _ H))
  end.

Lemma styping_regular : forall D G E dir e A,
  has_type D G E dir A e ->
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
      forwards (? & ?) : disjoint_regular H1.
      apply lc_sexp_tapp...
      eauto using swft_type.
    + SCase "wft".
      forwards (? & ?) : disjoint_regular H1.
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


Lemma typing_regular : forall D E e T,
  typ D E e T ->
  lc_exp e /\ wfe D E /\ wft D T.
Proof with simpl_env; try solve [auto | intuition auto].
  introv H; induction H...
  - Case "typ_var".
    splits...
    eauto using wft_from_wfe.
  - Case "typ_abs".
    pick_fresh y.
    destructs (H0 y)...
    inverts H3.
    splits...
    + SCase "lc_exp".
      apply (lc_exp_abs_exists y).
      destructs (H0 y)...
  - Case "typ_app".
    splits...
    destruct IHtyp1 as (_ & _ & K).
    inverts K...
  - Case "typ_tabs".
    pick_fresh Y.
    destructs (H0 Y)...
    splits...
    + SCase "lc_exp".
      apply (lc_exp_tabs_exists Y).
      destructs (H0 Y)...
    + SCase "wft".
      pick fresh Z and apply wft_all...
      destructs (H0 Z)...
  - Case "tapp".
    splits...
    + SCase "lc_exp".
      apply lc_exp_tapp...
      eauto using wft_type.
    + SCase "wft".
      destructs IHtyp.
      eapply wft_open; eauto.
      lets* : uniq_from_wfe H2.
Qed.


Lemma value_regular : forall v,
    value v ->
    lc_exp v.
Proof.
  intros v H.
  induction H; auto.
Qed.


Lemma step_regular : forall e e',
  step e e' ->
  lc_exp e /\ lc_exp e'.
Proof with eauto using value_regular, lc_body_exp_wrt_ty, lc_body_exp_wrt_exp, lc_body_exp_abs_1, lc_body_exp_tabs_1.
  intros e e' H.
  induction H; intuition eauto 6; try constructor...
Qed.

Lemma ctyp_wft : forall G c T1 T2,
    ctyp G c T1 T2 ->
    wft G T1 /\ wft G T2.
Proof with eauto.
  introv Ctyp.
  induction* Ctyp.


  splits...
  pick fresh X and apply wft_all.
  unfold open_ty_wrt_ty.
  simpls...

  (* Case 1 *)
  splits...

  pick fresh X and apply wft_all.
  forwards (? & ?): H0 X...

  pick fresh X and apply wft_all.
  forwards (? & ?): H0 X...

  (* Case 2 *)
  inverts H.
  inverts H0.

  splits; eauto.
  pick fresh X and apply wft_all; auto.
  unfold open_ty_wrt_ty.
  simpls; eauto.


  Unshelve.
  exact (dom dd).

Qed.


(* Automations to the resue *)


Hint Extern 1 (wfe ?D ?E) =>
  match goal with
  | H: typ D E _ _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ H)))
  end.


Hint Extern 1 (wft ?E ?T) =>
  match goal with
  | H: typ E _ _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ _ H)))
  | H: ctyp E _ T _ |- _ => apply (proj1 (ctyp_wft _ _ _ _ H))
  | H: ctyp E _ _ T |- _ => apply (proj2 (ctyp_wft _ _ _ _ H))
  end.


Hint Extern 1 (lc_exp ?e) =>
  match goal with
  | H: typ _ _ ?e _ |- _ => apply (proj1 (typing_regular _ _ _ _ H))
  | H: step ?e _ |- _ => apply (proj1 (step_regular _ _ H))
  | H: step _ ?e |- _ => apply (proj2 (step_regular _ _ H))
  | H : value ?v |- _ => apply value_regular
  end.


Hint Extern 1 (lc_ty ?T) =>
  match goal with
  | H: wft _ ?T |- _ => apply (wft_type _ _ H)
  | H : typ _ _ _ ?T |- _ => apply (wft_type _ _ (proj2 (proj2 (typing_regular _ _ _ _ H))))
  end.

Hint Extern 1 (uniq ?E) =>
  match goal with
  | H: swfe _ E |- _ => apply (uniq_from_swfe _ _ H)
  | H: swfte E |- _ => apply (uniq_from_swfte _ H)
  | H: wfe E _ |- _ => apply (proj2 (uniq_from_wfe _ _ H))
  | H: wfe _ E |- _ => apply (proj1 (uniq_from_wfe _ _ H))
  end.



(* ******************************************************************************* *)
(** *Properties of typing *)

Lemma typing_var_weakening : forall E F G e T D,
  typ D (G ++ E) e T ->
  wfe D (G ++ F ++ E) ->
  typ D (G ++ F ++ E) e T.
Proof with simpl_env; eauto using wft_weaken, wft_from_wfe.
  intros E F G e T D Typ.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...

  - Case "typ_abs".
    pick fresh x and apply typ_abs...
    rewrite <- app_assoc.
    apply (H0 x)...
  - Case "typing_tabs".
    pick fresh X and apply typ_tabs...
    apply (H0 X)...
    rewrite_env (nil ++ [(X, tt)] ++ dd).
    apply wfe_weaken...
Qed.


Lemma ctyp_weaken : forall E F G c T1 T2,
    ctyp (G ++ E) c T1 T2 ->
    uniq (G ++ F ++ E) ->
    ctyp (G ++ F ++ E) c T1 T2.
Proof with eauto using wft_weaken.
  introv Ctyp.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Ctyp; introv EQ Ok; subst...

  pick fresh X and apply ctyp_forall.
  rewrite_env (([(X, tt)] ++ G) ++ F ++ E).
  eapply H0...
  solve_uniq.
Qed.



Lemma typing_tvar_weakening : forall E G e T D X,
  typ (G ++ E) D e T ->
  uniq (G ++ [(X, tt)] ++ E) ->
  X \notin dom D ->
  typ (G ++ [(X, tt)] ++ E) D e T.
Proof with simpl_env; eauto using wfe_weaken, wft_weaken, ctyp_weaken.
  introv Typ Uniq Notin.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Typ; introv Ok Uniq; subst...

  - Case "typ_abs".
    pick fresh x and apply typ_abs...

  - Case "typ_tabs".
    pick fresh Y and apply typ_tabs...
    rewrite_env (([(Y, tt)] ++ G) ++ [(X, tt)] ++ E).
    apply (H0 Y)...
Qed.



Lemma ctyp_through_subst_typ_in_typ : forall E F Z S T P c,
    ctyp (F ++ Z ~ tt ++ E) c S T ->
    uniq (F ++ E) ->
    wft E P ->
    ctyp (F ++ E) c (subst_ty_in_ty P Z S) (subst_ty_in_ty P Z T).
Proof with simpl_env; eauto using wft_subst_tb.
  introv Ctyp Uniq Wf.
  remember (F ++ Z ~ tt ++ E) as G.
  generalize dependent F.
  induction Ctyp; introv EQ Uniq; subst; simpls...

  - Case "ctyp_forall".
    pick fresh X and apply ctyp_forall...
    rewrite subst_ty_in_ty_open_ty_wrt_ty_var...
    rewrite subst_ty_in_ty_open_ty_wrt_ty_var...
    rewrite_env (([(X, tt)] ++ F) ++ E).
    eapply H0...

  - Case "ctyp_distPoly".
    constructor...
    replace (ty_all (subst_ty_in_ty P Z T1)) with (subst_ty_in_ty P Z (ty_all T1))...
    replace (ty_all (subst_ty_in_ty P Z T2)) with (subst_ty_in_ty P Z (ty_all T2))...
Qed.


Lemma typing_through_subst_typ_in_exp : forall E F Z e T P D,
  typ (F ++ Z ~ tt ++ E) D e T ->
  uniq (F ++ E) ->
  wft E P ->
  typ (F ++ E) (map (subst_ty_in_ty P Z) D) (subst_ty_in_exp P Z e) (subst_ty_in_ty P Z T).
Proof with simpl_env; eauto 6 using wfe_subst_tb, wft_subst_tb.
  introv Typ Uniq Wf.
  remember (F ++ Z ~ tt ++ E) as G.
  generalize dependent F.
  induction Typ; intros F EQ Uniq; subst;
    simpl subst_ty_in_exp in *; simpl subst_ty_in_ty in *...

  - Case "typ_abs".
    pick fresh y and apply typ_abs...
    rewrite subst_ty_in_exp_open_exp_wrt_exp_var...
    rewrite_env (map (subst_ty_in_ty P Z) ([(y, T1)] ++ gg)).
    apply H0...

  - Case "typ_tabs".
    pick fresh Y and apply typ_tabs...
    rewrite subst_ty_in_exp_open_exp_wrt_ty_var...
    rewrite subst_ty_in_ty_open_ty_wrt_ty_var...
    rewrite_env (([(Y, tt)] ++ F) ++ E).
    apply H0...

  - Case "typ_tapp".
    rewrite subst_ty_in_ty_open_ty_wrt_ty...

  - Case "typ_capp".
    eapply typ_capp...
    apply ctyp_through_subst_typ_in_typ...
Qed.



Lemma typing_through_subst_exp_in_exp : forall U E F x T e u D,
  typ D (F ++ x ~ U ++ E) e T ->
  typ D E u U ->
  typ D (F ++ E) (subst_exp_in_exp u x e) T.
Proof with simpl_env; eauto 4 using wfe_strengthen.

  introv TypT TypU.
  remember (F ++ x ~ U ++ E) as E'.
  generalize dependent F.
  induction TypT; introv EQ; subst; simpl subst_exp_in_exp in *...

  - Case "typ_var".
    destruct (x0 == x); subst...
    analyze_binds_uniq H0.
    rewrite_env (nil ++ F ++ E).
    apply typing_var_weakening...

  - Case "typ_abs".
    pick fresh y and apply typ_abs...
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var...
    rewrite_env (([(y, T1)] ++ F) ++ E).
    apply H0...

  - Case "typ_tabs".
    pick fresh Y and apply typ_tabs...
    rewrite subst_exp_in_exp_open_exp_wrt_ty_var...
    apply H0...
    rewrite_env (nil ++ [(Y, tt)] ++ dd).
    apply typing_tvar_weakening...

Qed.


Lemma prod_canonical : forall t T1 T2,
    value t ->
    typ nil nil t (ty_prod T1 T2) ->
    exists t1 t2, value t1 /\ value t2 /\ t = exp_pair t1 t2.
Proof.
  introv VAL TY. inductions TY; try (solve [inversion VAL]).
  inversions VAL. exists e1 e2. splits~. 
  inversions VAL; inversions H.
Qed.

Lemma unit_canonical : forall t,
    value t ->
    typ nil nil t ty_unit ->
    t = exp_unit.
Proof with eauto.
  introv Val Typ. lets Typ' : Typ. inductions Typ; inverts Val; try solve [inverts H]...
Qed.


(* ********************************************************************** *)
(** * Properties of reductions *)

Lemma value_irred : forall v,
    value v -> irred step v.
Proof with eauto.
  introv V.
  induction V; unfolds; try solve [introv C; inverts C]...

  - Case "value_pair".
    introv H.
    inverts H as _ H.
    lets : IHV1 H...
    lets : IHV2 H...

  - Case "value_arr".
    introv H.
    inverts H as H.
    lets : IHV H...

  - Case "value_forall".
    introv H.
    inverts H as H.
    lets : IHV H...

  - Case "value_distArr".
    introv H.
    inverts H as H.
    lets : IHV H...

  - Case "value_topArr".
    introv H.
    inverts H as H.
    lets : IHV H...

  - Case "vaue_topAll".
    introv H.
    inverts H as H.
    lets : IHV H...

  - Case "value_distArr".
    introv H.
    inverts H as H.
    lets : IHV H...

Qed.


Ltac sweet :=
  match goal with
  | H : value ?t, H1 : step ?t ?e |- _ =>
    forwards* :  (value_irred _ H e)
  end.


Lemma step_unique: forall (t t1 t2 : exp),
  step t t1 -> step t t2 -> t1 = t2.
Proof with eauto; try sweet.
  introv Red1.
  gen t2.
  induction Red1; introv Red2.

  - Case "topArr".
    inverts Red2...
    inverts H3.
    inverts H4.
    inverts H3.
    inverts H1.

  - Case "topAll".
    inverts Red2...
    inverts H4.
    inverts H5.

  - Case "distArr".
    inverts Red2...
    inverts H6...
    inverts H7...

  - Case "distPoly".
    inverts Red2...
    inverts H6...
    inverts H7...

  - Case "id".
    inverts Red2...

  - Case "trans".
    inverts Red2...

  - Case "top".
    inverts Red2...

  - Case "arr".
    inverts Red2...
    inverts H5...

  - Case "pair".
    inverts Red2...

  - Case "projl".
    inverts Red2...
    inverts H4...

  - Case "projr".
    inverts Red2...
    inverts H4...

  - Case "forall".
    inverts Red2...
    inverts H5...

  - Case "beta".
    inverts Red2...
    inverts H5...

  - Case "tbeta".
    inverts Red2...
    inverts H5...

  - Case "app1".
    inverts Red2...
    inverts Red1...
    inverts H3...
    inverts Red1...
    inverts H6...
    inverts Red1...
    inverts Red1...
    erewrite IHRed1...

  - Case "app2".
    inverts Red2...
    inverts Red1...
    erewrite IHRed1...

  - Case "pairl".
    inverts Red2...
    erewrite IHRed1...

  - Case "pairr".
    inverts Red2...
    erewrite IHRed1...

  - Case "tapp".
    inverts Red2...
    inverts Red1...
    inverts H4...
    inverts Red1...
    inverts H6...
    inverts Red1...
    inverts Red1...
    erewrite IHRed1...

  - Case "pairr".
    inverts Red2...
    inverts Red1...
    inverts Red1...
    erewrite IHRed1...


Qed.


Lemma value_no_step : forall v1 v2,
    value v1 ->
    v1 ->* v2 ->
    v2 = v1.
Proof.
  introv ? Red.
  induction* Red.
  lets : value_irred H.
  pose (H1 b).
  tryfalse.
Qed.


Lemma multi_red_capp : forall c t t',
    t ->* t' -> (exp_capp c t) ->* (exp_capp c t').
Proof.
  intros.
  induction* H.
Qed.

Lemma multi_red_app1 : forall v1 t2 t2',
    value v1 ->
    t2 ->* t2' ->
    (exp_app v1 t2) ->* (exp_app v1 t2').
Proof.
  introv ? Red.
  induction* Red.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 ->
    t1 ->* t1' ->
    (exp_app t1 t2) ->* (exp_app t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.


Lemma multi_red_app : forall t1 t2 v1 v2,
    value v1 -> lc_exp t2 ->
    t1 ->* v1 -> t2 ->* v2 ->
    (exp_app t1 t2) ->* (exp_app v1 v2).
Proof.
  intros.
  apply star_trans with (b := exp_app v1 t2).
  sapply* multi_red_app2.
  sapply* multi_red_app1.
Qed.


Lemma multi_red_pair1 : forall t1 t2 t1',
    lc_exp t2 ->
    t1 ->* t1' ->
    (exp_pair t1 t2) ->* (exp_pair t1' t2).
Proof.
  introv ? Red.
  induction* Red.
Qed.

Lemma multi_red_pair2 : forall v1 t2 t2',
    value v1 ->
    t2 ->* t2' ->
    (exp_pair v1 t2) ->* (exp_pair v1 t2').
Proof.
  introv ? Red.
  induction* Red.
Qed.


Lemma multi_red_pair : forall t1 t2 v1 v2,
    value v1 -> lc_exp t2 ->
    t1 ->* v1 -> t2 ->* v2 ->
    (exp_pair t1 t2) ->* (exp_pair v1 v2).
Proof.
  intros.
  apply star_trans with (b := exp_pair v1 t2).
  sapply* multi_red_pair1.
  sapply* multi_red_pair2.
Qed.

Lemma multi_red_tapp : forall t t' T,
    lc_ty T -> t ->* t' -> (exp_tapp t T) ->* (exp_tapp t' T).
Proof with eauto.
  intros.
  induction* H0.
Qed.



(* ********************************************************************** *)
(** * Properties of subtyping *)

Lemma sub_subst : forall Z E F C A B P c,
  sub (F ++ Z ~ C ++ E) A B c ->
  swft E P ->
  uniq (map (subst_sty_in_sty P Z) F ++ E) ->
  sub (map (subst_sty_in_sty P Z) F ++ E) (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B) c.
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

Lemma sub_subst_push : forall Z E C A B P c,
  sub (Z ~ C ++ E) A B c ->
  swft E P ->
  uniq E ->
  sub E (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B) c.
Proof with auto.
  introv SUB WFT UNI.
  rewrite_env (nil ++ Z ~ C ++ E) in SUB.
  forwards : sub_subst SUB WFT...
Qed.

Lemma sub_change : forall Δ Δ' A B c,
    sub Δ A B c ->
    same_stctx Δ Δ' ->
    sub Δ' A B c.
Proof with eauto using swft_change.
  introv Sub.
  gen Δ'.
  induction Sub; introv Eq...

  eapply S_distPoly...

Qed.
  


Lemma sub_andr : forall Δ A B C c,
    sub Δ A (sty_and B C) c ->
    exists c1 c2, sub Δ A B c1 /\ sub Δ A C c2.
Proof.
  introv SUB. inductions SUB.

  inversions H.
  eexists. eexists. splits~. 

  forwards ~ (c1' & c2' & [co1 co2]) : IHSUB1.
  exists (co_trans c1' c2) (co_trans c2' c2).
  splits*.



  inverts H.
  eexists. eexists. splits*.

  eexists. eexists. splits*.

  inversions H.
  exists (co_trans co_proj1 co_proj1) (co_trans co_proj2 co_proj1).
  splits*. 

  inversions H0.
  exists (co_trans co_proj1 co_proj2) (co_trans co_proj2 co_proj2).
  splits*. 
Qed.

Lemma sub_and : forall DD A1 A2 B1 B2 co1 co2,
    sub DD A1 A2 co1 ->
    sub DD B1 B2 co2 ->
    sub DD (sty_and A1 B1) (sty_and A2 B2)
        (co_pair (co_trans co1 co_proj1)
                 (co_trans co2 co_proj2))
.
Proof with auto.
  introv S1 S2.
  apply S_and.
  apply S_trans with A1; auto.
  apply S_trans with B1; auto.
Qed.

Lemma sub_weakening : forall G F E A B c,
  sub (G ++ E) A B c ->
  sub (G ++ F ++ E) A B c.
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
    sub Δ A (sty_arrow sty_top sty_top) (co_trans co_topArr co_top).
Proof with eauto.
  introv Wft.
  eapply S_trans...
Qed.


Lemma rcdTop : forall Δ l A,
    swft Δ A ->
    sub Δ A (sty_rcd l sty_top) (co_trans co_id co_top).
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


Lemma sub_narrow : forall Q F E Z P S T c,
  sub (F ++ Z ~ Q ++ E) S T c ->
  sub (F ++ Z ~ P ++ E) S T c.
Proof with eauto using same_mid.
  intros.
  eapply sub_change...
Qed.

Lemma sub_renaming : forall X Y A D B B' c,
    uniq ([(X, A)] ++ D) ->
    sub ([(X, A)] ++ D) (open_sty_wrt_sty B (sty_var_f X)) (open_sty_wrt_sty B' (sty_var_f X)) c ->
    X `notin` fv_sty_in_sty B ->
    X `notin` fv_sty_in_sty B' ->
    Y `notin` fv_sty_in_sty B ->
    Y `notin` fv_sty_in_sty B' ->
    Y `notin` dom D ->
    sub ([(Y, A)] ++ D) (open_sty_wrt_sty B (sty_var_f Y)) (open_sty_wrt_sty B' (sty_var_f Y)) c.
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


Lemma swfte_tvar_push: forall X A D,
    swfte ([(X, A)] ++ D) ->
    swfte D /\ swft D A /\ X `notin` fv_sty_in_sty A.
Proof with eauto.
  introv WFTE.
  splits...
  inverts WFTE...
  inverts WFTE...
  eapply swfte_tvar...

Qed.


Lemma swfte_subst_tb : forall Q Z P E F,
  swfte (F ++ Z ~ Q ++ E) ->
  swft E P ->
  swfte (map (subst_sty_in_sty P Z) F ++ E).
Proof with eauto.
  introv Wfte.
  alist induction F; introv Wft; simpls...

  lets (? & ? & ?) : swfte_tvar_push Wfte...

  lets (? & ? & ?) : swfte_tvar_push Wfte...

  constructor...
  simpl_env in *.
  eapply swft_subst_tb...
  lets : uniq_from_swfte H...

  lets Imp: uniq_from_swfte Wfte.
  inverts Imp...
Qed.


Lemma swfte_strength: forall E G,
    swfte (E ++ G) ->
    swfte G.
Proof with eauto.
  intros E.
  alist induction E; introv Wfte; simpls...
  eapply IHE...
  rewrite_env ((map (subst_sty_in_sty sty_top x)) nil ++ (E ++ G)).
  eapply swfte_subst_tb...
  simpl_env in *...
Qed.





(* ********************************************************************** *)
(** * Misc *)


Lemma ftv_in_dom : forall Δ T,
    wft Δ T ->
    fv_ty_in_ty T [<=] dom Δ.
Proof.
  introv H.
  induction H; simpl; try fsetdec.

  apply binds_In in H.
  fsetdec.

  pick fresh X.
  assert (Fx : fv_ty_in_ty (open_ty_wrt_ty T2 (ty_var_f X)) [<=] dom ([(X,tt)] ++ dd)) by auto.
  simpl in Fx.
  assert (Fy : fv_ty_in_ty T2 [<=] fv_ty_in_ty (open_ty_wrt_ty T2 (ty_var_f X))).
  eapply fv_ty_in_ty_open_ty_wrt_ty_lower.
  fsetdec.
Qed.

Lemma fv_in_dom : forall Δ G e T,
    typ Δ G e T ->
    fv_exp_in_exp e [<=] dom G /\
    fv_ty_in_exp e [<=] dom Δ.
Proof.
  introv H.
  induction H; simpl; splits; try fsetdec.

  - Case "var".
    apply binds_In in H0.
    fsetdec.

  - Case "abs: var".
    pick fresh x.
    forwards~ (? & ?): H0 x.
    assert (Fx : fv_exp_in_exp (open_exp_wrt_exp e (exp_var_f x)) [<=] dom ([(x,T1)] ++ gg)) by auto.
    simpl in Fx.
    assert (Fy : fv_exp_in_exp e [<=] fv_exp_in_exp (open_exp_wrt_exp e (exp_var_f x))).
    eapply fv_exp_in_exp_open_exp_wrt_exp_lower.
    fsetdec.

  - Case "abs: tvar".
    pick fresh x.
    forwards~ (? & ?): H0 x.
    assert (Fy : fv_ty_in_exp e [<=] fv_ty_in_exp (open_exp_wrt_exp e (exp_var_f x))).
    eapply fv_ty_in_exp_open_exp_wrt_exp_lower.
    fsetdec.

  - Case "tabs: var".
    pick fresh X.
    forwards~ (? & ?): H0 X.
    assert (Fy : fv_exp_in_exp e [<=] fv_exp_in_exp (open_exp_wrt_ty e (ty_var_f X))).
    eapply fv_exp_in_exp_open_exp_wrt_ty_lower.
    fsetdec.

  - Case "tabs: tvar".
    pick fresh X.
    forwards~ (? & ?): H0 X.
    assert (Fy : fv_ty_in_exp e [<=] fv_ty_in_exp (open_exp_wrt_ty e (ty_var_f X))).
    eapply fv_ty_in_exp_open_exp_wrt_ty_lower.
    fsetdec.

  - Case "tapp".
    lets: ftv_in_dom H0.
    inverts IHtyp.
    fsetdec.
Qed.


Lemma closed_no_var : forall v T,
    typ nil nil v T ->
    fv_ty_in_exp v [=] {} /\ fv_exp_in_exp v [=] {}.
Proof.
  introv Typ.
  forwards (? & ?) : fv_in_dom Typ.
  splits; fsetdec.
Qed.

Definition exp_relation := exp -> exp -> Prop.

Definition getR (p : list (atom * (sty * sty * exp_relation))) : list (atom * exp_relation) :=
  map (fun t => match t with | (a, b, R) => R end) p.

Definition getOne (p : list (atom * (sty * sty * exp_relation))) : list (atom * sty) :=
  map (fun t => match t with | (a, b, R) => a end) p.

Definition getTwo (p : list (atom * (sty * sty * exp_relation))) : list (atom * sty) :=
  map (fun t => match t with | (a, b, R) => b end) p.

Definition mtsubst_in_sty (s : list (atom * sty)) (ty : sty) : sty :=
  fold_left (fun acc p => subst_sty_in_sty (snd p) (fst p) acc) s ty.

Definition mtsubst_in_exp (s : list (atom * sty)) (e : exp) : exp :=
  fold_left (fun acc p => subst_ty_in_exp (| snd p |) (fst p)  acc) s e.

Definition msubst_in_exp (s : list (atom * exp)) (t : exp) : exp :=
  fold_left (fun acc p => subst_exp_in_exp (snd p) (fst p) acc) s t.


Lemma mtsubst_arr : forall s A1 A2,
    mtsubst_in_sty s (sty_arrow A1 A2) = sty_arrow (mtsubst_in_sty s A1) (mtsubst_in_sty s A2).
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.


Lemma mtsubst_forall : forall s A1 A2,
    mtsubst_in_sty s (sty_all A1 A2) = sty_all (mtsubst_in_sty s A1) (mtsubst_in_sty s A2).
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.

Lemma mtsubst_and : forall s A1 A2,
    mtsubst_in_sty s (sty_and A1 A2) = sty_and (mtsubst_in_sty s A1) (mtsubst_in_sty s A2).
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.


Lemma mtsubst_nat : forall s,
    mtsubst_in_sty s sty_nat = sty_nat.
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.


Lemma mtsubst_top : forall s,
    mtsubst_in_sty s sty_top = sty_top.
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.

Lemma mtsubst_bot : forall s,
    mtsubst_in_sty s sty_bot = sty_bot.
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.


Lemma mtsubst_rcd : forall s l A,
    mtsubst_in_sty s (sty_rcd l A) = sty_rcd l (mtsubst_in_sty s A).
Proof with eauto.
  intros s.
  induction s; intros; simpls...
Qed.


Lemma mtsubst_unit : forall s,
    mtsubst_in_exp s exp_unit = exp_unit.
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.

Lemma mtsubst_lit : forall s i,
    mtsubst_in_exp s (exp_lit i) = exp_lit i.
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.


Lemma mtsubst_tabs : forall s e,
    mtsubst_in_exp s (exp_tabs e)  = exp_tabs (mtsubst_in_exp s e).
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.



Lemma mtsubst_capp : forall s c e,
    mtsubst_in_exp s (exp_capp c e) = exp_capp c (mtsubst_in_exp s e).
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.


Lemma msubst_unit : forall s,
    msubst_in_exp s exp_unit = exp_unit.
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.

Lemma msubst_lit : forall s i,
    msubst_in_exp s (exp_lit i) = exp_lit i.
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.


Lemma msubst_capp : forall s c e,
    msubst_in_exp s (exp_capp c e) = exp_capp c (msubst_in_exp s e).
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.


Lemma mtsubst_pair : forall s e1 e2,
    mtsubst_in_exp s (exp_pair e1 e2) = exp_pair (mtsubst_in_exp s e1) (mtsubst_in_exp s e2).
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.

Lemma msubst_pair : forall s e1 e2,
    msubst_in_exp s (exp_pair e1 e2) = exp_pair (msubst_in_exp s e1) (msubst_in_exp s e2).
Proof.
  intros s.
  induction s; intros; simpls; eauto.
Qed.


Lemma mtsubst_tapp : forall s e A,
    mtsubst_in_exp s (exp_tapp e (| A |)) = exp_tapp (mtsubst_in_exp s e) (|mtsubst_in_sty s A|).
Proof with eauto.
  intros s.
  alist induction s; intros; simpls...

  rewrite <- trans_subst_sty.
  rewrite IHs...

Qed.


Lemma msubst_tapp : forall s e T,
    msubst_in_exp s (exp_tapp e T) = exp_tapp (msubst_in_exp s e) T.
Proof with eauto.
  induction s; intros; simpls; eauto.
Qed.


Lemma mtsubst_app : forall s e e',
    mtsubst_in_exp s (exp_app e e') = exp_app (mtsubst_in_exp s e) (mtsubst_in_exp s e') .
Proof with eauto.
  intros s.
  alist induction s; intros; simpls...
Qed.


Lemma msubst_app : forall s e e',
    msubst_in_exp s (exp_app e e') = exp_app (msubst_in_exp s e) (msubst_in_exp s e').
Proof with eauto.
  induction s; intros; simpls; eauto.
Qed.


Lemma mtsubst_abs : forall s e,
    mtsubst_in_exp s (exp_abs e) = exp_abs (mtsubst_in_exp s e).
Proof with eauto.
  intros s.
  alist induction s; intros; simpls...
Qed.


Lemma msubst_abs : forall s e,
    msubst_in_exp s (exp_abs e) = exp_abs (msubst_in_exp s e).
Proof with eauto.
  induction s; intros; simpls; eauto.
Qed.


Lemma msubst_tabs : forall s e,
    msubst_in_exp s (exp_tabs e) = exp_tabs (msubst_in_exp s e).
Proof with eauto.
  induction s; intros; simpls; eauto.
Qed.



Inductive all_value : list (atom * exp) -> Prop :=
| all_empty : all_value nil
| all_cons : forall x v T g,
    value v ->
    typ nil nil v T ->
    all_value g ->
    all_value ([(x , v)] ++ g).

Hint Constructors all_value.


Lemma msubst_ty_open_wrt_ty : forall s e T,
    all_value s ->
    msubst_in_exp s (open_exp_wrt_ty e T) =
    open_exp_wrt_ty (msubst_in_exp s e) T.
Proof with eauto.
  intros s.
  alist induction s; intros; simpls...
  inverts H.
  rewrite <- IHs...
  rewrite subst_exp_in_exp_open_exp_wrt_ty...
Qed.


Lemma msubst_open : forall g t a,
    all_value g ->
    msubst_in_exp g (open_exp_wrt_exp t a) = open_exp_wrt_exp (msubst_in_exp g t) (msubst_in_exp g a).
Proof with eauto.
  intro g.
  alist induction g; intros; simpls...
  inverts H.
  rewrite subst_exp_in_exp_open_exp_wrt_exp...
Qed.


Lemma msubst_fresh : forall g e,
    fv_exp_in_exp e [=] {} ->
    msubst_in_exp g e = e.
Proof.
  intros.
  alist induction g.
  reflexivity.
  simpl.
  rewrite~ subst_exp_in_exp_fresh_eq.
  fsetdec.
Qed.


Lemma mtsubst_exp_fresh : forall s e,
    fv_ty_in_exp e [=] {} ->
    mtsubst_in_exp s e = e.
Proof.
  intros.
  alist induction s.
  reflexivity.
  simpl.
  rewrite~ subst_ty_in_exp_fresh_eq.
  fsetdec.
Qed.



(* ********************************************************************** *)
(** * Logical interpretation of type contexts *)

Inductive rel_d : stctx -> sctx -> Prop :=
| rel_d_empty : rel_d nil nil
| rel_d_cons : forall X Δ t B p,
    X `notin` dom Δ ->
    rel_d Δ p ->
    swft nil t ->
    mono t ->
    disjoint nil t (mtsubst_in_sty p B) ->
    rel_d ([(X, B)] ++ Δ) ([(X, t)] ++ p).

Hint Constructors rel_d.


Lemma rel_d_same : forall Δ p,
    rel_d Δ p -> same_stctx Δ p.
Proof with simpl_env; eauto.
  induction 1; simpls...
Qed.



Lemma rel_d_notin : forall Δ p X,
    rel_d Δ p ->
    X `notin` dom Δ ->
    X `notin` dom p.
Proof with eauto.
  introv RelD.
  induction RelD; simpls...
Qed.

Lemma rel_d_uniq : forall Δ p,
    rel_d Δ p ->
    uniq Δ /\ uniq p.
Proof with eauto using rel_d_notin.
  introv RelD.
  induction RelD; simpls...
  splits...
  solve_uniq.
  destruct IHRelD...
Qed.


Lemma mtsubst_open : forall Δ p A1 A2,
    rel_d Δ p ->
    mtsubst_in_sty p (open_sty_wrt_sty A1 A2) =
    open_sty_wrt_sty (mtsubst_in_sty p A1) (mtsubst_in_sty p A2).
Proof with eauto using swft_type.
  introv RelD.
  gen A1 A2.
  induction RelD; intros; simpls...
  rewrite subst_sty_in_sty_open_sty_wrt_sty...
Qed.


Lemma mtsubst_ty_open : forall Δ p e A,
    rel_d Δ p ->
    mtsubst_in_exp p (open_exp_wrt_ty e (|A|)) =
    open_exp_wrt_ty (mtsubst_in_exp p e) (|mtsubst_in_sty p A|).
Proof with eauto using swft_type, lc_sty_ty.
  introv RelD.
  gen A e.
  induction RelD; intros; simpls...
  rewrite <- IHRelD...
  rewrite subst_ty_in_exp_open_exp_wrt_ty...
  rewrite trans_subst_sty...
Qed.


Lemma mtsubst_exp_open : forall s e1 e2,
    mtsubst_in_exp s (open_exp_wrt_exp e1 e2) =
    open_exp_wrt_exp (mtsubst_in_exp s e1) (mtsubst_in_exp s e2).
Proof with eauto.
  intros s.
  alist induction s; intros; simpls...
  rewrite subst_ty_in_exp_open_exp_wrt_exp...
Qed.


Lemma mtsubst_fresh : forall s C,
    fv_sty_in_sty C [=] {} ->
    mtsubst_in_sty s C = C.
Proof.
  intros.
  alist induction s.
  reflexivity.
  simpl.
  rewrite~ subst_sty_in_sty_fresh_eq.
  fsetdec.
Qed.

Lemma mtsubst_in_exp_subst : forall s v x t,
    fv_ty_in_exp v [=] {} ->
    subst_exp_in_exp v x (mtsubst_in_exp s t) = mtsubst_in_exp s (subst_exp_in_exp v x t).
Proof with eauto.
  intros s.
  alist induction s; intros; simpls...

  rewrite IHs...
  rewrite subst_exp_in_exp_subst_ty_in_exp...
  fsetdec.
Qed.


Lemma mtsubst_var_notin : forall p x,
    x `notin` dom p ->
    mtsubst_in_exp p (exp_var_f x) = (exp_var_f x).
Proof with auto.
  intros p.
  alist induction p; intros; simpls...
Qed.


Lemma mtsubst_notin: forall X Δ p B,
    rel_d Δ p ->
    X `notin` dom p ->
    X `notin` (fv_sty_in_sty B) ->
    X `notin` fv_sty_in_sty (mtsubst_in_sty p B).
Proof with eauto.
  introv Wf.
  gen B.
  induction Wf; introv ? ?; simpls...
  eapply IHWf...
  eapply fv_sty_in_sty_subst_sty_in_sty_notin...
  eapply swft_tvar...
Qed.

Lemma mtsubst_swft : forall Δ A s,
    rel_d Δ s ->
    swft Δ A ->
    swft nil (mtsubst_in_sty s A).
Proof with eauto.
  introv H.
  gen A.
  induction H; introv WF; simpls...

  eapply IHrel_d...

  lets (? & ?) : rel_d_uniq...
  rewrite_env (map (subst_sty_in_sty t X) nil ++ Δ).
  eapply swft_subst_tb...
  exact WF.
  rewrite_env (Δ ++ nil).
  eapply swft_weaken_head...
Qed.

(* Lemma mtsubst_tvar: forall s Δ X (A : sty), *)
(*     rel_d Δ s -> *)
(*     binds X A Δ -> *)
(*     swft nil (mtsubst_in_sty s (sty_var_f X)). *)
(* Proof with eauto. *)
(*   introv H. *)
(*   gen X A. *)
(*   induction H; introv Bind; simpls... *)

(*   case_if... *)
(*   substs. *)
(*   inverts WF. *)
(*   inverts Uniq. *)
(*   eapply mtsubst_swft... *)
(*   rewrite_env (s1 ++ nil). *)
(*   eapply swft_weaken_head... *)
(*   inverts WF. *)
(*   inverts Uniq. *)
(*   analyze_binds Bind. *)
(*   eapply IHsame_stctx... *)
(* Qed. *)

Lemma mtsubst_nil : forall Γ,
    map (mtsubst_in_sty nil) Γ = Γ.
Proof with eauto.
  intros.
  alist induction Γ; simpls...
  rewrite IHΓ...
Qed.


Lemma mtsubst_cons : forall Γ X B s,
    map (mtsubst_in_sty ([(X, B)] ++ s)) Γ = map (mtsubst_in_sty s) (map (subst_sty_in_sty B X) Γ).
Proof with eauto.
  intros Γ.
  alist induction Γ; intros; simpls...
  rewrite IHΓ...
Qed.


Lemma mtsubst_trans : forall Γ B X,
    ∥ map (subst_sty_in_sty B X) Γ ∥ = map (subst_ty_in_ty (| B |) X) (∥ Γ ∥).
Proof with eauto.
  intros Γ.
  alist induction Γ; intros; simpls...
  rewrite IHΓ...
  rewrite trans_subst_sty...
Qed.



Lemma mtsubst_typ : forall (Δ : stctx) Γ s t A,
    rel_d Δ s ->
    typ (map (const tt) Δ) (∥ Γ ∥) t (| A |) ->
    typ nil (∥ map (mtsubst_in_sty s) Γ ∥) (mtsubst_in_exp s t) (| mtsubst_in_sty s A |).
Proof with eauto using swft_wft.
   introv H.
   gen Γ t A.
  induction H; introv Typ.

  - Case "empty".
    simpls.
    rewrite mtsubst_nil...

  - Case "cons".
    simpls.

    lets (? & ?) : rel_d_uniq...
    simpl_env.

    rewrite mtsubst_cons...
    eapply IHrel_d...
    rewrite trans_subst_sty.
    rewrite mtsubst_trans...
    rewrite_env (nil ++ map (const tt) Δ).
    eapply typing_through_subst_typ_in_exp...

    rewrite_env (map (const tt) Δ ++ nil).
    eapply wft_weaken_head...
    apply swft_wft_nil...
 Qed.


Lemma mtsubst_sub : forall A B Δ c s,
    rel_d Δ s ->
    sub Δ A B c ->
    sub nil (mtsubst_in_sty s A) (mtsubst_in_sty s B) c.
Proof with eauto.
  introv Eq.
  gen A B c.
  induction Eq; introv Sub; simpls...
  lets (? & ?) : rel_d_uniq...
  apply IHEq...
  rewrite_env (map (subst_sty_in_sty t X) nil ++ Δ).
  eapply sub_subst; simpls...
  rewrite_env (nil ++ Δ ++ nil).
  eapply swft_weaken; simpls...
Qed.


Lemma mtsubst_mono : forall Δ p t,
    rel_d Δ p ->
    mono t ->
    mono (mtsubst_in_sty p t).
Proof with eauto.
  introv WF.
  gen t.
  induction WF; introv Mono; simpls...
  apply IHWF...
  apply subst_mono...
Qed.



Lemma swft_subst_ctx: forall Δ2 Δ1 A p,
   swft (Δ1 ++ Δ2) A ->
   swfte (Δ1 ++ Δ2) ->
   rel_d Δ2 p ->
   swft (map (mtsubst_in_sty p) Δ1) (mtsubst_in_sty p A).
Proof with eauto.
  intros Δ2.
  induction Δ2; introv Wft Wfte RelD; simpls...
  inverts RelD.
  simpls...
  rewrite mtsubst_nil...
  simpl_env in Wft...

  inverts RelD as ? RelD.
  lets (? & ?) : rel_d_uniq RelD.
  assert (swft Δ2 t).
  rewrite_env (Δ2 ++ nil).
  eapply swft_weaken_head...

  rewrite mtsubst_cons.
  simpls.
  eapply IHΔ2...
  eapply swft_subst_tb...
  exact Wft.

  lets : uniq_from_swfte Wfte.
  solve_uniq.
  eapply swfte_subst_tb...
  exact Wfte.
Qed.


Lemma sub_subst_ctx: forall Δ2 Δ1 p A B c,
   sub (Δ1 ++ Δ2) A B c->
   swfte (Δ1 ++ Δ2) ->
   rel_d Δ2 p ->
   sub (map (mtsubst_in_sty p) Δ1) (mtsubst_in_sty p A) (mtsubst_in_sty p B) c.
Proof with eauto.
  intros Δ2.
  induction Δ2; introv Sub Wfte RelD.
  inverts RelD.
  rewrite mtsubst_nil...
  simpls...
  simpl_env in Sub...

  inverts RelD as ? RelD.
  lets (? & ?) : rel_d_uniq RelD.
  assert (swft Δ2 t).
  rewrite_env (Δ2 ++ nil).
  eapply swft_weaken_head...

  rewrite mtsubst_cons...
  simpls...
  eapply IHΔ2...
  eapply sub_subst...
  exact Sub.

  lets : uniq_from_swfte Wfte.
  solve_uniq.
  eapply swfte_subst_tb...
  exact Wfte.

Qed.


Lemma swfte_subst_ctx: forall Δ2 Δ1 p,
   swfte (Δ1 ++ Δ2) ->
   rel_d Δ2 p ->
   swfte (map (mtsubst_in_sty p) Δ1).
Proof with eauto.
  intros Δ2.
  induction Δ2; introv Wfte RelD.
  inverts RelD.
  rewrite mtsubst_nil...
  simpl_env in Wfte...

  inverts RelD as ? RelD.
  lets (? & ?) : rel_d_uniq RelD.

  rewrite mtsubst_cons...
  eapply IHΔ2...
  eapply swfte_subst_tb...
  exact Wfte.
  rewrite_env (Δ2 ++ nil).
  eapply swft_weaken_head...

Qed.



Lemma mtsubst_tvar_notin : forall p X,
    X `notin` dom p ->
    mtsubst_in_sty p (sty_var_f X) = (sty_var_f X).
Proof with auto.
  intros p.
  alist induction p; intros; simpls...
  case_if...
  substs...
  false H.
  solve_notin.
Qed.



(* ********************************************************************** *)
(** ** Renaming lemmas . *)

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


Lemma typing_tvar_rename : forall X Γ Y G e T,
    typ ([(X, tt)] ++ G) Γ (open_exp_wrt_ty e (ty_var_f X)) (open_ty_wrt_ty T (ty_var_f X)) ->
    wfe G Γ ->
    X `notin` dom G ->
    X `notin` dom Γ ->
    X `notin` fv_ty_in_ty T ->
    X `notin` fv_ty_in_exp e ->
    Y `notin` dom G ->
    Y `notin` dom Γ ->
    Y `notin` fv_ty_in_ty T ->
    Y `notin` fv_ty_in_exp e ->
    typ ([(Y, tt)] ++ G) Γ (open_exp_wrt_ty e (ty_var_f Y)) (open_ty_wrt_ty T (ty_var_f Y)).
Proof with eauto.
  introv TypX ? ? ? ? ? ? ? ? ?.
  destruct (X == Y); substs...

  assert (Wfe : wfe ([(X, tt)] ++ G) Γ)...
  assert (Uniq : uniq ([(X, tt)] ++ G))...
  inverts Uniq.

  rewrite (subst_ty_in_exp_intro X)...
  rewrite (subst_ty_in_ty_intro X)...
  rewrite_env (nil ++ [(Y, tt)] ++ G).
  replace Γ with (map (subst_ty_in_ty (ty_var_f Y) X) Γ).
  apply typing_through_subst_typ_in_exp...
  rewrite_env ([(X , tt)] ++ [(Y, tt)] ++ G).
  eapply typing_tvar_weakening...
  rewrite map_subst_typ_in_binding_id with (Z := X) (P := ty_var_f Y) (D := G)...
Qed.



Lemma typing_rename : forall x y E t U T G,
    typ G ([(x, U)] ++ E) (open_exp_wrt_exp t (exp_var_f x)) T ->
    x `notin` dom G \u dom E \u fv_exp_in_exp t ->
    y `notin` dom G \u dom E \u fv_exp_in_exp t ->
    typ G ([(y, U)] ++ E) (open_exp_wrt_exp t (exp_var_f y)) T.
Proof with eauto.
  introv TyX ? ?.
  destruct (x == y); substs...

  assert (Wfe : wfe G ([(x, U)] ++ E))...
  inverts Wfe.

  rewrite (subst_exp_in_exp_intro x)...
  rewrite_env (nil ++ [(y, U)] ++ E).
  apply typing_through_subst_exp_in_exp with (U := U)...
  rewrite_env ([(x, U)] ++ [(y, U)] ++ E).
  eapply typing_var_weakening...
Qed.



(* ********************************************************************** *)
(** * Enhance auto *)



Hint Rewrite mtsubst_ty_open msubst_ty_open_wrt_ty mtsubst_nat mtsubst_top mtsubst_arr mtsubst_forall mtsubst_and mtsubst_rcd mtsubst_open mtsubst_tabs mtsubst_abs msubst_tabs msubst_abs mtsubst_app msubst_unit msubst_lit msubst_app  mtsubst_tapp msubst_tapp mtsubst_pair msubst_pair mtsubst_lit mtsubst_unit mtsubst_capp msubst_capp trans_open_sty trans_subst_sty : lr_rewrite.


Hint Resolve mono_lc poly_lc swft_wft swft_wft_nil swft_type lc_sty_ty fv_sty_nil multi_red_tapp multi_red_capp multi_red_pair multi_red_app1 same_eq same_sym star_one star_trans swft_change swft_from_swfte swft_from_swfe mtsubst_swft swft_subst_ctx.
