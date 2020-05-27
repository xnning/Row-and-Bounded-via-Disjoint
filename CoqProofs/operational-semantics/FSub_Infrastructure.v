(** Infrastructure lemmas and tactic definitions for Fsub.

    Adapted from Metalib.

 *)

Require Export FSub_Definitions.


(* ********************************************************************** *)
(** * Free variables *)

Fixpoint fv_tt (T : ftyp) {struct T} : atoms :=
  match T with
  | ftyp_top => {}
  | ftyp_nat => {}
  | ftyp_rcd_nil => {}
  | ftyp_rcd_cons i T1 T2 =>(fv_tt T1) `union` (fv_tt T2)
  | ftyp_bvar J => {}
  | ftyp_fvar X => {{ X }}
  | ftyp_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | ftyp_all T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  end.

Fixpoint fv_te (e : fexp) {struct e} : atoms :=
  match e with
  | fexp_top => {}
  | fexp_lit _ => {}
  | fexp_rcd_nil => {}
  | fexp_rcd_cons i e1 e2 =>(fv_te e1) `union` (fv_te e2)
  | fexp_rcd_proj e i => fv_te e
  | fexp_bvar i => {}
  | fexp_fvar x => {}
  | fexp_abs V e1  => (fv_tt V) `union` (fv_te e1)
  | fexp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | fexp_tabs V e1 => (fv_tt V) `union` (fv_te e1)
  | fexp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  end.

Fixpoint fv_ee (e : fexp) {struct e} : atoms :=
  match e with
  | fexp_top => {}
  | fexp_lit i => {}
  | fexp_bvar i => {}
  | fexp_fvar x => {{ x }}
  | fexp_rcd_nil => {}
  | fexp_rcd_cons i e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | fexp_rcd_proj e1 i => (fv_ee e1)
  | fexp_abs V e1 => (fv_ee e1)
  | fexp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | fexp_tabs V e1 => (fv_ee e1)
  | fexp_tapp e1 V => (fv_ee e1)
  end.


(* ********************************************************************** *)
(** * Substitution *)

Fixpoint subst_tt (Z : atom) (U : ftyp) (T : ftyp) {struct T} : ftyp :=
  match T with
  | ftyp_top => ftyp_top
  | ftyp_nat => ftyp_nat
  | ftyp_bvar J => ftyp_bvar J
  | ftyp_fvar X => if X == Z then U else T
  | ftyp_rcd_nil => ftyp_rcd_nil
  | ftyp_rcd_cons i T1 T2 => ftyp_rcd_cons i (subst_tt Z U T1) (subst_tt Z U T2)
  | ftyp_arrow T1 T2 => ftyp_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | ftyp_all T1 T2 => ftyp_all (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Fixpoint subst_te (Z : atom) (U : ftyp) (e : fexp) {struct e} : fexp :=
  match e with
  | fexp_top => fexp_top
  | fexp_lit i => fexp_lit i
  | fexp_bvar i => fexp_bvar i
  | fexp_fvar x => fexp_fvar x
  | fexp_rcd_nil => fexp_rcd_nil
  | fexp_rcd_cons i e1 e2 => fexp_rcd_cons i (subst_te Z U e1) (subst_te Z U e2)
  | fexp_rcd_proj e1 i => fexp_rcd_proj (subst_te Z U e1) i
  | fexp_abs V e1 => fexp_abs  (subst_tt Z U V)  (subst_te Z U e1)
  | fexp_app e1 e2 => fexp_app  (subst_te Z U e1) (subst_te Z U e2)
  | fexp_tabs V e1 => fexp_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | fexp_tapp e1 V => fexp_tapp (subst_te Z U e1) (subst_tt Z U V)
  end.

Fixpoint subst_ee (z : atom) (u : fexp) (e : fexp) {struct e} : fexp :=
  match e with
  | fexp_top => fexp_top
  | fexp_lit i => fexp_lit i
  | fexp_bvar i => fexp_bvar i
  | fexp_fvar x => if x == z then u else e
  | fexp_rcd_nil => fexp_rcd_nil
  | fexp_rcd_cons i e1 e2 => fexp_rcd_cons i (subst_ee z u e1) (subst_ee z u e2)
  | fexp_rcd_proj e1 i => fexp_rcd_proj (subst_ee z u e1) i
  | fexp_abs V e1 => fexp_abs V (subst_ee z u e1)
  | fexp_app e1 e2 => fexp_app (subst_ee z u e1) (subst_ee z u e2)
  | fexp_tabs V e1 => fexp_tabs V (subst_ee z u e1)
  | fexp_tapp e1 V => fexp_tapp (subst_ee z u e1) V
  end.

Definition subst_tb (Z : atom) (P : ftyp) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.


(* ********************************************************************** *)
(** * The "[gather_atoms]" tactic *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : fexp => fv_te x) in
  let D := gather_atoms_with (fun x : fexp => fv_ee x) in
  let E := gather_atoms_with (fun x : ftyp => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F).


(* ********************************************************************** *)
(** *  Properties of opening and substitution *)


Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V k U Neq H; simpl in *; inversion H; f_equal...
  Case "ftyp_bvar".
    destruct (j === n)... destruct (k === n)...
Qed.

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "ftyp_all".
    unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (ftyp_fvar X))...
Qed.

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto.
  induction T; simpl; intro H; f_equal...
  Case "ftyp_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "ftyp_bvar".
    destruct (k === n); subst...
  Case "ftyp_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (ftyp_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "ftyp_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "ftyp_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.


Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with congruence || eauto.
  induction e; intros j u k P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q k P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := fexp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := ftyp_fvar X);
    auto
  ].
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_te e ->
  e = subst_te X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  type U ->
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with congruence || auto.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k (ftyp_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X `notin` fv_te e ->
  open_te e U = subst_te X U (open_te e X).
Proof with auto.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.


Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with congruence || eauto.
  induction e; intros j v u k Neq H; simpl in *; inversion H; f_equal...
  Case "fexp_bvar".
    destruct (j===n)... destruct (k===n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u k H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with auto.
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := fexp_fvar x);
    auto
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := ftyp_fvar X);
    auto
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with auto.
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "fexp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "fexp_bvar".
    destruct (k === n); subst...
  Case "fexp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with congruence || auto.
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
  subst_te Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te Z P e2) (subst_te Z P e1).
Proof with auto.
  induction e1; intros e2 Z P k; simpl; f_equal...
  Case "fexp_bvar".
    destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
  subst_te Z P (open_ee e1 e2) = open_ee (subst_te Z P e1) (subst_te Z P e2).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
  open_ee (subst_te Z P e) x = subst_te Z P (open_ee e x).
Proof with auto.
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u k,
  expr u ->
  subst_ee z u (open_te_rec k P e) = open_te_rec k P (subst_ee z u e).
Proof with auto.
  induction e; intros P z u k H; simpl; f_equal...
  Case "fexp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
  expr u ->
  subst_ee z u (open_te e P) = open_te (subst_ee z u e) P.
Proof with auto.
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u e,
  expr u ->
  open_te (subst_ee z u e) X = subst_ee z u (open_te e X).
Proof with auto.
  intros z X u e H.
  rewrite subst_ee_open_te...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (fexp_fvar x) e).
Proof with congruence || auto.
  induction e; intros u k Fr; simpl in *; f_equal...
  Case "fexp_bvar".
    destruct (k === n)... simpl. destruct (x == x)...
  Case "fexp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
Qed.

Lemma subst_ee_intro : forall x e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with auto.
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* *********************************************************************** *)
(** * Local closure is preserved under substitution *)

Lemma subst_tt_rt_type : forall Z P T,
  rt_type T ->
  rt_type (subst_tt Z P T).
Proof.
  induction  1; intros; simpl; auto.
Qed.

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto using subst_tt_rt_type.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_fvar".
    destruct (X == Z)...
  Case "type_all".
    pick fresh Y and apply type_all...
    rewrite subst_tt_open_tt_var...
Qed.


Lemma subst_te_rt_expr : forall Z P e,
  rt_expr e ->
  rt_expr (subst_te Z P e).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma subst_te_expr : forall Z P e,
  expr e ->
  type P ->
  expr (subst_te Z P e).
Proof with eauto using subst_tt_type, subst_te_rt_expr.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_tt_type, subst_te_rt_expr;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_te_open_ee_var;
    try rewrite subst_te_open_te_var;
    instantiate;
    eauto using subst_tt_type
  ].
Qed.


Lemma subst_ee_rt_expr : forall Z P e,
  rt_expr e ->
  rt_expr (subst_ee Z P e).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma subst_ee_expr : forall z e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee z e2 e1).
Proof with auto using subst_ee_rt_expr.
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto using subst_ee_rt_expr;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    instantiate;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
Qed.


(* *********************************************************************** *)
(** * Properties of [body_e] *)


Lemma open_ee_body_e : forall e1 e2,
  body_e e1 -> expr e2 -> expr (open_ee e1 e2).
Proof.
  intros e1 e2 [L H] J.
  pick fresh x.
  rewrite (subst_ee_intro x); auto using subst_ee_expr.
Qed.


(* *********************************************************************** *)
(** *  Automation *)

Hint Resolve subst_tt_rt_type subst_tt_type subst_te_expr subst_ee_expr subst_te_rt_expr subst_ee_rt_expr.

Hint Resolve open_ee_body_e.

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)).
