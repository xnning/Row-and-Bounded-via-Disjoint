Require Import Infrastructure.
Require Import SourceProperty.
Require Import Omega.
Require Import Assumed.
Require Import Disjoint.
Require Import TargetProperty.


From Equations Require Import Equations.



(* ********************************************************************** *)
(** * Auxiliary definitions *)


Module terminating.
  Definition t (P : exp_relation) (e1 e2 : exp) :=
    exists v1 v2, e1 ->* v1 /\ e2 ->* v2 /\ value v1 /\ value v2 /\ P v1 v2.

  Lemma impl :
    forall (P Q : exp_relation),
      (forall e1 e2, P e1 e2 -> Q e1 e2) ->
      (forall e1 e2, terminating.t P e1 e2 -> terminating.t Q e1 e2).
  Proof with eauto.
    introv H EH.
    destruct EH as (v1 & v2 & ? & ? & ? & ? & EH).
    specializes H EH.
    exists v1 v2...
  Qed.


  Lemma iff :
    forall (P Q : exp_relation),
      (forall e1 e2, P e1 e2 <-> Q e1 e2) ->
      (forall e1 e2, terminating.t P e1 e2 <-> terminating.t Q e1 e2).
  Proof.
    intros P Q HPQ e1 e2.
    split; apply impl; firstorder.
  Qed.
End terminating.


Module num_of_all.
  Fixpoint num_of_all (t: sty) : nat :=
    match t with
        | sty_nat => 0
        | sty_top => 0
        | sty_bot => 0
        | sty_var_b n => 0
        | sty_var_f x => 0
        | sty_arrow A B => (num_of_all A) + (num_of_all B)
        | sty_and A B => (num_of_all A) + (num_of_all B)
        | sty_all A B => 1 + (num_of_all B)
        | sty_rcd l A => num_of_all A
    end.
  
  Lemma num_of_all_mono : forall t,
      mono t ->
      num_of_all t = 0.
  Proof with auto.
    introv mn. inductions mn; simpl;
                 try(rewrite IHmn1, IHmn2)...
  Qed.
  
  Lemma num_of_all_open_mono : forall B t,
    mono t ->
    num_of_all (open_sty_wrt_sty B t) = num_of_all B.
  Proof with eauto using num_of_all_mono.
    intro B. unfold open_sty_wrt_sty.
    generalize 0; inductions B; introv mn; simpl...
    destruct (lt_eq_lt_dec n n0); simpl...
    destruct s...
  Qed.
End num_of_all.

Inductive rel_nat : exp -> exp -> Prop :=
| RelInt : forall n, rel_nat (exp_lit n) (exp_lit n).

Hint Constructors rel_nat.


Definition size_sum (ty : sty * sty) := size_sty (fst ty) + size_sty (snd ty).

Definition size_all (ty : sty * sty) := num_of_all.num_of_all (fst ty) + num_of_all.num_of_all (snd ty).

Definition sizeOrder (ty1 ty2 : sty * sty) := size_sum ty1 < size_sum ty2.



(* ****************************************************************************** *)
(** * Value relation (well-foundedness proof (Lemma 5) can be found in the paper) *)

Equations V (A B : sty) (v1 v2 : exp ) : Prop :=
V A B v1 v2 by rec (A, B) sizeOrder :=

V sty_nat sty_nat v1 v2 := rel_nat v1 v2;

V (sty_arrow A1 B1) (sty_arrow A2 B2) v1 v2 := value v1 /\ value v2 /\
  forall v1' v2', V A2 A1 v2' v1'  ->
    typ nil nil v1' (|A1|) ->
    typ nil nil v2' (|A2|) ->
    exists vv1 vv2,
      exp_app v1 v1' ->* vv1 /\
      exp_app v2 v2' ->* vv2 /\
      value vv1 /\
      value vv2 /\
      V B1 B2 vv1 vv2;

V (sty_rcd l1 A) (sty_rcd l2 B) v1 v2 := value v1 /\ value v2 /\ if l1 == l2 then V A B v1 v2 else True ;

V (sty_all A1 B1) (sty_all A2 B2) v1 v2 := value v1 /\ value v2 /\
  forall t,
    disjoint nil t (sty_and A1 A2) ->
    swft nil t ->
    mono t ->
    exists vv1 vv2,
      exp_tapp v1 (| t |) ->* vv1 /\
      exp_tapp v2 (| t |) ->* vv2 /\
      value vv1 /\
      value vv2 /\
      V (open_sty_wrt_sty B1 t)
        (open_sty_wrt_sty B2 t)
        vv1 vv2;

V (sty_and A B) ty2 v1 v2 := value v1 /\ value v2 /\
  exists v11 v12,
    v1 = exp_pair v11 v12 /\
    V A ty2 v11 v2 /\
    V B ty2 v12 v2;

V ty1 (sty_and A B) v1 v2 := value v1 /\ value v2 /\
  exists v21 v22,
    v2 = exp_pair v21 v22 /\
    V ty1 A v1 v21 /\
    V ty1 B v1 v22;

V _ _ v1 v2 := value v1 /\ value v2.

Admit Obligations.



(* ********************************************************************** *)
(** * Expression relation *)

Definition E A B e1 e2 :=
  swft nil A /\
  swft nil B /\
  typ nil nil e1 (|A|) /\
  typ nil nil e2 (|B|) /\
  terminating.t (V A B) e1 e2.


(* ********************************************************************** *)
(** * Logical interpretation of term contexts *)

Inductive rel_g : sctx -> sctx -> list (atom * exp) -> list (atom * exp) -> Prop :=
| rel_g_empty : forall p, rel_g nil p nil nil
| rel_g_cons : forall x G g1 g2 A v1 v2 p,
    x `notin` dom G ->
    rel_g G p g1 g2 ->
    fv_sty_in_sty A [<=] dom p ->
    typ nil nil v1 (| mtsubst_in_sty p A |) ->
    typ nil nil v2 (| mtsubst_in_sty p A |) ->
    V (mtsubst_in_sty p A) (mtsubst_in_sty p A) v1 v2 ->
    rel_g ([(x, A)] ++ G) p ([(x , v1)] ++ g1) ([(x , v2)] ++ g2).

Hint Constructors rel_g.


(* ********************************************************************** *)
(** * Logical equivalence *)

Definition E_open Δ Γ e1 e2 A B :=
  swft Δ A /\
  swft Δ B /\
  typ (map (const tt) Δ) (∥ Γ ∥) e1 (| A |) /\
  typ (map (const tt) Δ) (∥ Γ ∥) e2 (| B |) /\
  forall p g1 g2,
    rel_d Δ p ->
    rel_g Γ p g1 g2 ->
    E (mtsubst_in_sty p A) (mtsubst_in_sty p B)
      (msubst_in_exp g1 (mtsubst_in_exp p e1))
      (msubst_in_exp g2 (mtsubst_in_exp p e2)).


Lemma rel_g_same : forall Γ p g1 g2,
    rel_g Γ p g1 g2 -> same_stctx Γ g1 /\ same_stctx Γ g2.
Proof with simpl_env; eauto.
  induction 1; simpls...
  destructs IHrel_g.
  splits...
Qed.


Lemma rel_g_notin : forall Γ p g1 g2 x,
    rel_g Γ p g1 g2 ->
    x `notin` dom Γ ->
    x `notin` dom g1 /\ x `notin` dom g2.
Proof with eauto.
  introv RelG.
  induction RelG; simpls...
Qed.

Lemma rel_g_uniq : forall Γ p g1 g2,
    rel_g Γ p g1 g2 ->
    uniq Γ /\ uniq g1 /\ uniq g2.
Proof with eauto using rel_g_notin.
  introv RelG.
  induction RelG; simpls...
  forwards (? & ?) : rel_g_notin RelG...
  splits; try solve_uniq...
Qed.


(* ********************************************************************** *)
(** * Properties of logical exp_relation *)

Lemma V_value :
  forall A B v1 v2,
    V A B v1 v2 ->
    value v1 /\ value v2.
Proof with eauto.
  introv  HVrel.
  destruct A; destruct B; try simp V in HVrel; try destructs HVrel...
  inverts HVrel...
Qed.


Lemma E_type : forall A B e1 e2,
    E A B e1 e2 ->
    typ nil nil e1 (|A|) /\
    typ nil nil e2 (|B|).
Proof.
  introv H.
  destructs H; auto.
Qed.


Lemma E_conv1 : forall A B e1 e1' e2,
    E A B e1' e2 ->
    step e1 e1' ->
    typ nil nil e1 (|A|) ->
    E A B e1 e2.
Proof with eauto.
  introv HE ? ?.

  destruct HE as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).
  splits...
  exists v1 v2.
  splits...
Qed.


Lemma E_conv2 : forall A B e1 e2 e2',
    E A B e1 e2' ->
    step e2 e2' ->
    typ nil nil e2 (|B|) ->
    E A B e1 e2.
Proof with eauto.
  introv HE ? ?.

  destruct HE as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).
  splits...
  exists v1 v2.
  splits...
Qed.


Lemma E_star1 : forall A B e1 e1' e2,
    e1 ->* e1' ->
    E A B e1' e2 ->
    typ nil nil e1 (|A|) ->
    E A B e1 e2.
Proof with eauto using preservation, E_conv1.
  introv Star E12 Ty.
  revert A B e2 E12 Ty.
  induction Star...
Qed.


Lemma E_star2 : forall A B e1 e2 e2',
    e2 ->* e2' ->
    E A B e1 e2' ->
    typ nil nil e2 (|B|) ->
    E A B e1 e2.
Proof with eauto using preservation, E_conv2.
  introv Star E12 Ty.
  revert A B e1 E12 Ty.
  induction Star...
Qed.


Ltac simplifier :=
  repeat match goal with
         | H : ?v ->* ?v', V1 : value ?v, V2 : value ?v' |- _ =>
           apply value_no_step in H; autos; substs
         | H1 : ?t ->* ?v1, H2 : ?t ->* ?v2, V1 : value ?v1, V2 : value ?v2 |- _ =>
           forwards : finseq_unique step_unique H2 H1; eauto using value_irred; substs; clear H2
         end.


Lemma E_starr1 : forall A B e1 e1' e2,
    e1 ->* e1' ->
    E A B e1 e2 ->
    E A B e1' e2.
Proof with eauto.
  introv Red EH.

  destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).

  lets Ty :  preservation_multi_step H1 Red.
  lets (v1' & ? & ?) : normalization Ty.

  assert (e1 ->* v1').
  apply star_trans with (b := e1')...

  simplifier.

  splits...

  exists v1 v2.

  splits...

Qed.


Lemma E_starr2 : forall A B e1 e2 e2',
    e2 ->* e2' ->
    E A B e1 e2 ->
    E A B e1 e2'.
Proof with eauto.
  introv Red EH.

  destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).

  lets Ty :  preservation_multi_step H2 Red.
  lets (v2' & ? & ?) : normalization Ty.

  assert (e2 ->* v2').
  apply star_trans with (b := e2')...

  simplifier.

  splits...

  exists v1 v2.

  splits...

Qed.


Lemma V_topl : forall A v1 v2,
    value v1 ->
    value v2 ->
    typ nil nil v2 (| A |) ->
    V sty_top A v1 v2.
Proof with eauto.
  intros A.
  induction A; introv V1 V2 Typ; simp V; simpls...
  splits...
  forwards (v21 & v22 & ? & ? & ?): prod_canonical Typ...
  substs.
  inverts V2.
  inverts Typ.
  exists  v21 v22.
  splits...
Qed.


Lemma V_topr : forall A v1 v2,
    value v1 ->
    value v2 ->
    typ nil nil v1 (| A |) ->
    V A sty_top v1 v2.
Proof with eauto.
  intros A.
  induction A; introv V1 V2 Typ; simp V; simpls...
  splits...
  forwards (v21 & v22 & ? & ? & ?): prod_canonical Typ...
  substs.
  inverts V1.
  inverts Typ.
  exists  v21 v22.
  splits...
Qed.


Lemma V_andl : forall C v11 v12 v2 A B,
    value v11 ->
    value v12 ->
    value v2 ->
    typ nil nil v11 (|A|) ->
    typ nil nil v12 (|B|) ->
    V (sty_and A B) C (exp_pair v11 v12) v2 <->
    V A C v11 v2 /\ V B C v12 v2.
Proof with eauto.
  intros C.
  induction C; introv V11 V12 V2 Typ1 Typ2.

  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

  splits.
  introv RelV.
  splits; apply V_topr...
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits...


  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

  splits.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

Qed.


Lemma V_andr : forall C v11 v12 v2 A B,
    value v11 ->
    value v12 ->
    value v2 ->
    typ nil nil v2 (|C|) ->
    typ nil nil v11 (|A|) ->
    typ nil nil v12 (|B|) ->
    V C (sty_and A B) v2 (exp_pair v11 v12) <->
    V C A v2 v11 /\ V C B v2 v12.
Proof with eauto.
  intros C.
  induction C; introv V11 V12 V2 Typ1 Typ2 Typ3.

  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  split.
  introv RelV.
  splits; apply V_topl...
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits...


  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  simpls.
  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  substs.
  lets (? & ?) : V_value RelV1.
  lets (? & ?) : V_value RelV2.
  inverts Typ1.
  assert (Temp : V C1 A v11' v11 /\ V C1 B v11' v12).
  apply IHC1...
  destructs Temp.
  assert (Temp: V C2 A v12' v11 /\ V C2 B v12' v12).
  apply IHC2...
  destructs Temp.
  splits; apply V_andl...

  introv (RelV1 & RelV2).
  simp V.
  splits~.
  lets~ (v21 & v22 & ? & ? & ?): prod_canonical Typ1.
  substs.
  inverts Typ1.
  apply V_andl in RelV1...
  apply V_andl in RelV2...
  destructs RelV1.
  destructs RelV2.
  exists v21 v22.
  splits~.
  apply IHC1...
  apply IHC2...


  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.


  split.
  introv RelV.
  simp V in RelV.
  destruct RelV as (ValP & ? & v11' & v12' & Eq & RelV1 & RelV2).
  inverts Eq.
  splits~.
  introv (RelV1 & RelV2).
  lets (? & ?): V_value RelV1.
  lets (? & ?): V_value RelV2.
  simp V.
  splits~.
  exists v11 v12.
  splits~.

Qed.




Lemma var_empty : forall v X,
    typ nil nil v (ty_var_f X) ->
    False.
Proof with eauto.
  introv H.
  lets (? & ? & Bad): typing_regular H.
  apply ftv_in_dom in Bad.
  simpls.
  assert (X `in` empty).
  fsetdec.
  eapply empty_iff...
Qed.


Lemma V_sym_helper : forall m A B v1 v2,
    num_of_all.num_of_all A < m ->
    lc_sty A ->
    lc_sty B ->
    typ nil nil v1 (|A|) ->
    typ nil nil v2 (|B|) ->
    V A B v1 v2 ->
    V B A v2 v1.
Proof with eauto; try omega.
  intro m. induction m; introv lem.
  inversion lem.

  introv TA.
  gen B v1 v2.
  induction TA; simpl in lem.

  - Case "A = nat".
    introv TB.
    gen v1 v2.
    induction TB; introv TyA TyB VH; simp V in *; try solve [inverts~ VH | destructs~ VH].
    destruct VH as (? & ? & v21 & v22 & ? & ? & ?).
    substs.
    simpls.
    inverts TyB.
    splits...
    exists v21 v22.
    splits...

  - Case "A = top".
    introv TB TyA TyB VH.
    lets (? & ?): V_value VH.
    apply V_topr...

  - Case "A = bot".
    introv TB TyA TyB VH.
    lets (? & ?): V_value VH.
    simpls.
    eapply ty_absurd in TyA; simpls...

  - Case "A = var".
    intros.
    simpls.
    false var_empty...

  - Case "A = arrow".
    introv TB.
    gen v1 v2.
    induction TB; introv TyA TyB VH; simp V in *; try solve [inverts~ VH | destructs~ VH].
    + SCase "B = arrow ".
      destruct VH as (? & ? & VH).
      splits...
      introv VH1 TV1 TV2.
      apply IHTA1 in VH1...
      forwards (vv1 & vv2 & ? & ? & ? & ? & VH2) : VH VH1...
      exists vv2 vv1.
      splits...
      apply IHTA2...
      eapply preservation_multi_step...
      eapply preservation_multi_step...
    + SCase "B = and".
      destruct VH as (? & ? & v21 & v22 & ? & ? & VH).
      substs.
      inverts TyB.
      splits...
      exists v21 v22.
      splits...

  - Case "A = and".
    introv TB TyA TyB VH.
    lets (? & ?) : V_value VH.
    simpls.
    lets Prod : prod_canonical TyA...
    destruct Prod as (vv1 & vv2 & ? & ? & ?).
    substs.
    inverts TyA.
    eapply V_andr...
    eapply V_andl in VH...
    destruct VH as (VH1 & VH2).
    splits...
    apply IHTA1...
    apply IHTA2...

  - Case "A = forall".
    introv TB.
    gen v1 v2.
    induction TB; introv TyA TyB VH; simp V in *; try solve [inverts~ VH | destructs~ VH].
    + SCase "B = and".
      destruct VH as (? & ? & v21 & v22 & ? & ? & VH).
      substs.
      inverts TyB.
      splits...
      exists v21 v22.
      splits...

    + SCase "B = forall".
      destruct VH as (? & ? & VH).
      splits...
      introv Dis WFT Mono.
      assert (Dis' : disjoint [] t (sty_and A A0)).
      apply disjoint_and in Dis...
      destruct Dis.
      eapply disjoint_and...
      forwards (vv1 & vv2 & ? & ? & ? & ? & VH') : VH Dis'...
      exists vv2 vv1.
      splits...

      apply IHm...
      rewrite num_of_all.num_of_all_open_mono...
      apply lc_body_sty_wrt_sty...
      apply lc_body_sty_wrt_sty...
      eapply preservation_multi_step with (exp_tapp v1 (| t |))...
      autorewrite with lr_rewrite...
      apply preservation_multi_step with (exp_tapp v2 (| t |))...
      autorewrite with lr_rewrite...

  - Case "A = record".
    introv TB.
    gen v1 v2.
    induction TB; introv TyA TyB VH; simp V in *; try solve [inverts~ VH | destructs~ VH].
    + SCase "B = and".
      destruct VH as (? & ? & v21 & v22 & ? & ? & VH).
      substs.
      inverts TyB.
      splits...
      exists v21 v22.
      splits...

    + SCase "B = record".
      destruct VH as (? & ? & VH).
      splits...
      case_if in VH; case_if...
Qed.


Lemma V_sym : forall A B v1 v2,
    lc_sty A ->
    lc_sty B ->
    typ nil nil v1 (|A|) ->
    typ nil nil v2 (|B|) ->
    V A B v1 v2 ->
    V B A v2 v1.
Proof with eauto.
  intros.
  eapply V_sym_helper...
Qed.


Lemma E_sym : forall e1 e2 A B,
    E A B e1 e2 ->
    E B A e2 e1.
Proof with eauto.
  introv EH.
  destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & VH).
  splits...
  exists v2 v1.
  splits...
  apply V_sym; try eapply preservation_multi_step...
Qed.


Lemma V_toplike_helper : forall m A B v1 v2,
    num_of_all.num_of_all A < m ->
    TopLike A ->
    lc_sty B ->
    lc_sty A ->
    value v1 ->
    value v2 ->
    typ nil nil v1 (| A |) ->
    typ nil nil v2 (| B |) ->
    V A B v1 v2.
Proof with eauto; try omega.
  intro m. induction m; introv lem.
  inversion lem.

  introv TA.
  gen B v1 v2.
  induction TA; simpl in lem.

  - Case "top".
    intros.
    eapply V_topl...

  - Case "and".
    introv LC1 LC2 ? ? TyA TyB.
    simpls.
    inverts LC2.
    lets (vv1 & vv2 & ? & ? & ?) : prod_canonical TyA...
    substs.
    inverts TyA.
    eapply V_andl...
    splits...
    apply IHTA1...
    apply IHTA2...

  - Case "arrow".
    introv TB.
    gen v1 v2.
    induction TB; introv LC1 ? ? TyA TyB; simp V; splits; simpls...

    + SCase "arrow".
      introv VH Ty11 Ty22.
      inverts LC1.

      lets Ty3 : typ_app TyA Ty11.
      lets Ty4 : typ_app TyB Ty22.
      lets (vv1 & ? & Tvv1) : normalization Ty3.
      lets (vv2 & ? & Tvv2) : normalization Ty4.
      forwards : preservation_multi_step Tvv1...
      forwards : preservation_multi_step Tvv2...
      exists vv1 vv2.
      splits...
      eapply IHTA...

    + SCase "and".
      inverts LC1.

      lets~ (v21 & v22 & ? & ? & ?): prod_canonical TyB.
      substs.
      inverts TyB...
      exists v21 v22.
      splits...

  - Case "forall".
    introv TB.
    gen v1 v2.
    induction TB; introv LC1 ? ? TyA TyB; simp V; splits; simpls...

    + SCase "and".

      lets~ (v21 & v22 & ? & ? & ?): prod_canonical TyB.
      substs.
      inverts TyB...
      exists v21 v22.
      splits...

    + SCase "forall".

      introv Dis SWF Mono.

      forwards Ty3 : typ_tapp (|t|) TyA...
      forwards Ty4 : typ_tapp (|t|) TyB...
      forwards (vv1 & ? & ?) : normalization Ty3...
      forwards (vv2 & ? & ?) : normalization Ty4...
      inverts LC1.

      exists vv1 vv2.
      splits...
      eapply IHm...
      rewrite num_of_all.num_of_all_open_mono...
      pick fresh X.
      rewrite (subst_sty_in_sty_intro X)...
      eapply subst_toplike...
      apply lc_body_sty_wrt_sty...
      apply lc_body_sty_wrt_sty...
      eapply preservation_multi_step with (exp_tapp v1 (| t |))...
      autorewrite with lr_rewrite...
      eapply preservation_multi_step with (exp_tapp v2 (| t |))...
      autorewrite with lr_rewrite...


  - Case "rcd".
    introv TB.
    gen v1 v2.
    induction TB; introv LC1 ? ? TyA TyB; simp V; splits; simpls...

    + SCase "and".

      lets~ (v21 & v22 & ? & ? & ?): prod_canonical TyB.
      substs.
      inverts TyB...
      exists v21 v22.
      splits...

    + SCase "rcd".
      case_if~.
      inverts LC1.
      eapply IHTA...
Qed.


Lemma V_toplike : forall A B v1 v2,
    TopLike A ->
    lc_sty B ->
    lc_sty A ->
    value v1 ->
    value v2 ->
    typ nil nil v1 (| A |) ->
    typ nil nil v2 (| B |) ->
    V A B v1 v2.
Proof with eauto.
  intros.
  eapply V_toplike_helper...
Qed.


Lemma mono_disjoint_value : forall t1 t2 v1 v2,
    mono t1 ->
    mono t2 ->
    disjoint [] t1 t2 ->
    typ nil nil v1 (|t1|) ->
    typ nil nil v2 (|t2|) ->
    value v1 ->
    value v2 ->
    V t1 t2 v1 v2.
Proof with eauto.
  introv Mono1.
  gen v1 v2 t2.
  induction Mono1; introv Mono2 Dis Ty1 Ty2 ? ?.

  - Case "t1 is nat".
    gen v1 v2.
    induction Mono2; introv Ty1 ? Ty2 ?; try solve [inverts Dis]; try simp V; simpls...
    inverts Dis as HH1 HH2 HH3; inverts HH3.
    splits...
    apply disjoint_and in Dis...
    destruct Dis.
    lets~ (v21 & v22 & ? & ? & ?): prod_canonical Ty2.
    substs.
    inverts Ty2.
    exists v21 v22.
    splits...

  - Case "t1 is top".
    apply V_topl...

  - Case "bot".
    simpls.
    eapply ty_absurd in Ty1; inverts Ty1.

  - Case "impossible var case.".
    simpls.
    false var_empty...

  - Case "t1 is arrow".
    gen v1 v2.
    induction Mono2; introv Ty1 ? Ty2 ?; try solve [inverts Dis]; try simp V; simpls...
    + SCase "t2 is arrow".
      splits...
      introv VH Ty11 Ty22.
      lets Ty3 : typ_app Ty1 Ty11.
      lets Ty4 : typ_app Ty2 Ty22.
      lets (vv1 & ? & ?) : normalization Ty3.
      lets (vv2 & ? & ?) : normalization Ty4.
      exists vv1 vv2.
      splits...
      apply IHMono1_2...
      inverts Dis as HH1 HH2 HH3...
      inverts HH1.
      inverts HH2.
      inverts HH3...
      inverts HH1.
      inverts HH2.
      inverts HH3...
      eapply preservation_multi_step...
      eapply preservation_multi_step...

    + SCase "t2 is and".
      lets~ (v21 & v22 & ? & ? & ?): prod_canonical Ty2.
      substs.
      inverts Ty2.
      apply disjoint_and in Dis...
      destruct Dis.
      splits...
      exists v21 v22.
      splits...

  - Case "t1 is and".
    simpls.
    lets~ (v21 & v22 & ? & ? & ?): prod_canonical Ty1.
    substs.
    inverts Ty1.
    apply disjoint_symmetric in Dis...
    apply disjoint_and in Dis...
    destruct Dis.
    eapply V_andl...
    splits...
    eapply IHMono1_1...
    eapply disjoint_symmetric...
    eapply IHMono1_2...
    eapply disjoint_symmetric...

  - Case "t1 is record".
    gen v1 v2.
    induction Mono2; introv Ty1 ? Ty2 ?; try solve [inverts Dis]; try simp V; simpls...
    + SCase "t2 is and".
      lets~ (v21 & v22 & ? & ? & ?): prod_canonical Ty2.
      substs.
      inverts Ty2.
      apply disjoint_and in Dis...
      destruct Dis.
      splits...
      exists v21 v22.
      splits...

    + SCase "t2 is record".
      case_if...
      splits...
      eapply IHMono1...
      inverts Dis as HH1 HH2 HH3...
      inverts HH1.
      inverts HH2.
      inverts HH3...
      inverts HH1.
      inverts HH2.
      inverts HH3...
      tryfalse.
Qed.



Lemma mono_poly_disjoint_value : forall A t v1 v2,
    poly A ->
    mono t ->
    disjoint nil t A ->
    typ nil nil v1 (|t|) ->
    typ nil nil v2 (|A|) ->
    value v1 ->
    value v2 ->
    V t A v1 v2.
Proof with eauto using disjoint_symmetric.

  introv Poly.
  gen v1 v2 t.
  induction Poly; introv Mono Dis Tyt TyA ? ?; simpls...

  - Case "Poly".
    gen v1.
    induction Mono; introv Tyt ?; simp V; simpls...

    lets (v21 & v22 & ? & ? & ?): prod_canonical Tyt...
    apply disjoint_symmetric in Dis...
    apply disjoint_and in Dis...
    destruct Dis.
    substs.
    inverts Tyt.
    splits...
    exists v21 v22.
    splits...

  - Case "and1".
    apply disjoint_and in Dis...
    destruct Dis.
    lets (v21 & v22 & ? & ? & ?): prod_canonical TyA...
    substs.
    inverts TyA.
    apply V_andr...
    splits...
    apply mono_disjoint_value...

  - Case "and2".
    apply disjoint_and in Dis...
    destruct Dis.
    lets (v21 & v22 & ? & ? & ?): prod_canonical TyA...
    substs.
    inverts TyA.
    apply V_andr...
    splits...
    apply mono_disjoint_value...

  - Case "and3".
    apply disjoint_and in Dis...
    destruct Dis.
    lets (v21 & v22 & ? & ? & ?): prod_canonical TyA...
    substs.
    inverts TyA.
    apply V_andr...

  - Case "arrow1".
    gen v1.
    induction Mono; introv Tyt ?; simp V; simpls...

    + SCase "t is arrow".
      splits...
      introv VH Ty1 Ty2.
      lets Ty3 : typ_app Tyt Ty1.
      lets Ty4 : typ_app TyA Ty2.
      forwards (vv1 & ? & Tvv1) : normalization Ty3...
      forwards (vv2 & ? & Tvv2) : normalization Ty4...
      forwards : preservation_multi_step Tvv1...
      forwards : preservation_multi_step Tvv2...
      exists vv1 vv2.
      splits...

      inverts Dis as HH1 HH2 HH3...
      inverts HH1.
      inverts HH2.
      inverts HH3.
      eapply V_toplike...

      inverts HH1.
      inverts HH2.
      inverts HH3.
      eapply V_sym...
      eapply V_toplike...

      apply mono_disjoint_value...

    + SCase "t is and".
      apply disjoint_symmetric in Dis...
      apply disjoint_and in Dis...
      destruct Dis.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Tyt...
      substs.
      inverts Tyt.
      splits...
      exists v21 v22.
      splits...

  - Case "arrow2".
    gen v1.
    induction Mono; introv Tyt ?; simp V; simpls...

    + SCase "t is arrow".
      splits...
      introv VH Ty1 Ty2.
      lets Ty3 : typ_app Tyt Ty1.
      lets Ty4 : typ_app TyA Ty2.
      forwards (vv1 & ? & Tvv1) : normalization Ty3...
      forwards (vv2 & ? & Tvv2) : normalization Ty4...
      forwards : preservation_multi_step Tvv1...
      forwards : preservation_multi_step Tvv2...
      exists vv1 vv2.
      splits...

      inverts Dis as HH1 HH2 HH3...

      inverts HH1.
      inverts HH2.
      inverts HH3.
      eapply V_toplike...

      inverts HH1.
      inverts HH2.
      inverts HH3.
      eapply V_sym...
      eapply V_toplike...

    + SCase "t is and".
      apply disjoint_symmetric in Dis...
      apply disjoint_and in Dis...
      destruct Dis.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Tyt...
      substs.
      inverts Tyt.
      splits...
      exists v21 v22.
      splits...

  - Case "arrow3".
    gen v1.
    induction Mono; introv Tyt ?; simp V; simpls...

    + SCase "t is arrow".
      splits...
      introv VH Ty1 Ty2.
      lets Ty3 : typ_app Tyt Ty1.
      lets Ty4 : typ_app TyA Ty2.
      forwards (vv1 & ? & Tvv1) : normalization Ty3...
      forwards (vv2 & ? & Tvv2) : normalization Ty4...
      forwards : preservation_multi_step Tvv1...
      forwards : preservation_multi_step Tvv2...

      exists vv1 vv2.
      splits...

      inverts Dis as HH1 HH2 HH3...
      inverts HH1.
      inverts HH2.
      inverts HH3.
      eapply V_toplike...

      inverts HH1.
      inverts HH2.
      inverts HH3.
      eapply V_sym...
      eapply V_toplike...

    + SCase "t is and".
      apply disjoint_symmetric in Dis...
      apply disjoint_and in Dis...
      destruct Dis.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Tyt...
      substs.
      inverts Tyt.
      splits...
      exists v21 v22.
      splits...

  - Case "record".
    gen v1.
    induction Mono; introv Tyt ?; simp V; simpls...

    + SCase "t is and".
      apply disjoint_symmetric in Dis...
      apply disjoint_and in Dis...
      destruct Dis.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Tyt...
      substs.
      inverts Tyt.
      splits...
      exists v21 v22.
      splits...

    + SCase "t is record".
      case_if...
      inverts Dis as HH1 HH2 HH3...

      inverts HH1.
      inverts HH2.
      inverts HH3...

      inverts HH1.
      inverts HH2.
      inverts HH3...

      tryfalse.
Qed.



Lemma rel_d_tvar_mono: forall p X D A,
    rel_d D p ->
    binds X A D ->
    mono (mtsubst_in_sty p (sty_var_f X)).
Proof with eauto.
  introv RelD.
  gen A X.
  induction RelD; introv Bind.
  analyze_binds Bind.
  forwards (? & ?): rel_d_uniq RelD.
  simpls...
  case_if...
  eapply mtsubst_mono...
  eapply IHRelD...
  analyze_binds Bind...
Qed.



Lemma disjoint_value : forall v1 v2 A B Δ p,
    disjoint Δ A B ->
    rel_d Δ p ->
    swfte Δ ->
    swft Δ A ->
    swft Δ B ->
    typ nil nil v1 (|mtsubst_in_sty p A|) ->
    typ nil nil v2 (|mtsubst_in_sty p B|) ->
    value v1 ->
    value v2 ->
    V (mtsubst_in_sty p A) (mtsubst_in_sty p B) v1 v2.
Proof with simpl_env; eauto using mtsubst_swft, preservation_multi_step.
  introv Dis.
  gen v1 v2 p.
  induction Dis; introv RelD WFE WFA WFB Ty1 Ty2 Val1 Val2; try solve [autorewrite with lr_rewrite in *;simp V; eauto].

  - Case "D-topl".
    autorewrite with lr_rewrite.
    apply V_toplike...
    eapply mtsubst_toplike...

  - Case "D-topr".
    autorewrite with lr_rewrite.
    eapply V_sym...
    apply V_toplike...
    eapply mtsubst_toplike...

  - Case "D-arr".
    autorewrite with lr_rewrite in *.
    simp V.
    splits...
    introv RelV Ty1' Ty2'.
    simpls.
    lets Ty3 : typ_app Ty1 Ty1'.
    lets Ty4 : typ_app Ty2 Ty2'.
    lets (vv1 & ? & ?) : normalization Ty3.
    lets (vv2 & ? & ?) : normalization Ty4.

    exists vv1 vv2.
    splits...
    inverts WFA.
    inverts WFB.
    apply IHDis; try eapply preservation_multi_step...


  - Case "D-andL".
    autorewrite with lr_rewrite in *.
    simpls.
    lets~ (v11 & v12 & ? & ? & ?): prod_canonical Ty1.
    substs.
    inverts Ty1.
    inverts WFA.
    apply V_andl...


  - Case "D-andR".
    autorewrite with lr_rewrite in *.
    lets~ (v21 & v22 & ? & ? & ?): prod_canonical Ty2.
    substs.
    inverts Ty2.
    inverts WFB.
    apply V_andr...


  - Case "D-rcdEq".
    autorewrite with lr_rewrite in *.

    inverts WFA.
    inverts WFB.
    simp V.
    splits...
    case_if...

  - Case "D-rcdNeq".
    autorewrite with lr_rewrite in *.
    simp V.
    case_if...

  - Case "D-tvarL".
    forwards : rel_d_same RelD...
    forwards Dis : rel_d_tvar_disjoint RelD WFE...
    forwards Sub : mtsubst_sub H0...
    forwards Dis' : disjoint_sub Dis...

    lets (? & ?): sub_regular Sub.
    forwards : rel_d_tvar_mono RelD...
    forwards Mono : sty_mono_or_not (mtsubst_in_sty p B)...
    destruct Mono.
    apply mono_disjoint_value...
    eapply mono_poly_disjoint_value...
    eapply not_mono_is_poly...

  - Case "D-tvarR".
    forwards : rel_d_same RelD...
    forwards Dis : rel_d_tvar_disjoint RelD WFE...
    forwards Sub : mtsubst_sub...
    forwards : disjoint_sub Sub Dis...

    lets (? & ?): sub_regular Sub.
    forwards : rel_d_tvar_mono RelD...
    forwards Mono : sty_mono_or_not (mtsubst_in_sty p B)...
    destruct Mono.
    apply mono_disjoint_value...
    apply disjoint_symmetric...
    eapply V_sym...
    eapply mono_poly_disjoint_value...
    eapply not_mono_is_poly...

  - Case "D-forall".
    autorewrite with lr_rewrite in *.

    simp V.
    simpls.
    splits~.
    introv Dis WFC Mono.

    lets WFC' : swft_wft_nil WFC.
    lets Ty3 : typ_tapp Ty1 WFC'.
    lets Ty4 : typ_tapp Ty2 WFC'.
    lets (vv1 & ? & ?) : normalization Ty3.
    lets (vv2 & ? & ?) : normalization Ty4.

    inverts WFA as WFA1 WFB1.
    inverts WFB as WFA2 WFB2.

    pick_fresh  X.
    exists vv1 vv2.
    splits...
    forwards : WFB1 X...
    forwards : WFB2 X...


    assert (Eq1 : mtsubst_in_sty p (subst_sty_in_sty t X (open_sty_wrt_sty B1 (sty_var_f X))) = open_sty_wrt_sty (mtsubst_in_sty p B1) t).
    rewrite subst_sty_in_sty_open_sty_wrt_sty...
    erewrite mtsubst_open...
    simpl.
    case_if.
    rewrite subst_sty_in_sty_fresh_eq...
    asserts_rewrite (mtsubst_in_sty p t = t)...
    rewrite mtsubst_fresh...

    assert (Eq2 : (mtsubst_in_sty p (subst_sty_in_sty t X (open_sty_wrt_sty B2 (sty_var_f X))) = open_sty_wrt_sty (mtsubst_in_sty p B2) t)).
    rewrite subst_sty_in_sty_open_sty_wrt_sty...
    erewrite mtsubst_open...
    simpl.
    case_if.
    rewrite subst_sty_in_sty_fresh_eq...
    asserts_rewrite (mtsubst_in_sty p t = t)...
    rewrite mtsubst_fresh...

    forwards IMP : H0 X vv1 vv2 ([(X, t)] ++ p)...
    constructor; autorewrite with lr_rewrite...


    simpls.
    rewrite Eq1.
    autorewrite with lr_rewrite...

    simpls.
    rewrite Eq2.
    autorewrite with lr_rewrite...

    simpl in IMP.
    rewrite <- Eq1.
    rewrite <- Eq2...

Qed.




Lemma E_coercion1 : forall A1 A2 A0 c p d d' e1 e2,
    sub d' A1 A2 c ->
    same_stctx d d' ->
    swfte d ->
    rel_d d p ->
    E (mtsubst_in_sty p A1) A0 e1 e2 ->
    E (mtsubst_in_sty p A2) A0 (exp_capp c e1) e2.
Proof with simpl_env; eauto using subtype_well_type, mtsubst_swft, preservation_multi_step.

  introv Sub.
  gen A0 e1 e2 p d.
  induction Sub; introv SH Uniq PH EH.

  - Case "S-refl".
    destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & VH).

    splits...
    exists v1 v2.
    splits...

  - Case "S-trans".

    apply sub_change with (Δ' := d) in Sub1...
    apply sub_change with (Δ' := d) in Sub2...
    forwards : rel_d_same PH...
    forwards : mtsubst_sub p Sub1...
    forwards : mtsubst_sub p Sub2...

    specializes IHSub2 EH...
    specializes IHSub1 IHSub2...
    clear IHSub2.
    destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).
    lets (? & ?) : E_type IHSub1.
    apply E_starr1 with (e1' := exp_capp c1 (exp_capp c2 v1)) in IHSub1...
    destruct IHSub1 as (? & ? & ? & ? & v3 & v2' & ? & ? & ? & ? & VH).
    simplifier.
    forwards MSub1: mtsubst_sub Sub1...
    forwards MSub2: mtsubst_sub Sub2...
    eapply subtype_well_type in MSub1.
    eapply subtype_well_type in MSub2.

    splits; eauto.

    exists v3 v2.
    splits...


  - Case "S-top".

    destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).
    autorewrite with lr_rewrite...

    splits...

    exists exp_unit v2.
    splits...
    apply V_topl...

  - Case "S-bot".
    forwards (Ty & ?) : E_type EH.
    rewrite mtsubst_bot in Ty.
    simpls.
    eapply ty_absurd in Ty; inverts Ty.

  - Case "S-topArr".
    autorewrite with lr_rewrite in *.

    forwards : rel_d_same PH...

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    simpls.

    splits...

    exists (exp_capp co_topArr v1) v0.
    splits...

    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2.

    gen v0.

    induction A0; introv ? VH ?; simp V; splits...

    + SCase "A0 = A01 -> A02".

      introv VH' Ty1' Ty2'.
      simpls.

      lets (? & ?) : V_value VH'.
      simp V in VH.
      destructs VH.

      lets Temp : typ_app Ty4 Ty2'.
      lets (vv2 & ? & ?) : normalization Temp.
      forwards : unit_canonical Ty3...
      forwards : unit_canonical Ty1'...
      substs.

      exists exp_unit vv2.
      splits...

      apply V_topl...


    + SCase "A0 = A01 & A02".

      simpls.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Ty4...
      substs.

      inverts WFB.
      inverts Ty4 as Ty5 Ty6.

      forwards : IHA0_1 Ty5...
      apply V_topl...
      forwards : IHA0_2 Ty6...
      apply V_topl...


  - Case "S-topRcd".

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    autorewrite with lr_rewrite in *.
    simpls.

    forwards : rel_d_same PH...

    splits...

    exists v1 v0.
    splits...

    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2.

    gen v0.
    induction A0; introv ? VH ?; simp V; splits...

    + SCase "A0 = A01 & A02".

      autorewrite with lr_rewrite in *.
      simpls.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Ty4...
      substs.

      inverts WFB.
      inverts Ty4 as Ty5 Ty6.

      forwards : IHA0_1 Ty5...
      apply V_topl...
      forwards : IHA0_2 Ty6...
      apply V_topl...

    + SCase "A0 = {l : A0}".

      case_if...
      apply V_topl...

  - Case "S-topAll".

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    autorewrite with lr_rewrite in *.
    simpls.

    splits...

    exists (exp_capp co_topAll v1) v0.
    splits...

    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2.

    gen v0.
    induction A0; introv ? VH ?; simp V; splits...

    + SCase "A0 = A01 & A02".

      lets (v21 & v22 & ? & ? & ?): prod_canonical Ty4...
      substs.

      inverts WFB.
      inverts Ty4 as Ty5 Ty6.

      forwards : IHA0_1 Ty5...
      apply V_topl...
      forwards : IHA0_2 Ty6...
      apply V_topl...

    + SCase "A0 = forall".

      clear IHA0_1 IHA0_2.
      introv Dis SWF Mono.
      simp V in VH.
      inverts VH.
      forwards : unit_canonical Ty3...
      substs; simpls.

      forwards Ty5 : typ_tapp (|t|) Ty4...
      forwards (vv2 & ? & ?) : normalization Ty5...

      exists exp_unit vv2.
      splits...
      unfold open_sty_wrt_sty.
      simpls...
      eapply V_topl; eauto.
      rewrite trans_open_sty_rec.
      eapply preservation_multi_step...

  - Case "S-arr".

    apply sub_change with (Δ' := d) in Sub1...
    apply sub_change with (Δ' := d) in Sub2...
    forwards : rel_d_same PH...
    forwards Sub3 : mtsubst_sub p Sub1...
    forwards Sub4 : mtsubst_sub p Sub2...
    lets (? & ?) : sub_regular Sub1.
    lets (? & ?) : sub_regular Sub2.
    lets (? & ?) : sub_regular Sub3.
    lets (? & ?) : sub_regular Sub4.


    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    autorewrite with lr_rewrite in *.
    simpls.
    forwards MSub1: mtsubst_sub Sub1...
    forwards MSub2: mtsubst_sub Sub2...
    eapply subtype_well_type in MSub1.
    eapply subtype_well_type in MSub2.

    splits; simpls; eauto.


    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    exists (exp_capp (co_arr c1 c2 ) v1) v0.
    splits...

    clear Ty1 Ty2 Red1 Red2.

    gen v0.
    induction A0; introv ? VH ?; simp V; splits...
    simpls.

    + SCase "A0 = A01 -> A02".
      clear IHA0_1 IHA0_2.

      intros v v' VH' Ty1' Ty2'.
      autorewrite with lr_rewrite in *.
      simpls.

      inverts WFA.
      inverts WFB.
      lets (? & ?) : V_value VH.
      lets (? & ?) : V_value VH'.

      assert (EH' : E (mtsubst_in_sty p B1) A0_1 v v').
      splits...
      exists v v'.
      splits...
      apply V_sym...
      eapply IHSub1 in EH'...
      clear VH'.

      destruct EH' as (? & ? & ? & ? & v2 & v'' & ? & ? & ? & ? & VH').
      simplifier.

      simp V in VH.
      destruct VH as (? & ? & VH).

      apply V_sym in VH'...
      apply VH in VH'...
      destruct VH' as (v3 & v4 & ? & ? & ? & ? & VH').


      assert (EH' : E (mtsubst_in_sty p A2) A0_2 v3 v4).
      splits...
      exists v3 v4.
      splits...

      eapply IHSub2 in EH'...
      clear VH'.

      destruct EH' as (? & ? & ? & ? & v5 & v'' & ? & ? & ? & ? & VH').
      simplifier.

      exists v5 v4.
      splits...

      apply star_trans with (exp_capp c2 (exp_app v1 (exp_capp c1 v)))...


    + SCase "A0 = A01 & A02".
      clear IHSub1 IHSub2.
      autorewrite with lr_rewrite in *.
      simpls.

      lets (v21 & v22 & ? & ? & ?) : prod_canonical Ty4...
      substs.

      lets (? & VV) : V_value VH.
      inverts VV.
      inverts Ty4.
      inverts WFA.
      inverts WFB.


      apply V_andr in VH...
      destructs VH.

      exists v21 v22.
      splits...


  - Case "S-and".

    apply sub_change with (Δ' := d) in Sub1...
    apply sub_change with (Δ' := d) in Sub2...
    forwards : rel_d_same PH...
    forwards : mtsubst_sub p Sub1...
    forwards : mtsubst_sub p Sub2...
    autorewrite with lr_rewrite in *.

    specializes IHSub1 EH...
    specializes IHSub2 EH...

    destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & ?).
    apply E_starr1 with (e1' := exp_capp c1 v1) in IHSub1...
    apply E_starr1 with (e1' := exp_capp c2 v1) in IHSub2...
    destruct IHSub1 as (? & ? & ? & ? & v3 & v4 & ? & ? & ? & ? & ?).
    destruct IHSub2 as (? & ? & ? & ? & v5 & v6 & ? & ? & ? & ? & ?).
    simplifier.
    forwards MSub1: mtsubst_sub Sub1...
    forwards MSub2: mtsubst_sub Sub2...
    eapply subtype_well_type in MSub1.
    eapply subtype_well_type in MSub2.


    splits; simpls; eauto.

    exists (exp_pair v3 v5) v2.
    splits...
    apply star_trans with (b := exp_capp (co_pair c1 c2) v1)...
    apply V_andl...


  - Case "S-andl".

    destruct EH as (WF & ? & Ty1 & ? & v1 & v2 & Red1 & ? & ? & ? & VH).
    autorewrite with lr_rewrite in *.
    inverts WF.

    lets Ty4 : preservation_multi_step Ty1 Red1.
    lets~ (v11 & v12 & ? & ? & ?): prod_canonical Ty4.
    substs.

    simpls.
    inverts Ty4.

    apply V_andl in VH...
    destructs VH.

    splits...

    exists v11 v2.
    splits...


  - Case "S-andr".

    destruct EH as (WF & ? & Ty1 & ? & v1 & v2 & Red1 & ? & ? & ? & VH).
    autorewrite with lr_rewrite in *.
    inverts WF.

    lets Ty4 : preservation_multi_step Ty1 Red1.
    lets~ (v11 & v12 & ? & ? & ?): prod_canonical Ty4.
    substs.

    simpls.
    inverts Ty4.

    apply V_andl in VH...
    destructs VH.

    splits...

    exists v12 v2.
    splits...


  - Case "S-forall".

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & EH).
    autorewrite with lr_rewrite in *.

    assert (Sub' : sub DD (sty_all A1 B1) (sty_all A2 B2) (co_forall c))...
    apply sub_change with (Δ' := d) in Sub'...
    apply sub_change with (Δ' := d) in Sub...
    lets (WFC' & WFC) : sub_regular Sub'.

    forwards : rel_d_same PH...
    forwards Sub2 : mtsubst_sub p Sub'...
    lets (? & Temp) : sub_regular Sub2...
    autorewrite with lr_rewrite in *.

    forwards: subtype_well_type Sub2...

    splits; simpls; eauto.


    exists (exp_capp (co_forall c) v1) v0.
    splits...


    lets Ty5 : preservation_multi_step Ty1 Red1.
    lets Ty6 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2 Temp.
    gen v0.
    induction A0; introv ? VH ?; simp V; splits...
    simpls.

    + SCase "A0 = A01 & A02".
      simpls.
      lets~ (v01 & v02 & ? & ? & ?) : prod_canonical Ty6.
      substs.
      inverts Ty6.
      apply V_andr in VH...
      destruct VH as (VH1 & VH2).

      inverts WFA.
      inverts WFB.

      exists v01 v02.
      splits...

    + SCase "A0 = forall".

      clear IHA0_1 IHA0_2.
      introv Dis SWF Mono.
      simp V in VH.
      destruct VH as (? & ? & VH).

      inverts WFA.
      inverts WFB.
      inverts WFC.
      inverts WFC'.


      assert (Dis' : disjoint [] t (sty_and (mtsubst_in_sty p A1) A0_1)).
      assert (Temp : sub nil (sty_and (mtsubst_in_sty p A2) A0_1) (sty_and (mtsubst_in_sty p A1) A0_1) (co_pair (co_trans c' co_proj1) co_proj2))...
      constructor...
      eapply S_trans...
      eapply mtsubst_sub...
      eapply disjoint_sub...


      specializes VH Dis' SWF Mono.
      destruct VH as (vv1 & vv2 & ? & ? & ? & ? & VH).
      pick fresh X.


      assert (Eq1 : (mtsubst_in_sty p (subst_sty_in_sty t X (open_sty_wrt_sty B1 (sty_var_f X))) = open_sty_wrt_sty (mtsubst_in_sty p B1) t)).
      rewrite subst_sty_in_sty_open_sty_wrt_sty...
      erewrite mtsubst_open...
      simpl.
      case_if.
      rewrite subst_sty_in_sty_fresh_eq...
      replace (mtsubst_in_sty p t) with t...
      rewrite mtsubst_fresh...

      assert (Eq2 : (mtsubst_in_sty p (subst_sty_in_sty t X (open_sty_wrt_sty B2 (sty_var_f X))) = open_sty_wrt_sty (mtsubst_in_sty p B2) t)).
      rewrite subst_sty_in_sty_open_sty_wrt_sty...
      erewrite mtsubst_open...
      simpl.
      case_if.
      rewrite subst_sty_in_sty_fresh_eq...
      replace (mtsubst_in_sty p t) with t...
      rewrite mtsubst_fresh...

      assert (EH : E (open_sty_wrt_sty (mtsubst_in_sty p B1) t) (open_sty_wrt_sty A0_2 t) vv1 vv2).
      splits...
      rewrite subst_sty_in_sty_intro with (X1 := X)...
      apply swft_subst_sty with (B := mtsubst_in_sty p A1)...
      eapply mtsubst_notin...
      rewrite subst_sty_in_sty_intro with (X1 := X)...
      apply swft_subst_sty with (B := A0_1)...
      autorewrite with lr_rewrite...
      autorewrite with lr_rewrite...

      exists vv1 vv2.
      splits...
      rewrite <- Eq1 in EH.


      forwards IMP : H0 X ([(X, t)] ++ p) ([(X, sty_and A1 A0_1)] ++ d) EH...
      constructor...
      constructor...
      rewrite_env (d ++ nil).
      eapply swft_weaken_head...

      constructor...
      autorewrite with lr_rewrite.
      replace (mtsubst_in_sty p A0_1) with A0_1...
      rewrite mtsubst_fresh...
      simpls.
      rewrite Eq2 in IMP.
      clear EH VH.

      destruct IMP as (? & ? & ? & ? & vv3 & vv4 & ? & ? & ? & ? & VH).

      simplifier.

      exists vv3 vv2.
      apply sub_change with (Δ' := d) in Sub...
      splits...
      apply star_trans with (exp_capp c (exp_tapp v1 (| t |)))...


  - Case "S-rcd".

    autorewrite with lr_rewrite in *.

    apply sub_change with (Δ' := d) in Sub...
    forwards : rel_d_same PH...
    forwards Sub' : mtsubst_sub p Sub...
    lets (? & ?) : sub_regular Sub.
    lets (? & ?) : sub_regular Sub'.


    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    simpls...
    forwards: subtype_well_type Sub'.


    splits; simpls; eauto.

    assert (Ty : typ [] [] (exp_capp c v1) (| mtsubst_in_sty p B |))...
    lets (v2 & ? & ?) : normalization Ty...

    exists v2 v0.
    splits...

    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2.

    gen v0.
    induction A0; introv ? VH ?; simp V; splits...
    simpls.

    + SCase "A0 = A01 & A02".

      clear IHSub.
      simpls.

      lets (v21 & v22 & ? & ? & ?) : prod_canonical Ty4...
      substs.

      lets (? & VV) : V_value VH.
      inverts VV.
      inverts Ty4.
      inverts WFA.
      inverts WFB.

      apply V_andr in VH...
      destructs VH.

      exists v21 v22.
      splits...

    + SCase "A0 = {l : A0}".
      case_if...
      substs.
      inverts WFA.
      inverts WFB.
      simpls.

      simp V in VH.
      destruct VH as (? & ? & VH).
      case_if in VH.

      assert (EH : E (mtsubst_in_sty p A) A0 v1 v0).
      splits...
      exists v1 v0.
      splits...
      specializes IHSub EH...
      apply E_starr1 with (e1' := v2) in IHSub...
      destruct IHSub as (? & ? & ? & ? & v2' & v0' & ? & ? & ? & ? & ?).
      simplifier...


  - Case "S-distArr".

    autorewrite with lr_rewrite in *.


    forwards : rel_d_same PH...

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    simpls.

    inverts WFA as WFA1 WFA2.
    inverts WFA1.
    inverts WFA2.

    lets (? & ? & LC) : typing_regular Ty1.
    inverts LC as LC1 LC2.
    inverts LC1.
    inverts LC2.

    splits...
    simpls...


    exists (exp_capp co_distArr v1) v0.
    splits...

    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2.

    gen v0.

    induction A0; introv ? VH ?; simp V; splits...
    simpls.

    + SCase "A0 = A01 -> A02".
      clear IHA0_1 IHA0_2.

      introv VH' Ty1' Ty2'.
      simpls.

      simp V in VH.
      destruct VH as (? & ? & v11 & v12 & ? & VH1 & VH2).
      substs.

      simp V in VH1.
      destruct VH1 as (? & ? & VH1).
      specializes VH1 VH' Ty1' Ty2'...

      simp V in VH2.
      destruct VH2 as (? & ? & VH2).
      specializes VH2 VH' Ty1' Ty2'...

      destruct VH1 as (vv1 & vv3 & ? & ? & ? & ? & VH1).
      destruct VH2 as (vv2 & vv4 & ? & ? & ? & ? & VH2).
      simplifier.
      lets (? & ?) : V_value VH1.
      lets (? & ?) : V_value VH2.
      lets (? & ?) : V_value VH'.

      exists (exp_pair vv1 vv2) vv3.
      splits...
      apply star_trans with (exp_pair (exp_app v11 v1') (exp_app v12 v1'))...
      inverts Ty3.
      apply V_andl...


    + SCase "A0 = A01 & A02".

      autorewrite with lr_rewrite in *.
      simpls.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Ty4...
      substs.
      lets (v11 & v12 & ? & ? & ?) : prod_canonical Ty3...
      substs.

      inverts WFB.

      inverts Ty3 as Ty5 Ty6.
      inverts Ty4 as Ty7 Ty8.
      apply V_andl in VH...
      destruct VH as (VH1 & VH2).
      apply V_andr in VH1...
      destruct VH1 as (VH11 & VH12).
      apply V_andr in VH2...
      destruct VH2 as (VH21 & VH22).

      exists v21 v22.
      splits...
      apply IHA0_1...
      apply V_andl...
      apply IHA0_2...
      apply V_andl...


  - Case "S-distRcd".

    autorewrite with lr_rewrite in *.

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    autorewrite with lr_rewrite in Ty1.
    simpls.

    forwards : rel_d_same PH...
    inverts WFA as WFA1 WFA2.
    inverts WFA1.
    inverts WFA2.

    splits...
    simpls...

    exists v1 v0.
    splits...

    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.

    clear Ty1 Ty2 Red1 Red2.

    gen v0.
    induction A0; introv ? VH ?; simp V; splits...
    simpls.

    + SCase "A0 = A01 & A02".

      simpls.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Ty4...
      substs.

      inverts WFB.
      inverts Ty4.

      lets (v11 & v12 & ? & ? & ?): prod_canonical Ty3...
      substs.

      inverts Ty3.
      apply V_andr in VH...
      destructs VH.


      exists v21 v22.
      splits...

      autorewrite with lr_rewrite; simpls...


    + SCase "A0 = {l : A0}".

      case_if...
      simpls.
      lets (v11 & v12 & ? & ? & ?) : prod_canonical Ty3...
      substs.
      inverts Ty3.
      apply V_andl in VH...
      destruct VH as (VH1 & VH2).

      simp V in VH1.
      destruct VH1 as (? & ? & VH1).
      case_if in VH1.

      simp V in VH2.
      destruct VH2 as (? & ? & VH2).
      case_if in VH2.
      splits...

  - Case "S-distPoly".

    autorewrite with lr_rewrite in *.

    destruct EH as (WFA & WFB & Ty1 & Ty2 & v1 & v0 & Red1 & Red2 & ? & ? & ?).
    simpls.

    forwards : rel_d_same PH...
    inverts WFA as WFA1 WFA2.
    inverts WFA1.
    inverts WFA2.
    lets (? & ? & WW): typing_regular Ty1...
    inverts WW as WW1 WW2.
    inverts WW1.
    inverts WW2.

    splits; auto.
    (* swft case *)
    pick fresh X and apply swft_all...
    unfold open_sty_wrt_sty.
    simpl...
    (* typ case *)
    simpl.
    econstructor...
    pick fresh X and apply wft_all...
    unfold open_ty_wrt_ty.
    simpls...


    (* hard case *)
    lets Ty3 : preservation_multi_step Ty1 Red1.
    lets Ty4 : preservation_multi_step Ty2 Red2.
    lets (v11 & v12 & ? & ? & ?): prod_canonical Ty3...
    substs.
    inverts Ty3 as Ty31 Ty32.

    exists (exp_capp co_distPoly (exp_pair v11 v12)) v0.
    splits...

    clear Ty1 Ty2 Red1 Red2.

    gen v0.
    induction A0; introv ? VH ?; simp V; splits...
    simpls.

    + SCase "A0 = A01 & A02".

      simpls.
      lets (v21 & v22 & ? & ? & ?): prod_canonical Ty4...
      substs.

      inverts WFB.
      inverts Ty4.

      apply V_andr in VH...
      destructs VH.

      exists v21 v22.
      splits...
      simpls...


    + SCase "A0 = forall".

      clear IHA0_1 IHA0_2.
      introv Dis SWF Mono.
      simp V in VH.
      destruct VH as (? & ? & ? & ? & Eq & VH1 & VH2).
      symmetry in Eq.
      inverts Eq.

      simp V in VH1.
      destruct VH1 as (? & ? & VH1).
      specializes VH1 Dis SWF Mono.
      simp V in VH2.
      destruct VH2 as (? & ? & VH2).
      specializes VH2 Dis SWF Mono.

      destruct VH1 as (vv1 & vv2 & ? & ? & ? & ? & VH1).
      destruct VH2 as (vv3 & vv4 & ? & ? & ? & ? & VH2).
      simplifier.

      exists  (exp_pair vv1 vv3) vv2.
      splits...

      apply star_trans with (b := exp_pair (exp_tapp v11 (|t|)) (exp_tapp v12 (|t|))).
      econstructor...
      eapply multi_red_pair...


      unfold open_sty_wrt_sty.
      simpls...
      eapply V_andl...
      autorewrite with lr_rewrite...
      autorewrite with lr_rewrite...


      (* WTF *)
      Unshelve.
      exact (dom DD).
      exact (dom DD).
Qed.


(* Lemma sub_strengthen_push : forall X A B C c D, *)
(*   sub ((X, A) :: D) B C c -> *)
(*   swfte ([(X, A)] ++ D) -> *)
(*   X `notin` fv_sty_in_sty B -> *)
(*   X `notin` fv_sty_in_sty C -> *)
(*   sub D B C c. *)
(* Proof with auto. *)
(*   introv SUB WFTE NOTINB NOTINC. *)
(*   inversions WFTE. *)
(*   assert (I1: sub (nil ++ (X, A) :: D) B C c) by (simpl_alist; auto). *)
(*   apply sub_subst with (P:=A) in I1... *)
(*   simpl_alist in I1. *)
(*   rewrite subst_sty_in_sty_fresh_eq_mutual in I1... *)
(*   rewrite subst_sty_in_sty_fresh_eq_mutual in I1... *)
(* Qed. *)

(* Lemma swfte_tvar_dom : forall X X0 D A, *)
(*     swfte D -> *)
(*     X `notin` dom D -> *)
(*     binds X0 A D -> *)
(*     X `notin` fv_sty_in_sty A. *)
(* Proof with eauto. *)
(*   introv H. *)
(*   gen X A. *)
(*   induction H; introv B C. *)
(*   analyze_binds C. *)
(*   analyze_binds C. *)
(*   apply swft_tvar with DD... *)
(* Qed. *)




Lemma rel_g_well_type_value : forall g1 g2 Γ p,
    rel_g Γ p g1 g2 ->
    all_value g1 /\ all_value g2.
Proof with eauto.
  introv GG.
  induction GG; splits...

  lets (? & ?) : V_value H3.
  inverts IHGG.

  eapply all_cons...

  lets (? & ?) : V_value H3.
  inverts IHGG.

  eapply all_cons...

Qed.



Lemma msubst_rel_typ : forall Γ p g1 g2 t T,
    rel_g Γ p g1 g2 ->
    typ nil (∥ map (mtsubst_in_sty p) Γ ∥) t T ->
    typ nil nil (msubst_in_exp g1 t) T /\
    typ nil nil (msubst_in_exp g2 t) T.
Proof with eauto.
  introv RelG.
  gen t T.
  induction RelG; introv Typ; simpls...

  splits.

  eapply IHRelG...
  rewrite_env (nil ++ (∥ map (mtsubst_in_sty p) G ∥)).
  apply typing_through_subst_exp_in_exp with (U := (| mtsubst_in_sty p A |))...
  rewrite_env (nil ++ (∥ map (mtsubst_in_sty p) G ∥) ++ nil).
  eapply typing_var_weakening...
  simpl_env.
  lets (? & Wfe & ?): typing_regular Typ...
  inverts Wfe...

  eapply IHRelG...
  rewrite_env (nil ++ (∥ map (mtsubst_in_sty p) G ∥)).
  eapply typing_through_subst_exp_in_exp with (U := (| mtsubst_in_sty p A |))...

  rewrite_env (nil ++ (∥ map (mtsubst_in_sty p) G ∥) ++ nil).
  eapply typing_var_weakening...
  simpl_env.
  lets (? & Wfe & ?): typing_regular Typ...
  inverts Wfe...
Qed.


Lemma subst_close : forall p g1 g2 Δ Γ t B,
    rel_d Δ p ->
    rel_g Γ p g1 g2 ->
    typ (map (const tt) Δ) (∥ Γ ∥) t (| B |) ->
    typ nil nil (msubst_in_exp g1 (mtsubst_in_exp p t)) (|mtsubst_in_sty p B|) /\
    typ nil nil (msubst_in_exp g2 (mtsubst_in_exp p t)) (|mtsubst_in_sty p B|).
Proof with eauto.

  introv RelD RelG Typ.
  forwards (? & ?): rel_d_uniq RelD.
  forwards: rel_d_same RelD...
  lets (? & ?): rel_g_well_type_value RelG.
  forwards Ty : mtsubst_typ p Typ...
  eapply msubst_rel_typ...
Qed.




(* ********************************************************************** *)
(** * Compatibility *)


Lemma top_compatibility : forall D G A e,
    typ (map (const tt) D) (∥ G ∥) e (| A |) ->
    swft D A ->
    E_open D G exp_unit e sty_top A.
Proof with eauto using mtsubst_swft.
  introv Ty Wft.
  splits; simpls...
  introv RelD RelG.
  forwards (? & ?): rel_d_uniq RelD.
  forwards : rel_d_same RelD...
  forwards (Ty1 & Ty2) : subst_close Ty...
  autorewrite with lr_rewrite.
  lets (v & ? & ?) : normalization Ty2.
  splits...
  exists exp_unit v.
  splits...
  apply V_topl...
  eapply preservation_multi_step...
Qed.



Lemma lit_compatibility : forall D G i,
    uniq D ->
    swfe D G ->
    E_open D G (exp_lit i) (exp_lit i) sty_nat sty_nat.
Proof with eauto using swfe_wfe.
  introv Uniq Wfe.
  splits; simpls...
  introv RelD RelG.
  autorewrite with lr_rewrite.
  splits...
  exists (exp_lit i) (exp_lit i).
  splits...
  simp V...
Qed.



Lemma var_compatibility : forall D G x A,
    swfe D G ->
    swfte D ->
    binds x A G ->
    E_open D G (exp_var_f x) (exp_var_f x) A A.
Proof with eauto using swfe_wfe, mtsubst_swft, swfe_notin.
  introv Wft.
  gen x A.
  induction Wft; introv Wfte Bind; simpls...
  analyze_binds Bind.

  analyze_binds_uniq Bind.
  - splits; simpls...
    constructor; constructor...
    constructor; constructor...
    introv RelD RelG.
    forwards (? & ?): rel_d_uniq RelD.
    forwards : rel_d_same RelD...
    inverts RelG as ?  ?  ?  ?  ? VH.
    lets (? & ?) : V_value VH.
    asserts_rewrite ((mtsubst_in_exp p x) = x)...
    apply mtsubst_var_notin...
    asserts_rewrite (dom p [=] dom DD)...
    apply same_stctx_dom...

    repeat rewrite Eq.
    simpls...
    case_if...
    asserts_rewrite ((msubst_in_exp g0 v1) = v1).
    eapply msubst_fresh...
    eapply closed_no_var...

    asserts_rewrite ((msubst_in_exp g3 v2) = v2).
    eapply msubst_fresh...
    eapply closed_no_var...
    splits...
    exists v1 v2.
    splits...

  - assert (~ x0 = x)...
    forwards Imp : IHWft BindsTac...
    splits; simpls...
    constructor...
    constructor...
    constructor...
    constructor...
    introv RelD RelG.
    forwards (? & ?): rel_d_uniq RelD.
    forwards Same : rel_d_same RelD...
    inverts RelG as ? RelG.
    destruct Imp as (? & ? & ? & ? & VH).
    specializes VH RelD RelG.
    replace (mtsubst_in_exp p (exp_var_f x0)) with (exp_var_f x0) in *.
    simpls...
    case_if...

    rewrite mtsubst_var_notin...
    asserts_rewrite (dom p [=] dom DD)...
    apply same_stctx_dom...
Qed.



Lemma rel_g_weaken : forall G p g1 g2 X t,
  rel_g G p g1 g2 ->
  X `notin` dom p ->
  rel_g G ([(X, t)] ++ p) g1 g2.
Proof with eauto.
  introv RelG.
  gen X t.
  induction RelG; introv Uniq; simpls...
  assert (X `notin` fv_sty_in_sty A). fsetdec.
  constructor; simpls...
  fsetdec.
  rewrite subst_sty_in_sty_fresh_eq...
  rewrite subst_sty_in_sty_fresh_eq...
  rewrite subst_sty_in_sty_fresh_eq...
Qed.




Lemma tabs_compatibility : forall D G X A B1 B2 e1 e2,
    X `notin` dom G ->
    X `notin` dom D ->
    X `notin` fv_sty_in_sty B1 ->
    X `notin` fv_sty_in_sty B2 ->
    X `notin` fv_ty_in_exp e1 ->
    X `notin` fv_ty_in_exp e2 ->
    swfte D ->
    swfe D G ->
    swft D A ->
    E_open ([(X , A)] ++ D) G (open_exp_wrt_ty e1 (ty_var_f X)) (open_exp_wrt_ty e2 (ty_var_f X)) ( open_sty_wrt_sty B1 (sty_var_f X) ) ( open_sty_wrt_sty B2 (sty_var_f X) ) ->
    E_open D G (exp_tabs e1) (exp_tabs e2) (sty_all A B1) (sty_all A B2).
Proof with eauto using mtsubst_swft, notin_sty_ty, swfe_wfe.

  introv ? ? ? ? ? ? Swfte Swfe Wft EH.

  destruct EH as (WF1 & WF2 & ? & ? & EH).

  assert (swft D (sty_all A B1)).
  pick fresh Y and apply swft_all...
  eapply swft_renaming...
  assert (swft D (sty_all A B2)).
  pick fresh Y and apply swft_all...
  eapply swft_renaming...

  assert (Ty1: typ (map (const ()) D) (∥ G ∥) (exp_tabs e1) ((| sty_all A  B1 |))).
  simpl.
  pick fresh Y and apply typ_tabs...
  simpls...
  autorewrite with lr_rewrite in *.
  apply typing_tvar_rename with (X := X)...

  assert (Ty2: typ (map (const ()) D) (∥ G ∥) (exp_tabs e2) (|sty_all A B2 |)).
  simpl.
  pick fresh Y and apply typ_tabs...
  simpls...
  autorewrite with lr_rewrite in *.
  apply typing_tvar_rename with (X := X)...

  splits...

  introv RelD RelG.
  lets (Ty4 & ?) : subst_close RelD RelG Ty1...
  lets (? & Ty5) : subst_close RelD RelG Ty2...

  forwards (? & ?): rel_d_uniq RelD.
  forwards: rel_d_same RelD...

  splits...
  autorewrite with lr_rewrite in *.
  simpls.


  exists (exp_tabs (msubst_in_exp g1 (mtsubst_in_exp p e1)))     (exp_tabs (msubst_in_exp g2 (mtsubst_in_exp p e2))).
  splits...
  simp V.
  splits...
  introv Dis ? ?.
  apply disjoint_and in Dis...
  destruct Dis.

  forwards (? & ?): rel_g_well_type_value RelG.

  assert (RelD' : rel_d ([(X, A)] ++ D) ([(X, t)] ++ p)).
  constructor...
  assert (RelG' : rel_g G ([(X, t)] ++ p) g1 g2).
  apply rel_g_weaken...
  asserts_rewrite (dom p [=] dom D)...
  apply same_stctx_dom...

  specializes EH RelD' RelG'.
  simpls.

  rewrite <- subst_sty_in_sty_intro with (X1 := X) in EH...
  rewrite <- subst_sty_in_sty_intro with (X1 := X) in EH...
  autorewrite with lr_rewrite in *...
  replace (mtsubst_in_sty p t) with t in EH...
  rewrite <- subst_ty_in_exp_intro with (X1 := X) in EH...
  rewrite <- subst_ty_in_exp_intro with (X1 := X) in EH...
  erewrite mtsubst_open in EH...
  erewrite mtsubst_open in EH...
  erewrite mtsubst_ty_open in EH...
  erewrite mtsubst_ty_open in EH...
  autorewrite with lr_rewrite in EH...

  replace (mtsubst_in_sty p t) with t in EH...
  apply E_star1 with (e1 := exp_tapp (exp_tabs (msubst_in_exp g1 (mtsubst_in_exp p e1))) (| t |)) in EH...
  apply E_star2 with (e2 := exp_tapp (exp_tabs (msubst_in_exp g2 (mtsubst_in_exp p e2))) (| t |)) in EH...

  destruct EH as (WFA & WFB & ? & ? & v1 & v0 & Red1 & Red2 & ? & ? & VH).

  exists v1 v0.
  splits...

  autorewrite with lr_rewrite...
  autorewrite with lr_rewrite...

  rewrite mtsubst_fresh...
  rewrite mtsubst_fresh...

Qed.




Lemma record_compatibility : forall D G l A1 A2 e1 e2,
    E_open D G e1 e2 A1 A2 <->
    E_open D G e1 e2 (sty_rcd l A1) (sty_rcd l A2).
Proof with eauto.
  intros.

  splits.

  - Case "->".
    introv H.
    destruct H as (? & ? & ? & ? & EH).

    splits...
    introv RelD RelG.
    specializes EH RelD RelG.
    autorewrite with lr_rewrite in *.
    destruct EH as (? & ? & ? & ? & v1 & v2 & ? & ? & ? & ? & VH).
    splits...
    exists v1 v2.
    splits...
    simp V.
    splits...
    case_if...

  - Case "<-".
    introv H.
    destruct H as (WF1 & WF2 & ? & ? & EH).
    inverts WF1.
    inverts WF2.

    splits...
    introv RelD RelG.
    specializes EH RelD RelG.
    destruct EH as (WF1 & WF2 & ? & ? & v1 & v2 & ? & ? & ? & ? & VH).
    autorewrite with lr_rewrite in *.
    inverts WF1.
    inverts WF2.
    splits...
    exists v1 v2.
    splits...
    simp V in VH.
    case_if.
    destructs VH...

Qed.




Lemma tapp_compatibility : forall D G A B1 B2 t e1 e2,
    E_open D G e1 e2 (sty_all A B1) (sty_all A B2) ->
    disjoint D t A ->
    mono t ->
    swfte D ->
    swft D t ->
    E_open D G (exp_tapp e1 (| t |) ) (exp_tapp e2 (| t |)) (open_sty_wrt_sty B1 t) (open_sty_wrt_sty B2 t).
Proof with eauto using swft_open.
  introv EH Dis Mono WFS WFT.

  destruct EH as (WF & ? & ? & ? & EH).

  inverts WF.

  splits...
  autorewrite with lr_rewrite...
  autorewrite with lr_rewrite...

  introv RelD RelG.
  specializes EH RelD RelG.


  forwards: rel_d_same RelD...

  destruct EH as (? & ? & Ty1 & Ty2 & v1 & v2 & Red1 & Red2 & ? & ? & VH).
  autorewrite with lr_rewrite in *...

  assert (swft nil (mtsubst_in_sty p t)).
  eapply mtsubst_swft...

  assert (wft [] (| mtsubst_in_sty p t |)).
  apply swft_wft_nil...


  lets Ty3 : preservation_multi_step Ty1 Red1.
  lets Ty4 : preservation_multi_step Ty2 Red2.
  simpls.
  forwards Ty5 : typ_tapp (| mtsubst_in_sty p t |) Ty3...
  forwards Ty6 : typ_tapp (| mtsubst_in_sty p t |) Ty4...

  lets (v1' & ? & ?) : normalization Ty5.
  lets (v2' & ? & ?) : normalization Ty6.


  simp V in VH.
  destruct VH as (? & ? & VH).



  forwards : mtsubst_disjoint p Dis...

  forwards Imp : VH (mtsubst_in_sty p t)...
  eapply mtsubst_mono...

  destruct Imp as (vv1 & vv2 & ? & ? & ? & ? & Imp).
  simplifier.

  splits...
  erewrite mtsubst_open...
  autorewrite with lr_rewrite...
  erewrite mtsubst_open...
  autorewrite with lr_rewrite...

  exists v1' v2'.
  splits...
  erewrite mtsubst_open...
  erewrite mtsubst_open...

Qed.

Lemma tapp_compatibility' : forall D G A1 A2 B1 B2 t e1 e2,
    E_open D G e1 e2 (sty_all A1 B1) (sty_all A2 B2) ->
    disjoint D t A1 ->
    disjoint D t A2 ->
    mono t ->
    swfte D ->
    swft D t ->
    E_open D G (exp_tapp e1 (| t |) ) (exp_tapp e2 (| t |)) (open_sty_wrt_sty B1 t) (open_sty_wrt_sty B2 t).
Proof with eauto using swft_open.
  introv EH Dis1 Dis2 Mono WFS WFT.

  destruct EH as (WF & ? & ? & ? & EH).

  inverts WF.

  splits...
  autorewrite with lr_rewrite...
  autorewrite with lr_rewrite...

  introv RelD RelG.
  specializes EH RelD RelG.


  forwards: rel_d_same RelD...

  destruct EH as (? & ? & Ty1 & Ty2 & v1 & v2 & Red1 & Red2 & ? & ? & VH).
  autorewrite with lr_rewrite in *...

  assert (swft nil (mtsubst_in_sty p t)).
  eapply mtsubst_swft...

  assert (wft [] (| mtsubst_in_sty p t |)).
  apply swft_wft_nil...


  lets Ty3 : preservation_multi_step Ty1 Red1.
  lets Ty4 : preservation_multi_step Ty2 Red2.
  simpls.
  forwards Ty5 : typ_tapp (| mtsubst_in_sty p t |) Ty3...
  forwards Ty6 : typ_tapp (| mtsubst_in_sty p t |) Ty4...

  lets (v1' & ? & ?) : normalization Ty5.
  lets (v2' & ? & ?) : normalization Ty6.


  simp V in VH.
  destruct VH as (? & ? & VH).



  forwards : mtsubst_disjoint p Dis1...
  forwards : mtsubst_disjoint p Dis2...

  forwards Imp : VH (mtsubst_in_sty p t)...
  eapply mtsubst_mono...

  destruct Imp as (vv1 & vv2 & ? & ? & ? & ? & Imp).
  simplifier.

  splits...
  erewrite mtsubst_open...
  autorewrite with lr_rewrite...
  erewrite mtsubst_open...
  autorewrite with lr_rewrite...

  exists v1' v2'.
  splits...
  erewrite mtsubst_open...
  erewrite mtsubst_open...

Qed.

Lemma app_compatibility : forall D G e1 e2 e1' e2' A1 A2 A2',
    swfte D ->
    E_open D G e1 e2 (sty_arrow A1 A2) (sty_arrow A1 A2') ->
    E_open D G e1' e2' A1 A1 ->
    E_open D G (exp_app e1 e1') (exp_app e2 e2') A2 A2'.
Proof with eauto.

  introv WFE EH1 EH2 .

  destruct EH1 as (WF1 & WF2 & ? & ? & EH1).
  destruct EH2 as (WF3 & WF4 & ? & ? & EH2).

  inverts WF1.
  inverts WF2.
  simpls.

  splits...

  introv RelD RelG.
  specializes EH1 RelD RelG.
  specializes EH2 RelD RelG.

  autorewrite with lr_rewrite in *.

  forwards: rel_d_same RelD...


  destruct EH1 as (? & ? & Ty1 & Ty2 & v1 & v2 & Red1 & Red2 & ? & ? & VH1).
  destruct EH2 as (? & ? & Ty3 & Ty4 & v3 & v4 & Red3 & Red4 & ? & ? & VH2).

  simpls.

  lets Ty5 : typ_app Ty1 Ty3.
  lets Ty6 : typ_app Ty2 Ty4.
  lets Ty7 : preservation_multi_step Ty3 Red3.
  lets Ty8 : preservation_multi_step Ty4 Red4.

  simp V in VH1.
  destruct VH1 as (? & ? & VH1).
  apply V_sym in VH2...
  specializes VH1 VH2 Ty7 Ty8.
  destruct VH1 as (vv1 & vv2 & ? & ? & ? & ? & VH).

  splits...


  exists vv1 vv2.
  splits...

  apply star_trans with (exp_app v1 v3)...
  eapply multi_red_app...

  apply star_trans with (exp_app v2 v4)...
  eapply multi_red_app...

Qed.

Lemma app_compatibility' : forall D G e1 e2 e1' e2' A1 A1' A2 A2',
    swfte D ->
    E_open D G e1 e2 (sty_arrow A1 A2) (sty_arrow A1' A2') ->
    E_open D G e1' e2' A1 A1' ->
    E_open D G (exp_app e1 e1') (exp_app e2 e2') A2 A2'.
Proof with eauto.

  introv WFE EH1 EH2 .

  destruct EH1 as (WF1 & WF2 & ? & ? & EH1).
  destruct EH2 as (WF3 & WF4 & ? & ? & EH2).

  inverts WF1.
  inverts WF2.
  simpls.

  splits...

  introv RelD RelG.
  specializes EH1 RelD RelG.
  specializes EH2 RelD RelG.

  autorewrite with lr_rewrite in *.

  forwards: rel_d_same RelD...


  destruct EH1 as (? & ? & Ty1 & Ty2 & v1 & v2 & Red1 & Red2 & ? & ? & VH1).
  destruct EH2 as (? & ? & Ty3 & Ty4 & v3 & v4 & Red3 & Red4 & ? & ? & VH2).

  simpls.

  lets Ty5 : typ_app Ty1 Ty3.
  lets Ty6 : typ_app Ty2 Ty4.
  lets Ty7 : preservation_multi_step Ty3 Red3.
  lets Ty8 : preservation_multi_step Ty4 Red4.

  simp V in VH1.
  destruct VH1 as (? & ? & VH1).
  apply V_sym in VH2...
  specializes VH1 VH2 Ty7 Ty8.
  destruct VH1 as (vv1 & vv2 & ? & ? & ? & ? & VH).

  splits...


  exists vv1 vv2.
  splits...

  apply star_trans with (exp_app v1 v3)...
  eapply multi_red_app...

  apply star_trans with (exp_app v2 v4)...
  eapply multi_red_app...

Qed.


Lemma abs_compatibility : forall D G x A B1 B2 e1 e2,
    x `notin` dom G ->
    x `notin` dom D ->
    x `notin` fv_exp_in_exp e1 ->
    x `notin` fv_exp_in_exp e2 ->
    uniq D ->
    swft D A ->
    E_open D ([(x , A)] ++ G) (open_exp_wrt_exp e1 (exp_var_f x)) (open_exp_wrt_exp e2 (exp_var_f x)) B1 B2 ->
    E_open D G (exp_abs e1) (exp_abs e2) (sty_arrow A B1) (sty_arrow A B2).
Proof with eauto using mtsubst_swft, swfe_notin.
  introv ? ? ? ? Uniq WFT EH.

  destruct EH as (WF1 & WF2 & ? & ? & EH).

  assert (Ty1 : typ (map (const tt) D) (∥ G ∥) (exp_abs e1) (| sty_arrow A B1 |)).
  simpls.
  pick fresh y and apply typ_abs...
  apply typing_rename with (x := x)...

  assert (Ty2 : typ (map (const tt) D) (∥ G ∥) (exp_abs e2) (| sty_arrow A B2 |)).
  simpls.
  pick fresh y and apply typ_abs...
  apply typing_rename with (x := x)...

  splits...

  introv RelD RelG.

  forwards: rel_d_same RelD...
  lets (? & ?): rel_g_well_type_value RelG.

  lets (Ty4 & ?) : subst_close RelD RelG Ty1...
  lets (? & Ty5) : subst_close RelD RelG Ty2...

  autorewrite with lr_rewrite in *.

  splits...


  exists (exp_abs (msubst_in_exp g1 (mtsubst_in_exp p e1))) (exp_abs (msubst_in_exp g2 (mtsubst_in_exp p e2))).
  splits...

  simp V.
  splits...
  introv VH Ty6 Ty7.



  lets (? & ?): V_value VH.
  lets (? & ?): closed_no_var Ty6.
  lets (? & ?): closed_no_var Ty7.

  apply V_sym in VH...
  assert (RelG' : rel_g ([(x, A)] ++ G) p ([(x, v1')] ++ g1) ([(x, v2')] ++ g2)).
  constructor...
  lets : fv_sty_dom WFT.
  asserts_rewrite (dom p [=] dom D)...
  apply same_stctx_dom...


  specializes EH RelD RelG'.
  clear RelG'.
  simpls.
  rewrite mtsubst_in_exp_subst in EH...
  rewrite mtsubst_in_exp_subst in EH...
  rewrite <- subst_exp_in_exp_intro in EH...
  rewrite <- subst_exp_in_exp_intro in EH...
  rewrite mtsubst_exp_open in EH...
  rewrite mtsubst_exp_open in EH...
  rewrite msubst_open in EH...
  rewrite msubst_open in EH...
  replace (mtsubst_in_exp p v2') with v2' in EH...
  replace (mtsubst_in_exp p v1') with v1' in EH...
  replace (msubst_in_exp g1 v1') with v1' in EH...
  replace (msubst_in_exp g2 v2') with v2' in EH...

  lets Ty4' : typ_app Ty4 Ty6.
  lets Ty5' : typ_app Ty5 Ty7.

  lets (vv1 & ? & ?) : normalization Ty4'.
  lets (vv2 & ? & ?) : normalization Ty5'.
  clear Ty4' Ty5'.

  apply E_conv1 with (e1 :=  exp_app (exp_abs (msubst_in_exp g1 (mtsubst_in_exp p e1))) v1') in EH...
  apply E_conv2 with (e2 :=  exp_app (exp_abs (msubst_in_exp g2 (mtsubst_in_exp p e2))) v2') in EH...

  destruct EH as (? & ? & ? & ? & vv1' & vv2' & ? & ? & ? & ? & VH').
  simplifier.

  exists vv1' vv2'.
  splits...

  rewrite msubst_fresh...
  rewrite msubst_fresh...
  rewrite mtsubst_exp_fresh...
  rewrite mtsubst_exp_fresh...
Qed.
