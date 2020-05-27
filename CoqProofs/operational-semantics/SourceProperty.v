
Require Import Infrastructure.



(* ********************************************************************** *)
(** * Soundness of subtyping *)

Lemma subtype_well_type : forall Δ A B co,
    sub Δ A B co ->
    ctyp (map (const tt) Δ) co (| A |) (| B |).
Proof with eauto using swft_type, lc_sty_ty.
  introv Co.
  induction* Co; simpls...

  pick fresh X and apply ctyp_forall...
  lets Tmp : H0 X.
  autorewrite with lr_rewrite in *.
  apply Tmp...

  constructor...
  pick fresh X and apply wft_all...
  forwards : H0...
  forwards : H1...
  eapply swft_wft in H0...
  eapply swft_wft in H1...
  rewrite trans_open_sty in H0.
  rewrite trans_open_sty in H1.
  simpls...

  pick fresh X and apply wft_all...
  forwards : H0...
  forwards : H1...
  eapply swft_wft in H0...
  eapply swft_wft in H1...
  rewrite trans_open_sty in H0.
  rewrite trans_open_sty in H1.
  simpls...

Qed.


(* ********************************************************************** *)
(** * Soundness of typing *)

Lemma elaboration_well_type : forall Δ Γ E A d t,
    swfte Δ ->
    has_type Δ Γ E d A t ->
    typ (map (const tt) Δ)  (∥ Γ ∥) t (| A |).
Proof with eauto using swfe_wfe, swft_wft, subtype_well_type.
  introv W H.
  induction H; simpls...

  - Case "typ_tabs".
    pick fresh X and apply typ_tabs...

    rewrite_env ((X, const tt A) :: map (const tt) DD).
    assert (Eq : ty_var_f X = | sty_var_f X |) by reflexivity.
    rewrite Eq.
    rewrite <- trans_open_sty.
    apply (H1 X)...
    constructor...

  - Case "typ_tapp".
    forwards (? & ?) : disjoint_regular H1.
    rewrite trans_open_sty...

  - Case "typ_abs".
    pick fresh x and apply typ_abs...
    apply (H1 x)...
Qed.

(* ********************************************************************** *)
(** * Inference uniqueness *)

Lemma inference_unique : forall Δ Γ E A1 A2 t1 t2,
    has_type Δ Γ E Inf A1 t1 ->
    has_type Δ Γ E Inf A2 t2 ->
    A1 = A2.
Proof with eauto.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 t2.
  induction Ty1; introv Eq Ty2; try solve [inverts~ Eq; inverts~ Ty2].

  - Case "typ_var".
    inverts Ty2 as _ _ Bind.
    forwards ~ : binds_unique H1 Bind.
  - Case "typ_app".
    inverts Ty2.
    forwards : IHTy1_1...
    inverts~ H.
  - Case "typ_and".
    inverts Ty2.
    forwards : IHTy1_1...
    forwards : IHTy1_2...
    substs...
  - Case "typ_all".
    inverts Ty2 as _ IH.

    pick_fresh X.
    forwards~ IMP : IH.
    forwards~ IMP2 : H1 IMP.
    lets : open_sty_wrt_sty_inj IMP2...
    substs...


  - Case "typ_tapp".
    inverts Ty2 as IMP.
    forwards~ IMP2 : IHTy1 IMP.
    inverts IMP2...

  - Case "typ_rcd".
    inverts Ty2.
    forwards : IHTy1...
    substs...

  - Case "typ_proj".
    inverts Ty2.
    forwards IMP : IHTy1...
    inverts~ IMP.
Qed.
