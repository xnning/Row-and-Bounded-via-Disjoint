
Require Import Infrastructure.
Require Import SourceProperty.
Require Import LR.
Require Import Compatibility.


(* ********************************************************************** *)
(** * Fundamental property *)

Theorem fundamental_prop:  forall Δ Γ E A e e' dir,
    has_type Δ Γ E dir A e ->
    has_type Δ Γ E dir A e' ->
    E_open Δ Γ e e' A A.
Proof with eauto using swft_wft, swfe_wfe, elaboration_well_type, subtype_well_type, swft_from_swfe, swfe_notin.
  introv Ty1. gen e'.
  induction Ty1; introv Ty2.

  - Case "top".

    apply top_compatibility...

  - Case "lit".
    inverts Ty2.
    apply lit_compatibility...

  - Case "var".
    inverts Ty2.
    apply var_compatibility...

  - Case "app".
    inverts Ty2 as.
    introv Ty1 Ty2.
    lets H: inference_unique Ty1_1 Ty1.
    inverts H.
    forwards : IHTy1_1...
    forwards : IHTy1_2...
    eapply app_compatibility...

  - Case "merge".
    inverts Ty2 as Ty1 Ty2 ?.
    forwards : IHTy1_1 Ty1.
    forwards : IHTy1_2 Ty2.
    eapply pair_compatibility...

  - Case "anno".
    inverts Ty2.
    eapply IHTy1...

  - Case "tabs".
    inverts Ty2.
    pick_fresh X.
    eapply tabs_compatibility...
    forwards : H0...
    assert (Wfte : swfte ([(X, A)] ++ DD))...
    inverts Wfte...

  - Case "tapp".
    inverts Ty2 as TT ? Dis ?.
    forwards Eq : inference_unique Ty1 TT.
    forwards (? & ?) : disjoint_regular Dis.
    inverts Eq.
    forwards : IHTy1...
    eapply tapp_compatibility...

  - Case "rcd".
    inverts Ty2.
    forwards : IHTy1...
    apply record_compatibility...

  - Case "proj".
    inverts Ty2.
    forwards : IHTy1...
    apply record_compatibility in H...

  - Case "abs".
    inverts Ty2.
    pick_fresh x.
    forwards Imp : H8 x...
    forwards Imp2 : H1 Imp...
    eapply abs_compatibility...
    eapply uniq_from_swfte...
    inverts H2.

  - Case "capp".
    inverts Ty2.
    inverts Ty1.
    lets : inference_unique Ty1 H1.
    substs.
    forwards : IHTy1 H1.
    eapply coercion_compatibility1...
    eapply coercion_compatibility2...
Qed.


(* ********************************************************************** *)
(** * Typing of Fi+ expression contexts *)

(* Context replacement is not substitution, ott has difficulity generating correct definition *)

Inductive CTyp : CC -> stctx -> sctx -> dirflag -> sty -> stctx -> sctx -> dirflag -> sty -> cc -> Prop :=    (* defn CTyp *)
 | CTyp_empty1 : forall (DD:stctx) (GG:sctx) (A:sty),
     lc_sty A ->
     CTyp C_Empty DD GG Inf A DD GG Inf A cc_empty
 | CTyp_empty2 : forall (DD:stctx) (GG:sctx) (A:sty),
     lc_sty A ->
     CTyp C_Empty DD GG Chk A DD GG Chk A cc_empty
 | CTyp_appL1 : forall (CC5:CC) (ee2:sexp) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A2:sty) (cc5:cc) (e:exp) (A1:sty),
     CTyp CC5 DD GG Inf A DD' GG' Inf (sty_arrow A1 A2) cc5 ->
     has_type DD' GG' ee2 Chk A1 e ->
     CTyp (C_AppL CC5 ee2) DD GG Inf A DD' GG' Inf A2 (cc_appL cc5 e)
 | CTyp_appL2 : forall (CC5:CC) (ee2:sexp) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A2:sty) (cc5:cc) (e:exp) (A1:sty),
     CTyp CC5 DD GG Chk A DD' GG' Inf (sty_arrow A1 A2) cc5 ->
     has_type DD' GG' ee2 Chk A1 e ->
     CTyp (C_AppL CC5 ee2) DD GG Chk A DD' GG' Inf A2 (cc_appL cc5 e)
 | CTyp_appR1 : forall (ee1:sexp) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A2:sty) (e:exp) (cc5:cc) (A1:sty),
     CTyp CC5 DD GG Inf A DD' GG' Chk A1 cc5 ->
     has_type DD' GG' ee1 Inf (sty_arrow A1 A2) e ->
     CTyp (C_AppRd ee1 CC5) DD GG Inf A DD' GG' Inf A2 (cc_appR e cc5)
 | CTyp_appR2 : forall (ee1:sexp) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A2:sty) (e:exp) (cc5:cc) (A1:sty),
     CTyp CC5 DD GG Chk A DD' GG' Chk A1 cc5 ->
     has_type DD' GG' ee1 Inf (sty_arrow A1 A2) e ->
     CTyp (C_AppRd ee1 CC5) DD GG Chk A DD' GG' Inf A2 (cc_appR e cc5)
 | CTyp_mergeL1 : forall (CC5:CC) (ee2:sexp) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A1 A2:sty) (cc5:cc) (e:exp),
     CTyp CC5 DD GG Inf A DD' GG' Inf A1 cc5 ->
     has_type DD' GG' ee2 Inf A2 e ->
     disjoint DD' A1 A2 ->
     CTyp (C_MergeL CC5 ee2) DD GG Inf A DD' GG' Inf (sty_and A1 A2) (cc_pairL cc5 e)
 | CTyp_mergeL2 : forall (CC5:CC) (ee2:sexp) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A1 A2:sty) (cc5:cc) (e:exp),
     CTyp CC5 DD GG Chk A DD' GG' Inf A1 cc5 ->
     has_type DD' GG' ee2 Inf A2 e ->
     disjoint DD' A1 A2 ->
     CTyp (C_MergeL CC5 ee2) DD GG Chk A DD' GG' Inf (sty_and A1 A2) (cc_pairL cc5 e)
 | CTyp_mergeR1 : forall (ee1:sexp) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A1 A2:sty) (e:exp) (cc5:cc),
     CTyp CC5 DD GG Inf A DD' GG' Inf A2 cc5 ->
     has_type DD' GG' ee1 Inf A1 e ->
     disjoint DD' A1 A2 ->
     CTyp (C_MergeR ee1 CC5) DD GG Inf A DD' GG' Inf (sty_and A1 A2) (cc_pairR e cc5)
 | CTyp_mergeR2 : forall (ee1:sexp) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A1 A2:sty) (e:exp) (cc5:cc),
     CTyp CC5 DD GG Chk A DD' GG' Inf A2 cc5 ->
     has_type DD' GG' ee1 Inf A1 e ->
     disjoint DD' A1 A2 ->
     CTyp (C_MergeR ee1 CC5) DD GG Chk A DD' GG' Inf (sty_and A1 A2) (cc_pairR e cc5)
 | CTyp_rcd1 : forall (l:i) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (B:sty) (cc5:cc),
     CTyp CC5 DD GG Inf A DD' GG' Inf B cc5 ->
     CTyp (C_Rcd l CC5) DD GG Inf A DD' GG' Inf (sty_rcd l B) cc5
 | CTyp_rcd2 : forall (l:i) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (B:sty) (cc5:cc),
     CTyp CC5 DD GG Chk A DD' GG' Inf B cc5 ->
     CTyp (C_Rcd l CC5) DD GG Chk A DD' GG' Inf (sty_rcd l B) cc5
 | CTyp_proj1 : forall (CC5:CC) (l:i) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (B:sty) (cc5:cc),
     CTyp CC5 DD GG Inf A DD' GG' Inf (sty_rcd l B) cc5 ->
     CTyp (C_Proj CC5 l) DD GG Inf A DD' GG' Inf B cc5
 | CTyp_proj2 : forall (CC5:CC) (l:i) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (B:sty) (cc5:cc),
     CTyp CC5 DD GG Chk A DD' GG' Inf (sty_rcd l B) cc5 ->
     CTyp (C_Proj CC5 l) DD GG Chk A DD' GG' Inf B cc5
 | CTyp_anno1 : forall (CC5:CC) (A:sty) (DD:stctx) (GG:sctx) (B:sty) (DD':stctx) (GG':sctx) (cc5:cc),
     CTyp CC5 DD GG Inf B DD' GG' Chk A cc5 ->
     CTyp (C_Anno CC5 A) DD GG Inf B DD' GG' Inf A cc5
 | CTyp_anno2 : forall (CC5:CC) (A:sty) (DD:stctx) (GG:sctx) (B:sty) (DD':stctx) (GG':sctx) (cc5:cc),
     CTyp CC5 DD GG Chk B DD' GG' Chk A cc5 ->
     CTyp (C_Anno CC5 A) DD GG Chk B DD' GG' Inf A cc5
 | CTyp_abs1 : forall (x:expvar) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A1 A2:sty) (cc5:cc),
     CTyp CC5 DD GG Inf A DD'  (( x ~ A1 )++ GG' )  Chk A2 cc5 ->
     swft DD' A1 ->
     swfte DD' ->
     x `notin` dom GG' ->
     x `notin` dom DD' ->
     CTyp (C_Lam x CC5) DD GG Inf A DD' GG' Chk (sty_arrow A1 A2) (cc_lam x cc5)
 | CTyp_abs2 : forall (x:expvar) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A1 A2:sty) (cc5:cc),
     CTyp CC5 DD GG Chk A DD'  (( x ~ A1 )++ GG' )  Chk A2 cc5 ->
     swft DD' A1 ->
     swfte DD' ->
     x `notin` dom GG' ->
     x `notin` dom DD' ->
     CTyp (C_Lam x CC5) DD GG Chk A DD' GG' Chk (sty_arrow A1 A2) (cc_lam x cc5)
 | CTyp_tabs1 : forall X (L:vars) (B:sty) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (B':sty) (cc5:cc),
     CTyp CC5 DD GG Inf A  (( X ~ B )++ DD' )  GG' Inf  ( open_sty_wrt_sty B' (sty_var_f X) )  cc5   ->
     swft DD' B ->
     swfe DD' GG' ->
     swfte DD' ->
     X `notin` dom GG' ->
     X `notin` dom DD' ->
     X `notin` fv_sty_in_sty B' ->
     X `notin` fv_sty_in_sty B' ->
     CTyp (C_tabs X B CC5) DD GG Inf A DD' GG' Inf (sty_all B B') (cc_tabs X cc5)
 | CTyp_tabs2 : forall X (L:vars) (B:sty) (CC5:CC) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (B':sty) (cc5:cc),
     CTyp CC5 DD GG Chk A  (( X ~ B )++ DD' )  GG' Inf  ( open_sty_wrt_sty B' (sty_var_f X) )  cc5   ->
     swft DD' B ->
     swfe DD' GG' ->
     swfte DD' ->
     X `notin` dom GG' ->
     X `notin` dom DD' ->
     X `notin` fv_sty_in_sty B' ->
     X `notin` fv_sty_in_sty B' ->
     CTyp (C_tabs X B CC5) DD GG Chk A DD' GG' Inf (sty_all B B') (cc_tabs X cc5)
 | CTyp_tapp1 : forall (CC5:CC) (B:sty) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A2:sty) (cc5:cc) (A1:sty),
     CTyp CC5 DD GG Inf A DD' GG' Inf (sty_all A1 A2) cc5 ->
     swfte DD' ->
     swft DD' B ->
     disjoint DD' B A1 ->
     mono  B  ->
     CTyp (C_tapp CC5 B) DD GG Inf A DD' GG' Inf  (open_sty_wrt_sty  A2   B )  (cc_tapp cc5  (sty2ty  B ) )
 | CTyp_tapp2 : forall (CC5:CC) (B:sty) (DD:stctx) (GG:sctx) (A:sty) (DD':stctx) (GG':sctx) (A2:sty) (cc5:cc) (A1:sty),
     CTyp CC5 DD GG Chk A DD' GG' Inf (sty_all A1 A2) cc5 ->
     swfte DD' ->
     swft DD' B ->
     disjoint DD' B A1 ->
     mono  B  ->
     CTyp (C_tapp CC5 B) DD GG Chk A DD' GG' Inf  (open_sty_wrt_sty  A2   B )  (cc_tapp cc5  (sty2ty  B ) ).

Hint Constructors CTyp.

(** ** Context replacement *)

Fixpoint appctx (ctx : cc) (t : exp) : exp :=
  match ctx with
  | cc_empty => t
  | cc_lam x c => exp_abs (close_exp_wrt_exp x (appctx c t))
  | cc_tabs X c => exp_tabs (close_exp_wrt_ty X (appctx c t))
  | cc_tapp c T => exp_tapp (appctx c t) T
  | cc_appL c t2 => exp_app (appctx c t) t2
  | cc_appR t1 c => exp_app t1 (appctx c t)
  | cc_pairL c t2 => exp_pair (appctx c t) t2
  | cc_pairR t1 c => exp_pair t1 (appctx c t)
  | cc_co co c => exp_capp co (appctx c t)
  end.



(* ********************************************************************** *)
(** * Congruence lemma *)

Lemma congruence : forall Δ Δ' Γ Γ' E1 E2 A A' e1 e2 dir dir' C c,
    CTyp C Δ Γ dir A Δ' Γ' dir' A' c ->
    has_type Δ Γ E1 dir A e1 ->
    has_type Δ Γ E2 dir A e2 ->
    E_open Δ Γ e1 e2 A A ->
    E_open Δ' Γ' (appctx c e1) (appctx c e2) A' A'.
Proof with eauto.
  introv Ctx.
  gen E1 E2 e1 e2.
  induction Ctx; introv Ty1 Ty2 EH; simpls...

  - Case "appL1".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply app_compatibility...

  - Case "appL2".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply app_compatibility...

  - Case "appR1".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply app_compatibility...

  - Case "appR2".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply app_compatibility...

  - Case "mergeL1".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply pair_compatibility...

  - Case "mergeL2".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply pair_compatibility...

  - Case "mergeR1".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply pair_compatibility...

  - Case "mergeR2".
    lets : IHCtx Ty1 Ty2 EH...
    lets : fundamental_prop H H.
    eapply pair_compatibility...

  - Case "rcd1".
    lets : IHCtx Ty1 Ty2 EH...
    apply record_compatibility...

  - Case "rcd2".
    lets : IHCtx Ty1 Ty2 EH...
    apply record_compatibility...

  - Case "proj1".
    lets : IHCtx Ty1 Ty2 EH...
    lets HH : record_compatibility...
    apply HH in H...

  - Case "proj2".
    lets : IHCtx Ty1 Ty2 EH...
    lets HH : record_compatibility...
    apply HH in H...

  - Case "abs1".
    lets : IHCtx Ty1 Ty2 EH...
    apply abs_compatibility with (x := x)...
    rewrite fv_exp_in_exp_close_exp_wrt_exp...
    rewrite fv_exp_in_exp_close_exp_wrt_exp...
    repeat rewrite~ open_exp_wrt_exp_close_exp_wrt_exp.

  - Case "abs2".
    lets : IHCtx Ty1 Ty2 EH...
    apply abs_compatibility with (x := x)...
    rewrite fv_exp_in_exp_close_exp_wrt_exp...
    rewrite fv_exp_in_exp_close_exp_wrt_exp...
    repeat rewrite open_exp_wrt_exp_close_exp_wrt_exp...

  - Case "tabs1".
    lets : IHCtx Ty1 Ty2 EH...
    apply tabs_compatibility with (X := X)...
    rewrite fv_ty_in_exp_close_exp_wrt_ty...
    rewrite fv_ty_in_exp_close_exp_wrt_ty...
    repeat rewrite~ open_exp_wrt_ty_close_exp_wrt_ty...

  - Case "tabs2".
    lets : IHCtx Ty1 Ty2 EH...
    apply tabs_compatibility with (X := X)...
    rewrite fv_ty_in_exp_close_exp_wrt_ty...
    rewrite fv_ty_in_exp_close_exp_wrt_ty...
    repeat rewrite~ open_exp_wrt_ty_close_exp_wrt_ty...


  - Case "tapp".
    lets : IHCtx Ty1 Ty2 EH...
    eapply tapp_compatibility...

  - Case "tapp".
    lets : IHCtx Ty1 Ty2 EH...
    eapply tapp_compatibility...

Qed.


(* ********************************************************************** *)
(** * Contextual equivalence *)

Definition kleene_equiv t1 t2 :=
  exists k, t1 ->* (exp_lit k) /\ t2 ->* (exp_lit k).


Definition ctx_equiv Δ Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Δ Γ E1 dir A e1 ->
    has_type Δ Γ E2 dir A e2 ->
    CTyp C Δ Γ dir A nil nil dir' sty_nat c ->
    kleene_equiv (appctx c e1) (appctx c e2).


(* ********************************************************************** *)
(** * Adequacy lemma *)

Lemma adequacy : forall e1 e2,
    E_open nil nil e1 e2 sty_nat sty_nat ->
    kleene_equiv e1 e2.
Proof with eauto.
  introv EH.
  destruct EH as (WF1 & WF2 & ? & ? & EH).
  specializes EH rel_d_empty rel_g_empty...
  simpls...
  destruct EH as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & VH)...
  destruct VH...
  unfolds.
  exists n...
Qed.


(* ********************************************************************** *)
(** * Coherence property *)

Theorem coherence : forall Δ Γ E A,
    ctx_equiv Δ Γ E E A.
Proof with eauto.
  intros.
  unfolds.
  introv Ty1 Ty2 Ctx.
  lets H : fundamental_prop Ty1 Ty2.
  lets HH : congruence Ctx Ty1 Ty2 H.
  apply adequacy in HH...
Qed.
