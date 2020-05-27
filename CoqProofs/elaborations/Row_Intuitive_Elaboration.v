
Require Import Metalib.Metatheory.
Require Import Infrastructure.
Require Import Disjoint.
Require Import Syntax_ott.
Require Import Row_Intuitive_Syntax.
Require Import Row_Intuitive_Inf.

(* ********************************************************************** *)
(** * Auxiliary definitions *)
(* ********************************************************************** *)


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C3 := gather_atoms_with (fun x : stctx => dom x) in
  let C4 := gather_atoms_with (fun x : sctx => dom x) in
  let D4 := gather_atoms_with (fun x => fv_sty_in_sty x) in
  let D5 := gather_atoms_with (fun x => fv_sty_in_sexp x) in
  let D6 := gather_atoms_with (fun x => fv_sexp_in_sexp x) in
  let E1 := gather_atoms_with (fun x : TContext => dom x) in
  let E2 := gather_atoms_with (fun x : GContext => dom x) in
  let E3 := gather_atoms_with (fun x  => fv_rexp_in_rexp x) in
  let E4 := gather_atoms_with (fun x  => fv_rtyp_in_rexp x) in
  let E5 := gather_atoms_with (fun x  => fv_rtyp_in_rtyp x) in
  let E6 := gather_atoms_with (fun x  => fv_rtyp_in_rt x) in
  let E7 := gather_atoms_with (fun x  => fv_rtyp_in_rlist x) in
  constr:(A \u B \u C3 \u C4 \u D4 \u D5 \u D6 \u E1 \u E2 \u E3 \u E4 \u E5 \u E6 \u E7).


Definition trans_Ttx T := map trans_rlist  T.

Definition trans_Gtx G := map trans_rt G.

Lemma trans_open_rt_wrt_rtyp_rec : forall A B n,
    trans_rt ( open_rt_wrt_rtyp_rec n B A ) = open_sty_wrt_sty_rec n (trans_rtyp B ) (trans_rt A )

with

trans_open_rlist_wrt_rtyp_rec : forall R A n,
    trans_rlist (open_rlist_wrt_rtyp_rec n A R) =  open_sty_wrt_sty_rec n (trans_rtyp A) (trans_rlist R)

with

trans_open_rtyp_wrt_rtyp_rec : forall A B m,
    trans_rtyp ( open_rtyp_wrt_rtyp_rec m B A ) = open_sty_wrt_sty_rec m (trans_rtyp B ) (trans_rtyp A ).


Proof with eauto.
  - Case "rt".
    intros A.
    induction A; intros B n; simpls...

    rewrite IHA1...
    rewrite IHA2...

    rewrite trans_open_rlist_wrt_rtyp_rec...
    rewrite IHA...

  - Case "rlist".

    intros R.
    induction R; intros A n; simpls...

    rewrite trans_open_rtyp_wrt_rtyp_rec...
    rewrite IHR...

  - Case "rtyp".

    intros A.
    induction A; intros B m; simpls...


    destruct (lt_eq_lt_dec n m)...
    destruct s...

    rewrite trans_open_rt_wrt_rtyp_rec...
    rewrite trans_open_rtyp_wrt_rtyp_rec...
    rewrite trans_open_rtyp_wrt_rtyp_rec...
Qed.


Lemma trans_open_rt_wrt_rtyp : forall t1 t2,
    trans_rt (open_rt_wrt_rtyp t1 t2) = open_sty_wrt_sty (trans_rt t1) (trans_rtyp t2).
Proof.
  intros.
  unfold open_rt_wrt_rtyp.
  unfold open_sty_wrt_sty.
  rewrite trans_open_rt_wrt_rtyp_rec.
  reflexivity.
Qed.


Lemma wfr_lc : forall T r,
    wfr T r ->
    lc_rtyp r

with

wfrt_lc : forall T t,
    wfrt T t ->
    lc_rt t

with

wfcl_lc : forall T R,
    wfcl T R ->
    lc_rlist R.
Proof with eauto.
  - Case "wft".
    introv WFR.
    induction WFR.

    constructor.
    constructor...
    constructor.
    constructor...

  - Case "wfrt".
    introv WFT.
    induction WFT.
    constructor.
    constructor...
    pick fresh a.
    specializes H1; auto.
    eapply lc_rt_ConQuan_exists...
    constructor...

  - Case "wfcl".
    introv WFCL.
    induction WFCL.
    constructor.
    constructor...
Qed.



Lemma wftc_uniq : forall T,
    wftc T ->
    uniq T.
Proof with eauto.
  intros T.
  alist induction T; intros; simpls...
  inverts H...
Qed.



Lemma trans_lc_typ : forall t,
    lc_rt t ->
    lc_sty (trans_rt t)

with

trans_lc_rlist : forall R,
    lc_rlist R ->
    lc_sty (trans_rlist R)

with

trans_lc_rty : forall r,
    lc_rtyp r ->
    lc_sty (trans_rtyp r).

Proof with eauto.
  - Case "typ".
    introv LC.
    induction LC; simpls...

    pick fresh X.
    apply lc_sty_all_exists with X...
    replace (sty_var_f X) with (trans_rtyp (r_TyVar_f X))...
    rewrite <- trans_open_rt_wrt_rtyp...

  - Case "rtyp".
    introv LC.
    induction LC; simpls...

  - Case "rlist".
    introv LC.
    induction LC; simpls...
Qed.


Hint Resolve wfr_lc wfrt_lc wftc_uniq.


Hint Constructors has_type.


Lemma notin_rtyp_sty : forall A X,
    X `notin` fv_rtyp_in_rt A ->
    X `notin` fv_sty_in_sty (trans_rt A )

with

notin_rtyp_rlist : forall R X,
    X `notin` fv_rtyp_in_rlist R ->
    X `notin` fv_sty_in_sty (trans_rlist R)

with

notin_rtyp_rtyp : forall r X,
    X `notin` fv_rtyp_in_rtyp r ->
    X `notin` fv_sty_in_sty (trans_rtyp r).

Proof with eauto.

  - Case "typ".

    intros A.
    induction A; introv Notin; simpls...

  - Case "rlist".

    intros R.
    induction R; introv Notin; simpls...

  - Case "rtyp".

    intros r.
    induction r; introv Notin; simpls...

Qed.



(* ********************************************************************** *)
(** * Type safety lemmas *)
(* ********************************************************************** *)

Inductive wtt : TContext -> GContext -> rexp -> rt -> sexp -> Prop :=    (* defn wtt *)
 | wtt_Eq : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (rt':rt) (ee:sexp) (rt5:rt),
     wtt Ttx Gtx re rt5 ee ->
     teq Ttx rt5 rt' ->
     wtt Ttx Gtx re rt' (sexp_anno ee (trans_rt rt'))
 | wtt_Var : forall (Ttx:TContext) (Gtx:GContext) (x:expvar) (rt5:rt),
     wftc Ttx ->
     wfc Ttx Gtx ->
     binds  x   rt5   Gtx  ->
     wtt Ttx Gtx (re_Var_f x) rt5 (sexp_var_f x)
 | wtt_Lit : forall (Ttx:TContext) (Gtx:GContext) (x:nat),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wtt Ttx Gtx (re_Lit x) rt_Base (sexp_lit x)
 | wtt_ArrowI : forall (L:vars) (Ttx:TContext) (Gtx:GContext) (rt5:rt) (re:rexp) (rt':rt) (ee:sexp),
     wfrt Ttx rt5 ->
      ( forall x , x \notin  L  -> wtt Ttx  (( x ~ rt5 )++ Gtx )   ( open_rexp_wrt_rexp re (re_Var_f x) )  rt'  ( open_sexp_wrt_sexp ee (sexp_var_f x) )  )  ->
      wtt Ttx Gtx (re_Abs rt5 re) (rt_Fun rt5 rt')
          (sexp_anno  ( (sexp_abs ee) )  (sty_arrow  (trans_rt rt5) (trans_rt rt') ))
 | wtt_ArrowE : forall (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (rt':rt) (ee1 ee2:sexp) (rt5:rt),
     wtt Ttx Gtx re1 (rt_Fun rt5 rt') ee1 ->
     wtt Ttx Gtx re2 rt5 ee2 ->
     wtt Ttx Gtx (re_App re1 re2) rt' (sexp_app ee1 ee2)
 | wtt_Base : forall (Ttx:TContext) (Gtx:GContext) (l:i) (re:rexp) (rt5:rt) (ee:sexp),
     wtt Ttx Gtx re rt5 ee ->
     wtt Ttx Gtx (re_SingleField l re) (rt_Record (r_SingleField l rt5)) (sexp_rcd l ee)
 | wtt_Empty : forall (Ttx:TContext) (Gtx:GContext),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wtt Ttx Gtx re_Empty (rt_Record r_Empty) sexp_top
 | wtt_Merge : forall (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (r1 r2:rtyp) (ee1 ee2:sexp),
     wtt Ttx Gtx re1 (rt_Record r1) ee1 ->
     wtt Ttx Gtx re2 (rt_Record r2) ee2 ->
     cmp Ttx r1 r2 ->
     wtt Ttx Gtx (re_Merge re1 re2) (rt_Record (r_Merge r1 r2)) (sexp_merge ee1 ee2)
 | wtt_Restr : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (r:rtyp) (ee:sexp) (rt5:rt),
     wtt Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     wtt Ttx Gtx (re_Res re l) (rt_Record r) (sexp_anno ee  (trans_rtyp r) )
 | wtt_Select : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (rt5:rt) (ee:sexp) (r:rtyp),
     wtt Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     wtt Ttx Gtx (re_Selection re l) rt5 (sexp_proj  ( (sexp_anno ee (sty_rcd l  (trans_rt rt5) )) )  l)

 | wtt_AllI : forall (L:vars) (Ttx:TContext) (Gtx:GContext) (R:rlist) (re:rexp) (rt5:rt) (ee:sexp),
     wfc Ttx Gtx ->
     wfcl Ttx R ->
     ( forall a , a \notin  L  ->
             wtt  (( a ~ R )++ Ttx )  Gtx
                  ( open_rexp_wrt_rtyp re (r_TyVar_f a) )
                  ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )
                  (open_sexp_wrt_sty ee (sty_var_f a))  ) ->
     wtt Ttx Gtx (re_ConTyAbs R re) (rt_ConQuan R rt5) (sexp_tabs (trans_rlist R)  ee)

 | wtt_AllE : forall (Ttx:TContext) (Gtx:GContext) (re:rexp) (r:rtyp) (rt5:rt) (ee:sexp) (R:rlist),
     wtt Ttx Gtx re (rt_ConQuan R rt5) ee ->
     cmpList Ttx r R ->
     wtt Ttx Gtx (re_ConTyApp re r)  (open_rt_wrt_rtyp  rt5   r )  (sexp_tapp ee (trans_rtyp r)) .


Section type_safe_trans.

  (* These are internal properties of Harper's system *)
  Variable cmp_regular : forall T r r',
    cmp T r r' ->
    wfr T r /\ wfr T r'.

  Variable wtt_regular : forall T G e1 t E,
    wtt T G e1 t E ->
    wfrt T t /\ wftc T.


  Lemma cmp_list_regular : forall T r R,
      cmpList T r R ->
      wftc T ->
      wfr T r /\ wfcl T R.
    Proof with eauto.
      introv CMP.
      induction CMP; introv WFTC; splits; simpls...
      forwards (? & ?) : cmp_regular H...
      forwards (? & ?) : cmp_regular H...
      forwards (? & ?) : IHCMP WFTC...
    Qed.

  Lemma wfcl_to_swft : forall T R,
      wfcl T R ->
      swft (trans_Ttx T) (trans_rlist R)
  with

  wfr_to_swft : forall T r,
      wfr T r ->
      swft (trans_Ttx T) (trans_rtyp r)

  with

  wft_to_swft :forall T t,
      wfrt T t ->
      swft (trans_Ttx T) (trans_rt t).


  Proof with eauto.
    - Case "wfcl_to_swft".

      introv WFCL.

      induction WFCL.

      + SCase "empty".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "rl_rtyp".
        forwards : wfr_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

    - Case "wfr_to_swft".

      introv WFR.

      induction WFR.

      + SCase "var".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls.
        econstructor.
        eapply binds_map_2...


      + SCase "record".
        forwards : wft_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "empty".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "restrict".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...


    - Case "wft_to_swft".

      introv WFT.

      induction WFT.

      + SCase "base".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "arrow".
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...

      + SCase "forall".
        forwards : wfcl_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls.
        pick fresh X and apply swft_all...
        replace (sty_var_f X) with (trans_rtyp (r_TyVar_f X))...
        rewrite <- trans_open_rt_wrt_rtyp...

      + SCase "record".
        forwards : wfr_to_swft H.
        clear wfr_to_swft wft_to_swft wfcl_to_swft.
        simpls...
  Qed.


  Lemma wftc_to_swfte : forall T,
      wftc T ->
      swfte (trans_Ttx T).
  Proof with eauto.
    introv WFTC.

    induction WFTC; simpls...

    forwards : wfcl_to_swft H.

    econstructor...
    unfold trans_Ttx...
  Qed.


  Lemma wfc_to_swfe : forall T G,
      wfc T G ->
      swfe (trans_Ttx T) (trans_Gtx G).
  Proof with eauto using wft_to_swft.
    introv H.
    induction H; simpls...
    constructor...
    unfold trans_Gtx...
    unfold trans_Ttx...
  Qed.


  Lemma teq_csub : forall T t t',
      teq T t t' ->
      uniq T ->
      sub (trans_Ttx T) (trans_rt t) (trans_rt t') /\
      sub (trans_Ttx T) (trans_rt t') (trans_rt t)

  with

  ceq_csub: forall T R R',
      ceq T R R' ->
      uniq T ->
      sub (trans_Ttx T) (trans_rlist R) (trans_rlist R') /\
      sub (trans_Ttx T) (trans_rlist R') (trans_rlist R).

  Proof with eauto using wft_to_swft, wfr_to_swft, wfcl_to_swft, notin_rtyp_sty.

    - Case "teq".
      introv Eq.
      induction Eq; introv Uniq.

      + SCase "refl".
        clear teq_csub ceq_csub.
        splits...

      + SCase "sym".
        clear teq_csub ceq_csub.
        destruct IHEq...

      + SCase "trans".
        clear teq_csub ceq_csub.

        destruct (IHEq1 Uniq) as (Sub1 & Sub2).
        destruct (IHEq2 Uniq) as (Sub3 & Sub4).

        splits...

      + SCase "arrow".
        clear teq_csub ceq_csub.

        simpls.

        destruct (IHEq1 Uniq) as (Sub1 & Sub2).
        destruct (IHEq2 Uniq) as (Sub3 & Sub4).

        splits...

      + SCase "typ_all".
        simpls.
        splits.

        pick fresh a.
        forwards ( Sub1 & Sub2) : H1 a; auto.
        forwards (? & ?) : ceq_csub H; auto.
        rewrite trans_open_rt_wrt_rtyp in *.
        rewrite trans_open_rt_wrt_rtyp in *.
        pick fresh b and apply S_forall; eauto.
        apply sub_renaming with (X := a)...
        unfold trans_Ttx; eauto.
        unfold trans_Ttx; eauto.
        rewrite_env (nil ++ [(a, trans_rlist R')] ++ trans_Ttx Ttx).
        apply sub_narrow with (Q := trans_rlist R); auto.
        simpls...
        unfold trans_Ttx; eauto.


        pick fresh a.
        forwards (Sub1 & Sub2) : H1 a; auto.
        forwards (? & ?) : ceq_csub H; auto.
        rewrite trans_open_rt_wrt_rtyp in *.
        rewrite trans_open_rt_wrt_rtyp in *.
        pick fresh b and apply S_forall; eauto.
        apply sub_renaming with (X := a)...
        unfold trans_Ttx; eauto.
        unfold trans_Ttx; eauto.


      + SCase "base".
        forwards (? & ?) : teq_csub Eq; try assumption.
        clear teq_csub ceq_csub.

        simpls; splits...

      + SCase "merge".
        clear teq_csub ceq_csub.
        destruct (IHEq1 Uniq).
        destruct (IHEq2 Uniq).

        simpls; splits.

        eapply S_and.
        apply S_trans with (trans_rtyp r1)...
        apply S_trans with (trans_rtyp r2)...

        eapply S_and.
        apply S_trans with (trans_rtyp r1')...
        apply S_trans with (trans_rtyp r2')...


      + SCase "merge_unit".
        clear teq_csub ceq_csub.

        simpls; splits...

        eapply S_and...

      + SCase "merge_assoc".
        clear teq_csub ceq_csub.
        forwards (? & ?): cmp_regular H.
        forwards (? & ?): cmp_regular H0.
        simpls; splits.

        eapply S_and.
        eapply S_and.
        eapply S_andl...
        apply S_trans with ((sty_and (trans_rtyp r2) (trans_rtyp r3)))...
        eapply S_andr...
        apply S_trans with ((sty_and (trans_rtyp r2) (trans_rtyp r3)))...
        eapply S_andr...

        eapply S_and.
        apply S_trans with ((sty_and (trans_rtyp r1) (trans_rtyp r2)))...
        eapply S_andl...
        eapply S_and.
        apply S_trans with ((sty_and (trans_rtyp r1) (trans_rtyp r2)))...
        eapply S_andl...
        eapply S_andr...

      + SCase "merge_comm".
        clear teq_csub ceq_csub.
        forwards (? & ?): cmp_regular H.

        simpls; splits.

        eapply S_and...
        eapply S_and...

    - Case "ceq".

      introv Eq.
      induction Eq; introv Uniq.

      + SCase "refl".

        clear teq_csub ceq_csub.

        splits...


      + SCase "sym".
        clear teq_csub ceq_csub.

        destruct (IHEq Uniq).
        splits...

      + SCase "trans".
        clear teq_csub ceq_csub.

        destruct (IHEq1 Uniq) as (Sub1 & Sub2).
        destruct (IHEq2 Uniq) as (Sub3 & Sub4).

        splits...


      + SCase "inner".

        lets (? & ?) : teq_csub H; try assumption.
        clear teq_csub ceq_csub.

        destruct (IHEq Uniq) as (Sub1 & Sub2).
        simpls.
        splits.

        eapply S_and.
        apply S_trans with ((trans_rtyp r))...
        apply S_trans with ((trans_rlist R))...

        eapply S_and.
        apply S_trans with ((trans_rtyp r))...
        apply S_trans with ((trans_rlist R))...


      + SCase "swap".
        clear teq_csub ceq_csub.

        simpls.
        splits.


        eapply S_and.
        apply S_trans with ((sty_and (trans_rtyp r') (trans_rlist R)))...
        eapply S_andr...
        eapply S_and.
        eapply S_andl...
        apply S_trans with ((sty_and (trans_rtyp r') (trans_rlist R)))...
        eapply S_andr...

        eapply S_and.
        apply S_trans with ((sty_and (trans_rtyp r) (trans_rlist R)))...
        eapply S_andr...
        eapply S_and.
        eapply S_andl...
        apply S_trans with ((sty_and (trans_rtyp r) (trans_rlist R)))...
        eapply S_andr...


      + SCase "empty".
        clear teq_csub ceq_csub.
        simpls.
        splits...

        eapply S_and...

      + SCase "merge".
        clear teq_csub ceq_csub.

        simpls.
        inverts H.
        splits.

        eapply S_and.
        apply S_trans with ((sty_and (trans_rtyp r1) (trans_rtyp r2)))...
        eapply S_andl...
        eapply S_and.
        apply S_trans with ((sty_and (trans_rtyp r1) (trans_rtyp r2)))...
        eapply S_andl...
        eapply S_andr...


        eapply S_and.
        eapply S_and.
        eapply S_andl...
        apply S_trans with ((sty_and (trans_rtyp r2) (trans_rlist R)))...
        eapply S_andr...
        apply S_trans with ((sty_and (trans_rtyp r2) (trans_rlist R)))...
        eapply S_andr...

      + SCase "dupl".
        clear teq_csub ceq_csub.

        simpls; splits.


        eapply S_and.
        eapply S_andl...
        apply S_trans with ((sty_and (trans_rtyp r) (trans_rlist R)))...
        eapply S_andr...

        eapply S_and.
        eapply S_andl...
        apply S_trans with ((sty_and (trans_rtyp r) (trans_rlist R)))...


      + SCase "base".
        forwards (? & ?) : teq_csub H2; try assumption.
        clear teq_csub ceq_csub.

        simpls; splits.

        eapply S_and.
        eapply S_trans with ((sty_rcd l (trans_rt rt5)))...
        eapply S_andr...


        eapply S_and.
        apply S_trans with ((sty_rcd l (trans_rt rt')))...
        eapply S_andr...


  Qed.


  Lemma rtyp_in_rlist_sub: forall T r R,
      rtyp_in_rlist r R ->
      wfcl T R ->
      wfr T r ->
      sub (trans_Ttx T) (trans_rlist R) (trans_rtyp r).
  Proof with eauto using wfcl_to_swft, wfr_to_swft, wfr_to_swft.
    introv Rlst.
    induction Rlst; introv WFCL WFT; simpls...

    inverts WFCL.

    eapply S_andl...

    inverts WFCL.
    specializes IHRlst...
  Qed.


  Lemma cmp_disjoint : forall T r r',
      cmp T r r' ->
      wftc T ->
      disjoint (trans_Ttx T) (trans_rtyp r) (trans_rtyp r').
  Proof with eauto using wft_to_swft, wfr_to_swft, wftc_to_swfte.
    introv CMP.

    induction CMP; introv Uniq; simpls...

    - Case "eq".
      assert (uniq (trans_Ttx Ttx)).
      unfold trans_Ttx...
      lets (? & ?) : teq_csub H...
      lets (? & ?) : teq_csub H0...
      specializes IHCMP Uniq.
      eapply disjoint_symmetric in IHCMP...
      forwards HH3 : disjoint_sub IHCMP...
      eapply disjoint_symmetric in HH3...
      eapply disjoint_sub...

    - Case "symm".
      specializes IHCMP Uniq.
      eapply disjoint_symmetric...
      unfold trans_Ttx...

    - Case "tvar".
      forwards ? : rtyp_in_rlist_sub H0...
      unfolds trans_Ttx...

    - Case "mergeE1".
      specializes IHCMP Uniq.
      eapply disjoint_and in IHCMP...
      destruct IHCMP...
      forwards (? & ?): cmp_regular CMP...

    - Case "mergeE2".
      specializes IHCMP Uniq.
      eapply disjoint_and in IHCMP...
      destruct IHCMP...
      forwards (? & ?): cmp_regular CMP...

  Qed.


  Lemma cmp_list_disjoint : forall T r R,
      cmpList T r R ->
      wftc T ->
      disjoint (trans_Ttx T) (trans_rtyp r) (trans_rlist R).
  Proof with eauto using wfr_to_swft, cmp_disjoint.
    introv CMP.
    induction CMP; introv Uniq; simpls...
  Qed.


  Theorem type_safe : forall T G e t E,
      wtt T G e t E ->
      has_type (trans_Ttx T) (trans_Gtx G) E Inf (trans_rt t).
  Proof with eauto using wft_to_swft, wfc_to_swfe, wftc_to_swfte, cmp_disjoint, wfcl_to_swft, wfr_to_swft, cmp_list_disjoint.

    introv WTT.

    induction WTT; simpls...


    - Case "wtt_eq".
      lets (? & ?) : teq_csub...
      forwards (? & ?) : wtt_regular WTT...

    - Case "wtt_var".
      econstructor...
      eapply binds_map_2...

    - Case "wtt_abs".
      econstructor...

      pick fresh x and apply T_abs...
      forwards WTT : H0 x...
      forwards (? & ?) : wtt_regular WTT...
      forwards : H1 x...

    - Case "wtt_app".
      forwards (WFTC & ?) : wtt_regular WTT1...
      inverts WFTC...

      econstructor...


    - Case "wtt_merge".
      forwards (W & ?) : wtt_regular WTT1.
      inverts W.
      forwards (W & ?) : wtt_regular WTT2.
      inverts W.

      econstructor...

    - Case "wtt_restr".
      forwards (W & ?) : wtt_regular WTT.
      inverts W as W.
      inverts W as W.
      inverts W as W.

      econstructor.
      eapply T_sub...

    - Case "wtt_select".
      forwards (W & ?) : wtt_regular WTT.
      inverts W as W.
      inverts W as W.
      inverts W as W.
      econstructor...
      econstructor...
      eapply T_sub...

    - Case "wtt_tabs".
      pick fresh a and apply T_tabs...
      forwards : H1 a...
      replace (sty_var_f a) with (trans_rtyp (r_TyVar_f a))...
      rewrite <- trans_open_rt_wrt_rtyp...
      eapply H2...

    - Case "wtt_tapp".
      forwards (? & ?) : wtt_regular WTT.
      forwards (? & ?) : cmp_list_regular H...
      rewrite trans_open_rt_wrt_rtyp...
  Qed.

End type_safe_trans.