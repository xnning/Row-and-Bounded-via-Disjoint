Require Export LibTactics.
Require Export Metalib.Metatheory.
Require Import Row_inf.
Require Import Fii_inf.
Require Import Infrastructure.
Require Import Row_Properties.
Require Import Disjoint.

Set Implicit Arguments.

(** *Bottom translation of types  *)
Inductive bot_trans_r : PContext -> rtyp -> sty -> Prop :=    (* defn bot_trans_r *)
 | bot_trans_r_var : forall (Ptx:PContext) (a b:typvar),
      binds ( a ) ( b ) ( Ptx )  ->
     bot_trans_r Ptx (r_TyVar_f a) (sty_var_f b)
 | bot_trans_r_empty : forall (Ptx:PContext),
     bot_trans_r Ptx r_Empty sty_top
 | bot_trans_r_record : forall (Ptx:PContext) (l:i) (rt5:rt),
     lc_rt rt5 ->
     bot_trans_r Ptx (r_SingleField l rt5) (sty_rcd l sty_bot)
 | bot_trans_r_merge : forall (Ptx:PContext) (r1 r2:rtyp) (A B:sty),
     bot_trans_r Ptx r1 A ->
     bot_trans_r Ptx r2 B ->
     bot_trans_r Ptx (r_Merge r1 r2) (sty_and A B).


(** *Translation of types  *)
Inductive trans_rt : PContext -> rt -> sty -> Prop :=
 | trans_rt_nat : forall (Ptx:PContext),
     trans_rt Ptx rt_Base sty_nat
 | trans_rt_arrow : forall (Ptx:PContext) (rt1 rt2:rt) (A B:sty),
     trans_rt Ptx rt1 A ->
     trans_rt Ptx rt2 B ->
     trans_rt Ptx (rt_Fun rt1 rt2) (sty_arrow A B)
 | trans_rt_all : forall (L:vars) (Ptx:PContext) (R:rlist) (rt5:rt) (B A:sty),
      trans_rlist Ptx R B ->
      ( forall b , b \notin  L  ->
        ( forall a , a \notin L \u {{b}} ->
            trans_rt  (( a ~ b )++ Ptx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )
              ( open_sty_wrt_sty   ( open_sty_wrt_sty_rec 1 (sty_var_f a) A ) (sty_var_f b)  )  )  )  ->
      trans_rt Ptx (rt_ConQuan R rt5) (sty_all B (sty_all B A))
 | trans_rt_record : forall (Ptx:PContext) (r:rtyp) (A:sty),
     trans_r  Ptx r A ->
     trans_rt Ptx (rt_Record r) A

(** *Translation of records  *)
with trans_r : PContext -> rtyp -> sty -> Prop :=
 | trans_r_empty : forall (Ptx:PContext),
     trans_r Ptx r_Empty sty_top
 | trans_r_tvar : forall (Ptx:PContext) (a b:typvar),
    binds ( a ) ( b ) ( Ptx )  ->
     trans_r Ptx (r_TyVar_f a) (sty_var_f a)
 | trans_r_record : forall (Ptx:PContext) (l:i) (rt5:rt) (A:sty),
     trans_rt Ptx rt5 A ->
     trans_r Ptx (r_SingleField l rt5) (sty_rcd l A)
 | trans_r_merge : forall (Ptx:PContext) (r1 r2:rtyp) (A B:sty),
     trans_r Ptx r1 A ->
     trans_r Ptx r2 B ->

     trans_r Ptx (r_Merge r1 r2) (sty_and A B)

(** *Translation of constraint lists  *)
with trans_rlist : PContext -> rlist -> sty -> Prop :=    (* defn trans_rlist *)
 | trans_rlist_empty : forall (Ptx:PContext),
     trans_rlist Ptx R_Empty sty_top
 | trans_rlist_cons : forall (Ptx:PContext) (r:rtyp) (R:rlist) (A1 A2 B:sty),
     trans_r Ptx r A1 ->
     bot_trans_r Ptx r A2 ->
     trans_rlist Ptx R B ->
     trans_rlist Ptx (R_Cons r R) (sty_and  ( (sty_and A1 A2) )  B).

(** *Translation of type contexts  *)
Inductive trans_Ttx : PContext -> TContext -> stctx -> Prop :=
  | trans_Ttx_nil :
      trans_Ttx nil nil nil
  | trans_Ttx_cons : forall Ptx Ttx DD a b R A,
      trans_Ttx Ptx Ttx DD ->
      trans_rlist Ptx R A ->
      a \notin dom DD \u dom Ttx \u dom Ptx \u fv_Ptx Ptx ->
      b \notin dom Ptx \u dom Ttx \u dom ((a ~ A) ++ DD) \u fv_Ptx Ptx ->
      trans_Ttx ((a~b)++Ptx) ((a ~ R)++Ttx) ((b ~ A ) ++ (a ~ A) ++ DD)
.


(** *Translation of term contexts  *)
Inductive trans_Gtx : PContext -> GContext -> stctx -> Prop :=
  | trans_Gtx_nil : forall Ptx,
      trans_Gtx Ptx nil nil
  | trans_Gtx_cons : forall Ptx Gtx GG A x rt,
      trans_Gtx Ptx Gtx GG ->
      trans_rt Ptx rt A ->
      x \notin fv_Ptx Ptx ->
      trans_Gtx Ptx ((x ~ rt) ++ Gtx) ((x ~ A ) ++ GG)
.

(** *Translation of well-typed terms  *)
Inductive wtt : PContext -> TContext -> GContext -> rexp -> rt -> sexp -> Prop :=    (* defn wtt *)
 | wtt_Eq : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (rt':rt) (ee:sexp) (rt5:rt) (A:sty),
     wtt Ptx Ttx Gtx re rt5 ee ->
     teq Ttx rt5 rt' ->
     trans_rt Ptx  rt' A ->
     wtt Ptx Ttx Gtx re rt' (sexp_anno ee A)
 | wtt_Var : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (x:expvar) (rt5:rt),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wfp Ttx Ptx ->
     binds  x   rt5   Gtx  ->
     wtt Ptx Ttx Gtx (re_Var_f x) rt5 (sexp_var_f x)
 | wtt_Lit : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (x:nat),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wfp Ttx Ptx ->
     wtt Ptx Ttx Gtx (re_Lit x) rt_Base (sexp_lit x)
 | wtt_ArrowI : forall (L:vars) (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (rt5:rt) (re:rexp) (rt':rt) (ee:sexp) (A B:sty),
     wfrt Ttx rt5 ->
      ( forall x , x \notin  L  -> wtt Ptx Ttx  (( x ~ rt5 )++ Gtx )   ( open_rexp_wrt_rexp re (re_Var_f x) )  rt'  ( open_sexp_wrt_sexp ee (sexp_var_f x) )  )  ->
      trans_rt Ptx  rt5 A ->
      trans_rt Ptx  rt' B ->
      wtt Ptx Ttx Gtx (re_Abs rt5 re) (rt_Fun rt5 rt')
          (sexp_anno  ( (sexp_abs ee) )  (sty_arrow  A B ))
 | wtt_ArrowE : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (rt':rt) (ee1 ee2:sexp) (rt5:rt),
     wtt Ptx Ttx Gtx re1 (rt_Fun rt5 rt') ee1 ->
     wtt Ptx Ttx Gtx re2 rt5 ee2 ->
     wtt Ptx Ttx Gtx (re_App re1 re2) rt' (sexp_app ee1 ee2)
 | wtt_Base : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (l:i) (re:rexp) (rt5:rt) (ee:sexp),
     wtt Ptx Ttx Gtx re rt5 ee ->
     wtt Ptx Ttx Gtx (re_SingleField l re) (rt_Record (r_SingleField l rt5)) (sexp_rcd l ee)
 | wtt_Empty : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext),
     wftc Ttx ->
     wfc Ttx Gtx ->
     wfp Ttx Ptx ->
     wtt Ptx Ttx Gtx re_Empty (rt_Record r_Empty) sexp_top
 | wtt_Merge : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re1 re2:rexp) (r1 r2:rtyp) (ee1 ee2:sexp),
     wtt Ptx Ttx Gtx re1 (rt_Record r1) ee1 ->
     wtt Ptx Ttx Gtx re2 (rt_Record r2) ee2 ->
     cmp Ttx r1 r2 ->
     wtt Ptx Ttx Gtx (re_Merge re1 re2) (rt_Record (r_Merge r1 r2)) (sexp_merge ee1 ee2)
 | wtt_Restr : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (r:rtyp) (ee:sexp) (rt5:rt) (A:sty),
     wtt Ptx Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     trans_r Ptx r A ->
     wtt Ptx Ttx Gtx (re_Res re l) (rt_Record r) (sexp_anno ee  A )
 | wtt_Select : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (l:i) (rt5:rt) (ee:sexp) (r:rtyp) (A:sty),
     wtt Ptx Ttx Gtx re (rt_Record (r_Merge (r_SingleField l rt5) r)) ee ->
     trans_rt Ptx rt5 A ->
     wtt Ptx Ttx Gtx (re_Selection re l) rt5 (sexp_proj  ( (sexp_anno ee (sty_rcd l  A )) )  l)

 | wtt_AllI : forall (L:vars) (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (R:rlist) (re:rexp) (rt5:rt) (ee:sexp) (A:sty),
     wfcl Ttx R ->
     trans_rlist Ptx R A ->
     ( forall a b , a \notin  L  ->
               b \notin L \u {{a}} ->
               wtt  ((a~b) ++ Ptx) (( a ~ R )++ Ttx )  Gtx
                    ( open_rexp_wrt_rtyp re (r_TyVar_f a) )
                    ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )
                    (open_sexp_wrt_sty  ( open_sexp_wrt_sty_rec 1 (sty_var_f a) ee) (sty_var_f b) ) ) ->
     wtt Ptx Ttx Gtx (re_ConTyAbs R re) (rt_ConQuan R rt5) (sexp_tabs  A (sexp_tabs A  ee))
 | wtt_AllE : forall (Ptx:PContext) (Ttx:TContext) (Gtx:GContext) (re:rexp) (r:rtyp) (rt5:rt) (ee:sexp) (R:rlist) (A B : sty),
     wtt Ptx Ttx Gtx re (rt_ConQuan R rt5) ee ->
     cmpList Ttx r R ->
     trans_r Ptx r A ->
     bot_trans_r Ptx r B ->
     wtt Ptx Ttx Gtx (re_ConTyApp re r)  (open_rt_wrt_rtyp  rt5   r )  (sexp_tapp (sexp_tapp ee A) B ).

Hint Constructors bot_trans_r trans_rt trans_r trans_rlist.

Scheme trans_rt_ind' := Induction for trans_rt Sort Prop
  with trans_r_ind'  := Induction for trans_r  Sort Prop
  with trans_rlist_ind'  := Induction for trans_rlist Sort Prop.
Combined Scheme trans_rt_mutind from trans_rt_ind', trans_r_ind', trans_rlist_ind'.

Scheme wfrt_ind' := Induction for wfrt Sort Prop
  with wfr_ind'  := Induction for wfr  Sort Prop
  with wfcl_ind'  := Induction for wfcl Sort Prop.
Combined Scheme wfrt_mutind from wfrt_ind', wfr_ind', wfcl_ind'.

Scheme teq_ind' := Induction for teq  Sort Prop
  with ceq_ind'  := Induction for ceq Sort Prop.
Combined Scheme teq_ceq_mutind from teq_ind', ceq_ind'.


(* ********************************************************************** *)
(** * Existence *)

Lemma wfp_binds : forall a R Ttx Ptx,
  binds a R Ttx ->
  wfp Ttx Ptx ->
  exists b, binds a b Ptx.
Proof with auto.
  introv BD TR. inductions TR.
  false.
  analyze_binds BD...
  exists b...
  forwards ~ (? & ?) : IHTR.
  eexists...
  eapply binds_app_3... eassumption...
Qed.

Lemma trans_Ptx_binds : forall a b Ptx Ttx DD,
  binds a b Ptx ->
  trans_Ttx Ptx Ttx DD ->
  exists A, binds b A DD.
Proof with auto.
  introv BD TR. inductions TR.
  false.
  apply binds_cons_1 in BD.
  destruct BD as [[I1 I2]| I3].
    subst. exists A...
    forwards ~ (? & ?) : IHTR I3.
    exists x...
Qed.

Lemma trans_Ttx_binds : forall a R Ttx Ptx DD,
  binds a R Ttx ->
  trans_Ttx Ptx Ttx DD ->
  exists A, binds a A DD.
Proof with auto.
  introv BD TR. inductions TR.
  false.
  apply binds_cons_1 in BD.
  destruct BD as [[I1 I2]| I3].
    subst. exists A...
    forwards ~ (? & ?) : IHTR I3.
    exists x...
Qed.

Lemma trans_Gtx_notin_dom : forall x Gtx Ptx GG,
  x `notin` dom Gtx ->
  trans_Gtx Ptx Gtx GG ->
  x `notin` dom GG.
Proof with eauto.
  introv NOTIN TR.
  induction TR...
Qed.

Lemma trans_Ttx_notin_dom : forall x Ttx Ptx DD,
  x `notin` dom Ttx ->
  trans_Ttx Ptx Ttx DD ->
  x `notin` fv_Ptx Ptx ->
  x `notin` dom DD.
Proof with eauto.
  introv NOTIN1 TR NOTIN2. inductions TR...
  simpl in NOTIN1. simpl in NOTIN2...
Qed.


Lemma bot_trans_renaming:
    (forall Ptx T A,
    bot_trans_r Ptx T A ->
    forall Ttx a b X Y G P,
      Ptx = G ++ [(a, b)] ++ P ->
      wfp Ttx Ptx ->
      bot_trans_r (G ++ [(X, Y)] ++ P)
                  (subst_rtyp_in_rtyp (r_TyVar_f X) a T)
                  (subst_sty_in_sty (sty_var_f Y) b (subst_sty_in_sty (sty_var_f X) a A))).
Proof with eauto.
  introv Trans.
  induction Trans; introv Eq WFP; simpls...

  - Case "var".
    substs.

    analyze_binds_uniq H...

    + SCase "(a, b) in G".
      simpl_env in *.
      assert (a <> a0); auto.
      assert (b <> a0).
        eapply wfp_binds_neq...
      case_if. case_if.
      simpls.
      assert (b <> b0).
        eapply wfp_binds_range_neq...
      case_if...

    + SCase "a = a0, b = b0".
      substs.
      case_if.
      assert (b0 <> a0).
        eapply wfp_binds_neq...
      case_if.
      simpls.
      case_if...

    + SCase "(a, b) in P".
      assert (a <> a0); auto.
      assert (b <> a0).
        eapply wfp_binds_neq...
      case_if.
      case_if.
      simpls.
      assert (b <> b0).
        eapply wfp_binds_range_neq...
      case_if...

  - Case "record".
    constructor...
    eapply subst_rtyp_in_rt_lc_rt...
Qed.


Lemma trans_renaming_general :
  (forall Ptx T A,
    trans_rt Ptx T A ->
    forall Ttx a b X Y G P,
      Ptx = G ++ [(a, b)] ++ P ->
      wfp Ttx Ptx ->
      X <> b ->
      trans_rt (G ++ [(X, Y)] ++ P)
               (subst_rtyp_in_rt (r_TyVar_f X) a T)
               (subst_sty_in_sty (sty_var_f Y) b (subst_sty_in_sty (sty_var_f X) a A)))
  /\
  (forall Ptx r A,
      trans_r Ptx r A ->
    forall Ttx a b X Y G P,
      Ptx = G ++ [(a, b)] ++ P ->
      wfp Ttx Ptx ->
      X <> b ->
      trans_r (G ++ [(X, Y)] ++ P)
              (subst_rtyp_in_rtyp (r_TyVar_f X) a r)
              (subst_sty_in_sty (sty_var_f Y) b (subst_sty_in_sty (sty_var_f X) a A)))
/\  (forall Ptx rl A,
    trans_rlist Ptx rl A ->
    forall Ttx a b X Y G P,
      Ptx = G ++ [(a, b)] ++ P ->
      wfp Ttx Ptx ->
      X <> b ->
      trans_rlist (G ++ [(X, Y)] ++ P)
                  (subst_rtyp_in_rlist (r_TyVar_f X) a rl)
                  (subst_sty_in_sty (sty_var_f Y) b (subst_sty_in_sty (sty_var_f X) a A))).
Proof with eauto using wfp_uniq.
  apply trans_rt_mutind; simpls...


  + introv RLIST FACT1 FACT2 FACT3 Binds WFP1 WFP2.
    simpl_env in *.
    substs.

    pick fresh d and apply trans_rt_all...

    - Case "rlist".
      eapply FACT1...

    - Case "body".
      intros c Fr2.

      specialize FACT3 with (b0 := d) (a0 := c) (Ttx := (c, R_Empty) :: Ttx) (a1 := a) (b1 := b) (X := X) (Y := Y) (G0 := (c, d) :: G) (P0 := P).
      forwards~ IMP : FACT3.
      constructor~.

      rewrite fv_Ptx_union...
      rewrite fv_Ptx_union...

      rewrite subst_rtyp_in_rt_open_rt_wrt_rtyp in IMP...
      simpl in IMP. assert (c <> a) by auto. case_if...
      rewrite subst_sty_in_sty_open_sty_wrt_sty in IMP...
      simpl in IMP. assert (d <> a) by auto. case_if...
      rewrite subst_sty_in_sty_open_sty_wrt_sty in IMP...
      simpl in IMP. assert (d <> b) by auto. case_if...
      rewrite subst_sty_in_sty_open_sty_wrt_sty_rec in IMP...
      rewrite subst_sty_in_sty_open_sty_wrt_sty_rec in IMP...
      simpl in IMP. case_if...
      simpl in IMP. assert (c <> b) by auto. case_if...


  + introv Binds Eq WFP1 WFP2.
    simpl_env in *.
    substs.

    analyze_binds_uniq Binds...
    - Case "(a, b) in G".
      case_if; substs; simpls; try solve_notin.
      assert (b0 <> a).
        eapply wfp_binds_neq...
      case_if; substs; simpls; try solve_notin...

    - Case "a = a0, b = b0".
      substs; case_if; simpls...
      case_if...

    - Case "(a, b) in P".
      case_if; substs; simpls; try solve_notin.
      assert (b0 <> a).
        eapply wfp_binds_neq...
      case_if; substs; simpls; try solve_notin...


  + introv RTRANS FACT1 BTRANS FACT2 FACT3 Binds WFP1 WFP2.
    econstructor...
    eapply bot_trans_renaming...

Qed.


Lemma trans_rt_renaming : forall Ttx a b X Y G P A T,
    trans_rt (G ++ [(a, b)] ++ P) T A ->
    wfp Ttx (G ++ [(a, b)] ++ P) ->
    X <> b ->
    trans_rt (G ++ [(X, Y)] ++ P)
             (subst_rtyp_in_rt (r_TyVar_f X) a T)
             (subst_sty_in_sty (sty_var_f Y) b (subst_sty_in_sty (sty_var_f X) a A)).
Proof.
  intros.
  pose (proj1 trans_renaming_general) as I.
  eapply I; eauto.
Qed.


Lemma trans_rt_open_renaming : forall X Y a b Ttx Ptx rt5 T,
    b \notin fv_sty_in_sty T \u singleton a \u singleton X ->
    a \notin fv_rtyp_in_rt rt5 \u fv_sty_in_sty T ->
    wfp Ttx ([(a, b)] ++ Ptx) ->
    trans_rt ([(a, b)] ++ Ptx) (open_rt_wrt_rtyp rt5 (r_TyVar_f a))
             (open_sty_wrt_sty  (open_sty_wrt_sty_rec 1 (sty_var_f a) T) (sty_var_f b)) ->
    trans_rt ([(X, Y)] ++ Ptx) (open_rt_wrt_rtyp rt5 (r_TyVar_f X))
             (open_sty_wrt_sty (open_sty_wrt_sty_rec 1 (sty_var_f X) T) (sty_var_f Y) ).
Proof with eauto.
  introv Fr Fr2 WFP Orig.
  destruct (X == a); substs...

  - Case "X == a".
    destruct (Y == b); substs...
    + SCase "Y <> b".
      rewrite (subst_rtyp_in_rt_intro a)...
      rewrite (subst_sty_in_sty_intro b)...
      rewrite (subst_sty_in_sty_intro_rec _ a)...
      rewrite subst_sty_in_sty_open_sty_wrt_sty_var...

      rewrite_env (nil ++ [(a, Y)] ++ Ptx).
      eapply trans_rt_renaming...
      rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_upper; simpls...

  - Case "X <> a".
    destruct (Y == b); substs...
    + SCase "Y == b".

      rewrite (subst_rtyp_in_rt_intro a)...
      rewrite (subst_sty_in_sty_intro b)...
      rewrite (subst_sty_in_sty_intro_rec _ a)...
      rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
      rewrite_env (nil ++ [(X, b)] ++ Ptx).
      eapply trans_rt_renaming...
      rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_upper; simpls...

    + SCase "Y <> b".
      rewrite (subst_rtyp_in_rt_intro a)...
      rewrite (subst_sty_in_sty_intro b)...
      rewrite (subst_sty_in_sty_intro_rec _ a)...
      rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
      rewrite_env (nil ++ [(X, Y)] ++ Ptx).
      eapply trans_rt_renaming...
      rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_upper; simpls...

Qed.


Lemma bot_trans_r_exists : forall Ttx Ptx r,
  wfr Ttx r ->
  wfp Ttx Ptx ->
  exists A, bot_trans_r Ptx r A
with trans_r_exists : forall Ttx Ptx r,
  wfr Ttx r ->
  wfp Ttx Ptx ->
  exists A, trans_r Ptx r A
with trans_rt_exists : forall Ttx Ptx rt,
  wfrt Ttx rt ->
  wfp Ttx Ptx ->
  exists A, trans_rt Ptx rt A
with trans_rlist_exists : forall Ttx Ptx rl,
  wfcl Ttx rl ->
  wfp Ttx Ptx ->
  exists A, trans_rlist Ptx rl A.
Proof with eauto.
  -
  introv WR WP.  inductions WR.
    +
    forwards ~ (? & ?): wfp_binds H WP.
    exists (sty_var_f x). apply bot_trans_r_var...
    + exists (sty_rcd l sty_bot)...
      constructor...
      eapply lc_rt_from_wfrt...
    + exists sty_top...
    + forwards ~ (I1 & ? ) : IHWR1.
      forwards ~ (I2 & ? ) : IHWR2.
      exists (sty_and I1 I2)...

  -
  introv WR WP. inductions WR.
    + exists (sty_var_f a)...
      forwards (? & ?) : wfp_binds H WP...
    + forwards ~ (I1 & ?) : trans_rt_exists H WP.
      exists (sty_rcd l I1)...
    + exists sty_top...
    + forwards ~ (I1 & ? ) : IHWR1.
      forwards ~ (I2 & ? ) : IHWR2.
      exists (sty_and I1 I2)...

  -
  introv WR WP. gen Ptx. induction WR; introv WP.
    + exists (sty_nat)...
    + forwards ~ (I1 & ? ) : IHWR1 Ptx.
      forwards ~ (I2 & ? ) : IHWR2 Ptx.
      exists (sty_arrow I1 I2)...
    + Case "ConQuan".
      forwards (B & Imp1) : trans_rlist_exists Ttx Ptx R; auto.

      pick fresh a.
      pick fresh b.
      forwards (A & Imp2) : H1 a ([(a, b)] ++ Ptx); auto.
      constructor...
      eapply lc_rlist_from_wfcl...
      exists (sty_all B (sty_all B (close_sty_wrt_sty_rec 1 a (close_sty_wrt_sty_rec 0 b A)))).
      pick fresh Y and apply trans_rt_all; auto.
      intros X Fr2.

      eapply trans_rt_open_renaming with (b := b) (a := a) (Ttx := [(a, R_Empty)] ++ Ttx)...
      rewrite fv_sty_in_sty_close_sty_wrt_sty_rec.
      rewrite fv_sty_in_sty_close_sty_wrt_sty_rec.
      solve_notin.
      rewrite fv_sty_in_sty_close_sty_wrt_sty_rec.
      solve_notin.
      rewrite open_sty_wrt_sty_rec_close_sty_wrt_sty_rec.
      unfold open_sty_wrt_sty.
      rewrite open_sty_wrt_sty_rec_close_sty_wrt_sty_rec...

    + forwards ~ (I & ?) : trans_r_exists H WP.
      exists I...

  - introv WR WP. inductions WR.
    + exists (sty_top)...
    + forwards ~ (I1 & ? ) : trans_r_exists H WP.
      forwards ~ (I2 & ? ) : bot_trans_r_exists H WP.
      forwards ~ (I3 & ? ) : IHWR.
      exists (sty_and (sty_and I1 I2) I3)...
Qed.

(* ********************************************************************** *)
(** * Wellformedness *)



Lemma wtt_regular : forall Ptx Ttx Gtx re rt E,
    wtt Ptx Ttx Gtx re rt E ->
    wftc Ttx /\ wfc Ttx Gtx /\ wfp Ttx Ptx /\ wfrt Ttx rt.
Proof with eauto using empty_cmp.
  induction 1; repeat destruct_hypo; splits...
  +
  eapply wfrt_from_binds_wfc...
  + pick fresh X. forwards ~ : H1 X. repeat destruct_hypo...
  + pick fresh X. forwards ~ : H1 X. repeat destruct_hypo...
    inverts H5...
  + pick fresh X. forwards ~ : H1 X. repeat destruct_hypo...
  + pick fresh X. forwards ~ : H1 X. repeat destruct_hypo...
  + inverts H8...
  + inversions H4... inversions H7...
  + inversions H4... inversions H7... inversions H6... 
  + pick fresh X. pick fresh Y. forwards ~ : H2 X Y. repeat destruct_hypo...
    inverts H3...
  + pick fresh X. pick fresh Y. forwards ~ : H2 X Y. repeat destruct_hypo...
    rewrite_env (map (subst_rtyp_in_rlist r_Empty X) nil ++ Ttx).
    assert (Eq : Gtx = map (subst_rtyp_in_rt r_Empty X) Gtx).
      eapply map_subst_rtyp_in_binding_id...
    rewrite Eq. clear Eq.
    eapply wfc_subst_tb; simpls...
    simpl_env in *.
    eapply wftc_strength...
  + pick fresh X. pick fresh Y. forwards ~ : H2 X Y. repeat destruct_hypo...
    inverts H5...
  + pick fresh X and apply wfrt_All.
      pick fresh X. pick fresh Y. forwards ~ : H2 X Y.
      pick fresh Y. forwards ~ : H2 X Y. repeat destruct_hypo...
  + forwards ~ : cmpList_wfr H0...
    inverts H6.
    pick fresh X.
    forwards ~ : H12 X.
    Search (subst_rtyp_in_rt (open_rt_wrt_rtyp _ _)).
    unfold open_rt_wrt_rtyp.
    rewrite subst_rtyp_in_rt_intro_rec with (a1:=X)...
    rewrite_env (map (subst_rtyp_in_rlist r X) nil ++ Ttx).
    eapply wfrt_subst...
    simpl... constructor...
Qed.

Lemma bot_trans_r_regular : forall Ptx Ttx r A DD,
    wfr Ttx r ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r A ->
    swft DD A.
Proof with eauto.
  introv WF TT TR  . generalize dependent A.
  inductions WF; introv TR; inverts TR...
  forwards ~ (? & ?) : trans_Ptx_binds H2 TT...
Qed.


Lemma trans_regular_general :
  (forall Ttx rt, wfrt Ttx rt ->
      forall  Ptx A DD,
        trans_Ttx Ptx Ttx DD ->
        trans_rt Ptx rt A ->
        swft DD A)
  /\ (forall Ttx r , wfr Ttx r ->
        forall Ptx A DD,
          trans_Ttx Ptx Ttx DD ->
          trans_r Ptx r A ->
          swft DD A)
  /\ (forall Ttx R, wfcl Ttx R ->
        forall Ptx A DD,
          trans_Ttx Ptx Ttx DD ->
          trans_rlist Ptx R A ->
          swft DD A)
.
Proof with eauto.
  apply wfrt_mutind.
  + introv TT TR. inverts TR...
  + introv WF IHWF1 TR IHWF2 TT TR2.
    inverts TR2.
    forwards ~ : IHWF1 TT H2.
    forwards ~ : IHWF2 TT H4.
  + introv WF RLIST IH1 IH2 TT TR. inverts TR.
    pick fresh X and apply swft_all... unfold open_sty_wrt_sty.
    assert (I: (open_sty_wrt_sty_rec 0 (sty_var_f X) B) = B).
      change (open_sty_wrt_sty_rec 0 (sty_var_f X) B)
        with (open_sty_wrt_sty B (sty_var_f X))...
      rewrite open_sty_wrt_sty_lc_sty...
    simpl. pick fresh Y and apply swft_all...
    rewrite I.
      forwards ~ : RLIST TT H2.
      assert (swft ((X ~ B) ++ DD) B); auto. apply swft_weaken_head...
    rewrite I. forwards ~ I2 : H4 Y X.
    assert (I3: trans_Ttx ((X~ Y) ++ Ptx) ((X~ R)++Ttx) ((Y~B)++(X~B)++DD)).
      constructor; auto.
    simpl in I3.
    simpl in IH2.
    forwards ~ : IH2 I2. exact I3.
    simpl...
  + introv WR TRANSR TT TR. inverts TR.
    forwards ~ : TRANSR TT H1.

  + introv BD TT TR. inverts TR; auto.
    forwards ~ (? & ?): trans_Ttx_binds BD TT...
  + introv WF TRANSRT TT TR. inverts TR.
    forwards ~ : TRANSRT TT H3.
  + introv TT TR. inverts TR...
  + introv WF1 IHWF1 WF2 IHWF2 CMP TT TR.
    inverts TR.
    forwards ~ : IHWF1 TT H2.
    forwards ~ : IHWF2 TT H4.

  + introv WF TT TR. inverts TR...
  + introv WF TRANSR WFCL TRANSRLIST TT TR; inverts TR; auto.
  forwards ~ : TRANSR TT H1.
  forwards ~ : bot_trans_r_regular TT H3.
  forwards ~ : TRANSRLIST TT H5.
Qed.

Lemma trans_rt_regular: forall Ttx rt Ptx A DD,
    wfrt Ttx rt ->
    trans_Ttx Ptx Ttx DD ->
    trans_rt Ptx rt A ->
    swft DD A.
Proof.
  introv H1 H2 H3.
  pose (proj1 trans_regular_general) as I.
  forwards ~ : I H1 H2 H3.
Qed.

Lemma trans_r_regular: forall Ttx r Ptx A DD,
    wfr Ttx r ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx r A ->
    swft DD A.
Proof.
  introv H1 H2 H3.
  pose (proj1 (proj2 trans_regular_general)) as I.
  forwards ~ : I H1 H2 H3.
Qed.

Lemma trans_rlist_regular : forall Ttx R Ptx A DD,
   wfcl Ttx R ->
   trans_Ttx Ptx Ttx DD ->
   trans_rlist Ptx R A ->
   swft DD A.
Proof.
  introv H1 H2 H3.
  pose (proj2 (proj2 trans_regular_general)) as I.
  forwards ~ : I H1 H2 H3.
Qed.

Lemma trans_Ttx_regular : forall Ptx Ttx DD,
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    swfte DD.
Proof with eauto.
  introv WF TR. generalize dependent DD.
  generalize dependent Ptx.
  inductions WF; introv TR; inverts TR...
  constructor...
  constructor...
  eapply trans_rlist_regular...
  apply swft_weaken_head.
  eapply trans_rlist_regular...
Qed.


Lemma trans_Gtx_regular : forall Ptx Ttx Gtx DD GG,
    wfc Ttx Gtx ->
    trans_Ttx Ptx Ttx DD ->
    trans_Gtx Ptx Gtx GG ->
    swfe DD GG.
Proof with eauto.
  introv WF TRD TRG.
  generalize dependent DD.
  generalize dependent GG.
  inductions WF; introv TRG TRD.
  inverts TRG; inverts TRD...
  inverts TRG. constructor...
  forwards ~ : trans_rt_regular H TRD H8.
  eapply trans_Gtx_notin_dom...
  forwards ~ : trans_Ttx_notin_dom H0 TRD H9.
Qed.

Lemma bot_trans_r_lc_rtyp : forall R Ptx A,
    bot_trans_r Ptx R A ->
    lc_rtyp R /\ lc_sty A.
Proof.
  induction 1; repeat destruct_hypo; splits; eauto.
Qed.

Lemma trans_rlist_lc_rlist : forall R Ptx A,
    trans_rlist Ptx R A ->
    lc_rlist R /\ lc_sty A
with trans_r_lc_rtyp : forall R Ptx A,
    trans_r Ptx R A ->
    lc_rtyp R /\ lc_sty A
with trans_rt_lc_rt : forall R Ptx A,
    trans_rt Ptx R A ->
    lc_rt R /\ lc_sty A.
Proof with auto.
  induction 1; auto; repeat destruct_hypo.
  splits; constructor...
  forwards ~ : trans_r_lc_rtyp H. destruct_hypo...
  constructor...
  forwards ~ : trans_r_lc_rtyp H. destruct_hypo...
  forwards ~ : bot_trans_r_lc_rtyp H0.
  destruct_hypo...

  induction 1; auto; repeat destruct_hypo...
  forwards ~ : trans_rt_lc_rt H. repeat destruct_hypo...

  induction 1; auto; repeat destruct_hypo...
  forwards ~ : trans_rlist_lc_rlist H. destruct_hypo...
  pick_fresh X. pick_fresh Y. forwards ~ : H1 X Y. clear Fr Fr0.
  destruct_hypo...
  splits...
  forwards ~ : lc_rt_ConQuan_exists H2 H4.
  assert (lc_sty (open_sty_wrt_sty (sty_all B A) (sty_var_f Y))).
  unfold open_sty_wrt_sty. simpl.
  assert ((open_sty_wrt_sty B (sty_var_f Y)) = B).
    apply open_sty_wrt_sty_lc_sty...
  unfold open_sty_wrt_sty in H6. rewrite H6.
  eapply lc_sty_all_exists... exact H5.
  eapply lc_sty_all_exists... exact H6.

  forwards ~ : trans_r_lc_rtyp H.
  destruct_hypo...
Qed.

Lemma trans_Ttx_wfp : forall Ptx Ttx DD,
    trans_Ttx Ptx Ttx DD ->
    wfp Ttx Ptx.
Proof with eauto.
  induction 1...
  constructor...
  forwards ~ : trans_rlist_lc_rlist H0.
  destruct_hypo...
Qed.

Hint Extern 1 (wfp ?T ?P) =>
match goal with
| H : trans_Ttx P T _ |- _ => apply (trans_Ttx_wfp H)
end.

Hint Extern 1 (uniq ?P) =>
match goal with
| H : trans_Ttx P _ _ |- _ => apply (wfp_uniq (trans_Ttx_wfp H))
end.

Hint Extern 1 (lc_rlist ?R) =>
match goal with
| H : trans_rlist _ R _ |- _ => apply (proj1 (trans_rlist_lc_rlist H))
end.

Hint Extern 1 (lc_rtyp ?R) =>
match goal with
| H : trans_r _ R _ |- _ => apply (proj1 (trans_r_lc_rtyp H))
| H : bot_trans_r _ R _ |- _ => apply (proj1 (bot_trans_r_lc_rtyp H))
end.

Hint Extern 1 (lc_rt ?R) =>
match goal with
| H : trans_rt _ R _ |- _ => apply (proj1 (trans_rt_lc_rt H))
end.

Hint Extern 1 (lc_sty ?R) =>
match goal with
| H : trans_rlist _ _ R |- _ =>   apply (proj2 (trans_rlist_lc_rlist H))
| H : bot_trans_r _ _ R  |- _ =>  apply (proj2 (bot_trans_r_lc_rtyp H))
| H : trans_r _ _ R  |- _ =>  apply (proj2 (trans_r_lc_rtyp H))
| H : trans_rt _ _ R |- _ =>  apply (proj2 (trans_rt_lc_rt H))
end.


(* ********************************************************************** *)
(** * Unicity *)

Lemma bot_trans_r_uniq : forall Ptx r A B,
    uniq Ptx ->
    bot_trans_r Ptx r A ->
    bot_trans_r Ptx r B ->
    A = B.
Proof with eauto.
  introv UNIQ TR1 TR2.
  generalize dependent B.
  inductions TR1; introv TR2;inversions TR2...
  f_equal~. eapply binds_unique...
  f_equal...
Qed.


Lemma trans_uniq_general :
  (forall Ptx rt A,
    trans_rt Ptx rt A ->
    forall B, uniq Ptx ->
         trans_rt Ptx rt B ->
         A = B)
  /\
  (forall Ptx r A,
      trans_r Ptx r A ->
      forall B, uniq Ptx ->
           trans_r Ptx r B ->
           A = B)
/\  (forall Ptx rl A,
    trans_rlist Ptx rl A ->
    forall B,
      uniq Ptx ->
      trans_rlist Ptx rl B ->
      A = B).
Proof with eauto.
  apply trans_rt_mutind.
  + introv UNIQ TR2. inverts TR2...
  + introv TR1 IH1 TR2 IH2 UNIQ TR.
    inverts TR. f_equal...
  + introv TR1 IH1 HY IH2 UNIQ TR2. inverts TR2.
    forwards ~ : IH1 TR1. f_equal... f_equal...
    pick fresh X. pick fresh Y. forwards ~ : IH2 X Y H4.
    apply open_sty_wrt_sty_rec_inj in H0...
    apply open_sty_wrt_sty_rec_inj in H0...
    apply fv_notin_open_sty_wrt_sty_rec...
    apply fv_notin_open_sty_wrt_sty_rec...
  + introv TR IH1 UNIQ TR2. inverts TR2.
    forwards ~ : IH1 UNIQ H1.

  + introv UNIQ TR. inverts TR...
  + introv BD UNIQ TR1. inverts TR1...
  + introv TR1 IH UNIQ TR2. inverts TR2... f_equal...
  + introv TR1 IH1 TR2 IH2 UNIQ TR. inverts TR...
    f_equal...
  + introv UNIQ TRANSRLIST. inverts TRANSRLIST...
  + introv TR1 IH1 TR2 TR3 IH2 UNIQ TR. inverts TR.
  f_equal... f_equal...
  forwards ~ : IH1 H1.
  forwards ~ : bot_trans_r_uniq TR2 H3.
Qed.

Lemma trans_rt_uniq : forall Ptx rt A B,
    uniq Ptx ->
    trans_rt Ptx rt A ->
    trans_rt Ptx rt B ->
    A = B.
Proof.
  pose (proj1 trans_uniq_general) as I.
  introv H1 H2 H3.
  forwards ~ : I H2 H1 H3.
Qed.

Lemma trans_r_uniq : forall Ptx r A B,
    uniq Ptx ->
    trans_r Ptx r A ->
    trans_r Ptx r B ->
    A = B.
Proof.
  pose (proj1 (proj2 trans_uniq_general)) as I.
  introv H1 H2 H3.
  forwards ~ : I H2 H1 H3.
Qed.

Lemma trans_rlist_uniq : forall Ptx rl A B,
    uniq Ptx ->
    trans_rlist Ptx rl A ->
    trans_rlist Ptx rl B ->
    A = B.
Proof.
  pose (proj2 (proj2 trans_uniq_general)) as I.
  introv H1 H2 H3.
  forwards ~ : I H2 H1 H3.
Qed.

Lemma trans_Ttx_uniq : forall Ptx ttx s1 s2,
    uniq Ptx ->
    trans_Ttx Ptx ttx s1 ->
    trans_Ttx Ptx ttx s2 ->
    s1 = s2.
Proof with eauto.
  introv UNI TR1 TR2.
  generalize dependent s2.
  inductions TR1; introv TR2; inverts TR2...
  forwards ~ : trans_rlist_uniq H H9.
  forwards ~ : IHTR1 H7.
  substs...
Qed.

Lemma trans_Gtx_uniq : forall Ptx gtx s1 s2,
    uniq Ptx ->
    trans_Gtx Ptx gtx s1 ->
    trans_Gtx Ptx gtx s2 ->
    s1 = s2.
Proof with eauto.
  introv UNI TR1 TR2.
  generalize dependent s2.
  inductions TR1; introv TR2; inverts TR2...
  forwards ~ : IHTR1 H5...
  forwards ~ : trans_rt_uniq H H7.
  substs...
Qed.


(* ********************************************************************** *)
(** * TRANSLATION OF EQUIVALENCE *)

Ltac destruct_exists :=
  match goal with
  | H: exists _, _ |- _ => destruct H as (? & ?)
  end.


Lemma bot_trans_teq: forall Ttx Ptx r1 r2 A B DD,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r1 A ->
    bot_trans_r Ptx r2 B ->
    sub DD A B /\ sub DD B A.
Proof with eauto.
    introv EQ TRT TR1 TR2.
    generalize dependent Ptx. generalize dependent DD.
    generalize dependent A. generalize dependent B.
    inductions EQ; introv TRT TR1 TR2.

    +
      forwards ~ : bot_trans_r_uniq TR1 TR2. substs.
      inversions H.
      forwards ~ : bot_trans_r_regular H2 TRT TR1.
    + forwards ~ : IHEQ TRT TR2 TR1.
      destruct_hypo.
      splits...
    + forwards ~ : teq_record_l EQ1. destruct_exists.
      forwards ~ : teq_record_r EQ2. destruct_exists. substs.  inversions H0.
      assert (I1: wfr Ttx x0). apply teq_regular in EQ1.
        destruct_hypo. inversions H0...
      forwards ~ I2 : trans_Ttx_wfp TRT.
      forwards ~ I3 : bot_trans_r_exists  I1 I2.
      destruct_exists.
      forwards ~ : IHEQ1 r1 x0 TRT TR1 H.
      forwards ~ : IHEQ2 x0 r2 TRT H TR2.
      repeat destruct_hypo. split...
    + inversions TR1. inversions TR2.
      split...
    + inversions TR1. inversions TR2.
      forwards ~ : IHEQ1 r0 r1' TRT H4 H5.
      forwards ~ : IHEQ2 r3 r2' TRT H6 H8.
      repeat destruct_hypo.
      split.
      apply sub_and...
      apply sub_and...
    + inversions TR1.
      inversions H5.
      forwards ~ : bot_trans_r_uniq TR2 H3. substs.
      assert (swft DD A0).
      forwards ~ : bot_trans_r_regular TRT TR2.
      splits. apply S_andl...
      apply S_and...
    + inversions TR1. inversions H7.
      inversions TR2. inversions H7.
      forwards ~ : bot_trans_r_uniq H9 H10.
      forwards ~ : bot_trans_r_uniq H6 H12.
      forwards ~ : bot_trans_r_uniq H5 H8.
      substs. clear H5 H6 H9.
      assert (swft DD A2).
        forwards ~ :bot_trans_r_regular TRT H8.
      assert (swft DD B).
        forwards ~ :bot_trans_r_regular TRT H12.
      assert (swft DD B0).
        forwards ~ :bot_trans_r_regular TRT H10.
      split . apply S_and. apply S_and.
      apply S_andl...
      apply S_trans with (sty_and B B0)...
      apply S_trans with (sty_and B B0)...
      apply S_and. 
      apply S_trans with (sty_and A2 B)...
      apply S_and. 
      apply S_trans with (sty_and A2 B)...
      apply S_andr...
    + inversions TR1. inversions TR2.
      forwards ~ : bot_trans_r_uniq H4 H5.
      forwards ~ : bot_trans_r_uniq H3 H7.
      substs.
      assert (swft DD B0).
        forwards ~ :bot_trans_r_regular TRT H4.
      assert (swft DD B1).
        forwards ~ :bot_trans_r_regular TRT H7.
        split...
Qed.

Lemma trans_teq_ceq :
  (forall Ttx  rt1 rt2,
      teq Ttx rt1 rt2 ->
      forall Ptx A B DD,
        trans_Ttx Ptx Ttx DD ->
        trans_rt Ptx rt1 A ->
        trans_rt Ptx rt2 B ->
        sub DD A B /\ sub DD B A)
  /\
  (
    forall Ttx R1 R2,
      ceq Ttx R1 R2 ->
      forall Ptx A B DD,
        trans_Ttx Ptx Ttx DD ->
        trans_rlist Ptx R1 A ->
        trans_rlist Ptx R2 B ->
        sub DD A B /\ sub DD B A)
.
Proof with auto.
  apply teq_ceq_mutind.
    + introv WF TRT TR1 TR2.
      forwards ~ : trans_rt_uniq TR1 TR2.
      substs.
      forwards ~ : trans_rt_regular TRT TR1.
    + introv EQ IHEQ TRT TR1 TR2.
      forwards ~ : IHEQ TRT TR2 TR1.
      destruct_hypo. splits...
    + introv EQ1 IHEQ1 EQ2 IHEQ2 TRT TR1 TR2.
      assert (I1: wfrt Ttx rt'). apply teq_regular in EQ1.
        destruct_hypo...
      forwards ~ I2 : trans_Ttx_wfp TRT.
      forwards ~ I3 : trans_rt_exists  I1 I2.
      destruct_exists.
      forwards ~ : IHEQ1 x TRT TR1 H.
      forwards ~ : IHEQ2 x TRT H TR2.
      repeat destruct_hypo. split; eauto...
    + introv EQ1 IH1 EQ2 IH2 TRT TR1 TR2.
      inversions TR1. inversions TR2.
      forwards ~ : IH1 TRT H2 H3.
      forwards ~ : IH2 TRT H4 H6.
      repeat destruct_hypo.
      splits...
    + introv EQ IH1 IH2 IH3 IH4 IH5 TRT TR1 TR2.
      inversions TR1. inversions TR2.
      forwards ~ : IH1 TRT H2 H3. destruct_hypo. clear IH1.
      assert (HH1: swft DD B1). forwards ~ : trans_rlist_regular  TRT H3.
      assert (HH2: swft DD B0). forwards ~ : trans_rlist_regular  TRT H2.
      split.
      *
      pick fresh X and apply S_forall...
      unfold open_sty_wrt_sty. simpl.
      pick fresh Y and apply S_forall...
      forwards ~ : H4 Y X.
      forwards ~ : H6 Y X. clear H4 H6.
      simpl in H1.
      assert (I: trans_Ttx ((X, Y) :: Ptx) ((X, R) :: Ttx) ((Y ~ B0) ++ (X ~ B0) ++ DD)).
        constructor...
      forwards ~ : IH3 I H1 H5.
      clear Fr Fr0. destruct_hypo.
      apply sub_change with ([(Y, B0)] ++ [(X, B0)] ++ DD)...
      constructor... constructor...
      change (open_sty_wrt_sty_rec 0 (sty_var_f X) B1) with
        (open_sty_wrt_sty B1 (sty_var_f X)).
      change (open_sty_wrt_sty_rec 0 (sty_var_f X) B0) with
        (open_sty_wrt_sty B0 (sty_var_f X)).
      rewrite open_sty_wrt_sty_lc_sty...
      rewrite open_sty_wrt_sty_lc_sty...
      rewrite_env (nil ++ (X ~ B1) ++ DD)...
      apply sub_weakening. simpl...
      *
      pick fresh X and apply S_forall...
      unfold open_sty_wrt_sty. simpl.
      pick fresh Y and apply S_forall...
      forwards ~ : H4 Y X.
      forwards ~ : H6 Y X. clear H4 H6.
      simpl in H1.
      assert (I: trans_Ttx ((X, Y) :: Ptx) ((X, R) :: Ttx) ((Y ~ B0) ++ (X ~ B0) ++ DD)).
        constructor...
      forwards ~ : IH3 I H1 H5.
      clear Fr Fr0. destruct_hypo.
      apply sub_change with ([(Y, B0)] ++ [(X, B0)] ++ DD)...
      change (open_sty_wrt_sty_rec 0 (sty_var_f X) B1) with
        (open_sty_wrt_sty B1 (sty_var_f X)).
      change (open_sty_wrt_sty_rec 0 (sty_var_f X) B0) with
        (open_sty_wrt_sty B0 (sty_var_f X)).
      rewrite open_sty_wrt_sty_lc_sty...
      rewrite open_sty_wrt_sty_lc_sty...
      rewrite_env (nil ++ (X ~ B0) ++ DD)...
      apply sub_weakening. simpl...
    + introv EQ IH1 TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H2.
      forwards ~ : IH1 TRT H5 H4. destruct_hypo.
      splits; eauto.
    + introv EQ1 IH1 EQ2 IH2 CMP1 CMP2 TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H2.
      forwards ~ : IH1 A0 A TRT... destruct_hypo.
      forwards ~ : IH2 B0 B1 TRT. destruct_hypo.
      splits;  apply sub_and...
    + introv WF TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H6.
      forwards ~ : trans_r_uniq H2 H4. substs.
      assert (swft DD A0).
        forwards ~ : trans_r_regular TRT H2.
      splits; eauto.
    + introv CMP1 CMP2 CMP3 TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H2.
      inverts H3. inverts H6.
      forwards ~ : trans_r_uniq H3 H8. substs.
      forwards ~ : trans_r_uniq H7 H9. substs. clear H9.
      forwards ~ : trans_r_uniq H2 H4. substs. clear H4.
      assert (swft DD A0). forwards ~ : trans_r_regular TRT H2.
      assert (swft DD B). forwards ~ : trans_r_regular TRT H3.
      assert (swft DD B2). forwards ~ : trans_r_regular TRT H7.
      splits. apply S_and. apply S_and... apply S_trans with (sty_and B B2)...
      apply S_trans with (sty_and B B2)...
      apply S_and.  apply S_trans with (sty_and A0 B)...
      apply S_and; auto.  apply S_trans with (sty_and A0 B)...
    + introv CMP TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H2.
      forwards ~ : trans_r_uniq H4 H7. substs.
      forwards ~ : trans_r_uniq H3 H6. substs.
      assert (swft DD B0). forwards ~ : trans_r_regular TRT H3.
      assert (swft DD B1). forwards ~ : trans_r_regular TRT H7.
      splits...

    + introv WF TRT TR1 TR2.
      assert (swft DD B). forwards ~ : trans_rlist_regular WF TRT TR2.
      forwards ~ : trans_rlist_uniq TR1 TR2. substs...

    + introv EQ IH1 TRT TR1 TR2.
      forwards ~ : IH1 TRT TR2 TR1.
      destruct_hypo...
    + introv EQ1 IH1 EQ2 IH2 TRT TR1 TR2.
      assert (I1: wfcl Ttx R'). apply ceq_regular in EQ1.
        destruct_hypo...
      forwards ~ I2 : trans_Ttx_wfp TRT.
      forwards ~ I3 : trans_rlist_exists  I1 I2.
      destruct_exists.
      forwards ~ : IH1 TRT TR1 H.
      forwards ~ : IH2 TRT H TR2.
      repeat destruct_hypo. split; eauto...
    + introv EQ1 IH EQ2 IH2 TRT TR1 TR2.
      inversions TR1. inversions TR2.
      forwards ~ : IH2 A1 A0 TRT. destruct_hypo.
      forwards ~ : bot_trans_teq TRT H3 H6. destruct_hypo.
      forwards ~ : IH TRT H5 H8. destruct_hypo.
      splits.
      apply sub_and... apply sub_and...
      apply sub_and... apply sub_and...
    + introv WF1 WF2 WFCL TRT TR1 TR2.
      inversions TR1. inversions TR2.
      inversions H5. inversions H8.
      forwards ~ : bot_trans_r_uniq H3 H10. substs. clear H10.
      forwards ~ : bot_trans_r_uniq H6 H9. substs. clear H9.
      forwards ~ : trans_r_uniq H5 H1. substs. clear H5.
      forwards ~ : trans_r_uniq H2 H4. substs. clear H4.
      forwards ~ : trans_rlist_uniq H11 H13. substs. clear H13.
      assert (swft DD A5). forwards ~ : bot_trans_r_regular TRT H6.
      assert (swft DD A7). forwards ~ : bot_trans_r_regular TRT H3.
      assert (swft DD A4). forwards ~ : trans_r_regular TRT H2.
      assert (swft DD A1). forwards ~ : trans_r_regular TRT H1.
      assert (swft DD B0). forwards ~ : trans_rlist_regular TRT H11.
      split. apply S_and... apply S_trans with (sty_and (sty_and A4 A5) B0)...
      apply S_and... apply S_trans with (sty_and (sty_and A4 A5) B0)...
      apply S_and... apply S_trans with (sty_and (sty_and A1 A7) B0)...
      apply S_and... apply S_trans with (sty_and (sty_and A1 A7) B0)...
    + introv WFCL TRT TR1 TR2.
      inverts TR1.
      inverts H3. inverts H1.
      forwards ~ : trans_rlist_uniq TR2 H5. substs.
      assert (swft DD B0). forwards ~ : trans_rlist_regular TRT H5.
      splits...
    + introv WFR WFCL TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H3. inverts H8.
      forwards ~ : bot_trans_r_uniq H11 H9. substs. clear H11.
      forwards ~ : bot_trans_r_uniq H4 H6. substs. clear H6.
      forwards ~ : trans_r_uniq H2 H7. substs. clear H7.
      forwards ~ : trans_rlist_uniq H5 H13. substs. clear H13.
      forwards ~ : trans_r_uniq H1 H10. substs. clear H10.
      inversions WFR.
      assert (swft DD A3). forwards ~ : bot_trans_r_regular TRT H4.
      assert (swft DD A4). forwards ~ : bot_trans_r_regular TRT H9.
      assert (swft DD A). forwards ~ : trans_r_regular TRT H2.
      assert (swft DD B). forwards ~ : trans_r_regular TRT H1.
      assert (swft DD B3). forwards ~ : trans_rlist_regular TRT H5.
      split. apply S_and... apply S_and...
      apply S_trans with (sty_and (sty_and A B) (sty_and A3 A4))...
      apply S_trans with (sty_and A B)...
      apply S_trans with (sty_and (sty_and A B) (sty_and A3 A4))...
      apply S_trans with (sty_and A3 A4)...
      apply S_and... apply S_and...
      apply S_trans with (sty_and (sty_and A B) (sty_and A3 A4))...
      apply S_trans with (sty_and A B)...
      apply S_trans with (sty_and (sty_and A B) (sty_and A3 A4))...
      apply S_trans with (sty_and A3 A4)...
      apply S_and... apply S_and... apply S_and...
      apply S_trans with (sty_and A A3)...
      apply S_trans with (sty_and (sty_and B A4) B3)...
      apply S_trans with (sty_and B A4)...
      apply S_and...
      apply S_trans with (sty_and A A3)...
      apply S_trans with (sty_and (sty_and B A4) B3)...
      apply S_trans with (sty_and B A4)...
      apply S_trans with (sty_and (sty_and B A4) B3)...
    + introv WFR WFCL TRT TR1 TR2.
      inverts TR1. inverts TR2. inverts H5.
      forwards ~ : bot_trans_r_uniq H3 H6. substs. clear H6.
      forwards ~ : trans_r_uniq H2 H4. substs. clear H4.
      forwards ~ : trans_rlist_uniq H8 H11. substs. clear H11.
      forwards ~ : bot_trans_r_uniq H3 H9. substs. clear H9.
      forwards ~ : trans_r_uniq H1 H2. substs. clear H2.
      assert (swft DD A4). forwards ~ : trans_r_regular TRT H1.
      assert (swft DD A5). forwards ~ : bot_trans_r_regular TRT H3.
      assert (swft DD B). forwards ~ : trans_rlist_regular TRT H8.
      split...
    + introv EQ IH1 WFCL TRT TR1 TR2.
      inverts TR1. inverts TR2.
      inverts H1. inverts H3. inverts H2. inverts H6.
      forwards ~ : trans_rlist_uniq H5 H8. substs. clear H8.
      assert (swft DD A). forwards ~ : trans_rt_regular TRT H9.
      assert (swft DD A1). forwards ~ : trans_rt_regular TRT H4.
      assert (swft DD B1). forwards ~ : trans_rlist_regular TRT H5.
      split. apply sub_and...
      apply S_and... apply S_trans with (sty_rcd l sty_bot)...
      apply sub_and...
      apply S_and... apply S_trans with (sty_rcd l sty_bot)...
Qed.

Lemma trans_teq : forall Ttx  rt1 rt2 Ptx A B DD,
    teq Ttx rt1 rt2 ->
    trans_Ttx Ptx Ttx DD ->
    trans_rt Ptx rt1 A ->
    trans_rt Ptx rt2 B ->
    sub DD A B /\ sub DD B A
.
Proof.
  intros.
  pose (proj1 trans_teq_ceq).
  eauto.
Qed.

Lemma trans_ceq : forall Ttx R1 R2 Ptx A B DD,
    ceq Ttx R1 R2 ->
    trans_Ttx Ptx Ttx DD ->
    trans_rlist Ptx R1 A ->
    trans_rlist Ptx R2 B ->
    sub DD A B /\ sub DD B A
.
Proof.
  intros.
  pose (proj2 trans_teq_ceq).
  eauto.
Qed.

(* ********************************************************************** *)
(** * FV *)

Lemma notin_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec: forall A a B n,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rt A ->
    a `notin` fv_rtyp_in_rt (open_rt_wrt_rtyp_rec n B A)
with  notin_fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec: forall A a B n,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rlist A ->
    a `notin` fv_rtyp_in_rlist (open_rlist_wrt_rtyp_rec n B A)
with  notin_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec: forall A a B n,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rtyp A ->
    a `notin` fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp_rec n B A).
Proof.
  -
  intro A. induction A; introv NOT1 NOT2 ; simpls; auto.
  -
  intro A. induction A; introv NOT1 NOT2 ; simpls; auto.
  -
  intro A. induction A. introv I1; introv I2 . simpl.
  destruct (lt_eq_lt_dec n n0). destruct s; simpl; auto...
  simpl; auto.

  introv I1; introv I2 . simpl; auto.
  introv I1; introv I2 . simpl; auto.
  introv I1; introv I2 . simpl; auto.
  introv I1; introv I2 . simpl; auto.
  simpl in I2.
  apply notin_union.
  apply IHA1; auto.
  apply IHA2; auto.
Qed.

Lemma notin_fv_rtyp_in_rt_open_rt_wrt_rtyp: forall A a B,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rt A ->
    a `notin` fv_rtyp_in_rt (open_rt_wrt_rtyp A B).
Proof.
  introv I1 I2.
  unfold open_rt_wrt_rtyp.
  apply notin_fv_rtyp_in_rt_open_rt_wrt_rtyp_rec; eauto.
Qed.

Lemma notin_fv_rtyp_in_rlist_open_rlist_wrt_rtyp: forall A a B,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rlist A ->
    a `notin` fv_rtyp_in_rlist (open_rlist_wrt_rtyp A B).
Proof.
  introv I1 I2.
  unfold open_rlist_wrt_rtyp.
  apply notin_fv_rtyp_in_rlist_open_rlist_wrt_rtyp_rec; eauto.
Qed.

Lemma  notin_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp: forall A a B,
    a `notin` fv_rtyp_in_rtyp B ->
    a `notin` fv_rtyp_in_rtyp A ->
    a `notin` fv_rtyp_in_rtyp (open_rtyp_wrt_rtyp A B).
Proof.
  introv I1 I2.
  unfold open_rlist_wrt_rtyp.
  apply notin_fv_rtyp_in_rtyp_open_rtyp_wrt_rtyp_rec; eauto.
Qed.


Lemma bot_trans_r_preserve_notin :
    forall Ptx r A,
      bot_trans_r Ptx r A ->
      forall Ttx a b,
      wfp Ttx Ptx ->
      binds a b Ptx ->
      a `notin` fv_rtyp_in_rtyp r ->
      b `notin` fv_sty_in_sty A.
Proof with eauto.
  introv BD. inductions BD; intros; simpls...
  forwards ~ : wfp_binds_range_neq H0 H1 H...
Qed.

Lemma trans_general_preserve_notin :
  ( forall Ptx r A,
      trans_rt Ptx r A ->
      forall Ttx a b,
      wfp Ttx Ptx ->
      binds a b Ptx ->
      a `notin` fv_rtyp_in_rt r ->
      b `notin` fv_sty_in_sty A
  ) /\ (
    forall Ptx r A,
      trans_r Ptx r A ->
      forall Ttx a b,
      wfp Ttx Ptx ->
      binds a b Ptx ->
      a `notin` fv_rtyp_in_rtyp r ->
      b `notin` fv_sty_in_sty A
  ) /\ (
    forall Ptx r A,
    trans_rlist Ptx r A ->
    forall Ttx a b,
    wfp Ttx Ptx ->
    binds a b Ptx ->
    a `notin` fv_rtyp_in_rlist r ->
    b `notin` fv_sty_in_sty A
  ).
Proof with eauto.
  apply trans_rt_mutind; try solve [intros; simpls; eauto].
  - introv TR1 IH1 IH2 IH3 WFP BD NOTIN.
    simpls...
    forwards ~ : IH1 WFP BD.
    pick_fresh X.
    pick_fresh Y.
    forwards ~ : IH3 X Y ((Y, R_Empty ) :: Ttx) a b.
    econstructor...
    apply notin_fv_rtyp_in_rt_open_rt_wrt_rtyp...
    assert (b `notin` fv_sty_in_sty (open_sty_wrt_sty_rec 1 (sty_var_f Y) A)).
    forwards ~ : fv_sty_in_sty_open_sty_wrt_sty_rec_lower_mutual (open_sty_wrt_sty_rec 1 (sty_var_f Y) A) (sty_var_f X) 0.
    assert (b `notin` fv_sty_in_sty A).
    forwards ~ : fv_sty_in_sty_open_sty_wrt_sty_rec_lower_mutual A (sty_var_f Y) 1.
    eauto.
  - introv BD1 WFP BD2 NOTIN. simpls...
    forwards ~ : wfp_binds_neq WFP BD2 BD1.
  - introv TR1 IH1 BOT_TR TR2 IH2 WFP BD NOTIN.
    simpls...
    apply notin_union... apply notin_union...
    eapply bot_trans_r_preserve_notin...
Qed.

Lemma trans_rt_preserve_notin : forall Ptx r A Ttx a b,
      trans_rt Ptx r A ->
      wfp Ttx Ptx ->
      binds a b Ptx ->
      a `notin` fv_rtyp_in_rt r ->
      b `notin` fv_sty_in_sty A.
Proof.
  intros.
  pose (proj1 trans_general_preserve_notin).
  eapply n; eauto.
Qed.

Lemma trans_r_preserve_notin : forall Ptx r A Ttx a b,
      trans_r Ptx r A ->
      wfp Ttx Ptx ->
      binds a b Ptx ->
      a `notin` fv_rtyp_in_rtyp r ->
      b `notin` fv_sty_in_sty A.
Proof.
  intros.
  pose (proj1 (proj2 trans_general_preserve_notin)).
  eapply n; eauto.
Qed.

Lemma trans_rlist_preserve_notin : forall Ptx r A Ttx a b,
      trans_rlist Ptx r A ->
      wfp Ttx Ptx ->
      binds a b Ptx ->
      a `notin` fv_rtyp_in_rlist r ->
      b `notin` fv_sty_in_sty A.
Proof.
  intros.
  pose (proj2 (proj2 trans_general_preserve_notin)).
  eapply n; eauto.
Qed.

Lemma bot_trans_r_fresh_Eq : forall P1 P2 r Rb Y X,
    bot_trans_r (P1 ++ P2) r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx (P1 ++ P2)) ->
    bot_trans_r (P1 ++(Y ~ X) ++ P2) r Rb.
Proof with auto.
  introv TR. inductions TR; introv NOT1 NOT2...
  simpl in NOT1...
Qed.

Lemma bot_trans_r_fresh_head_Eq : forall P r Rb Y X,
    bot_trans_r P r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx P) ->
    bot_trans_r ((Y ~ X) ++ P) r Rb.
Proof with auto.
  introv TR. inductions TR; introv NOT1 NOT2...
  simpl in NOT1...
Qed.

Lemma trans_r_fresh_Eq : forall P1 P2 r Rb Y X,
    trans_r (P1++P2) r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx (P1 ++ P2)) ->
    trans_r (P1 ++ (Y ~ X) ++ P2) r Rb
with trans_rt_fresh_Eq : forall P1 P2 r Rb Y X,
    trans_rt (P1++P2) r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx (P1++P2)) ->
    trans_rt (P1 ++(Y ~ X) ++ P2) r Rb
with trans_rlist_fresh_Eq : forall P1 P2 r Rb Y X,
    trans_rlist (P1++P2) r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx (P1++P2)) ->
    trans_rlist (P1++(Y ~ X) ++ P2) r Rb.
Proof with trivial.
  -
  introv TR. inductions TR; introv NOT1 NOT2...
  apply trans_r_tvar with b... apply binds_weaken...
  constructor... apply trans_rt_fresh_Eq...
  simpl in NOT1.
  constructor... apply IHTR1... auto.
  apply IHTR2... auto.
  -
  introv TR. inductions TR; introv NOT1 NOT2...
  simpl in NOT1.
  simpl. constructor... apply IHTR1... auto.
    apply IHTR2... auto.
  simpl in NOT1.
  pick fresh Z and apply trans_rt_all.
  apply trans_rlist_fresh_Eq... auto.
  intros Z1 Fr1.
  rewrite_env (([(Z1, Z)] ++ P1) ++ [(Y, X)] ++ P2).
  apply H1... auto. auto.
  apply fv_notin_open_sty_wrt_sty_rec... auto.
  apply fv_notin_open_sty_wrt_sty_rec... auto. auto. auto.
  constructor... apply trans_r_fresh_Eq...
  -
  introv TR. inductions TR; introv NOT1 NOT2...
  simpl in NOT1.
  constructor... apply trans_r_fresh_Eq... auto.
     apply bot_trans_r_fresh_Eq... auto.
     apply trans_rlist_fresh_Eq... auto.
Qed.

Lemma trans_Gtx_fresh_Eq : forall P1 P2 Gtx GG Y X,
    trans_Gtx (P1 ++ P2) Gtx GG ->
    Y `notin` fv_stctx GG ->
    Y `notin` (fv_Ptx (P1++P2)) ->
    X `notin` dom GG ->
    trans_Gtx (P1 ++ (Y ~ X) ++P2) Gtx GG.
Proof with eauto.
  introv TR. inductions TR; introv NOT1 NOT2 NOT3...
  constructor...
  simpl in NOT1...
  constructor...
  apply trans_rt_fresh_Eq...
  repeat rewrite fv_Ptx_union in *...
Qed.

Lemma trans_r_fresh_head_Eq : forall P r Rb Y X,
    trans_r P r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx P) ->
    trans_r ((Y ~ X) ++ P) r Rb.
Proof with eauto.
  intros.
  rewrite_env (nil ++ (Y~ X) ++P).
  apply trans_r_fresh_Eq...
Qed.

Lemma trans_rt_fresh_head_Eq : forall P r Rb Y X,
    trans_rt P r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx (P)) ->
    trans_rt ((Y ~ X) ++ P) r Rb.
Proof with eauto.
  intros.
  rewrite_env (nil ++ (Y~ X) ++P).
  apply trans_rt_fresh_Eq...
Qed.

Lemma trans_rlist_fresh_head_Eq : forall P r Rb Y X,
    trans_rlist P r Rb ->
    Y `notin` (fv_sty_in_sty Rb) ->
    Y `notin` (fv_Ptx P) ->
    trans_rlist ((Y ~ X) ++ P) r Rb.
Proof with eauto.
  intros.
  rewrite_env (nil ++ (Y~ X) ++P).
  apply trans_rlist_fresh_Eq...
Qed.

Lemma trans_Gtx_fresh_head_Eq : forall P Gtx GG X Y,
    trans_Gtx P Gtx GG ->
    Y `notin` fv_stctx GG ->
    Y `notin` (fv_Ptx P) ->
    X `notin` dom  GG ->
    trans_Gtx ((Y ~ X) ++ P) Gtx GG.
Proof with eauto.
  intros.
  rewrite_env (nil ++ (Y~ X) ++P).
  apply trans_Gtx_fresh_Eq...
Qed.

Lemma bot_trans_r_notin :
  (forall Ptx r Ra,
      bot_trans_r Ptx r Ra ->
      forall b,
        b `notin` dom Ptx ->
        b `notin` fv_Ptx Ptx ->
        b `notin` fv_sty_in_sty Ra
  )
.
Proof with eauto.
  induction 1; intros; simpls...
  apply notin_singleton_2.
  introv I. substs.
  forwards ~ : binds_ptx_fv H.
Qed.



Lemma trans_r_notin :
  (forall Ptx r Ra,
      trans_rt Ptx r Ra ->
      forall b,
        b `notin` dom Ptx ->
        b `notin` fv_Ptx Ptx ->
        b `notin` fv_sty_in_sty Ra
  )
  /\
  (forall Ptx r Ra,
      trans_r Ptx r Ra ->
      forall b,
        b `notin` dom Ptx ->
        b `notin` fv_Ptx Ptx ->
        b `notin` fv_sty_in_sty Ra
  )
  /\
  (forall Ptx r Ra,
      trans_rlist Ptx r Ra ->
      forall b,
        b `notin` dom Ptx ->
        b `notin` fv_Ptx Ptx ->
        b `notin` fv_sty_in_sty Ra
  ).
Proof with eauto using bot_trans_r_notin.
  apply trans_rt_mutind; simpls...

  -
    intros.
    pick_fresh X. pick_fresh Y.
    forwards ~ : H0 X Y b...
    forwards ~ : H.
    assert (b `notin` fv_sty_in_sty A).
    unfold open_sty_wrt_sty in H3.
    rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_lower...
    rewrite fv_sty_in_sty_open_sty_wrt_sty_lower...
    auto.
  -
    introv BD N1 N2.
    apply notin_singleton_2.
    introv H. substs.
    false binds_dom_contradiction...
Qed.

(* ********************************************************************** *)
(** * Substitution *)

Lemma bot_trans_r_subsitution_distributivity': forall r1 Ttx Ptx1 Ptx2 a r A Ra Rb b,
    wfp Ttx (Ptx1 ++ [(a,b)] ++ Ptx2) ->
    bot_trans_r (Ptx1 ++ [(a,b)] ++ Ptx2) r1 A ->
    bot_trans_r (Ptx1 ++ Ptx2) r  Rb ->
    trans_r     (Ptx1 ++ Ptx2) r  Ra ->
    bot_trans_r (Ptx1 ++ Ptx2) (subst_rtyp_in_rtyp r a r1)
                    (subst_sty_in_sty Rb b (subst_sty_in_sty Ra a A)).
Proof with eauto.
  intro r1. induction r1;
              introv WFP BOT_TRANS_R1 BOT_TRANS_RB BOT_TRANS_RA; simpls.
  - inverts BOT_TRANS_R1.
  - inverts BOT_TRANS_R1.
    case_if.
    + substs.
      assert (binds a0 b (Ptx1 ++ (a0, b) :: Ptx2)). auto.
      assert (b = b0). eapply binds_unique... substs.
      simpl. case_if. false wfp_binds_neq...
      simpl. case_if...
    + forwards ~ : wfp_binds_neq H1...
      simpl... case_if...
      forwards ~ : wfp_binds_range_neq H1...
      simpl... case_if...
      apply binds_remove_mid in H1...
  - inverts BOT_TRANS_R1. simpl...
  - inverts BOT_TRANS_R1. simpl...
    constructor...
    apply subst_rtyp_in_rt_lc_rt...
  - inverts BOT_TRANS_R1. simpl...
Qed.

Lemma trans_general_subsitution_distributivity':
  (forall Ttx r1,
      wfcl Ttx r1 ->
      forall Ptx1 Ptx2 a b r A Ra Rb,
        a \notin fv_rtyp_in_rtyp r ->
        wfp Ttx (Ptx1 ++ [(a,b)] ++ Ptx2) ->
        trans_rlist (Ptx1 ++ [(a,b)] ++ Ptx2) r1 A ->
        bot_trans_r (Ptx1 ++ Ptx2) r  Rb ->
        trans_r     (Ptx1 ++ Ptx2) r  Ra ->
        trans_rlist (Ptx1 ++ Ptx2) (subst_rtyp_in_rlist r a r1)
                    (subst_sty_in_sty Rb b (subst_sty_in_sty Ra a A))
  ) /\ (
    forall Ttx r1,
      wfrt Ttx r1 ->
    forall Ptx1 Ptx2 a b r A Ra Rb,
      a \notin fv_rtyp_in_rtyp r ->
      wfp Ttx (Ptx1 ++ [(a,b)] ++ Ptx2) ->
      trans_rt    (Ptx1 ++ [(a,b)] ++ Ptx2) r1 A ->
      bot_trans_r (Ptx1 ++ Ptx2) r  Rb ->
      trans_r     (Ptx1 ++ Ptx2) r  Ra ->
      trans_rt    (Ptx1 ++ Ptx2) (subst_rtyp_in_rt r a r1)
               (subst_sty_in_sty Rb b (subst_sty_in_sty Ra a A))
  ) /\ (
    forall Ttx r1,
      wfr Ttx r1 ->
    forall Ptx1 Ptx2 a b r A Ra Rb,
      a \notin fv_rtyp_in_rtyp r ->
      wfp Ttx (Ptx1 ++ [(a,b)] ++ Ptx2) ->
      trans_r     (Ptx1 ++ [(a,b)] ++ Ptx2) r1 A ->
      bot_trans_r (Ptx1 ++ Ptx2) r  Rb ->
      trans_r     (Ptx1 ++ Ptx2) r  Ra ->
      trans_r     (Ptx1 ++ Ptx2) (subst_rtyp_in_rtyp r a r1)
              (subst_sty_in_sty Rb b (subst_sty_in_sty Ra a A))
  ).
Proof with eauto.
  apply rlist_rt_mutind.
  - introv WFTC NOTIN WFP TR1 BOT_TR TR2.
    inverts TR1...
  - introv WFR NOTIN IH1 WFCL IH2 WFP TR1 BOT_TR TR2.
    inverts TR1... simpl...
    constructor...
    eapply bot_trans_r_subsitution_distributivity'...
  - introv NOTIN WFP TR1 BOT_TR TR2...
    inverts TR1...
  - introv WFRT1 IH1 WFRT2 IH2 NOTIN WFP TR1 BOT_TR TR2...
    inverts TR1... simpl...
  - introv WFCL IH1 IH2 IH3 NOTIN WFP TR1 BOT_TR TR2...
    inverts TR1... simpl...
    pick fresh X and apply trans_rt_all...
    intros Y Fr0.
    forwards ~ : H4 X Y.
    assert (I1: bot_trans_r ((Y, X) :: Ptx1 ++ Ptx2) r Rb).
      apply bot_trans_r_fresh_head_Eq...
      rewrite fv_Ptx_union...
    assert (I2: trans_r ((Y, X) :: Ptx1 ++ Ptx2) r Ra).
      apply trans_r_fresh_head_Eq...
      rewrite fv_Ptx_union...
    specialize IH3 with (a:=Y) (Ptx1:= ((Y, X) :: Ptx1)) (Ptx2:=Ptx2) (a0:=a) (b:=b) (Ra := Ra) (Rb := Rb) (r:=r).
    forwards ~ : IH3 H.
      simpl.
      constructor...
      rewrite fv_Ptx_union...
      rewrite fv_Ptx_union...
    assert (Y <> a). eauto.
    assert (X <> a). eauto.
    assert (X <> b). eauto.
    assert (Y <> b). eauto.
    rewrite subst_rtyp_in_rt_open_rt_wrt_rtyp in H0...
    simpl in H0. case_if...
    rewrite subst_sty_in_sty_open_sty_wrt_sty in H0...
    simpl in H0. case_if...
    rewrite subst_sty_in_sty_open_sty_wrt_sty in H0...
    simpl in H0. case_if...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_rec in H0...
    rewrite subst_sty_in_sty_open_sty_wrt_sty_rec in H0...
    simpl in H0. case_if...
    simpl in H0. case_if...
  - introv WFR IH1 NOTIN WFP TRAN1 BOT_TR TRAN2.
    inverts TRAN1.
    simpl...
  - introv BD1 NOTIN WFP TR1 BOT_TR TR2.
    inverts TR1.
    simpls... case_if... substs.
      assert (binds a0 b (Ptx1 ++ (a0, b) :: Ptx2)). auto.
      assert (b = b0). eapply binds_unique... substs.
      rewrite subst_sty_in_sty_fresh_eq...
      apply wfp_mid_inv in WFP.
      destruct_hypo...
      pose (proj1 (proj2 trans_r_notin)) as II.
      eapply II...

    assert (BD2: binds a0 b (Ptx1 ++ (a0, b) :: Ptx2)). auto.
    forwards ~ : wfp_binds_neq BD2 H1...
    simpls... case_if...
      apply binds_remove_mid in H1...
  - introv WFRT IH1 NOTIN WFP TRT BOT_TR TR2.
    inverts TRT.
    simpls...
  - introv NOTIN WFP TRT BOTTR TR2.
    inverts TRT. simpls...
  - introv WFR IH1 WF2 IH2 CMP NOTIN WFP TR1 BOTTR TR2.
    inverts TR1. simpls...
Qed.

Lemma trans_rt_substitution_distributivity:
    forall Ttx r1 Ptx a b r A Ra Rb,
      wfrt Ttx r1 ->
      a \notin fv_rtyp_in_rtyp r ->
      wfp Ttx ( [(a,b)] ++ Ptx) ->
      trans_rt ([(a,b)] ++ Ptx) r1 A ->
      bot_trans_r (Ptx) r  Rb ->
      trans_r     (Ptx) r  Ra ->
      trans_rt    (Ptx) (subst_rtyp_in_rt r a r1)
               (subst_sty_in_sty Rb b (subst_sty_in_sty Ra a A))
.
Proof.
  pose (proj1 (proj2 trans_general_subsitution_distributivity')) as I.
  intros.
  rewrite_env (nil ++ Ptx).
  eapply I; eauto.
Qed.


(* ********************************************************************** *)
(** * Labels *)

Inductive label_in_rtyp : i -> rtyp -> Prop :=
  | label_in_rtyp_rcd : forall l rt,
      label_in_rtyp l (r_SingleField l rt)
  | label_in_rtyp_merge_l : forall l rt1 rt2,
      label_in_rtyp l rt1 ->
      label_in_rtyp l (r_Merge rt1 rt2)
  | label_in_rtyp_merge_r : forall l rt1 rt2,
      label_in_rtyp l rt2 ->
      label_in_rtyp l (r_Merge rt1 rt2)

.

Inductive label_in_rlist : i -> rlist -> Prop :=
  | label_in_rlist_head : forall l r R,
      label_in_rtyp l r ->
      label_in_rlist l (R_Cons r R)
  | label_in_rlist_tail : forall l r R,
      label_in_rlist l R ->
      label_in_rlist l (R_Cons r R)
.

Inductive label_notin_rtyp : i -> rtyp -> Prop :=
  | label_notin_rtyp_bvar : forall l i,
      label_notin_rtyp l (r_TyVar_b i)
  | label_notin_rtyp_fvar : forall l x,
      label_notin_rtyp l (r_TyVar_f x)
  | label_notin_rypt_empty : forall l,
      label_notin_rtyp l r_Empty
  | label_notin_rypt_singlefield : forall l l2 rt,
      l <> l2 ->
      label_notin_rtyp l (r_SingleField l2 rt)
  | label_notin_rypt_merge : forall l r1 r2,
      label_notin_rtyp l r1 ->
      label_notin_rtyp l r2 ->
      label_notin_rtyp l  (r_Merge r1 r2)
.

Hint Constructors label_notin_rtyp.
Lemma label_notin_teq: forall l Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    ((label_notin_rtyp l r1 -> label_notin_rtyp l r2)
    /\ (label_notin_rtyp l r2 -> label_notin_rtyp l r1)).
Proof with eauto.
  introv HH.
  inductions HH; split; introv I; eauto;
    try solve [inverts I; eauto];
    try solve [forwards ~ : IHHH; destruct_hypo; eauto];
    try solve [forwards ~ : IHHH1; forwards ~ : IHHH2;
               repeat destruct_hypo; eauto].
  - forwards ~ (? & ?) : teq_record_l HH1.
    forwards ~ (? & ?) : teq_record_r HH2.
    substs...
    forwards ~ : IHHH1; forwards ~ : IHHH2; repeat destruct_hypo; eauto.
  - forwards ~ (? & ?) : teq_record_l HH1.
    forwards ~ (? & ?) : teq_record_r HH2.
    substs...
    forwards ~ : IHHH1; forwards ~ : IHHH2; repeat destruct_hypo; eauto.
  - inverts I...
    forwards ~ : IHHH1; forwards ~ : IHHH2; repeat destruct_hypo; eauto.
  - inverts I...
    forwards ~ : IHHH1; forwards ~ : IHHH2; repeat destruct_hypo; eauto.
  - inverts I as I1 I2. inverts I2...
  - inverts I as I1 I2. inverts I1...
Qed.

Lemma label_notin_teq_l: forall l Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    label_notin_rtyp l r1 -> label_notin_rtyp l r2.
Proof.
  introv H1 H2.
  apply label_notin_teq with (l:=l) in H1.
  destruct_hypo; eauto.
Qed.

Lemma label_notin_teq_r: forall l Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    label_notin_rtyp l r2 -> label_notin_rtyp l r1.
Proof.
  introv H1 H2.
  apply label_notin_teq with (l:=l) in H1.
  destruct_hypo; eauto.
Qed.

Hint Constructors label_in_rtyp.
Lemma label_in_teq: forall l Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    ((label_in_rtyp l r1 -> label_in_rtyp l r2)
    /\ (label_in_rtyp l r2 -> label_in_rtyp l r1)).
Proof with eauto.
  introv HH.
  inductions HH; split; introv I; repeat destruct_hypo; simpls;
    try solve [inverts I as I2; try inverts I2; eauto].
  - forwards ~ : IHHH. destruct_hypo...
  - forwards ~ : IHHH. destruct_hypo...
  - forwards ~ (? & ?) : teq_record_l HH1.
    forwards ~ (? & ?) : teq_record_r HH2.
    substs. forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo. eauto.
  - forwards ~ (? & ?) : teq_record_l HH1.
    forwards ~ (? & ?) : teq_record_r HH2.
    substs. forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo. eauto.
  - forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo.
    inverts I...
  - forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo.
    inverts I...
Qed.

Lemma label_in_teq_l: forall l Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    label_in_rtyp l r1 -> label_in_rtyp l r2.
Proof.
  introv H1 H2.
  apply label_in_teq with (l:=l) in H1.
  destruct_hypo; eauto.
Qed.

Lemma label_in_teq_r: forall l Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    label_in_rtyp l r2 -> label_in_rtyp l r1.
Proof.
  introv H1 H2.
  apply label_in_teq with (l:=l) in H1.
  destruct_hypo; eauto.
Qed.

Lemma label_in_cmp : forall l Ttx r1 r2,
    cmp Ttx r1 r2 ->
    (
      label_in_rtyp l r1 ->
      label_notin_rtyp l r2
    )
    /\
    (
      label_in_rtyp l r2 ->
      label_notin_rtyp l r1
    ).
Proof with eauto.
  introv HH.
  induction HH; split; introv I; repeat destruct_hypo;
    try solve [inverts I; eauto].
  - forwards ~ : label_in_teq_r H I.
    forwards ~ : H1.
    forwards ~ : label_notin_teq_l H0.
  - forwards ~ : label_in_teq_r H0 I.
    forwards ~ : H2.
    forwards ~ : label_notin_teq_l H.
  - forwards ~ : H0 I. inverts H2...
  - forwards ~ : H. inverts H1...
  - forwards ~ : H. inverts H1...
  - constructor...
Qed.

Lemma label_in_cmp_r : forall l Ttx r1 r2,
    cmp Ttx r1 r2 ->
    label_in_rtyp l r2 ->
    label_notin_rtyp l r1.
Proof with eauto.
  introv I1 I2.
  forwards ~ : label_in_cmp I1.
  destruct_hypo...
Qed.

Lemma bot_trans_r_label_in : forall l r A B Ptx Ttx DD,
    label_in_rtyp l r ->
    wfr Ttx r ->
    bot_trans_r Ptx r A ->
    trans_Ttx Ptx Ttx DD ->
    swft DD B ->
    sub DD A (sty_rcd l B).
Proof with eauto.
  introv LABEL.
  generalize dependent A.
  generalize dependent B.
  induction LABEL; introv WFR TRB TR WFT.
  - inverts TRB...
  - inverts TRB. inverts WFR.
    apply S_trans with A0; auto.
    apply S_andl.
    eapply bot_trans_r_regular with (r:=rt1)...
    eapply bot_trans_r_regular with (r:=rt2)...
  - inverts TRB. inverts WFR.
    apply S_trans with B0; auto.
    apply S_andr.
    eapply bot_trans_r_regular with (r:=rt1)...
    eapply bot_trans_r_regular with (r:=rt2)...
Qed.


Lemma trans_rlist_label_in : forall l R A B Ptx Ttx DD,
    label_in_rlist l R ->
    wfcl Ttx R ->
    trans_rlist Ptx R A ->
    trans_Ttx Ptx Ttx DD ->
    swft DD B ->
    sub DD A (sty_rcd l B).
Proof with eauto.
  introv LABEL.
  generalize dependent A.
  generalize dependent B.
  induction LABEL; introv WFR TRB TR WFT.
  - inverts TRB. inverts WFR.
    apply S_trans with A2.
    eapply bot_trans_r_label_in...
    assert (swft DD A2). eapply bot_trans_r_regular...
    assert (swft DD B0). eapply trans_rlist_regular...
    assert (swft DD A1). eapply trans_r_regular...
    apply S_trans with (sty_and A1 A2)...
  - inverts TRB. inverts WFR.
    apply S_trans with B0; auto.
    assert (swft DD A2). eapply bot_trans_r_regular...
    assert (swft DD B0). eapply trans_rlist_regular...
    assert (swft DD A1). eapply trans_r_regular...
    apply S_andr...
Qed.

Lemma label_in_rtyp_in_rlist : forall l r R,
    label_in_rtyp l r ->
    rtyp_in_rlist r R ->
    label_in_rlist l R.
Proof with eauto.
  introv I1 I2. inductions I2...
  apply label_in_rlist_head...
  apply label_in_rlist_tail...
Qed.

(* ********************************************************************** *)
(** * Type Variables *)

Inductive tvar_in_rtyp : typvar -> rtyp -> Prop :=
  | tvar_in_rtyp_rcd : forall a,
      tvar_in_rtyp a (r_TyVar_f a )
  | tvar_in_rtyp_merge_a : forall a rt1 rt2,
      tvar_in_rtyp a rt1 ->
      tvar_in_rtyp a (r_Merge rt1 rt2)
  | tvar_in_rtyp_merge_r : forall a rt1 rt2,
      tvar_in_rtyp a rt2 ->
      tvar_in_rtyp a (r_Merge rt1 rt2)
.

Hint Constructors tvar_in_rtyp.
Lemma tvar_in_teq: forall a Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    ((tvar_in_rtyp a r1 -> tvar_in_rtyp a r2)
    /\ (tvar_in_rtyp a r2 -> tvar_in_rtyp a r1)).
Proof with eauto.
  introv HH.
  inductions HH; split; introv I; repeat destruct_hypo; simpls;
    try solve [inverts I as I2; try inverts I2; eauto].
  - forwards ~ : IHHH. destruct_hypo...
  - forwards ~ : IHHH. destruct_hypo...
  - forwards ~ (? & ?) : teq_record_l HH1.
    forwards ~ (? & ?) : teq_record_r HH2.
    substs. forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo. eauto.
  - forwards ~ (? & ?) : teq_record_l HH1.
    forwards ~ (? & ?) : teq_record_r HH2.
    substs. forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo. eauto.
  - forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo.
    inverts I...
  - forwards ~ : IHHH1. forwards ~ : IHHH2.
    repeat destruct_hypo.
    inverts I...
Qed.

Lemma tvar_in_teq_l: forall a Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    tvar_in_rtyp a r1 -> tvar_in_rtyp a r2.
Proof.
  introv H1 H2.
  apply tvar_in_teq with (a:=a) in H1.
  destruct_hypo; eauto.
Qed.

Lemma tvar_in_teq_r: forall a Ttx r1 r2,
    teq Ttx (rt_Record r1) (rt_Record r2) ->
    tvar_in_rtyp a r2 -> tvar_in_rtyp a r1.
Proof.
  introv H1 H2.
  apply tvar_in_teq with (a:=a) in H1.
  destruct_hypo; eauto.
Qed.

Lemma tvar_in_cmp: forall a l Ttx r1 r2,
    cmp Ttx r1 r2 ->
    (
      tvar_in_rtyp a r1 /\
      label_in_rtyp l r2
    )
    \/
    (
      label_in_rtyp l r1 /\
      tvar_in_rtyp a r2
    )
    -> exists R, 
        (binds  a   R   Ttx
               /\ label_in_rlist l R).
Proof with eauto.
  introv HH.
  inductions HH; introv I.
  - destruct I as [ [I1 I2] | [I1 I2] ].
    forwards ~ : label_in_teq_r H0...
    forwards ~ : tvar_in_teq_r H...
    forwards ~ : label_in_teq_r H...
    forwards ~ : tvar_in_teq_r H0...
  - apply IHHH...
    destruct I ; destruct_hypo ; [right | left]...
  - destruct I as [ [I1 I2] | [I1 I2] ];
      inverts I1...
    exists R... splits...
    eapply label_in_rtyp_in_rlist...
  - destruct I as [ [I1 I2] | [I1 I2] ];
    inverts I2.
    apply IHHH...
  - destruct I as [ [I1 I2] | [I1 I2] ];
    apply IHHH; [left | right]... 
  - destruct I as [ [I1 I2] | [I1 I2] ];
    apply IHHH; [left | right]... 
  - destruct I as [ [I1 I2] | [I1 I2] ].
    inverts I2; [apply IHHH2 | apply IHHH3]... 
    inverts I2; [apply IHHH2 | apply IHHH3]... 
  - destruct I as [ [I1 I2] | [I1 I2] ].
    inverts I1. inverts I2.
  - destruct I as [ [I1 I2] | [I1 I2] ].
    inverts I2. inverts I2.
Qed.

Lemma tvar_in_cmp_l: forall a l Ttx r1 r2,
    cmp Ttx r1 r2 ->
    tvar_in_rtyp a r1 ->
    label_in_rtyp l r2 ->
    exists R, 
      (binds  a   R   Ttx
       /\ label_in_rlist l R).
Proof.
  introv I1 I2 I3.
  eapply tvar_in_cmp; eauto.
Qed.

Lemma tvar_in_cmp_r: forall a l Ttx r1 r2,
    cmp Ttx r1 r2 ->
    label_in_rtyp l r1 ->
    tvar_in_rtyp a r2 ->
    exists R, 
      (binds  a   R   Ttx
       /\ label_in_rlist l R).
Proof.
  introv I1 I2 I3.
  eapply tvar_in_cmp; eauto.
Qed.

Lemma trans_Ttx_binds' : forall a R Ttx Ptx DD,
  wftc Ttx ->
  binds a R Ttx ->
  trans_Ttx Ptx Ttx DD ->
  exists A, binds a A DD /\ trans_rlist Ptx R A.
Proof with auto.
  introv WFT BD TR. inductions TR.
  false.
  apply binds_cons_1 in BD.
  destruct BD as [[I1 I2]| I3].
    subst. exists A... splits...
    forwards ~ : trans_rlist_fresh_head_Eq a0 b H.
    apply swft_tvar with DD...
    apply trans_rlist_regular with Ttx R0 Ptx...
    inverts WFT...

    inverts WFT...
    forwards ~ (? & ?) : IHTR I3.
    destruct_hypo...
    exists x... splits...
    forwards ~ : trans_rlist_fresh_head_Eq a0 b H3.
    apply swft_tvar with DD...
    apply swft_from_swfte with a...
    apply trans_Ttx_regular with (Ttx:=Ttx) (Ptx:=Ptx)...
Qed.

(* ********************************************************************** *)
(** * Essence of compatibility *)

Lemma label_in_rlist_disjoint1: forall a R l Ttx Ptx A B DD,
    wftc Ttx ->
    binds  a   R   Ttx ->
    label_in_rlist l R ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx (r_TyVar_f a) A ->
    swft DD B ->
    disjoint DD A (sty_rcd l B).
Proof with eauto.
  introv WFTC BD LABELIN TRT TRR WFTB.
  forwards ~ WFCL : wfcl_from_binds_wftc BD...
  forwards ~ (RA & TRRA): trans_rlist_exists WFCL. 
    eapply trans_Ttx_wfp...
  forwards ~ : trans_rlist_label_in B LABELIN TRRA TRT...
  forwards ~ (RA' & [BD' TRR']): trans_Ttx_binds' WFTC BD TRT...
  forwards ~ : trans_rlist_uniq TRRA TRR'...
  substs.
  inverts TRR.
  apply D_tvarL with (A:=RA')...
Qed.

Lemma trans_Ttx_binds_Ptx' : forall a R Ttx Ptx DD b,
  wftc Ttx ->
  binds a R Ttx ->
  binds a b Ptx ->
  trans_Ttx Ptx Ttx DD ->
  exists A, binds b A DD /\ trans_rlist Ptx R A.
Proof with auto.
  introv WFT BD1 BD2 TR. inductions TR.
  false.
  apply binds_cons_1 in BD1.
  destruct BD1 as [[I1 I2]| I3].

    subst.
    assert (b = b0).
      apply binds_unique with a0 ([(a0, b0)] ++ Ptx)...
    substs.
    exists A... splits...
    forwards ~ : trans_rlist_fresh_head_Eq a0 b0 H.
    apply swft_tvar with DD...
    apply trans_rlist_regular with Ttx R0 Ptx...
    inverts WFT...

    inverts WFT...
    analyze_binds BD2.
    false binds_dom_contradiction a0 R Ttx...
    forwards ~ (? & ?) : IHTR I3.
    destruct_hypo...
    exists x... splits...
    forwards ~ : trans_rlist_fresh_head_Eq a0 b0 H3.
    apply swft_tvar with DD...
    apply swft_from_swfte with b...
    apply trans_Ttx_regular with (Ttx:=Ttx) (Ptx:=Ptx)...
Qed.

Lemma label_in_rlist_disjoint2: forall a R l Ttx Ptx A B DD,
    wftc Ttx ->
    binds  a   R   Ttx ->
    label_in_rlist l R ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx (r_TyVar_f a) A ->
    swft DD B ->
    disjoint DD A (sty_rcd l B).
Proof with eauto.
  introv WFTC BD LABELIN TRT TRR WFTB.
  forwards ~ WFCL : wfcl_from_binds_wftc BD...
  forwards ~ (RA & TRRA): trans_rlist_exists WFCL. 
    eapply trans_Ttx_wfp...
  inverts TRR.
  forwards ~ : trans_rlist_label_in B LABELIN TRRA TRT...
  forwards ~ (RA' & [BD' TRR']): trans_Ttx_binds_Ptx' WFTC BD TRT...
  forwards ~ : trans_rlist_uniq TRRA TRR'...
  substs.
  apply D_tvarL with (A:=RA')...
Qed.

Lemma tvar_in_label_in_cmp : forall Ttx r1 r2 a l Ptx DD A B,
    wftc Ttx ->
    cmp Ttx r1 r2 ->
    tvar_in_rtyp a r1 ->
    label_in_rtyp l r2 ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx (r_TyVar_f a) A ->
    swft DD B ->
    disjoint DD A (sty_rcd l B).
Proof.
  introv WFTC CMP TVAR LABEL TRT TRR WFT.
  forwards ~ (R & [BD LABELIN]) : tvar_in_cmp_l CMP TVAR LABEL.
  eapply label_in_rlist_disjoint1; eauto.
Qed.

Lemma tvar_in_label_in_cmp_bot : forall Ttx r1 r2 a l Ptx DD A B,
    wftc Ttx ->
    cmp Ttx r1 r2 ->
    tvar_in_rtyp a r1 ->
    label_in_rtyp l r2 ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx (r_TyVar_f a) A ->
    swft DD B ->
    disjoint DD A (sty_rcd l B).
Proof.
  introv WFTC CMP TVAR LABEL TRT TRR WFT.
  forwards ~ (R & [BD LABELIN]) : tvar_in_cmp_l CMP TVAR LABEL.
  eapply label_in_rlist_disjoint2; eauto.
Qed.

Lemma cmp_record_r : forall Ttx r l t Ptx DD B A,
    wftc Ttx ->
    cmp Ttx r (r_SingleField l t) ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx r A ->
    swft DD B ->
    disjoint DD A (sty_rcd l B).
Proof with eauto.
  introv I1 I2 I3 I4 I5.
  forwards ~ I6 : label_in_cmp_r I2...
  generalize dependent A.
  induction I6; introv I4; inverts I4.
  -
  eapply tvar_in_label_in_cmp...
  -
  constructor...
  -
  apply D_rcdNeq...
  eapply trans_rt_regular with (rt:=rt)...
  apply cmp_regular in I2.
  destruct_hypo... inverts H0...
  - forwards ~ : IHI6_1 H2.
    apply cmp_Symm.
    apply cmp_MergeE1 with r2.
    apply cmp_Symm...
    forwards ~ : IHI6_2 H4.
    apply cmp_Symm.
    apply cmp_MergeE2 with r1.
    apply cmp_Symm...
Qed.

Lemma bot_cmp_record_r : forall Ttx r l t Ptx DD B A,
    wftc Ttx ->
    cmp Ttx r (r_SingleField l t) ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r A ->
    swft DD B ->
    disjoint DD A (sty_rcd l B).
Proof with eauto.
  introv I1 I2 I3 I4 I5.
  forwards ~ I6 : label_in_cmp_r I2...
  generalize dependent A.
  induction I6; introv I4; inverts I4.
  -
  eapply tvar_in_label_in_cmp_bot...
  -
  constructor...
  -
  apply D_rcdNeq...
  - forwards ~ : IHI6_1 H2.
    apply cmp_Symm.
    apply cmp_MergeE1 with r2.
    apply cmp_Symm...
    forwards ~ : IHI6_2 H4.
    apply cmp_Symm.
    apply cmp_MergeE2 with r1.
    apply cmp_Symm...
Qed.

(* ********************************************************************** *)
(** * Translation of records *)

Lemma bot_trans_rtyp_in_rlist : forall Ptx Ttx r R DD A B,
    wfcl Ttx R ->
    rtyp_in_rlist r R ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r A ->
    trans_rlist Ptx R B ->
    sub DD B A.
Proof with eauto.
  introv WFCL RIN.
  generalize dependent B.
  inductions RIN; introv TRT TRR TRRL; inverts TRRL.
  - forwards ~ : bot_trans_r_uniq TRR H3.
    substs. inverts WFCL.
    assert (swft DD A2). eapply bot_trans_r_regular...
    assert (swft DD A1). eapply trans_r_regular...
    assert (swft DD B0). eapply trans_rlist_regular with (R:=rl)...
    eauto.
  - inverts WFCL.
    forwards ~ : IHRIN H5.
    assert (swft DD A2). eapply bot_trans_r_regular...
    assert (swft DD A1). eapply trans_r_regular...
    assert (swft DD B0). eapply trans_rlist_regular with (R:=rl)...
    apply S_trans with B0...
Qed.

Lemma trans_rtyp_in_rlist : forall Ptx Ttx r R DD A B,
    wfcl Ttx R ->
    rtyp_in_rlist r R ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx r A ->
    trans_rlist Ptx R B ->
    sub DD B A.
Proof with eauto.
  introv WFCL RIN.
  generalize dependent B.
  inductions RIN; introv TRT TRR TRRL; inverts TRRL.
  - forwards ~ : trans_r_uniq TRR H1.
    substs. inverts WFCL.
    assert (swft DD A2). eapply bot_trans_r_regular...
    assert (swft DD A1). eapply trans_r_regular...
    assert (swft DD B0). eapply trans_rlist_regular with (R:=rl)...
    apply S_trans with (sty_and A1 A2)...
  - inverts WFCL.
    forwards ~ : IHRIN H5.
    assert (swft DD A2). eapply bot_trans_r_regular...
    assert (swft DD A1). eapply trans_r_regular...
    assert (swft DD B0). eapply trans_rlist_regular with (R:=rl)...
    apply S_trans with B0...
Qed.

(* ********************************************************************** *)
(** * Translation of Compactibility *)

Lemma trans_r_trans_r_cmp : forall Ttx r1 r2 Ptx DD A B,
    cmp Ttx r1 r2 ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx r1 A ->
    trans_r Ptx r2 B ->
    disjoint DD A B.
Proof with eauto.
  introv CMP WFTC TRT TR1 TR2.
  generalize dependent A.
  generalize dependent B.
  induction CMP; introv TR1 TR2.

  -
  forwards ~ (A' & TR3) : trans_r_exists Ttx Ptx r.
  forwards ~ (B' & TR4) : trans_r_exists Ttx Ptx s.
  forwards ~ : IHCMP TR4 TR3.
  forwards ~ : trans_teq H...
  forwards ~ : trans_teq H0...
  repeat destruct_hypo...
  apply disjoint_sub with (Δ' := DD) (B:=B')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  apply disjoint_sub with (Δ' := DD) (B:=A')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  forwards ~ : IHCMP...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  inverts TR2.
  forwards ~ (A' & [BD TR3]): trans_Ttx_binds' H1 TRT.
  forwards~ : trans_rtyp_in_rlist H2 TRT TR1...

  -
  inverts TR1.
  eapply cmp_record_r...
  eapply trans_rt_regular...

  -
  forwards ~ (C & ?): trans_r_exists Ttx Ptx s2.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and B C)...
  apply disjoint_and in I...
  destruct_hypo...

  -
  forwards ~ (C & ?): trans_r_exists Ttx Ptx s1.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and C B)...
  apply disjoint_and in I...
  destruct_hypo...

  -
  inverts TR1...

  -
  inverts TR1...
  inverts TR2...
  apply D_rcdNeq...
  eapply trans_rt_regular with (rt:=rt5)...
  eapply trans_rt_regular with (rt:=rt')...

  -
  inverts TR1...
  apply D_topR...
  eapply trans_r_regular with (r:=r)...
Qed.

Lemma bot_trans_Ttx_binds' : forall a R Ttx Ptx DD b,
  wftc Ttx ->
  binds a R Ttx ->
  binds a b Ptx ->
  trans_Ttx Ptx Ttx DD ->
  exists A, binds b A DD /\ trans_rlist Ptx R A.
Proof with auto.
  introv WFT BD1 BD2 TR. inductions TR.
  - false.
  - destruct (a == a0). subst.

    *
      assert (BD3 : binds a0 b0 ([(a0, b0)] ++ Ptx)) by auto.
      forwards ~ : binds_unique BD2 BD3. subst.
      assert (BD4 : binds a0 R0 ([(a0, R0)] ++ Ttx)) by auto.
      forwards ~ : binds_unique BD1 BD4. subst.
      exists A... splits...
      forwards ~ : trans_rlist_fresh_head_Eq a0 b0 H.
      apply swft_tvar with DD...
      apply trans_rlist_regular with Ttx R0 Ptx...
      inverts WFT...

    *
      analyze_binds BD1...
      analyze_binds BD2...
      inverts WFT...
      forwards ~ (? & ?) : IHTR...
      destruct_hypo...
      exists x... splits...
      forwards ~ : trans_rlist_fresh_head_Eq a0 b0 H3.
      apply swft_tvar with DD...
      apply swft_from_swfte with b...
      apply trans_Ttx_regular with (Ttx:=Ttx) (Ptx:=Ptx)...
Qed.

Lemma bot_trans_r_bot_trans_r_cmp : forall Ttx r1 r2 Ptx DD A B,
    cmp Ttx r1 r2 ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r1 A ->
    bot_trans_r Ptx r2 B ->
    disjoint DD A B.
Proof with eauto.
  introv CMP WFTC TRT TR1 TR2.
  generalize dependent A.
  generalize dependent B.
  induction CMP; introv TR1 TR2.

  -
  forwards ~ (A' & TR3) : bot_trans_r_exists Ttx Ptx r.
  forwards ~ (B' & TR4) : bot_trans_r_exists Ttx Ptx s.
  forwards ~ : IHCMP TR4 TR3.
  forwards ~ : bot_trans_teq H...
  forwards ~ : bot_trans_teq H0...
  repeat destruct_hypo...
  apply disjoint_sub with (Δ' := DD) (B:=B')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  apply disjoint_sub with (Δ' := DD) (B:=A')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  forwards ~ : IHCMP...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  inverts TR2.
  forwards ~ (A' & [BD TR3]): bot_trans_Ttx_binds' H1 TRT...
  forwards~ : bot_trans_rtyp_in_rlist H2 TRT TR1...

  -
  inverts TR1.
  eapply bot_cmp_record_r...

  -
  forwards ~ (C & ?): bot_trans_r_exists Ttx Ptx s2.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and B C)...
  apply disjoint_and in I...
  destruct_hypo...

  -
  forwards ~ (C & ?): bot_trans_r_exists Ttx Ptx s1.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and C B)...
  apply disjoint_and in I...
  destruct_hypo...

  -
  inverts TR1...

  -
  inverts TR1...
  inverts TR2...

  -
  inverts TR1...
  apply D_topR...
  eapply bot_trans_r_regular with (r:=r)...
Qed.

Lemma bot_trans_r_trans_r_cmp_and_trans_r_bot_trans_r_cmp : forall Ttx r1 r2 Ptx DD A B,
    cmp Ttx r1 r2 ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    (
      trans_r Ptx r1 A ->
      bot_trans_r Ptx r2 B ->
      disjoint DD A B
    ) /\ (
      bot_trans_r Ptx r1 A ->
      trans_r Ptx r2 B ->
      disjoint DD A B )
.
Proof with eauto.
  introv CMP WFTC TRT.
  generalize dependent A.
  generalize dependent B.
  induction CMP; split; introv TR1 TR2.

  -
  forwards ~ (A' & TR3) : trans_r_exists Ttx Ptx r.
  forwards ~ (B' & TR4) : bot_trans_r_exists Ttx Ptx s.
  specialize (IHCMP WFTC TRT B' A').
  destruct IHCMP as [I1 I2].
  forwards ~ : I1.
  forwards ~ : trans_teq H...
  forwards ~ : bot_trans_teq H0...
  repeat destruct_hypo...
  apply disjoint_sub with (Δ' := DD) (B:=B')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  apply disjoint_sub with (Δ' := DD) (B:=A')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  forwards ~ (A' & TR3) : bot_trans_r_exists Ttx Ptx r.
  forwards ~ (B' & TR4) : trans_r_exists Ttx Ptx s.
  specialize (IHCMP WFTC TRT B' A').
  destruct IHCMP as [I1 I2].
  forwards ~ : I2.
  forwards ~ : bot_trans_teq H...
  forwards ~ : trans_teq H0...
  repeat destruct_hypo...
  apply disjoint_sub with (Δ' := DD) (B:=B')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  apply disjoint_sub with (Δ' := DD) (B:=A')...
  eapply trans_Ttx_regular...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  forwards ~ : IHCMP A B...
  destruct_hypo...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  forwards ~ : IHCMP A B...
  destruct_hypo...
  apply disjoint_symmetric...
  eapply uniq_from_swfte...
  eapply trans_Ttx_regular...

  -
  inverts TR1.
  forwards ~ (A' & [BD TR3]): trans_Ttx_binds' H1 TRT...
  forwards~ : bot_trans_rtyp_in_rlist H2 TRT TR2...

  -
  inverts TR1.
  forwards ~ (A' & [BD TR3]): bot_trans_Ttx_binds' H1 TRT...
  forwards~ : trans_rtyp_in_rlist H2 TRT TR2...

  -
  inverts TR2.
  eapply cmp_record_r...

  -
  inverts TR2.
  eapply bot_cmp_record_r...
  eapply trans_rt_regular...

  -
  forwards ~ (C & ?): bot_trans_r_exists Ttx Ptx s2.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and B C) A...
  destruct I as [I1 _]...
  forwards~ I2 : I1.
  apply disjoint_and in I2...
  destruct_hypo...

  -
  forwards ~ (C & ?): trans_r_exists Ttx Ptx s2.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and B C) A...
  destruct I as [_ I1]...
  forwards~ I2 : I1.
  apply disjoint_and in I2...
  destruct_hypo...

  -
  forwards ~ (C & ?): bot_trans_r_exists Ttx Ptx s1.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and C B) A...
  destruct I as [I1 _]...
  forwards~ I2 : I1.
  apply disjoint_and in I2...
  destruct_hypo...

  -
  forwards ~ (C & ?): trans_r_exists Ttx Ptx s1.
  forwards ~ I : cmp_regular CMP.
  destruct I as [I1 I2]. inverts I2...
  forwards ~ I : IHCMP (sty_and C B) A...
  destruct I as [_ I1]...
  forwards~ I2 : I1.
  apply disjoint_and in I2...
  destruct_hypo...

  -
  inverts TR2...

  forwards ~ : IHCMP2 A0 A...
  destruct H as [I1 _].
  forwards ~ I2  : I1.
  forwards ~ : IHCMP3 B0 A...
  destruct H as [I3 _].
  forwards ~ I4  : I3.

  -
  inverts TR2...

  forwards ~ : IHCMP2 A0 A...
  destruct H as [_ I1].
  forwards ~ I2  : I1.
  forwards ~ : IHCMP3 B0 A...
  destruct H as [_ I3].
  forwards ~ I4  : I3.

  -
  inverts TR1...
  inverts TR2...
  apply D_rcdNeq...
  eapply trans_rt_regular with (rt:=rt5)...

  -
  inverts TR1...
  inverts TR2...
  apply D_rcdNeq...
  eapply trans_rt_regular with (rt:=rt')...

  -
  inverts TR2...
  apply D_topR...
  eapply trans_r_regular with (r:=r)...

  -
  inverts TR2...
  apply D_topR...
  eapply bot_trans_r_regular with (r:=r)...
Qed.

Lemma bot_trans_r_trans_r_cmp : forall Ttx r1 r2 Ptx DD A B,
    cmp Ttx r1 r2 ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r1 A ->
    trans_r Ptx r2 B ->
    disjoint DD A B
.
Proof.
  intros.
  forwards ~ (_ & I) : bot_trans_r_trans_r_cmp_and_trans_r_bot_trans_r_cmp A B H H0 H1.
Qed.

Lemma trans_r_bot_trans_r_cmp : forall Ttx r1 r2 Ptx DD A B,
    cmp Ttx r1 r2 ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx r1 A ->
    bot_trans_r Ptx r2 B ->
    disjoint DD A B
.
Proof.
  intros.
  forwards ~ (I & _) : bot_trans_r_trans_r_cmp_and_trans_r_bot_trans_r_cmp A B H H0 H1.
Qed.

Lemma trans_r_trans_rlist_cmpList : forall Ttx r R Ptx DD A B,
    cmpList Ttx r R  ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    trans_r Ptx r A ->
    trans_rlist Ptx R B ->
    disjoint DD A B.
Proof with eauto.
  introv CMP WFTC TRT.
  generalize dependent A.
  generalize dependent B.
  induction CMP; introv TR1 TR2.

  inverts TR2...
  apply D_topR...
  eapply trans_r_regular with (r:=r)...

  inverts TR2...
  forwards ~ : trans_r_bot_trans_r_cmp H TR1 H4...
  forwards ~ : trans_r_trans_r_cmp H TR1 H2...
Qed.

Lemma bot_trans_r_trans_rlist_cmpList : forall Ttx r R Ptx DD A B,
    cmpList Ttx r R  ->
    wftc Ttx ->
    trans_Ttx Ptx Ttx DD ->
    bot_trans_r Ptx r A ->
    trans_rlist Ptx R B ->
    disjoint DD A B.
Proof with eauto.
  introv CMP WFTC TRT.
  generalize dependent A.
  generalize dependent B.
  induction CMP; introv TR1 TR2.

  inverts TR2...
  apply D_topR...
  eapply bot_trans_r_regular with (r:=r)...

  inverts TR2...
  forwards ~ : bot_trans_r_bot_trans_r_cmp H TR1 H4...
  forwards ~ : bot_trans_r_trans_r_cmp H TR1 H2...
Qed.


Lemma trans_Gtx_binds: forall x rt Gtx Ptx GG,
    binds x rt Gtx ->
    trans_Gtx Ptx Gtx GG ->
    exists A, binds x A GG /\ trans_rt Ptx rt A.
Proof with eauto.
  introv BD TR. inductions TR.
  false.
  apply binds_cons_1 in BD.
  destruct BD as [[I1 I2]| I3].
  subst. exists A...

  forwards ~ (? & ?) : IHTR I3.
  destruct_hypo...
Qed.

Lemma translation_well_formed : forall Ptx Ttx Gtx e t E A DD GG,
    wtt Ptx Ttx Gtx e t E ->
    trans_Ttx Ptx Ttx DD ->
    trans_Gtx Ptx Gtx GG ->
    trans_rt Ptx t A ->
    has_type DD GG E Inf A.
Proof with eauto.
  introv WTT TRT TRG TR.
  generalize dependent DD.
  generalize dependent GG.
  generalize dependent A.
  inductions WTT; introv TR TRG TRT.

  -
  forwards ~ (TY & I1) : trans_rt_exists Ttx Ptx rt5.
  forwards ~ : IHWTT I1 TRT...
  forwards ~ : trans_teq H...
  forwards ~ : trans_rt_uniq H0 TR. substs.
  destruct_hypo...

  -
  forwards ~ (TY & [BD I1]): trans_Gtx_binds H2 TRG.
  forwards ~ : trans_rt_uniq I1 TR. substs.
  apply T_var...
  eapply trans_Ttx_regular...
  eapply trans_Gtx_regular...

  -
  inverts TR...
  auto.
  constructor...
  eapply trans_Gtx_regular...
  eapply trans_Ttx_regular...

  -
  inverts TR.
  forwards ~ : trans_rt_uniq H2 H7. substs.
  forwards ~ : trans_rt_uniq H3 H9. substs.
  constructor...
  pick fresh X and apply T_abs...
  eapply trans_rt_regular with (rt:=rt5)...
  forwards ~ : H1 H3 ([(X, A1)] ++ GG) TRT.
  constructor...
  clear Fr.
  assert (swft DD B0).
    apply styping_regular in H4.
    repeat destruct_hypo...
  apply T_sub with B0...

  -
  forwards ~ (TY & I1) : trans_rt_exists Ttx Ptx rt5.
    apply wtt_regular in WTT1.
    repeat destruct_hypo...
    inverts H2...
  forwards ~ : IHWTT1 (sty_arrow TY A)...
  forwards ~ : IHWTT2 I1...
  assert (swft DD TY).
    apply styping_regular in H0.
    repeat destruct_hypo...
  eapply T_app...

  -
  inverts TR as I1.
  inverts I1.
  constructor...
  -
  inverts TR as I1.
  inverts I1.
  constructor...
  eapply trans_Gtx_regular...
  eapply trans_Ttx_regular...

  -
  inverts TR as I1.
  inverts I1.
  constructor...
  eapply trans_r_trans_r_cmp...
  apply wtt_regular in WTT1.
  repeat destruct_hypo...

  -
  inverts TR as I1.
  forwards ~ : trans_r_uniq H I1. substs.
  constructor...
  forwards ~ (TY & I2) : trans_rt_exists Ttx Ptx rt5...
    apply wtt_regular in WTT.
    repeat destruct_hypo...
    inverts H3...
    inverts H6...
    inverts H5...
  forwards ~ : IHWTT...
  assert (swft DD A0 /\ swft DD (sty_rcd l TY)).
    apply styping_regular in H0.
    repeat destruct_hypo...
    inverts H2...
  destruct_hypo...

  -
  forwards ~ (TY & I2) : trans_r_exists Ttx Ptx r...
    apply wtt_regular in WTT.
    repeat destruct_hypo...
    inverts H3...
    inverts H6...
  forwards ~ : IHWTT...
  forwards ~ : trans_rt_uniq H TR. substs.
  assert (swft DD (sty_rcd l A0) /\ swft DD TY).
    apply styping_regular in H0.
    repeat destruct_hypo...
    inverts H2...
  destruct_hypo...

  -
  inverts TR.
  forwards ~ : trans_rlist_uniq H0 H6... substs. clear H6.
  pick fresh X and apply T_tabs.
    eapply trans_rlist_regular...
  unfold open_sty_wrt_sty, open_sexp_wrt_sty.
  simpl.
  assert (I: (open_sty_wrt_sty_rec 0 (sty_var_f X) B) = B).
    change (open_sty_wrt_sty_rec 0 (sty_var_f X) B)
      with (open_sty_wrt_sty B (sty_var_f X))...
    rewrite open_sty_wrt_sty_lc_sty...

  *
  pick fresh Y and apply T_tabs...
    + rewrite I.
      rewrite_env ([(X, B)] ++ DD).
      apply swft_weaken_head...
      eapply trans_rlist_regular...
    + rewrite I.
      specialize H2 with (a:=X) (b:=Y)
                     (A:=(open_sty_wrt_sty (open_sty_wrt_sty_rec 1 (sty_var_f X) A1) (sty_var_f Y)))
                     (GG:=GG)
                     (DD:=([(Y, B)] ++ (X, B) :: DD)).
      forwards ~ : H2...
        ++ apply H8...
        ++ apply trans_Gtx_fresh_head_Eq...
        ++ constructor...
    + apply swfe_fresh_head...
      eapply trans_Gtx_regular with (Ttx:=Ttx)...
      pick_fresh Y.
      forwards ~ I1 : H1 X Y.
      apply wtt_regular in I1.
      repeat destruct_hypo...
      eapply wfc_strengthen...
      simpls...
      inverts H3...

  *
  eapply trans_Gtx_regular with (Ptx:=Ptx) (Ttx:=Ttx)...
  pick_fresh X. pick_fresh Y.
  forwards ~ I1 : H1 X Y.
  apply wtt_regular in I1.
  repeat destruct_hypo...
  eapply wfc_strengthen...
   simpls...
   inverts H3...

  -
  forwards ~ (TY & I1) : trans_rt_exists Ttx Ptx (rt_ConQuan R rt5).
    apply wtt_regular in WTT.
    repeat destruct_hypo...
  forwards ~ : IHWTT...
  inverts I1...
  assert (A0 = (open_sty_wrt_sty (open_sty_wrt_sty_rec 1 A A1) B)).
    apply wtt_regular in WTT.
    repeat destruct_hypo...
    inverts H7...
    pick_fresh X. pick_fresh Y.
    forwards ~ : H8 X Y.
    forwards ~ : trans_rt_substitution_distributivity ([(Y, R)] ++ Ttx) H7 H1 H0...
    eapply H13...
    constructor...
    rewrite <- subst_rtyp_in_rt_intro in H9...
    forwards ~ : trans_rt_uniq TR H9...
    rewrite subst_sty_in_sty_open_sty_wrt_sty in H10...
    rewrite <- subst_sty_in_sty_intro_rec in H10...
    simpl in H10. assert (X <> Y) by auto. case_if.
    rewrite <- subst_sty_in_sty_intro in H10...
    rewrite fv_sty_in_sty_open_sty_wrt_sty_rec_upper_mutual...
  substs.
  apply T_tapp with (B:=B0)...
  assert (I2: (sty_all B0 (open_sty_wrt_sty_rec 1 A A1)) = open_sty_wrt_sty (sty_all B0 A1) A).
    unfold open_sty_wrt_sty. simpls. f_equal...
    change (open_sty_wrt_sty_rec 0 A B0) with (open_sty_wrt_sty B0 A).
    rewrite open_sty_wrt_sty_lc_sty...
  rewrite I2.
  apply T_tapp with (B:=B0)...
  eapply trans_r_trans_rlist_cmpList...
    apply wtt_regular in WTT.
    repeat destruct_hypo...
  eapply bot_trans_r_trans_rlist_cmpList...
    apply wtt_regular in WTT.
    repeat destruct_hypo...
Qed.