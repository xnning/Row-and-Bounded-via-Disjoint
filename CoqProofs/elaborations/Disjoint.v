
Require Import Infrastructure.


Hint Constructors TopLike.

(* ********************************************************************** *)
(** * Properties of disjointness *)

Lemma disjoint_and : forall Δ A B C,
    lc_sty A ->
    disjoint Δ A (sty_and B C) <->
    disjoint Δ A B /\ disjoint Δ A C.
Proof with eauto.
  introv LCA.
  induction LCA.

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL.
    inverts TL.
    inverts WF2.
    inverts TL.
    splits...
    splits...

    introv Dis.
    destruct Dis...

  - splits.

    introv Dis.
    lets (? & Wft): disjoint_regular Dis.
    inverts Wft...

    introv Dis.
    destruct Dis...

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL.
    inverts TL.
    inverts WF2.
    inverts TL.
    splits...
    splits...

    introv Dis.
    inverts Dis...

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL.
    inverts TL.
    inverts WF2.
    inverts TL.
    splits...
    splits...

    splits...
    forwards (Sub1 & Sub2) : sub_andr WF2...
    forwards (Sub1 & Sub2) : sub_andr WF2...

    introv Dis.
    destruct Dis...

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL.
    inverts TL.
    inverts WF1.
    inverts WF2.
    splits...
    inverts TL.
    inverts WF1.
    inverts WF2.
    splits...

    splits...

    introv Dis.
    inverts Dis...

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL.
    inverts TL.
    inverts WF1.
    inverts WF2.
    splits...
    inverts TL.
    inverts WF1.
    inverts WF2.
    splits...

    apply IHLCA1 in WF1...
    apply IHLCA2 in WF2...
    destructs WF1...
    destructs WF2...

    splits...

    introv Dis.
    inverts Dis...

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL...
    inverts TL.
    inverts WF1.
    splits...
    inverts TL.
    inverts WF2.
    splits...

    introv Dis.
    inverts Dis...

  - splits.

    introv Dis.
    inverts Dis as WF1 WF2 TL...
    inverts TL.
    inverts WF1.
    inverts WF2.
    splits...
    inverts TL.
    inverts WF1.
    inverts WF2.
    splits...


    introv Dis.
    inverts Dis...

Qed.


Lemma disjoint_narrow : forall F X U T E A B,
    disjoint (F ++ X ~ U ++ E) A B ->
    sub E T U ->
    uniq (F ++ X ~ U ++ E) ->
    disjoint (F ++ X ~ T ++ E) A B.
Proof with eauto using swft_narrow, sub_narrow.
  introv Dis.
  remember (F ++ X ~ U ++ E) as G.
  generalize dependent F.
  induction Dis; introv EQ Uniq Sub; subst...

  - Case "Var1".
    analyze_binds_uniq H...
    assert (sub (F ++ X ~ T ++ E) T B).
      eapply S_trans...
      rewrite_env (nil ++ (F ++ [(X, T)]) ++ E).
      apply sub_weakening...
    eapply D_tvarL...

  - Case "Var2".
    analyze_binds_uniq H...
    assert (sub (F ++ X ~ T ++ E) T B).
      eapply S_trans...
      rewrite_env (nil ++ (F ++ [(X, T)]) ++ E).
      apply sub_weakening...
    eapply D_tvarR...

  - Case "forall".
    pick fresh Y and apply D_forall...
    rewrite_env (([(Y, sty_and A1 A2)] ++ F) ++ [(X, T)] ++ E)...
Qed.



Lemma disjoint_symmetric: forall Δ A B,
    disjoint Δ A B ->
    uniq Δ ->
    disjoint Δ B A.
Proof with eauto.
  introv Dis.
  induction Dis; introv Uniq...
  pick fresh X and apply D_forall...

  rewrite_env (nil ++ [(X, sty_and A2 A1)] ++ DD).
  eapply disjoint_narrow...
Qed.


Inductive BotDisjoint : stctx -> sty -> Prop :=
| bl_bot : forall Δ A,
    TopLike A ->
    BotDisjoint Δ A
| bl_and : forall Δ A B,
    BotDisjoint Δ A ->
    BotDisjoint Δ B ->
    BotDisjoint Δ (sty_and A B)
| bl_tvar : forall Δ A X,
    binds X A Δ ->
    sub Δ A sty_bot->
    BotDisjoint Δ (sty_var_f X).

Hint Constructors BotDisjoint.


Lemma bot_disjoint : forall Δ A B,
    BotDisjoint Δ A ->
    swft Δ A ->
    swft Δ B ->
    disjoint Δ A B.
Proof with eauto.
  introv Bob.
  gen B.

  induction Bob; introv SWFT1 SWFT2; simpls...

  inverts SWFT1...
Qed.


Lemma disjoint_bot : forall Δ A,
    lc_sty A ->
    uniq Δ ->
    disjoint Δ A sty_bot ->
    BotDisjoint Δ A.

Proof with eauto.
  introv LC.
  gen Δ.
  induction LC; introv Uniq Dis; simpls...

  - inverts Dis as ? HH1 HH2; inverts HH2.
  - inverts Dis as ? HH1 HH2; inverts HH2.
  - inverts Dis as ? HH1 HH2; try solve [inverts HH2]; simpls...
  - inverts Dis as ? HH1 HH2; try solve [inverts HH2]; simpls...
  - inverts Dis as ? HH1 HH2; try solve [inverts HH2]; simpls...
  - inverts Dis as ? HH1 HH2; try solve [inverts HH2]; simpls...
  - inverts Dis as ? HH1 HH2; try solve [inverts HH2]; simpls...
Qed.


Lemma TopLike_sub : forall Δ A B,
    sub Δ A B ->
    TopLike A ->
    TopLike B.
Proof with eauto.
  introv Sub.
  induction Sub; introv TT; try solve [inverts TT; auto]; simpls...

  inverts TT.

  pick fresh X and apply tl_all...

  inverts TT as TT1 TT2.
  inverts TT1...
  inverts TT2...

  inverts TT as TT1 TT2.
  inverts TT1...
  inverts TT2...

  inverts TT as TT1 TT2.
  inverts TT1.
  inverts TT2.
  pick fresh X and apply tl_all...
  unfold open_sty_wrt_sty.
  simpls...

  Unshelve.
  exact (dom DD).
Qed.




Lemma  sub_TopLike_aux : forall Δ B,
    TopLike B ->
    uniq Δ ->
    swft Δ B ->
    sub Δ sty_top B.
Proof with eauto.
  introv Bob.
  gen Δ.

  induction Bob; introv Uniq WFT; auto.

  - Case "and".
    inverts WFT...

  - Case "arr".
    inverts WFT...

  - Case "all".
    inverts WFT.
    pick fresh X.
    forwards : H0 X ([(X, A)] ++ Δ)...
    apply S_trans with (A2 := sty_all sty_top sty_top)...
    pick fresh Y and apply S_forall...

  - Case "rcd".
    inverts WFT...
Qed.



Lemma sub_TopLike : forall Δ A B,
    TopLike B ->
    uniq Δ ->
    swft Δ A ->
    swft Δ B ->
    sub Δ A B.
Proof with eauto.
  introv TT ? ? ?.

  forwards  : sub_TopLike_aux TT...
Qed.



Lemma disjoint_sub : forall Δ Δ' A B C,
    sub Δ' B C ->
    same_stctx Δ' Δ ->
    swfte Δ ->
    disjoint Δ A B ->
    disjoint Δ A C.
Proof with eauto using swft_type.
  introv Sub.
  gen A Δ.

  induction Sub; introv Same Wfte Dis...


  -Case "bot".
   forwards (WFA & ?) : disjoint_regular Dis...
   forwards : disjoint_bot Dis...
   eapply bot_disjoint...

  (* - Case "topArr". *)
  (*   forwards (WFA & ?) : disjoint_regular Dis... *)

  (* - Case "topRcd". *)
  (*   forwards (WFA & ?) : disjoint_regular Dis... *)

  (* - Case "topAll". *)
  (*   forwards (WFA & ?) : disjoint_regular Dis... *)

  - Case "arr".
    forwards (WFA & WFB) : disjoint_regular Dis...
    apply sub_change with (Δ' := Δ) in Sub1...
    apply sub_change with (Δ' := Δ) in Sub2...
    inverts WFB.
    forwards (? & ?) : sub_regular Sub1...
    forwards (? & ?) : sub_regular Sub2...
    induction WFA...

    + SCase "A is bot".
      inverts Dis as WF1 WF2 WF3; auto.
      eapply D_topR...
      inverts WF3...
      constructor.
      eapply TopLike_sub...

    + SCase "A is var".
      inverts Dis as WF1 WF2 WF3...
      inverts WF3.
      eapply D_topR...
      constructor.
      eapply TopLike_sub...

    + SCase "A is arrow".
      inverts Dis as WF1 WF2 WF3; auto.
      inverts WF3...

    + SCase "A is and".
      inverts Dis as WF1 WF2 WF3; auto.

  - Case "andl".
    forwards (? & ?) : disjoint_regular Dis...
    apply disjoint_and in Dis...
    destruct Dis...

  - Case "andr".
    forwards (? & ?) : disjoint_regular Dis...
    apply disjoint_and in Dis...
    destruct Dis...

  - Case "forall".
    forwards (WFA & ?) : disjoint_regular Dis...
    assert (Sub2 : sub DD (sty_all A1 B1) (sty_all A2 B2))...
    apply sub_change with (Δ' := Δ) in Sub...
    apply sub_change with (Δ' := Δ) in Sub2...
    forwards (? & ?) : sub_regular Sub...
    lets (? & ?) : sub_regular Sub2.
    induction WFA...

    + SCase "A is bot".
      inverts Dis as WF1 WF2 WF3; auto.
      eapply D_topR...
      eapply TopLike_sub...

    + SCase "A is var".
      inverts Dis as WF1 WF2 WF3...
      eapply D_topR...
      eapply TopLike_sub...

    + SCase "A is all".
      inverts Dis as WF1 WF2 WF3; auto.
      eapply D_topR...
      eapply TopLike_sub...

      pick fresh X and apply D_forall...
      eapply H0...
      rewrite_env (nil ++ [(X, sty_and A A2)] ++ DD0).
      eapply disjoint_narrow...


    + SCase "A is and".
      inverts Dis as WF1 WF2 WF3; auto.

  - Case "rcd".
    forwards (WFA & ?) : disjoint_regular Dis...
    apply sub_change with (Δ' := Δ) in Sub...
    forwards (? & ?) : sub_regular Sub...
    induction WFA...

    + SCase "A is bot".
      inverts Dis as WF1 WF2 WF3; auto.
      eapply D_topR...
      eapply TopLike_sub...

    + SCase "A is var".
      inverts Dis as WF1 WF2 WF3...
      eapply D_topR...
      eapply TopLike_sub...

    + SCase "A is and".
      inverts Dis as WF1 WF2 WF3; auto.

    + SCase "A is record".
      inverts Dis as WF1 WF2 WF3; auto.
      eapply D_topR...
      eapply TopLike_sub...

  - Case "distArr".
    forwards (WFA & ?) : disjoint_regular Dis...
    apply swft_change with (Δ' := Δ) in H...
    apply swft_change with (Δ' := Δ) in H0...
    apply swft_change with (Δ' := Δ) in H1...
    induction WFA...

    + SCase "A is bot".
      apply disjoint_and in Dis...
      inverts Dis as Dis1 Dis2.
      eapply disjoint_symmetric in Dis1...
      eapply disjoint_symmetric in Dis2...
      eapply disjoint_bot in Dis1...
      inverts Dis1 as Dis1.
      eapply disjoint_bot in Dis2...
      inverts Dis2 as Dis2.
      inverts Dis1.
      inverts Dis2.
      eapply D_topR...

    + SCase "A is var".


      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT; auto.
      inverts TT as TT1.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT as TT2.
      eapply D_topR...
      forwards : binds_unique WF21 H3; auto.
      substs.
      forwards : sub_TopLike DD0 A3 TT1...
      assert (sub DD0 (sty_arrow A1 A3) (sty_arrow A1 (sty_and A2 A3)))...

      forwards : binds_unique WF11 H3; auto.
      substs.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT as TT.
      forwards  : sub_TopLike DD0 A2 TT...
      assert (sub DD0 (sty_arrow A1 A2) (sty_arrow A1 (sty_and A2 A3)))...

      forwards : binds_unique WF21 H3; auto.
      substs...


    + SCase "A is arrow".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT; auto.
      inverts TT.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT.
      eapply D_topR...

      inverts WF2 as WF21 WF22 TT1 TT2; auto.
      inverts TT1...

    + SCase "A is and".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.


      inverts WF1 as WF11 WF12 TT; auto.
      inverts TT.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT.
      eapply D_topR...
      eapply D_andL...

      inverts WF2 as WF21 WF22 TT; auto.

  - Case "distRcd".
    forwards (WFA & ?) : disjoint_regular Dis...
    apply swft_change with (Δ' := Δ) in H...
    apply swft_change with (Δ' := Δ) in H0...
    induction WFA...


    + SCase "A is bot".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      eapply disjoint_symmetric in WF1...
      eapply disjoint_symmetric in WF2...
      forwards WW1: disjoint_bot WF1...
      forwards WW2: disjoint_bot WF2...
      inverts WW1 as WW1.
      inverts WW2 as WW2.
      inverts WW1.
      inverts WW2.
      eapply D_topR...

    + SCase "A is var".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT; auto.
      inverts TT as TT1.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT as TT2.
      eapply D_topR...
      forwards : binds_unique WF21 H2; auto.
      substs.
      forwards : sub_TopLike DD0 B TT1...
      assert (sub DD0 (sty_rcd l B) (sty_rcd l (sty_and A B)))...

      forwards : binds_unique WF11 H2; auto.
      substs.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT as TT.
      forwards : sub_TopLike DD0 A TT...
      assert (sub DD0 (sty_rcd l A) (sty_rcd l (sty_and A B)))...

      forwards : binds_unique WF21 H2; auto.
      substs...

    + SCase "A is and".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT; auto.
      inverts TT.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT.
      eapply D_topR...
      eapply D_andL...


      inverts WF2 as WF21 WF22 TT; auto.

    + SCase "A is record".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT; auto.
      inverts TT.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT.
      eapply D_topR...

      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT.
      eapply D_rcdEq...


  - Case "distPoly".
    forwards (WFA & WFB) : disjoint_regular Dis...
    inverts WFB as WFB1 WFB2.
    assert (swft Δ (sty_all A (sty_and B1 B2))).
      inverts WFB2.
      inverts WFB1.
      pick fresh X and apply swft_all...
      unfold open_sty_wrt_sty.
      simpl...

    induction WFA...


    + SCase "A is bot".


      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      eapply disjoint_symmetric in WF1...
      eapply disjoint_symmetric in WF2...
      forwards WW1: disjoint_bot WF1...
      forwards WW2: disjoint_bot WF2...
      inverts WW1 as WW1.
      inverts WW2 as WW2.
      inverts WW1 as WW1.
      inverts WW2 as WW2.
      eapply D_topR...
      pick fresh X and apply tl_all.
      forwards : WW1...
      forwards : WW2...
      unfold open_sty_wrt_sty in *.
      simpls...

    + SCase "A is var".

      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT1; auto.
      inverts WF2 as WF21 WF22 TT2; auto.
      inverts TT1 as TT1.
      inverts TT2 as TT2.
      eapply D_topR...
      pick fresh Y and apply tl_all...
      forwards : TT1...
      forwards : TT2...
      unfold open_sty_wrt_sty in *.
      simpls...

      forwards : binds_unique WF21 H3; auto.
      substs.
      inverts TT1 as TT1.
      inverts WFB1.
      inverts WFB2.
      pick fresh Y.
      forwards TT : TT1 Y...
      clear TT1.
      forwards Imp: sub_TopLike ([(Y, A)] ++ DD0) (open_sty_wrt_sty B2 (sty_var_f Y)) TT...
      assert (sub DD0 (sty_all A B2) (sty_all A (sty_and B1 B2)))...
      pick fresh Z and apply S_forall...
      forwards Imp' : sub_renaming Y Z Imp...
      unfold open_sty_wrt_sty.
      simpls...

      forwards : binds_unique WF11 H3; auto.
      substs.
      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT as TT.
      inverts WFB1.
      inverts WFB2.
      pick fresh Y.
      forwards TT' : TT Y...
      clear TT.
      forwards Imp: sub_TopLike ([(Y, A)] ++ DD0) (open_sty_wrt_sty B1 (sty_var_f Y)) TT'...
      assert (sub DD0 (sty_all A B1) (sty_all A (sty_and B1 B2)))...
      pick fresh Z and apply S_forall...
      forwards Imp' : sub_renaming Y Z Imp...
      unfold open_sty_wrt_sty.
      simpls...


      forwards : binds_unique WF21 H3; auto.
      substs.

      apply D_tvarL with (A := A0)...
      apply S_trans with (A2 := sty_and (sty_all A B1) (sty_all A B2))...
      eapply S_distPoly...


    + SCase "A is all".


      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT1; auto.
      inverts WF2 as WF21 WF22 TT2; auto.
      inverts TT1 as TT1.
      inverts TT2 as TT2.
      eapply D_topR...
      pick fresh Y and apply tl_all...
      forwards : TT1...
      forwards : TT2...
      unfold open_sty_wrt_sty in *.
      simpls...

      inverts TT1.
      pick fresh X and apply D_forall...
      unfold open_sty_wrt_sty.
      simpls...
      eapply disjoint_and...
      splits...
      eapply D_topR...
      inverts WFB1...
      eapply swft_change...
      econstructor...
      eapply swft_change...
      econstructor...

      inverts WF2 as WF21 WF22 TT; auto.
      inverts TT as TT.
      pick fresh X and apply D_forall...
      unfold open_sty_wrt_sty.
      simpls.
      eapply disjoint_and...
      splits...
      eapply D_topR...
      eapply swft_change...
      econstructor...
      eapply swft_change...
      econstructor...

      pick fresh X and apply D_forall...
      unfold open_sty_wrt_sty.
      simpls...

    + SCase "A is and".
      apply disjoint_and in Dis...
      inverts Dis as WF1 WF2.

      inverts WF1 as WF11 WF12 TT1; auto.
      inverts WF2 as WF21 WF22 TT2; auto.

      inverts WF2 as WF21 WF22 TT; auto.

      (* WTF? *)
      Unshelve.
      exact (dom DD).
      exact (dom DD).

Qed.



Lemma disjoint_weakening : forall G F E A B,
  disjoint (G ++ E) A B ->
  uniq (G ++ F ++ E) ->
  disjoint (G ++ F ++ E) A B.
Proof with eauto using sub_weakening, swft_weaken.
  introv Dis.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Dis; introv EQ Ok; subst...

  pick fresh X and apply D_forall...
  rewrite_env (([(X, sty_and A1 A2)] ++ G) ++ F ++ E).
  eapply H0...
  solve_uniq.
Qed.

(* Lemma disjoint_subst : forall Z E F C A B P, *)
(*   disjoint (F ++ Z ~ C ++ E) A B -> *)
(*   swfte (F ++ Z ~ C ++ E) -> *)
(*   swft E P -> *)
(*   disjoint E P C -> *)
(*   swfte (map (subst_sty_in_sty P Z) F ++ E) -> *)
(*   disjoint (map (subst_sty_in_sty P Z) F ++ E) (subst_sty_in_sty P Z A) (subst_sty_in_sty P Z B). *)
(* Proof with eauto using subst_sty_in_sty_lc_sty, swft_subst_tb, swft_type, same_eq. *)
(*   introv WT EP. *)
(*   remember (F ++ Z ~ C ++ E) as G. *)
(*   generalize dependent F. *)
(*   induction WT; introv Eq Wft Dis Uniq; substs; simpl... *)

(*   constructor; *)
(*   replace (sty_all (subst_sty_in_sty P Z A1) (subst_sty_in_sty P Z B1)) with (subst_sty_in_sty P Z (sty_all A1 B1))... *)
(*   constructor; *)
(*   replace (sty_all (subst_sty_in_sty P Z A1) (subst_sty_in_sty P Z B1)) with (subst_sty_in_sty P Z (sty_all A1 B1))... *)
(*   constructor; *)
(*   replace (sty_all (subst_sty_in_sty P Z A1) (subst_sty_in_sty P Z B1)) with (subst_sty_in_sty P Z (sty_all A1 B1))... *)
(*   constructor; *)
(*   replace (sty_all (subst_sty_in_sty P Z A1) (subst_sty_in_sty P Z B1)) with (subst_sty_in_sty P Z (sty_all A1 B1))... *)
(*   constructor; *)
(*   replace (sty_all (subst_sty_in_sty P Z A1) (subst_sty_in_sty P Z B1)) with (subst_sty_in_sty P Z (sty_all A1 B1))... *)
(*   constructor; *)
(*   replace (sty_all (subst_sty_in_sty P Z A1) (subst_sty_in_sty P Z B1)) with (subst_sty_in_sty P Z (sty_all A1 B1))... *)


(*   - Case "Var1". *)
(*     case_if. *)
(*     substs. *)
(*     analyze_binds_uniq H... *)
(*     substs... *)
(*     apply disjoint_sub with (Δ' := (map (subst_sty_in_sty P Z) F ++ E)) (B := (subst_sty_in_sty P Z C)) (c := c)... *)
(*     eapply sub_subst... *)
(*     replace (subst_sty_in_sty P Z C) with C. *)
(*     rewrite_env (nil ++ map (subst_sty_in_sty P Z) F ++ E). *)
(*     eapply disjoint_weakening... *)
(*     rewrite subst_sty_in_sty_fresh_eq... *)
(*     clear Uniq. *)
(*     eapply swfte_tvar... *)

(*     analyze_binds_uniq H... *)
(*     eapply D_tvarL... *)
(*     eapply sub_subst... *)

(*     eapply D_tvarL... *)
(*     replace A with (subst_sty_in_sty P Z A). *)
(*     eapply sub_subst... *)
(*     rewrite subst_sty_in_sty_fresh_eq... *)
(*     apply swft_tvar with (D := E)... *)
(*     eapply swft_from_swfte... *)
(*     eapply swfte_strength... *)
(*     inverts BindsTacSideCond0... *)


(*   - Case "Var2". *)
(*     eapply disjoint_symmetric... *)
(*     case_if. *)
(*     substs. *)
(*     analyze_binds_uniq H... *)
(*     substs... *)
(*     apply disjoint_sub with (Δ' := (map (subst_sty_in_sty P Z) F ++ E)) (B := (subst_sty_in_sty P Z C)) (c := c)... *)
(*     eapply sub_subst... *)
(*     replace (subst_sty_in_sty P Z C) with C. *)
(*     rewrite_env (nil ++ map (subst_sty_in_sty P Z) F ++ E). *)
(*     eapply disjoint_weakening... *)
(*     rewrite subst_sty_in_sty_fresh_eq... *)
(*     clear Uniq. *)
(*     eapply swfte_tvar... *)

(*     analyze_binds_uniq H... *)
(*     eapply D_tvarL... *)
(*     eapply sub_subst... *)

(*     eapply D_tvarL... *)
(*     replace A with (subst_sty_in_sty P Z A). *)
(*     eapply sub_subst... *)
(*     rewrite subst_sty_in_sty_fresh_eq... *)
(*     apply swft_tvar with (D := E)... *)
(*     eapply swft_from_swfte... *)
(*     eapply swfte_strength... *)
(*     inverts BindsTacSideCond0... *)


(*   - Case "forall". *)

(*     pick fresh Y and apply D_forall... *)
(*     rewrite subst_sty_in_sty_open_sty_wrt_sty_var... *)
(*     rewrite subst_sty_in_sty_open_sty_wrt_sty_var... *)
(*     rewrite_env (map (subst_sty_in_sty P Z) ([(Y, sty_and A1 A2)] ++ F) ++ E). *)
(*     apply H0... *)

(*     simpl; constructor... *)

(* Qed. *)


Lemma subst_toplike : forall C x B,
    TopLike B ->
    lc_sty C ->
    TopLike (subst_sty_in_sty C x B).
Proof with eauto.
  introv TT.
  gen C x.

  induction TT; introv LC; simpls...

  pick fresh X and apply tl_all...
  rewrite subst_sty_in_sty_open_sty_wrt_sty_var...
Qed.

