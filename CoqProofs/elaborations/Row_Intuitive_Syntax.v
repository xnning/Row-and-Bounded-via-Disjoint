Require Import Metalib.Metatheory.
(** syntax *)
Definition typvar := var.
Definition expvar := var.
Definition i := nat.

Inductive rt : Set := 
 | rt_Base : rt
 | rt_Fun (rt1:rt) (rt2:rt)
 | rt_ConQuan (R:rlist) (rt5:rt)
 | rt_Record (r:rtyp)
with rlist : Set := 
 | R_Empty : rlist
 | R_Cons (r:rtyp) (R:rlist)
with rtyp : Set := 
 | r_TyVar_b (_:nat)
 | r_TyVar_f (a:typvar)
 | r_Empty : rtyp
 | r_SingleField (l:i) (rt5:rt)
 | r_Merge (r1:rtyp) (r2:rtyp).

Inductive rexp : Set := 
 | re_Var_b (_:nat)
 | re_Var_f (x:expvar)
 | re_Lit (_:nat)
 | re_Abs (rt5:rt) (re:rexp)
 | re_App (re1:rexp) (re2:rexp)
 | re_Empty : rexp
 | re_SingleField (l:i) (re:rexp)
 | re_Res (re:rexp) (l:i)
 | re_Merge (re1:rexp) (re2:rexp)
 | re_Selection (re:rexp) (l:i)
 | re_ConTyAbs (R:rlist) (re:rexp)
 | re_ConTyApp (re:rexp) (r:rtyp).

Definition TContext : Set := list (atom * rlist).

Definition GContext : Set := list (atom * rt).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_rtyp_wrt_rtyp_rec (k:nat) (r_5:rtyp) (r__6:rtyp) {struct r__6}: rtyp :=
  match r__6 with
  | (r_TyVar_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => r_TyVar_b nat
        | inleft (right _) => r_5
        | inright _ => r_TyVar_b (nat - 1)
      end
  | (r_TyVar_f a) => r_TyVar_f a
  | r_Empty => r_Empty 
  | (r_SingleField l rt5) => r_SingleField l (open_rt_wrt_rtyp_rec k r_5 rt5)
  | (r_Merge r1 r2) => r_Merge (open_rtyp_wrt_rtyp_rec k r_5 r1) (open_rtyp_wrt_rtyp_rec k r_5 r2)
end
with open_rlist_wrt_rtyp_rec (k:nat) (r5:rtyp) (R5:rlist) {struct R5}: rlist :=
  match R5 with
  | R_Empty => R_Empty 
  | (R_Cons r R) => R_Cons (open_rtyp_wrt_rtyp_rec k r5 r) (open_rlist_wrt_rtyp_rec k r5 R)
end
with open_rt_wrt_rtyp_rec (k:nat) (r5:rtyp) (u5:rt) {struct u5}: rt :=
  match u5 with
  | rt_Base => rt_Base 
  | (rt_Fun rt1 rt2) => rt_Fun (open_rt_wrt_rtyp_rec k r5 rt1) (open_rt_wrt_rtyp_rec k r5 rt2)
  | (rt_ConQuan R rt5) => rt_ConQuan (open_rlist_wrt_rtyp_rec k r5 R) (open_rt_wrt_rtyp_rec (S k) r5 rt5)
  | (rt_Record r) => rt_Record (open_rtyp_wrt_rtyp_rec k r5 r)
end.


Fixpoint open_rexp_wrt_rexp_rec (k:nat) (re_5:rexp) (re__6:rexp) {struct re__6}: rexp :=
  match re__6 with
  | (re_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => re_Var_b nat
        | inleft (right _) => re_5
        | inright _ => re_Var_b (nat - 1)
      end
  | (re_Var_f x) => re_Var_f x
  | (re_Lit i) => re_Lit i
  | (re_Abs rt5 re) => re_Abs rt5 (open_rexp_wrt_rexp_rec (S k) re_5 re)
  | (re_App re1 re2) => re_App (open_rexp_wrt_rexp_rec k re_5 re1) (open_rexp_wrt_rexp_rec k re_5 re2)
  | re_Empty => re_Empty 
  | (re_SingleField l re) => re_SingleField l (open_rexp_wrt_rexp_rec k re_5 re)
  | (re_Res re l) => re_Res (open_rexp_wrt_rexp_rec k re_5 re) l
  | (re_Merge re1 re2) => re_Merge (open_rexp_wrt_rexp_rec k re_5 re1) (open_rexp_wrt_rexp_rec k re_5 re2)
  | (re_Selection re l) => re_Selection (open_rexp_wrt_rexp_rec k re_5 re) l
  | (re_ConTyAbs R re) => re_ConTyAbs R (open_rexp_wrt_rexp_rec k re_5 re)
  | (re_ConTyApp re r) => re_ConTyApp (open_rexp_wrt_rexp_rec k re_5 re) r
end.

Fixpoint open_rexp_wrt_rtyp_rec (k:nat) (r5:rtyp) (re_5:rexp) {struct re_5}: rexp :=
  match re_5 with
  | (re_Var_b nat) => re_Var_b nat
  | (re_Var_f x) => re_Var_f x
  | (re_Lit nat) => re_Lit nat
  | (re_Abs rt5 re) => re_Abs (open_rt_wrt_rtyp_rec k r5 rt5) (open_rexp_wrt_rtyp_rec k r5 re)
  | (re_App re1 re2) => re_App (open_rexp_wrt_rtyp_rec k r5 re1) (open_rexp_wrt_rtyp_rec k r5 re2)
  | re_Empty => re_Empty 
  | (re_SingleField l re) => re_SingleField l (open_rexp_wrt_rtyp_rec k r5 re)
  | (re_Res re l) => re_Res (open_rexp_wrt_rtyp_rec k r5 re) l
  | (re_Merge re1 re2) => re_Merge (open_rexp_wrt_rtyp_rec k r5 re1) (open_rexp_wrt_rtyp_rec k r5 re2)
  | (re_Selection re l) => re_Selection (open_rexp_wrt_rtyp_rec k r5 re) l
  | (re_ConTyAbs R re) => re_ConTyAbs (open_rlist_wrt_rtyp_rec k r5 R) (open_rexp_wrt_rtyp_rec (S k) r5 re)
  | (re_ConTyApp re r) => re_ConTyApp (open_rexp_wrt_rtyp_rec k r5 re) (open_rtyp_wrt_rtyp_rec k r5 r)
end.


Definition open_rt_wrt_rtyp r5 u5 := open_rt_wrt_rtyp_rec 0 u5 r5.

Definition open_rexp_wrt_rexp re_5 re__6 := open_rexp_wrt_rexp_rec 0 re__6 re_5.

Definition open_rtyp_wrt_rtyp r_5 r__6 := open_rtyp_wrt_rtyp_rec 0 r__6 r_5.

Definition open_rexp_wrt_rtyp r5 re_5 := open_rexp_wrt_rtyp_rec 0 re_5 r5.

Definition open_rlist_wrt_rtyp r5 R5 := open_rlist_wrt_rtyp_rec 0 R5 r5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_sty *)

(* defns LC_rtyp_rlist_rt *)
Inductive lc_rtyp : rtyp -> Prop :=    (* defn lc_rtyp *)
 | lc_r_TyVar_f : forall (a:typvar),
     (lc_rtyp (r_TyVar_f a))
 | lc_r_Empty : 
     (lc_rtyp r_Empty)
 | lc_r_SingleField : forall (l:i) (rt5:rt),
     (lc_rt rt5) ->
     (lc_rtyp (r_SingleField l rt5))
 | lc_r_Merge : forall (r1 r2:rtyp),
     (lc_rtyp r1) ->
     (lc_rtyp r2) ->
     (lc_rtyp (r_Merge r1 r2))
with lc_rlist : rlist -> Prop :=    (* defn lc_rlist *)
 | lc_R_Empty : 
     (lc_rlist R_Empty)
 | lc_R_Cons : forall (r:rtyp) (R:rlist),
     (lc_rtyp r) ->
     (lc_rlist R) ->
     (lc_rlist (R_Cons r R))
with lc_rt : rt -> Prop :=    (* defn lc_rt *)
 | lc_rt_Base : 
     (lc_rt rt_Base)
 | lc_rt_Fun : forall (rt1 rt2:rt),
     (lc_rt rt1) ->
     (lc_rt rt2) ->
     (lc_rt (rt_Fun rt1 rt2))
 | lc_rt_ConQuan : forall (R:rlist) (rt5:rt),
     (lc_rlist R) ->
      ( forall a , lc_rt  ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )  )  ->
     (lc_rt (rt_ConQuan R rt5))
 | lc_rt_Record : forall (r:rtyp),
     (lc_rtyp r) ->
     (lc_rt (rt_Record r)).

(* defns LC_rexp *)
Inductive lc_rexp : rexp -> Prop :=    (* defn lc_rexp *)
 | lc_re_Var_f : forall (x:expvar),
     (lc_rexp (re_Var_f x))
 | lc_re_Lit_f : forall (i:nat),
     (lc_rexp (re_Lit i))
 | lc_re_Abs : forall (rt5:rt) (re:rexp),
     (lc_rt rt5) ->
      ( forall x , lc_rexp  ( open_rexp_wrt_rexp re (re_Var_f x) )  )  ->
     (lc_rexp (re_Abs rt5 re))
 | lc_re_App : forall (re1 re2:rexp),
     (lc_rexp re1) ->
     (lc_rexp re2) ->
     (lc_rexp (re_App re1 re2))
 | lc_re_Empty : 
     (lc_rexp re_Empty)
 | lc_re_SingleField : forall (l:i) (re:rexp),
     (lc_rexp re) ->
     (lc_rexp (re_SingleField l re))
 | lc_re_Res : forall (re:rexp) (l:i),
     (lc_rexp re) ->
     (lc_rexp (re_Res re l))
 | lc_re_Merge : forall (re1 re2:rexp),
     (lc_rexp re1) ->
     (lc_rexp re2) ->
     (lc_rexp (re_Merge re1 re2))
 | lc_re_Selection : forall (re:rexp) (l:i),
     (lc_rexp re) ->
     (lc_rexp (re_Selection re l))
 | lc_re_ConTyAbs : forall (R:rlist) (re:rexp),
     (lc_rlist R) ->
      ( forall a , lc_rexp  ( open_rexp_wrt_rtyp re (r_TyVar_f a) )  )  ->
     (lc_rexp (re_ConTyAbs R re))
 | lc_re_ConTyApp : forall (re:rexp) (r:rtyp),
     (lc_rexp re) ->
     (lc_rtyp r) ->
     (lc_rexp (re_ConTyApp re r)).
(** free variables *)
Fixpoint fv_rtyp_in_rtyp (r_5:rtyp) : vars :=
  match r_5 with
  | (r_TyVar_b nat) => {}
  | (r_TyVar_f a) => {{a}}
  | r_Empty => {}
  | (r_SingleField l rt5) => (fv_rtyp_in_rt rt5)
  | (r_Merge r1 r2) => (fv_rtyp_in_rtyp r1) \u (fv_rtyp_in_rtyp r2)
end
with fv_rtyp_in_rlist (R5:rlist) : vars :=
  match R5 with
  | R_Empty => {}
  | (R_Cons r R) => (fv_rtyp_in_rtyp r) \u (fv_rtyp_in_rlist R)
end
with fv_rtyp_in_rt (u5:rt) : vars :=
  match u5 with
  | rt_Base => {}
  | (rt_Fun rt1 rt2) => (fv_rtyp_in_rt rt1) \u (fv_rtyp_in_rt rt2)
  | (rt_ConQuan R rt5) => (fv_rtyp_in_rlist R) \u (fv_rtyp_in_rt rt5)
  | (rt_Record r) => (fv_rtyp_in_rtyp r)
end.

Fixpoint fv_rexp_in_rexp (re_5:rexp) : vars :=
  match re_5 with
  | (re_Var_b nat) => {}
  | (re_Var_f x) => {{x}}
  | (re_Lit nat) => {}
  | (re_Abs rt5 re) => (fv_rexp_in_rexp re)
  | (re_App re1 re2) => (fv_rexp_in_rexp re1) \u (fv_rexp_in_rexp re2)
  | re_Empty => {}
  | (re_SingleField l re) => (fv_rexp_in_rexp re)
  | (re_Res re l) => (fv_rexp_in_rexp re)
  | (re_Merge re1 re2) => (fv_rexp_in_rexp re1) \u (fv_rexp_in_rexp re2)
  | (re_Selection re l) => (fv_rexp_in_rexp re)
  | (re_ConTyAbs R re) => (fv_rexp_in_rexp re)
  | (re_ConTyApp re r) => (fv_rexp_in_rexp re)
end.

Fixpoint fv_rtyp_in_rexp (re_5:rexp) : vars :=
  match re_5 with
  | (re_Var_b nat) => {}
  | (re_Var_f x) => {}
  | (re_Lit nat ) => {}
  | (re_Abs rt5 re) => (fv_rtyp_in_rt rt5) \u (fv_rtyp_in_rexp re)
  | (re_App re1 re2) => (fv_rtyp_in_rexp re1) \u (fv_rtyp_in_rexp re2)
  | re_Empty => {}
  | (re_SingleField l re) => (fv_rtyp_in_rexp re)
  | (re_Res re l) => (fv_rtyp_in_rexp re)
  | (re_Merge re1 re2) => (fv_rtyp_in_rexp re1) \u (fv_rtyp_in_rexp re2)
  | (re_Selection re l) => (fv_rtyp_in_rexp re)
  | (re_ConTyAbs R re) => (fv_rtyp_in_rlist R) \u (fv_rtyp_in_rexp re)
  | (re_ConTyApp re r) => (fv_rtyp_in_rexp re) \u (fv_rtyp_in_rtyp r)
end.

(** substitutions *)
Fixpoint subst_rtyp_in_rtyp (r_5:rtyp) (X5:typvar) (r__6:rtyp) {struct r__6} : rtyp :=
  match r__6 with
  | (r_TyVar_b nat) => r_TyVar_b nat
  | (r_TyVar_f a) => (if eq_var a X5 then r_5 else (r_TyVar_f a))
  | r_Empty => r_Empty 
  | (r_SingleField l rt5) => r_SingleField l (subst_rtyp_in_rt r_5 X5 rt5)
  | (r_Merge r1 r2) => r_Merge (subst_rtyp_in_rtyp r_5 X5 r1) (subst_rtyp_in_rtyp r_5 X5 r2)
end
with subst_rtyp_in_rlist (r5:rtyp) (X5:typvar) (R5:rlist) {struct R5} : rlist :=
  match R5 with
  | R_Empty => R_Empty 
  | (R_Cons r R) => R_Cons (subst_rtyp_in_rtyp r5 X5 r) (subst_rtyp_in_rlist r5 X5 R)
end
with subst_rtyp_in_rt (r5:rtyp) (X5:typvar) (u5:rt) {struct u5} : rt :=
  match u5 with
  | rt_Base => rt_Base 
  | (rt_Fun rt1 rt2) => rt_Fun (subst_rtyp_in_rt r5 X5 rt1) (subst_rtyp_in_rt r5 X5 rt2)
  | (rt_ConQuan R rt5) => rt_ConQuan (subst_rtyp_in_rlist r5 X5 R) (subst_rtyp_in_rt r5 X5 rt5)
  | (rt_Record r) => rt_Record (subst_rtyp_in_rtyp r5 X5 r)
end.

Fixpoint subst_rexp_in_rexp (re_5:rexp) (x5:expvar) (re__6:rexp) {struct re__6} : rexp :=
  match re__6 with
  | (re_Var_b nat) => re_Var_b nat
  | (re_Var_f x) => (if eq_var x x5 then re_5 else (re_Var_f x))
  | (re_Lit nat) => re_Lit nat
  | (re_Abs rt5 re) => re_Abs rt5 (subst_rexp_in_rexp re_5 x5 re)
  | (re_App re1 re2) => re_App (subst_rexp_in_rexp re_5 x5 re1) (subst_rexp_in_rexp re_5 x5 re2)
  | re_Empty => re_Empty 
  | (re_SingleField l re) => re_SingleField l (subst_rexp_in_rexp re_5 x5 re)
  | (re_Res re l) => re_Res (subst_rexp_in_rexp re_5 x5 re) l
  | (re_Merge re1 re2) => re_Merge (subst_rexp_in_rexp re_5 x5 re1) (subst_rexp_in_rexp re_5 x5 re2)
  | (re_Selection re l) => re_Selection (subst_rexp_in_rexp re_5 x5 re) l
  | (re_ConTyAbs R re) => re_ConTyAbs R (subst_rexp_in_rexp re_5 x5 re)
  | (re_ConTyApp re r) => re_ConTyApp (subst_rexp_in_rexp re_5 x5 re) r
end.


Fixpoint subst_rtyp_in_rexp (r5:rtyp) (X5:typvar) (re_5:rexp) {struct re_5} : rexp :=
  match re_5 with
  | (re_Var_b nat) => re_Var_b nat
  | (re_Var_f x) => re_Var_f x
  | (re_Lit nat) => re_Lit nat
  | (re_Abs rt5 re) => re_Abs (subst_rtyp_in_rt r5 X5 rt5) (subst_rtyp_in_rexp r5 X5 re)
  | (re_App re1 re2) => re_App (subst_rtyp_in_rexp r5 X5 re1) (subst_rtyp_in_rexp r5 X5 re2)
  | re_Empty => re_Empty 
  | (re_SingleField l re) => re_SingleField l (subst_rtyp_in_rexp r5 X5 re)
  | (re_Res re l) => re_Res (subst_rtyp_in_rexp r5 X5 re) l
  | (re_Merge re1 re2) => re_Merge (subst_rtyp_in_rexp r5 X5 re1) (subst_rtyp_in_rexp r5 X5 re2)
  | (re_Selection re l) => re_Selection (subst_rtyp_in_rexp r5 X5 re) l
  | (re_ConTyAbs R re) => re_ConTyAbs (subst_rtyp_in_rlist r5 X5 R) (subst_rtyp_in_rexp r5 X5 re)
  | (re_ConTyApp re r) => re_ConTyApp (subst_rtyp_in_rexp r5 X5 re) (subst_rtyp_in_rtyp r5 X5 r)
end.


Inductive rtyp_in_rlist : rtyp -> rlist -> Prop :=
| ti_head : forall r rl,
    rtyp_in_rlist r (R_Cons r rl)
| ti_cons : forall r r' rl,
    rtyp_in_rlist r rl ->
    rtyp_in_rlist r (R_Cons r' rl).


(** definitions *)

(* defns WFTC_WFCL *)
Inductive wftc : TContext -> Prop :=    (* defn wftc *)
 | wftc_Empty : 
     wftc  nil 
 | wftc_Tvar : forall (Ttx:TContext) (a:typvar) (R:rlist),
     wftc Ttx ->
     wfcl Ttx R ->
      ( a  `notin` dom ( Ttx ))  ->
     wftc  (( a ~ R )++ Ttx ) 
with wfcl : TContext -> rlist -> Prop :=    (* defn wfcl *)
 | wfcl_Nil : forall (Ttx:TContext),
     wftc Ttx ->
     wfcl Ttx R_Empty
 | wfcl_Cons : forall (Ttx:TContext) (r:rtyp) (R:rlist),
     wfr Ttx r ->
     wfcl Ttx R ->
     wfcl Ttx (R_Cons r R)
with wfrt : TContext -> rt -> Prop :=    (* defn wfrt *)
 | wfrt_Prim : forall (Ttx:TContext),
     wfrt Ttx rt_Base
 | wfrt_Arrow : forall (Ttx:TContext) (rt1 rt2:rt),
     wfrt Ttx rt1 ->
     wfrt Ttx rt2 ->
     wfrt Ttx (rt_Fun rt1 rt2)
 | wfrt_All : forall (L:vars) (Ttx:TContext) (R:rlist) (rt5:rt),
     wfcl Ttx R ->
      ( forall a , a \notin  L  -> wfrt  (( a ~ R )++ Ttx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )  )  ->
     wfrt Ttx (rt_ConQuan R rt5)
 | wfrt_Rec : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     wfrt Ttx (rt_Record r)
with wfr : TContext -> rtyp -> Prop :=    (* defn wfr *)
 | wfr_Var : forall (Ttx:TContext) (a:typvar) (R:rlist),
      binds  a   R   Ttx  ->
     wfr Ttx (r_TyVar_f a)
 | wfr_Base : forall (Ttx:TContext) (l:i) (rt5:rt),
     wfrt Ttx rt5 ->
     wfr Ttx (r_SingleField l rt5)
 | wfr_Empty : forall (Ttx:TContext),
     wfr Ttx r_Empty
 | wfr_Merge : forall (Ttx:TContext) (r1 r2:rtyp),
     wfr Ttx r1 ->
     wfr Ttx r2 ->
     cmp Ttx r1 r2 ->
     wfr Ttx (r_Merge r1 r2)
with cmp : TContext -> rtyp -> rtyp -> Prop :=    (* defn cmp *)
 | cmp_Eq : forall (Ttx:TContext) (r' s' r s:rtyp),
     cmp Ttx r s ->
     teq Ttx (rt_Record r) (rt_Record r') ->
     teq Ttx (rt_Record s) (rt_Record s') ->
     cmp Ttx r' s'
 | cmp_Symm : forall (Ttx:TContext) (s r:rtyp),
     cmp Ttx r s ->
     cmp Ttx s r
 | cmp_Tvar : forall (Ttx:TContext) (a:typvar) (r:rtyp) (R:rlist),
     wfcl Ttx R ->
     wfr Ttx r ->
      binds  a   R   Ttx  ->
      rtyp_in_rlist  r   R  ->
     cmp Ttx (r_TyVar_f a) r
 | cmp_MergeE1 : forall (Ttx:TContext) (r s1 s2:rtyp),
     cmp Ttx r  (r_Merge s1 s2)  ->
     cmp Ttx r s1
 | cmp_MergeE2 : forall (Ttx:TContext) (r s2 s1:rtyp),
     cmp Ttx r  (r_Merge s1 s2)  ->
     cmp Ttx r s2
 | cmp_MergeI : forall (Ttx:TContext) (r s1 s2:rtyp),
     cmp Ttx s1 s2 ->
     cmp Ttx r s1 ->
     cmp Ttx r s2 ->
     cmp Ttx r  (r_Merge s1 s2) 
 | cmp_BaseBase : forall (Ttx:TContext) (l:i) (rt5:rt) (l':i) (rt':rt),
      l  <>  l'  ->
     wfrt Ttx rt5 ->
     wfrt Ttx rt' ->
     cmp Ttx (r_SingleField l rt5) (r_SingleField l' rt')
 | cmp_Empty : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     cmp Ttx r r_Empty
with ceq : TContext -> rlist -> rlist -> Prop :=    (* defn ceq *)
 | ceq_Refl : forall (Ttx:TContext) (R:rlist),
     wfcl Ttx R ->
     ceq Ttx R R
 | ceq_Symm : forall (Ttx:TContext) (R' R:rlist),
     ceq Ttx R R' ->
     ceq Ttx R' R
 | ceq_Trans : forall (Ttx:TContext) (R R'' R':rlist),
     ceq Ttx R R' ->
     ceq Ttx R' R'' ->
     ceq Ttx R R''
 | ceq_Inner : forall (Ttx:TContext) (r:rtyp) (R:rlist) (r':rtyp) (R':rlist),
     ceq Ttx R R' ->
     teq Ttx (rt_Record r) (rt_Record r') ->
     ceq Ttx (R_Cons r R) (R_Cons r' R')
 | ceq_Swap : forall (Ttx:TContext) (r r':rtyp) (R:rlist),
     wfr Ttx r ->
     wfr Ttx r' ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons r  (R_Cons r' R) ) (R_Cons r'  (R_Cons r R) )
 | ceq_Empty : forall (Ttx:TContext) (R:rlist),
     wfcl Ttx R ->
     ceq Ttx (R_Cons r_Empty R) R
 | ceq_Merge : forall (Ttx:TContext) (r1 r2:rtyp) (R:rlist),
     wfr Ttx (r_Merge r1 r2) ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons  (r_Merge r1 r2)  R) (R_Cons r1  (R_Cons r2 R) )
 | ceq_Dupl : forall (Ttx:TContext) (r:rtyp) (R:rlist),
     wfr Ttx r ->
     wfcl Ttx R ->
     ceq Ttx (R_Cons r  (R_Cons r R) ) (R_Cons r R)
 | ceq_Base : forall (Ttx:TContext) (l:i) (rt5:rt) (R:rlist) (rt':rt),
     wfrt Ttx rt5 ->
     wfrt Ttx rt' ->
     wfcl Ttx R ->
     teq Ttx rt5 rt' ->
     ceq Ttx (R_Cons (r_SingleField l rt5) R) (R_Cons (r_SingleField l rt') R)
with teq : TContext -> rt -> rt -> Prop :=    (* defn teq *)
 | teq_Refl : forall (Ttx:TContext) (rt5:rt),
     wfrt Ttx rt5 ->
     teq Ttx rt5 rt5
 | teq_Symm : forall (Ttx:TContext) (rt' rt5:rt),
     teq Ttx rt5 rt' ->
     teq Ttx rt' rt5
 | teq_Trans : forall (Ttx:TContext) (rt5 rt'' rt':rt),
     teq Ttx rt5 rt' ->
     teq Ttx rt' rt'' ->
     teq Ttx rt5 rt''
 | teq_CongArrow : forall (Ttx:TContext) (rt1 rt2 rt1' rt2':rt),
     teq Ttx rt1 rt1' ->
     teq Ttx rt2 rt2' ->
     teq Ttx (rt_Fun rt1 rt2) (rt_Fun rt1' rt2')
 | teq_CongAll : forall (L:vars) (Ttx:TContext) (R:rlist) (rt5:rt) (R':rlist) (rt':rt),
     ceq Ttx R R' ->
      ( forall a , a \notin  L  -> teq  (( a ~ R )++ Ttx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )   ( open_rt_wrt_rtyp rt' (r_TyVar_f a) )  )  ->
      ( forall a , a \notin  L  -> teq  (( a ~ R' )++ Ttx )   ( open_rt_wrt_rtyp rt5 (r_TyVar_f a) )   ( open_rt_wrt_rtyp rt' (r_TyVar_f a) )  )  ->
     teq Ttx (rt_ConQuan R rt5) (rt_ConQuan R' rt')
 | teq_CongBase : forall (Ttx:TContext) (l:i) (rt5 rt':rt),
     teq Ttx rt5 rt' ->
     teq Ttx (rt_Record (r_SingleField l rt5)) (rt_Record (r_SingleField l rt'))
 | teq_CongMerge : forall (Ttx:TContext) (r1 r2 r1' r2':rtyp),
     teq Ttx (rt_Record r1) (rt_Record r1') ->
     teq Ttx (rt_Record r2) (rt_Record r2') ->
     cmp Ttx r1 r2 ->
     cmp Ttx r1' r2' ->
     teq Ttx (rt_Record (r_Merge r1 r2)) (rt_Record (r_Merge r1' r2'))
 | teq_MergeUnit : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     teq Ttx (rt_Record (r_Merge r r_Empty)) (rt_Record r)
 | teq_MergeAssoc : forall (Ttx:TContext) (r1 r2 r3:rtyp),
     cmp Ttx r1 r2 ->
     cmp Ttx r1 r3 ->
     cmp Ttx r2 r3 ->
     teq Ttx (rt_Record (r_Merge r1  (r_Merge r2 r3) )) (rt_Record (r_Merge  (r_Merge r1 r2)  r3))
 | teq_MergeComm : forall (Ttx:TContext) (r1 r2:rtyp),
     cmp Ttx r1 r2 ->
     teq Ttx (rt_Record (r_Merge r1 r2)) (rt_Record (r_Merge r2 r1)).

(* defns COMLIST *)
Inductive cmpList : TContext -> rtyp -> rlist -> Prop :=    (* defn cmpList *)
 | cmpList_Nil : forall (Ttx:TContext) (r:rtyp),
     wfr Ttx r ->
     cmpList Ttx r R_Empty
 | cmpList_Cons : forall (Ttx:TContext) (r r':rtyp) (R:rlist),
     cmp Ttx r r' ->
     cmpList Ttx r R ->
     cmpList Ttx r (R_Cons r' R).

(* defns WFC *)
Inductive wfc : TContext -> GContext -> Prop :=    (* defn wfc *)
 | wfc_Empty : forall (Ttx:TContext),
     wftc Ttx ->
     wfc Ttx  nil 
 | wfc_Var : forall (Ttx:TContext) (Gtx:GContext) (x:expvar) (rt5:rt),
     wfc Ttx Gtx ->
     wfrt Ttx rt5 ->
      ( x  `notin` dom ( Ttx ))  ->
      ( x  `notin` dom ( Gtx ))  ->
     wfc Ttx  (( x ~ rt5 )++ Gtx ) .

(** infrastructure *)
Hint Constructors  wftc wfcl wfrt wfr cmp ceq teq cmpList wfc lc_rtyp lc_rlist lc_rt lc_rexp.
