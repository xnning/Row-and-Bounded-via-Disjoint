Require Import Metalib.Metatheory.
(** syntax *)
Definition typvar := var.
Definition expvar := var.
Definition i := nat.

Inductive sty : Set := 
 | sty_nat : sty
 | sty_top : sty
 | sty_bot : sty
 | sty_var_b (_:nat)
 | sty_var_f (X:typvar)
 | sty_arrow (A:sty) (B:sty)
 | sty_and (A:sty) (B:sty)
 | sty_all (A:sty) (B:sty)
 | sty_rcd (l:i) (A:sty).

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

Definition stctx : Set := list ( atom * sty ).

Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

Inductive sexp : Set := 
 | sexp_var_b (_:nat)
 | sexp_var_f (x:expvar)
 | sexp_top : sexp
 | sexp_lit (i5:i)
 | sexp_abs (ee:sexp)
 | sexp_app (ee1:sexp) (ee2:sexp)
 | sexp_merge (ee1:sexp) (ee2:sexp)
 | sexp_tabs (A:sty) (ee:sexp)
 | sexp_tapp (ee:sexp) (A:sty)
 | sexp_anno (ee:sexp) (A:sty)
 | sexp_rcd (l:i) (ee:sexp)
 | sexp_proj (ee:sexp) (l:i).

Definition sctx : Set := list ( atom * sty ).

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

Definition PContext : Set := list (atom * atom).

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

Fixpoint open_sty_wrt_sty_rec (k:nat) (A5:sty) (A_6:sty) {struct A_6}: sty :=
  match A_6 with
  | sty_nat => sty_nat 
  | sty_top => sty_top 
  | sty_bot => sty_bot 
  | (sty_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => sty_var_b nat
        | inleft (right _) => A5
        | inright _ => sty_var_b (nat - 1)
      end
  | (sty_var_f X) => sty_var_f X
  | (sty_arrow A B) => sty_arrow (open_sty_wrt_sty_rec k A5 A) (open_sty_wrt_sty_rec k A5 B)
  | (sty_and A B) => sty_and (open_sty_wrt_sty_rec k A5 A) (open_sty_wrt_sty_rec k A5 B)
  | (sty_all A B) => sty_all (open_sty_wrt_sty_rec k A5 A) (open_sty_wrt_sty_rec (S k) A5 B)
  | (sty_rcd l A) => sty_rcd l (open_sty_wrt_sty_rec k A5 A)
end.

Fixpoint open_sexp_wrt_sexp_rec (k:nat) (ee_5:sexp) (ee__6:sexp) {struct ee__6}: sexp :=
  match ee__6 with
  | (sexp_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => sexp_var_b nat
        | inleft (right _) => ee_5
        | inright _ => sexp_var_b (nat - 1)
      end
  | (sexp_var_f x) => sexp_var_f x
  | sexp_top => sexp_top 
  | sexp_lit i5 => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (open_sexp_wrt_sexp_rec (S k) ee_5 ee)
  | (sexp_app ee1 ee2) => sexp_app (open_sexp_wrt_sexp_rec k ee_5 ee1) (open_sexp_wrt_sexp_rec k ee_5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (open_sexp_wrt_sexp_rec k ee_5 ee1) (open_sexp_wrt_sexp_rec k ee_5 ee2)
  | (sexp_tabs A ee) => sexp_tabs A (open_sexp_wrt_sexp_rec k ee_5 ee)
  | (sexp_tapp ee A) => sexp_tapp (open_sexp_wrt_sexp_rec k ee_5 ee) A
  | (sexp_anno ee A) => sexp_anno (open_sexp_wrt_sexp_rec k ee_5 ee) A
  | (sexp_rcd l ee) => sexp_rcd l (open_sexp_wrt_sexp_rec k ee_5 ee)
  | (sexp_proj ee l) => sexp_proj (open_sexp_wrt_sexp_rec k ee_5 ee) l
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

Fixpoint open_sexp_wrt_sty_rec (k:nat) (A5:sty) (ee_5:sexp) {struct ee_5}: sexp :=
  match ee_5 with
  | (sexp_var_b nat) => sexp_var_b nat
  | (sexp_var_f x) => sexp_var_f x
  | sexp_top => sexp_top 
  | sexp_lit i5 => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (open_sexp_wrt_sty_rec k A5 ee)
  | (sexp_app ee1 ee2) => sexp_app (open_sexp_wrt_sty_rec k A5 ee1) (open_sexp_wrt_sty_rec k A5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (open_sexp_wrt_sty_rec k A5 ee1) (open_sexp_wrt_sty_rec k A5 ee2)
  | (sexp_tabs A ee) => sexp_tabs (open_sty_wrt_sty_rec k A5 A) (open_sexp_wrt_sty_rec (S k) A5 ee)
  | (sexp_tapp ee A) => sexp_tapp (open_sexp_wrt_sty_rec k A5 ee) (open_sty_wrt_sty_rec k A5 A)
  | (sexp_anno ee A) => sexp_anno (open_sexp_wrt_sty_rec k A5 ee) (open_sty_wrt_sty_rec k A5 A)
  | (sexp_rcd l ee) => sexp_rcd l (open_sexp_wrt_sty_rec k A5 ee)
  | (sexp_proj ee l) => sexp_proj (open_sexp_wrt_sty_rec k A5 ee) l
end.

Definition open_rt_wrt_rtyp r5 u5 := open_rt_wrt_rtyp_rec 0 u5 r5.

Definition open_sexp_wrt_sexp ee_5 ee__6 := open_sexp_wrt_sexp_rec 0 ee__6 ee_5.

Definition open_rexp_wrt_rexp re_5 re__6 := open_rexp_wrt_rexp_rec 0 re__6 re_5.

Definition open_rtyp_wrt_rtyp r_5 r__6 := open_rtyp_wrt_rtyp_rec 0 r__6 r_5.

Definition open_rexp_wrt_rtyp r5 re_5 := open_rexp_wrt_rtyp_rec 0 re_5 r5.

Definition open_sexp_wrt_sty A5 ee_5 := open_sexp_wrt_sty_rec 0 ee_5 A5.

Definition open_sty_wrt_sty A5 A_6 := open_sty_wrt_sty_rec 0 A_6 A5.

Definition open_rlist_wrt_rtyp r5 R5 := open_rlist_wrt_rtyp_rec 0 R5 r5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_sty *)
Inductive lc_sty : sty -> Prop :=    (* defn lc_sty *)
 | lc_sty_nat : 
     (lc_sty sty_nat)
 | lc_sty_top : 
     (lc_sty sty_top)
 | lc_sty_bot : 
     (lc_sty sty_bot)
 | lc_sty_var_f : forall (X:typvar),
     (lc_sty (sty_var_f X))
 | lc_sty_arrow : forall (A B:sty),
     (lc_sty A) ->
     (lc_sty B) ->
     (lc_sty (sty_arrow A B))
 | lc_sty_and : forall (A B:sty),
     (lc_sty A) ->
     (lc_sty B) ->
     (lc_sty (sty_and A B))
 | lc_sty_all : forall (A B:sty),
     (lc_sty A) ->
      ( forall X , lc_sty  ( open_sty_wrt_sty B (sty_var_f X) )  )  ->
     (lc_sty (sty_all A B))
 | lc_sty_rcd : forall (l:i) (A:sty),
     (lc_sty A) ->
     (lc_sty (sty_rcd l A)).

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

(* defns LC_sexp *)
Inductive lc_sexp : sexp -> Prop :=    (* defn lc_sexp *)
 | lc_sexp_var_f : forall (x:expvar),
     (lc_sexp (sexp_var_f x))
 | lc_sexp_top : 
     (lc_sexp sexp_top)
 | lc_sexp_lit : forall i5, 
     (lc_sexp (sexp_lit i5))
 | lc_sexp_abs : forall (ee:sexp),
      ( forall x , lc_sexp  ( open_sexp_wrt_sexp ee (sexp_var_f x) )  )  ->
     (lc_sexp (sexp_abs ee))
 | lc_sexp_app : forall (ee1 ee2:sexp),
     (lc_sexp ee1) ->
     (lc_sexp ee2) ->
     (lc_sexp (sexp_app ee1 ee2))
 | lc_sexp_merge : forall (ee1 ee2:sexp),
     (lc_sexp ee1) ->
     (lc_sexp ee2) ->
     (lc_sexp (sexp_merge ee1 ee2))
 | lc_sexp_tabs : forall (A:sty) (ee:sexp),
     (lc_sty A) ->
      ( forall X , lc_sexp  ( open_sexp_wrt_sty ee (sty_var_f X) )  )  ->
     (lc_sexp (sexp_tabs A ee))
 | lc_sexp_tapp : forall (ee:sexp) (A:sty),
     (lc_sexp ee) ->
     (lc_sty A) ->
     (lc_sexp (sexp_tapp ee A))
 | lc_sexp_anno : forall (ee:sexp) (A:sty),
     (lc_sexp ee) ->
     (lc_sty A) ->
     (lc_sexp (sexp_anno ee A))
 | lc_sexp_rcd : forall (l:i) (ee:sexp),
     (lc_sexp ee) ->
     (lc_sexp (sexp_rcd l ee))
 | lc_sexp_proj : forall (ee:sexp) (l:i),
     (lc_sexp ee) ->
     (lc_sexp (sexp_proj ee l)).

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
Fixpoint fv_sty_in_sty (A5:sty) : vars :=
  match A5 with
  | sty_nat => {}
  | sty_top => {}
  | sty_bot => {}
  | (sty_var_b nat) => {}
  | (sty_var_f X) => {{X}}
  | (sty_arrow A B) => (fv_sty_in_sty A) \u (fv_sty_in_sty B)
  | (sty_and A B) => (fv_sty_in_sty A) \u (fv_sty_in_sty B)
  | (sty_all A B) => (fv_sty_in_sty A) \u (fv_sty_in_sty B)
  | (sty_rcd l A) => (fv_sty_in_sty A)
end.

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

Fixpoint fv_sexp_in_sexp (ee_5:sexp) : vars :=
  match ee_5 with
  | (sexp_var_b nat) => {}
  | (sexp_var_f x) => {{x}}
  | sexp_top => {}
  | sexp_lit _ => {}
  | (sexp_abs ee) => (fv_sexp_in_sexp ee)
  | (sexp_app ee1 ee2) => (fv_sexp_in_sexp ee1) \u (fv_sexp_in_sexp ee2)
  | (sexp_merge ee1 ee2) => (fv_sexp_in_sexp ee1) \u (fv_sexp_in_sexp ee2)
  | (sexp_tabs A ee) => (fv_sexp_in_sexp ee)
  | (sexp_tapp ee A) => (fv_sexp_in_sexp ee)
  | (sexp_anno ee A) => (fv_sexp_in_sexp ee)
  | (sexp_rcd l ee) => (fv_sexp_in_sexp ee)
  | (sexp_proj ee l) => (fv_sexp_in_sexp ee)
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

Fixpoint fv_sty_in_sexp (ee_5:sexp) : vars :=
  match ee_5 with
  | (sexp_var_b nat) => {}
  | (sexp_var_f x) => {}
  | sexp_top => {}
  | sexp_lit _ => {}
  | (sexp_abs ee) => (fv_sty_in_sexp ee)
  | (sexp_app ee1 ee2) => (fv_sty_in_sexp ee1) \u (fv_sty_in_sexp ee2)
  | (sexp_merge ee1 ee2) => (fv_sty_in_sexp ee1) \u (fv_sty_in_sexp ee2)
  | (sexp_tabs A ee) => (fv_sty_in_sty A) \u (fv_sty_in_sexp ee)
  | (sexp_tapp ee A) => (fv_sty_in_sexp ee) \u (fv_sty_in_sty A)
  | (sexp_anno ee A) => (fv_sty_in_sexp ee) \u (fv_sty_in_sty A)
  | (sexp_rcd l ee) => (fv_sty_in_sexp ee)
  | (sexp_proj ee l) => (fv_sty_in_sexp ee)
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
Fixpoint subst_sty_in_sty (A5:sty) (X5:typvar) (A_6:sty) {struct A_6} : sty :=
  match A_6 with
  | sty_nat => sty_nat 
  | sty_top => sty_top 
  | sty_bot => sty_bot 
  | (sty_var_b nat) => sty_var_b nat
  | (sty_var_f X) => (if eq_var X X5 then A5 else (sty_var_f X))
  | (sty_arrow A B) => sty_arrow (subst_sty_in_sty A5 X5 A) (subst_sty_in_sty A5 X5 B)
  | (sty_and A B) => sty_and (subst_sty_in_sty A5 X5 A) (subst_sty_in_sty A5 X5 B)
  | (sty_all A B) => sty_all (subst_sty_in_sty A5 X5 A) (subst_sty_in_sty A5 X5 B)
  | (sty_rcd l A) => sty_rcd l (subst_sty_in_sty A5 X5 A)
end.

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

Fixpoint subst_sexp_in_sexp (ee_5:sexp) (x5:expvar) (ee__6:sexp) {struct ee__6} : sexp :=
  match ee__6 with
  | (sexp_var_b nat) => sexp_var_b nat
  | (sexp_var_f x) => (if eq_var x x5 then ee_5 else (sexp_var_f x))
  | sexp_top => sexp_top 
  | sexp_lit i5 => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (subst_sexp_in_sexp ee_5 x5 ee)
  | (sexp_app ee1 ee2) => sexp_app (subst_sexp_in_sexp ee_5 x5 ee1) (subst_sexp_in_sexp ee_5 x5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (subst_sexp_in_sexp ee_5 x5 ee1) (subst_sexp_in_sexp ee_5 x5 ee2)
  | (sexp_tabs A ee) => sexp_tabs A (subst_sexp_in_sexp ee_5 x5 ee)
  | (sexp_tapp ee A) => sexp_tapp (subst_sexp_in_sexp ee_5 x5 ee) A
  | (sexp_anno ee A) => sexp_anno (subst_sexp_in_sexp ee_5 x5 ee) A
  | (sexp_rcd l ee) => sexp_rcd l (subst_sexp_in_sexp ee_5 x5 ee)
  | (sexp_proj ee l) => sexp_proj (subst_sexp_in_sexp ee_5 x5 ee) l
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

Fixpoint subst_sty_in_sexp (A5:sty) (X5:typvar) (ee_5:sexp) {struct ee_5} : sexp :=
  match ee_5 with
  | (sexp_var_b nat) => sexp_var_b nat
  | (sexp_var_f x) => sexp_var_f x
  | sexp_top => sexp_top 
  | sexp_lit i5 => sexp_lit i5
  | (sexp_abs ee) => sexp_abs (subst_sty_in_sexp A5 X5 ee)
  | (sexp_app ee1 ee2) => sexp_app (subst_sty_in_sexp A5 X5 ee1) (subst_sty_in_sexp A5 X5 ee2)
  | (sexp_merge ee1 ee2) => sexp_merge (subst_sty_in_sexp A5 X5 ee1) (subst_sty_in_sexp A5 X5 ee2)
  | (sexp_tabs A ee) => sexp_tabs (subst_sty_in_sty A5 X5 A) (subst_sty_in_sexp A5 X5 ee)
  | (sexp_tapp ee A) => sexp_tapp (subst_sty_in_sexp A5 X5 ee) (subst_sty_in_sty A5 X5 A)
  | (sexp_anno ee A) => sexp_anno (subst_sty_in_sexp A5 X5 ee) (subst_sty_in_sty A5 X5 A)
  | (sexp_rcd l ee) => sexp_rcd l (subst_sty_in_sexp A5 X5 ee)
  | (sexp_proj ee l) => sexp_proj (subst_sty_in_sexp A5 X5 ee) l
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



Inductive TopLike : sty -> Prop :=
| tl_top : TopLike sty_top
| tl_and : forall A B,
    TopLike A ->
    TopLike B ->
    TopLike (sty_and A B)
| tl_arr : forall A B,
    TopLike B ->
    TopLike (sty_arrow A B)
| tl_all : forall L A B,
    (forall X, X `notin` L -> TopLike (open_sty_wrt_sty B (sty_var_f X))) ->
    TopLike (sty_all A B)
| tl_rcd : forall A l,
    TopLike A ->
    TopLike (sty_rcd l A).



Inductive rtyp_in_rlist : rtyp -> rlist -> Prop :=
| ti_head : forall r rl,
    rtyp_in_rlist r (R_Cons r rl)
| ti_cons : forall r r' rl,
    rtyp_in_rlist r rl ->
    rtyp_in_rlist r (R_Cons r' rl).

Fixpoint fv_Ptx (Ptx : PContext) {struct Ptx} : vars :=
  match Ptx with
  | nil            => {}
  | cons (x, y) P' => singleton y \u fv_Ptx P'
  end.


(** definitions *)

(* defns Jswft *)
Inductive swft : stctx -> sty -> Prop :=    (* defn swft *)
 | swft_top : forall (DD:stctx),
     swft DD sty_top
 | swft_bot : forall (DD:stctx),
     swft DD sty_bot
 | swft_nat : forall (DD:stctx),
     swft DD sty_nat
 | swft_var : forall (DD:stctx) (X:typvar) (A:sty),
      binds ( X ) ( A ) ( DD )  ->
     swft DD (sty_var_f X)
 | swft_arrow : forall (DD:stctx) (A B:sty),
     swft DD A ->
     swft DD B ->
     swft DD (sty_arrow A B)
 | swft_all : forall (L:vars) (DD:stctx) (A B:sty),
     swft DD A ->
      ( forall X , X \notin  L  -> swft  (( X ~ A )++ DD )   ( open_sty_wrt_sty B (sty_var_f X) )  )  ->
     swft DD (sty_all A B)
 | swft_and : forall (DD:stctx) (A B:sty),
     swft DD A ->
     swft DD B ->
     swft DD (sty_and A B)
 | swft_rcd : forall (DD:stctx) (l:i) (A:sty),
     swft DD A ->
     swft DD (sty_rcd l A).

(* defns Jswf_env *)
Inductive swfe : stctx -> sctx -> Prop :=    (* defn swfe *)
 | swfe_empty : forall (DD:stctx),
     swfe DD  nil 
 | swfe_var : forall (DD:stctx) (GG:sctx) (x:expvar) (A:sty),
     swfe DD GG ->
     swft DD A ->
      ( x  `notin` dom ( GG ))  ->
      ( x  `notin` dom ( DD ))  ->
     swfe DD  (( x ~ A )++ GG ) .

(* defns Jswf_tenv *)
Inductive swfte : stctx -> Prop :=    (* defn swfte *)
 | swfte_empty : 
     swfte  nil 
 | swfte_var : forall (DD:stctx) (X:typvar) (A:sty),
     swfte DD ->
     swft DD A ->
      ( X  `notin` dom ( DD ))  ->
     swfte  (( X ~ A )++ DD ) .

(* defns JSubtyping *)
Inductive sub : stctx -> sty -> sty -> Prop :=    (* defn sub *)
 | S_refl : forall (DD:stctx) (A:sty),
     swft DD A ->
     sub DD A A
 | S_trans : forall (DD:stctx) (A1 A3 A2:sty),
     sub DD A2 A3 ->
     sub DD A1 A2 ->
     sub DD A1 A3
 | S_top : forall (DD:stctx) (A:sty),
     swft DD A ->
     sub DD A sty_top
 | S_bot : forall (DD:stctx) (A:sty),
     swft DD A ->
     sub DD sty_bot A
 | S_topArr : forall (DD:stctx),
     sub DD sty_top (sty_arrow sty_top sty_top)
 | S_topRcd : forall (DD:stctx) (l:i),
     sub DD sty_top (sty_rcd l sty_top)
 | S_topAll : forall (DD:stctx),
     sub DD sty_top (sty_all sty_top sty_top)
 | S_arr : forall (DD:stctx) (A1 A2 B1 B2:sty),
     sub DD B1 A1 ->
     sub DD A2 B2 ->
     sub DD (sty_arrow A1 A2) (sty_arrow B1 B2)
 | S_and : forall (DD:stctx) (A1 A2 A3:sty),
     sub DD A1 A2 ->
     sub DD A1 A3 ->
     sub DD A1 (sty_and A2 A3)
 | S_andl : forall (DD:stctx) (A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     sub DD (sty_and A1 A2) A1
 | S_andr : forall (DD:stctx) (A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     sub DD (sty_and A1 A2) A2
 | S_forall : forall (L:vars) (DD:stctx) (A1 B1 A2 B2:sty),
      ( forall X , X \notin  L  -> sub  (( X ~ A2 )++ DD )   ( open_sty_wrt_sty B1 (sty_var_f X) )   ( open_sty_wrt_sty B2 (sty_var_f X) )  )  ->
     sub DD A2 A1 ->
     sub DD (sty_all A1 B1) (sty_all A2 B2)
 | S_rcd : forall (DD:stctx) (l:i) (A B:sty),
     sub DD A B ->
     sub DD (sty_rcd l A) (sty_rcd l B)
 | S_distArr : forall (DD:stctx) (A1 A2 A3:sty),
     swft DD A1 ->
     swft DD A2 ->
     swft DD A3 ->
     sub DD (sty_and  ( (sty_arrow A1 A2) )   ( (sty_arrow A1 A3) ) ) (sty_arrow A1 (sty_and A2 A3))
 | S_distRcd : forall (DD:stctx) (l:i) (A B:sty),
     swft DD A ->
     swft DD B ->
     sub DD (sty_and (sty_rcd l A) (sty_rcd l B)) (sty_rcd l (sty_and A B))
 | S_distPoly : forall (L:vars) (DD:stctx) (A B1 B2:sty),
     swft DD A ->
      ( forall X , X \notin  L  -> swft  (( X ~ A )++ DD )   ( open_sty_wrt_sty B1 (sty_var_f X) )  )  ->
      ( forall X , X \notin  L  -> swft  (( X ~ A )++ DD )   ( open_sty_wrt_sty B2 (sty_var_f X) )  )  ->
     sub DD (sty_and  ( (sty_all A B1) )   ( (sty_all A B2) ) ) (sty_all A (sty_and B1 B2)).

(* defns Disjoint *)
Inductive disjoint : stctx -> sty -> sty -> Prop :=    (* defn disjoint *)
 | D_topL : forall (DD:stctx) (B A:sty),
     swft DD A ->
     swft DD B ->
      TopLike  B  ->
     disjoint DD B A
 | D_topR : forall (DD:stctx) (A B:sty),
     swft DD A ->
     swft DD B ->
      TopLike  B  ->
     disjoint DD A B
 | D_arr : forall (DD:stctx) (A1 A2 B1 B2:sty),
     disjoint DD A2 B2 ->
     swft DD A1 ->
     swft DD B1 ->
     disjoint DD (sty_arrow A1 A2) (sty_arrow B1 B2)
 | D_andL : forall (DD:stctx) (A1 A2 B:sty),
     disjoint DD A1 B ->
     disjoint DD A2 B ->
     disjoint DD (sty_and A1 A2) B
 | D_andR : forall (DD:stctx) (A B1 B2:sty),
     disjoint DD A B1 ->
     disjoint DD A B2 ->
     disjoint DD A (sty_and B1 B2)
 | D_rcdEq : forall (DD:stctx) (l:i) (A B:sty),
     disjoint DD A B ->
     disjoint DD (sty_rcd l A) (sty_rcd l B)
 | D_rcdNeq : forall (DD:stctx) (l1:i) (A:sty) (l2:i) (B:sty),
      l1  <>  l2  ->
     swft DD A ->
     swft DD B ->
     disjoint DD (sty_rcd l1 A) (sty_rcd l2 B)
 | D_axNatArr : forall (DD:stctx) (A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     disjoint DD sty_nat (sty_arrow A1 A2)
 | D_axArrNat : forall (DD:stctx) (A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     disjoint DD (sty_arrow A1 A2) sty_nat
 | D_axNatRcd : forall (DD:stctx) (l:i) (A:sty),
     swft DD A ->
     disjoint DD sty_nat (sty_rcd l A)
 | D_axRcdNat : forall (DD:stctx) (l:i) (A:sty),
     swft DD A ->
     disjoint DD (sty_rcd l A) sty_nat
 | D_axArrRcd : forall (DD:stctx) (A1 A2:sty) (l:i) (A:sty),
     swft DD A1 ->
     swft DD A2 ->
     swft DD A ->
     disjoint DD (sty_arrow A1 A2) (sty_rcd l A)
 | D_axRcdArr : forall (DD:stctx) (l:i) (A A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     swft DD A ->
     disjoint DD (sty_rcd l A) (sty_arrow A1 A2)
 | D_axRcdAll : forall (DD:stctx) (l:i) (A A1 B1:sty),
     swft DD (sty_all A1 B1) ->
     swft DD A ->
     disjoint DD (sty_rcd l A) (sty_all A1 B1)
 | D_axAllRcd : forall (DD:stctx) (A1 B1:sty) (l:i) (A:sty),
     swft DD (sty_all A1 B1) ->
     swft DD A ->
     disjoint DD (sty_all A1 B1) (sty_rcd l A)
 | D_axAllNat : forall (DD:stctx) (A1 B1:sty),
     swft DD (sty_all A1 B1) ->
     disjoint DD (sty_all A1 B1) sty_nat
 | D_axNatAll : forall (DD:stctx) (A1 B1:sty),
     swft DD (sty_all A1 B1) ->
     disjoint DD sty_nat (sty_all A1 B1)
 | D_axArrAll : forall (DD:stctx) (A B A1 B1:sty),
     swft DD (sty_all A1 B1) ->
     swft DD A ->
     swft DD B ->
     disjoint DD (sty_arrow A B) (sty_all A1 B1)
 | D_axAllArr : forall (DD:stctx) (A1 B1 A B:sty),
     swft DD (sty_all A1 B1) ->
     swft DD A ->
     swft DD B ->
     disjoint DD (sty_all A1 B1) (sty_arrow A B)
 | D_tvarL : forall (DD:stctx) (X:typvar) (B A:sty),
      binds ( X ) ( A ) ( DD )  ->
     sub DD A B ->
     disjoint DD (sty_var_f X) B
 | D_tvarR : forall (DD:stctx) (B:sty) (X:typvar) (A:sty),
      binds ( X ) ( A ) ( DD )  ->
     sub DD A B ->
     disjoint DD B (sty_var_f X)
 | D_forall : forall (L:vars) (DD:stctx) (A1 B1 A2 B2:sty),
      ( forall X , X \notin  L  -> disjoint  (( X ~ (sty_and A1 A2) )++ DD )   ( open_sty_wrt_sty B1 (sty_var_f X) )   ( open_sty_wrt_sty B2 (sty_var_f X) )  )  ->
     swft DD A1 ->
     swft DD A2 ->
     disjoint DD (sty_all A1 B1) (sty_all A2 B2).

(* defns JSTyping *)
Inductive has_type : stctx -> sctx -> sexp -> dirflag -> sty -> Prop :=    (* defn has_type *)
 | T_top : forall (DD:stctx) (GG:sctx),
     swfe DD GG ->
     swfte DD ->
     has_type DD GG sexp_top Inf sty_top
 | T_nat : forall (DD:stctx) (GG:sctx) i5,
     swfe DD GG ->
     swfte DD ->
     has_type DD GG (sexp_lit i5) Inf sty_nat
 | T_var : forall (DD:stctx) (GG:sctx) (x:expvar) (A:sty),
     swfte DD ->
     swfe DD GG ->
      binds ( x ) ( A ) ( GG )  ->
     has_type DD GG (sexp_var_f x) Inf A
 | T_app : forall (DD:stctx) (GG:sctx) (ee1 ee2:sexp) (A2 A1:sty),
     has_type DD GG ee1 Inf (sty_arrow A1 A2) ->
     has_type DD GG ee2 Chk A1 ->
     has_type DD GG (sexp_app ee1 ee2) Inf A2
 | T_merge : forall (DD:stctx) (GG:sctx) (ee1 ee2:sexp) (A1 A2:sty),
     has_type DD GG ee1 Inf A1 ->
     has_type DD GG ee2 Inf A2 ->
     disjoint DD A1 A2 ->
     has_type DD GG (sexp_merge ee1 ee2) Inf (sty_and A1 A2)
 | T_anno : forall (DD:stctx) (GG:sctx) (ee:sexp) (A:sty),
     has_type DD GG ee Chk A ->
     has_type DD GG (sexp_anno ee A) Inf A
 | T_tabs : forall (L:vars) (DD:stctx) (GG:sctx) (A:sty) (ee:sexp) (B:sty),
     swft DD A ->
      ( forall X , X \notin  L  -> has_type  (( X ~ A )++ DD )  GG  ( open_sexp_wrt_sty ee (sty_var_f X) )  Inf  ( open_sty_wrt_sty B (sty_var_f X) )  )  ->
     swfe DD GG ->
     has_type DD GG (sexp_tabs A ee) Inf (sty_all A B)
 | T_tapp : forall (DD:stctx) (GG:sctx) (ee:sexp) (A C B:sty),
     has_type DD GG ee Inf (sty_all B C) ->
     disjoint DD A B ->
     has_type DD GG (sexp_tapp ee A) Inf  (open_sty_wrt_sty  C   A ) 
 | T_rcd : forall (DD:stctx) (GG:sctx) (l:i) (ee:sexp) (A:sty),
     has_type DD GG ee Inf A ->
     has_type DD GG (sexp_rcd l ee) Inf (sty_rcd l A)
 | T_proj : forall (DD:stctx) (GG:sctx) (ee:sexp) (l:i) (A:sty),
     has_type DD GG ee Inf (sty_rcd l A) ->
     has_type DD GG (sexp_proj ee l) Inf A
 | T_abs : forall (L:vars) (DD:stctx) (GG:sctx) (ee:sexp) (A B:sty),
     swft DD A ->
      ( forall x , x \notin  L  -> has_type DD  (( x ~ A )++ GG )   ( open_sexp_wrt_sexp ee (sexp_var_f x) )  Chk B )  ->
     has_type DD GG (sexp_abs ee) Chk (sty_arrow A B)
 | T_sub : forall (DD:stctx) (GG:sctx) (ee:sexp) (A B:sty),
     has_type DD GG ee Inf B ->
     swft DD A ->
     sub DD B A ->
     has_type DD GG ee Chk A.

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
 | cmp_Base : forall (Ttx:TContext) (r:rtyp) (l:i) (rt' rt5:rt),
     cmp Ttx r (r_SingleField l rt5) ->
     wfrt Ttx rt' ->
     cmp Ttx r (r_SingleField l rt')
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

(* defns WFP *)
Inductive wfp : TContext -> PContext -> Prop :=    (* defn wfp *)
 | wfp_Nil : 
     wfp  nil   nil 
 | wfp_Cons : forall (Ttx:TContext) (a:typvar) (R:rlist) (Ptx:PContext) (b:typvar),
     lc_rlist R ->
     wfp Ttx Ptx ->
      ( a  `notin` dom ( Ttx ))  ->
      ( a  `notin` dom ( Ptx ))  ->
      a  `notin` fv_Ptx  Ptx  ->
      ( b  `notin` dom ( Ttx ))  ->
      ( b  `notin` dom ( Ptx ))  ->
      b  `notin` fv_Ptx  Ptx  ->
      a  <>  b  ->
     wfp  (( a ~ R )++ Ttx )   (( a ~ b )++ Ptx ) .


(** infrastructure *)
Hint Constructors swft swfe swfte sub disjoint has_type wftc wfcl wfrt wfr cmp ceq teq cmpList wfc wfp lc_sty lc_rtyp lc_rlist lc_rt lc_sexp lc_rexp.


