
Require Import Metalib.Metatheory.
Require Export Syntax_ott.

(* ********************************************************************** *)
(** * Monotype predicate *)

Inductive mono : sty -> Prop :=
| mono_nat : mono sty_nat
| mono_top : mono sty_top
| mono_bot : mono sty_bot
| mono_var_f : forall (X:typvar),
    (mono (sty_var_f X))
| mono_arrow : forall (A B:sty),
    (mono A) ->
    (mono B) ->
    (mono (sty_arrow A B))
| mono_and : forall (A B:sty),
    (mono A) ->
    (mono B) ->
    (mono (sty_and A B))
| mono_rcd : forall (l:i) (A:sty),
    (mono A) ->
    (mono (sty_rcd l A)).

(* ********************************************************************** *)
(** * Type translation *)

Fixpoint sty2ty (A : sty) : ty :=
  match A with
  | sty_nat => ty_nat
  | sty_arrow A1 A2  => ty_arrow (sty2ty A1) (sty2ty A2)
  | sty_and A1 A2 => ty_prod (sty2ty A1) (sty2ty A2)
  | sty_top => ty_unit
  | sty_bot => ty_all (ty_var_b 0)
  | sty_all _ A => ty_all (sty2ty A)
  | sty_rcd _ A => sty2ty A
  | sty_var_b n => ty_var_b n
  | sty_var_f n => ty_var_f n
  end.


(* ********************************************************************** *)
(** * Fco well-formedness of types *)

Inductive wft : tctx -> ty -> Prop :=    (* defn wft *)
 | wft_unit : forall (dd:tctx),
     wft dd ty_unit
 | wft_nat : forall (dd:tctx),
     wft dd ty_nat
 | wft_var : forall (dd:tctx) (X:typvar),
      binds  X  tt  dd  ->
     wft dd (ty_var_f X)
 | wft_arrow : forall (dd:tctx) (T1 T2:ty),
     wft dd T1 ->
     wft dd T2 ->
     wft dd (ty_arrow T1 T2)
 | wft_prod : forall (dd:tctx) (T1 T2:ty),
     wft dd T1 ->
     wft dd T2 ->
     wft dd (ty_prod T1 T2)
 | wft_all : forall (L:vars) (dd:tctx) (T2:ty),
      ( forall X , X \notin  L  -> wft  (( X ~tt)++ dd )   ( open_ty_wrt_ty T2 (ty_var_f X) )  )  ->
     wft dd (ty_all T2).

(* ********************************************************************** *)
(** * Fco well-formedness of term contexts *)

Inductive wfe : tctx -> ctx -> Prop :=    (* defn wfe *)
 | wfe_empty : forall (dd:tctx),
      uniq  dd  ->
     wfe dd  nil
 | wfe_var : forall (dd:tctx) (gg:ctx) (x:expvar) (T:ty),
     wft dd T ->
     wfe dd gg ->
      ( x  `notin` dom ( gg ))  ->
      ( x  `notin` dom ( dd ))  ->
     wfe dd  (( x ~ T )++ gg ) .


(* ********************************************************************** *)
(** * Coercion typing *)

Inductive ctyp : tctx -> co -> ty -> ty -> Prop :=    (* defn ctyp *)
 | ctyp_id : forall (dd:tctx) (T:ty),
     wft dd T ->
     ctyp dd co_id T T
 | ctyp_trans : forall (dd:tctx) (c1 c2:co) (T1 T3 T2:ty),
     ctyp dd c1 T2 T3 ->
     ctyp dd c2 T1 T2 ->
     ctyp dd (co_trans c1 c2) T1 T3
 | ctyp_top : forall (dd:tctx) (T:ty),
     wft dd T ->
     ctyp dd co_top T ty_unit
 | ctyp_bot : forall (dd:tctx) (T:ty),
     wft dd T ->
     ctyp dd co_bot (ty_all (ty_var_b 0)) T
 | ctyp_arr : forall (dd:tctx) (c1 c2:co) (T1 T2 T1' T2':ty),
     ctyp dd c1 T1' T1 ->
     ctyp dd c2 T2 T2' ->
     ctyp dd (co_arr c1 c2) (ty_arrow T1 T2) (ty_arrow T1' T2')
 | ctyp_pair : forall (dd:tctx) (c1 c2:co) (T1 T2 T3:ty),
     ctyp dd c1 T1 T2 ->
     ctyp dd c2 T1 T3 ->
     ctyp dd (co_pair c1 c2) T1 (ty_prod T2 T3)
 | ctyp_projl : forall (dd:tctx) (T1 T2:ty),
     wft dd T1 ->
     wft dd T2 ->
     ctyp dd co_proj1 (ty_prod T1 T2) T1
 | ctyp_projr : forall (dd:tctx) (T1 T2:ty),
     wft dd T1 ->
     wft dd T2 ->
     ctyp dd co_proj2 (ty_prod T1 T2) T2
 | ctyp_forall : forall (L:vars) (dd:tctx) (c:co) (T1 T2:ty),
      ( forall X , X \notin  L  -> ctyp  (( X ~tt)++ dd )  c  ( open_ty_wrt_ty T1 (ty_var_f X) )   ( open_ty_wrt_ty T2 (ty_var_f X) )  )  ->
     ctyp dd (co_forall c) (ty_all T1) (ty_all T2)
 | ctyp_distArr : forall (dd:tctx) (T1 T2 T3:ty),
     wft dd T1 ->
     wft dd T2 ->
     wft dd T3 ->
     ctyp dd co_distArr (ty_prod  ( (ty_arrow T1 T2) )   ( (ty_arrow T1 T3) ) ) (ty_arrow T1 (ty_prod T2 T3))
 | ctyp_topArr : forall (dd:tctx),
     ctyp dd co_topArr ty_unit (ty_arrow ty_unit ty_unit)
 | ctyp_topAll : forall (dd:tctx),
     ctyp dd co_topAll ty_unit (ty_all ty_unit)
 | ctyp_distPoly : forall (dd:tctx) (T1 T2:ty),
     wft dd (ty_all T1) ->
     wft dd (ty_all T2) ->
     ctyp dd co_distPoly (ty_prod  ( (ty_all T1) )   ( (ty_all T2) ) ) (ty_all (ty_prod T1 T2)).


(* ********************************************************************** *)
(** * Fco typing *)

Inductive typ : tctx -> ctx -> exp -> ty -> Prop :=    (* defn typ *)
 | typ_unit : forall (dd:tctx) (gg:ctx),
     wfe dd gg ->
     typ dd gg exp_unit ty_unit
 | typ_nat : forall (dd:tctx) (gg:ctx) (i5:i),
     wfe dd gg ->
     typ dd gg (exp_lit i5) ty_nat
 | typ_var : forall (dd:tctx) (gg:ctx) (x:expvar) (T:ty),
     wfe dd gg ->
      binds  x   T   gg  ->
     typ dd gg (exp_var_f x) T
 | typ_abs : forall (L:vars) (dd:tctx) (gg:ctx) (e:exp) (T1 T2:ty),
      ( forall x , x \notin  L  -> typ dd  (( x ~ T1 )++ gg )   ( open_exp_wrt_exp e (exp_var_f x) )  T2 )  ->
     wft dd T1 ->
     typ dd gg (exp_abs e) (ty_arrow T1 T2)
 | typ_app : forall (dd:tctx) (gg:ctx) (e1 e2:exp) (T2 T1:ty),
     typ dd gg e1 (ty_arrow T1 T2) ->
     typ dd gg e2 T1 ->
     typ dd gg (exp_app e1 e2) T2
 | typ_pair : forall (dd:tctx) (gg:ctx) (e1 e2:exp) (T1 T2:ty),
     typ dd gg e1 T1 ->
     typ dd gg e2 T2 ->
     typ dd gg (exp_pair e1 e2) (ty_prod T1 T2)
 | typ_tabs : forall (L:vars) (dd:tctx) (gg:ctx) (e:exp) (T:ty),
      ( forall X , X \notin  L  -> typ  (( X ~tt)++ dd )  gg  ( open_exp_wrt_ty e (ty_var_f X) )   ( open_ty_wrt_ty T (ty_var_f X) )  )  ->
     wfe dd gg ->
     typ dd gg (exp_tabs e) (ty_all T)
 | typ_tapp : forall (dd:tctx) (gg:ctx) (e:exp) (T T':ty),
     typ dd gg e (ty_all T') ->
     wft dd T ->
     typ dd gg (exp_tapp e T)  (open_ty_wrt_ty  T'   T )
 | typ_capp : forall (dd:tctx) (gg:ctx) (c:co) (e:exp) (T' T:ty),
     typ dd gg e T ->
     ctyp dd c T T' ->
     wft dd T' ->
     typ dd gg (exp_capp c e) T'.


(* ********************************************************************** *)
(** * Value predicate *)

Inductive value : exp -> Prop :=    (* defn value *)
 | value_unit :
     value exp_unit
 | value_lit : forall (i5:i),
     value (exp_lit i5)
 | value_abs : forall (e:exp),
     lc_exp (exp_abs e) ->
     value (exp_abs e)
 | value_tabs : forall (e:exp),
     lc_exp (exp_tabs e) ->
     value (exp_tabs e)
 | value_pair : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     value (exp_pair v1 v2)
 | value_arr : forall (c1 c2:co) (v:exp),
     value v ->
     value (exp_capp  ( (co_arr c1 c2) )  v)
 | value_forall : forall (c:co) (v:exp),
     value v ->
     value (exp_capp  ( (co_forall c) )  v)
 | value_distArr : forall (v:exp),
     value v ->
     value (exp_capp co_distArr v)
 | value_topArr : forall (v:exp),
     value v ->
     value (exp_capp co_topArr v)
 | value_topAll : forall (v:exp),
     value v ->
     value (exp_capp co_topAll v)
 | value_distPoly : forall (v:exp),
     value v ->
     value (exp_capp co_distPoly v).


(* ********************************************************************** *)
(** * Single-step reduction *)

Inductive step : exp -> exp -> Prop :=
 | step_topArr :
     step (exp_app  ( (exp_capp co_topArr exp_unit) )  exp_unit) exp_unit
 | step_topAll : forall (T:ty),
     lc_ty T ->
     step (exp_tapp  ( (exp_capp co_topAll exp_unit) )  T) exp_unit
 | step_distArr : forall (v1 v2 v3:exp),
     value v1 ->
     value v2 ->
     value v3 ->
     step (exp_app  ( (exp_capp co_distArr (exp_pair v1 v2)) )  v3) (exp_pair (exp_app v1 v3) (exp_app v2 v3))
 | step_distPoly : forall (v1 v2:exp) (T:ty),
     lc_ty T ->
     value v1 ->
     value v2 ->
     step (exp_tapp  ( (exp_capp co_distPoly (exp_pair v1 v2)) )  T) (exp_pair (exp_tapp v1 T) (exp_tapp v2 T))
 | step_id : forall (v:exp),
     value v ->
     step (exp_capp co_id v) v
 | step_trans : forall (c1 c2:co) (v:exp),
     value v ->
     step (exp_capp  ( (co_trans c1 c2) )  v) (exp_capp c1  ( (exp_capp c2 v) ) )
 | step_top : forall (v:exp),
     value v ->
     step (exp_capp co_top v) exp_unit
 | step_arr : forall (c1 c2:co) (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (exp_app  ( (exp_capp  ( (co_arr c1 c2) )  v1) )  v2) (exp_capp c2  ( (exp_app v1  ( (exp_capp c1 v2) ) ) ) )
 | step_pair : forall (c1 c2:co) (v:exp),
     value v ->
     step (exp_capp (co_pair c1 c2) v) (exp_pair (exp_capp c1 v) (exp_capp c2 v))
 | step_projl : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (exp_capp co_proj1 (exp_pair v1 v2)) v1
 | step_projr : forall (v1 v2:exp),
     value v1 ->
     value v2 ->
     step (exp_capp co_proj2 (exp_pair v1 v2)) v2
 | step_forall : forall (c:co) (v:exp) (T:ty),
     lc_ty T ->
     value v ->
     step (exp_tapp  ( (exp_capp (co_forall c) v) )  T) (exp_capp c  ( (exp_tapp v T) ) )
 | step_beta : forall (e v:exp),
     lc_exp (exp_abs e) ->
     value v ->
     step (exp_app  ( (exp_abs e) )  v)  (open_exp_wrt_exp  e v )
 | step_tbeta : forall (e:exp) (T:ty),
     lc_exp (exp_tabs e) ->
     lc_ty T ->
     step (exp_tapp  ( (exp_tabs e) )  T)  (open_exp_wrt_ty  e   T )
 | step_app1 : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (exp_app e1 e2) (exp_app e1' e2)
 | step_app2 : forall (v1 e2 e2':exp),
     step e2 e2' ->
     value v1 ->
     step (exp_app v1 e2) (exp_app v1 e2')
 | step_pairl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (exp_pair e1 e2) (exp_pair e1' e2)
 | step_pairr : forall (v1 e2 e2':exp),
     value v1 ->
     step e2 e2' ->
     step (exp_pair v1 e2) (exp_pair v1 e2')
 | step_tapp : forall (e:exp) (T:ty) (e':exp),
     lc_ty T ->
     step e e' ->
     step (exp_tapp e T) (exp_tapp e' T)
 | step_capp : forall (c:co) (e e':exp),
     step e e' ->
     step (exp_capp c e) (exp_capp c e').


(* ********************************************************************** *)
(** * Fi+ well-formedness of types *)

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

(* ********************************************************************** *)
(** * Fi+ well-formedness of term contexts *)

Inductive swfe : stctx -> sctx -> Prop :=    (* defn swfe *)
 | swfe_empty : forall (DD:stctx),
     swfe DD  nil
 | swfe_var : forall (DD:stctx) (GG:sctx) (x:expvar) (A:sty),
     swfe DD GG ->
     swft DD A ->
      ( x  `notin` dom ( GG ))  ->
      ( x  `notin` dom ( DD ))  ->
     swfe DD  (( x ~ A )++ GG ) .


(* ********************************************************************** *)
(** * Fi+ well-formedness of type contexts *)

Inductive swfte : stctx -> Prop :=    (* defn swfte *)
 | swfte_empty :
     swfte  nil
 | swfte_var : forall (DD:stctx) (X:typvar) (A:sty),
     swfte DD ->
     swft DD A ->
      ( X  `notin` dom ( DD ))  ->
     swfte  (( X ~ A )++ DD ) .


(* ********************************************************************** *)
(** * Coercive subtyping *)

Inductive sub : stctx -> sty -> sty -> co -> Prop :=    (* defn sub *)
 | S_refl : forall (DD:stctx) (A:sty),
     swft DD A ->
     sub DD A A co_id
 | S_trans : forall (DD:stctx) (A1 A3:sty) (c1 c2:co) (A2:sty),
     sub DD A2 A3 c1 ->
     sub DD A1 A2 c2 ->
     sub DD A1 A3 (co_trans c1 c2)
 | S_top : forall (DD:stctx) (A:sty),
     swft DD A ->
     sub DD A sty_top co_top
 | S_bot : forall (DD:stctx) (A:sty),
     swft DD A ->
     sub DD sty_bot A co_bot
 | S_topArr : forall (DD:stctx),
     sub DD sty_top (sty_arrow sty_top sty_top) co_topArr
 | S_topRcd : forall (DD:stctx) (l:i),
     sub DD sty_top (sty_rcd l sty_top) co_id
 | S_topAll : forall (DD:stctx),
     sub DD sty_top (sty_all sty_top sty_top) co_topAll
 | S_arr : forall (DD:stctx) (A1 A2 B1 B2:sty) (c1 c2:co),
     sub DD B1 A1 c1 ->
     sub DD A2 B2 c2 ->
     sub DD (sty_arrow A1 A2) (sty_arrow B1 B2) (co_arr c1 c2)
 | S_and : forall (DD:stctx) (A1 A2 A3:sty) (c1 c2:co),
     sub DD A1 A2 c1 ->
     sub DD A1 A3 c2 ->
     sub DD A1 (sty_and A2 A3) (co_pair c1 c2)
 | S_andl : forall (DD:stctx) (A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     sub DD (sty_and A1 A2) A1 co_proj1
 | S_andr : forall (DD:stctx) (A1 A2:sty),
     swft DD A1 ->
     swft DD A2 ->
     sub DD (sty_and A1 A2) A2 co_proj2
 | S_forall : forall (L:vars) (DD:stctx) (A1 B1 A2 B2:sty) (c c':co),
      ( forall X , X \notin  L  -> sub  (( X ~ A2 )++ DD )   ( open_sty_wrt_sty B1 (sty_var_f X) )   ( open_sty_wrt_sty B2 (sty_var_f X) )  c )  ->
     sub DD A2 A1 c' ->
     sub DD (sty_all A1 B1) (sty_all A2 B2) (co_forall c)
 | S_rcd : forall (DD:stctx) (l:i) (A B:sty) (c:co),
     sub DD A B c ->
     sub DD (sty_rcd l A) (sty_rcd l B) c
 | S_distArr : forall (DD:stctx) (A1 A2 A3:sty),
     swft DD A1 ->
     swft DD A2 ->
     swft DD A3 ->
     sub DD (sty_and  ( (sty_arrow A1 A2) )   ( (sty_arrow A1 A3) ) ) (sty_arrow A1 (sty_and A2 A3)) co_distArr
 | S_distRcd : forall (DD:stctx) (l:i) (A B:sty),
     swft DD A ->
     swft DD B ->
     sub DD (sty_and (sty_rcd l A) (sty_rcd l B)) (sty_rcd l (sty_and A B)) co_id
 | S_distPoly : forall (L:vars) (DD:stctx) (A B1 B2:sty),
     swft DD A ->
      ( forall X , X \notin  L  -> swft  (( X ~ A )++ DD )   ( open_sty_wrt_sty B1 (sty_var_f X) )  )  ->
      ( forall X , X \notin  L  -> swft  (( X ~ A )++ DD )   ( open_sty_wrt_sty B2 (sty_var_f X) )  )  ->
     sub DD (sty_and  ( (sty_all A B1) )   ( (sty_all A B2) ) ) (sty_all A (sty_and B1 B2)) co_distPoly.

(* ********************************************************************** *)
(** * Subtyping minus contexts and coercions *)

Inductive csub : sty -> sty -> co -> Prop :=
 | CS_refl : forall (A:sty),
     lc_sty A ->
     csub A A co_id
 | CS_trans : forall (A1 A3:sty) (c1 c2:co) (A2:sty),
     csub A2 A3 c1 ->
     csub A1 A2 c2 ->
     csub A1 A3 (co_trans c1 c2)
 | CS_top : forall (A:sty),
     lc_sty A ->
     csub A sty_top co_top
 | CS_bot : forall (A:sty),
     lc_sty A ->
     csub sty_bot A co_bot
 | CS_topArr :
     csub sty_top (sty_arrow sty_top sty_top) co_topArr
 | CS_topRcd : forall (l:i),
     csub sty_top (sty_rcd l sty_top) co_id
 | CS_topAll :
     csub sty_top (sty_all sty_top sty_top) co_topAll
 | CS_arr : forall (A1 A2 B1 B2:sty) (c1 c2:co),
     csub B1 A1 c1 ->
     csub A2 B2 c2 ->
     csub (sty_arrow A1 A2) (sty_arrow B1 B2) (co_arr c1 c2)
 | CS_and : forall (A1 A2 A3:sty) (c1 c2:co),
     csub A1 A2 c1 ->
     csub A1 A3 c2 ->
     csub A1 (sty_and A2 A3) (co_pair c1 c2)
 | CS_andl : forall (A1 A2:sty),
     lc_sty A2 ->
     lc_sty A1 ->
     csub (sty_and A1 A2) A1 co_proj1
 | CS_andr : forall (A1 A2:sty),
     lc_sty A1 ->
     lc_sty A2 ->
     csub (sty_and A1 A2) A2 co_proj2
 | CS_forall : forall (L:vars) (A1 B1 A2 B2:sty) (c c':co),
      ( forall X , X \notin  L  -> csub  ( open_sty_wrt_sty B1 (sty_var_f X) )   ( open_sty_wrt_sty B2 (sty_var_f X) )  c )  ->
     csub A2 A1 c' ->
     csub (sty_all A1 B1) (sty_all A2 B2) (co_forall c)
 | CS_rcd : forall (l:i) (A B:sty) (c:co),
     csub A B c ->
     csub (sty_rcd l A) (sty_rcd l B) c
 | CS_distArr : forall (A1 A2 A3:sty),
     lc_sty A1 ->
     lc_sty A2 ->
     lc_sty A3 ->
     csub (sty_and  ( (sty_arrow A1 A2) )   ( (sty_arrow A1 A3) ) ) (sty_arrow A1 (sty_and A2 A3)) co_distArr
 | CS_distRcd : forall (l:i) (A B:sty),
     lc_sty A ->
     lc_sty B ->
     csub (sty_and (sty_rcd l A) (sty_rcd l B)) (sty_rcd l (sty_and A B)) co_id
 | CS_distPoly : forall (A B1 B2:sty),
     lc_sty (sty_all A B1) ->
     lc_sty (sty_all A B2) ->
     lc_sty A ->
     csub (sty_and  ( (sty_all A B1) )   ( (sty_all A B2) ) ) (sty_all A (sty_and B1 B2)) co_distPoly.


(* ********************************************************************** *)
(** * Top-like predicate *)

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


(* ********************************************************************** *)
(** * Disjointness relation *)

Inductive disjoint : stctx -> sty -> sty -> Prop :=
 | D_topL : forall (DD:stctx) (A:sty) B,
     swft DD A ->
     swft DD B ->
     TopLike B ->
     disjoint DD B A
 | D_topR : forall (DD:stctx) (A:sty) B,
     swft DD A ->
     swft DD B ->
     TopLike B ->
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
 | D_tvarL : forall (DD:stctx) (X:typvar) (B A:sty) (c:co),
      binds ( X ) ( A ) ( DD )  ->
     sub DD A B c ->
     disjoint DD (sty_var_f X) B
 | D_tvarR : forall (DD:stctx) (B:sty) (X:typvar) (A:sty) (c:co),
      binds ( X ) ( A ) ( DD )  ->
     sub DD A B c ->
     disjoint DD B (sty_var_f X)
 | D_forall : forall (L:vars) (DD:stctx) (A1 B1 A2 B2:sty),
      ( forall X , X \notin  L  -> disjoint  (( X ~ (sty_and A1 A2) )++ DD )   ( open_sty_wrt_sty B1 (sty_var_f X) )   ( open_sty_wrt_sty B2 (sty_var_f X) )  )  ->
     swft DD A1 ->
     swft DD A2 ->
     disjoint DD (sty_all A1 B1) (sty_all A2 B2).


(* ********************************************************************** *)
(** * Fi+ elaboration typing *)

Inductive has_type : stctx -> sctx -> sexp -> dirflag -> sty -> exp -> Prop :=    (* defn has_type *)
 | T_top : forall (DD:stctx) (GG:sctx),
     swfe DD GG ->
     swfte DD ->
     has_type DD GG sexp_top Inf sty_top exp_unit
 | T_nat : forall (DD:stctx) (GG:sctx) (i5:i),
     swfe DD GG ->
     swfte DD ->
     has_type DD GG (sexp_lit i5) Inf sty_nat (exp_lit i5)
 | T_var : forall (DD:stctx) (GG:sctx) (x:expvar) (A:sty),
     swfte DD ->
     swfe DD GG ->
      binds ( x ) ( A ) ( GG )  ->
     has_type DD GG (sexp_var_f x) Inf A (exp_var_f x)
 | T_app : forall (DD:stctx) (GG:sctx) (ee1 ee2:sexp) (A2:sty) (e1 e2:exp) (A1:sty),
     has_type DD GG ee1 Inf (sty_arrow A1 A2) e1 ->
     has_type DD GG ee2 Chk A1 e2 ->
     has_type DD GG (sexp_app ee1 ee2) Inf A2 (exp_app e1 e2)
 | T_merge : forall (DD:stctx) (GG:sctx) (ee1 ee2:sexp) (A1 A2:sty) (e1 e2:exp),
     has_type DD GG ee1 Inf A1 e1 ->
     has_type DD GG ee2 Inf A2 e2 ->
     disjoint DD A1 A2 ->
     has_type DD GG (sexp_merge ee1 ee2) Inf (sty_and A1 A2) (exp_pair e1 e2)
 | T_anno : forall (DD:stctx) (GG:sctx) (ee:sexp) (A:sty) (e:exp),
     has_type DD GG ee Chk A e ->
     has_type DD GG (sexp_anno ee A) Inf A e
 | T_tabs : forall (L:vars) (DD:stctx) (GG:sctx) (A:sty) (ee:sexp) (B:sty) (e:exp),
     swft DD A ->
      ( forall X , X \notin  L  -> has_type  (( X ~ A )++ DD )  GG  ( open_sexp_wrt_sty ee (sty_var_f X) )  Inf  ( open_sty_wrt_sty B (sty_var_f X) )   ( open_exp_wrt_ty e (ty_var_f X) )  )  ->
     swfe DD GG ->
     has_type DD GG (sexp_tabs A ee) Inf (sty_all A B) (exp_tabs e)
 | T_tapp : forall (DD:stctx) (GG:sctx) (ee:sexp) (t C:sty) (e:exp) (B:sty),
     has_type DD GG ee Inf (sty_all B C) e ->
      mono  t  ->
     disjoint DD t B ->
     has_type DD GG (sexp_tapp ee t) Inf  (open_sty_wrt_sty  C   t )  (exp_tapp e  (sty2ty  t ) )
 | T_rcd : forall (DD:stctx) (GG:sctx) (l:i) (ee:sexp) (A:sty) (e:exp),
     has_type DD GG ee Inf A e ->
     has_type DD GG (sexp_rcd l ee) Inf (sty_rcd l A) e
 | T_proj : forall (DD:stctx) (GG:sctx) (ee:sexp) (l:i) (A:sty) (e:exp),
     has_type DD GG ee Inf (sty_rcd l A) e ->
     has_type DD GG (sexp_proj ee l) Inf A e
 | T_abs : forall (L:vars) (DD:stctx) (GG:sctx) (ee:sexp) (A B:sty) (e:exp),
     swft DD A ->
      ( forall x , x \notin  L  -> has_type DD  (( x ~ A )++ GG )   ( open_sexp_wrt_sexp ee (sexp_var_f x) )  Chk B  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     has_type DD GG (sexp_abs ee) Chk (sty_arrow A B) (exp_abs e)
 | T_sub : forall (DD:stctx) (GG:sctx) (ee:sexp) (A:sty) (c:co) (e:exp) (B:sty),
     has_type DD GG ee Inf B e ->
     swft DD A ->
     sub DD B A c ->
     has_type DD GG ee Chk A (exp_capp c e).


Section Star.

  Variable A : Type.

  Definition relation := A -> A -> Prop.

  Variable R : relation.

  Inductive star : relation :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

  Lemma star_one:
    forall a b, R a b -> star a b.
  Proof.
    eauto using star.
  Qed.

  Lemma star_trans:
    forall a b, star a b -> forall c, star b c -> star a c.
  Proof.
    induction 1; eauto using star.
  Qed.


  Hypothesis R_functional:
    forall a b c, R a b -> R a c -> b = c.

  Lemma star_star_inv:
    forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
  Proof.
    induction 1; intros.
    - auto.
    - inversion H1; subst.
      + right. eauto using star.
      + assert (b = b0) by (eapply R_functional; eauto). subst b0.
        apply IHstar; auto.
  Qed.

  Definition irred a : Prop := forall b, ~(R a b).

  Lemma finseq_unique:
    forall a b b',
      star a b -> irred b ->
      star a b' -> irred b' ->
      b = b'.
  Proof.
    intros. destruct (star_star_inv _ _ H _ H1).
    - inversion H3; subst. auto. elim (H0 _ H4).
    - inversion H3; subst. auto. elim (H2 _ H4).
  Qed.


End Star.

Arguments star : default implicits.
Arguments irred : default implicits.

Notation "t ->* t'" := (star step t t') (at level 68).

Hint Constructors wft wfe ctyp typ value step swft swfe swfte sub csub disjoint has_type TopLike star.
