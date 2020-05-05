Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.
Require Import JaSyntax.
Require Import JaTypes.
Require Import JaProgram.
Require Import JaEnvs.
Require Import Jafun.
Require Import Bool.
Require Import JaIrisCommon.
Require Import Classical_Prop.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module StrMap := JaIrisCommon.StrMap.
Module HeapFacts := Facts Heap.

(* ======================= Definition ====================== *)
(* Evaluation is a transitive closure of reduction relation *)

Fixpoint JFIPartialEval (h0 : Heap) (st0 : FrameStack) (confs : list (Heap * FrameStack)) (hn : Heap) (stn : FrameStack) (CC : JFProgram) : Prop :=
  match confs with
  | [] => h0 = hn /\ st0 = stn
  | (expected_h, expected_st)::confs' => h0 = expected_h /\ st0 = expected_st /\
      match red CC (h0, st0) with
      | Some (h, st) => JFIPartialEval h st confs' hn stn CC
      | None => False
      end 
  end.

Definition JFIEval (h : Heap) (e : JFExpr) (confs : list (Heap * FrameStack)) (hn : Heap) (res : Loc) (CC : JFProgram) : Prop :=
  let EmptyCtx := []
  in JFIPartialEval h [EmptyCtx [[ e ]]_ None] confs hn [EmptyCtx [[ JFVal1 (JFVLoc res) ]]_ None] CC.

Definition JFIEvalInEnv (h : Heap) (e : JFExpr) (confs : list (Heap * FrameStack)) (hn : Heap) (res : Loc) (env : JFITermEnv) (CC : JFProgram) : Prop :=
  JFIEval h (JFIExprSubstituteEnv env e) confs hn res CC.

(* ======================= Evalution is deterministic ======================= *)

Lemma EvaluationFirstStepIsDeterministic : forall h0 st0 h1 h1' st1 st1' confs confs' hn hn' stn stn' CC,
 (JFIPartialEval h0 st0 ((h1, st1) :: confs) hn stn CC) ->
 (JFIPartialEval h0 st0 ((h1', st1') :: confs') hn' stn' CC) ->
  h1 = h1' /\ st1 = st1' /\ exists h' st', JFIPartialEval h' st' confs hn stn CC /\ JFIPartialEval h' st' confs' hn' stn' CC.
Proof.
  intros h0 st0 h1 h1' st1 st1' confs confs' hn hn' stn stn' CC.
  intros eval1 eval2.
  unfold JFIEval, JFIPartialEval in eval1, eval2.
  destruct eval1 as (h0_eq_h1 & st0_eq_st1 & red1).
  destruct eval2 as (h0_eq_h2 & st0_eq_st1' & red2).
  rewrite <- h0_eq_h1, h0_eq_h2.
  rewrite <- st0_eq_st1, st0_eq_st1'.
  split; try split; trivial.

  fold JFIPartialEval in *.
  unfold JFIEval.

  rewrite st0_eq_st1 in red1, red2.

  destruct (red CC (h0, st1)); try destruct red1.
  destruct p.
  exists h, f.
  split; assumption.
Qed.

Lemma EvaluationLastStepIsDeterministic : forall confs h0 st0 hn hn' res res' CC,
 (JFIPartialEval h0 st0 []    hn  [ [] [[ JFVal1 (JFVLoc res)  ]]_ None ] CC) ->
 (JFIPartialEval h0 st0 confs hn' [ [] [[ JFVal1 (JFVLoc res') ]]_ None ] CC) ->
 ([] = confs /\ hn = hn' /\ res = res').
Proof.
  intros confs h0 st0 hn hn' res res' CC.
  intros eval1 eval2.
  unfold JFIPartialEval in *.
  destruct eval1 as (h0_eq_hn & st0_is_res).
  destruct confs.
  + destruct eval2 as (h0_eq_hn' & st0_is_res').
    rewrite st0_is_res' in st0_is_res.
    injection st0_is_res as res_eq_res'.
    rewrite <- h0_eq_hn, h0_eq_hn', res_eq_res'.
    split; try split; trivial.
  + exfalso.
    destruct p.
    destruct eval2 as (h0_eq_h & st0_eq_f & red2).
    rewrite st0_is_res in red2.
    unfold red in red2.
    exact red2.
Qed.

Lemma PartialEvaluationIsDeterministic : forall confs confs' h0 st0 hn hn' res res' CC,
  (JFIPartialEval h0 st0 confs  hn  [ [] [[ JFVal1 (JFVLoc res)  ]]_ None ] CC)  ->
  (JFIPartialEval h0 st0 confs' hn' [ [] [[ JFVal1 (JFVLoc res') ]]_ None ] CC) ->
  (confs = confs' /\ hn = hn' /\ res = res').
Proof.
  intros confs.
  induction confs as [ | (h, st)].
  + apply EvaluationLastStepIsDeterministic.
  + intros confs' h0 st0 hn hn' res res' CC.
    intros e_eval_hs e_eval_hs'.
    destruct confs' as [ | (h', st')].
    ++ apply EvaluationLastStepIsDeterministic with (hn := hn') (res := res') in e_eval_hs.
       +++ destruct e_eval_hs as (false & _).
           discriminate false.
       +++ exact e_eval_hs'.
    ++ destruct (EvaluationFirstStepIsDeterministic h0 st0 h h' st st' confs confs' hn hn'
           [ [] [[ JFVal1 (JFVLoc res)  ]]_ None ]  [ [] [[ JFVal1 (JFVLoc res')  ]]_ None ] CC e_eval_hs e_eval_hs')
        as (h_eq_h' & (st_eq_st' & new_h & (e' & (e'_eval_hs & e'_eval_hs')))).
       set (IH_applied := IHconfs confs' new_h e'  hn hn' res res' CC e'_eval_hs e'_eval_hs').
       destruct IH_applied as (confs_eq_confs' & (hn_eq_hn' & res_eq_res')).
       split; try split.
       +++ rewrite <- h_eq_h'.
           rewrite <- st_eq_st'.
           rewrite <- confs_eq_confs'.
           trivial.
       +++ exact hn_eq_hn'.
       +++ exact res_eq_res'.
Qed.

Lemma EvaluationIsDeterministic : forall confs confs' h0 e hn hn' res res' CC,
  (JFIEval h0 e confs  hn  res CC)  ->
  (JFIEval h0 e confs' hn' res' CC) ->
  (confs = confs' /\ hn = hn' /\ res = res').
Proof.
  intros confs confs' h0 e hn hn' res res' CC.
  intros eval1 eval2.
  destruct (PartialEvaluationIsDeterministic confs confs' h0 [ [] [[ e ]]_ None] hn hn' res res' CC)
    as (confs_eq & res_eq & stn_eq); try assumption.
  split; try split; assumption.
Qed.

Lemma EvaluationSplit : forall confs_part confs_full h st hn res h' st' CC,
  let stn := [ [] [[JFVal1 (JFVLoc res) ]]_ None] in
  (JFIPartialEval h st confs_full hn stn CC) ->
  (JFIPartialEval h st confs_part h' st' CC) ->
   exists confs_rest, JFIPartialEval h' st' confs_rest hn stn CC.
Proof.
  intros confs_part.
  induction confs_part.
  + intros confs_full h st hn res h' st' CC.
    intros stn eval_full eval_part.
    exists confs_full.
    destruct eval_part as (h_eq_h' & st_eq_st').
    rewrite <-h_eq_h', <-st_eq_st'.
    exact eval_full.
  + intros confs_full h st hn res h' st' CC.
    intros stn eval_full eval_part.
    destruct confs_full.
    ++ exfalso.
       unfold stn in eval_full.
       unfold JFIPartialEval in eval_full, eval_part.
       destruct a.
       destruct eval_full as (h_eq_hn & st_is_res).
       destruct eval_part as (_ & _ & red2).
       rewrite st_is_res in red2.
       unfold red in red2.
       destruct red2.
    ++ unfold JFIPartialEval in eval_full, eval_part.
       destruct p, a.
       destruct eval_full as (h_eq_h0 & st_eq_f & red_full).
       destruct eval_part as (h_eq_h1 & st_eq_f0 & red_part).
       destruct (red CC (h, st)); try destruct red_full.
       destruct p as (red_h & red_st).
       fold JFIPartialEval in *.
       apply IHconfs_part with (h' := h') (st' := st') in red_full as (confs_rest & eval_rest); try apply red_part.
       exists confs_rest.
       exact eval_rest.
Qed.

(* =================== Reduction step preserves context at the bottom until inner expression fully evaluates ================ *)

Definition InnerExprRedPreservesLetCtx expr := forall h0 ctx class x e2 confs hn res A CC,
  (JFIPartialEval h0
     [(ctx ++ [JFCtxLet class x __ e2]) [[ expr ]]_ A]
      confs hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC) ->
  exists st' ctx' h' e1' A',
    red CC (h0, [(ctx ++ [JFCtxLet class x __ e2]) [[ expr ]]_ A]) = 
      Some (h', st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']).

Definition OuterExprRedPreservesLetCtx expr := forall h0 st ctx let_ctx class x e1 e2 confs hn res A A0 CC,
  (JFIPartialEval h0
     ([ctx [[ expr ]]_ A] ++ st ++ [(let_ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A0])
      confs hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC) ->
  exists st' ctx' h' e1' A',
    red CC (h0, [ctx [[ expr ]]_ A] ++ st ++ [(let_ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A0]) =
      Some (h', st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']).

Lemma AppNonemptyHasHead : forall A l (el : A),  exists (h : A) l', (l ++ [el]) = h::l'.
Proof.
  intros A l el.
  destruct l.
  + exists el, [].
    auto.
  + exists a, (l ++ [el]).
    auto.
Qed.
Arguments AppNonemptyHasHead {_} l el.

Lemma SinglAppIsCons : forall A l (x : A), [x] ++ l = x::l.
Proof.
  intros A l x.
  unfold app.
  trivial.
Qed.

Lemma app_split : forall T (a : T) l b,
(a :: l) ++ [b] = [a] ++ l ++ [b].
Proof.
  intros T a l b.
  unfold app.
  trivial.
Qed.

Lemma NewInnerRedPreservesLetCtx : forall mu cn vs, InnerExprRedPreservesLetCtx (JFNew mu cn vs).
Proof.
  intros mu cn vs h0 ctx class x e2 confs hn res A CC.
  intros let_eval.

  exists [], ctx.
  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.

  assert (ctx_has_head := AppNonemptyHasHead ctx (JFCtxLet class x __ e2)).
  destruct ctx_has_head as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.
  rewrite <- ctx_concat in *.

  destruct ctx_h.
  + destruct (list_map_opt loc_of_val vs), A; try destruct let_eval.
    destruct (alloc_init CC h0 cn l); try destruct let_eval.
    destruct p.
    exists h1, (JFVal1 (JFVLoc l0)), None.
    trivial.
  + destruct (list_map_opt loc_of_val vs), A; try destruct let_eval.
    destruct (alloc_init CC h0 cn l); try destruct let_eval.
    destruct p.
    exists h1, (JFVal1 (JFVLoc l0)), None.
    trivial.
Qed.

Lemma NewOuterRedPreservesLetCtx : forall mu cn vs, OuterExprRedPreservesLetCtx (JFNew mu cn vs).
Proof.
  intros mu cn vs h0 st ctx let_ctx class x e1 e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.
  rewrite SinglAppIsCons in *.

  destruct ctx.
  + destruct A; try destruct let_eval.
    destruct (list_map_opt loc_of_val vs); try destruct let_eval.
    destruct (alloc_init CC h0 cn l); try destruct let_eval.
    destruct p.
    exists (([] [[JFVal1 (JFVLoc l0) ]]_ None)::st), let_ctx, h1, e1, A_top.
    trivial.
  + destruct A; try (destruct j; destruct let_eval).
    destruct (list_map_opt loc_of_val vs); try (destruct j; destruct let_eval).
    destruct (alloc_init CC h0 cn l); try (destruct j; destruct let_eval).
    destruct p.
    exists (ctx _[ j _[[_ JFVal1 (JFVLoc l0) _]]_ None ]_ :: st), let_ctx, h1, e1, A_top.
    destruct j; trivial.
Qed.

Lemma LetInnerRedPreservesLetCtx : forall cn x e1 e2, InnerExprRedPreservesLetCtx (JFLet cn x e1 e2).
Proof.
  intros cn x e1 e2 h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.
  exists [], ([JFCtxLet cn x __ e2] ++ ctx).

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.

  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat.
  rewrite <- ctx_concat.
  destruct A.
  + destruct (ctx ++ [JFCtxLet outer_class outer_x __ outer_e2]) in let_eval; try destruct let_eval.
    destruct j0 in let_eval; try destruct let_eval.
  + exists h0, e1, None.
   destruct ctx_h; try destruct let_eval; trivial.
Qed.

Lemma LetOuterRedPreservesLetCtx : forall cn x e1 e2, OuterExprRedPreservesLetCtx (JFLet cn x e1 e2).
Proof.
  intros cn x e1 e2 h0 st ctx let_ctx outer_class outer_x outer_e1 outer_e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.
  rewrite SinglAppIsCons in *.

  destruct ctx.
  + exists ([ [] _[ JFCtxLet cn x __ e2 _[[_ e1 _]]_ None ]_ ] ++ st), let_ctx, h0, outer_e1, A_top.
    destruct A; try destruct let_eval; try trivial.
  + destruct j; destruct A; try destruct let_eval.
    ++ exists ((JFCtxLet C x0 Ctx E2 :: ctx) _[ JFCtxLet cn x __ e2 _[[_ e1 _]]_ None ]_ :: st),
          let_ctx, h0, outer_e1, A_top.
       trivial.
    ++ exists ((JFCtxTry Ctx mu C x0 E2 :: ctx) _[ JFCtxLet cn x __ e2 _[[_ e1 _]]_ None ]_ :: st),
          let_ctx, h0, outer_e1, A_top.
       trivial.
Qed.

Lemma IfInnerRedPreservesLetCtx : forall v1 v2 e1 e2, InnerExprRedPreservesLetCtx (JFIf v1 v2 e1 e2).
Proof.
  intros v1 v2 e1 e2 h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.
  exists [], ctx, h0.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.
  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.

  destruct v1, v2; try (destruct ctx_h; destruct let_eval).

  destruct (Loc_dec l l0).
  + exists e1, None.
    destruct ctx_h, A; trivial; try destruct let_eval.
  + exists e2, None.
    destruct ctx_h, A; trivial; try destruct let_eval.
Qed.

Lemma IfOuterRedPreservesLetCtx : forall v1 v2 e1 e2, OuterExprRedPreservesLetCtx (JFIf v1 v2 e1 e2).
Proof.
  intros v1 v2 e1 e2 h0 st ctx let_ctx outer_class outer_x outer_e1 outer_e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.
  rewrite SinglAppIsCons in *.

  destruct v1, v2; try (destruct ctx as [ | j]; try destruct j; destruct let_eval).
  destruct A.
  + destruct ctx as [ | j0]; try destruct j0; try destruct let_eval.
  + destruct (Loc_dec l l0).
    ++ exists ((ctx [[ e1 ]]_ None)::st), let_ctx, h0, outer_e1, A_top.
       destruct ctx; trivial.
       destruct j; trivial.
    ++ exists ((ctx [[ e2 ]]_ None)::st), let_ctx, h0, outer_e1, A_top.
       destruct ctx; trivial.
       destruct j; trivial.
Qed.

Lemma InvokeInnerRedPreservesLetCtx : forall v m vs, InnerExprRedPreservesLetCtx (JFInvoke v m vs).
Proof.
  intros v m vs h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.
  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.

  destruct v; try (destruct ctx_h; destruct let_eval).
  destruct l.
  + destruct ctx_h.
    ++ destruct A; try destruct let_eval.
       rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
       trivial.
    ++ destruct A; try destruct let_eval.
       rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
       trivial.
  + destruct ctx_h.
    ++ unfold getInvokeBody in *.
       destruct A, getClassName; try destruct let_eval.
       destruct methodLookup; try destruct let_eval.
       destruct substList; try destruct let_eval.
       rewrite <- ctx_concat.
       exists ([ [] [[j1 ]]_ None ]), ctx, h0, (JFInvoke (JFVLoc (JFLoc n)) m vs), None.
       trivial.
    ++ unfold getInvokeBody in *.
       destruct A, getClassName; try destruct let_eval.
       destruct methodLookup; try destruct let_eval.
       destruct substList; try destruct let_eval.
       rewrite <- ctx_concat.
       exists ([ [] [[j1 ]]_ None ]), ctx, h0, (JFInvoke (JFVLoc (JFLoc n)) m vs), None.
       trivial.
Qed.

Lemma InvokeOuterRedPreservesLetCtx : forall v m vs, OuterExprRedPreservesLetCtx (JFInvoke v m vs).
Proof.
  intros v m vs h0 st ctx let_ctx class x e1 e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  unfold red in *.
  rewrite SinglAppIsCons in *.

  destruct A; try (
   destruct ctx; destruct v as [ | l];
   destruct l; try destruct j0; destruct let_eval).

  destruct ctx, v; try destruct let_eval.
  + destruct l.
    ++ exists (([] [[JFVal1 NPE_val ]]_ NPE_mode)::st), let_ctx, h0, e1, A_top.
       trivial.
    ++ unfold getInvokeBody in *.
       destruct getClassName; try destruct let_eval.
       destruct methodLookup; try destruct let_eval.
       destruct substList; try destruct let_eval.
       exists (([] [[j1 ]]_ None)::([] [[JFInvoke (JFVLoc (JFLoc n)) m vs ]]_ None)::st),
          let_ctx, h0, e1, A_top.
       trivial.
  + destruct j.
    ++ destruct l.
       +++ exists (ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_::st),
              let_ctx, h0, e1, A_top.
           trivial.
       +++ unfold getInvokeBody in *.
           destruct getClassName; try destruct let_eval.
           destruct methodLookup; try destruct let_eval.
           destruct substList; try destruct let_eval.
            exists (([] [[j1 ]]_ None)
              ::ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFInvoke (JFVLoc (JFLoc n)) m vs _]]_ None ]_ 
              ::st), let_ctx, h0, e1, A_top.
           trivial.
    ++ destruct l.
       +++ exists (ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_ :: st),
              let_ctx, h0, e1, A_top.
           trivial.
       +++ unfold getInvokeBody in *.
           destruct getClassName; try destruct let_eval.
           destruct methodLookup; try destruct let_eval.
           destruct substList; try destruct let_eval.
            exists (([] [[j1 ]]_ None)
              ::ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFInvoke (JFVLoc (JFLoc n)) m vs _]]_ None ]_ 
              ::st),
              let_ctx, h0, e1, A_top.
           trivial.
  + destruct j; destruct let_eval.
Qed.

Lemma AssignInnerRedPreservesLetCtx : forall vx v, InnerExprRedPreservesLetCtx (JFAssign vx v).
Proof.
  intros vx v h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.

  unfold red in *.
  destruct vx.
  destruct v; try (
    destruct ctx_h; destruct j as [ | l];
    try destruct l; destruct let_eval
  ).
  destruct j.
  + destruct ctx_h.
    ++ destruct l0, A; try destruct let_eval.
       +++ rewrite <- ctx_concat.
           exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
           trivial.
       +++ destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
           destruct o.
           rewrite <- ctx_concat.
           exists [], ctx, (Heap.add n (JFXIdMap.add j0 l r, j) h0), (JFVal1 (JFVLoc l)), None.
           trivial.
    ++ destruct l0, A; try destruct let_eval.
       +++ rewrite <- ctx_concat.
           exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
           trivial.
       +++ destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
           destruct o.
           rewrite <- ctx_concat.
           exists [], ctx, (Heap.add n (JFXIdMap.add j0 l r, j) h0), (JFVal1 (JFVLoc l)), None.
           trivial.
  + destruct ctx_h; try destruct let_eval.
Qed.

Lemma AssignOuterRedPreservesLetCtx : forall vx v, OuterExprRedPreservesLetCtx (JFAssign vx v).
Proof.
  intros vx v h0 st ctx let_ctx class x e1 e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  rewrite SinglAppIsCons in *.
  unfold red in *.

  destruct vx.
  destruct ctx.
  + destruct j; try destruct let_eval.
    destruct l.
    ++ destruct A, v; try destruct let_eval.
       exists (([] [[JFVal1 NPE_val ]]_ NPE_mode)::st), let_ctx, h0, e1, A_top.
       trivial.
    ++ destruct A, v; try destruct let_eval.
       destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
       destruct o.
       exists (([] [[JFVal1 (JFVLoc l) ]]_ None)::st), let_ctx, (Heap.add n (JFXIdMap.add j0 l r, j) h0), e1, A_top.
       trivial.
  + destruct j; try destruct let_eval.
    ++ destruct l.
       +++ destruct A, v; try (destruct j1; destruct let_eval).
           destruct j1.
           - exists (ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_::st), let_ctx, h0, e1, A_top.
             trivial.
           - exists (ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_::st), let_ctx, h0, e1, A_top.
             trivial.
       +++ destruct A, v; try (destruct j1; destruct let_eval).
           destruct j1.
           - destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
             destruct o.
             exists (ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 (JFVLoc l) _]]_ None ]_::st), let_ctx,
                (Heap.add n (JFXIdMap.add j0 l r, j) h0), e1, A_top.
             trivial.
           - destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
             destruct o.
             exists (ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 (JFVLoc l) _]]_ None ]_::st), let_ctx,
                (Heap.add n (JFXIdMap.add j0 l r, j) h0), e1, A_top.
             trivial.
    ++ destruct j1; try destruct let_eval.
Qed.

Lemma Val1InnerRedPreservesLetCtx : forall v h0 ctx ctxs outer_class outer_x outer_e2 confs hn res A CC,
  (JFIPartialEval h0 [((ctx::ctxs) ++ [JFCtxLet outer_class outer_x __ outer_e2]) [[ JFVal1 v ]]_ A] confs 
                  hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC) ->
  exists st' ctx' h' e1' A',
    red CC (h0, [((ctx::ctxs) ++ [JFCtxLet outer_class outer_x __ outer_e2]) [[ JFVal1 v ]]_ A]) = 
      Some (h', st' ++ [(ctx' ++ [JFCtxLet outer_class outer_x __ outer_e2]) [[ e1' ]]_ A']).
Proof.
  intros v h0 ctx ctxs outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).

  unfold red in *.
  rewrite <- app_comm_cons in *.
  destruct v; try (destruct ctx; destruct let_eval).
  destruct A.
  + destruct ctx.
    ++ exists [], ctxs, h0, (JFVal1 (JFVLoc l)), (Some j).
       trivial.
    ++ destruct JaSubtype.subtype_bool.
       +++ exists [], ctxs, h0, (substExpr (JFVar x) l E2), None.
           trivial.
       +++ exists [], ctxs, h0, (JFVal1 (JFVLoc l)), (Some j).
           trivial.
  + destruct ctx.
    ++ exists [], ctxs, h0, (substExpr (JFVar x) l E2), None.
       trivial.
    ++ exists [], ctxs, h0, (JFVal1 (JFVLoc l)), None.
       trivial.
Qed.

Lemma Val1OuterRedPreservesLetCtx : forall v, OuterExprRedPreservesLetCtx (JFVal1 v).
Proof.
  intros v h0 st ctx let_ctx class x e1 e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval.
  destruct confs.
  + destruct let_eval as (h_eq & let_eval).
    apply app_eq_unit in let_eval.
    destruct let_eval.
    ++ discriminate (proj1 H).
    ++ destruct H as (_ & H).
       apply app_eq_nil in H.
       discriminate (proj2 H).
  + destruct p.
    fold JFIPartialEval in let_eval.
    destruct let_eval as (h_eq & (ctx_eq & let_eval)).
    rewrite SinglAppIsCons in *.
    unfold red in *.
   destruct v; try (destruct ctx as [ | j]; try destruct j; destruct let_eval).
   destruct ctx.
   ++ destruct A.
      +++ destruct st.
          - rewrite app_nil_l in *.
            destruct e1; try destruct let_eval.
            destruct A_top; try destruct let_eval.
            exists [], let_ctx, h0, (JFVal1 (JFVLoc l)), (Some j).
            trivial.
          - rewrite <- app_comm_cons in *.
            destruct f0; try destruct let_eval.
            destruct E; try destruct let_eval.
            destruct A; try destruct let_eval.
            exists ((Ctx [[JFVal1 (JFVLoc l) ]]_ Some j)::st), let_ctx, h0, e1, A_top.
            trivial.
      +++ destruct st.
          - rewrite app_nil_l in *.
            destruct e1, A_top; try destruct let_eval.
            exists [], let_ctx, h0, (JFVal1 (JFVLoc l)), None.
            trivial.
          - rewrite <- app_comm_cons in *.
          destruct f0; try destruct let_eval.
          destruct E; try destruct let_eval.
          destruct A; try destruct let_eval.
          exists ((Ctx [[JFVal1 (JFVLoc l) ]]_ None)::st), let_ctx, h0, e1, A_top.
          trivial.
   ++ destruct A.
      +++ destruct st.
          - rewrite app_nil_l in *.
            destruct j.
            -- exists [ctx [[JFVal1 (JFVLoc l) ]]_ Some j0], let_ctx, h0, e1, A_top.
               trivial.
            -- destruct (JaSubtype.subtype_bool CC (JFClass j0) (JFClass C)).
               --- exists [ctx [[substExpr (JFVar x0) l E2 ]]_ None], let_ctx, h0, e1, A_top.
                   trivial.
               --- exists [ctx [[JFVal1 (JFVLoc l) ]]_ Some j0], let_ctx, h0, e1, A_top.
                   trivial.
          - destruct j.
            -- exists ((ctx [[JFVal1 (JFVLoc l) ]]_ Some j0)::(f0 :: st)), let_ctx, h0, e1, A_top.
               trivial.
            -- destruct (JaSubtype.subtype_bool CC (JFClass j0) (JFClass C)).
               --- exists ((ctx [[substExpr (JFVar x0) l E2 ]]_ None)::(f0 :: st)), let_ctx, h0, e1, A_top.
                   trivial.
               --- exists ((ctx [[JFVal1 (JFVLoc l) ]]_ Some j0)::(f0 :: st)), let_ctx, h0, e1, A_top.
                   trivial.
      +++ destruct st.
          - destruct j.
            -- exists [ctx [[substExpr (JFVar x0) l E2 ]]_ None], let_ctx, h0, e1, A_top.
               trivial.
            -- exists [ctx [[JFVal1 (JFVLoc l) ]]_ None], let_ctx, h0, e1, A_top.
               trivial.
          - destruct j.
            -- exists ((ctx [[substExpr (JFVar x0) l E2 ]]_ None)::(f0::st)), let_ctx, h0, e1, A_top.
               trivial.
            -- exists ((ctx [[JFVal1 (JFVLoc l) ]]_ None)::(f0::st)), let_ctx, h0, e1, A_top.
               trivial.
Qed.

Lemma Val2InnerRedPreservesLetCtx : forall vx, InnerExprRedPreservesLetCtx (JFVal2 vx).
Proof.
  intros vx h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.

  unfold red in *.
  destruct vx.
  destruct j as [ | l]; try (destruct l; destruct ctx_h; destruct let_eval).
  destruct ctx_h.
  + destruct l, A; try destruct let_eval.
    ++ rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
       trivial.
    ++ destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
       destruct o.
       destruct (JFXIdMap.find (elt:=Loc) j0 r); try destruct let_eval.
       rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 (JFVLoc l)), None.
       trivial.
  + destruct l, A; try destruct let_eval.
    ++ rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
       trivial.
    ++ destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
       destruct o.
       destruct (JFXIdMap.find (elt:=Loc) j0 r); try destruct let_eval.
       rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 (JFVLoc l)), None.
       trivial.
Qed.

Lemma Val2OuterRedPreservesLetCtx : forall vx, OuterExprRedPreservesLetCtx (JFVal2 vx).
Proof.
  intros vx h0 st ctx let_ctx class x e1 e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  rewrite SinglAppIsCons in *.
  unfold red in *.

  destruct vx.
  destruct A; try (
    destruct ctx as [ | j2]; try destruct j2;
    destruct j as [ | l]; try destruct l; destruct let_eval).
  destruct ctx.
  + destruct j; try destruct let_eval.
    destruct l; try destruct let_eval.
    ++ exists (([] [[JFVal1 NPE_val ]]_ NPE_mode)::st), let_ctx, h0, e1, A_top.
       trivial.
    ++ destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
       destruct o.
       destruct (JFXIdMap.find (elt:=Loc) j0 r); try destruct let_eval.
       exists (([] [[JFVal1 (JFVLoc l) ]]_ None)::st), let_ctx, h0, e1, A_top.
       trivial.
  + destruct j.
    ++ destruct j1.
       +++ destruct l; try destruct let_eval.
           - exists ((ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_)::st), let_ctx, h0, e1, A_top.
             trivial.
           - destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
             destruct o.
             destruct (JFXIdMap.find (elt:=Loc) j0 r); try destruct let_eval.
             exists ((ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 (JFVLoc l) _]]_ None ]_)::st), let_ctx, h0, e1, A_top.
             trivial.
       +++ destruct l; try destruct let_eval.
           - exists ((ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_)::st), let_ctx, h0, e1, A_top.
             trivial.
           - destruct (Heap.find (elt:=Obj) n h0); try destruct let_eval.
             destruct o.
             destruct (JFXIdMap.find (elt:=Loc) j0 r); try destruct let_eval.
             exists ((ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 (JFVLoc l) _]]_ None ]_)::st), let_ctx, h0, e1, A_top.
             trivial.
    ++ destruct j1; try destruct let_eval.
Qed.

Lemma ThrowInnerRedPreservesLetCtx : forall v, InnerExprRedPreservesLetCtx (JFThrow v).
Proof.
  intros v h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.

  unfold red in *.
  destruct v; try (destruct ctx_h; destruct let_eval).
  destruct ctx_h.
  + destruct l, A; try destruct let_eval.
    ++ rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
       trivial.
    ++ destruct (class h0 n); try destruct let_eval.
       rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 (JFVLoc (JFLoc n))), (Some j).
       trivial.
  + destruct l, A; try destruct let_eval.
    ++ rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 NPE_val), NPE_mode.
       trivial.
    ++ destruct (class h0 n); try destruct let_eval.
       rewrite <- ctx_concat.
       exists [], ctx, h0, (JFVal1 (JFVLoc (JFLoc n))), (Some j).
       trivial.
Qed.

Lemma ThrowOuterRedPreservesLetCtx : forall v, OuterExprRedPreservesLetCtx (JFThrow v).
Proof.
  intros v h0 st ctx let_ctx class x e1 e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  rewrite SinglAppIsCons in *.
  unfold red in *.
  destruct A; try (
    destruct ctx as [ | j0]; try destruct j0;
    destruct v as [ | l]; try destruct l; destruct let_eval).
  destruct ctx.
  + destruct v; try destruct let_eval.
    destruct l.
    ++ exists (([] [[JFVal1 NPE_val ]]_ NPE_mode)::st), let_ctx, h0, e1, A_top.
       trivial.
    ++ destruct (Jafun.class h0 n); try destruct let_eval.
       exists (([] [[JFVal1 (JFVLoc (JFLoc n)) ]]_ Some j)::st), let_ctx, h0, e1, A_top.
       trivial.
  + destruct j.
    ++ destruct v; try destruct let_eval.
       destruct l.
       +++ exists (( ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_)::st), let_ctx, h0, e1, A_top.
           trivial.
       +++ destruct (Jafun.class h0 n); try destruct let_eval.
           exists ((ctx _[ JFCtxLet C x0 Ctx E2 _[[_ JFVal1 (JFVLoc (JFLoc n)) _]]_ Some j ]_)::st), let_ctx, h0, e1, A_top.
           trivial.
    ++ destruct v; try destruct let_eval.
       destruct l.
       +++ exists (( ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 NPE_val _]]_ NPE_mode ]_)::st), let_ctx, h0, e1, A_top.
           trivial.
       +++ destruct (Jafun.class h0 n); try destruct let_eval.
           exists ((ctx _[ JFCtxTry Ctx mu C x0 E2 _[[_ JFVal1 (JFVLoc (JFLoc n)) _]]_ Some j ]_)::st), let_ctx, h0, e1, A_top.
           trivial.
Qed.

Lemma TryInnerRedPreservesLetCtx : forall e1 mu cn x0 e2, InnerExprRedPreservesLetCtx (JFTry e1 mu cn x0 e2).
Proof.
  intros e1 mu cn x0 e2 h0 ctx outer_class outer_x outer_e2 confs hn res A CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  destruct (AppNonemptyHasHead ctx (JFCtxLet outer_class outer_x __ outer_e2))
   as (ctx_h & (ctx_l & ctx_concat)).
  rewrite ctx_concat in *.
  unfold red in *.
  rewrite <- ctx_concat in *.
  destruct ctx_h, A; try destruct let_eval.
  + exists [], ((JFCtxTry __ mu cn x0 e2)::ctx), h0, e1, None.
    trivial.
  + exists [], ((JFCtxTry __ mu cn x0 e2)::ctx), h0, e1, None.
    trivial.
Qed.

Lemma TryOuterRedPreservesLetCtx : forall e1 mu cn x0 e2, OuterExprRedPreservesLetCtx (JFTry e1 mu cn x0 e2).
Proof.
  intros e1 mu cn x0 e2 h0 st ctx let_ctx outer_class outer_x outer_e1 outer_e2 confs hn res A A_top CC.
  intros let_eval.

  unfold JFIPartialEval in let_eval;
  destruct confs; try discriminate (proj2 let_eval);
  fold JFIPartialEval in let_eval.
  destruct p.
  destruct let_eval as (_ & (_ & let_eval)).
  rewrite SinglAppIsCons in *.
  unfold red in *.
  destruct ctx.
  + destruct A; try destruct let_eval.
    exists (([] _[ JFCtxTry __ mu cn x0 e2 _[[_ e1 _]]_ None ]_)::st), let_ctx, h0, outer_e1, A_top.
    trivial.
  + destruct A; try destruct let_eval.
    destruct j; try destruct let_eval.
    destruct j.
    ++ exists (((JFCtxLet C x Ctx E2 :: ctx) _[ JFCtxTry __ mu cn x0 e2 _[[_ e1 _]]_ None ]_)::st), let_ctx, h0, outer_e1, A_top.
       trivial.
    ++ exists (((JFCtxTry Ctx mu0 C x E2:: ctx) _[ JFCtxTry __ mu cn x0 e2 _[[_ e1 _]]_ None ]_)::st), let_ctx, h0, outer_e1, A_top.
       trivial.
Qed.

Lemma OnlyFrameIsValOrRedPreservesLetCtx : forall h0 class x e1 e2 confs hn res A CC ctx,
  let st0 := [ (ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A ] in
  JFIPartialEval h0 st0 confs hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC ->
   (ctx = [] /\ exists e1_res, e1 = JFVal1 (JFVLoc e1_res) /\ A = None) \/
   (exists st' ctx' h' e1' A', red CC (h0, st0) = Some (h', st' ++ [ (ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A' ])).
Proof.
  intros h0 class x e1 e2 confs hn res A CC ctx.
  destruct e1;
    intros st0 let_eval.
  + apply or_intror.
    apply NewInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + apply or_intror.
    apply LetInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + apply or_intror.
    apply IfInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + apply or_intror.
    apply InvokeInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + apply or_intror.
    apply AssignInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + destruct ctx.
    ++ apply or_introl.
       split; trivial.
       unfold st0 in let_eval.
       rewrite app_nil_l in let_eval.
       unfold JFIPartialEval in let_eval.
       destruct confs; try discriminate (proj2 (let_eval)).
       destruct p.
       fold JFIPartialEval in let_eval.
       destruct let_eval as (h_eq & f_eq & red_is_some).
       unfold red in red_is_some.
       destruct v; try destruct red_is_some.
       exists l; split; trivial.
       destruct A; trivial.
       unfold JFIPartialEval in red_is_some.
       destruct confs. 
       +++ discriminate (proj2 (red_is_some)).
       +++ destruct p.
           destruct red_is_some as (_ & _ & red_is_some).
           unfold red in red_is_some.
           destruct red_is_some.
    ++ apply or_intror.
       apply Val1InnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
       exact let_eval.
  + apply or_intror.
    apply Val2InnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + apply or_intror.
    apply ThrowInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + apply or_intror.
    apply TryInnerRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
Qed.

Lemma TopFrameRedPreservesLetCtx : forall h0 f st let_ctx class x e2 e1 confs hn res A CC,
  let st0 := [ f ] ++ st ++
             [ (let_ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A ] in
  JFIPartialEval h0 st0 confs hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC ->
   (exists st' ctx' h' e1' A', red CC (h0, st0) = Some (h', st' ++ [ (ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A' ])).
Proof.
  intros h0 f st let_ctx class x e2 e1 confs hn res A CC.
  intros st0 let_eval.
  destruct f.
  destruct E.
  + unfold st0 in *.
    apply NewOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply LetOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply IfOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply InvokeOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply AssignOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply Val1OuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply Val2OuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply ThrowOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
  + unfold st0 in *.
    apply TryOuterRedPreservesLetCtx with (confs := confs) (hn := hn) (res := res).
    exact let_eval.
Qed.

Lemma RedPreservesLetCtxUntilE2Evaluates : forall h0 class x e1 e2 confs hn res A CC st ctx,
  let st0 := st ++ [ (ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A ] in
  JFIPartialEval h0 st0 confs hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC ->
   (st = [] /\ ctx = [] /\ exists e1_res, e1 = JFVal1 (JFVLoc e1_res) /\ A = None) \/
   (exists st' ctx' h' e1' A', red CC (h0, st0) = Some (h', st' ++ [ (ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A' ])).
Proof.
  intros h0 class x e1 e2 confs hn res A CC st ctx.
  intros st0 let_eval.
  destruct st.
  + unfold st0 in let_eval.
    rewrite app_nil_l in let_eval.
    apply OnlyFrameIsValOrRedPreservesLetCtx in let_eval
      as [(ctx_empty & exists_e1_res) | red_is_some].
    ++ apply or_introl.
       split; try split; try assumption.
    ++ apply or_intror.
       exact red_is_some.
  + apply or_intror.
    unfold st0 in let_eval.
    rewrite app_split in let_eval.
    assert (tmp := TopFrameRedPreservesLetCtx _ _ _ _ _ _ _ _ _ _ _ _ _ let_eval);
    destruct tmp as (st' & ctx' & h' & e1' & red_is_some).
    exists st', ctx', h', e1'.
    rewrite <- app_split in red_is_some.
    fold st0 in red_is_some.
    exact red_is_some.
Qed.

(* ======================== Let evaluation ======================== *)

Definition LetCtxSt ctxs class x e1 e2 :=
  [(ctxs ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ None].

Definition LetCtxStInEnv ctxs class x e1 e2 env :=
  LetCtxSt ctxs class x (JFIExprSubstituteEnv env e1) (JFIExprSubstituteEnv env e2).

(* Evaluation with stripped last context *)

Definition E1ConfIsStrippedLetConf (e1_conf conf : Heap * FrameStack) class x e2 :=
  fst e1_conf = fst conf /\ 
  exists st ctxs e1 A,
    snd e1_conf = st ++ [ ctxs [[ e1 ]]_ A] /\
    snd conf    = st ++ [(ctxs ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A].

Fixpoint E1ConfsAreStrippedLetConfs e1_confs confs class x e2:=
  match (e1_confs, confs) with
  | (e1_conf::e1_confs, conf::confs) => E1ConfIsStrippedLetConf e1_conf conf class x e2 /\ E1ConfsAreStrippedLetConfs e1_confs confs class x e2
  | ([], []) => True
  | _ => False
  end.

Lemma StrippedConfHasSameHeap : forall e1_h e1_st let_h let_st h class x e2,
  E1ConfIsStrippedLetConf (e1_h, e1_st) (let_h, let_st) class x e2 -> let_h = h -> e1_h = h.
Proof.
  intros.
  unfold E1ConfIsStrippedLetConf, fst in H.
  destruct H as (h_eq & _).
  rewrite h_eq.
  exact H0.
Qed.

Lemma ForStripedConfExistLetContext : forall e1_h e1_st let_h let_st class x e2,
  E1ConfIsStrippedLetConf (e1_h, e1_st) (let_h, let_st) class x e2 ->
  exists st ctx e1 A, 
   st ++ [(ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A] = let_st /\
   st ++ [ ctx [[ e1 ]]_ A] = e1_st.
Proof.
  intros.
  unfold E1ConfIsStrippedLetConf in H.
  destruct H as (_ & st & ctx & e1 & A & e1_st_eq & st_eq).
  exists st, ctx, e1, A.
  split.
  + unfold LetCtxSt, snd in st_eq.
    symmetry.
    exact st_eq.
  + unfold snd in e1_st_eq.
    symmetry.
    exact e1_st_eq.
Qed.

Lemma StrenghtenInAssumption : forall T (h : T) l (p : T -> Prop),
  (forall x, (In x (h::l)) -> p x) ->
  (forall x, ((In x l) -> p x)).
Proof.
  intros T h l p.
  intros forall_x_px.
  intros x x_in_l.
  apply forall_x_px.
  apply List.in_cons.
  exact x_in_l.
Qed.

Lemma ExistsStrippedInnerLetEvaluation : forall confs class x e2,
  (forall conf, In conf confs -> 
    exists conf_h st' ctxs' e1' A', conf = (conf_h, st' ++ [(ctxs' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A'])) ->
  exists e1_confs, E1ConfsAreStrippedLetConfs e1_confs confs class x e2.
Proof.
  intros confs class x e2.
  intros forall_conf_confs_exists_stripped_conf.
  induction confs as [ | conf].
  + exists [].
    simpl.
    trivial.
  + destruct (forall_conf_confs_exists_stripped_conf conf (List.in_eq conf confs))
      as (e1_h & st' & ctxs' & e1' & A' & conf_eq).
    assert (e1_confs : forall conf0 : Heap * list Frame,
               In conf0 confs ->
               exists (conf_h : Heap) st' (ctxs' : list JFContextNode) (e1' : JFExpr) A',
                 conf0 = (conf_h, st' ++ [(ctxs' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']));
      [apply StrenghtenInAssumption with (h := conf);
       exact forall_conf_confs_exists_stripped_conf |].
    apply IHconfs in e1_confs as (e1_confs & e1_confs_stripped).
    unfold LetCtxSt in conf_eq.
    exists ((e1_h, st' ++ [ctxs' [[ e1' ]]_ A'])::e1_confs).
    simpl.
    split.
    ++ rewrite conf_eq.
       unfold E1ConfIsStrippedLetConf, fst, snd.
       split; trivial.
       exists st', ctxs', e1', A'.
       split; trivial.
    ++ exact e1_confs_stripped.
Qed.

Lemma CtxInjection : forall (h : Heap) h' st st' ctx ctx' class x e2 e1 e1' A A',
  Some (h, st ++ [(ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) =
    Some (h', st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']) ->
  Some (h, st ++ [ctx [[ e1 ]]_ A]) =
    Some (h', st' ++ [ctx' [[ e1' ]]_ A']).
Proof.
  intros h h' st st' ctx ctx' class x e2 e1 e1' A A'.
  intros conf_eq.
  injection conf_eq.
  intros ctx_eq h_eq.
  rewrite h_eq.
  apply app_inj_tail in ctx_eq.
  destruct ctx_eq as (st_eq_st' & ctx_eq).
  rewrite st_eq_st'.
  injection ctx_eq.
  intros A_eq_A' e1_eq_e1' let_eq.
  rewrite e1_eq_e1', A_eq_A'.
  apply app_inj_tail in let_eq.
  destruct let_eq as (ctx_eq_ctx' & let_eq).
  rewrite ctx_eq_ctx'.
  trivial.
Qed.

Lemma StrippedRedExistsInnerRedex : forall h h' st' ctx ctx' class x e2 e1 e1' A A' CC,
  red CC (h , [(ctx  ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) =
    Some (h', st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']) ->
  red CC (h , [ctx  [[ e1 ]]_ A]) =
    Some (h', st' ++ [ctx' [[ e1' ]]_ A']).
Proof.
  intros h h' st' ctx ctx' class x e2 e1 e1' A A' CC.
  intros red_let.

  unfold red in *.
  destruct e1.
  + destruct ctx.
    ++ destruct A; try discriminate red_let.
       rewrite app_nil_l in red_let.
       destruct (list_map_opt loc_of_val vs); try discriminate red_let.
       destruct (alloc_init CC h cn l ); try discriminate red_let.
       destruct p.
       apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2).
       exact red_let.
    ++ rewrite <- app_comm_cons in red_let.
       destruct j; 
         destruct A; try discriminate red_let;
         destruct (list_map_opt loc_of_val vs); try discriminate red_let;
         destruct (alloc_init CC h cn l ); try discriminate red_let;
         destruct p;
         apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
         exact red_let.
  + destruct ctx; try destruct j; destruct A; try discriminate red_let;
     try rewrite app_nil_l in red_let;
     apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
     exact red_let.
  + destruct ctx; try destruct j; destruct A; try discriminate red_let;
     destruct v1, v2; try discriminate red_let;
     destruct (Loc_dec l l0);
       apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
       exact red_let.
  + destruct ctx.
    ++ rewrite app_nil_l in red_let.
       destruct v; try discriminate red_let.
       destruct l, A; try discriminate red_let.
       +++ apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ unfold getInvokeBody in *.
           destruct (getClassName h n); try discriminate red_let.
           destruct (methodLookup CC j m); try discriminate red_let.
           destruct (substList (map JFVar (params_of_md j0)) vs
                  (substExpr JFThis (JFLoc n) (body_of_md j0))); try discriminate red_let.
           apply CtxInjection with (ctx := []) (st := [ [] [[j1 ]]_ None]) (class := class) (x := x) (e2 := e2);
             exact red_let.
    ++ rewrite <- app_comm_cons in red_let.
       destruct j; destruct v; try discriminate red_let.
       +++ destruct l, A; try discriminate red_let.
           - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
               exact red_let.
           - unfold getInvokeBody in *.
             destruct (getClassName h n); try discriminate red_let.
             destruct (methodLookup CC j m); try discriminate red_let.
             destruct (substList (map JFVar (params_of_md j0)) vs
               (substExpr JFThis (JFLoc n) (body_of_md j0))); try discriminate red_let.
             apply CtxInjection with (st := [ [] [[j1 ]]_ None]) (class := class) (x := x) (e2 := e2);
               exact red_let.
       +++ destruct l, A; try discriminate red_let.
           - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
               exact red_let.
           - unfold getInvokeBody in *.
             destruct (getClassName h n); try discriminate red_let.
             destruct (methodLookup CC j m); try discriminate red_let.
             destruct (substList (map JFVar (params_of_md j0)) vs
               (substExpr JFThis (JFLoc n) (body_of_md j0))); try discriminate red_let.
             apply CtxInjection with (st := [ [] [[j1 ]]_ None]) (class := class) (x := x) (e2 := e2);
               exact red_let.
  + destruct vx.
    destruct ctx.
    ++ destruct j; try discriminate red_let.
       destruct l; try discriminate red_let.
       +++ destruct v, A; try discriminate red_let.
           apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ destruct v, A; try discriminate red_let.
           destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
           destruct o.
           apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
    ++ destruct j1.
       +++ destruct j; try discriminate red_let.
           destruct l.
           - destruct v, A; try discriminate red_let.
             apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
               exact red_let.
           - destruct v, A, (Heap.find (elt:=Obj) n h); try discriminate red_let.
             destruct o.
             destruct (Heap.add n (JFXIdMap.add j0 l r, j) h); try discriminate red_let.
             apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
               exact red_let.
       +++ destruct j; try (rewrite <- app_comm_cons in red_let; discriminate red_let).
           destruct l, v, A; try discriminate red_let.
           - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
               exact red_let.
           - destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
             destruct o.
             apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
               exact red_let.
  + destruct ctx.
    ++ exfalso.
       rewrite app_nil_l in red_let.
       destruct v; try discriminate red_let.
       destruct A;
        injection red_let;
        intros st_eq _;
        symmetry in st_eq;
        rewrite <- app_nil_l in st_eq;
        apply app_inj_tail in st_eq as (_ & ctx_eq);
        injection ctx_eq;
        intros _ _ ctx_is_nil;
        apply app_eq_nil in ctx_is_nil as (_ & unit_is_nil);
        discriminate unit_is_nil.
    ++ rewrite <- app_comm_cons in red_let.
       destruct j, v, A; try discriminate red_let;
         try apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
         try exact red_let.
       destruct (JaSubtype.subtype_bool CC (JFClass j) (JFClass C)); 
         apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
         exact red_let.
  + destruct vx.
    destruct ctx.
    ++ destruct j; try discriminate red_let.
       destruct l, A; try discriminate red_let.
       +++ apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
           destruct o.
           destruct (JFXIdMap.find (elt:=Loc) j0 r); try discriminate red_let.
           apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
   ++ destruct j1.
      +++ destruct j; try discriminate red_let.
          destruct l, A; try discriminate red_let.
          - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
            destruct o.
            destruct (JFXIdMap.find (elt:=Loc) j0 r); try discriminate red_let.
            apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
      +++ destruct j; try discriminate red_let.
          destruct l, A; try discriminate red_let.
          - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
            destruct o.
            destruct (JFXIdMap.find (elt:=Loc) j0 r); try discriminate red_let.
            apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
  + destruct ctx.
    ++ destruct v; try discriminate red_let.
       destruct l, A; try discriminate red_let.
       +++ apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
           exact red_let.
       +++ destruct (Jafun.class h n); try discriminate red_let.
           apply CtxInjection with (ctx := []) (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
   ++ destruct j.
      +++ destruct v; try discriminate red_let.
          destruct l, A; try discriminate red_let.
          - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Jafun.class h n); try discriminate red_let.
            apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
      +++ destruct v; try discriminate red_let.
          destruct l, A; try discriminate red_let.
          - apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Jafun.class h n); try discriminate red_let.
            apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
              exact red_let.
  + destruct ctx as [ | j]; destruct A; try destruct j; try discriminate red_let;
     apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
     exact red_let.
Qed.



Lemma StrippedRedExistsOuterRedex : forall h h' f st st' inner_ctx ctx' class x e2 e1 e1' A A' CC,
  red CC (h , (f::st) ++ [(inner_ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) =
    Some (h', st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']) ->
  red CC (h,  (f::st) ++ [inner_ctx [[ e1  ]]_ A]) =
    Some (h', st' ++ [ctx' [[ e1' ]]_ A']).
Proof.
  intros h h' f st st' inner_ctx ctx' class x e2 e1 e1' A A' CC.
  intros red_let.
  rewrite <- app_comm_cons in *.
  destruct f as (ctx, e, A0).
  unfold red in *.
  destruct e.
  + destruct ctx.
    ++ destruct A0; try discriminate red_let.
       destruct (list_map_opt loc_of_val vs); try discriminate red_let.
       destruct (alloc_init CC h cn l ); try discriminate red_let.
       destruct p.
       rewrite app_comm_cons.
       apply CtxInjection with (class := class) (x := x) (e2 := e2).
       exact red_let.
    ++ destruct j; 
         destruct A0; try discriminate red_let;
         destruct (list_map_opt loc_of_val vs); try discriminate red_let;
         destruct (alloc_init CC h cn l ); try discriminate red_let;
         destruct p;
         rewrite app_comm_cons;
         apply CtxInjection with (class := class) (x := x) (e2 := e2);
         exact red_let.
  + destruct ctx; try destruct j; destruct A0; try discriminate red_let;
     try rewrite app_nil_l in red_let;
     rewrite app_comm_cons;
     apply CtxInjection with (class := class) (x := x) (e2 := e2);
     exact red_let.
  + destruct ctx; try destruct j; destruct A0; try discriminate red_let;
     destruct v1, v2; try discriminate red_let;
     destruct (Loc_dec l l0);
       rewrite app_comm_cons;
       apply CtxInjection with (class := class) (x := x) (e2 := e2);
       exact red_let.
  + destruct ctx.
    ++ destruct v; try discriminate red_let.
       destruct l, A0; try discriminate red_let.
       +++ rewrite app_comm_cons;
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ unfold getInvokeBody in *.
           destruct (getClassName h n); try discriminate red_let.
           destruct (methodLookup CC j m); try discriminate red_let.
           destruct (substList (map JFVar (params_of_md j0)) vs
                  (substExpr JFThis (JFLoc n) (body_of_md j0))); try discriminate red_let.
           rewrite 2!app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
    ++ destruct j; destruct v; try discriminate red_let.
       +++ destruct l, A0; try discriminate red_let.
           - rewrite app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
           - unfold getInvokeBody in *.
             destruct (getClassName h n); try discriminate red_let.
             destruct (methodLookup CC j m); try discriminate red_let.
             destruct (substList (map JFVar (params_of_md j0)) vs
               (substExpr JFThis (JFLoc n) (body_of_md j0))); try discriminate red_let.
             rewrite 2!app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
       +++ destruct l, A0; try discriminate red_let.
           - rewrite app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
           - unfold getInvokeBody in *.
             destruct (getClassName h n); try discriminate red_let.
             destruct (methodLookup CC j m); try discriminate red_let.
             destruct (substList (map JFVar (params_of_md j0)) vs
               (substExpr JFThis (JFLoc n) (body_of_md j0))); try discriminate red_let.
             rewrite 2!app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
  + destruct vx.
    destruct ctx.
    ++ destruct j; try discriminate red_let.
       destruct l; try discriminate red_let.
       +++ destruct v, A0; try discriminate red_let.
           rewrite app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ destruct v, A0; try discriminate red_let.
           destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
           destruct o.
           rewrite app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
    ++ destruct j1.
       +++ destruct j; try discriminate red_let.
           destruct l.
           - destruct v, A0; try discriminate red_let.
             rewrite app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
           - destruct v, A0, (Heap.find (elt:=Obj) n h); try discriminate red_let.
             destruct o.
             destruct (Heap.add n (JFXIdMap.add j0 l r, j) h); try discriminate red_let.
             rewrite app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
       +++ destruct j; try discriminate red_let.
           destruct l, v, A0; try discriminate red_let.
           rewrite app_comm_cons.
           - apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
           - destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
             destruct o.
             rewrite app_comm_cons.
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
               exact red_let.
  + destruct st.
    ++ destruct ctx.
       +++ destruct v; try discriminate red_let.
           destruct A0; rewrite app_nil_l in *; destruct e1, A; try discriminate red_let;
             injection red_let;
             intros st_eq _;
             symmetry in st_eq; 
             apply app_eq_unit in st_eq as [(_ & ctx_eq) | (_ & unit_is_nil)]; try discriminate unit_is_nil;
             apply CtxInjection with (st := []) (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ destruct j, v; try discriminate red_let.
           - destruct A0;
               rewrite app_comm_cons;
               apply CtxInjection with (class := class) (x := x) (e2 := e2);
                 exact red_let.
           - destruct A0.
             -- destruct (JaSubtype.subtype_bool CC (JFClass j) (JFClass C));
                  rewrite app_comm_cons;
                  apply CtxInjection with (class := class) (x := x) (e2 := e2);
                  exact red_let.
             -- rewrite app_comm_cons.
                apply CtxInjection with (class := class) (x := x) (e2 := e2).
                exact red_let.
    ++ destruct ctx.
       +++ destruct v; try discriminate red_let.
           destruct f.
           rewrite <- app_comm_cons in *.
           destruct A0, E, A1; try discriminate red_let;
            rewrite app_comm_cons;
             apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ destruct j, v; try discriminate red_let.
           - destruct A0;
               rewrite app_comm_cons;
               apply CtxInjection with (class := class) (x := x) (e2 := e2);
                 exact red_let.
           - destruct A0.
             -- destruct (JaSubtype.subtype_bool CC (JFClass j) (JFClass C));
                  rewrite app_comm_cons;
                  apply CtxInjection with (class := class) (x := x) (e2 := e2);
                  exact red_let.
             -- rewrite app_comm_cons.
                apply CtxInjection with (class := class) (x := x) (e2 := e2).
                exact red_let.
  + destruct vx.
    destruct ctx.
    ++ destruct j; try discriminate red_let.
       destruct l, A0; try discriminate red_let.
       +++ rewrite app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
       +++ destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
           destruct o.
           destruct (JFXIdMap.find (elt:=Loc) j0 r); try discriminate red_let.
           rewrite app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
   ++ destruct j1.
      +++ destruct j; try discriminate red_let.
          destruct l, A0; try discriminate red_let.
          - rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
            destruct o.
            destruct (JFXIdMap.find (elt:=Loc) j0 r); try discriminate red_let.
            rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
      +++ destruct j; try discriminate red_let.
          destruct l, A0; try discriminate red_let.
          - rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Heap.find (elt:=Obj) n h); try discriminate red_let.
            destruct o.
            destruct (JFXIdMap.find (elt:=Loc) j0 r); try discriminate red_let.
            rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
  + destruct ctx.
    ++ destruct v; try discriminate red_let.
       destruct l, A0; try discriminate red_let.
       +++ rewrite app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
           exact red_let.
       +++ destruct (Jafun.class h n); try discriminate red_let.
           rewrite app_comm_cons.
           apply CtxInjection with (class := class) (x := x) (e2 := e2);
             exact red_let.
   ++ destruct j.
      +++ destruct v; try discriminate red_let.
          destruct l, A0; try discriminate red_let.
          - rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Jafun.class h n); try discriminate red_let.
            rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
      +++ destruct v; try discriminate red_let.
          destruct l, A0; try discriminate red_let.
          - rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
          - destruct (Jafun.class h n); try discriminate red_let.
            rewrite app_comm_cons.
            apply CtxInjection with (class := class) (x := x) (e2 := e2);
              exact red_let.
  + destruct ctx as [ | j]; destruct A0; try destruct j; try discriminate red_let;
     rewrite app_comm_cons;
     apply CtxInjection with (class := class) (x := x) (e2 := e2);
     exact red_let.
Qed.

Lemma StrippedRedExists : forall h st ctx class x e1 e2 h' st' ctx' e1' A A' CC,
  red CC (h, st ++ [(ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) =
     Some (h', st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']) ->
  red CC (h, st ++ [ctx [[ e1 ]]_ A]) =  Some (h', st' ++ [ctx' [[ e1' ]]_ A']).
Proof.
  intros h st ctx class x e1 e2 h' st' ctx' e1' CC.
  intros red_let.
  destruct st.
  + rewrite app_nil_l in *.
    apply StrippedRedExistsInnerRedex with (class := class) (x := x) (e2 := e2).
 + apply StrippedRedExistsOuterRedex with (class := class) (x := x) (e2 := e2).
Qed.

Lemma rewrite_red : forall h st hn st' CC,
  red CC (h, st) = Some (hn, st') ->
  match red CC (h, st) with
  | Some (h0, st0) => h0 = hn /\ st0 = st'
  | None => False
  end.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Lemma rewrite_red1 : forall h st h' st' e1_res e1_confs' hn CC,
  red CC (h, st) = Some (h', st') ->
  JFIPartialEval h' st' e1_confs' hn [ [] [[JFVal1 (JFVLoc e1_res) ]]_ None] CC ->
  match red CC (h, st) with
  | Some (h0, st0) => JFIPartialEval h0 st0 e1_confs' hn
      [ [] [[JFVal1 (JFVLoc e1_res) ]]_ None] CC
  | None => False
  end.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Lemma RedIsNoneIsFalseImpliesRedIsSome : forall CC conf p,
  match red CC conf with
  | Some (h, st) => p h st
  | None => False
  end -> exists h st, (red CC conf = Some (h, st) /\ p h st).
Proof.
  intros.
  destruct (Classical_Prop.classic (exists h st, red CC conf = Some (h, st))).
  + destruct H0 as (h & (st & red_is_some)).
    exists h, st.
    rewrite red_is_some in H.
    exact (conj red_is_some H).
  + destruct (red CC conf).
    ++ destruct p0.
       exists h, f.
       split; try trivial.
    ++ destruct H.
Qed.

Lemma StripConf : forall st ctx class x e1 e2 A e1_h e1_st let_h let_st,
  st ++ [(ctx ++ [JFCtxLet class x __ e2]) [[e1 ]]_ A] = let_st ->
  E1ConfIsStrippedLetConf (e1_h, e1_st) (let_h, let_st) class x e2 ->
  st ++ [ctx [[e1 ]]_ A] = e1_st.
Proof.
  intros.
  unfold E1ConfIsStrippedLetConf, snd in H0.
  destruct H0 as (_ & st' & ctx' & e1' & A' & e1_st_eq & let_st_eq').
  rewrite e1_st_eq.
  rewrite <- H in let_st_eq'.
  unfold LetCtxSt in let_st_eq'.
  apply app_inj_tail in let_st_eq' as (st_eq_st' & let_st_eq').
  injection let_st_eq' as tmp.
  apply app_inj_tail in tmp as (ctx_eq_ctx' & _).
  rewrite st_eq_st', ctx_eq_ctx', H0, H1.
  trivial.
Qed.

Lemma StrippedInnerLetEvaluationIsE1Evaluation : forall e1_confs h st ctx class x e1 e2 A confs hn e1_res CC,
  JFIPartialEval h (st ++ [(ctx ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) confs hn
      (LetCtxSt [] class x (JFVal1 (JFVLoc e1_res)) e2) CC ->
  E1ConfsAreStrippedLetConfs e1_confs confs class x e2 ->
  JFIPartialEval h (st ++ [ ctx [[ e1 ]]_ A]) e1_confs hn [ [] [[JFVal1 (JFVLoc e1_res) ]]_ None] CC.
Proof.
  intros e1_confs.
  unfold LetCtxSt.

  induction e1_confs;
    intros h st ctx class x e1 e2 A confs hn e1_res CC;
    intros inner_eval confs_stripped;
    destruct confs; try destruct confs_stripped.
  + unfold JFIPartialEval in inner_eval.
    destruct inner_eval as (h_eq_hn & inner_eval).
    rewrite <- app_nil_l in inner_eval.
    apply app_inj_tail in inner_eval as (st_empty & inner_eval).
    injection inner_eval.
    intros A_is_none e1_is_val ctx_is_nil.
    rewrite <- app_nil_l in ctx_is_nil.
    apply app_inv_tail in ctx_is_nil.
    rewrite ctx_is_nil, e1_is_val, st_empty, h_eq_hn, A_is_none.
    unfold JFIPartialEval.
    auto.
  + destruct e1_confs; destruct confs; try destruct H0.
    ++ rewrite app_nil_l in inner_eval.
       unfold JFIPartialEval in inner_eval |- *.
       destruct a as (e1_h & e1_st), p as (let_h & let_st).
       destruct inner_eval as (let_h_eq & (let_st_eq & let_red)).
       split; try split.
       +++ apply StrippedConfHasSameHeap with (h := h) in H; auto.
       +++ apply StripConf with (class := class) (x := x) (e2 := e2) (e1_h := e1_h)
                (let_h := let_h) (let_st := let_st); try assumption.
       +++ apply RedIsNoneIsFalseImpliesRedIsSome in let_red
             as (h0' & (st' & (red_is_some & (h'_eq & st'_eq)))).
           rewrite h'_eq, st'_eq in *.
           assert (strip_red := StrippedRedExists h st ctx class x e1 e2 hn [] []).
           rewrite app_nil_l in strip_red.
           apply strip_red in red_is_some.
           apply rewrite_red.
           apply red_is_some.
    ++ set (confs' := p1 :: confs) in *.
       set (e1_confs' := p0 :: e1_confs) in *.
       rewrite app_nil_l in inner_eval.
       destruct a as (e1_h & e1_st), p as (let_h & let_st).
       unfold JFIPartialEval in inner_eval |- *.
       fold JFIPartialEval in inner_eval |- *.

       destruct inner_eval as (let_h_eq & (let_st_eq & let_red)).
       split; try split.
       +++ apply StrippedConfHasSameHeap with (h := h) in H; auto.
       +++ apply StripConf with (class := class) (x := x) (e2 := e2) (e1_h := e1_h)
                (let_h := let_h) (let_st := let_st); try assumption.
       +++ apply RedIsNoneIsFalseImpliesRedIsSome in let_red
             as (h0' & (st0' & (red_is_some & inner_eval))).

           assert (tmp := inner_eval).
           unfold confs' in tmp.
           unfold JFIPartialEval in tmp.
           destruct p1.
           destruct tmp as (h0'_eq_h0 & (st0'_eq_f & _)).
           rewrite h0'_eq_h0, st0'_eq_f in *.
           clear h0'_eq_h0 st0'_eq_f h0'.

           assert (p0_stripped := H0).
           apply ForStripedConfExistLetContext in H0
              as (st' & ctx' & e1' & A' & f_eq & p0_eq).
           rewrite <- f_eq in red_is_some.

           assert (strip_red := StrippedRedExists h st ctx class x e1 e2 h0 st' ctx').
           apply strip_red in red_is_some.
           apply rewrite_red1 with
                  (h' := h0) (st' := st' ++ [ctx' [[e1' ]]_ A']); try assumption.
           apply IHe1_confs with (class := class) (x := x) (e2 := e2) (confs := confs').
           - rewrite f_eq.
             apply inner_eval.
           - unfold e1_confs', confs'.
             unfold E1ConfsAreStrippedLetConfs.
             split; assumption.
Qed.

(* Actual let evaluation lemmas *)

Lemma LetInnerEvaluation : forall confs st ctxs h class x e1 e2 hn res A CC,
  (JFIPartialEval h (st ++ [(ctxs ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) confs hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC) ->
   exists confs_e1 h' e1_res,
     JFIPartialEval h (st ++ [(ctxs ++ [JFCtxLet class x __ e2]) [[ e1 ]]_ A]) confs_e1 h' (LetCtxSt [] class x (JFVal1 (JFVLoc e1_res)) e2) CC /\
     forall conf, In conf confs_e1 -> exists conf_h st' ctxs' e1' A', conf = (conf_h, (st' ++ [(ctxs' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A'])).
Proof.
  intros confs.
  induction confs.
  + intros st ctxs h class x e1 e2 hn res A CC.
    intros let_eval.
    simpl in let_eval.
    unfold LetCtxSt in let_eval.
    simpl in let_eval.
    destruct ctxs.
    ++ destruct let_eval as (_ & st_eq).
       rewrite app_nil_l in st_eq.
       rewrite <- app_nil_l in st_eq.
       apply app_inj_tail in st_eq.
       discriminate (proj2 st_eq).
    ++ destruct let_eval as (_ & st_eq).
       rewrite <- app_nil_l in st_eq.
       apply app_inj_tail in st_eq.
       discriminate (proj2 st_eq).
  + intros st ctxs h class x e1 e2 hn res A CC.
    intros let_eval.
    destruct (RedPreservesLetCtxUntilE2Evaluates h class x e1 e2 (a :: confs) hn res A CC st ctxs let_eval)
        as [(st_empty & (ctxs_empty & (e1_res & is_val & A_is_None)))  | (st' & (ctx' & (h' & (e1' & A' & red_to_let_ctx))))].
    ++ rewrite is_val.
       exists [], h, e1_res.
       split.
       +++ unfold JFIPartialEval.
           rewrite st_empty, ctxs_empty, A_is_None.
           split; try split; try trivial.
       +++ intros conf conf_in_nil.
           destruct conf_in_nil.
    ++ unfold JFIPartialEval in let_eval.
       destruct a.
       destruct let_eval as (h_eq_h0 & (st_eq_f & let_red)).
       rewrite st_eq_f in *.

       replace (red CC (h, f)) with (Some
                   (h',
                   (st' ++ [(ctx' ++
                     [JFCtxLet class x __ e2])
                    [[e1' ]]_ A']))) in let_red.
       fold JFIPartialEval in let_red.

       unfold LetCtxStInEnv, LetCtxSt in IHconfs.
       apply IHconfs in let_red.

       destruct let_red as
          (confs_e1' & (hn_e1' & (e1_res & (eval_e1' & confs_e1'_let_ctx)))).
       exists ((h, f)::confs_e1'), hn_e1', e1_res.
       split.
       +++ unfold JFIPartialEval, LetCtxSt.
           split; try split; trivial.
           replace (red CC (h, f) ) with (Some
                   (h',
                   (st' ++ [(ctx' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A']))).
           fold JFIPartialEval.
           exact eval_e1'.
       +++ intros conf conf_in_confs.
           apply in_inv in conf_in_confs.
           destruct conf_in_confs as [conf_eq_h_f | conf_in_confs].
           - destruct conf as (conf_h, conf_f).
             exists h, st, ctxs, e1, A.
             rewrite st_eq_f.
             symmetry.
             exact conf_eq_h_f.
           - assert (exists_conf_h := confs_e1'_let_ctx conf conf_in_confs).
             destruct (confs_e1'_let_ctx conf conf_in_confs) as (conf_h & (st'' & (ctx'' & (e1'' & A'' & conf_h_st_l)))).
             unfold LetCtxSt.
             exists conf_h, st'', ctx'', e1'', A''.
             rewrite conf_h_st_l.
             trivial.
Qed.

Lemma LetE1Evaluation : forall h class x e1 e1_res e2 confs hn CC,
  (JFIPartialEval h (LetCtxSt [] class x e1 e2) confs hn (LetCtxSt [] class x (JFVal1 (JFVLoc e1_res)) e2) CC /\
    forall conf, In conf confs ->
      exists conf_h st' ctxs' e1' A', conf = (conf_h, st' ++ [(ctxs' ++ [JFCtxLet class x __ e2]) [[ e1' ]]_ A'])) ->
   exists confs_e1,
     JFIPartialEval h [ [] [[ e1 ]]_ None] confs_e1 hn
        [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ None] CC.
Proof.
  intros h class x e1 e1_res e2 confs hn CC.
  intros (inner_eval & confs_in_let_ctx).
  apply ExistsStrippedInnerLetEvaluation in confs_in_let_ctx as (e1_confs & e1_confs_are_stripped_confs).
  exists e1_confs.
  apply StrippedInnerLetEvaluationIsE1Evaluation with (st := []) (class := class) (x := x) (e2 := e2) (confs := confs); assumption.
Qed.

Lemma LetGoEvaluationStep : forall h class x env e1_res e2 confs_let_e2 hn res CC,
  ~StrMap.In x env ->
  JFIPartialEval h (LetCtxSt [] class x (JFVal1 (JFVLoc e1_res)) (JFIExprSubstituteEnv env e2))
            confs_let_e2 hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC ->
  exists confs_e2, JFIPartialEval h
            [ [] [[ JFIExprSubstituteEnv env (JFIExprSubstituteVal x (JFVLoc e1_res) e2) ]]_ None]
            confs_e2 hn [ [] [[JFVal1 (JFVLoc res) ]]_ None] CC.
Proof.
  intros h class x env e1_res e2 confs_let_e2 hn res CC.
  simpl.
  intros x_not_in_env let_eval.
  unfold JFIPartialEval, LetCtxSt in let_eval.
  destruct confs_let_e2.
  + discriminate (proj2 let_eval).
  + destruct p as (h0 & st0).
    destruct let_eval as (h_eq_h0 & (let_eq_st0 & let_eval)).
    exists confs_let_e2.
    rewrite app_nil_l in let_eval.
    unfold red in let_eval.
    rewrite SubstExprEqExprSubstituteVal in let_eval.
    rewrite <- SubstituteExprEnvComm in let_eval; assumption.
Qed.

Lemma LetEvaluation : forall h class x e1 e2 confs hn res env CC,
   (JFIEvalInEnv h (JFLet class x e1 e2) confs hn res env) CC ->
    exists confs_let_e1 confs_let_e2 h' e1_res,
      (JFIEvalInEnv h e1 confs_let_e1 h' e1_res env CC) /\
      (JFIEvalInEnv h' (JFIExprSubstituteVal x (JFVLoc e1_res) e2) confs_let_e2 hn res env CC).
Proof.
  intros h class x e1 e2 confs hn res env CC.
  intros let_eval.
  unfold JFIEvalInEnv, JFIEval in let_eval.
  unfold JFIExprSubstituteEnv in let_eval.
  fold JFIExprSubstituteEnv in let_eval.
  unfold JFIPartialEval in let_eval.
  destruct confs.
  + discriminate (proj2 let_eval).
  + destruct p as (h0, st0).
    destruct let_eval as (h_eq_h0 & (let_eq_st0 & let_eval)).
    fold JFIPartialEval in let_eval.
    unfold red in let_eval.
    assert (tmp := let_eval).
    apply (LetInnerEvaluation confs [] []) in tmp as (confs_let_e1 & (h' & (e1_res & e1_eval))).
    assert (e1_let_eval := e1_eval).
    destruct e1_let_eval as (e1_let_eval & _).
    rewrite app_nil_l in e1_eval.
    apply LetE1Evaluation in e1_eval as (confs_e1 & e1_eval).
    unfold LetCtxSt in e1_let_eval.
    rewrite app_nil_l in e1_let_eval.
    assert (outer_eval := EvaluationSplit _ _ _ _ _ _ _ _ _ let_eval e1_let_eval).
    destruct outer_eval as (confs_let_e2 & e2_eval).
    apply LetGoEvaluationStep in e2_eval as (confs_e2 & e2_eval); try apply StrMap.remove_1; try trivial.
    exists confs_e1, confs_e2, h', e1_res.
    split.
    ++ unfold JFIEvalInEnv, JFIEval.
       exact e1_eval.
    ++ unfold JFIEvalInEnv, JFIEval.
       rewrite RemoveSubstitutedVarFromEnv in e2_eval.
       exact e2_eval.
Qed.
