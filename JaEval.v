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
Require Import JaSubtype.
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

Definition JFIEval (h : Heap) (e : JFExpr) (confs : list (Heap * FrameStack)) (hn : Heap) (ex : JFEvMode) (res : Loc) (CC : JFProgram) : Prop :=
  let EmptyCtx := []
  in JFIPartialEval h [EmptyCtx [[ e ]]_ None] confs hn [EmptyCtx [[ JFVal1 (JFVLoc res) ]]_ ex] CC.

Definition JFIEvalInEnv (h : Heap) (e : JFExpr) (confs : list (Heap * FrameStack)) (hn : Heap) (exn : JFEvMode) (res : Loc) (env : JFITermEnv) (CC : JFProgram) : Prop :=
  JFIEval h (JFIExprSubstituteEnv env e) confs hn exn res CC.

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

Lemma EvaluationLastStepIsDeterministic : forall confs h0 st0 hn hn' ex res ex' res' CC,
 (JFIPartialEval h0 st0 []    hn  [ [] [[ JFVal1 (JFVLoc res)  ]]_ ex ] CC) ->
 (JFIPartialEval h0 st0 confs hn' [ [] [[ JFVal1 (JFVLoc res') ]]_ ex' ] CC) ->
 ([] = confs /\ hn = hn' /\ ex = ex' /\ res = res').
Proof.
  intros confs h0 st0 hn hn' ex res ex' res' CC.
  intros eval1 eval2.
  unfold JFIPartialEval in *.
  destruct eval1 as (h0_eq_hn & st0_is_res).
  destruct confs.
  + destruct eval2 as (h0_eq_hn' & st0_is_res').
    rewrite st0_is_res' in st0_is_res.
    injection st0_is_res.
    intros ex_eq_ex' res_eq_res'.
    rewrite <- h0_eq_hn, h0_eq_hn', res_eq_res', ex_eq_ex'.
    split; try split; try split; trivial.
  + exfalso.
    destruct p.
    destruct eval2 as (h0_eq_h & st0_eq_f & red2).
    rewrite st0_is_res in red2.
    unfold red in red2.
    destruct ex;
    exact red2.
Qed.

Lemma PartialEvaluationIsDeterministic : forall confs confs' h0 st0 hn hn' ex res ex' res' CC,
  (JFIPartialEval h0 st0 confs  hn  [ [] [[ JFVal1 (JFVLoc res)  ]]_ ex ] CC)  ->
  (JFIPartialEval h0 st0 confs' hn' [ [] [[ JFVal1 (JFVLoc res') ]]_ ex' ] CC) ->
  (confs = confs' /\ hn = hn' /\ ex = ex' /\ res = res').
Proof.
  intros confs.
  induction confs as [ | (h, st)].
  + apply EvaluationLastStepIsDeterministic.
  + intros confs' h0 st0 hn hn' ex res ex' res' CC.
    intros e_eval_hs e_eval_hs'.
    destruct confs' as [ | (h', st')].
    ++ apply EvaluationLastStepIsDeterministic with (hn := hn') (ex := ex') (res := res') in e_eval_hs.
       +++ destruct e_eval_hs as (false & _).
           discriminate false.
       +++ exact e_eval_hs'.
    ++ destruct (EvaluationFirstStepIsDeterministic h0 st0 h h' st st' confs confs' hn hn'
           [ [] [[ JFVal1 (JFVLoc res)  ]]_ ex ]  [ [] [[ JFVal1 (JFVLoc res')  ]]_ ex' ] CC e_eval_hs e_eval_hs')
        as (h_eq_h' & (st_eq_st' & new_h & (e' & (e'_eval_hs & e'_eval_hs')))).
       set (IH_applied := IHconfs confs' new_h e'  hn hn' ex res ex' res' CC e'_eval_hs e'_eval_hs').
       destruct IH_applied as (confs_eq_confs' & (hn_eq_hn' & res_eq_res')).
       split; try split.
       +++ rewrite <- h_eq_h'.
           rewrite <- st_eq_st'.
           rewrite <- confs_eq_confs'.
           trivial.
       +++ exact hn_eq_hn'.
       +++ exact res_eq_res'.
Qed.

Theorem EvaluationIsDeterministic : forall confs confs' h0 e hn hn' ex res ex' res' CC,
  (JFIEval h0 e confs  hn  ex  res CC)  ->
  (JFIEval h0 e confs' hn' ex' res' CC) ->
  (confs = confs' /\ hn = hn' /\ ex = ex' /\ res = res').
Proof.
  intros confs confs' h0 e hn hn' ex res ex' res' CC.
  intros eval1 eval2.
  destruct (PartialEvaluationIsDeterministic confs confs' h0 [ [] [[ e ]]_ None] hn hn' ex res ex' res' CC)
    as (confs_eq & res_eq & stn_eq); try assumption.
  split; try split; assumption.
Qed.

(* ======================= Evalution structure ======================= *)

Lemma EvaluationJoin : forall h st confs h' st' confs' h'' st'' CC,
  JFIPartialEval h  st  confs  h'  st'  CC ->
  JFIPartialEval h' st' confs' h'' st'' CC ->
  JFIPartialEval h  st (confs ++ confs') h'' st'' CC.
Proof.
Admitted.

(* ======================= Evalution in extended context ======================= *)

Definition ConfExtendedByCtx (ext_conf conf : Heap * FrameStack) ctx :=
  fst conf = fst ext_conf /\ 
  exists st ctxs e1 A,
    snd conf =     st ++ [ ctxs           [[ e1 ]]_ A] /\
    snd ext_conf = st ++ [(ctxs ++ [ctx]) [[ e1 ]]_ A].

Fixpoint ConfsExtendedByCtx ext_confs confs ctx:=
  match (ext_confs, confs) with
  | (ext_conf::ext_confs, conf::confs) => ConfExtendedByCtx ext_conf conf ctx /\ ConfsExtendedByCtx ext_confs confs ctx
  | ([], []) => True
  | _ => False
  end.

Lemma ExistExtendedConfs : forall confs ctx,
  exists ext_confs, ConfsExtendedByCtx ext_confs confs ctx.
Proof.
Admitted.

Lemma ExtendedRedIsRed : forall h h' st st' ctxs ctxs' e1 e1' A A' CC ctx,
  red CC (h , st  ++ [ ctxs            [[ e1 ]]_  A]) =
    Some (h', st' ++ [ ctxs'           [[ e1' ]]_ A']) ->
  red CC (h , st  ++ [(ctxs  ++ [ctx]) [[ e1 ]]_  A]) =
    Some (h', st' ++ [(ctxs' ++ [ctx]) [[ e1' ]]_ A']).
Proof.
Admitted.

Lemma ExtendedEvaluationIsEvaluation : forall confs h ctxs ctxs' ctx e e' A ext_confs hn e_A CC,
  JFIPartialEval h ([ ctxs  [[ e  ]]_ A  ]) confs hn
                    [ ctxs' [[ e' ]]_ e_A] CC ->
  ConfsExtendedByCtx ext_confs confs ctx ->
  JFIPartialEval h ([ (ctxs  ++ [ctx]) [[ e  ]]_ A  ]) ext_confs hn
                    [ (ctxs' ++ [ctx]) [[ e' ]]_ e_A] CC.
Proof.
Admitted.

(* ======================= Let and Try evaluation ======================= *)

Lemma ExistsNormalLetEval : forall h e1 e1_confs hn e1_res class x e2 CC,
  JFIPartialEval h  [ [] [[ e1 ]]_ None ] e1_confs
                 hn [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ None] CC ->
  exists let_e1_confs,
  JFIPartialEval h  [ [] [[ JFLet class x e1 e2 ]]_ None ] let_e1_confs
                 hn [ [] [[ substExpr (JFVar x) e1_res e2 ]]_ None] CC.
Proof.
  intros h e1 e1_confs hn e1_res class x e2 CC.
  intros e1_eval.
  destruct (ExistExtendedConfs e1_confs (JFCtxLet class x __ e2))
    as (e1_ext_confs & e1_ext_extended).
  set (letin := (h, [ [] [[ JFLet class x e1 e2 ]]_ None ])).
  set (letgo := (hn, [ [JFCtxLet class x __ e2] [[ JFVal1 (JFVLoc e1_res) ]]_ None])).
  exists (letin::(e1_ext_confs ++ [letgo])).
  simpl.
  split; try split; try trivial.
  apply EvaluationJoin with (h' := hn) (st' := snd letgo).
  + now apply ExtendedEvaluationIsEvaluation with
      (ctxs := []) (ctxs' := []) (confs := e1_confs).
  + now simpl.
Qed.

Lemma ExistsExLetEval : forall h e1 e1_confs hn e1_res ex class x e2 CC,
  JFIPartialEval h  [ [] [[ e1 ]]_ None ] e1_confs
                 hn [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some ex)] CC ->
  exists let_e1_confs,
  JFIPartialEval h  [ [] [[ JFLet class x e1 e2 ]]_ None ] let_e1_confs
                 hn [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some ex)] CC.
Proof.
  intros h e1 e1_confs hn e1_res ex class x e2 CC.
  intros e1_eval.
  destruct (ExistExtendedConfs e1_confs (JFCtxLet class x __ e2))
    as (e1_ext_confs & e1_ext_extended).
  set (letin := (h, [ [] [[ JFLet class x e1 e2 ]]_ None ])).
  set (letgo := (hn, [ [JFCtxLet class x __ e2] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some ex)])).
  exists (letin::(e1_ext_confs ++ [letgo])).
  simpl.
  split; try split; try trivial.
  apply EvaluationJoin with (h' := hn) (st' := snd letgo).
  + now apply ExtendedEvaluationIsEvaluation with
      (ctxs := []) (ctxs' := []) (confs := e1_confs).
  + now simpl.
Qed.

Lemma ExistsNormalTryEval : forall h e1 e1_confs hn e1_res mu catch_ex x e2 CC,
  JFIPartialEval h  [ [] [[ e1 ]]_ None ] e1_confs
                 hn [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ None] CC ->
  exists try_e1_confs,
  JFIPartialEval h  [ [] [[ JFTry e1 mu catch_ex x e2 ]]_ None ] try_e1_confs
                 hn [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ None] CC.
Proof.
  intros h e1 e1_confs hn e1_res mu catch_ex x e2 CC.
  intros e1_eval.
  destruct (ExistExtendedConfs e1_confs (JFCtxTry __ mu catch_ex x e2))
    as (e1_ext_confs & e1_ext_extended).
  set (tryin := (h, [ [] [[ JFTry e1 mu catch_ex x e2 ]]_ None ])).
  set (trygo := (hn, [ [JFCtxTry __ mu catch_ex x e2] [[ JFVal1 (JFVLoc e1_res) ]]_ None])).
  exists (tryin::(e1_ext_confs ++ [trygo])).
  simpl.
  split; try split; try trivial.
  apply EvaluationJoin with (h' := hn) (st' := snd trygo).
  + now apply ExtendedEvaluationIsEvaluation with
      (ctxs := []) (ctxs' := []) (confs := e1_confs).
  + now simpl.
Qed.

Lemma ExistsExTryEval : forall h e1 e1_confs hn e1_res mu catch_ex ex x e2 CC,
  JFIPartialEval h  [ [] [[ e1 ]]_ None ] e1_confs
                 hn [ [] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some ex)] CC ->
  exists try_e1_confs,
  JFIPartialEval h  [ [] [[ JFTry e1 mu catch_ex x e2 ]]_ None ] try_e1_confs
                 hn [ [JFCtxTry __ mu catch_ex x e2] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some ex)] CC.
Proof.
  intros h e1 e1_confs hn e1_res mu catch_ex ex x e2 CC.
  intros e1_eval.
  destruct (ExistExtendedConfs e1_confs (JFCtxTry __ mu catch_ex x e2))
    as (e1_ext_confs & e1_ext_extended).
  set (tryin := (h, [ [] [[ JFTry e1 mu catch_ex x e2 ]]_ None ])).
  set (trygo := (hn, [ [] [[ e2 ]]_ None])).
  exists (tryin::e1_ext_confs).
  simpl.
  split; try split; try trivial.
  now apply ExtendedEvaluationIsEvaluation with
      (ctxs := []) (ctxs' := []) (confs := e1_confs).
Qed.

Theorem LetEvaluationNormal : forall h h' hn class x v e1 e2 e1_confs e2_confs e1_res e2_res A env CC,
   JFIEvalInEnv h e1 e1_confs h' None e1_res env CC ->
   JFIEvalInEnv h' (JFIExprSubstituteVar x v e2) e2_confs hn A e2_res (StrMap.add v e1_res env) CC ->
   exists confs, JFIEvalInEnv h (JFLet class x e1 e2) confs hn A e2_res env CC.
Proof.
  intros h h' hn class x v e1 e2 e1_confs e2_confs e1_res e2_res A env CC.
  intros e1_eval e2_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsNormalLetEval with (x := x) (class := class) (e2 := e2_in_env) in e1_eval
    as (let_e1_confs & e1_let_eval).
  exists (let_e1_confs ++ e2_confs).
  unfold JFIEvalInEnv, JFIEval in  e2_eval.
  rewrite <- RemoveVarFromEnv in e2_eval.
  rewrite <- SubstExprEqExprSubstituteVal in e2_eval.
  now apply EvaluationJoin with (h' := h')
    (st' := [ [] [[ substExpr (JFVar x) e1_res e2_in_env ]]_ None]).
Qed.

Theorem LetEvaluationEx : forall h hn class x e1 e2 e1_confs e1_res ex env CC,
   JFIEvalInEnv h e1 e1_confs hn (Some ex) e1_res env CC ->
   exists confs, JFIEvalInEnv h (JFLet class x e1 e2) confs hn (Some ex) e1_res env CC.
Proof.
  intros h hn class x e1 e2 e1_confs e1_res ex env CC.
  intros e1_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsExLetEval with (x := x) (class := class) (e2 := e2_in_env) in e1_eval.
  destruct e1_eval as (let_e1_confs & e1_let_eval).
  now exists (let_e1_confs).
Qed.

Theorem TryEvaluationNormal : forall h hn mu catch_A x e1 e2 e1_confs e1_res env CC,
   (JFIEvalInEnv h e1 e1_confs hn None e1_res env CC) ->
   (exists confs, JFIEvalInEnv h (JFTry e1 mu catch_A x e2) confs hn None e1_res env CC).
Proof.
  intros h hn mu catch_A x e1 e2 e1_confs e1_res env CC.
  intros e1_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsNormalTryEval with (x := x) (mu := mu)
    (catch_ex := catch_A) (e2 := e2_in_env) in e1_eval.
  destruct e1_eval as (try_e1_confs & try_e1_eval).
  now exists (try_e1_confs).
Qed.

Theorem TryEvaluationExPass : forall h hn mu e1_A catch_A x e1 e2 e1_confs e1_res env CC,
   ~Is_true (subtype_bool CC (JFClass e1_A) (JFClass catch_A)) ->
   JFIEvalInEnv h e1 e1_confs hn (Some e1_A) e1_res env CC ->
   exists confs, JFIEvalInEnv h (JFTry e1 mu catch_A x e2) confs hn (Some e1_A) e1_res env CC.
Proof.
  intros h hn mu e1_A catch_A x e1 e2 e1_confs e1_res env CC.
  intros not_subtype e1_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsExTryEval with (x := x) (mu := mu)
    (catch_ex := catch_A) (e2 := e2_in_env) in e1_eval.
  destruct e1_eval as (try_e1_confs & try_e1_eval).
  set (trygo := (hn, [ [JFCtxTry __ mu catch_A x e2_in_env] [[ JFVal1 (JFVLoc e1_res)]]_ Some e1_A ])).
  exists (try_e1_confs ++ [trygo]).
  apply EvaluationJoin with (h' := hn) (st' := snd trygo); try trivial.
  simpl.
  split; try split; try trivial.
  unfold subtype_bool in not_subtype.
  destruct (subtype_class_bool CC e1_A catch_A); try easy.
  exfalso.
  now apply not_subtype.
Qed.

Theorem TryEvaluationExCatch : forall h h' hn mu e1_A e2_A catch_A x v e1 e2 e1_confs e2_confs e1_res e2_res env CC,
   Is_true (subtype_bool CC (JFClass e1_A) (JFClass catch_A)) ->
   JFIEvalInEnv h e1 e1_confs h' (Some e1_A) e1_res env CC ->
   JFIEvalInEnv h' (JFIExprSubstituteVar x v e2) e2_confs hn e2_A e2_res (StrMap.add v e1_res env) CC ->
   exists confs, JFIEvalInEnv h (JFTry e1 mu catch_A x e2) confs hn e2_A e2_res env CC.
Proof.
  intros h h' hn mu e1_A e2_A catch_A x v e1 e2 e1_confs e2_confs e1_res e2_res env CC.
  intros is_subtype e1_eval e2_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsExTryEval with (x := x) (mu := mu)
    (catch_ex := catch_A) (e2 := e2_in_env) in e1_eval.
  unfold JFIEvalInEnv, JFIEval in e2_eval.
  rewrite <- RemoveVarFromEnv in e2_eval.
  rewrite <- SubstExprEqExprSubstituteVal in e2_eval.
  destruct e1_eval as (try_e1_confs & try_e1_eval).
  set (trygo1 := (h', [ [JFCtxTry __ mu catch_A x e2_in_env] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some e1_A)])).
  set (trygo2 := (h', [ [] [[ substExpr (JFVar x) e1_res e2_in_env ]]_ None])).
  exists ((try_e1_confs ++ [trygo1]) ++ e2_confs).
  apply EvaluationJoin with (h' := h') (st' := snd trygo2); try easy.

  apply EvaluationJoin with (h' := h')
    (st' := snd trygo1); try easy.
  split; try split; trivial.
  unfold trygo1, snd, red.
  now destruct (subtype_bool CC (JFClass e1_A) (JFClass catch_A)).
Qed.
