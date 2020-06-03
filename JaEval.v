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
Require Import JaIrisPermutation.
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

(* ======================= Evaluation on extended heap ======================= *)
Fixpoint ValsPermuted vs vs' pi :=
  match (vs, vs') with
  | ([], []) => True
  | (JFVLoc v::vs, JFVLoc v'::vs') => PiMapsTo v v' pi /\ ValsPermuted vs vs' pi
  | _ => False
  end.

Fixpoint ExprsPermuted e e' pi :=
  match (e, e') with
  | (JFNew _ _ vs, JFNew _ _ vs') =>
      ValsPermuted vs vs' pi
  | (JFLet cn x e1 e2, JFLet cn' x' e1' e2') =>
      cn = cn' /\ x = x' /\
      ExprsPermuted e1 e1' pi /\ ExprsPermuted e2 e2' pi
  | (JFIf (JFVLoc v1) (JFVLoc v2) e1 e2, JFIf (JFVLoc v1') (JFVLoc v2') e1' e2') =>
      ExprsPermuted e1 e1' pi /\ ExprsPermuted e2 e2' pi /\
      PiMapsTo v1 v1' pi /\ PiMapsTo v2 v2' pi
  | (JFInvoke (JFVLoc v1) m vs, JFInvoke (JFVLoc v1') m' vs') =>
      PiMapsTo v1 v1' pi /\ ValsPermuted vs vs' pi /\ m = m'
  | (JFAssign ((JFVLoc v1), _) (JFVLoc v2), JFAssign ((JFVLoc v1'), _) (JFVLoc v2')) =>
      PiMapsTo v1 v1' pi /\ PiMapsTo v2 v2' pi
  | (JFVal1 (JFVLoc v1), JFVal1 (JFVLoc v1')) =>
      PiMapsTo v1 v1' pi
  | (JFVal2 ((JFVLoc v1), _), JFVal2 ((JFVLoc v1'), _)) =>
      PiMapsTo v1 v1' pi
  | (JFThrow (JFVLoc v1), JFThrow (JFVLoc v1')) =>
      PiMapsTo v1 v1' pi
  | (JFTry e1 _ _ _ e2, JFTry e1' _ _ _ e2') =>
      ExprsPermuted e1 e1' pi /\ ExprsPermuted e2 e2' pi
  | _ => False
  end.

Definition CtxPermuted ctx ctx' pi :=
  match (ctx, ctx') with
  | (JFCtxLet cn x _ e2, JFCtxLet cn' x' _ e2') => cn = cn' /\ x = x' /\ ExprsPermuted e2 e2' pi
  | (JFCtxTry _ _ cn x e2, JFCtxTry _ _ cn' x' e2') => cn = cn' /\ x = x' /\ ExprsPermuted e2 e2' pi
  | _ => False
  end.

Fixpoint CtxsPermuted ctxs ctxs' pi :=
  match (ctxs, ctxs') with
  | ([], []) => True
  | (ctx::ctxs, ctx'::ctxs') => CtxPermuted ctx ctx' pi /\ CtxsPermuted ctxs ctxs' pi
  | _ => False
  end.

Definition FramesPermuted f f' pi :=
  match (f, f') with
  | (MkFrame ctxs e A, MkFrame ctxs' e' A') =>
      ExprsPermuted e e' pi /\ CtxsPermuted ctxs ctxs' pi /\ A = A'
  end.

Fixpoint StacksPermuted st st' pi :=
  match (st, st') with
  | ([], []) => True
  | (f::st, f'::st') => FramesPermuted f f' pi /\ StacksPermuted st st' pi
  | _ => False
  end.

Definition PermutationSubset (pi pi' : HeapPermutation) :=
  forall l1 l2, PiMapsTo l1 l2 pi -> PiMapsTo l1 l2 pi'.

Lemma PermutationSubsetTrans : forall pi1 pi2 pi3,
  PermutationSubset pi1 pi2 ->
  PermutationSubset pi2 pi3 ->
  PermutationSubset pi1 pi3.
Proof.
  intros pi1 pi2 pi3 pi1_pi2 pi2_pi3 x l pi1_x_l.
  now apply pi2_pi3, pi1_pi2.
Qed.

Lemma PiMapsToEqIff : forall l1 l2 l1' l2' pi,
  Bijection pi ->
  PiMapsTo l1 l1' pi ->
  PiMapsTo l2 l2' pi ->
  (l1 = l2 <-> l1' = l2').
Proof.
  intros l1 l2 l1' l2' pi bijection pi_l1 pi_l2.
  split.
  + intros l_eq.
    unfold PiMapsTo in *.
    destruct l1, l2, l1', l2'; try easy.
    injection l_eq as n_eq.
    rewrite <-n_eq in pi_l2.
    assert (n1_eq := MapsToEq (fst pi) n n1 n2 pi_l1 pi_l2).
    now rewrite n1_eq.
  + intros l_eq.
    unfold PiMapsTo in *.
    destruct l1, l2, l1', l2'; try easy.
    apply bijection in pi_l1.
    apply bijection in pi_l2.
    injection l_eq as n1_eq.
    rewrite <-n1_eq in pi_l2.
    assert (n_eq := MapsToEq (snd pi) n1 n n0 pi_l1 pi_l2).
    now rewrite n_eq.
Qed.

Lemma ExistsPermutedResult : forall res A stn_ext pi',
  StacksPermuted [ [] [[JFVal1 (JFVLoc res) ]]_ A] stn_ext pi' ->
  exists res', PiMapsTo res res' pi' /\
       stn_ext = [ [] [[JFVal1 (JFVLoc res') ]]_ A].
Proof.
  intros res A stn_ext pi'.
  intros pi_st.
  unfold StacksPermuted in pi_st.
  destruct stn_ext; try destruct pi_st.
  destruct stn_ext; try destruct H0.
  unfold FramesPermuted in H.
  destruct f.
  destruct H as (pi_val & pi_ctxs & A_eq).
  simpl in pi_ctxs.
  destruct Ctx; try destruct pi_ctxs.
  unfold ExprsPermuted in pi_val.
  destruct E; try destruct pi_val.
  destruct v; try destruct pi_val.
  exists l.
  now rewrite A_eq.
Qed.

Lemma PermutationPreservesClassName : forall h0 h0' h0_perm h0_ext n n_perm C pi,
  PiMapsTo (JFLoc n) (JFLoc n_perm) pi ->
  HeapsPermuted h0 h0_perm pi ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  getClassName h0 n = Some C ->
  getClassName h0_ext n_perm = Some C.
Proof.
  intros h0 h0' h0_perm h0_ext n n_perm C pi.
  intros pi_n pi_h union class_name.
  unfold getClassName in *.
  assert (exists o, Heap.find n h0 = Some o).
    destruct (Heap.find n h0); try discriminate class_name.
    now exists o.
  destruct H as (o & n_o_h).
  rewrite n_o_h in class_name.
  destruct pi_h as (_ & locs_fst & _ & objs).
  unfold PiMapsTo in pi_n.
  assert (n_in_h : Heap.In n h0).
    apply HeapFacts.elements_in_iff.
    exists o.
    now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
  destruct (locs_fst n n_in_h) as (n_perm' & n_nperm'_pi & n_perm'_in_h_perm).
  rewrite <-(MapsToEq (fst pi) n n_perm n_perm') in *; trivial.
  apply HeapFacts.elements_in_iff in n_perm'_in_h_perm.
  destruct n_perm'_in_h_perm as (o' & n'_o'_h').
  apply HeapFacts.elements_mapsto_iff in n'_o'_h'.

  apply HeapFacts.find_mapsto_iff in n_o_h.
  destruct o as (o & cn), o' as (o' & cn').
  injection class_name as C_eq.
  destruct (objs n n_perm o cn o' cn') as (cn_eq & _); trivial.

  apply HeapFacts.find_mapsto_iff in n_o_h.
  assert (subheap : JFISubheap h0_perm h0_ext). apply union.
  assert (n'_o'_h_ext := subheap n_perm (o', cn') n'_o'_h').
  apply HeapFacts.find_mapsto_iff in n'_o'_h_ext.
  now rewrite n'_o'_h_ext, <-cn_eq, C_eq.
Qed.

Lemma ExistsPermutedExpr : forall e pi,
  exists e', ExprsPermuted e e' pi.
Proof.
Admitted.

Lemma PermutationPreservesSubstExpr : forall e e' pi f l l' e_body e_body',
  ExprsPermuted e_body e_body' pi ->
  ExprsPermuted e e' pi ->
  PiMapsTo l l' pi ->
  substExpr f l e_body = e ->
  substExpr f l' e_body' = e'.
Proof.
Admitted.

Lemma SubstPermutedExpr : forall f l l' e e' pi,
  ExprsPermuted e e' pi ->
  PiMapsTo l l' pi ->
  ExprsPermuted (substExpr f l e) (substExpr f l' e') pi.
Proof.
Admitted.

Lemma PermutationPreservesSubstList : forall fs vs vs',
  (forall f, In f fs -> f <> JFThis) ->
  length fs = length vs ->
  length vs = length vs' -> forall e_body e_body' n n' e pi,
  ValsPermuted vs vs' pi ->
  ExprsPermuted e_body e_body' pi ->
  PiMapsTo (JFLoc n) (JFLoc n') pi ->
  substList fs vs  (substExpr JFThis (JFLoc n) e_body) = Some e ->
  exists e',
  ExprsPermuted e e' pi /\
  substList fs vs' (substExpr JFThis (JFLoc n') e_body') = Some e'.
Proof.
  intros fs vs vs' fs_not_this fs_length_eq vs_length_eq.
  set (_fs := fs).
  replace fs with _fs in fs_not_this; try now unfold _fs.
  set (_vs := vs).
  set (_vs' := vs').
  replace _fs  with (fst (split (combine fs (combine vs vs')))) in *.
  replace _vs  with (fst (split (snd (split (combine fs (combine vs vs')))))).
  replace _vs' with (snd (split (snd (split (combine fs (combine vs vs')))))).
  clear fs_length_eq vs_length_eq _fs _vs _vs'.
  induction (combine fs (combine vs vs')); clear fs vs vs'.
  + intros e_body e_body' n n' e pi.
    intros pi_vs pi_body pi_n subst.
    simpl in *.
         destruct (ExistsPermutedExpr e pi) as (e' & pi_e).
    exists e'.
    split; trivial.
    unfold substList in *.
    injection subst as subst.
    apply PermutationPreservesSubstExpr
      with (e' := e') (e_body' := e_body') (l' := (JFLoc n')) (pi := pi) in subst; trivial.
    now rewrite subst.
  + intros e_body e_body' n n' e pi.
    intros pi_vs pi_body pi_n subst.
    destruct a as (f & (v & v')).
    simpl in *.
    destruct (split l) as (fs & vs_vs').
    unfold fst, snd in *.
    simpl in *.
    unfold fst, snd in *.
    destruct (split vs_vs') as (vs & vs').
    destruct v; try discriminate subst.
    destruct v'; try destruct pi_vs.
    assert (next_f_not_this : (forall f : JFRef, In f fs -> f <> JFThis)).
      intros f0 f0_in_fs. apply (fs_not_this f0). now apply or_intror.
    rewrite SubstExprComm in subst; [ | now apply fs_not_this, or_introl].
    destruct (IHl next_f_not_this (substExpr f l0 e_body) (substExpr f l1 e_body') n n' e pi)
      as (e' & pi_e & subst'); trivial.
    now apply SubstPermutedExpr.
    rewrite SubstExprComm in subst'; [ | now apply neq_symmetry, fs_not_this, or_introl].
    now exists e'.
  + rewrite combine_split; trivial.
    ++ unfold snd.
       rewrite combine_split; trivial.
    ++ rewrite combine_length.
       rewrite <-vs_length_eq, <-fs_length_eq.
       now rewrite min_r.
  + rewrite combine_split; trivial.
    ++ unfold snd.
       rewrite combine_split; trivial.
    ++ rewrite combine_length.
       rewrite <-vs_length_eq, <-fs_length_eq.
       now rewrite min_r.
  + rewrite combine_split; trivial.
    rewrite combine_length.
    rewrite <-vs_length_eq, <-fs_length_eq.
    now rewrite min_r.
Qed.

Lemma PermutedValsLengthEq: forall vs vs' pi,
  ValsPermuted vs vs' pi ->
  length vs = length vs'.
Proof.
Admitted.

Lemma ExistsPermutedBody : forall CC h0 h0' h0_ext h0_perm n n_perm m vs vs_perm ctxs ctxs_perm st st_perm h' st' pi,
  HeapsPermuted h0 h0_perm pi ->
  PiMapsTo (JFLoc n) (JFLoc n_perm) pi ->
  ValsPermuted vs vs_perm pi ->
  CtxsPermuted ctxs ctxs_perm pi ->
  StacksPermuted st st_perm pi ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  getInvokeBody CC (getClassName h0 n) n m vs h0 ctxs st = Some (h', st') ->
  h' = h0 /\
  exists st'_perm,
    StacksPermuted st' st'_perm pi  /\
    getInvokeBody CC (getClassName h0_ext n_perm) n_perm m vs_perm h0_ext ctxs_perm st_perm = Some (h0_ext, st'_perm).
Proof.
  intros CC h0 h0' h0_ext h0_perm n n_perm m vs vs_perm ctxs ctxs_perm st st_perm h' st' pi.
  intros pi_h pi_n pi_vs pi_ctxs pi_st union invoke.
  unfold getInvokeBody in invoke.
  assert (exists C, getClassName h0 n = Some C).
    destruct (getClassName h0 n); try discriminate invoke.
    now exists j.
  destruct H as (C & class_name).
  rewrite class_name in invoke.
  assert (exists md, methodLookup CC C m = Some md).
    destruct (methodLookup CC C m); try discriminate invoke.
    now exists j.
  destruct H as (md & method_lookup).
  rewrite method_lookup in invoke.
  assert (exists Es, substList (map JFVar (params_of_md md)) vs
             (substExpr JFThis (JFLoc n) (body_of_md md)) = Some Es).
    destruct (substList (map JFVar (params_of_md md)) vs
             (substExpr JFThis (JFLoc n) (body_of_md md))); try discriminate invoke.
    now exists j.
  destruct H as (Es, subst_method).
  rewrite subst_method in invoke.
  injection invoke.
  intros st_eq h_eq.
  symmetry in h_eq.
  split; trivial.
  destruct st'; try discriminate st_eq.
  destruct st'; try discriminate st_eq.
  injection st_eq; clear st_eq.
  intros st_eq invoke_eq es_eq.
  rewrite <-st_eq, <-es_eq, <-invoke_eq.
  assert (fs_not_this : forall f, In f (map JFVar (params_of_md md)) -> f <> JFThis).
    intros f1 f1_in_map f1_this.
    apply in_map_iff in f1_in_map.
    destruct f1_in_map as (x & f1_var & _).
    now rewrite f1_this in f1_var.
  assert (fs_length_eq : length (map JFVar (params_of_md md)) = length vs).
    rewrite map_length.
    admit. (* TODO params length *)
  assert (vs_length_eq : length vs = length vs_perm).
    now apply PermutedValsLengthEq with (pi := pi).
  assert (pi_body : ExprsPermuted (body_of_md md) (body_of_md md) pi).
    admit. (* TODO body permuted -- no locs in it *)
  destruct (PermutationPreservesSubstList (map JFVar (params_of_md md)) vs vs_perm fs_not_this fs_length_eq vs_length_eq (body_of_md md) (body_of_md md) n n_perm Es pi)
    as (Es_perm & pi_es & subst_perm); trivial.
  exists (([] [[ Es_perm ]]_ None)
        :: (ctxs_perm [[JFInvoke (JFVLoc (JFLoc n_perm)) m vs_perm
            ]]_ None) :: st_perm).
  split; try easy.
  apply PermutationPreservesClassName
    with (h0' := h0') (h0_perm := h0_perm) (h0_ext := h0_ext)
         (n_perm := n_perm) (pi := pi) in class_name; trivial.
  unfold getInvokeBody.
  now rewrite class_name, method_lookup, subst_perm.
Admitted.

Lemma ReductionPreservesHeapPermutation : forall h0 h0_perm h0' h0_ext st h' st' st_perm pi CC,
  PiMapsTo (JFLoc NPE_object_loc) (JFLoc NPE_object_loc) pi ->
  StacksPermuted st st_perm pi ->
  HeapsPermuted h0 h0_perm pi ->
  red CC (h0, st) = Some (h', st') ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  exists h'_perm h'_ext st'_perm pi',
    PermutationSubset pi pi' /\
    HeapsPermuted h' h'_perm pi' /\
    StacksPermuted st' st'_perm pi' /\
    JFIDisjointUnion h'_perm h0' h'_ext /\
    red CC (h0_ext, st_perm) = Some (h'_ext, st'_perm).
Proof.
  intros h0 h0_perm h0' h0_ext st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  destruct st; try discriminate red_st.
  destruct f, E; try discriminate red_st.
  + admit.
  + simpl in pi_st.
    destruct st_perm; [ destruct pi_st |].
    destruct pi_st as (pi_f & pi_st).
    unfold FramesPermuted in pi_f.
    destruct f.
    destruct pi_f as (pi_let & pi_ctx & A_eq).
    simpl in pi_let.
    destruct E; try now destruct pi_let.
    destruct pi_let as (cn_eq & x_eq & pi_e1 & pi_e2).
    destruct A.
      destruct Ctx; try destruct j0; try discriminate red_st.
    assert (Some (h0, Ctx _[ JFCtxLet cn x __ E2 _[[_ E1 _]]_ None ]_ :: st)
              = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H.
    intros st_eq h_eq.
    exists h0_perm, h0_ext, (Ctx0 _[ JFCtxLet cn x __ E4 _[[_ E3  _]]_ None]_ :: st_perm), pi.
    rewrite <-st_eq, <-h_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    rewrite <-A_eq, cn_eq, x_eq.
    now destruct Ctx0; try destruct j.
  + simpl in pi_st.
    destruct st_perm; [ destruct pi_st |].
    destruct pi_st as (pi_f & pi_st).
    unfold FramesPermuted in pi_f.
    destruct f.
    destruct pi_f as (pi_if & pi_ctx & A_eq).
    simpl in pi_if.
    destruct v1, v2, E; try destruct v1, v2; try now destruct pi_if.
    destruct pi_if as (pi_e1 & pi_e2 & pi_l & pi_l0).
    destruct A.
      destruct Ctx; try destruct j0; try discriminate red_st.
    destruct (Classical_Prop.classic (l = l0)) as [l_eq | l_neq].
   ++ Loc_dec_eq l l0 l_eq.
      assert (l1_eq : l1 = l2).
        now apply (PiMapsToEqIff l l0 l1 l2 pi (proj1 pi_h0)).
      assert (Some (h0, (Ctx [[ E1 ]]_ None) :: st) = Some (h', st')).
        now destruct Ctx; try destruct j.
      injection H.
      intros st_eq h_eq.
      exists h0_perm, h0_ext, (Ctx0[[ E3 ]]_ None :: st_perm), pi.
      rewrite <-st_eq, <-h_eq, <-A_eq.
      split; [ | split; [ | split; [| split]]]; try easy.
      simpl.
      Loc_dec_eq l1 l2 l1_eq.
      now destruct Ctx0; try destruct j.
   ++ Loc_dec_neq l l0 l_neq.
      assert (l1_neq : l1 <> l2).
        intros l1_eq. apply l_neq.
        now apply (PiMapsToEqIff l l0 l1 l2 pi (proj1 pi_h0)).
      assert (Some (h0, (Ctx [[ E2 ]]_ None) :: st) = Some (h', st')).
        now destruct Ctx; try destruct j.
      injection H.
      intros st_eq h_eq.
      exists h0_perm, h0_ext, (Ctx0[[ E4 ]]_ None :: st_perm), pi.
      rewrite <-st_eq, <-h_eq, <-A_eq.
      split; [ | split; [ | split; [| split]]]; try easy.
      simpl.
      Loc_dec_neq l1 l2 l1_neq.
      now destruct Ctx0; try destruct j.
  + simpl in pi_st.
    destruct st_perm; [ destruct pi_st |].
    destruct pi_st as (pi_f & pi_st).
    unfold FramesPermuted in pi_f.
    destruct f.
    destruct pi_f as (pi_invoke & pi_ctx & A_eq).
    simpl in pi_invoke.
    destruct v, E; try destruct v; try now destruct pi_invoke.
    destruct pi_invoke as (pi_l & pi_vs & m_eq).
    destruct A.
      destruct Ctx, l; try destruct j0; try discriminate red_st.
    destruct l.
    ++ assert (Some (h0, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st) = Some (h', st')).
         now destruct Ctx; try destruct j.
       assert (l0_eq : l0 = null).
         now destruct l0; try destruct pi_l.
       injection H; intros h_eq st_eq.
       exists h0_perm, h0_ext, (Ctx0 [[ JFVal1 NPE_val ]]_ NPE_mode :: st_perm), pi.
       rewrite <-st_eq, <-h_eq, <-A_eq, l0_eq.
       split; [ | split; [ | split; [| split]]]; try easy.
       now destruct Ctx0; try destruct j.
    ++ assert (getInvokeBody CC (getClassName h0 n) n m vs h0 Ctx st = Some (h', st')).
         now destruct Ctx; try destruct j.
       destruct l0; try now destruct pi_l.
       assert (ASdf := ExistsPermutedBody).
       destruct (ExistsPermutedBody CC h0 h0' h0_ext h0_perm n n0 m vs vs0 Ctx Ctx0 st st_perm h' st' pi)
         as (h_eq & st'_perm & pi_st' & invoke); trivial.
       exists h0_perm, h0_ext, st'_perm, pi.
       rewrite h_eq, <-A_eq, <-m_eq.
       split; [ | split; [ | split; [| split]]]; try easy.
       now destruct Ctx0; try destruct j; simpl.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
Admitted.

Lemma PermutationEvalAux1 : forall h st confs hn stn CC,
  match red CC (h, st) with
  | Some (h, st) => JFIPartialEval h st confs hn stn CC
  | None => False
  end ->
  exists h' st', red CC (h, st) = Some (h', st') /\
    JFIPartialEval h' st' confs hn stn CC.
Proof.
  intros.
  destruct (red CC (h, st)); try destruct H.
  destruct p.
  now exists h0, f.
Qed.

Lemma PermutationEvalAux2 : forall h0_ext st_ext h'_ext st'_perm confs_ext hn_ext stn_ext CC,
  red CC (h0_ext, st_ext) = Some (h'_ext, st'_perm) ->
  JFIPartialEval h'_ext st'_perm confs_ext hn_ext stn_ext CC ->
  match red CC (h0_ext, st_ext) with
  | Some (h1, st0) =>
      JFIPartialEval h1 st0 confs_ext hn_ext stn_ext CC
  | None => False
  end.
Proof.
  intros.
  now rewrite H.
Qed.

Lemma PartialEvaluationOnExtendedHeap : forall confs h0 h0_perm h0' h0_ext st st_ext hn stn pi CC,
  PiMapsTo (JFLoc NPE_object_loc) (JFLoc NPE_object_loc) pi ->
  StacksPermuted st st_ext pi ->
  HeapsPermuted h0 h0_perm pi ->
  JFIPartialEval h0 st confs hn stn CC ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  exists confs_ext hn_perm hn_ext stn_ext pi',
    PermutationSubset pi pi' /\
    HeapsPermuted hn hn_perm pi' /\
    StacksPermuted stn stn_ext pi' /\
    JFIDisjointUnion hn_perm h0' hn_ext /\ 
    JFIPartialEval h0_ext st_ext confs_ext hn_ext stn_ext CC.
Proof.
  intros confs.
  induction confs.
  + intros h0 h0_perm h0' h0_ext st st_ext hn stn pi CC.
    intros pi_npe pi_h pi_st eval union.
    unfold JFIPartialEval in eval.
    destruct eval as (h0_eq & st_eq).
    exists [], h0_perm, h0_ext, st_ext, pi.
    split; [ | split; [ | split; [ | split]]]; try easy.
    ++ now rewrite <-h0_eq.
    ++ now rewrite <-st_eq.
  + intros h0 h0_perm h0' h0_ext st st_ext hn stn pi CC.
    intros pi_npe pi_h pi_st eval union.
    unfold JFIPartialEval in eval.
    fold JFIPartialEval in eval.
    destruct a.
    destruct eval as (h_eq & st_eq & eval).
    apply PermutationEvalAux1 in eval as (h' & st' & red_is_some & eval).
    destruct (ReductionPreservesHeapPermutation h0 h0_perm h0' h0_ext st h' st' st_ext pi CC)
      as (h'_perm & h'_ext & st'_perm & pi' & pi_subset & pi'_h' & pi'_st' & union' & red_ext); trivial.
    destruct (IHconfs h' h'_perm h0' h'_ext st' st'_perm hn stn pi' CC)
      as (confs_ext & hn_perm & hn_ext & stn_ext & pin &
          pi'_subset & pin_hn & pin_stn & union_n & eval_rest); trivial.
      now apply pi_subset.
    exists ((h0_ext,st_ext)::confs_ext), hn_perm, hn_ext, stn_ext, pin.
    split; [ | split; [ | split; [ | split]]]; trivial.
    now apply PermutationSubsetTrans with (pi2 := pi').
    unfold JFIPartialEval; fold JFIPartialEval.
    split; [ | split]; trivial.
    now apply PermutationEvalAux2 with (h'_ext := h'_ext) (st'_perm := st'_perm).
Qed.

Theorem EvaluationOnExtendedHeap : forall h0 h0' h0_ext e confs hn res_ex res env CC,
   JFIEvalInEnv h0 e confs hn res_ex res env CC ->
   JFIDisjointUnion h0 h0' h0_ext ->
   exists confs_ext hn_perm hn_ext res_ext pi,
      HeapsPermuted hn hn_perm pi /\
      EnvsPermuted env env pi /\
      PiMapsTo res res_ext pi /\
      JFIDisjointUnion hn_perm h0' hn_ext /\ 
      JFIEvalInEnv h0_ext e confs_ext hn_ext res_ex res_ext env CC.
Proof.
  intros h0 h0' h0_ext e confs hn res_ex res env CC.
  intros eval union.
  unfold JFIEvalInEnv, JFIEval in eval.

  assert (pi : HeapPermutation). admit.
  assert (pi_env : EnvsPermuted env env pi). admit.
  assert (pi_h : HeapsPermuted h0 h0 pi). admit.
  assert (pi_st : StacksPermuted 
    [ [] [[ JFIExprSubstituteEnv env e ]]_ None]
    [ [] [[ JFIExprSubstituteEnv env e ]]_ None] pi). admit.
  assert (pi_npe : PiMapsTo (JFLoc NPE_object_loc) (JFLoc NPE_object_loc) pi). admit.

  destruct (PartialEvaluationOnExtendedHeap confs h0 h0 h0' h0_ext 
    [ [] [[JFIExprSubstituteEnv env e ]]_ None]
    [ [] [[JFIExprSubstituteEnv env e ]]_ None]
    hn [ [] [[ JFVal1 (JFVLoc res) ]]_ res_ex] pi CC)
    as (confs_ext & hn_perm & hn_ext & stn_ext & pi' &
       pi_subset & pi'_hn & pi'_stn & hn_union & ext_eval); trivial.

  destruct (ExistsPermutedResult res res_ex stn_ext pi')
    as (res_ext & pi_res & stn_eq); trivial.
  exists confs_ext, hn_perm, hn_ext, res_ext, pi'.
  split; [ | split; [ | split; [ | split]]]; try easy.
  + unfold EnvsPermuted.
    split; [ | split]; try easy.
    ++ apply (proj1 pi'_hn).
    ++ intros x l1 l2 x_l1_env x_l2_env.
       apply pi_subset.
       now apply ((proj2 (proj2 pi_env)) x).
  + unfold JFIEvalInEnv, JFIEval.
    now rewrite <-stn_eq.
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
