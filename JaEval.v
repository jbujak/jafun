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
    now apply PermutedValsLength with (pi := pi).
  assert (pi_body : ExprsPermuted (body_of_md md) (body_of_md md) pi).
    admit. (* TODO body permuted -- no locs in it *)
  destruct (PermutationPreservesSubstList (map JFVar (params_of_md md)) vs vs_perm fs_not_this fs_length_eq vs_length_eq (body_of_md md) (body_of_md md) n n_perm Es pi)
    as (Es_perm & pi_es & subst_perm); trivial.
  exists (([] [[ Es_perm ]]_ None)
        :: (ctxs_perm [[JFInvoke (JFVLoc (JFLoc n_perm)) m vs_perm
            ]]_ None) :: st_perm).
  split; try easy.
  apply PermutationPreservesClassName_to_remove
    with (h0' := h0') (h0_perm := h0_perm) (h0_ext := h0_ext)
         (n_perm := n_perm) (pi := pi) in class_name; trivial.
  unfold getInvokeBody.
  now rewrite class_name, method_lookup, subst_perm.
Admitted.

Lemma AllocOnExtendedHeap : forall h0 h0_perm h0' h0_ext pi CC cn locs locs_perm l0 hp,
  alloc_init CC h0 cn locs = Some (l0, hp) ->
  HeapsPermuted h0 h0_perm pi ->
  LocsPermuted locs locs_perm pi ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  exists pi' l0_perm hp_perm hp_ext,
    (PermutationSubset pi pi' /\
     HeapsPermuted hp hp_perm pi' /\
     PiMapsTo l0 l0_perm pi' /\
     JFIDisjointUnion hp_perm h0' hp_ext /\
     alloc_init CC h0_ext cn locs_perm = Some (l0_perm, hp_ext)).
Proof.
  intros h0 h0_perm h0' h0_ext pi CC cn locs locs_perm l0 hp.
  intros alloc pi_h pi_locs (union & disjoint).
  unfold alloc_init in *.
  destruct pi_h as (bijection & locs_fst & locs_snd & objs).
  destruct (flds CC (JFClass cn)) as [flds | ]; try discriminate alloc.
  unfold init_obj in *.
  assert (exists flds_locs, JaUtils.zip flds locs = Some flds_locs).
    destruct (JaUtils.zip flds locs); try now discriminate alloc.
    now exists l.
  destruct H as (flds_locs & zip_locs).
  destruct (ExistsPermutedZip flds locs locs_perm flds_locs pi)
    as (flds_locs_perm & zip_locs_perm & pi_zip); trivial.
  rewrite zip_locs in alloc.
  rewrite zip_locs_perm.
  injection alloc as l0_eq hp_eq.
  destruct l0 as [ | n0]; try discriminate l0_eq.
  injection l0_eq as n0_eq.
  set (n0_perm := newloc h0_ext).
  set (pi' := (NatMap.add n0 n0_perm (fst pi), NatMap.add n0_perm n0 (snd pi))).
  assert (pi_subset : PermutationSubset pi pi').
    apply ExtendPiSubset.
    rewrite <-n0_eq.
    admit. (* TODO newloc h0 not in pi *)
  assert (pi_obj := PermutedZipIsPermutedInit flds_locs flds_locs_perm cn
      (JFXIdMap.empty Loc) (JFXIdMap.empty Loc) pi pi_zip).
  apply ExtendObjPermutation with (pi' := pi') in pi_obj; trivial.
  exists pi', (JFLoc n0_perm),
    (Heap.add n0_perm (init_obj_aux (JFXIdMap.empty Loc) flds_locs_perm, cn) h0_perm),
    (Heap.add n0_perm (init_obj_aux (JFXIdMap.empty Loc) flds_locs_perm, cn) h0_ext).
  split; [ | split; [ | split; [ | split]]]; try easy.
  + rewrite <-hp_eq, n0_eq.
    simpl.
    apply ExtendPermutedHeaps; simpl; trivial.
    now apply ExtendHeapsPermutation with (pi := pi).
    now rewrite NatMapFacts.find_mapsto_iff, NatMapFacts.add_eq_o.
  + unfold PiMapsTo, pi', fst.
    now rewrite NatMapFacts.find_mapsto_iff, NatMapFacts.add_eq_o.
  + apply ExtendDisjointUnion; try easy.
    intros in_h0'.
    apply HeapFacts.elements_in_iff in in_h0' as (o0_perm & n0_o0).
    rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n0_o0.
    assert (disjoint_union : JFIDisjointUnion h0_perm h0' h0_ext); try easy.
    apply DisjointUnionSymmetry in disjoint_union.
    apply FindInUnion with (h2 := h0_perm) (h := h0_ext) in n0_o0; trivial.
    unfold n0_perm in n0_o0.
    apply newloc_new in n0_o0.
    now apply n0_o0.
Admitted.

Definition ExprReductionPreservesHeapPermutation (e : JFExpr) := forall h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC,
  PiMapsTo (JFLoc NPE_object_loc) (JFLoc NPE_object_loc) pi ->
  StacksPermuted ((Ctx [[ e ]]_ A) :: st) st_perm pi ->
  HeapsPermuted h0 h0_perm pi ->
  red CC (h0, (Ctx [[ e ]]_ A) :: st) = Some (h', st') ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  exists h'_perm h'_ext st'_perm pi',
    PermutationSubset pi pi' /\
    HeapsPermuted h' h'_perm pi' /\
    StacksPermuted st' st'_perm pi' /\
    JFIDisjointUnion h'_perm h0' h'_ext /\
    red CC (h0_ext, st_perm) = Some (h'_ext, st'_perm).

Lemma NewReductionPreservesHeapPermutation : forall mu cn vs,
   ExprReductionPreservesHeapPermutation (JFNew mu cn vs).
Proof.
  intros mu cn vs.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_new & pi_ctx & A_eq).
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  rewrite <-A_eq in *.
  destruct E; try (simpl in pi_new; now destruct pi_new).
  assert (exists locs, list_map_opt loc_of_val vs = Some locs).
    destruct (list_map_opt loc_of_val vs).
    now exists l.
    destruct Ctx; try destruct j; try destruct (alloc_init CC h0 cn l); discriminate red_st.
  destruct H as (locs & locs_of_vs).
  rewrite locs_of_vs in red_st.
  assert (exists l0 hp, alloc_init CC h0 cn locs = Some (l0, hp)).
    destruct alloc_init.
    destruct p. now exists l, h.
    destruct Ctx; try destruct j; discriminate red_st.
  destruct H as (l0 & hp & alloc_h0).
  rewrite alloc_h0 in *.
  assert (h' = hp /\ st' = ((Ctx [[JFVal1 (JFVLoc l0) ]]_ None) :: st)).
    destruct Ctx; try destruct j; now injection red_st.
  simpl in pi_new.
  destruct pi_new as (_ & cn_eq & vs_perm).
  destruct H as (h'_eq & st'_eq).
  rewrite h'_eq, st'_eq, <-cn_eq in *.
  apply LocOfValsPermutation with (vs_perm := vs0) (pi := pi) in locs_of_vs as (locs' & locs'_of_vs0 & locs_permuted); try easy.
  destruct (AllocOnExtendedHeap h0 h0_perm h0' h0_ext pi CC cn locs locs' l0 hp alloc_h0 pi_h0 locs_permuted union)
    as (pi' & l0_perm & hp_perm & hp_ext & pi_subset & pi_h_ext & pi_l0 & union_ext & alloc_h_ext).
  exists hp_perm, hp_ext, ((Ctx0 [[JFVal1 (JFVLoc l0_perm) ]]_ None) :: st_perm), pi'.
  apply ExtendCtxsPermutation with (pi' := pi') in pi_ctx; try easy.
  apply ExtendStacksPermutation with (pi' := pi') in pi_st; try easy.
  split; [ | split; [ | split; [ | split]]]; try easy.
  simpl.
  rewrite locs'_of_vs0.
  rewrite alloc_h_ext.
  now destruct Ctx0; try destruct j.
Qed.

Lemma LetReductionPreservesHeapPermutation : forall cn x e1 e2,
   ExprReductionPreservesHeapPermutation (JFLet cn x e1 e2).
Proof.
  intros cn x e1 e2.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
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
  assert (Some (h0, Ctx _[ JFCtxLet cn x __ e2 _[[_ e1 _]]_ None ]_ :: st) = Some (h', st')).
    now destruct Ctx; try destruct j.
  injection H.
  intros st_eq h_eq.
  exists h0_perm, h0_ext, (Ctx0 _[ JFCtxLet cn x __ E2 _[[_ E1  _]]_ None]_ :: st_perm), pi.
  rewrite <-st_eq, <-h_eq.
  split; [ | split; [ | split; [| split]]]; try easy.
  rewrite <-A_eq, cn_eq, x_eq.
  now destruct Ctx0; try destruct j.
Qed.

Lemma IfReductionPreservesHeapPermutation : forall v1 v2 e1 e2,
   ExprReductionPreservesHeapPermutation (JFIf v1 v2 e1 e2).
Proof.
  intros v1 v2 e1 e2.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_if & pi_ctx & A_eq).
  simpl in pi_if.
  destruct v1, v2, E; try destruct v1, v2; try now destruct pi_if;
    try now (destruct Ctx; try destruct j; discriminate red_st).
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  destruct (Classical_Prop.classic (l = l0)) as [l_eq | l_neq].
  + Loc_dec_eq l l0 l_eq.
    assert (l1_eq : l1 = l2).
      now apply (PiMapsToEqIff l l0 l1 l2 pi (proj1 pi_h0)).
    assert (Some (h0, (Ctx [[ e1 ]]_ None) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H.
    intros st_eq h_eq.
    exists h0_perm, h0_ext, (Ctx0[[ E1 ]]_ None :: st_perm), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    simpl.
    Loc_dec_eq l1 l2 l1_eq.
    now destruct Ctx0; try destruct j.
  + Loc_dec_neq l l0 l_neq.
    assert (l1_neq : l1 <> l2).
      intros l1_eq. apply l_neq.
      now apply (PiMapsToEqIff l l0 l1 l2 pi (proj1 pi_h0)).
    assert (Some (h0, (Ctx [[ e2 ]]_ None) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H.
    intros st_eq h_eq.
    exists h0_perm, h0_ext, (Ctx0[[ E2 ]]_ None :: st_perm), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    simpl.
    Loc_dec_neq l1 l2 l1_neq.
    now destruct Ctx0; try destruct j.
Qed.

Lemma InvokeReductionPreservesHeapPermutation : forall v m vs,
   ExprReductionPreservesHeapPermutation (JFInvoke v m vs).
Proof.
  intros v m vs.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_invoke & pi_ctx & A_eq).
  simpl in pi_invoke.
  destruct v, E; try destruct v; try now destruct pi_invoke;
    try now (destruct Ctx; try destruct j; discriminate red_st).
  destruct pi_invoke as (pi_l & pi_vs & m_eq).
  destruct A.
    destruct Ctx, l; try destruct j0; try discriminate red_st.
  destruct l.
  + assert (Some (h0, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    assert (l0_eq : l0 = null).
      now destruct l0; try destruct pi_l.
    injection H; intros h_eq st_eq.
    exists h0_perm, h0_ext, (Ctx0 [[ JFVal1 NPE_val ]]_ NPE_mode :: st_perm), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq, l0_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    now destruct Ctx0; try destruct j.
  + assert (getInvokeBody CC (getClassName h0 n) n m vs h0 Ctx st = Some (h', st')).
      now destruct Ctx; try destruct j.
    destruct l0; try now destruct pi_l.
    assert (asdf := ExistsPermutedBody).
    destruct (ExistsPermutedBody CC h0 h0' h0_ext h0_perm n n0 m vs vs0 Ctx Ctx0 st st_perm h' st' pi)
      as (h_eq & st'_perm & pi_st' & invoke); trivial.
    exists h0_perm, h0_ext, st'_perm, pi.
    rewrite h_eq, <-A_eq, <-m_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    now destruct Ctx0; try destruct j; simpl.
Qed.

Lemma AssignReductionPreservesHeapPermutation : forall vx v,
   ExprReductionPreservesHeapPermutation (JFAssign vx v ).
Proof.
  intros vx v.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_assign & pi_ctx & A_eq).
  simpl in pi_assign.
  destruct vx as (v1 & f).
  destruct E; try now destruct pi_assign.
  set (v' := v0); replace v0 with v' in *; try easy.
  destruct vx as (v1' & f').
  destruct pi_assign as (f_eq & pi_v1 & pi_v).
  destruct A.
    destruct Ctx, v, v1; try destruct j0;
    try destruct l; try destruct l0; try discriminate red_st.
  destruct v1 as [l1 | ]; try destruct l1.
  + assert (Some (h0, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st) = Some (h', st')).
      now destruct Ctx, v; try destruct j.
    injection H as h_eq st_eq.
    assert (v1_eq : v1' = JFnull).
      unfold ValPermuted in pi_v1.
      destruct v1'; try destruct pi_v1.
      unfold PiMapsTo in pi_v1.
      now destruct l.
    exists h0_perm, h0_ext, (Ctx0 [[ JFVal1 NPE_val ]]_ NPE_mode :: st_perm), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq, v1_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    destruct v, v'; try destruct pi_v.
    now destruct Ctx0; try destruct j.
    now destruct Ctx; try destruct j; try discriminate red_st.
  + destruct v; try (destruct Ctx; try destruct j; now discriminate red_st).
    assert (exists ro cid, Heap.find n h0 = Some (ro, cid)).
      destruct (Heap.find (elt:=Obj) n h0); try (destruct Ctx; try destruct j; now discriminate red_st).
      exists (fst o), (snd o).
      now destruct o.
    destruct H as (ro & cid & n_h_ro).
    rewrite n_h_ro in red_st.
    assert (Some (Heap.add n (JFXIdMap.add f l ro, cid) h0, (Ctx [[ JFVal1 (JFVLoc l) ]]_ None) :: st) =
        Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    destruct v1' as [l' |]; try destruct l' as [| n']; try now destruct pi_v1.
    destruct v' as [l' |]; try now destruct pi_v.
    assert (exists ro', Heap.find n' h0_perm = Some (ro', cid)).
      now apply ExistsInPermutedHeap with (n := n) (h := h0) (pi := pi) (ro := ro).
    destruct H as (ro' & n'_ro').
    set (h'_perm := Heap.add n' (JFXIdMap.add f l' ro', cid) h0_perm).
    assert (pi_h' : HeapsPermuted h' h'_perm pi).
      unfold h'_perm.
      rewrite <-h_eq.
      now apply ChangeFieldInPermutedHeaps.
    exists h'_perm, (Heap.add n' (JFXIdMap.add f' l' ro', cid) h0_ext), ((Ctx0 [[JFVal1 (JFVLoc l') ]]_ None) :: st_perm), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq.
    unfold h'_perm.
    split; [ | split; [ | split; [| split]]]; try easy.
    ++ now rewrite h_eq.
    ++ rewrite <-f_eq.
       apply ExtendDisjointUnion; trivial.
       intros n'_in_h0'.
       destruct union as (union & disjoint).
       apply (disjoint n').
       split; trivial.
       apply HeapFacts.elements_in_iff.
       exists (ro', cid).
       now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
    ++ apply FindInUnion with (h2 := h0') (h := h0_ext) in n'_ro'; trivial.
       unfold red.
       rewrite n'_ro'.
       now destruct Ctx0; try destruct j.
  + destruct Ctx; try destruct j; try discriminate red_st.
Qed.

Lemma Val1ReductionPreservesHeapPermutation : forall v,
   ExprReductionPreservesHeapPermutation (JFVal1 v).
Proof.
  intros v.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_val1 & pi_ctx & A_eq).
  simpl in pi_val1.
  destruct E; try now destruct pi_val1.
  destruct A.
  + destruct Ctx; [ | destruct j0].
    ++ destruct v, st; try destruct f; try destruct E, A; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct pi_ctx.
       destruct st_perm; try destruct f; try now destruct pi_st.
       simpl in pi_st.
       destruct pi_st as (pi_f & pi_st).
       destruct E, A; try now destruct pi_f.
       unfold FramesPermuted in pi_f.
       destruct pi_f as (pi_e & pi_ctx & _).
       destruct pi_e as (pi_v & pi_vs & m_eq).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-m_eq, <-h0_eq, <-st_eq, <-A_eq.
       now exists h0_perm, h0_ext, (Ctx0 [[JFVal1 (JFVLoc l') ]]_ Some j :: st_perm), pi.
    ++ destruct v; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct j0; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct pi_ctx as ((C_eq & x_eq & pi_e) & pi_ctxs).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-h0_eq, <-st_eq, <-A_eq.
       now exists h0_perm, h0_ext, (Ctx0 [[JFVal1 (JFVLoc l') ]]_ Some j :: st_perm), pi.
    ++ destruct v; try discriminate red_st.
       destruct Ctx0; try destruct j0; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       destruct pi_ctx as ((C_eq & x_eq & pi_e) & pi_ctxs).
       rewrite <-C_eq, <-x_eq, <-A_eq in *.
       replace h' with h0;
         [ | destruct (subtype_bool CC (JFClass j) (JFClass C)); now injection red_st].
       destruct (Classical_Prop.classic (Is_true (subtype_bool CC (JFClass j) (JFClass C)))).
       +++ unfold red.
           destruct (subtype_bool CC (JFClass j) (JFClass C)); try destruct H.
           injection red_st as h_eq st_eq.
           rewrite <-st_eq.
           exists h0_perm, h0_ext,
            ((Ctx0 [[substExpr (JFVar x) l' E0 ]]_ None) :: st_perm), pi.
           unfold red.
           split; [ | split; [ | split; [ | split]]]; try easy.
           split; try easy.
           unfold FramesPermuted.
           split; try split; try easy.
           now apply SubstPermutedExpr.
       +++ unfold red.
           destruct (subtype_bool CC (JFClass j) (JFClass C)); try now (exfalso; now apply H).
           injection red_st as h_eq st_eq.
           rewrite <-st_eq.
           now exists h0_perm, h0_ext,
            ((Ctx0 [[JFVal1 (JFVLoc l') ]]_ Some j) :: st_perm), pi.
  + destruct Ctx; [ | destruct j].
    ++ destruct v, st; try destruct f; try destruct E, A; try discriminate red_st.
       injection red_st as h_eq st_eq.
       destruct Ctx0; try destruct pi_ctx.
       destruct st_perm; try destruct f; try now destruct pi_st.
       simpl in pi_st.
       destruct pi_st as (pi_f & pi_st).
       destruct E, A; try now destruct pi_f.
       unfold FramesPermuted in pi_f.
       destruct pi_f as (pi_e & pi_ctx & _).
       destruct pi_e as (pi_v & pi_vs & m_eq).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-m_eq, <-h_eq, <-st_eq, <-A_eq.
       now exists h0_perm, h0_ext, (Ctx0 [[ JFVal1 (JFVLoc l') ]]_ None:: st_perm), pi.
    ++ destruct v; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct j; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct pi_ctx as ((C_eq & x_eq & pi_e) & pi_ctxs).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-h0_eq, <-st_eq, <-A_eq, <-x_eq.
       exists h0_perm, h0_ext, (Ctx0 [[ substExpr (JFVar x) l' E0 ]]_ None:: st_perm), pi.
       split; [ | split; [ | split; [ | split]]]; try easy.
       split; try easy.
       unfold FramesPermuted.
       split; try split; try easy.
       now apply SubstPermutedExpr.
    ++ destruct v; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct j0; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-h0_eq, <-st_eq, <-A_eq.
       now exists h0_perm, h0_ext, (Ctx0 [[ JFVal1 (JFVLoc l') ]]_ None:: st_perm), pi;
          destruct j.
Qed.

Lemma Val2ReductionPreservesHeapPermutation : forall vx,
   ExprReductionPreservesHeapPermutation (JFVal2 vx).
Proof.
  intros (v, f).
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f0.
  destruct pi_f as (pi_val2 & pi_ctx & A_eq).
  simpl in pi_val2.
  destruct E; try now destruct pi_val2.
  destruct vx as (v', f').
  destruct pi_val2 as (f_eq & pi_v).
  destruct A; try now (destruct Ctx, v; try destruct j0; try destruct l; discriminate red_st).
  destruct v as [ l |]; try destruct l.
  + destruct v' as [ l' |]; try destruct l'; try now destruct pi_v.
    assert (Some (h0, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H as h_eq st'_eq.
    rewrite <-h_eq, <-st'_eq, <-A_eq.
    exists h0_perm, h0_ext, ((Ctx0 [[JFVal1 NPE_val ]]_ NPE_mode) :: st_perm), pi.
    split; [ | split; [ | split; [ | split]]]; try easy.
    now destruct Ctx0; try destruct j.
  + destruct v' as [ l' |]; try destruct l' as [ | n']; try now destruct pi_v.
    unfold ValPermuted in pi_v.
    destruct pi_h0 as (bijection & locs_fst & locs_snd & objs).
    assert (exists o, Heap.find n h0 = Some o).
      destruct (Heap.find n h0) as [ o |].
      now exists o.
      now destruct Ctx; try destruct j.
    destruct H as (o & n_o).
    rewrite n_o in red_st.
    destruct (locs_fst n) as (n'' & n_n'' & n'_h0_perm).
      apply HeapFacts.elements_in_iff.
      exists o.
      now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
    apply MapsToEq with (n2 := n') in n_n''; try easy.
    rewrite <-n_n'' in *; clear n_n'' n''.
    unfold ObjsPermuted in objs.
    apply HeapFacts.elements_in_iff in n'_h0_perm as (o' & n'_o').
    apply HeapFacts.elements_mapsto_iff in n'_o'.
    apply HeapFacts.find_mapsto_iff in n_o.
    destruct o as (ro & cn), o' as (ro' & cn').
    destruct (objs n n' (ro, cn) (ro', cn') pi_v n_o n'_o') as (cn_eq & pi_o).
    rewrite <-cn_eq in *; clear cn_eq cn'.
    destruct (pi_o f) as (same_keys & _ & pi_f).
    assert (exists l, JFXIdMap.find f ro = Some l).
      destruct (JFXIdMap.find f ro).
      now exists l.
      now destruct Ctx; try destruct j; discriminate red_st.
    destruct H as (l & f_l).
    rewrite f_l in red_st.
    apply JFXIdMapFacts.find_mapsto_iff in f_l.
    destruct (same_keys l) as (l' & f_l'); trivial.
    assert (pi_l := pi_f l l' f_l f_l').
    assert (Some (h0, (Ctx [[JFVal1 (JFVLoc l) ]]_ None) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    rewrite <-h_eq, <-st_eq, <-A_eq, <-f_eq.
    exists h0_perm, h0_ext, ((Ctx0 [[JFVal1 (JFVLoc l') ]]_ None) :: st_perm), pi.
    split; [ | split; [ | split; [ | split]]]; try easy.
    simpl.
    apply HeapFacts.find_mapsto_iff in n'_o'.
    rewrite FindInUnion with (h1 := h0_perm) (h2 := h0') (o := (ro', cn)); trivial.
    apply JFXIdMapFacts.find_mapsto_iff in f_l'.
    rewrite f_l'.
    now destruct Ctx0; try destruct j.
  + now destruct Ctx; try destruct j.
Qed.

Lemma ThrowReductionPreservesHeapPermutation : forall v,
   ExprReductionPreservesHeapPermutation (JFThrow v).
Proof.
  intros v.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_throw & pi_ctx & A_eq).
  simpl in pi_throw.
  destruct E; try now destruct pi_throw.
  destruct A; try now (destruct Ctx, v; try destruct j0; try destruct l; discriminate red_st).
  destruct v as [ l | ]; try destruct l.
  + assert (Some (h0, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    destruct v0; try destruct l; try now destruct pi_throw.
    rewrite <-h_eq, <-st_eq, <-A_eq.
    exists h0_perm, h0_ext, ((Ctx0 [[JFVal1 NPE_val ]]_ NPE_mode) :: st_perm), pi.
    split; [ | split; [ | split; [ | split]]]; try easy.
    now destruct Ctx0; try destruct j.
  + assert (exists cn, class h0 n = Some cn).
      destruct (class h0 n); try now (destruct Ctx; try destruct j; discriminate red_st).
      now exists j.
    destruct H as (cn & n_cn).
    rewrite n_cn in red_st.
    destruct v0; try destruct l as [ | n']; try now destruct pi_throw.
    unfold ValPermuted in pi_throw.
    assert (n'_cn : class h0_ext n' = Some cn).
      apply PermutedClass with (h' := h0_perm) (n' := n') (pi := pi) in n_cn; trivial.
      unfold class in n_cn |- *.
      assert (exists o, Heap.find n' h0_perm = Some o).
        destruct (Heap.find n' h0_perm); try discriminate n_cn.
        now exists o.
      destruct H as (o' & n'_o').
      rewrite n'_o' in n_cn.
      apply FindInUnion with (h2 := h0') (h := h0_ext) in n'_o'; trivial.
      rewrite n'_o'.
      now destruct o' as (ro' & cn').
    assert (Some (h0, (Ctx [[ JFVal1 (JFVLoc (JFLoc n)) ]]_ Some cn) :: st) = Some (h', st')).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    rewrite <-h_eq, <-st_eq, <-A_eq.
    exists h0_perm, h0_ext, ((Ctx0 [[JFVal1 (JFVLoc (JFLoc n')) ]]_ Some cn) :: st_perm), pi.
    split; [ | split; [ | split; [ | split]]]; try easy.
    simpl.
    rewrite n'_cn.
    now destruct Ctx0; try destruct j.
  + now destruct Ctx; try destruct j.
Qed.

Lemma TryReductionPreservesHeapPermutation : forall e1 mu cn x e2,
   ExprReductionPreservesHeapPermutation (JFTry e1 mu cn x e2).
Proof.
  intros e1 mu cn x e2.
  intros h0 h0_perm h0' h0_ext Ctx A st h' st' st_perm pi CC.
  intros pi_npe pi_st pi_h0 red_st union.
  unfold red in red_st.
  simpl in pi_st.
  destruct st_perm; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_try & pi_ctx & A_eq).
  simpl in pi_try.
  destruct E; try now destruct pi_try.
  destruct pi_try as (mu_eq & cn_eq & x_eq & pi_e1 & pi_e2).
  rewrite <-mu_eq, <-cn_eq, <-x_eq, <-A_eq in *.
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  assert (Some (h0, Ctx _[ JFCtxTry __ mu cn x e2 _[[_ e1 _]]_ None ]_ :: st) = Some (h', st')).
    now destruct Ctx; try destruct j.
  injection H as st_eq h_eq.
  exists h0_perm, h0_ext, (Ctx0 _[ JFCtxTry __ mu cn x E2 _[[_ E1  _]]_ None]_ :: st_perm), pi.
  rewrite <-st_eq, <-h_eq.
  split; [ | split; [ | split; [| split]]]; try easy.
  now destruct Ctx0; try destruct j.
Qed.

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
  destruct st; try discriminate red_st.
  destruct f, E; try discriminate red_st.
  + now apply (NewReductionPreservesHeapPermutation mu cn vs)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (LetReductionPreservesHeapPermutation cn x E1 E2)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (IfReductionPreservesHeapPermutation v1 v2 E1 E2)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (InvokeReductionPreservesHeapPermutation v m vs)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (AssignReductionPreservesHeapPermutation vx v)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (Val1ReductionPreservesHeapPermutation v)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (Val2ReductionPreservesHeapPermutation vx)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (ThrowReductionPreservesHeapPermutation v)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
  + now apply (TryReductionPreservesHeapPermutation E1 mu cn x E2)
      with (h0 := h0) (h0_perm := h0_perm) (Ctx := Ctx) (A := A) (st := st).
Qed.

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
    [ [] [[ JFIExprSubstituteEnv env e ]]_ None]
    [ [] [[ JFIExprSubstituteEnv env e ]]_ None]
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

(* Evaluation depends only on heap fragment containing free variables *)

Definition FreeVarsInExprAreInHeap e (h : Heap) (env : JFITermEnv) :=
  forall x, VarFreeInExpr x e ->
    ((StrMap.MapsTo x null env) \/ exists n o, StrMap.MapsTo x (JFLoc n) env /\ Heap.MapsTo n o h).

Definition ValIsNotHardcodedLoc v :=
  match v with
  | JFVLoc (JFLoc _) => False
  | _ => True
  end.

Fixpoint NoHardcodedLocsInVals vs :=
  match vs with
  | [] => True
  | (v::vs) => ValIsNotHardcodedLoc v /\ NoHardcodedLocsInVals vs
  end.

Fixpoint NoHardcodedLocsInExpr e :=
  match e with
  | JFNew mu C vs => NoHardcodedLocsInVals vs
  | JFLet C x e1 e2 => NoHardcodedLocsInExpr e1 /\ NoHardcodedLocsInExpr e2
  | JFIf v1 v2 e1 e2 => ValIsNotHardcodedLoc v1 /\ ValIsNotHardcodedLoc v2 /\
      NoHardcodedLocsInExpr e1 /\ NoHardcodedLocsInExpr e2
  | JFInvoke v1 m vs => ValIsNotHardcodedLoc v1 /\ NoHardcodedLocsInVals vs
  | JFAssign (v1,fld) v2 => ValIsNotHardcodedLoc v1 /\ ValIsNotHardcodedLoc v2
  | JFVal1 v1 => ValIsNotHardcodedLoc v1
  | JFVal2 (v1, fld) => ValIsNotHardcodedLoc v1
  | JFThrow v1 => ValIsNotHardcodedLoc v1
  | JFTry e1 mu C x e2 => NoHardcodedLocsInExpr e1 /\ NoHardcodedLocsInExpr e2
  end.

Definition LocsInValAreInHeap v (h : Heap) :=
  match v with
  | JFVLoc (JFLoc n) => Heap.In n h
  | _ => True
  end.

Fixpoint LocsAreInHeap ls (h : Heap) :=
  match ls with
  | [] => True
  | null::ls => LocsAreInHeap ls h
  | (JFLoc n)::ls => Heap.In n h /\ LocsAreInHeap ls h
  end.

Fixpoint LocsInValsAreInHeap vs h :=
  match vs with
  | [] => True
  | v::vs => LocsInValAreInHeap v h /\ LocsInValsAreInHeap vs h
  end.

Fixpoint LocsInExprAreInHeap e h :=
  match e with
  | JFNew mu C vs => LocsInValsAreInHeap vs h
  | JFLet C x e1 e2 => LocsInExprAreInHeap e1 h /\ LocsInExprAreInHeap e2 h
  | JFIf v1 v2 e1 e2 => LocsInValAreInHeap v1 h /\ LocsInValAreInHeap v2 h /\
      LocsInExprAreInHeap e1 h /\ LocsInExprAreInHeap e2 h
  | JFInvoke v1 m vs => LocsInValAreInHeap v1 h /\ LocsInValsAreInHeap vs h
  | JFAssign (v1,fld) v2 => LocsInValAreInHeap v1 h /\ LocsInValAreInHeap v2 h
  | JFVal1 v1 => LocsInValAreInHeap v1 h
  | JFVal2 (v1, fld) => LocsInValAreInHeap v1 h
  | JFThrow v1 => LocsInValAreInHeap v1 h
  | JFTry e1 mu C x e2 => LocsInExprAreInHeap e1 h /\ LocsInExprAreInHeap e2 h
  end.

Definition NoFreeVars e := forall x, ~VarFreeInExpr x e.

Definition OnlyFreeVar e x := forall y, VarFreeInExpr y e -> x = y.

Definition LocsInCtxAreInHeap ctx h :=
  match ctx with
  | JFCtxLet _ x _ e => LocsInExprAreInHeap e h /\ OnlyFreeVar e x
  | JFCtxTry _ _ _ x e => LocsInExprAreInHeap e h /\ OnlyFreeVar e x
  end.

Fixpoint LocsInCtxsAreInHeap ctxs h :=
  match ctxs with
  | [] => True
  | ctx::ctxs => LocsInCtxAreInHeap ctx h /\ LocsInCtxsAreInHeap ctxs h
  end.

Definition LocsInFrameAreInHeap f h :=
  match f with 
  | MkFrame ctxs e _ => LocsInExprAreInHeap e h /\ NoFreeVars e /\ LocsInCtxsAreInHeap ctxs h
  end.

Fixpoint LocsInStackAreInHeap st h :=
  match st with
  | [] => True
  | f::st => LocsInFrameAreInHeap f h /\ LocsInStackAreInHeap st h
  end.

Definition LocMapsToHeap l (h : Heap) :=
  match l with
  | null => True
  | JFLoc n => Heap.In n h
  end.

Definition PiOnlyFromHeap (pi : HeapPermutation) (h : Heap) :=
  forall n, NatMap.In n (fst pi) -> Heap.In n h.

Definition EverythingPermuted h1 h2 st1 st2 pi :=
  PiMapsTo (JFLoc NPE_object_loc) (JFLoc NPE_object_loc) pi /\
  HeapsPermuted h1 h2 pi /\
  StacksPermuted st1 st2 pi.

Definition DisjointUnionOfLocsInStackAndRest st h_base h_rest h :=
  LocsInStackAreInHeap st h_base /\
  HeapConsistent h_base /\
  JFIDisjointUnion h_base h_rest h.

Definition ExprReductionDependsOnFreeVars (e1 : JFExpr) := forall Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi,
  let st1 := ((Ctx [[ e1 ]]_ A) :: st1') in
  PiOnlyFromHeap pi h1_base ->
  EverythingPermuted h1_base h2_base st1 st2 pi ->
  DisjointUnionOfLocsInStackAndRest st1 h1_base h1_rest h1 ->
  DisjointUnionOfLocsInStackAndRest st2 h2_base h2_rest h2 ->
  red CC (h1, st1) = Some (hn1, stn1) ->
  exists hn1_base hn2_base hn2 stn2 pi',
    PermutationSubset pi pi' /\
    PiOnlyFromHeap pi' hn1_base /\
    EverythingPermuted hn1_base hn2_base stn1 stn2 pi' /\
    DisjointUnionOfLocsInStackAndRest stn1 hn1_base h1_rest hn1 /\
    DisjointUnionOfLocsInStackAndRest stn2 hn2_base h2_rest hn2 /\
    red CC (h2, st2) = Some (hn2, stn2).

Lemma NoFreeVarsInIfExprs : forall v1 v2 e1 e2,
  NoFreeVars (JFIf v1 v2 e1 e2) ->
  (NoFreeVars e1 /\ NoFreeVars e2).
Proof.
  intros v1 v2 e1 e2 no_free_in_if.
  split; intros x x_in_e; apply (no_free_in_if x); simpl.
  + now apply or_intror, or_intror, or_introl.
  + now apply or_intror, or_intror, or_intror.
Qed.

Lemma NoFreeVarsInLetExprs : forall cn x e1 e2,
  NoFreeVars (JFLet cn x e1 e2) ->
  (NoFreeVars e1 /\ OnlyFreeVar e2 x).
Proof.
  intros cn x e1 e2 no_free_in_let.
  split.
  + intros y y_in_e1.
    apply (no_free_in_let y).
    now apply or_introl.
  + intros y y_free.
    assert (y_not_free := no_free_in_let y).
    simpl in y_not_free.
    assert (~ y <> x).
      intro.
      apply y_not_free.
      now apply or_intror.
    symmetry.
    now apply NNPP.
Qed.

Lemma NoFreeVarsInTryExprs : forall e1 mu cn x e2,
  NoFreeVars (JFTry e1 mu cn x e2) ->
  (NoFreeVars e1 /\ OnlyFreeVar e2 x).
Proof.
  intros e1 mu cn x e2 no_free_in_try.
  split.
  + intros y y_in_e1.
    apply (no_free_in_try y).
    now apply or_introl.
  + intros y y_free.
    assert (y_not_free := no_free_in_try y).
    simpl in y_not_free.
    assert (~ y <> x).
      intro.
      apply y_not_free.
      now apply or_intror.
    symmetry.
    now apply NNPP.
Qed.

Lemma NewlocNewInUnion : forall h_base h_rest h,
  JFIDisjointUnion h_base h_rest h ->
  ~ Heap.In (newloc h) h_rest.
Proof.
  intros h_base h_rest h union in_rest.
  apply HeapFacts.elements_in_iff in in_rest as (o & n_o).
  rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n_o.
  apply DisjointUnionSymmetry in union.
  apply FindInUnion with (h2 := h_base) (h := h) in n_o; trivial.
  apply newloc_new in n_o.
  now apply n_o.
Qed.

Lemma ExtendPiOnlyFromHeap : forall pi n1 n2 o1 h,
  PiOnlyFromHeap pi h ->
  PiOnlyFromHeap (NatMap.add n1 n2 (fst pi), NatMap.add n2 n1 (snd pi)) (Heap.add n1 o1 h).
Proof.
  intros pi n1 n2 o1 h.
  intros pi_in_h.
  intros n n_in_pi.
  simpl in n_in_pi.
  destruct (Classical_Prop.classic (n1 = n)).
  + apply HeapFacts.elements_in_iff.
    exists o1.
    now rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o.
  + apply NatMapFacts.elements_in_iff in n_in_pi as (n' & n_n').
    rewrite <-NatMapFacts.elements_mapsto_iff, NatMapFacts.find_mapsto_iff, NatMapFacts.add_neq_o in n_n'; trivial.
    assert (n_in_h := pi_in_h n).
    apply HeapFacts.elements_in_iff in n_in_h as (o & n_o).
    ++ apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n_o.
       apply HeapFacts.elements_in_iff.
       exists o.
       now rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o.
    ++ apply HeapFacts.elements_in_iff.
       exists n'.
       now rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
Qed.

Lemma ExtendSubheapWithNewloc : forall h_base h_rest h o,
  JFIDisjointUnion h_base h_rest h ->
  JFISubheap h_base (Heap.add (newloc h) o h_base).
Proof.
  intros h_base h_rest h o union.
  intros n' o' n'_o'.
  rewrite HeapFacts.find_mapsto_iff in n'_o' |-*.
  rewrite HeapFacts.add_neq_o; trivial.
  intros n_eq.
  rewrite <-n_eq in n'_o'.
  apply DisjointUnionSymmetry in union.
  apply NewlocNewInUnion in union.
  apply union.
  apply HeapFacts.elements_in_iff.
  exists o'.
  now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
Qed.

Lemma InitFldInFldsLocs : forall flds_locs f l o,
  JFXIdMap.MapsTo f l (init_obj_aux o flds_locs) ->
  ~JFXIdMap.MapsTo f l o ->
  In (f, l) flds_locs.
Proof.
  intros flds_locs.
  induction flds_locs; intros f l o f_l not_f_l.
  + simpl in f_l.
    now exfalso.
  + destruct a as (f' & l').
    apply JFXIdMapFacts.find_mapsto_iff in f_l.
    destruct (Classical_Prop.classic (f' = f)).
    ++ simpl in f_l |- *.
       destruct (Classical_Prop.classic (l' = l)).
       +++ apply or_introl.
           now rewrite H, H0.
       +++ apply or_intror.
           apply JFXIdMapFacts.find_mapsto_iff in f_l.
           apply IHflds_locs with (o := (JFXIdMap.add f' l' o)); try easy.
           intros f_l_add.
           rewrite JFXIdMapFacts.find_mapsto_iff, JFXIdMapFacts.add_eq_o in f_l_add; trivial.
           now injection f_l_add as l_eq.
    ++ simpl in f_l |- *.
       apply or_intror.
       apply JFXIdMapFacts.find_mapsto_iff in f_l.
       apply IHflds_locs with (o := (JFXIdMap.add f' l' o)); try easy.
       intros f_l_o.
       apply not_f_l.
       rewrite JFXIdMapFacts.find_mapsto_iff in f_l_o |- *.
       now rewrite JFXIdMapFacts.add_neq_o in f_l_o.
Qed.

Lemma FldsLocsInHeap : forall flds_locs (flds : list JFXId) locs h,
  LocsAreInHeap locs h ->
  JaUtils.zip flds locs = Some flds_locs ->
  (forall f n, In (f, (JFLoc n)) flds_locs -> Heap.In n h).
Proof.
  intros flds_locs.
  induction flds_locs; try easy.
  intros flds locs h locs_in_h zip.
  intros f n fn_in_flds_locs.
  destruct flds, locs; try discriminate zip.
  simpl in zip.
  assert (exists flds_locs', JaUtils.zip flds locs = Some flds_locs').
    destruct (JaUtils.zip flds locs); try discriminate zip.
    now exists l0.
  destruct H as (flds_locs' & zip').
  rewrite zip' in zip.
  injection zip as a_eq flds_locs_eq.
  rewrite flds_locs_eq in *.
  clear flds_locs' flds_locs_eq.
  destruct (Classical_Prop.classic ((f, JFLoc n) = a)).
  + rewrite <-H in *.
    injection a_eq as f_eq l_eq.
    rewrite l_eq in locs_in_h.
    now simpl in locs_in_h.
  + rewrite <-a_eq in *.
    apply in_inv in fn_in_flds_locs.
    destruct fn_in_flds_locs.
    ++ exfalso.
       now apply H.
    ++ apply IHflds_locs with (flds := flds) (locs := locs) (f := f); try easy.
       simpl in locs_in_h.
       now destruct l.
Qed.

Lemma ExtendConsistentHeap : forall new_n flds_locs cn h,
  (forall f n, In (f, (JFLoc n)) flds_locs -> Heap.In n h) ->
  HeapConsistent h ->
  HeapConsistent (Heap.add new_n (init_obj_aux (JFXIdMap.empty Loc) flds_locs, cn) h).
Proof.
  intros new_n flds_locs cn h.
  intros locs_in_h h_consistent n o f f_n n_o f_fn.
  rewrite HeapFacts.find_mapsto_iff in n_o.
  destruct (Classical_Prop.classic (new_n = n)).
  + rewrite HeapFacts.add_eq_o in n_o; trivial.
    destruct (Classical_Prop.classic (new_n = f_n)).
    ++ exists (init_obj_aux (JFXIdMap.empty Loc) flds_locs, cn).
       now rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o.
    ++ destruct o as (ro & cno).
       injection n_o as ro_eq cno_eq.
       rewrite <-cno_eq in *; clear cno_eq cno.
       rewrite <-ro_eq in f_fn.
       simpl in f_fn.
       apply InitFldInFldsLocs, locs_in_h in f_fn.
       apply HeapFacts.elements_in_iff in f_fn as (o' & fn_o').
       exists o'.
       rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o; trivial.
       now rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in fn_o'.
       intros f_fn_empty.
       now apply JFXIdMapFacts.empty_mapsto_iff in f_fn_empty.
  + rewrite HeapFacts.add_neq_o, <-HeapFacts.find_mapsto_iff in n_o; trivial.
    destruct (Classical_Prop.classic (new_n = f_n)).
    ++ exists (init_obj_aux (JFXIdMap.empty Loc) flds_locs, cn).
       now rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o.
    ++ destruct (h_consistent n o f f_n n_o f_fn) as (o' & f_n_o').
       exists o'.
       rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o, <-HeapFacts.find_mapsto_iff; trivial.
Qed.

Lemma AllocOnFreeVars : forall h1_base h1_rest h1 hn1 h2_base h2_rest h2 CC cn locs1 l1 locs2 pi,
  alloc_init CC h1 cn locs1 = Some (l1, hn1) ->
  HeapConsistent h1_base ->
  HeapConsistent h2_base ->
  JFIDisjointUnion h1_base h1_rest h1 ->
  JFIDisjointUnion h2_base h2_rest h2 ->
  HeapsPermuted h1_base h2_base pi ->
  LocsPermuted locs1 locs2 pi ->
  LocsAreInHeap locs1 h1_base ->
  LocsAreInHeap locs2 h2_base ->
  PiOnlyFromHeap pi h1_base ->
  exists pi' hn1_base l2 hn2_base hn2,
    (PermutationSubset pi pi' /\
     HeapsPermuted hn1_base hn2_base pi' /\
     PiMapsTo l1 l2 pi' /\
     JFISubheap h1_base hn1_base /\
     JFISubheap h2_base hn2_base /\
     HeapConsistent hn1_base /\
     HeapConsistent hn2_base /\
     JFIDisjointUnion hn1_base h1_rest hn1 /\
     JFIDisjointUnion hn2_base h2_rest hn2 /\
     LocsInValAreInHeap (JFVLoc l1) hn1_base /\
     LocsInValAreInHeap (JFVLoc l2) hn2_base /\
     PiOnlyFromHeap pi' hn1_base /\
     alloc_init CC h2 cn locs2 = Some (l2, hn2)).
Proof.
  intros h1_base h1_rest h1 hn1 h2_base h2_rest h2 CC cn locs1 l1 locs2 pi.
  intros h1_alloc h1_consistent h2_consistent h1_union h2_union pi_base pi_locs locs1_in_h1 locs_in_h2 pi_in_h1.
  unfold alloc_init in *.
  destruct pi_base as (bijection & locs_fst & locs_snd & objs).
  destruct (flds CC (JFClass cn)) as [flds | ]; try discriminate h1_alloc.
  unfold init_obj in *.
  assert (exists flds_locs1, JaUtils.zip flds locs1 = Some flds_locs1).
    destruct (JaUtils.zip flds locs1); try now discriminate h1_alloc.
    now exists l.
  destruct H as (flds_locs1 & zip_locs1).
  destruct (ExistsPermutedZip flds locs1 locs2 flds_locs1 pi)
    as (flds_locs2 & zip_locs2 & pi_zip); trivial.
  rewrite zip_locs1 in h1_alloc.
  rewrite zip_locs2.
  injection h1_alloc as l1_eq hn1_eq.
  destruct l1 as [ | n1]; try discriminate l1_eq.
  injection l1_eq as n1_eq.
  set (n2 := newloc h2).
  set (pi' := (NatMap.add n1 n2 (fst pi), NatMap.add n2 n1 (snd pi))).
  assert (pi_subset : PermutationSubset pi pi').
    apply ExtendPiSubset.
    rewrite <-n1_eq.
    intros n1_in_pi.
    apply pi_in_h1 in n1_in_pi.
    apply HeapFacts.elements_in_iff in n1_in_pi as (newobj & newloc_newobj).
    apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in newloc_newobj.
    apply (newloc_new h1 (newloc h1) newobj); trivial.
    rewrite <-HeapFacts.find_mapsto_iff in newloc_newobj |- *.
    destruct h1_union as ((subheap & _) & _).
    now apply subheap.
  assert (pi_obj := PermutedZipIsPermutedInit flds_locs1 flds_locs2 cn
      (JFXIdMap.empty Loc) (JFXIdMap.empty Loc) pi pi_zip).
  apply ExtendObjPermutation with (pi' := pi') in pi_obj; try easy.
  exists pi',
    (Heap.add n1 (init_obj_aux (JFXIdMap.empty Loc) flds_locs1, cn) h1_base),
    (JFLoc n2),
    (Heap.add n2 (init_obj_aux (JFXIdMap.empty Loc) flds_locs2, cn) h2_base),
    (Heap.add n2 (init_obj_aux (JFXIdMap.empty Loc) flds_locs2, cn) h2).
  split; [ | split; [ | split; [ | split; [ | split; [ | split;
      [ | split; [ | split; [ | split; [ | split; [ | split; [ | split]]]]]]]]]]]; try easy.
  + apply ExtendPermutedHeaps; simpl; trivial.
    now apply ExtendHeapsPermutation with (pi := pi).
    now rewrite NatMapFacts.find_mapsto_iff, NatMapFacts.add_eq_o.
  + unfold PiMapsTo, pi', fst.
    now rewrite NatMapFacts.find_mapsto_iff, NatMapFacts.add_eq_o.
  + rewrite <-n1_eq.
    now apply ExtendSubheapWithNewloc with (h_rest := h1_rest).
  + unfold n2.
    now apply ExtendSubheapWithNewloc with (h_rest := h2_rest).
  + apply ExtendConsistentHeap; try easy.
    now apply FldsLocsInHeap with (flds := flds) (locs := locs1).
  + apply ExtendConsistentHeap; try easy.
    now apply FldsLocsInHeap with (flds := flds) (locs := locs2).
  + rewrite <-hn1_eq, <-n1_eq.
    apply ExtendDisjointUnion; try easy.
    now apply NewlocNewInUnion with (h_base := h1_base).
  + apply ExtendDisjointUnion; try easy.
    now apply NewlocNewInUnion with (h_base := h2_base).
  + simpl.
    apply HeapFacts.elements_in_iff.
    exists ((init_obj_aux (JFXIdMap.empty Loc) flds_locs1, cn)).
    apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
    now rewrite HeapFacts.add_eq_o.
  + simpl.
    apply HeapFacts.elements_in_iff.
    exists ((init_obj_aux (JFXIdMap.empty Loc) flds_locs2, cn)).
    apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
    now rewrite HeapFacts.add_eq_o.
  + now apply ExtendPiOnlyFromHeap.
Qed.

Lemma LocsInValAreInSuperheap : forall v h1 h2,
  LocsInValAreInHeap v h1 ->
  JFISubheap h1 h2 ->
  LocsInValAreInHeap v h2.
Proof.
  intros v h1 h2 v_in_h1 subheap.
  unfold LocsInValAreInHeap in *.
  destruct v; try destruct l; try easy.
  rewrite HeapFacts.elements_in_iff in *.
  destruct v_in_h1 as (o & n_o).
  exists o.
  rewrite <-HeapFacts.elements_mapsto_iff in *.
  now apply subheap.
Qed.
Hint Resolve LocsInValAreInSuperheap : locs_in_superheap.

Lemma LocsInValsAreInSuperheap : forall vs h1 h2,
  LocsInValsAreInHeap vs h1 ->
  JFISubheap h1 h2 ->
  LocsInValsAreInHeap vs h2.
Proof.
  intros vs.
  induction vs; try easy.
  intros h1 h2 vs_in_h1 subheap.
  simpl in *.
  destruct vs_in_h1 as (a_in_h1 & vs_in_h1).
  eauto with locs_in_superheap.
Qed.
Hint Resolve LocsInValsAreInSuperheap : locs_in_superheap.

Lemma LocsInExprAreInSuperheap : forall e h1 h2,
  LocsInExprAreInHeap e h1 ->
  JFISubheap h1 h2 ->
  LocsInExprAreInHeap e h2.
Proof.
  intros e.
  induction e; intros h1 h2 e_in_h1 subheap; simpl in e_in_h1 |- *;
       try destruct vx; try destruct e_in_h1; eauto with locs_in_superheap.
  destruct H0 as (H0 & H1 & H2).
  split; [ | split; [ | split]]; eauto with locs_in_superheap.
Qed.
Hint Resolve LocsInExprAreInSuperheap : locs_in_superheap.

Lemma LocsInCtxAreInSuperheap : forall ctx h1 h2,
  LocsInCtxAreInHeap ctx h1 ->
  JFISubheap h1 h2 ->
  LocsInCtxAreInHeap ctx h2.
Proof.
  intros ctx h1 h2 ctx_in_h1 subheap.
  unfold LocsInCtxAreInHeap in *.
  destruct ctx; destruct ctx_in_h1 as (e_in_h1 & only_free_var);
  eauto with locs_in_superheap.
Qed.
Hint Resolve LocsInCtxAreInSuperheap : locs_in_superheap.

Lemma LocsInCtxsAreInSuperheap : forall ctxs h1 h2,
  LocsInCtxsAreInHeap ctxs h1 ->
  JFISubheap h1 h2 ->
  LocsInCtxsAreInHeap ctxs h2.
Proof.
  intros ctxs.
  induction ctxs; try easy.
  intros h1 h2 ctxs_in_h1 subheap.
  destruct ctxs_in_h1 as (a_in_h1 & ctxs_in_h1).
  split; eauto with locs_in_superheap.
Qed.
Hint Resolve LocsInCtxsAreInSuperheap : locs_in_superheap.

Lemma LocsInStackAreInSuperheap : forall st h1 h2,
  LocsInStackAreInHeap st h1 ->
  JFISubheap h1 h2 ->
  LocsInStackAreInHeap st h2.
Proof.
  intros st.
  induction st; try easy.
  intros h1 h2.
  intros st_in_h1 subheap.
  simpl in *.
  destruct a.
  destruct st_in_h1 as ((e_in_h1 & no_free_in_e & ctx_in_h1) & st_in_h1).
  split; [ split; [ | split] | ]; eauto with locs_in_superheap.
Qed.

Lemma NewParamsAreInHeap : forall locs Ctx mu cn vs st h_base h_rest h,
  DisjointUnionOfLocsInStackAndRest ((Ctx [[JFNew mu cn vs ]]_ None) :: st) h_base h_rest h ->
  list_map_opt loc_of_val vs = Some locs ->
  LocsAreInHeap locs h_base.
Proof.
  intros locs.
  induction locs; intros Ctx mu cn vs st h_base h_rest h;
                intros (vs_in_base & base_consistent & union) locs_of_vs; try easy.
  destruct vs; try discriminate locs_of_vs.
  destruct j; try discriminate locs_of_vs.
  simpl in locs_of_vs.
  assert (exists locs', list_map_opt loc_of_val vs = Some locs').
    destruct (list_map_opt loc_of_val vs); try discriminate locs_of_vs.
    now exists l0.
  destruct H as (locs' & locs'_of_vs).
  rewrite locs'_of_vs in locs_of_vs.
  injection locs_of_vs as a_eq locs_eq.
  rewrite a_eq, locs_eq in *.
  clear l locs' a_eq locs_eq.
  destruct a.
  + simpl.
    apply (IHlocs Ctx mu cn vs st h_base h_rest h); try easy.
    split; [ | split]; try easy.
    simpl in vs_in_base |- *.
    split; [ split; [ | split] |]; try easy.
    destruct vs_in_base as ( (_  & no_free_vars & _) & _).
    unfold NoFreeVars in *.
    intros x x_in_new.
    apply (no_free_vars x).
    simpl.
    now apply or_intror.
  + simpl.
    simpl in vs_in_base.
    destruct vs_in_base as ((n_in_base & vs_in_base) & st_in_base).
    split; try easy.
    apply (IHlocs Ctx mu cn vs st h_base h_rest h); try easy.
    split; [ | split]; try easy.
    simpl in vs_in_base |- *.
    split; [ split; [ | split] |]; try easy.
    destruct vs_in_base as (no_free_vars & _).
    unfold NoFreeVars in *.
    intros x x_in_new.
    apply (no_free_vars x).
    simpl.
    now apply or_intror.
Qed.

Lemma NewReductionDependsOnFreeVars : forall mu cn vs,
  ExprReductionDependsOnFreeVars (JFNew mu cn vs).
Proof.
  intros mu cn vs.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_new & pi_ctx & A_eq).
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  rewrite <-A_eq in *.
  destruct E; try (simpl in pi_new; now destruct pi_new).
  assert (exists locs1, list_map_opt loc_of_val vs = Some locs1).
    destruct (list_map_opt loc_of_val vs).
    now exists l.
    destruct Ctx; try destruct j; try destruct (alloc_init CC h0 cn l); discriminate red_st.
  destruct H as (locs1 & locs1_of_vs).
  assert (locs1_of_vs1 := locs1_of_vs).
  rewrite locs1_of_vs in red_st.
  assert (exists l1 hp, alloc_init CC h1 cn locs1 = Some (l1, hp)).
    destruct alloc_init.
    destruct p. now exists l, h.
    destruct Ctx; try destruct j; discriminate red_st.
  destruct H as (l1 & hp & alloc_h1).
  rewrite alloc_h1 in *.
  assert (hn1 = hp /\ stn1 = ((Ctx [[JFVal1 (JFVLoc l1) ]]_ None) :: st1')).
    destruct Ctx; try destruct j; now injection red_st.
  simpl in pi_new.
  destruct pi_new as (_ & cn_eq & vs_perm).
  destruct H as (hn1_eq & stn1_eq).
  rewrite <-hn1_eq, stn1_eq, <-cn_eq in *.
  apply LocOfValsPermutation with (vs_perm := vs0) (pi := pi) in locs1_of_vs as (locs2 & locs2_of_vs2 & locs_permuted); try easy.

  destruct (AllocOnFreeVars h1_base h1_rest h1 hn1 h2_base h2_rest h2 CC cn locs1 l1 locs2 pi)
    as (pi' & hn1_base & l2 & hn2_base & hn2 & pi_subset & pi_hn_base & pi_l &
        h1_subheap & h2_subheap & hn1_consistent & hn2_consistent & hn1_union & hn2_union &
        l1_in_h1 & l2_in_h2 & pi'_in_h2 & alloc_h2); try easy.
    now apply h1_union.
    now apply h2_union.
    now apply h1_union.
    now apply h2_union.
    now apply NewParamsAreInHeap with (locs := locs1) in h1_union.
    now apply NewParamsAreInHeap with (locs := locs2) in h2_union.

  exists hn1_base, hn2_base, hn2, ((Ctx0 [[JFVal1 (JFVLoc l2) ]]_ None) :: st2), pi'.
  apply ExtendCtxsPermutation with (pi' := pi') in pi_ctx; try easy.
  apply ExtendStacksPermutation with (pi' := pi') in pi_st; try easy.
  split; [ |split; [ | split; [split; [ | split] | split; [ | split]]]]; try easy.
  + now apply pi_subset.
  + unfold DisjointUnionOfLocsInStackAndRest.
    split; [ | split]; try easy.
    split.
    ++ split; [ | split]; try easy.
       apply LocsInCtxsAreInSuperheap with (h1 := h1_base); try easy.
       apply h1_union.
    ++ apply LocsInStackAreInSuperheap with (h1 := h1_base); try easy.
       apply h1_union.
  + unfold DisjointUnionOfLocsInStackAndRest.
    split; [ | split]; try easy.
    split.
    ++ split; [ | split]; try easy.
       apply LocsInCtxsAreInSuperheap with (h1 := h2_base); try easy.
       apply h2_union.
    ++ apply LocsInStackAreInSuperheap with (h1 := h2_base); try easy.
       apply h2_union.
  + simpl.
    rewrite locs2_of_vs2, alloc_h2.
    now destruct Ctx0; try destruct j.
Qed.

Lemma LetReductionDependsOnFreeVars : forall cn x e1 e2,
   ExprReductionDependsOnFreeVars (JFLet cn x e1 e2).
Proof.
  intros cn x e1 e2.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_let & pi_ctx & A_eq).
  simpl in pi_let.
  destruct E; try now destruct pi_let.
  destruct pi_let as (cn_eq & x_eq & pi_e1 & pi_e2).
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  assert (Some (h1, Ctx _[ JFCtxLet cn x __ e2 _[[_ e1 _]]_ None ]_ :: st1') = Some (hn1, stn1)).
    now destruct Ctx; try destruct j.
  injection H.
  intros st_eq h_eq.
  exists h1_base, h2_base, h2, (Ctx0 _[ JFCtxLet cn x __ E2 _[[_ E1  _]]_ None]_ :: st2), pi.
  rewrite <-st_eq, <-h_eq, <-x_eq in *.
  unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
  simpl in h1_union, h2_union.
  assert (NoFreeVars e1 /\ OnlyFreeVar e2 x).
    split; now apply (NoFreeVarsInLetExprs cn x e1 e2).
  destruct H0 as (no_free_e1 & only_free_e2).
  assert (NoFreeVars E1 /\ OnlyFreeVar E2 x).
    split; now apply (NoFreeVarsInLetExprs cn0 x E1 E2).
  destruct H0 as (no_free_E1 & only_free_E2).
  split; [ | split; [ | split; [| split; [ | split]]]]; try easy.
  rewrite <-A_eq, cn_eq, x_eq.
  now destruct Ctx0; try destruct j.
Qed.

Lemma IfReductionDependsOnFreeVars : forall v1 v2 e1 e2,
   ExprReductionDependsOnFreeVars (JFIf v1 v2 e1 e2).
Proof.
  intros v1 v2 e1 e2.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_if & pi_ctx & A_eq).
  simpl in pi_if.
  destruct v1, v2, E; try destruct v1, v2; try now destruct pi_if;
    try now (destruct Ctx; try destruct j; discriminate red_st).
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
  simpl in h1_union, h2_union.
  assert (NoFreeVars e1 /\ NoFreeVars e2).
    split; now apply (NoFreeVarsInIfExprs (JFVLoc l) (JFVLoc l0) e1 e2).
  destruct H as (no_free_in_e1 & no_free_in_e2).
  assert (NoFreeVars E1 /\ NoFreeVars E2).
    split; now apply (NoFreeVarsInIfExprs (JFVLoc l1) (JFVLoc l2) E1 E2).
  destruct H as (no_free_in_E1 & no_free_in_E2).
  destruct (Classical_Prop.classic (l = l0)) as [l_eq | l_neq].
  + Loc_dec_eq l l0 l_eq.
    assert (l1_eq : l1 = l2).
      now apply (PiMapsToEqIff l l0 l1 l2 pi (proj1 pi_base)).
    assert (Some (h1, (Ctx [[ e1 ]]_ None) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H.
    intros st_eq h_eq.
    exists h1_base, h2_base, h2, (Ctx0 [[ E1 ]]_ None :: st2), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq.
    split; [ | split; [ | split; [| split; [ | split]]]]; try easy.
    simpl.
    Loc_dec_eq l1 l2 l1_eq.
    now destruct Ctx0; try destruct j.
  + Loc_dec_neq l l0 l_neq.
    assert (l1_neq : l1 <> l2).
      intros l1_eq. apply l_neq.
      now apply (PiMapsToEqIff l l0 l1 l2 pi (proj1 pi_base)).
    assert (Some (h1, (Ctx [[ e2 ]]_ None) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H.
    intros st_eq h_eq.
    exists h1_base, h2_base, h2, (Ctx0 [[ E2 ]]_ None :: st2), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq.
    split; [ | split; [ | split; [| split]]]; try easy.
    simpl.
    Loc_dec_neq l1 l2 l1_neq.
    now destruct Ctx0; try destruct j.
Qed.

Lemma SubheapPreservesClassName : forall n h h',
  JFISubheap h' h ->
  Heap.In n h' ->
  getClassName h' n = getClassName h n.
Proof.
  intros n h h'.
  intros subheap n_in_h'.
  apply HeapFacts.elements_in_iff in n_in_h' as (o & n_o_h').
  apply HeapFacts.elements_mapsto_iff in n_o_h'.
  assert (n_o_h := subheap _ _ n_o_h').
  rewrite HeapFacts.find_mapsto_iff in n_o_h', n_o_h.
  unfold getClassName.
  now rewrite n_o_h', n_o_h.
Qed.

Lemma ClassNameClassEq : forall n h,
  Heap.In n h ->
  class h n = getClassName h n.
Proof.
  intros n h n_in_h.
Admitted.

Lemma ExistsBodyWithSameFreeVars : forall Ctx1 Ctx2 h1_base h1_rest h1 hn1 h2_base h2_rest h2 n1 n2 vs1 vs2 st1 stn1 st2 m pi CC,
  HeapsPermuted h1_base h2_base pi ->
  PiMapsTo (JFLoc n1) (JFLoc n2) pi ->
  ValsPermuted vs1 vs2 pi ->
  CtxsPermuted Ctx1 Ctx2 pi ->
  StacksPermuted st1 st2 pi ->
  DisjointUnionOfLocsInStackAndRest
             ((Ctx1 [[JFInvoke (JFVLoc (JFLoc n1)) m vs1 ]]_ None) :: st1)
             h1_base h1_rest h1 ->
  DisjointUnionOfLocsInStackAndRest
             ((Ctx2 [[JFInvoke (JFVLoc (JFLoc n2)) m vs2 ]]_ None) :: st2)
             h2_base h2_rest h2 ->
  getInvokeBody CC (getClassName h1 n1) n1 m vs1 h1 Ctx1 st1 = Some (hn1, stn1) ->
  hn1 = h1 /\
  exists stn2,
    StacksPermuted stn1 stn2 pi /\
    DisjointUnionOfLocsInStackAndRest stn1 h1_base h1_rest h1 /\
    DisjointUnionOfLocsInStackAndRest stn2 h2_base h2_rest h2 /\
    getInvokeBody CC (getClassName h2 n2) n2 m vs2 h2 Ctx2 st2 = Some (h2, stn2).
Proof.
  intros Ctx1 Ctx2 h1_base h1_rest h1 hn1 h2_base h2_rest h2 n1 n2 vs1 vs2 st1 stn1 st2 m pi CC.
  intros pi_h pi_n pi_vs pi_ctxs pi_st h1_union h2_union invoke.
  unfold getInvokeBody in invoke.
  assert (exists C, getClassName h1 n1 = Some C).
    destruct (getClassName h1 n1); try discriminate invoke.
    now exists j.
  destruct H as (C & class_name).
  rewrite class_name in invoke.
  assert (exists md, methodLookup CC C m = Some md).
    destruct (methodLookup CC C m); try discriminate invoke.
    now exists j.
  destruct H as (md & method_lookup).
  rewrite method_lookup in invoke.
  assert (exists Es1, substList (map JFVar (params_of_md md)) vs1
             (substExpr JFThis (JFLoc n1) (body_of_md md)) = Some Es1).
    destruct (substList (map JFVar (params_of_md md)) vs1
             (substExpr JFThis (JFLoc n1) (body_of_md md))); try discriminate invoke.
    now exists j.
  destruct H as (Es1, subst_es1).
  rewrite subst_es1 in invoke.
  injection invoke.
  intros st_eq h_eq.
  symmetry in h_eq.
  split; trivial.
  destruct stn1; try discriminate st_eq.
  destruct stn1; try discriminate st_eq.
  injection st_eq as f_eq f0_eq st_eq.
  rewrite <-st_eq, <-f_eq, <-f0_eq in *.
  assert (fs_not_this : forall f, In f (map JFVar (params_of_md md)) -> f <> JFThis).
    intros f1 f1_in_map f1_this.
    apply in_map_iff in f1_in_map.
    destruct f1_in_map as (x & f1_var & _).
    now rewrite f1_this in f1_var.
  assert (fs_length_eq : length (map JFVar (params_of_md md)) = length vs1).
    rewrite map_length.
    admit. (* TODO params length *)
  assert (vs_length_eq : length vs1 = length vs2).
    now apply PermutedValsLength with (pi := pi).
  assert (pi_body : ExprsPermuted (body_of_md md) (body_of_md md) pi).
    admit. (* TODO body permuted -- no locs in it *)
  destruct (PermutationPreservesSubstList (map JFVar (params_of_md md)) vs1 vs2 fs_not_this fs_length_eq vs_length_eq (body_of_md md) (body_of_md md) n1 n2 Es1 pi)
    as (Es2 & pi_es & subst_es2); trivial.
  exists (([] [[ Es2 ]]_ None)
        :: (Ctx2 [[JFInvoke (JFVLoc (JFLoc n2)) m vs2
            ]]_ None) :: st2).
  unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
  simpl in h1_union, h2_union.
  split; [ | split; [ | split]]; try easy.
  + unfold DisjointUnionOfLocsInStackAndRest.
    split; [ | split]; try easy.
    simpl.
    split; [ split; [ | split] | split; [ split |]]; try easy.
    ++ admit. (* TODO no locs hardcoded in method *)
    ++ admit. (* TODO only free vars in method are params *)
  + unfold DisjointUnionOfLocsInStackAndRest.
    split; [ | split]; try easy.
    simpl.
    split; [ split; [ | split] | split; [ split |]]; try easy.
    ++ admit. (* TODO no locs hardcoded in method *)
    ++ admit. (* TODO only free vars in method are params *)
  + rewrite <-SubheapPreservesClassName with (h' := h1_base) in class_name; try apply h1_union.
    apply PermutationPreservesClassName with (h2 := h2_base) (n2 := n2) (pi := pi) in class_name; trivial.
    rewrite SubheapPreservesClassName with (h := h2) in class_name; try apply h2_union.
    unfold getInvokeBody.
    now rewrite class_name, method_lookup, subst_es2.
Admitted.

Lemma InvokeReductionDependsOnFreeVars : forall v m vs,
   ExprReductionDependsOnFreeVars (JFInvoke v m vs).
Proof.
  intros v m vs.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_invoke & pi_ctx & A_eq).
  simpl in pi_invoke.
  destruct v, E; try destruct v; try now destruct pi_invoke;
    try now (destruct Ctx; try destruct j; discriminate red_st).
  destruct pi_invoke as (pi_l & pi_vs & m_eq).
  destruct A.
    destruct Ctx, l; try destruct j0; try discriminate red_st.
  destruct l.
  + assert (Some (h1, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    assert (l0_eq : l0 = null).
      now destruct l0; try destruct pi_l.
    injection H; intros h_eq st_eq.
    exists h1_base, h2_base, h2, (Ctx0 [[ JFVal1 NPE_val ]]_ NPE_mode :: st2), pi.
    rewrite <-st_eq, <-h_eq, <-A_eq, l0_eq.
    unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
    simpl in h1_union, h2_union.
    assert (asdf : Heap.In (elt:=Obj) NPE_object_loc h1_base). admit.
    assert (qwer : Heap.In (elt:=Obj) NPE_object_loc h2_base). admit.
    split; [ | split; [ | split; [| split; [ | split]]]]; try easy.
    now destruct Ctx0; try destruct j.
  + assert (getInvokeBody CC (getClassName h1 n) n m vs h1 Ctx st1' = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    destruct l0; try now destruct pi_l.
    rewrite <-m_eq, <-A_eq in *.
    destruct (ExistsBodyWithSameFreeVars Ctx Ctx0 h1_base h1_rest h1 hn1 h2_base h2_rest h2 n n0 vs vs0 st1' stn1 st2 m pi CC)
    as (h_eq & stn2 & pi_stn & h1_union' & h2_union' & invoke); try easy.
    exists h1_base, h2_base, h2, stn2, pi.
    rewrite h_eq.
    split; [ | split; [ | split; [ split; [ | split] | split; [ | split]]]]; try easy.
    now destruct Ctx0; try destruct j; simpl.
Admitted.

Lemma ModifyFieldOnConsistentHeap : forall (h : Heap) l ro cid f n,
  HeapConsistent h ->
  Heap.MapsTo n (ro, cid) h ->
  LocMapsToHeap l h ->
  HeapConsistent (Heap.add n (JFXIdMap.add f l ro, cid) h).
Proof.
  intros h l ro cid f n.
  intros consistent n_ro_h l_h.
  intros n' o' f' fn' n'_o' f'_fn'.
  destruct (Classical_Prop.classic (n = fn')).
    exists (JFXIdMap.add f l ro, cid).
    now rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o.
  destruct (Classical_Prop.classic (n = n')).
  + rewrite <-H0 in *; clear H0 n'.
    rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o in n'_o'; trivial.
    injection n'_o' as o'_eq.
    rewrite <-o'_eq in *; clear o'_eq.
    simpl in f'_fn'.
    apply JFXIdMapFacts.find_mapsto_iff in f'_fn'.
    destruct (Classical_Prop.classic (f = f')).
    ++ rewrite <-H0 in *; clear H0 f'.
       rewrite JFXIdMapFacts.add_eq_o in f'_fn'; trivial.
       injection f'_fn' as l_eq.
       rewrite l_eq in *.
       simpl in l_h.
       apply HeapFacts.elements_in_iff in l_h as (o & fn'_o).
       exists o.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in fn'_o.
       now rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o.
    ++ rewrite JFXIdMapFacts.add_neq_o, <-JFXIdMapFacts.find_mapsto_iff in f'_fn'; trivial.
       destruct (consistent n (ro, cid) f' fn') as (o & fn'_o); try easy.
       exists o.
       apply HeapFacts.find_mapsto_iff in fn'_o.
       now rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o.
  + rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o, <-HeapFacts.find_mapsto_iff in n'_o'; trivial.
    destruct (consistent n' o' f' fn' n'_o' f'_fn') as (o & fn'_o).
    exists o.
    now rewrite HeapFacts.find_mapsto_iff, HeapFacts.add_neq_o, <-HeapFacts.find_mapsto_iff.
Qed.

Lemma ExtendUnionOfFreeVarsAndRest : forall h_base h_rest h n ro f l cid Ctx st,
  Heap.MapsTo n (ro, cid) h_base ->
  DisjointUnionOfLocsInStackAndRest ((Ctx [[JFVal1 (JFVLoc l) ]]_ None) :: st)
    h_base h_rest h ->
  DisjointUnionOfLocsInStackAndRest ((Ctx [[JFVal1 (JFVLoc l) ]]_ None) :: st)
    (Heap.add n (JFXIdMap.add f l ro, cid) h_base) h_rest
    (Heap.add n (JFXIdMap.add f l ro, cid) h).
Proof.
  intros h_base h_rest h n ro f l cid Ctx st.
  intros n_ro union.
  unfold DisjointUnionOfLocsInStackAndRest in *.
  assert (n_in_base : Heap.In n h_base).
    apply HeapFacts.elements_in_iff.
    exists (ro, cid).
    now apply HeapFacts.elements_mapsto_iff.
 destruct union as (locs_in_base & base_consistent & (union & disjoint)).
  split; [ | split].
  + simpl in *.
    split; [ split; [ | split] | ]; try easy.
    ++ destruct l; try easy.
       now apply InExtendedHeap.
    ++ admit.
    ++ admit.
  + apply ModifyFieldOnConsistentHeap; try easy.
    destruct l; try easy.
    apply locs_in_base.
  + unfold JFIDisjointUnion.
    split.
    ++ apply ExtendDisjointUnion; try easy.
       intros n_in_rest.
       now apply (disjoint n).
    ++ intros n' (n'_in_base & n'_in_rest).
       destruct (Classical_Prop.classic (n = n')).
       +++ rewrite <-H in *.
           now apply (disjoint n).
       +++ apply (disjoint n').
           split; try easy.
           rewrite HeapFacts.elements_in_iff in n'_in_base |- *.
           destruct n'_in_base as (o' & n'_o').
           exists o'.
           rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n'_o' |- *.
           now rewrite HeapFacts.add_neq_o in n'_o'.
Admitted.

Lemma AssignReductionDependsOnFreeVars: forall vx v,
   ExprReductionDependsOnFreeVars (JFAssign vx v).
 Proof.
  intros (v1 & f1) v1'.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_assign & pi_ctx & A_eq).
  simpl in pi_assign.

  destruct E; try now destruct pi_assign.
  set (v2' := v); replace v with v2' in *; try easy.
  destruct vx as (v2 & f2).
  destruct pi_assign as (f_eq & pi_v & pi_v').
  destruct A.
    destruct Ctx, v1, v1'; try destruct j0;
    try destruct l; try destruct l0; try discriminate red_st.
  rewrite <-f_eq, <-A_eq.
  destruct v1 as [l1 | ]; try destruct l1.
  + assert (Some (h1, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st1') = Some (hn1, stn1)).
      now destruct Ctx, v1'; try destruct j.
    injection H as h_eq st_eq.
    assert (v1_eq : v2 = JFnull).
      unfold ValPermuted in pi_v.
      destruct v2; try destruct pi_v.
      unfold PiMapsTo in pi_v.
      now destruct l.
    exists h1_base, h2_base, h2, (Ctx0 [[ JFVal1 NPE_val ]]_ NPE_mode :: st2), pi.
    rewrite <-st_eq, <-h_eq, v1_eq.
    unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
    simpl in h1_union, h2_union.
    assert (asdf : Heap.In (elt:=Obj) NPE_object_loc h1_base). admit.
    assert (qwer : Heap.In (elt:=Obj) NPE_object_loc h2_base). admit.
    split; [ | split; [ | split; [| split; [ | split]]]]; try easy.
    destruct v1', v2'; try destruct pi_v'.
    now destruct Ctx0; try destruct j.
    now destruct Ctx; try destruct j; try discriminate red_st.
  + destruct v1'; try (destruct Ctx; try destruct j; now discriminate red_st).
    assert (exists ro cid, Heap.find n h1 = Some (ro, cid)).
      destruct (Heap.find (elt:=Obj) n h1); try (destruct Ctx; try destruct j; now discriminate red_st).
      exists (fst o), (snd o).
      now destruct o.
    destruct H as (ro & cid & n_h_ro).
    rewrite n_h_ro in red_st.
    assert (Some (Heap.add n (JFXIdMap.add f1 l ro, cid) h1, (Ctx [[ JFVal1 (JFVLoc l) ]]_ None) :: st1') =
        Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    destruct v2 as [l2 |]; try destruct l2 as [| n2]; try now destruct pi_v.
    destruct v2' as [l2 |]; try now destruct pi_v'.
    assert (exists ro2, Heap.find n2 h2_base = Some (ro2, cid)).
      apply ExistsInPermutedHeap with (n := n) (h := h1_base) (pi := pi) (ro := ro); try easy.
      rewrite <-HeapFacts.find_mapsto_iff in n_h_ro |- *.
      apply InSubheap with (h := h1); try easy; now apply h1_union.
    destruct H as (ro2 & n2_ro2).
    set (hn1_base := Heap.add n (JFXIdMap.add f1 l ro, cid) h1_base).
    set (hn2_base := Heap.add n2 (JFXIdMap.add f1 l2 ro2, cid) h2_base).
    set (hn2 := Heap.add n2 (JFXIdMap.add f1 l2 ro2, cid) h2).
    assert (pi_hn_base : HeapsPermuted hn1_base hn2_base pi).
      unfold hn1_base, hn2_base.
      apply ChangeFieldInPermutedHeaps; try easy.
      rewrite <-HeapFacts.find_mapsto_iff in n_h_ro |- *.
      apply InSubheap with (h := h1); try easy; now apply h1_union.
    exists hn1_base, hn2_base, hn2, ((Ctx0 [[JFVal1 (JFVLoc l2) ]]_ None) :: st2), pi.
    rewrite <-st_eq, <-h_eq.
    unfold hn2.
    unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
    simpl in h1_union, h2_union.
    split; [ | split; [ | split; [| split; [ | split]]]]; try easy.
    ++ unfold hn1_base.
       intros n' n'_in_pi.
       destruct (Classical_Prop.classic (n = n')).
       +++ apply HeapFacts.elements_in_iff.
           exists (JFXIdMap.add f1 l ro, cid).
           now rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o.
       +++ assert (pi_in_hn1 := pi_in_h1 n' n'_in_pi).
           apply HeapFacts.elements_in_iff in pi_in_hn1 as (ro' & n'_ro').
           apply HeapFacts.elements_in_iff.
           exists ro'.
           rewrite <-HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n'_ro' |- *.
           now rewrite HeapFacts.add_neq_o.
    ++ unfold hn1_base.
       apply ExtendUnionOfFreeVarsAndRest; try easy.
       apply HeapFacts.find_mapsto_iff in n_h_ro.
       apply InSubheap with (h := h1); try easy.
       apply h1_union.
    ++ unfold hn2_base.
       apply ExtendUnionOfFreeVarsAndRest; try easy.
       apply HeapFacts.find_mapsto_iff in n2_ro2.
       apply InSubheap with (h := h2); try easy.
       apply h2_union.
       now apply h2_union in n2_ro2.
    ++ simpl.
       apply HeapFacts.find_mapsto_iff, h2_union, HeapFacts.find_mapsto_iff in n2_ro2.
       rewrite n2_ro2.
       now destruct Ctx0; try destruct j.
  + destruct Ctx; try destruct j; try discriminate red_st.
Admitted.

Lemma LocsInSubstValAreInHeap : forall v h y l,
  LocMapsToHeap l h ->
  LocsInValAreInHeap v h ->
  LocsInValAreInHeap (substVal (JFVar y) l v) h.
Proof.
  intros v h y l l_in_h v_in_h.
  unfold substVal.
  destruct v; try easy.
  now destruct (JFRef_dec (JFVar y) x ).
Qed.
Hint Resolve LocsInSubstValAreInHeap : locs_in_subst.

Lemma LocsInSubstValsAreInHeap : forall vs y h l,
  LocMapsToHeap l h ->
  LocsInValsAreInHeap vs h ->
  LocsInValsAreInHeap (map (substVal (JFVar y) l) vs) h.
Proof.
  intros vs.
  induction vs; try easy.
  intros y h l l_in_h vs_in_h.
  simpl in *.
  destruct vs_in_h.
  eauto with locs_in_subst.
Qed.
Hint Resolve LocsInSubstValsAreInHeap : locs_in_subst.

Lemma LocsInSubstExprAreInHeap : forall e y l h,
  LocMapsToHeap l h ->
  LocsInExprAreInHeap e h ->
  LocsInExprAreInHeap (substExpr (JFVar y) l e) h.
Proof.
  intros e.
  induction e; intros y l h l_in_h e_in_h;
    unfold LocsInExprAreInHeap, substExpr;
    fold substExpr; fold LocsInExprAreInHeap;
    try destruct vx;
    eauto with locs_in_subst.
  + destruct e_in_h.
    destruct (JFRef_dec (JFVar x) (JFVar y)); simpl in *; eauto with locs_in_subst.
  + destruct e_in_h as (v1_in_h & v2_in_h & e1_in_h & e2_in_h).
    split; [ | split; [ | split]]; eauto with locs_in_subst.
  + destruct e_in_h.
    eauto with locs_in_subst.
  + destruct e_in_h.
    split; eauto with locs_in_subst.
  + simpl in *.
    eauto with locs_in_subst.
  + destruct e_in_h.
    destruct (JFRef_dec (JFVar x) (JFVar y)); simpl in *; eauto with locs_in_subst.
Qed.

Lemma VarNotFreeInSubstVal : forall v y l,
  ~VarFreeInJFVal y ((substVal (JFVar y) l) v).
Proof.
  intros v y l y_free.
  unfold VarFreeInJFVal, substVal in y_free.
  destruct v; try destruct y_free.
  destruct (JFRef_dec (JFVar y) x); try destruct y_free.
  destruct x; try destruct y_free.
  now apply n.
Qed.

Lemma VarNotFreeInSubstVals : forall vs y l,
  ~VarFreeInJFVals y (map (substVal (JFVar y) l) vs).
Proof.
  intros vs.
  induction vs; try easy.
  intros y l y_free.
  simpl in y_free.
  destruct y_free.
  + now apply VarNotFreeInSubstVal in H.
  + now apply IHvs in H.
Qed.

Lemma VarNotFreeInSubstExpr : forall e y l,
  ~VarFreeInExpr y (substExpr (JFVar y) l e).
Proof.
  intros e.
  induction e; intros y l y_free.
  + simpl in y_free.
    destruct vs; destruct y_free.
    now apply VarNotFreeInSubstVal in H.
    now apply VarNotFreeInSubstVals in H.
  + unfold substExpr in y_free.
    fold substExpr in y_free.
    destruct (JFRef_dec (JFVar x) (JFVar y)); destruct y_free.
    ++ now apply IHe1 in H.
    ++ apply H.
       now injection e.
    ++ now apply IHe1 in H.
    ++ destruct H as (_ & H).
       now apply IHe2 in H.
  + destruct y_free as [free_in_v1 | [free_in_v2 | [free_in_e1 | free_in_e2]]].
    now apply VarNotFreeInSubstVal in free_in_v1.
    now apply VarNotFreeInSubstVal in free_in_v2.
    now apply IHe1 in free_in_e1.
    now apply IHe2 in free_in_e2.
  + destruct y_free.
    now apply VarNotFreeInSubstVal in H.
    now apply VarNotFreeInSubstVals in H.
  + destruct vx.
    destruct y_free; now apply VarNotFreeInSubstVal in H.
  + simpl in y_free.
    now apply VarNotFreeInSubstVal in y_free.
  + destruct vx.
    simpl in y_free.
    now apply VarNotFreeInSubstVal in y_free.
  + simpl in y_free.
    now apply VarNotFreeInSubstVal in y_free.
  + unfold substExpr in y_free.
    fold substExpr in y_free.
    destruct (JFRef_dec (JFVar x) (JFVar y)); destruct y_free.
    ++ now apply IHe1 in H.
    ++ apply H.
       now injection e.
    ++ now apply IHe1 in H.
    ++ destruct H as (_ & H).
       now apply IHe2 in H.
Qed.

Lemma VarFreeInSubstVal : forall v y z l,
  VarFreeInJFVal z ((substVal (JFVar y) l) v) ->
  VarFreeInJFVal z v.
Proof.
  intros v y z l z_free.
  destruct v; try easy.
  destruct x; try easy.
  unfold VarFreeInJFVal in *.
  unfold substVal in z_free.
  now destruct (JFRef_dec (JFVar y) (JFVar x)).
Qed.

Lemma VarFreeInSubstVals : forall vs y z l,
  VarFreeInJFVals z (map (substVal (JFVar y) l) vs) ->
  VarFreeInJFVals z vs.
Proof.
  intros vs.
  induction vs; try easy.
  intros y z l z_free.
  simpl in *.
  destruct z_free.
  + apply or_introl.
    now apply VarFreeInSubstVal in H.
  + apply or_intror.
    now apply IHvs in H.
Qed.

Lemma VarFreeInSubstExpr : forall e y z l,
  VarFreeInExpr z (substExpr (JFVar y) l e) ->
  VarFreeInExpr z e.
Proof.
  intros e.
  induction e; intros y z l z_free.
  + now apply VarFreeInSubstVals in z_free.
  + unfold substExpr in z_free.
    fold substExpr in z_free.
    destruct (JFRef_dec (JFVar x) (JFVar y)); destruct z_free.
    ++ apply IHe1 in H.
       now apply or_introl.
    ++ now apply or_intror.
    ++ apply IHe1 in H.
       now apply or_introl.
    ++ destruct H as (z_eq & z_free).
       apply IHe2 in z_free.
       now apply or_intror.
  + destruct z_free as [free_in_v1 | [free_in_v2 | [free_in_e1 | free_in_e2]]].
    ++ apply VarFreeInSubstVal in free_in_v1.
       now apply or_introl.
    ++ apply VarFreeInSubstVal in free_in_v2.
       now apply or_intror, or_introl.
    ++ apply IHe1 in free_in_e1.
       now apply or_intror, or_intror, or_introl.
    ++ apply IHe2 in free_in_e2.
       now apply or_intror, or_intror, or_intror.
  + simpl in z_free |- *.
    destruct z_free.
    ++ apply or_introl.
       now apply VarFreeInSubstVal in H.
    ++ apply or_intror.
       now apply VarFreeInSubstVals in H.
  + destruct vx.
    simpl in z_free |- *.
    destruct z_free; apply VarFreeInSubstVal in H.
    ++ now apply or_introl.
    ++ now apply or_intror.
  + simpl in z_free |- *.
    now apply VarFreeInSubstVal in z_free.
  + destruct vx.
    simpl in z_free |- *.
    now apply VarFreeInSubstVal in z_free.
  + simpl in z_free |- *.
    now apply VarFreeInSubstVal in z_free.
  + unfold substExpr in z_free.
    fold substExpr in z_free.
    destruct (JFRef_dec (JFVar x) (JFVar y)); destruct z_free.
    ++ apply IHe1 in H.
       now apply or_introl.
    ++ now apply or_intror.
    ++ apply IHe1 in H.
       now apply or_introl.
    ++ destruct H as (z_eq & z_free).
       apply IHe2 in z_free.
       now apply or_intror.
Qed.

Lemma NoFreeVarsAfterOnlyVarSubst : forall e y l,
  OnlyFreeVar e y ->
  NoFreeVars (substExpr (JFVar y) l e).
Proof.
  intros.
  intros z z_free.
  unfold OnlyFreeVar, NoFreeVars in *.
  replace z with y in *.
  + now apply VarNotFreeInSubstExpr in z_free.
  + apply VarFreeInSubstExpr in z_free.
    now apply H.
Qed.

Lemma LetGoPreservesFreeVars : forall Ctx Ctx1 C x e l j st h_base h_rest h,
  DisjointUnionOfLocsInStackAndRest
    (Ctx _[ JFCtxLet C x Ctx1 e _[[_ JFVal1 (JFVLoc l) _]]_ Some j ]_ :: st)
    h_base h_rest h ->
  DisjointUnionOfLocsInStackAndRest
    ((Ctx [[substExpr (JFVar x) l e ]]_ None) :: st)
    h_base h_rest h.
Proof.
  intros Ctx Ctx1 C x e l j st h_base h_rest h.
  intros union.
  destruct union as (locs_in_h & h_consistent & union).
  split; [ | split]; try easy.
  simpl in locs_in_h |- *.
  split; [split; [ | split] |]; try easy.
  unfold LocsInStackAreInHeap in locs_in_h.
  fold LocsInStackAreInHeap in locs_in_h.
  now apply LocsInSubstExprAreInHeap.
  now apply NoFreeVarsAfterOnlyVarSubst.
Qed.

Lemma TryGoPreservesFreeVars : forall Ctx Ctx1 mu C x e l j st h_base h_rest h,
  DisjointUnionOfLocsInStackAndRest
    (Ctx _[ JFCtxTry Ctx1 mu C x e _[[_ JFVal1 (JFVLoc l) _]]_ Some j ]_ :: st)
    h_base h_rest h ->
  DisjointUnionOfLocsInStackAndRest
    ((Ctx [[substExpr (JFVar x) l e ]]_ None) :: st)
    h_base h_rest h.
Proof.
  intros Ctx Ctx1 mu C x e l j st h_base h_rest h.
  intros union.
  destruct union as (locs_in_h & h_consistent & union).
  split; [ | split]; try easy.
  simpl in locs_in_h |- *.
  split; [split; [ | split] |]; try easy.
  unfold LocsInStackAreInHeap in locs_in_h.
  fold LocsInStackAreInHeap in locs_in_h.
  now apply LocsInSubstExprAreInHeap.
  now apply NoFreeVarsAfterOnlyVarSubst.
Qed.

Lemma Val1ReductionDependsOnFreeVars : forall v,
   ExprReductionDependsOnFreeVars (JFVal1 v).
Proof.
  intros v.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_val1 & pi_ctx & A_eq).
  rewrite <-A_eq in *.
  simpl in pi_val1.
  destruct E; try now destruct pi_val1.
  destruct A.
  + destruct Ctx; [ | destruct j0].
    ++ destruct v, st1'; try destruct f; try destruct E, A; try discriminate red_st.
       injection red_st as h1_eq stn1_eq.
       destruct Ctx0; try destruct pi_ctx.
       destruct st2; try destruct f; try now destruct pi_st.
       simpl in pi_st.
       destruct pi_st as (pi_f & pi_st).
       destruct E, A; try now destruct pi_f.
       unfold FramesPermuted in pi_f.
       destruct pi_f as (pi_e & pi_ctx & _).
       destruct pi_e as (pi_v & pi_vs & m_eq).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-m_eq, <-h1_eq, <-stn1_eq.
       unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
       simpl in h1_union, h2_union.
       now exists h1_base, h2_base, h2, (Ctx0 [[ JFVal1 (JFVLoc l') ]]_ Some j :: st2), pi.
    ++ destruct v; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct j0; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct pi_ctx as ((C_eq & x_eq & pi_e) & pi_ctxs).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-h0_eq, <-st_eq.
       unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
       simpl in h1_union, h2_union.
       now exists h1_base, h2_base, h2, (Ctx0 [[JFVal1 (JFVLoc l') ]]_ Some j :: st2), pi.
    ++ destruct v; try discriminate red_st.
       destruct Ctx0; try destruct j0; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       destruct pi_ctx as ((C_eq & x_eq & pi_e) & pi_ctxs).
       rewrite <-C_eq, <-x_eq in *.
       replace hn1 with h1;
         [ | destruct (subtype_bool CC (JFClass j) (JFClass C)); now injection red_st].
       destruct (Classical_Prop.classic (Is_true (subtype_bool CC (JFClass j) (JFClass C)))).
       +++ unfold red.
           destruct (subtype_bool CC (JFClass j) (JFClass C)); try destruct H.
           injection red_st as h_eq st_eq.
           rewrite <-st_eq.
           exists h1_base, h2_base, h2,
            ((Ctx0 [[substExpr (JFVar x) l' E0 ]]_ None) :: st2), pi.
           unfold red.           split; [ | split; [ | split; [ split; [ | split] | split; [ | split]]]]; try easy.
           - split; try easy.
             unfold FramesPermuted.
             split; try split; try easy.
             now apply SubstPermutedExpr.
           -  now apply TryGoPreservesFreeVars in h1_union.
           -  now apply TryGoPreservesFreeVars in h2_union.
       +++ unfold red.
           destruct (subtype_bool CC (JFClass j) (JFClass C)); try now (exfalso; now apply H).
           injection red_st as h_eq st_eq.
           rewrite <-st_eq.
           unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
           simpl in h1_union, h2_union.
           now exists h1_base, h2_base, h2,
            ((Ctx0 [[JFVal1 (JFVLoc l') ]]_ Some j) :: st2), pi.
  + destruct Ctx; [ | destruct j].
    ++ destruct v, st1'; try destruct f; try destruct E, A; try discriminate red_st.
       injection red_st as h_eq st_eq.
       destruct Ctx0; try destruct pi_ctx.
       destruct st2; try destruct f; try now destruct pi_st.
       simpl in pi_st.
       destruct pi_st as (pi_f & pi_st).
       destruct E, A; try now destruct pi_f.
       unfold FramesPermuted in pi_f.
       destruct pi_f as (pi_e & pi_ctx & _).
       destruct pi_e as (pi_v & pi_vs & m_eq).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-m_eq, <-h_eq, <-st_eq.
       unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
       simpl in h1_union, h2_union.
       now exists h1_base, h2_base, h2, (Ctx0 [[ JFVal1 (JFVLoc l') ]]_ None:: st2), pi.
    ++ destruct v; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct j; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct pi_ctx as ((C_eq & x_eq & pi_e) & pi_ctxs).
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-h0_eq, <-st_eq, <-x_eq in *.
       exists h1_base, h2_base, h2, (Ctx0 [[ substExpr (JFVar x) l' E0 ]]_ None:: st2), pi.
       split; [ | split; [ | split; [ split; [ | split] | split; [ | split]]]]; try easy.
       +++ split; try easy.
           unfold FramesPermuted.
           split; try split; try easy.
           now apply SubstPermutedExpr.
       +++ now apply LetGoPreservesFreeVars in h1_union.
       +++ now apply LetGoPreservesFreeVars in h2_union.
    ++ destruct v; try discriminate red_st.
       injection red_st as h0_eq st_eq.
       destruct Ctx0; try destruct j0; try now destruct pi_ctx.
       simpl in pi_ctx.
       destruct v0 as [ l' | ]; try now destruct pi_val1.
       unfold ValPermuted in pi_val1.
       rewrite <-h0_eq, <-st_eq.
       unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
       simpl in h1_union, h2_union.
       now exists h1_base, h2_base, h2, (Ctx0 [[ JFVal1 (JFVLoc l') ]]_ None:: st2), pi;
          destruct j.
Qed.

Lemma Val2ReductionDependsOnFreeVars : forall vx,
   ExprReductionDependsOnFreeVars (JFVal2 vx).
Proof.
  intros (v, f).
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f0.
  destruct pi_f as (pi_val2 & pi_ctx & A_eq).
  simpl in pi_val2.
  destruct E; try now destruct pi_val2.
  destruct vx as (v', f').
  destruct pi_val2 as (f_eq & pi_v).
  destruct A; try now (destruct Ctx, v; try destruct j0; try destruct l; discriminate red_st).
  destruct v as [ l |]; try destruct l.
  + destruct v' as [ l' |]; try destruct l'; try now destruct pi_v.
    assert (Some (h1, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H as h_eq st'_eq.
    rewrite <-h_eq, <-st'_eq, <-A_eq.
    exists h1_base, h2_base, h2, ((Ctx0 [[JFVal1 NPE_val ]]_ NPE_mode) :: st2), pi.
    unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
    assert (asdf : Heap.In (elt:=Obj) NPE_object_loc h1_base). admit.
    assert (qwer : Heap.In (elt:=Obj) NPE_object_loc h2_base). admit.
    simpl in h1_union, h2_union.
    split; [ | split; [ | split; [ | split; [ | split]]]]; try easy.
    now destruct Ctx0; try destruct j.
  + destruct v' as [ l' |]; try destruct l' as [ | n']; try now destruct pi_v.
    unfold ValPermuted in pi_v.
    destruct pi_base as (bijection & locs_fst & locs_snd & objs).
    assert (exists o, Heap.find n h1 = Some o).
      destruct (Heap.find n h1) as [ o |].
      now exists o.
      now destruct Ctx; try destruct j.
    destruct H as (o & n_o).
    rewrite n_o in red_st.
    apply HeapFacts.find_mapsto_iff in n_o.
    apply InSubheap with (h' := h1_base) in n_o; try easy; try now apply h1_union.
    destruct (locs_fst n) as (n'' & n_n'' & n'_h0_perm).
      apply HeapFacts.elements_in_iff.
      exists o.
      now apply HeapFacts.elements_mapsto_iff.
    apply MapsToEq with (n2 := n') in n_n''; try easy.
    rewrite <-n_n'' in *; clear n_n'' n''.
    unfold ObjsPermuted in objs.
    apply HeapFacts.elements_in_iff in n'_h0_perm as (o' & n'_o').
    apply HeapFacts.elements_mapsto_iff in n'_o'.
    destruct o as (ro & cn), o' as (ro' & cn').
    destruct (objs n n' (ro, cn) (ro', cn') pi_v n_o n'_o') as (cn_eq & pi_o).
    rewrite <-cn_eq in *; clear cn_eq cn'.
    destruct (pi_o f) as (same_keys & _ & pi_f).
    assert (exists l, JFXIdMap.find f ro = Some l).
      destruct (JFXIdMap.find f ro).
      now exists l.
      now destruct Ctx; try destruct j; discriminate red_st.
    destruct H as (l & f_l).
    rewrite f_l in red_st.
    apply JFXIdMapFacts.find_mapsto_iff in f_l.
    destruct (same_keys l) as (l' & f_l'); trivial.
    assert (pi_l := pi_f l l' f_l f_l').
    assert (Some (h1, (Ctx [[JFVal1 (JFVLoc l) ]]_ None) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    rewrite <-h_eq, <-st_eq, <-A_eq, <-f_eq.
    unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
    simpl in h1_union, h2_union.
    exists h1_base, h2_base, h2, ((Ctx0 [[JFVal1 (JFVLoc l') ]]_ None) :: st2), pi.
    split; [ | split; [ | split; [ | split; [ | split]]]]; try easy.
    ++ split; [ | split]; try easy.
       simpl.
       split; [ split; [ | split] | ]; try easy.
       destruct h1_union as (locs_in_h1 & (h1_consistent & h1_union)).
       destruct l; trivial.
       destruct (h1_consistent n (ro, cn) f n0) as (o0 & n0_o0); trivial.
       apply HeapFacts.elements_in_iff.
       exists o0.
       now apply HeapFacts.elements_mapsto_iff.
    ++ split; [ | split]; try easy.
       simpl.
       split; [ split; [ | split] | ]; try easy.
       destruct h2_union as (locs_in_h2 & (h2_consistent & h2_union)).
       destruct l'; trivial.
       destruct (h2_consistent n' (ro', cn) f n0) as (o0 & n0_o0); trivial.
       apply HeapFacts.elements_in_iff.
       exists o0.
       now apply HeapFacts.elements_mapsto_iff.
    ++ simpl.
       apply HeapFacts.find_mapsto_iff in n'_o'.
       rewrite FindInUnion with (h1 := h2_base) (h2 := h2_rest) (o := (ro', cn)); trivial.
       apply JFXIdMapFacts.find_mapsto_iff in f_l'.
       rewrite f_l'.
       now destruct Ctx0; try destruct j.
       now apply h2_union.
  + now destruct Ctx; try destruct j.
Admitted.

Lemma ThrowReductionDependsOnFreeVars : forall v,
   ExprReductionDependsOnFreeVars (JFThrow v).
Proof.
  intros v.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_throw & pi_ctx & A_eq).
  simpl in pi_throw.
  destruct E; try now destruct pi_throw.
  destruct A; try now (destruct Ctx, v; try destruct j0; try destruct l; discriminate red_st).
  unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
  simpl in h1_union, h2_union.
  destruct v as [ l | ]; try destruct l.
  + assert (Some (h1, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    destruct v0; try destruct l; try now destruct pi_throw.
    assert (npe_in_h1 : Heap.In (elt:=Obj) NPE_object_loc h1_base). admit.
    assert (npe_in_h2 : Heap.In (elt:=Obj) NPE_object_loc h2_base). admit.
    rewrite <-h_eq, <-st_eq, <-A_eq.
    exists h1_base, h2_base, h2, ((Ctx0 [[JFVal1 NPE_val ]]_ NPE_mode) :: st2), pi.
    split; [ | split; [ | split; [ | split]]]; try easy.
    now destruct Ctx0; try destruct j.
  + rewrite ClassNameClassEq in red_st;
      [ | apply InSuperheap with (h1 := h1_base); apply h1_union].
    rewrite <-SubheapPreservesClassName with (h' := h1_base) in red_st; try easy; try apply h1_union.
    assert (exists cn, getClassName h1_base n = Some cn).
      destruct (getClassName h1_base n); try now (destruct Ctx; try destruct j; discriminate red_st).
      now exists j.
    destruct H as (cn & n_cn).
    rewrite n_cn in red_st.
    destruct v0; try destruct l as [ | n']; try now destruct pi_throw.
    unfold ValPermuted in pi_throw.
    assert (n'_cn : class h2 n' = Some cn).
      rewrite ClassNameClassEq; [ | now apply InSuperheap with (h1 := h2_base); apply h2_union].
      rewrite <-SubheapPreservesClassName with (h' := h2_base); try easy; try apply h2_union.
      now apply PermutedClass with (h' := h2_base) (n' := n') (pi := pi) in n_cn.
    assert (Some (h1, (Ctx [[ JFVal1 (JFVLoc (JFLoc n)) ]]_ Some cn) :: st1') = Some (hn1, stn1)).
      now destruct Ctx; try destruct j.
    injection H as h_eq st_eq.
    rewrite <-h_eq, <-st_eq, <-A_eq.
    exists h1_base, h2_base, h2, ((Ctx0 [[JFVal1 (JFVLoc (JFLoc n')) ]]_ Some cn) :: st2), pi.
    split; [ | split; [ | split; [ | split; [ | split]]]]; try easy.
    simpl.
    rewrite n'_cn.
    now destruct Ctx0; try destruct j.
  + now destruct Ctx; try destruct j.
Admitted.

Lemma TryReductionDependsOnFreeVars : forall e1 mu cn x e2,
   ExprReductionDependsOnFreeVars (JFTry e1 mu cn x e2).
Proof.
  intros e1 mu cn x e2.
  intros Ctx A h1_base h1_rest h1 st1' h2_base h2_rest h2 st2 hn1 stn1 CC pi st1.
  unfold st1 in *.
  clear st1.
  unfold EverythingPermuted.
  intros pi_in_h1 (pi_npe & pi_base & pi_st) h1_union h2_union red_st.
  unfold red in red_st.
  simpl in pi_st.
  destruct st2; [ destruct pi_st |].
  destruct pi_st as (pi_f & pi_st).
  unfold FramesPermuted in pi_f.
  destruct f.
  destruct pi_f as (pi_try & pi_ctx & A_eq).
  simpl in pi_try.
  destruct E; try now destruct pi_try.
  destruct pi_try as (mu_eq & cn_eq & x_eq & pi_e1 & pi_e2).
  rewrite <-mu_eq, <-cn_eq, <-x_eq, <-A_eq in *.
  destruct A.
    destruct Ctx; try destruct j0; try discriminate red_st.
  assert (Some (h1, Ctx _[ JFCtxTry __ mu cn x e2 _[[_ e1 _]]_ None ]_ :: st1') = Some (hn1, stn1)).
    now destruct Ctx; try destruct j.
  injection H as st_eq h_eq.
  exists h1_base, h2_base, h2, (Ctx0 _[ JFCtxTry __ mu cn x E2 _[[_ E1  _]]_ None]_ :: st2), pi.
  rewrite <-st_eq, <-h_eq.
  unfold DisjointUnionOfLocsInStackAndRest in h1_union, h2_union.
  simpl in h1_union, h2_union.
  assert (NoFreeVars e1 /\ OnlyFreeVar e2 x).
    split; now apply (NoFreeVarsInTryExprs e1 mu cn x e2).
  destruct H as (no_free_e1 & only_free_e2).
  assert (NoFreeVars E1 /\ OnlyFreeVar E2 x).
    split; now apply (NoFreeVarsInTryExprs E1 mu cn x E2).
  destruct H as (no_free_E1 & only_free_E2).
  split; [ | split; [ | split; [| split; [ | split]]]]; try easy.
  now destruct Ctx0; try destruct j.
Qed.

Lemma ReductionDependsOnFreeVars : forall h1_base h1_rest h1 st1 h2_base h2_rest h2 st2 hn1 stn1 CC pi,
  EverythingPermuted h1_base h2_base st1 st2 pi ->
  PiOnlyFromHeap pi h1_base ->
  DisjointUnionOfLocsInStackAndRest st1 h1_base h1_rest h1 ->
  DisjointUnionOfLocsInStackAndRest st2 h2_base h2_rest h2 ->
  red CC (h1, st1) = Some (hn1, stn1) ->
  exists hn1_base hn2_base hn2 stn2 pi',
    PermutationSubset pi pi' /\
    PiOnlyFromHeap pi' hn1_base /\
    EverythingPermuted hn1_base hn2_base stn1 stn2 pi' /\
    DisjointUnionOfLocsInStackAndRest stn1 hn1_base h1_rest hn1 /\
    DisjointUnionOfLocsInStackAndRest stn2 hn2_base h2_rest hn2 /\
    red CC (h2, st2) = Some (hn2, stn2).
Proof.
  intros h1_base h1_rest h1 st1 h2_base h2_rest h2 st2 hn1 stn1 CC pi.
  intros pi_in_h1 pi_everything h1_union h2_union h1_red.
  destruct st1; try now discriminate h1_red.
  destruct f, E.
  + now apply (NewReductionDependsOnFreeVars mu cn vs)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (LetReductionDependsOnFreeVars cn x E1 E2)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (IfReductionDependsOnFreeVars v1 v2 E1 E2)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (InvokeReductionDependsOnFreeVars v m vs)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (AssignReductionDependsOnFreeVars vx v)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (Val1ReductionDependsOnFreeVars v)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (Val2ReductionDependsOnFreeVars vx)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (ThrowReductionDependsOnFreeVars v)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
  + now apply (TryReductionDependsOnFreeVars E1 mu cn x E2)
      with (Ctx := Ctx) (h1_base := h1_base) (h1 := h1) (h2_base := h2_base) (A := A) (st1' := st1).
Qed.

Lemma PartialEvaluationDependsOnFreeVars : forall confs1 h1_base h1_rest h1 st1 h2_base h2_rest h2 st2 hn1 stn1 CC pi,
  EverythingPermuted h1_base h2_base st1 st2 pi ->
  PiOnlyFromHeap pi h1_base ->
  DisjointUnionOfLocsInStackAndRest st1 h1_base h1_rest h1 ->
  DisjointUnionOfLocsInStackAndRest st2 h2_base h2_rest h2 ->
  JFIPartialEval h1 st1 confs1 hn1 stn1 CC ->
  exists hn1_base confs2 hn2_base hn2 stn2 pi',
    PermutationSubset pi pi' /\
    PiOnlyFromHeap pi' hn1_base /\
    EverythingPermuted hn1_base hn2_base stn1 stn2 pi' /\
    DisjointUnionOfLocsInStackAndRest stn1 hn1_base h1_rest hn1 /\
    DisjointUnionOfLocsInStackAndRest stn2 hn2_base h2_rest hn2 /\
    JFIPartialEval h2 st2 confs2 hn2 stn2 CC.
Proof.
  intros confs1.
  induction confs1;
    intros h1_base h1_rest h1 st1 h2_base h2_rest h2 st2 hn1 stn1 CC pi;
    intros perm pi_in_h1 union_h1 union_h2 eval.
  + exists h1_base, [], h2_base, h2, st2, pi.
    simpl in eval.
    destruct eval as (h1_eq & st1_eq).
    rewrite <-h1_eq, <-st1_eq.
    now split; [ | split; [ | split; [ | split]]].
  + destruct a.
    unfold JFIPartialEval in eval.
    fold JFIPartialEval in eval.
    destruct eval as (h_eq & st_eq & eval).
    apply PermutationEvalAux1 in eval as (h1' & st1' & red_is_some & eval).
    destruct (ReductionDependsOnFreeVars h1_base h1_rest h1 st1 h2_base h2_rest h2 st2 h1' st1' CC pi)
      as (h1'_base & h2'_base & h2' & st2' & pi' &
          pi_subset & pi'_everything & pi_in_hn1 & h1'_union & h2'_union & red2); trivial.
    destruct (IHconfs1 h1'_base h1_rest h1' st1' h2'_base h2_rest h2' st2' hn1 stn1 CC pi')
      as (hn1_base & confs2 & hn2_base & hn2 & stn2 & pi'' &
          pi'_subset & pi''_in_hn1 & pi''_everything & hn1_union & hn2_union & h2_eval); trivial.
    exists hn1_base, ((h2, st2)::confs2), hn2_base, hn2, stn2, pi''.
    split; [ | split; [ | split; [ | split]]]; try easy.
      now apply PermutationSubsetTrans with (pi2 := pi').
    unfold JFIPartialEval; fold JFIPartialEval.
    split; [ | split; [ | split]]; trivial.
    now apply PermutationEvalAux2 with (h'_ext := h2') (st'_perm := st2').
Qed.

Lemma FreeVarsInHeapThenLocsInStack : forall e h env,
  NoHardcodedLocsInExpr e ->
  FreeVarsInExprAreInHeap e h env ->
  LocsInStackAreInHeap [ [] [[JFIExprSubstituteEnv env e ]]_ None] h.
Proof.
Admitted.

Theorem EvaluationDependsOnFreeVars : forall h h1_rest h2_rest h1 h2 e confs1 hn1 res_ex res1 env CC,
  HeapConsistent h ->
  NoHardcodedLocsInExpr e ->
  FreeVarsInExprAreInHeap e h env ->
  JFIDisjointUnion h h1_rest h1 ->
  JFIDisjointUnion h h2_rest h2 ->
  JFIEvalInEnv h1 e confs1 hn1 res_ex res1 env CC ->
  exists hn1_base confs2 hn2_base hn2 res2 pi,
    EnvsPermuted env env pi /\
    PiMapsTo res1 res2 pi /\
    LocMapsToHeap res1 hn1_base /\
    HeapsPermuted hn1_base hn2_base pi /\
    JFIDisjointUnion hn1_base h1_rest hn1 /\
    JFIDisjointUnion hn2_base h2_rest hn2 /\
    JFIEvalInEnv h2 e confs2 hn2 res_ex res2 env CC.
Proof.
  intros h h1_rest h2_rest h1 h2 e confs1 hn1 res_ex res1 env CC.
  intros h_consistent no_hardcoded_locs free_vars_in_h union_h1 union_h2 h1_eval.
  set (st := [ [] [[JFIExprSubstituteEnv env e ]]_ None]).
  set (stn1 := [ [] [[JFVal1 (JFVLoc res1) ]]_ res_ex]).

  assert (pi : HeapPermutation). admit.
  assert (pi_env : EnvsPermuted env env pi). admit.
  assert (pi_h : HeapsPermuted h h pi). admit.
  assert (pi_st : StacksPermuted st st pi). admit.
  assert (pi_npe : PiMapsTo (JFLoc NPE_object_loc) (JFLoc NPE_object_loc) pi). admit.
  assert (pi_in_h : PiOnlyFromHeap pi h). admit.

  destruct (PartialEvaluationDependsOnFreeVars confs1 h h1_rest h1 st
               h h2_rest h2 st hn1 stn1 CC pi)
  as (hn1_base & confs2 & hn2_base & hn2 & stn2 & pi' & pi_subset &
          pi'_in_hn1 & pi'_everything & hn1_union & hn2_union & h2_eval); try easy.
  + split; [ | split]; try easy.
    now apply FreeVarsInHeapThenLocsInStack.
  + split; [ | split]; try easy.
    now apply FreeVarsInHeapThenLocsInStack.
  + destruct pi'_everything as (pi'_npe & pi'_hn & pi'_stn).
    unfold stn1 in pi'_stn.
    destruct stn2; try now destruct pi'_stn.
    unfold StacksPermuted in pi'_stn.
    destruct pi'_stn as (pi_f & stn_eq).
    destruct stn2; try now destruct stn_eq.
    destruct f.
    destruct E; try now destruct pi_f.
    unfold FramesPermuted, ExprsPermuted in pi_f.
    destruct pi_f as (pi_res & pi_ctxs & A_eq).
    destruct Ctx; try now destruct pi_ctxs.
    destruct v as [ res2 |]; try now destruct pi_res.
    unfold ValPermuted in pi_res.
    exists hn1_base, confs2, hn2_base, hn2, res2, pi'.
    split; [ | split; [ | split; [ | split; [ | split; [ | split]]]]]; try easy.
    ++ unfold EnvsPermuted.
       split; [ | split]; try easy.
       +++ apply (proj1 pi'_hn).
       +++ intros x l1 l2 x_l1_env x_l2_env.
          apply pi_subset.
          now apply ((proj2 (proj2 pi_env)) x).
    ++ apply hn1_union.
    ++ apply hn1_union.
    ++ apply hn2_union.
    ++ unfold JFIEvalInEnv, JFIEval.
       fold st.
       now rewrite A_eq.
Admitted.

Theorem EvaluationOnExtendedHeap_as_special_case : forall h h2_rest h2 e confs hn1 res_ex res1 env CC,
  HeapConsistent h ->
  NoHardcodedLocsInExpr e ->
  FreeVarsInExprAreInHeap e h env ->
  JFIEvalInEnv h e confs hn1 res_ex res1 env CC ->
  JFIDisjointUnion h h2_rest h2 ->
  exists confs2 hn2_base hn2 res2 pi,
    HeapsPermuted hn1 hn2_base pi /\
    EnvsPermuted env env pi /\
    PiMapsTo res1 res2 pi /\
    JFIDisjointUnion hn2_base h2_rest hn2 /\ 
    JFIEvalInEnv h2 e confs2 hn2 res_ex res2 env CC.
Proof.
  intros h h2_rest h2 e confs hn1 res_ex res1 env CC.
  intros h_consistent no_hardcoded free_vals_in_h eval union.
  destruct (EvaluationDependsOnFreeVars h (Heap.empty Obj) h2_rest h h2 e confs hn1 res_ex res1 env CC)
    as (hn1_base & confs2 & hn2_base & hn2 & res2 & pi & conds); try easy.
  now apply DisjointUnionSymmetry, DisjointUnionIdentity.
  exists confs2, hn2_base, hn2, res2, pi.
  split; [ | split; [ | split]]; try easy.
  apply EqPermuted1 with (h1 := hn1_base); try easy.
  apply UnionWithEmptyEq.
  now apply conds.
Qed.

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

Theorem LetEvaluationNormal : forall h h' hn class x e1 e2 e1_confs e2_confs e1_res e2_res A env CC,
   JFIEvalInEnv h e1 e1_confs h' None e1_res env CC ->
   JFIEvalInEnv h' e2 e2_confs hn A e2_res (StrMap.add x e1_res env) CC ->
   exists confs, JFIEvalInEnv h (JFLet class x e1 e2) confs hn A e2_res env CC.
Proof.
  intros h h' hn class x e1 e2 e1_confs e2_confs e1_res e2_res A env CC.
  intros e1_eval e2_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsNormalLetEval with (x := x) (class := class) (e2 := e2_in_env) in e1_eval
    as (let_e1_confs & e1_let_eval).
  exists (let_e1_confs ++ e2_confs).
  unfold JFIEvalInEnv, JFIEval in  e2_eval.
  apply EvaluationJoin with (h' := h')
    (st' := [ [] [[ substExpr (JFVar x) e1_res e2_in_env ]]_ None]); try easy.
  unfold e2_in_env.
  rewrite SubstExprEqExprSubstituteVal.
  rewrite RemoveVarFromEnv with (v := x).
  now rewrite SubsituteVarIdentity.
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

Theorem TryEvaluationExCatch : forall h h' hn mu e1_A e2_A catch_A x e1 e2 e1_confs e2_confs e1_res e2_res env CC,
   Is_true (subtype_bool CC (JFClass e1_A) (JFClass catch_A)) ->
   JFIEvalInEnv h e1 e1_confs h' (Some e1_A) e1_res env CC ->
   JFIEvalInEnv h' e2 e2_confs hn e2_A e2_res (StrMap.add x e1_res env) CC ->
   exists confs, JFIEvalInEnv h (JFTry e1 mu catch_A x e2) confs hn e2_A e2_res env CC.
Proof.
  intros h h' hn mu e1_A e2_A catch_A x e1 e2 e1_confs e2_confs e1_res e2_res env CC.
  intros is_subtype e1_eval e2_eval.
  set (e2_in_env := JFIExprSubstituteEnv (StrMap.remove x env) e2).
  apply ExistsExTryEval with (x := x) (mu := mu)
    (catch_ex := catch_A) (e2 := e2_in_env) in e1_eval.
  unfold JFIEvalInEnv, JFIEval in e2_eval.
  destruct e1_eval as (try_e1_confs & try_e1_eval).
  set (trygo1 := (h', [ [JFCtxTry __ mu catch_A x e2_in_env] [[ JFVal1 (JFVLoc e1_res) ]]_ (Some e1_A)])).
  set (trygo2 := (h', [ [] [[ substExpr (JFVar x) e1_res e2_in_env ]]_ None])).
  exists ((try_e1_confs ++ [trygo1]) ++ e2_confs).
  apply EvaluationJoin with (h' := h') (st' := snd trygo2); try easy.

  apply EvaluationJoin with (h' := h')
    (st' := snd trygo1); try easy.
  split; try split; trivial.
  + unfold trygo1, snd, red.
    now destruct (subtype_bool CC (JFClass e1_A) (JFClass catch_A)).
  + unfold trygo2, snd, e2_in_env.
    rewrite SubstExprEqExprSubstituteVal.
    rewrite RemoveVarFromEnv with (v := x).
    now rewrite SubsituteVarIdentity.
Qed.
