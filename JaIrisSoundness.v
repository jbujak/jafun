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
Require Import JaIrisCommon.
Require Import JaEval.
Require Import JaIris.
Require Import JaSubtype.
Require Import Bool.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.


Module HeapFacts := Facts Heap.
Module StrMapFacts := JaIrisCommon.StrMapFacts.
Module JFXIdMapFacts := Facts JFXIdMap.

Definition JFISemanticallyImplies (gamma : JFITypeEnv) (s : JFITerm) (p : JFITerm) (CC : JFProgram) :=
  forall env h,
    (JFIGammaMatchEnv h gamma env) ->
    (JFIHeapSatisfiesInEnv h s env CC) ->
     JFIHeapSatisfiesInEnv h p env CC.

Ltac unfoldSubstitutions :=
  unfold JFITermSubstituteVals;
  unfold JFITermSubstituteVar;
  unfold JFITermSubstituteVal;
  unfold JFIExprSubstituteVar;
  unfold JFIValSubstituteVal;
  unfold JFIStringSubstitute;
  simpl.

Lemma neq_symmetry : forall t (x : t) (y : t), x <> y -> y <> x.
Proof.
  intros t x y.
  intros x_neq_y.
  unfold not.
  intros y_eq_x.
  symmetry in y_eq_x.
  exact (x_neq_y y_eq_x).
Qed.

Lemma LocNotNullIff : forall loc,
  (exists n, loc = JFLoc n) <-> (loc <> null).
Proof.
  intro loc .
  split.
  + intros (n & loc_is_n).
    rewrite loc_is_n.
    unfold not.
    discriminate.
  + intros loc_is_not_null.
    destruct loc.
    ++ exfalso.
       apply loc_is_not_null.
       trivial.
    ++ exists n.
       trivial.
Qed.

(* =============== StrMap Lemmas =============== *)

Lemma StrMap_in_find_iff : forall t m x,
  (StrMap.In x m) <-> (exists e : t, StrMap.find x m = Some e).
Proof.
  intros t m x.
  split.
  + intros x_in_m.
    apply StrMapFacts.elements_in_iff in x_in_m.
    destruct x_in_m as ( e & e_in_elements ).
    apply StrMapFacts.elements_mapsto_iff in e_in_elements.
    apply StrMapFacts.find_mapsto_iff in e_in_elements.
    exists e.
    exact e_in_elements.
  + intros find_gives_some.
    apply StrMapFacts.elements_in_iff.
    destruct find_gives_some as ( e & find_gives_e).
    exists e.
    apply StrMapFacts.elements_mapsto_iff.
    apply StrMapFacts.find_mapsto_iff.
    exact find_gives_e.
Qed.


(* =============== Heap Lemmas =============== *)

Lemma JFIHeapsDisjointSym : forall h1 h2, JFIHeapsDisjoint h1 h2 -> JFIHeapsDisjoint h2 h1.
Proof.
  intros h1 h2 disjoint.
  unfold JFIHeapsDisjoint.
  intros l.
  unfold not.
  intros notDisjoint.
  refine (disjoint l _).
  apply and_comm.
  exact notDisjoint.
Qed.

Lemma JFINotInEmptyHeap : forall l, Heap.In l (Heap.empty Obj) -> False.
Proof.
  intros l.
  apply HeapFacts.empty_in_iff.
Qed.

Lemma JFIEmptyHeapDisjoint : forall h, JFIHeapsDisjoint (Heap.empty Obj) h.
Proof.
  intros h.
  unfold JFIHeapsDisjoint.
  intros l.
  unfold not.
  intros l_in_both.
  case l_in_both.
  intros in_empty in_h.
  exact (JFINotInEmptyHeap l in_empty).
Qed.

Lemma HeapsUnionSymmetry : forall h1 h2 h, JFIHeapsUnion h1 h2 h -> JFIHeapsUnion h2 h1 h.
Proof.
  intros h1 h2 h h1_h2_union.
  unfold JFIHeapsUnion.
  unfold JFIHeapsUnion in h1_h2_union.
  split; [| split].
  + apply h1_h2_union.
  + apply h1_h2_union.
  + intros l l_in_h.
    apply or_comm.
    apply h1_h2_union.
    apply l_in_h.
Qed.

Lemma SubheapOfUnion : forall h1 h2 h, JFIHeapsUnion h1 h2 h -> JFISubheap h1 h.
Proof.
  intros h1 h2 h h_is_union.
  unfold JFIHeapsUnion in h_is_union.
  apply h_is_union.
Qed.

(* =============== Gamma Match Env Lemmas =============== *)

Lemma ExtendedGammaMatchesExtendedEnv : forall x l type env gamma h,
  (JFIGammaMatchEnv h gamma env) ->
  (JFILocOfType l h type) ->
  (JFIGammaMatchEnv h (JFIGammaAdd x type gamma) ((StrMap.add x l env))).
Proof.
  intros x l type env gamma h.
  intros gamma_match_env loc_of_type.
  unfold JFIGammaAdd.
  unfold JFIGammaMatchEnv.
  intros var_name.
  split.
  + split;
      (intros x_in;
       apply StrMapFacts.add_in_iff in x_in;
       apply StrMapFacts.add_in_iff;
       rewrite <- String.eqb_eq in *;
       destruct (String.eqb x var_name); auto;
       destruct x_in as [ false_eq_true | var_in]; try discriminate false_eq_true;
       apply or_intror;
       assert (in_iff := (proj1 (gamma_match_env var_name)));
       apply in_iff;
       assumption).
  + intros var_loc var_type var_is_some_type.
    intros var_is_some_loc.
    rewrite StrMapFacts.find_mapsto_iff, StrMapFacts.add_o in var_is_some_type, var_is_some_loc.
    destruct (StrMapFacts.eq_dec x var_name).
    ++ injection var_is_some_type as type_eq_var_type.
       injection var_is_some_loc as l_eq_var_loc.
       rewrite <- type_eq_var_type, <- l_eq_var_loc.
       assumption.
    ++ apply (proj2 (gamma_match_env var_name)); rewrite StrMapFacts.find_mapsto_iff; try assumption.
Qed.

Lemma StrictlyExtendedGammaMatchesExtendedEnv : forall x l type env gamma gamma_x h,
  (JFIGammaMatchEnv h gamma env) ->
  (JFILocOfType l h type) ->
  (JFIGammaAddNew x type gamma = Some gamma_x) ->
  (JFIGammaMatchEnv h gamma_x ((StrMap.add x l env))).
Proof.
  intros x l type env gamma gamma_x h.
  intros gamma_match_env loc_of_type add_new_x.
  replace gamma_x with (StrMap.add x type gamma). 
  + apply ExtendedGammaMatchesExtendedEnv.
    ++ exact gamma_match_env.
    ++ exact loc_of_type.
  + unfold JFIGammaAddNew in add_new_x.
    destruct (StrMap.mem (elt:=JFClassName) x gamma).
    ++ discriminate add_new_x.
    ++ injection add_new_x. trivial.
Qed.

(* =============== Env Lemmas =============== *)

Lemma DifferentVarIsFresh : forall v w,
  (w <> JFSyn (JFVar v)) -> JFIVarFreshInVal v w.
Proof.
  intros v w.
  intros w_is_not_v.
  unfold JFIVarFreshInVal.
  destruct w; [ | destruct x]; try trivial.
  unfold not.
  intros v_eq_x.
  apply f_equal with (f := fun x => JFSyn (JFVar x)) in v_eq_x.
  symmetry in v_eq_x.
  exact (w_is_not_v v_eq_x).
Qed.

Lemma FreshVarDifferentFromForallVar : forall x class name t,
  (JFIVarFreshInTerm x (JFIForall class name t)) ->
   x <> name.
Proof.
  intros x class name t.
  intros x_fresh.
  unfold not.
  intros x_eq_name.
  symmetry in x_eq_name.
  apply (String.eqb_eq) in x_eq_name.
  simpl in x_fresh.
  destruct (String.eqb name x).
  + destruct x_fresh.
  + discriminate x_eq_name.
Qed.

Lemma AddingFreshVarPreservesValToLoc : forall x l val env,
  (JFIVarFreshInVal x val) ->
   JFIValToLoc val env = JFIValToLoc val (StrMap.add x l env).
Proof.
  intros x l val env.
  intros x_fresh.
  unfold JFIValToLoc.
  destruct val as [ | loc].
  + trivial.
  + destruct loc as [y | ].
    ++ symmetry.
       apply StrMapFacts.add_neq_o.
       unfold JFIVarFreshInVal in x_fresh.
       exact x_fresh.
    ++ trivial.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfiyingEq : forall val1 val2 x l env h CC,
  (JFIVarFreshInTerm x (JFIEq val1 val2)) ->
    ((JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env CC) <->
      JFIHeapSatisfiesInEnv h (JFIEq val1 val2) (StrMap.add x l env) CC).
Proof.
  intros val1 val2 x l env h CC.
  intros x_fresh.
  split.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    replace (JFIValToLoc val1 (StrMap.add x l env)) with (JFIValToLoc val1 env).
    replace (JFIValToLoc val2 (StrMap.add x l env)) with (JFIValToLoc val2 env).
    ++ exact h_satisfies_eq.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    replace (JFIValToLoc val1 (StrMap.add x l env))
      with (JFIValToLoc val1 env) in h_satisfies_eq.
    replace (JFIValToLoc val2 (StrMap.add x l env))
      with (JFIValToLoc val2 env) in h_satisfies_eq.
    ++ exact h_satisfies_eq.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfiyingFieldEq : forall obj field val x l env h CC,
  (JFIVarFreshInTerm x (JFIFieldEq obj field val)) ->
    ((JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env CC) <->
      JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) (StrMap.add x l env) CC).
Proof.
  intros obj field val x l env h CC. 
  intros (x_fresh_in_obj & x_fresh_in_val).
  split.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    replace (JFIValToLoc obj (StrMap.add x l env)) with (JFIValToLoc obj env).
    replace (JFIValToLoc val (StrMap.add x l env)) with (JFIValToLoc val env).
    ++ exact h_satisfies_eq.
    ++ apply AddingFreshVarPreservesValToLoc.
       exact x_fresh_in_val.
    ++ apply AddingFreshVarPreservesValToLoc.
       exact x_fresh_in_obj.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    replace (JFIValToLoc obj (StrMap.add x l env))
      with (JFIValToLoc obj env) in h_satisfies_eq.
    replace (JFIValToLoc val (StrMap.add x l env))
      with (JFIValToLoc val env) in h_satisfies_eq.
    ++ exact h_satisfies_eq.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh_in_val.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh_in_obj.
Qed.

Definition EnvEq (env1 : JFITermEnv) (env2 : JFITermEnv) := 
  forall x, StrMap.find x env1 = StrMap.find x env2.

Definition EqualEnvsEquivalentInTermForHeap (t : JFITerm) CC :=
  forall h env1 env2, 
    (EnvEq env1 env2) -> ((JFIHeapSatisfiesInEnv h t env1 CC) <-> (JFIHeapSatisfiesInEnv h t env2 CC)).

Lemma EnvEqSymmetry : forall env1 env2,
  (EnvEq env1 env2) -> (EnvEq env2 env1).
Proof.
  intros env1 env2.
  intros env1_eq_env2.
  unfold EnvEq.
  intros x.
  symmetry.
  apply env1_eq_env2.
Qed.

Lemma AddPreservesEnvEq : forall x l env1 env2,
  (EnvEq env1 env2) -> (EnvEq (StrMap.add x l env1) (StrMap.add x l env2)).
Proof.
  intros x l env1 env2.
  intros env1_eq_env2.
  intros y.
  rewrite 2!StrMapFacts.add_o.
  destruct (StrMapFacts.eq_dec x y); trivial.
Qed.

Lemma RemovePreservesEnvEq : forall x env1 env2,
  (EnvEq env1 env2) -> (EnvEq (StrMap.remove x env1) (StrMap.remove x env2)).
Proof.
  intros x env1 env2.
  intros env_eq.
  intros y.
  rewrite 2!StrMapFacts.remove_o.
  destruct (StrMapFacts.eq_dec x y); trivial.
Qed.

Lemma AddOrderChangePreservesEnvEq : forall x1 l1 x2 l2 env,
  (x2 <> x1) ->
  EnvEq (StrMap.add x1 l1 (StrMap.add x2 l2 env)) (StrMap.add x2 l2 (StrMap.add x1 l1 env)).
Proof.
  intros x1 l1 x2 l2 env.
  intros x2_neq_x1.
  unfold EnvEq.
  intros x.
  destruct (Classical_Prop.classic (x1 = x)) as [x1_eq_x | x1_neq_x].
  + rewrite StrMapFacts.add_eq_o.
    symmetry.
    rewrite StrMapFacts.add_neq_o.
    rewrite StrMapFacts.add_eq_o.
    ++ trivial.
    ++ exact x1_eq_x.
    ++ replace x with x1.
       exact x2_neq_x1.
    ++ exact x1_eq_x.
  + destruct (Classical_Prop.classic (x2 = x)) as [x2_eq_x | x2_neq_x].
    ++ rewrite StrMapFacts.add_neq_o.
       rewrite StrMapFacts.add_eq_o.
       symmetry.
       rewrite StrMapFacts.add_eq_o.
       +++ trivial.
       +++ exact x2_eq_x.
       +++ exact x2_eq_x.
       +++ exact x1_neq_x.
    ++ rewrite StrMapFacts.add_neq_o.
       rewrite StrMapFacts.add_neq_o.
       symmetry.
       rewrite StrMapFacts.add_neq_o.
       rewrite StrMapFacts.add_neq_o.
       +++ trivial.
       +++ exact x1_neq_x.
       +++ exact x2_neq_x.
       +++ exact x2_neq_x.
       +++ exact x1_neq_x.
Qed.

Lemma EnvEqGivesValSubstEnvEq : forall env1 env2 v,
  (EnvEq env1 env2) ->
  (JFIValSubstituteEnv env1 v = JFIValSubstituteEnv env2 v).
Proof.
  intros env1 env2 v.
  intros env_eq.
  destruct v as [ | x]; try destruct x.
  + rewrite 2!ValEnvSubstitutionPreservesVLoc.
    trivial.
  + destruct (Classical_Prop.classic (StrMap.In x env1)) as [x_in_env1 | x_not_in_env1].
    ++ apply StrMap_in_find_iff in x_in_env1 as (l & x_l_in_env1).
       assert (x_l_in_env2 := env_eq x).
       rewrite x_l_in_env1 in x_l_in_env2.
       symmetry in x_l_in_env2.
       rewrite 2!ValEnvSubstitutionReplacesVarInEnv with (l := l); trivial.
    ++ rewrite 2!(ValEnvSubstitutionPreservesVarNotInEnv); try assumption; trivial.
       intros x_in_env2.
       apply StrMapFacts.not_find_mapsto_iff in x_not_in_env1 as x_is_none.
       apply StrMap_in_find_iff in x_in_env2 as (l & x_is_l).
       rewrite <- (env_eq x) in x_is_l.
       rewrite x_is_none in x_is_l.
       discriminate x_is_l.
  + rewrite 2!ValEnvSubstitutionPreservesThis.
    trivial.
Qed.

Lemma EnvEqGivesMapValSubstEq : forall env1 env2 vs,
  (EnvEq env1 env2) ->
  (map (JFIValSubstituteEnv env1) vs = map (JFIValSubstituteEnv env2) vs).
Proof.
  intros env1 env2 vs.
  intros env_eq.
  induction vs; try trivial.
  rewrite 2!List.map_cons.
  rewrite IHvs.
  rewrite EnvEqGivesValSubstEnvEq with (env2 := env2); trivial.
Qed.

Lemma EnvEqGivesExprSubstEnvEq : forall e env1 env2,
  (EnvEq env1 env2) ->
  (JFIExprSubstituteEnv env1 e =  JFIExprSubstituteEnv env2 e).
Proof.
  intros e.
  induction e; intros env1 env2 env_eq; simpl;
    try rewrite ?(EnvEqGivesValSubstEnvEq env1 env2);
    try rewrite (EnvEqGivesMapValSubstEq env1 env2);
    try assumption;
    trivial.
  + rewrite (IHe1 env1 env2); try assumption.
    rewrite (IHe2 (StrMap.remove x env1) (StrMap.remove x env2)); trivial.
    apply RemovePreservesEnvEq; try assumption.
  + rewrite <- (IHe1 env1 env2), <- (IHe2 env1 env2); try assumption.
    trivial.
  + destruct vx.
    rewrite (EnvEqGivesValSubstEnvEq env1 env2); try assumption.
    trivial.
  + destruct vx.
    rewrite (EnvEqGivesValSubstEnvEq env1 env2); try assumption.
    trivial.
  + rewrite (IHe1 env1 env2); try assumption.
    rewrite (IHe2 (StrMap.remove x env1) (StrMap.remove x env2)); trivial.
    apply RemovePreservesEnvEq; try assumption.
Qed.

Lemma EnvEqGivesEvalEq : forall confs h e hn ex res env1 env2 CC,
  (EnvEq env1 env2) ->
  (JFIEvalInEnv h e confs hn ex res env1 CC) ->
  (JFIEvalInEnv h e confs hn ex res env2 CC).
Proof.
  intros confs.
  induction confs; intros h e hn ex res env1 env2 CC env_eq.
  + unfold JFIEvalInEnv, JFIEval, JFIPartialEval.
    intros (h_eq & f_eq).
    rewrite h_eq.
    split; trivial.
    rewrite <- f_eq.
    symmetry.
    rewrite EnvEqGivesExprSubstEnvEq with (env2 := env2); trivial.
  + intros e_eval.
    unfold JFIEvalInEnv, JFIEval, JFIPartialEval in *.
    destruct a.
    fold JFIPartialEval in *.
    destruct e_eval as (h_eq & f_eq & red_is_some).
    rewrite h_eq, <-f_eq in *.
    apply EnvEqSymmetry in env_eq.
    split; try split; try rewrite EnvEqGivesExprSubstEnvEq with (env2 := env1); try trivial.
Qed.

Lemma EnvEqGivesExistsImplication : forall h type x t env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t CC) ->
  (JFIHeapSatisfiesInEnv h (JFIExists type x t) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIExists type x t) env2 CC.
Proof.
  intros h type x t env1 env2 CC.
  intros env1_eq_env2 t_equivalence h_satisfies_exists_t.
  simpl.
  simpl in h_satisfies_exists_t.
  destruct h_satisfies_exists_t as ( loc & (loc_of_type & h_satisfies_t)).
  unfold EqualEnvsEquivalentInTermForHeap in t_equivalence.
  exists loc.
  split.
  + exact loc_of_type.
  + apply (t_equivalence h (StrMap.add x loc env1) (StrMap.add x loc env2)).
    ++ apply AddPreservesEnvEq.
       exact env1_eq_env2.
    ++ exact h_satisfies_t.
Qed.

Lemma EnvEqGivesAndImplication : forall h t1 t2 env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIAnd t1 t2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIAnd t1 t2) env2 CC.
Proof.
    intros h t1 t2 env1 env2 CC.
    intros env_eq t1_equivalence t2_equivalence (h_satisfies_t1 & h_satisfies_t2).
    split.
    + apply (t1_equivalence h env1 env2 env_eq).
      exact h_satisfies_t1.
    + apply (t2_equivalence h env1 env2 env_eq).
      exact h_satisfies_t2.
Qed.

Lemma EnvEqGivesOrImplication : forall h t1 t2 env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIOr t1 t2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIOr t1 t2) env2 CC.
Proof.
  intros h t1 t2 env1 env2 CC.
  intros env_eq t1_equivalence t2_equivalence [h_satisfies_t1 | h_satisfies_t2].
  + simpl.
    apply or_introl.
    apply (t1_equivalence h env1 env2 env_eq).
    exact h_satisfies_t1.
  + simpl.
    apply or_intror.
    apply (t2_equivalence h env1 env2 env_eq).
    exact h_satisfies_t2.
Qed.

Lemma EnvEqGivesImpliesImplication : forall h t1 t2 env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIImplies t1 t2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIImplies t1 t2) env2 CC.
Proof.
  intros h t1 t2 env1 env2 CC.
  intros env_eq t1_equivalence t2_equivalence [not_h_satisfies_t1 | h_satisfies_t2].
  + simpl.
    apply or_introl.
    intros h_satisfies_t1.
    apply (t1_equivalence h env1 env2 env_eq) in h_satisfies_t1.
    apply not_h_satisfies_t1.
    exact h_satisfies_t1.
  + simpl.
    apply or_intror.
    apply (t2_equivalence h env1 env2 env_eq).
    exact h_satisfies_t2.
Qed.

Lemma EnvEqGivesForallImplication : forall h type x t env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t CC) ->
  (JFIHeapSatisfiesInEnv h (JFIForall type x t) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIForall type x t) env2 CC.
Proof.
  intros h type x t env1 env2 CC.
  intros env1_eq_env2 t_equivalence h_satisfies_t.
  simpl.
  intros loc loc_of_type.
  unfold EqualEnvsEquivalentInTermForHeap in t_equivalence.
  apply (t_equivalence h (StrMap.add x loc env1) (StrMap.add x loc env2)).
  + apply AddPreservesEnvEq.
    exact env1_eq_env2.
  + exact (h_satisfies_t loc loc_of_type).
Qed.

Lemma EnvEqGivesHoareImplication : forall h t1 e ex v t2 env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIHoare t1 e ex v t2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIHoare t1 e ex v t2) env2 CC.
Proof.
  intros h t1 e ex v t2 env1 env2 CC.
  intros env_eq t1_equivalence t2_equivalence.
  simpl.
  intros h_satisfies_hoare confs hn ex' res h_satisfies_t1 e_eval.
  assert (h_satisfies_t1_in_env1 := proj2 (t1_equivalence h env1 env2 env_eq) h_satisfies_t1).
  split.
  + eassert (ex'_eq_ex := h_satisfies_hoare confs hn ex' res h_satisfies_t1_in_env1).
    apply ex'_eq_ex.
    apply EnvEqGivesEvalEq with (env1 := env2); try assumption.
    apply EnvEqSymmetry.
    exact env_eq.
  + apply (t2_equivalence hn (StrMap.add v res env1) (StrMap.add v res env2)).
    ++ apply AddPreservesEnvEq.
       exact env_eq.
    ++ eassert (h_satisfies_t2 := h_satisfies_hoare confs hn ex' res h_satisfies_t1_in_env1).
       apply h_satisfies_t2.
       apply EnvEqGivesEvalEq with (env1 := env2); try assumption.
       apply EnvEqSymmetry.
       exact env_eq.
Qed.

Lemma EnvEqGivesEqualValToLoc : forall val env1 env2,
  (EnvEq env1 env2) ->
  (JFIValToLoc val env1) = (JFIValToLoc val env2).
Proof.
  intros val env1 env2.
  intros env_eq.
  unfold JFIValToLoc.
  destruct val.
  + trivial.
  + destruct x.
    ++ rewrite env_eq.
       trivial.
    ++ trivial.
Qed.

Lemma EnvEqGivesEqImplication : forall h env1 env2 val1 val2 CC,
  (EnvEq env1 env2) ->
  (JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env2 CC.
Proof.
  intros h env1 env2 val1 val2 CC.
  intros env_eq.
  apply EnvEqSymmetry in env_eq.
  simpl.
  rewrite (EnvEqGivesEqualValToLoc val1 env2 env1 env_eq).
  rewrite (EnvEqGivesEqualValToLoc val2 env2 env1 env_eq).
  trivial.
Qed.

Lemma EnvEqGivesFieldEqImplication : forall h env1 env2 obj field val CC,
  (EnvEq env1 env2) ->
  (JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env2 CC.
Proof.
  intros h env1 env2 obj field val CC.
  intros env_eq.
  apply EnvEqSymmetry in env_eq.
  simpl.
  rewrite (EnvEqGivesEqualValToLoc obj env2 env1 env_eq).
  rewrite (EnvEqGivesEqualValToLoc val env2 env1 env_eq).
  trivial.
Qed.

Lemma EnvEqGivesSepImplication : forall h t1 t2 env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFISep t1 t2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFISep t1 t2) env2 CC.
Proof.
  intros h t1 t2 env1 env2 CC.
  intros env_eq t1_equivalence t2_equivalence.
  simpl.
  intros (h1 & (h2 & (disjoint_unions & (h1_satisfies_t1 & h2_satisfies_t2)))).
  exists h1, h2.
  split.
  + exact disjoint_unions.
  + split.
    ++ apply (t1_equivalence h1 env1 env2 env_eq).
       exact h1_satisfies_t1.
    ++ apply (t2_equivalence h2 env1 env2 env_eq).
       exact h2_satisfies_t2.
Qed.

Lemma EnvEqGivesWandImplication : forall h t1 t2 env1 env2 CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIWand t1 t2) env1 CC) ->
   JFIHeapSatisfiesInEnv h (JFIWand t1 t2) env2 CC.
Proof.
  intros h t1 t2 env1 env2 CC.
  intros env_eq t1_equivalence t2_equivalence.
  simpl.
  intros wand h' disjoint_h_h' h'_satisfies_t1.
  unfold EqualEnvsEquivalentInTermForHeap in t1_equivalence.
  apply (t1_equivalence h' env1 env2 env_eq) in h'_satisfies_t1.
  destruct (wand h' disjoint_h_h' h'_satisfies_t1) as (h_h' & union_h_h' & h_h'_satisfies_t2).
  apply (t2_equivalence h_h' env1 env2 env_eq) in h_h'_satisfies_t2.
  exists h_h'.
  split; assumption.
Qed.

Lemma EqualEnvsAreEquivalent : forall t CC h env1 env2,
  (EnvEq env1 env2) ->
    ((JFIHeapSatisfiesInEnv h t env1 CC) <-> (JFIHeapSatisfiesInEnv h t env2 CC)).
Proof.
  intros t CC.
  induction t; intros h env1 env2 env1_eq_env2.
  (* JFITrue *)
  + split; simpl; trivial.
  (* JFIFalse *)
  + split; simpl; trivial.
  (* JFIAnd t1 t2 *)
  + split; apply EnvEqGivesAndImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIOr t1 t2 *)
  + split; apply EnvEqGivesOrImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIImplies t1 t2 *)
  + split; apply EnvEqGivesImpliesImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIExists *)
  + split; apply EnvEqGivesExistsImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIForall *)
  + split; apply EnvEqGivesForallImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIHoare *)
 + split; apply EnvEqGivesHoareImplication; try assumption.
   exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIEq *)
  + split; apply EnvEqGivesEqImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIFieldEq *)
  + split; apply EnvEqGivesFieldEqImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFISep*)
  + split; apply EnvEqGivesSepImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIWand *)
  + split; apply EnvEqGivesWandImplication; try assumption.
    exact (EnvEqSymmetry env1 env2 env1_eq_env2).
Qed.

Lemma EnvOrderChangePreservesHeapSatisfiying : forall h t x1 l1 x2 l2 env CC,
  (x1 <> x2) ->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x1 l1 (StrMap.add x2 l2 env)) CC) <->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x2 l2 (StrMap.add x1 l1 env)) CC).
Proof.
  intros h t x1 l1 x2 l2 env CC.
  intros x1_neq_x2.
  apply EqualEnvsAreEquivalent.
  apply AddOrderChangePreservesEnvEq.
  apply neq_symmetry.
  exact x1_neq_x2.
Qed.

Lemma FreshEnvOrderChangePreservesHeapSatisfiying : forall h t x1 l1 x2 l2 env CC,
  (JFIVarFreshInTerm x1 t) ->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x1 l1 (StrMap.add x2 l2 env)) CC) <->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x2 l2 (StrMap.add x1 l1 env)) CC).
Proof.
Admitted.

Definition FreshVarPreservesTermSatysfying t CC :=
forall h x l env,
        JFIVarFreshInTerm x t ->
        JFIHeapSatisfiesInEnv h t env CC <->
        JFIHeapSatisfiesInEnv h t (StrMap.add x l env) CC.

Lemma FreshVarPreservesEval : forall h e confs hn ex res x l env CC,
  JFIVarFreshInExpr x e ->
  JFIEvalInEnv h e confs hn ex res env CC <->
  JFIEvalInEnv h e confs hn ex res (StrMap.add x l env) CC.
Proof.
Admitted.

Lemma FreshVarPreservesAndSatystying : forall t1 t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFIAnd t1 t2) CC.
Proof.
  intros t1 t2 CC.
  intros t1_preserves t2_preserves.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env and_fresh.
  destruct and_fresh as (t1_fresh & t2_fresh).
  split; intros h_satisfies_and; split;
  destruct h_satisfies_and as (h_satisfies_t1 & h_satisfies_t2);
  try apply (t1_preserves h x l env t1_fresh);
  try apply (t2_preserves h x l env t2_fresh);
  try assumption.
Qed.

Lemma FreshVarPreservesHoareSatystying : forall t1 e ex v t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFIHoare t1 e ex v t2) CC.
Proof.
  intros t1 e ex v t2 CC.
  intros IH_t1 IH_t2.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env x_fresh_in_hoare.
  simpl in x_fresh_in_hoare.
  destruct (String.eqb v x); destruct x_fresh_in_hoare.
  destruct H0 as (x_fresh_in_t2 & x_fresh_in_e).
  simpl.
  split.
  + intros h_satisfies_hoare_in_env.
    intros confs hn res_ex res h_satisfies_t1_in_env_x e_eval_in_env_x.
    assert (t1_preserves := IH_t1 h x l env H).
    apply FreshVarPreservesEval in e_eval_in_env_x; try assumption.
    split.
    apply (h_satisfies_hoare_in_env confs hn res_ex res).
    ++ apply t1_preserves; assumption.
    ++ exact e_eval_in_env_x.
    ++ apply FreshEnvOrderChangePreservesHeapSatisfiying with (x1 := x); try assumption.
       assert (t2_preserves := IH_t2 hn x l (StrMap.add v res env) x_fresh_in_t2).
       apply (proj1 t2_preserves).
       apply (h_satisfies_hoare_in_env confs hn res_ex res).
       +++ apply t1_preserves; assumption.
       +++ apply e_eval_in_env_x.
  + intros h_satisfies_hoare_in_env_x.
    intros confs hn res_ex res h_satisfies_t1_in_env e_eval_in_env.
    assert (t1_preserves := IH_t1 h x l env H).
    assert (t2_preserves := IH_t2 hn x l (StrMap.add v res env) x_fresh_in_t2).
    apply (FreshVarPreservesEval h e confs hn res_ex res x l env) in e_eval_in_env; try assumption.
    split.
    apply (h_satisfies_hoare_in_env_x confs hn res_ex res).
    ++ apply t1_preserves; assumption.
    ++ exact e_eval_in_env.
    ++ apply (proj2 t2_preserves).
       apply FreshEnvOrderChangePreservesHeapSatisfiying with (x1 := x); try assumption.
       apply (h_satisfies_hoare_in_env_x confs hn res_ex res).
       +++ apply t1_preserves; assumption.
       +++ exact e_eval_in_env.
Qed.

Lemma FreshVarPreservesSepSatystying : forall t1 t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFISep t1 t2) CC.
Proof.
  intros t1 t2 CC.
  intros t1_preserves t2_preserves.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env (x_fresh_in_t1 & x_fresh_in_t2).
  split.
  + simpl.
    intros (h1 & h2 & disjoint_union & h1_satisfies_t1 & h2_satisfies_t2).
    exists h1, h2.
    assert (h1_satisfies_t1_in_env_x := proj1 (t1_preserves h1 x l env x_fresh_in_t1) h1_satisfies_t1).
    assert (h2_satisfies_t2_in_env_x := proj1 (t2_preserves h2 x l env x_fresh_in_t2) h2_satisfies_t2).
    split; try assumption; split; assumption.
  + simpl.
    intros (h1 & h2 & disjoint_union & h1_satisfies_t1 & h2_satisfies_t2).
    exists h1, h2.
    assert (h1_satisfies_t1_in_env := proj2 (t1_preserves h1 x l env x_fresh_in_t1) h1_satisfies_t1).
    assert (h2_satisfies_t2_in_env := proj2 (t2_preserves h2 x l env x_fresh_in_t2) h2_satisfies_t2).
    split; try assumption; split; assumption.
Qed.

Lemma FreshVarPreservesWandSatystying : forall t1 t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFIWand t1 t2) CC.
Proof.
  intros t1 t2 CC.
  intros t1_preserves t2_preserves.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env (x_fresh_in_t1 & x_fresh_in_t2).
  split.
  + intros h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1.
    apply t1_preserves in h'_satisfies_t1; try assumption.
    destruct (h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1) as (h_h' & h_h'_union & h_h'_satisfies_t2).
    exists h_h'.
    unfold FreshVarPreservesTermSatysfying in t2_preserves.
    apply t2_preserves with (x := x) (l := l) in h_h'_satisfies_t2; try assumption.
    split; assumption.
  + intros h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1.
    apply t1_preserves with (x := x) (l := l) in h'_satisfies_t1; try assumption.
    destruct (h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1) as (h_h' & h_h'_union & h_h'_satisfies_t2).
    exists h_h'.
    unfold FreshVarPreservesTermSatysfying in t2_preserves.
    apply t2_preserves with (x := x) (l := l) in h_h'_satisfies_t2; try assumption.
    split; assumption.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfiying : forall q CC h x l env,
  (JFIVarFreshInTerm x q) ->
    ((JFIHeapSatisfiesInEnv h q env CC) <->
      JFIHeapSatisfiesInEnv h q (StrMap.add x l env) CC).
Proof.
  intros q CC.
  induction q as
    [ | | t1 IH_t1 t2 IH_t2
    | t1 IH_t1 t2 IH_t2
    | t1 IH_t1 t2 IH_t2
    | type name t IH_t
    | type name t IH_t
    | t1 IH_t1 e v t2 IH_t2
    | val1 val2
    | obj field val
    | t1 IH_t1 t2 IH_t2
    | t1 IH_t1 t2 IH_t2
    ];   intros h x l.
  (* JFITrue *)
  + simpl.
    split; trivial.
  (* JFIFalse *)
  + simpl.
    split; trivial.
  (* JFIAnd t1 t2 *)
  + apply FreshVarPreservesAndSatystying; assumption.
  (* JFIOr t1 t2 *)
  + simpl.
    intros env x_fresh.
    destruct x_fresh as (t1_fresh & t2_fresh).
    split; intros [ h_satisfies_t1 | h_satisfies_t2 ].
    ++ apply or_introl.
       apply (IH_t1 h x l env t1_fresh); exact h_satisfies_t1.
    ++ apply or_intror.
       apply (IH_t2 h x l env t2_fresh); exact h_satisfies_t2.
    ++ apply or_introl.
       apply (IH_t1 h x l env t1_fresh); exact h_satisfies_t1.
    ++ apply or_intror.
       apply (IH_t2 h x l env t2_fresh); exact h_satisfies_t2.
  (* JFIImplies t1 t2 *)
  + simpl.
    intros env x_fresh.
    destruct x_fresh as (t1_fresh & t2_fresh);
    split; intros [ not_h_satisfies_t1 | h_satisfies_t2 ].
    ++ apply or_introl.
       unfold not.
       intros h_satisfies_t1.
       apply (IH_t1 h x l env t1_fresh) in h_satisfies_t1.
       exact (not_h_satisfies_t1 h_satisfies_t1).
    ++ apply or_intror.
       apply (IH_t2 h x l env t2_fresh); exact h_satisfies_t2.
    ++ apply or_introl.
       unfold not.
       intros h_satisfies_t1.
       apply (IH_t1 h x l env t1_fresh) in h_satisfies_t1.
       exact (not_h_satisfies_t1 h_satisfies_t1).
    ++ apply or_intror.
       apply (IH_t2 h x l env t2_fresh); exact h_satisfies_t2.
  (* JFIExists *)
  + intros env x_fresh.
    split.
    ++ simpl.
       intros (loc & loc_of_type & h_satisfies_t).
       exists loc.
       split; try assumption.
       apply EnvOrderChangePreservesHeapSatisfiying.
       +++ apply neq_symmetry.
           apply FreshVarDifferentFromForallVar with (class := name) (t := t).
           exact x_fresh.
       +++ apply (IH_t h x l (StrMap.add name loc env)); try assumption.
           simpl in x_fresh.
           destruct (String.eqb name x); try assumption.
           destruct x_fresh.
    ++ simpl.
       intros (loc & loc_of_type & h_satisfies_t).
       exists loc.
       split; try assumption.
       apply EnvOrderChangePreservesHeapSatisfiying in h_satisfies_t.
       +++ apply (IH_t h x l (StrMap.add name loc env)) in h_satisfies_t; try assumption.
           simpl in x_fresh.
           destruct (String.eqb name x); try assumption.
           destruct x_fresh.
       +++ apply FreshVarDifferentFromForallVar with (class := name) (t := t).
           exact x_fresh.
  (* JFIForall *)
  + intros env x_fresh.
    split.
    ++ simpl.
       intros h_satisfies_t loc loc_of_type.
       apply EnvOrderChangePreservesHeapSatisfiying.
       +++ apply neq_symmetry.
           apply FreshVarDifferentFromForallVar with (class := name) (t := t).
           exact x_fresh.
       +++ apply (IH_t h x l (StrMap.add name loc env)).
           - simpl in x_fresh.
             destruct (String.eqb name x); try assumption.
             destruct x_fresh.
           - exact (h_satisfies_t loc loc_of_type).
    ++ simpl.
       intros h_satisfies_t loc loc_of_type.
       set (h_satisfies_t' := h_satisfies_t loc loc_of_type).
       apply EnvOrderChangePreservesHeapSatisfiying in h_satisfies_t'.
       +++ apply (IH_t h x l (StrMap.add name loc env)) in h_satisfies_t'; try assumption.
           simpl in x_fresh.
           destruct (String.eqb name x); try assumption.
           destruct x_fresh.
       +++ apply FreshVarDifferentFromForallVar with (class := name) (t := t).
           exact x_fresh.
  (* JFIHoare *)
  + apply FreshVarPreservesHoareSatystying; assumption.
  (* JFIEq *)
  + intros env x_fresh.
    split;
    apply AddingFreshVarPreservesHeapSatisfiyingEq with (x := x) (l := l);
    exact x_fresh.
  (* JFIFieldEq *)
  + intros env x_fresh.
    split;
    apply AddingFreshVarPreservesHeapSatisfiyingFieldEq with (x := x) (l := l);
    exact x_fresh.
  (* JFISep*)
  + apply FreshVarPreservesSepSatystying; try assumption.
  (* JFIWand *)
  + apply FreshVarPreservesWandSatystying; try assumption.
Qed.

Lemma RemovingFreshVarPreservesHeapSatisfyig : forall h p x l env CC x0,
  (JFIVarFreshInTerm x0 p) ->
  (JFIHeapSatisfiesInEnv h p (StrMap.add x l env) CC) ->
   JFIHeapSatisfiesInEnv h p (StrMap.add x l (StrMap.remove (elt:=Loc) x0 env)) CC.
Proof.
Admitted.

Lemma VarNameChangePreservesHeapSatisfiying : forall h t u v l env CC,
  (JFIHeapSatisfiesInEnv h t (StrMap.add v l env) CC) <->
   JFIHeapSatisfiesInEnv h (JFITermSubstituteVar v u t) (StrMap.add u l env) CC.
Proof.
Admitted.

Lemma HeapSatisfiesSubstIffVarMovedToEnv : forall h x v l p env CC,
  (StrMap.find v env = Some l) ->
  (JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x (JFSyn (JFVar v)) p) env CC <->
   JFIHeapSatisfiesInEnv h p (StrMap.add x l env) CC).
Proof.
Admitted.

(* =============== Equality Lemmas =============== *)

Lemma EqSymmetry : forall h v1 v2 env CC,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env CC) -> 
   JFIHeapSatisfiesInEnv h (JFIEq v2 v1) env CC.
Proof.
  intros h v1 v2 env CC.
  intros v1_eq_v2.
  unfold JFIHeapSatisfiesInEnv.
  unfold JFIHeapSatisfiesInEnv in v1_eq_v2.
  destruct (JFIValToLoc v1 env), (JFIValToLoc v2 env).
  + symmetry.
    exact v1_eq_v2.
  + destruct v1_eq_v2.
  + destruct v1_eq_v2.
  + destruct v1_eq_v2.
Qed.

(* =============== Soundness of basic logical rules =============== *)

Lemma AsmRuleSoundness : forall gamma p CC,
  JFISemanticallyImplies gamma p p CC.
Proof.
  intros gamma p CC.
  intros env h gamma_match_env h_satisfies_p.
  exact h_satisfies_p.
Qed.

Lemma TransRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma p q CC) ->
  (JFISemanticallyImplies gamma q r CC) ->
   JFISemanticallyImplies gamma p r CC.
Proof.
  intros gamma p q r CC.
  intros p_implies_q.
  intros q_implies_r.
  intros env h gamma_match_env h_satisfies_p.
  apply (q_implies_r env h gamma_match_env).
  apply (p_implies_q env h gamma_match_env).
  exact h_satisfies_p.
Qed.

Lemma EqReflRuleSoundness : forall gamma p v CC,
  JFISemanticallyImplies gamma p (JFIEq v v) CC.
Proof.
  intros gamma p v CC.
  intros env h gamma_match_env h_satisfies_p.
  unfold JFIHeapSatisfiesInEnv.

  destruct (JFIValToLoc v env).
  + trivial.
  + admit. (* TODO zapewnic obecnosc zmiennej w srodowisku *)
Admitted.

Lemma EqSymRuleSoundness : forall gamma p v1 v2 CC,
  JFISemanticallyImplies gamma p (JFIEq v1 v2) CC ->
  JFISemanticallyImplies gamma p (JFIEq v2 v1) CC.
Proof.
  intros gamma p v1 v2 CC.
  intros v1_eq_v2.
  intros env h gamma_match_env h_satisfies_p.
  apply EqSymmetry.
  apply (v1_eq_v2 env h).
  + exact gamma_match_env.
  + exact h_satisfies_p.
Qed.

Lemma FalseElimRuleSoundness : forall gamma p q CC,
  (JFISemanticallyImplies gamma p JFIFalse CC) ->
   JFISemanticallyImplies gamma p q CC.
Proof.
  intros gamma p q CC.
  intros p_implies_false.
  intros env h gamma_match_env h_satisfies_p.
  set (h_satisfies_false := p_implies_false env h gamma_match_env h_satisfies_p).
  simpl in h_satisfies_false.
  destruct h_satisfies_false.
Qed.

Lemma TrueIntroRuleSoundness : forall gamma p CC,
  JFISemanticallyImplies gamma p JFITrue CC.
Proof.
  intros gamma p CC.
  intros env h gamma_match_env h_satisfies_p.
  unfold JFIHeapSatisfiesInEnv.
  trivial.
Qed.

Lemma AndIntroRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma r p CC) ->
  (JFISemanticallyImplies gamma r q CC) ->
   JFISemanticallyImplies gamma r (JFIAnd p q) CC.
Proof.
  intros gamma p q r CC.
  intros r_implies_p r_implies_q.
  intros env h gamma_match_env h_satisfies_r.
  simpl.
  split.
  + apply r_implies_p.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
  + apply r_implies_q.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
Qed.

Lemma AndElimRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma r (JFIAnd p q) CC) ->
   JFISemanticallyImplies gamma r p CC /\ JFISemanticallyImplies gamma r q CC.
Proof.
  intros gamma p q r CC.
  intros r_implies_p_and_q.
  split;
  intros env h gamma_match_env h_satisfies_r;
  apply r_implies_p_and_q.
  + exact gamma_match_env.
  + exact h_satisfies_r.
  + exact gamma_match_env.
  + exact h_satisfies_r.
Qed.

Lemma OrIntroRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma r p CC \/ JFISemanticallyImplies gamma r q CC) ->
   JFISemanticallyImplies gamma r (JFIOr p q) CC.
Proof.
  intros gamma p q r CC.
  intros [r_implies_p | r_implies_q]; intros env h gamma_match_env h_satisfies_r; simpl.
  + apply or_introl.
    apply r_implies_p.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
  + apply or_intror.
    apply r_implies_q.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
Qed.

Lemma OrElimRuleSoundness : forall gamma p q r s CC,
  (JFISemanticallyImplies gamma s (JFIOr p q) CC) ->
  (JFISemanticallyImplies gamma (JFIAnd s p) r CC) ->
  (JFISemanticallyImplies gamma (JFIAnd s q) r CC) ->
   JFISemanticallyImplies gamma s r CC.
Proof.
  intros gamma p q r s CC.
  intros s_implies_p_or_q s_and_p_implies_r s_and_q_implies_r.
  intros env h gamma_match_env h_satisfies_s.
  set (p_or_q := s_implies_p_or_q env h gamma_match_env h_satisfies_s).
  destruct p_or_q as [h_satisfies_p | h_satisfies_q].
  + apply (s_and_p_implies_r env h gamma_match_env).
    simpl.
    exact (conj h_satisfies_s h_satisfies_p).
  + apply (s_and_q_implies_r env h gamma_match_env).
    simpl.
    exact (conj h_satisfies_s h_satisfies_q).
Qed.

Lemma ImpliesIntroRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma (JFIAnd r p) q CC) ->
   JFISemanticallyImplies gamma r (JFIImplies p q) CC.
Proof.
  intros gamma p q r CC.
  intros r_and_p_implies_q.
  intros env h gamma_match_env h_satisfies_r.
  simpl.
  simpl in r_and_p_implies_q.
  apply Classical_Prop.imply_to_or.
  intros h_satisfies_p.
  apply r_and_p_implies_q.
  + exact gamma_match_env.
  + apply (conj h_satisfies_r h_satisfies_p).
Qed.

Lemma ImpliesElimRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma r (JFIImplies p q) CC) ->
  (JFISemanticallyImplies gamma r p CC) ->
   JFISemanticallyImplies gamma r q CC.
Proof.
  intros gamma p q r CC.
  intros r_implies_p_implies_q r_implies_p.
  intros env h gamma_match_env h_satisfies_r.
  apply (Classical_Prop.or_to_imply (JFIHeapSatisfiesInEnv h p env CC)).
  + apply r_implies_p_implies_q.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
  + apply r_implies_p.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
Qed.

Lemma ForallIntroRuleSoundness : forall x type gamma gamma_x p q CC,
  (JFIVarFreshInTerm x q) ->
  (JFIGammaAddNew x type gamma = Some gamma_x) ->
  (JFISemanticallyImplies gamma_x q p CC) ->
   JFISemanticallyImplies gamma q (JFIForall type x p) CC.
Proof.
  intros x type gamma gamma_x p q CC.
  intros x_fresh_in_q gamma_add_new_x q_implies_p.
  intros env h gamma_match_env h_satisfies_q.
  simpl.
  intros loc loc_of_type.
  apply q_implies_p.
  + apply StrictlyExtendedGammaMatchesExtendedEnv with (type := type) (gamma := gamma).
    ++ exact gamma_match_env.
    ++ exact loc_of_type.
    ++ exact gamma_add_new_x.
  + apply AddingFreshVarPreservesHeapSatisfiying. (* TODO replace with ,,extending env preserves heap satisfying *)
    ++ exact x_fresh_in_q.
    ++ exact h_satisfies_q.
Qed.

Lemma ForallElimRuleSoundness : forall decls gamma q type x p r v CC,
  (r = JFITermSubstituteVal x (JFSyn v) p) ->
  (JFISemanticallyImplies gamma q (JFIForall type x p) CC) ->
  (JFIRefType decls gamma v = Some type) ->
  (JFIRefFreshInTerm v p) ->
   JFISemanticallyImplies gamma q r CC.
Proof.
  intros decls gamma q type x p r v CC.
  intros r_is_subst q_implies_forall type_of_v v_fresh.
  intros env h gamma_match_env h_satisfies_q.
  assert (h_satisfies_forall := q_implies_forall env h gamma_match_env h_satisfies_q).
  simpl in h_satisfies_forall.
  rewrite r_is_subst.
  destruct v.
  + unfold JFIRefType in type_of_v.
    assert (x0_same_in_gamma_env := gamma_match_env x0).
    destruct (Classical_Prop.classic (exists l, StrMap.MapsTo x0 l env)) as [(l & x0_is_l) | ].
    ++ apply EqualEnvsAreEquivalent with (env1 := env) (env2 := (StrMap.add x0 l (StrMap.remove x0 env))).
       +++ admit. (* TODO remove and add same var is equivalent *)
       +++ apply VarNameChangePreservesHeapSatisfiying.
           unfold JFIRefFreshInTerm in v_fresh.
           rewrite <- StrMapFacts.find_mapsto_iff in type_of_v.
           assert (l_of_type := (proj2 (x0_same_in_gamma_env) l type type_of_v x0_is_l)).
           apply (h_satisfies_forall l) in l_of_type as h_satisfies_p_in_env_x.
           apply RemovingFreshVarPreservesHeapSatisfyig; assumption.
    ++ admit. (* TODO zapewnic zmienna w srodowisku *)
  + admit. (* TODO this *)
Admitted.
Hint Resolve ForallElimRuleSoundness : core.

Lemma ExistsIntroRuleSoundness : forall x v type decls gamma p q CC,
  (JFIRefType decls gamma (JFVar v) = Some type) ->
  (JFISemanticallyImplies gamma q
                (JFITermSubstituteVal x (JFSyn (JFVar v)) p) CC) ->
   JFISemanticallyImplies gamma q (JFIExists type x p) CC.
Proof.
  intros x v type decls gamma p q CC.
  intros type_of_v q_implies_p.
  intros env h gamma_match_env h_satisfies_q.
  simpl.
  simpl in type_of_v.
  destruct (proj1 (gamma_match_env v)) as (gamma_implies_env & _).
  assert (v_in_gamma : StrMap.In v gamma);
    try (apply StrMap_in_find_iff; exists type; assumption).
  apply gamma_implies_env in v_in_gamma.
  apply StrMap_in_find_iff in v_in_gamma.
  destruct v_in_gamma as (l & v_is_l).
  exists l.
  split.
  + rewrite <- StrMapFacts.find_mapsto_iff in type_of_v, v_is_l.
    exact (proj2 (gamma_match_env v) l type type_of_v v_is_l).
  + unfold JFISemanticallyImplies in q_implies_p.
    apply (HeapSatisfiesSubstIffVarMovedToEnv h x v l p env CC v_is_l).
    apply q_implies_p; assumption.
Qed.
Hint Resolve ExistsIntroRuleSoundness : core.

Lemma ExistsElimRuleSoundness : forall gamma decls p q r type x,
  let CC := JFIDeclsProg decls in
  JFIVarFreshInTerm x r ->
  JFIVarFreshInTerm x q ->
  JFISemanticallyImplies gamma r (JFIExists type x p) CC ->
  JFISemanticallyImplies (JFIGammaAdd x type gamma) (JFIAnd r p) q CC ->
  JFISemanticallyImplies gamma r q CC.
Proof.
  intros gamma decls p q r type x CC.
  intros x_fresh_in_r x_fresh_in_q r_implies_exists and_implies_q.
  intros env h gamma_match_env h_satisfies_r.
  assert (h_satisfies_exists := r_implies_exists env h gamma_match_env h_satisfies_r).
  destruct h_satisfies_exists as (l & l_of_type & h_satisfies_p).
  assert (h_satisfies_q := and_implies_q (StrMap.add x l env) h).
  apply AddingFreshVarPreservesHeapSatisfiying with (x := x) (l := l); try assumption.
  apply h_satisfies_q.
  + apply ExtendedGammaMatchesExtendedEnv; assumption.
  + simpl.
    split.
    ++ apply AddingFreshVarPreservesHeapSatisfiying; assumption.
    ++ exact h_satisfies_p.
Qed.
Hint Resolve ExistsElimRuleSoundness : core.

(* =============== Separation rules soundness ===============*)

Definition HeapEq (h1 h2 : Heap) :=
  forall n, Heap.find n h1 = Heap.find n h2.

Lemma EqualHeapsAreEquivalent : forall t CC h1 h2 env,
  (HeapEq h1 h2) ->
    ((JFIHeapSatisfiesInEnv h1 t env CC) <-> (JFIHeapSatisfiesInEnv h2 t env CC)).
Proof.
Admitted.

Definition _HeapUnion (h1 h2 : Heap) := 
  Heap.fold (fun k v a => Heap.add k v a) h1 h2.

Definition _HeapUnion_fold_1 els1 (h2 : Heap) :=
  fold_left (fun a p => Heap.add (fst p) (snd p) a) els1 h2.

Lemma UnionPreservesNonElements : forall l o els1 h2,
  ~(exists o', In (l, o') els1) -> Heap.MapsTo l o h2 ->
   Heap.MapsTo l o (_HeapUnion_fold_1 els1 h2).
Proof.
  intros l o els1.
  induction els1.
  + intros h2 _ l_o_h2.
    simpl.
    exact l_o_h2.
  + intros h2 not_in_els1 l_o_h2.
    simpl.
    apply IHels1.
    ++ intros in_els1.
       apply not_in_els1.
       destruct in_els1 as (o' & o'_in_els1).
       exists o'.
       apply in_cons.
       exact o'_in_els1.
    ++ apply HeapFacts.add_mapsto_iff.
       apply or_intror.
       split; try assumption.
       destruct a.
       simpl.
       intros k_eq_l.
       rewrite k_eq_l in *.
       apply not_in_els1.
       exists o0.
       apply in_eq.
Qed.

Lemma H1SubheapUnion : forall h1 h2,
  JFISubheap h1 (_HeapUnion h1 h2).
Proof.
  intros h1 h2 l o l_o_h1.
  unfold _HeapUnion.
  rewrite Heap.fold_1.
  apply HeapFacts.elements_mapsto_iff in l_o_h1.
  generalize h2.
  assert (no_dup := Heap.elements_3w h1).
  induction (Heap.elements h1).
  + apply InA_nil in l_o_h1.
    destruct l_o_h1.
  + intros h0.
    apply InA_cons in l_o_h1.
    destruct l_o_h1.
    ++ unfold Heap.eq_key_elt, Heap.Raw.Proofs.PX.eqke in H.
       destruct a as (ll, oo).
       simpl in H.
       destruct H as (fst_a_eq & snd_a_eq).
       rewrite <-fst_a_eq, <-snd_a_eq in *.
       simpl.
       apply UnionPreservesNonElements.
       +++ inversion no_dup.
           intros (o' & l_o'_l0).
           apply H1.
           apply InA_eqA with (x := (l, o')).
           - exact HeapEqKeyEquivalence.
           - now unfold Heap.eq_key, Heap.Raw.Proofs.PX.eqk.
           - apply In_InA; try assumption.
             exact HeapEqKeyEquivalence.
       +++ apply HeapFacts.find_mapsto_iff.
           apply HeapFacts.add_eq_o.
           trivial.
    ++ simpl.
       apply (IHl0 H).
       now inversion no_dup.
Qed.

Lemma H2SubheapUnion : forall h1 h2,
  JFIHeapsDisjoint h1 h2 ->
  JFISubheap h2 (_HeapUnion h1 h2).
Proof.
  intros h1 h2 disj.
  intros l o l_o_h2.
  unfold _HeapUnion.
  rewrite Heap.fold_1.
  apply UnionPreservesNonElements; try assumption.
  unfold JFIHeapsDisjoint in disj.
  intros (o', l_o'_h1).
  apply (disj l).
  split.
  + apply HeapFacts.elements_in_iff.
    exists o'.
    apply In_InA; try assumption.
    exact HeapEqKeyEltEquivalence.
  + apply HeapFacts.elements_in_iff.
    exists o.
    apply HeapFacts.elements_mapsto_iff.
    exact l_o_h2.
Qed.

Lemma UnionHasNoExtraElements : forall h1 h2 n,
  Heap.In n (_HeapUnion h1 h2) ->
  Heap.In n h1 \/ Heap.In n h2.
Proof.
  intros h1 h2 n.
  unfold _HeapUnion.
  rewrite Heap.fold_1.
  generalize h2 n.
  clear h2 n.
  assert (el_in_heap : forall n' o', In (n', o') (Heap.elements h1) -> Heap.In n' h1).
  + intros n' o' in_h1.
    apply HeapFacts.elements_in_iff.
    exists o'.
    apply In_InA; try assumption.
    apply HeapEqKeyEltEquivalence.
  + induction (Heap.elements h1).
    ++ intros h2 n n_in_union.
       simpl in n_in_union.
       apply or_intror.
       exact n_in_union.
    ++ intros h2 n n_in_union.
       destruct a as (n' & l').
       simpl in *.
       apply IHl in n_in_union.
       +++ destruct n_in_union as [n_in_h1 | n_in_h2].
           - now apply or_introl.
           - destruct (Classical_Prop.classic (n = n')).
             -- rewrite <- H in *.
                apply or_introl.
                apply (el_in_heap n l').
                now apply or_introl.
             -- apply or_intror.
                apply neq_symmetry in H.
                now rewrite HeapFacts.add_neq_in_iff in n_in_h2.
       +++ intros n'' o'' in_h1.
           apply (el_in_heap n'' o'').
           now apply or_intror.
Qed.

Lemma ExistsUnion : forall h1 h2,
  JFIHeapsDisjoint h1 h2 -> exists h, JFIHeapsUnion h1 h2 h.
Proof.
  intros h1 h2 disj.
  exists (_HeapUnion h1 h2).
  unfold JFIHeapsUnion.
  split; try split.
  + apply H1SubheapUnion.
  + apply H2SubheapUnion.
    exact disj.
  + apply UnionHasNoExtraElements.
Qed.

Lemma InSubheap : forall h1 h2 l,
  JFISubheap h1 h2 -> Heap.In l h1 -> Heap.In l h2.
Proof.
  intros h1 h2 l.
  intros subheap_h1_h2 l_in_h1.
  unfold JFISubheap in subheap_h1_h2.
  apply HeapFacts.elements_in_iff in l_in_h1.
  apply HeapFacts.elements_in_iff.
  destruct l_in_h1 as (o & l_o_h1).
  exists o.
  apply HeapFacts.elements_mapsto_iff in l_o_h1.
  apply HeapFacts.elements_mapsto_iff.
  apply (subheap_h1_h2 l o l_o_h1).
Qed.

Lemma SubheapTransitive : forall h1 h2 h3,
  (JFISubheap h1 h2) -> (JFISubheap h2 h3) -> (JFISubheap h1 h3).
Proof.
  intros h1 h2 h3.
  intros subheap_h1_h2 subheap_h2_h3.
  intros l o l_o_h1.
  apply (subheap_h2_h3 l o).
  now apply (subheap_h1_h2 l o).
Qed.

Lemma UnionSubheap : forall h1 h2 h12 h,
  (JFIHeapsUnion h1 h2 h12) ->
  (JFISubheap h12 h) <-> (JFISubheap h1 h /\ JFISubheap h2 h).
Proof.
  intros h1 h2 h12 h.
  intros (subheap_h1_h12 & subheap_h2_h12 & union_h1_h2).
  split.
    intros subheap_h12_h.
    split.
  + intros l o l_o_h1.
    apply (subheap_h12_h l o).
    now apply (subheap_h1_h12 l o).
  + intros l o l_o_h2.
    apply (subheap_h12_h l o).
    now apply (subheap_h2_h12 l o).
  + intros (subheap_h1_h & subheap_h2_h).
    intros l o l_o_h12.
    apply HeapFacts.elements_mapsto_iff in l_o_h12.
    assert (l_in_h12 : exists o, InA (Heap.eq_key_elt (elt:=Obj)) 
            (l, o) (Heap.elements (elt:=Obj) h12)).
      now exists o.
    apply HeapFacts.elements_in_iff in l_in_h12.
    destruct (union_h1_h2 l l_in_h12).
    ++ apply (subheap_h1_h l o).

       apply HeapFacts.elements_in_iff in H.
       destruct H as (o' & l_o'_h1).
       apply HeapFacts.elements_mapsto_iff in l_o'_h1.
       apply HeapFacts.elements_mapsto_iff in l_o_h12.
       assert (l_o'_h12 := l_o'_h1).
       apply subheap_h1_h12 in l_o'_h12.
       apply HeapFacts.find_mapsto_iff in l_o_h12.
       apply HeapFacts.find_mapsto_iff in l_o'_h12.
       rewrite l_o'_h12 in l_o_h12.
       injection l_o_h12 as o_eq_o'.
       now rewrite o_eq_o' in *.
    ++ apply (subheap_h2_h l o).

       apply HeapFacts.elements_in_iff in H.
       destruct H as (o' & l_o'_h2).
       apply HeapFacts.elements_mapsto_iff in l_o'_h2.
       apply HeapFacts.elements_mapsto_iff in l_o_h12.
       assert (l_o'_h12 := l_o'_h2).
       apply subheap_h2_h12 in l_o'_h12.
       apply HeapFacts.find_mapsto_iff in l_o_h12.
       apply HeapFacts.find_mapsto_iff in l_o'_h12.
       rewrite l_o'_h12 in l_o_h12.
       injection l_o_h12 as o_eq_o'.
       now rewrite o_eq_o' in *.
Qed.

Lemma UnionSymmetry : forall h1 h2 h,
  JFIHeapsUnion h1 h2 h <-> JFIHeapsUnion h2 h1 h.
Proof.
  assert (one_way : forall h1 h2 h, JFIHeapsUnion h1 h2 h -> JFIHeapsUnion h2 h1 h).
  + intros h1 h2 h (subheap_h1_h & subheap_h2_h & union_h1_h2).
    split; try split; try assumption.
    intros l l_in_h.
    destruct (union_h1_h2 l l_in_h).
    ++ now apply or_intror.
    ++ now apply or_introl.
  + intros h1 h2 h.
    split; apply one_way.
Qed.

Lemma UnionAssoc : forall h1 h2 h3 h12 h23 h,
  (JFIHeapsUnion h1 h2 h12 /\ JFIHeapsUnion h2 h3 h23) ->
  (JFIHeapsUnion h1 h23 h) <-> (JFIHeapsUnion h12 h3 h).
Proof.
  intros h1 h2 h3 h12 h23 h.
  intros (union_h1_h2, union_h2_h3).
  split.
  + intros union_h1_h23.
    unfold JFIHeapsUnion in *.
    destruct union_h1_h2, union_h2_h3, union_h1_h23.
    destruct H0, H2, H4.
    split; try split.
    ++ apply (UnionSubheap h1 h2 h12 h).
       now unfold JFIHeapsUnion.
       split; try assumption.
       now apply (SubheapTransitive h2 h23 h).
    ++ apply (UnionSubheap h2 h3 h23 h); try assumption.
       now unfold JFIHeapsUnion.
    ++ intros l l_in_h.
       destruct (H7 l l_in_h) as [l_in_h1 | l_in_h23].
       +++ apply or_introl.
           now apply (InSubheap h1 h12 l).
       +++ destruct (H6 l l_in_h23) as [l_in_h2 | l_in_h3].
           - apply or_introl.
             now apply (InSubheap h2 h12 l).
           - now apply or_intror.
  + intros union_h12_h3.
    unfold JFIHeapsUnion in *.
    destruct union_h1_h2, union_h2_h3, union_h12_h3.
    destruct H0, H2, H4.
    split; try split.
    ++ now apply (UnionSubheap h1 h2 h12 h).
    ++ apply (UnionSubheap h2 h3 h23 h); try assumption.
       now unfold JFIHeapsUnion.
       split; try assumption.
       now apply (SubheapTransitive h2 h12 h).
    ++ intros l l_in_h.
       destruct (H7 l l_in_h) as [l_in_h12 | l_in_h3].
       +++ destruct (H5 l l_in_h12) as [l_in_h1 | l_in_h2].
           - now apply or_introl.
           - apply or_intror.
             now apply (InSubheap h2 h23 l).
       +++ apply or_intror.
           now apply (InSubheap h3 h23 l).
Qed.

Lemma UnionDisjoint : forall h1 h2 h12 h,
  JFIHeapsUnion h1 h2 h12 ->
  JFIHeapsDisjoint h1 h ->
  JFIHeapsDisjoint h2 h ->
  JFIHeapsDisjoint h12 h.
Proof.
  intros h1 h2 h12 h.
  intros (_ & _ & union) disj_h1_h disj_h2_h.
  intros l.
  intros (l_in_h12 & l_in_h).
  destruct (union l); try assumption.
  + now apply (disj_h1_h l).
  + now apply (disj_h2_h l).
Qed.

Lemma UnionIdentity : forall h,
  JFIHeapsUnion (Heap.empty Obj) h h.
Proof.
  intros h.
  split; try split; try easy; auto.
Qed.

Lemma UnionUnique : forall h1 h2 h h',
  JFIHeapsUnion h1 h2 h ->
  JFIHeapsUnion h1 h2 h' ->
  HeapEq h h'.
Proof.
  intros h1 h2 h h'.
  intros (subheap_h1_h & subheap_h2_h & union_h) (subheap_h1_h' & subheap_h2_h' & union_h').
  intros l.
  destruct (Classical_Prop.classic (Heap.In l h)) as [l_in_h | not_l_in_h].
  + destruct (union_h l l_in_h).
    ++ apply HeapFacts.elements_in_iff in H.
       destruct H as (o & l_o_h1).
       apply HeapFacts.elements_mapsto_iff in l_o_h1.
       assert (l_o_h := l_o_h1).
       apply subheap_h1_h' in l_o_h1.
       apply subheap_h1_h in l_o_h.
       apply HeapFacts.find_mapsto_iff in l_o_h1.
       apply HeapFacts.find_mapsto_iff in l_o_h.
       rewrite l_o_h1, l_o_h.
       trivial.
    ++ apply HeapFacts.elements_in_iff in H.
       destruct H as (o & l_o_h2).
       apply HeapFacts.elements_mapsto_iff in l_o_h2.
       assert (l_o_h := l_o_h2).
       apply subheap_h2_h' in l_o_h2.
       apply subheap_h2_h in l_o_h.
       apply HeapFacts.find_mapsto_iff in l_o_h2.
       apply HeapFacts.find_mapsto_iff in l_o_h.
       rewrite l_o_h2, l_o_h.
       trivial.
  + apply HeapFacts.not_find_mapsto_iff in not_l_in_h.
    rewrite not_l_in_h.
    symmetry.
    apply HeapFacts.not_find_mapsto_iff.
    intros l_in_h'.
    apply HeapFacts.not_find_mapsto_iff in not_l_in_h.
    apply not_l_in_h.
    destruct (union_h' l l_in_h').
    ++ apply HeapFacts.elements_in_iff.
       apply HeapFacts.elements_in_iff in H.
       destruct H as (o & l_o_h1).
       exists o.
       apply HeapFacts.elements_mapsto_iff.
       apply HeapFacts.elements_mapsto_iff in l_o_h1.
       now apply (subheap_h1_h l).
    ++ apply HeapFacts.elements_in_iff.
       apply HeapFacts.elements_in_iff in H.
       destruct H as (o & l_o_h2).
       exists o.
       apply HeapFacts.elements_mapsto_iff.
       apply HeapFacts.elements_mapsto_iff in l_o_h2.
       now apply (subheap_h2_h l).
Qed.

Lemma SubheapDisjoint : forall h1 h2 h12 h,
  JFIHeapsUnion h1 h2 h12 ->
  JFIHeapsDisjoint h12 h ->
  JFIHeapsDisjoint h1 h.
Proof.
  intros h1 h2 h12 h.
  intros (subheap_h1_h12 & _ & _) disj_h12_h.
  intros l (l_in_h1 & l_in_h).
  apply (disj_h12_h l).
  split; try assumption.
  apply HeapFacts.elements_in_iff.
  apply HeapFacts.elements_in_iff in l_in_h1.
  destruct l_in_h1 as (o & l_o_h1).
  exists o.
  apply HeapFacts.elements_mapsto_iff.
  apply HeapFacts.elements_mapsto_iff in l_o_h1.
  now apply (subheap_h1_h12 l).
Qed.

Lemma DisjointSymmetry : forall h1 h2,
  JFIHeapsDisjoint h1 h2 <-> JFIHeapsDisjoint h2 h1.
Proof.
  assert (one_way : forall h1 h2, JFIHeapsDisjoint h1 h2 -> JFIHeapsDisjoint h2 h1).
  + intros h1 h2 disj.
    intros l (l_in_h2 & l_in_h1).
    now apply (disj l).
  + intros h1 h2.
    split; apply one_way.
Qed.

Lemma UnionMatchesGamma : forall gamma h1 h2 h1_h2 env,
  JFIHeapsUnion h1 h2 h1_h2 ->
  JFIGammaMatchEnv h1 gamma env ->
  JFIGammaMatchEnv h2 gamma env ->
  JFIGammaMatchEnv h1_h2 gamma env.
Proof.
Admitted.

Definition EnvRestrictedToHeap (env : JFITermEnv) (h' : Heap)  (env' : JFITermEnv):=
  (forall x, StrMap.In x env <-> StrMap.In x env') /\
  (forall x n, StrMap.MapsTo x (JFLoc n) env' -> Heap.In n h').

Lemma RestrictEnvToHeap : forall env h', exists env', EnvRestrictedToHeap env h' env'.
Proof.
Admitted.

Lemma RestrictedEnvMatchesGamma : forall gamma env h env' h',
  JFIGammaMatchEnv h gamma env ->
  JFISubheap h' h ->
  EnvRestrictedToHeap env h' env' ->
  JFIGammaMatchEnv h' gamma env'.
Proof.
Admitted.

Lemma RestrictedEnvPreservesHeapSatisfying : forall h p env env' CC,
  EnvRestrictedToHeap env h env' ->
  (JFIHeapSatisfiesInEnv h p env CC <-> JFIHeapSatisfiesInEnv h p env' CC).
Proof.
Admitted.

Lemma EmptyHeapSatisfiesPersistentTerm : forall h p env CC,
  JFITermPersistent p ->
  JFIHeapSatisfiesInEnv h p env CC ->
  JFIHeapSatisfiesInEnv (Heap.empty Obj) p env CC.
Proof.
Admitted.

Lemma SepAssoc1Soundness : forall decls gamma p1 p2 p3,
  JFISemanticallyImplies gamma
    (JFISep p1 (JFISep p2 p3))
    (JFISep (JFISep p1 p2) p3) (JFIDeclsProg decls).
Proof.
  intros decls gamma p1 p2 p3.
  intros env h gamma_match_env h_satisfies_q.
  destruct h_satisfies_q as (h1 & h23 & (union_h1_h23 & disj_h1_h23) & h1_satisfies_p1 &
          h2 & h3 & (union_h2_h3 & disj_h2_h3) & h_2_satisfies_p2 & h3_satisfies_p3).
  simpl.
  destruct (ExistsUnion h1 h2) as (h12, union_h1_h2).
  + apply DisjointSymmetry.
    apply (SubheapDisjoint h2 h3 h23 h1); try assumption.
    apply DisjointSymmetry.
    exact disj_h1_h23.
  + exists h12, h3.
    split; try split; try trivial.
    ++ now apply (UnionAssoc h1 h2 h3 h12 h23).
    ++ apply (UnionDisjoint h1 h2 h12 h3); try assumption.
       apply DisjointSymmetry.
       apply (SubheapDisjoint h3 h2 h23 h1); try (apply DisjointSymmetry; assumption).
       apply UnionSymmetry.
       assumption.
    ++ exists h1, h2.
       split; try split; trivial.
       apply DisjointSymmetry.
       apply (SubheapDisjoint h2 h3 h23 h1); try apply DisjointSymmetry; assumption.
Qed.
Hint Resolve SepAssoc1Soundness : core.

Lemma SepAssoc2Soundness : forall decls gamma p1 p2 p3,
  JFISemanticallyImplies gamma
    (JFISep (JFISep p1 p2) p3)
    (JFISep p1 (JFISep p2 p3)) (JFIDeclsProg decls).
Proof.
  intros decls gamma p1 p2 p3.
  intros env h gamma_match_env h_satisfies_q.
  destruct h_satisfies_q as (h12 & h3 & (union_h1_h23 & disj_h1_h23) &
      ((h1 & h2 & (union_h1_h2 & disjoint_h1_h2) & (h1_satisfies_p1 & h2_satisfies_p2)) &
       h3_satisfies_p3)).
  simpl.

  destruct (ExistsUnion h2 h3) as (h23 & h2_h3_union).
  + apply (SubheapDisjoint h2 h1 h12 h3); try assumption.
    now apply UnionSymmetry.
  + exists h1, h23.
    split; try split; try trivial.
    ++ now apply (UnionAssoc h1 h2 h3 h12 h23).
    ++ apply DisjointSymmetry.
        apply (UnionDisjoint h2 h3 h23 h1); try assumption.
        +++ apply DisjointSymmetry.
            assumption.
        +++ apply DisjointSymmetry.
            apply (SubheapDisjoint h1 h2 h12 h3); try assumption.
    ++ exists h2, h3.
       split; try split; trivial.
       apply (SubheapDisjoint h2 h1 h12 h3); try apply UnionSymmetry; assumption.
Qed.
Hint Resolve SepAssoc2Soundness : core.

Lemma SepCommRuleSoundness : forall decls gamma p1 p2,
  JFISemanticallyImplies gamma (JFISep p1 p2) (JFISep p2 p1) (JFIDeclsProg decls).
Proof.
  intros decls gamma p1 p2.
  intros env h gamma_match_env h_satisfies_sep.
  destruct h_satisfies_sep as (h1 & h2 & (union_h2_h2 & disjoint_h1_h2) & h_satisfies_p1 & h2_satisfies_p2).
  exists h2, h1.
  split; split; try assumption.
  + apply UnionSymmetry.
    assumption.
  + apply DisjointSymmetry.
    assumption.
Qed.
Hint Resolve SepCommRuleSoundness : core.

Lemma ImplicationToRestrictedImplication : forall gamma env h h' p q CC,
  JFISubheap h' h ->
  JFIGammaMatchEnv h gamma env ->
  JFISemanticallyImplies gamma p q CC ->
  JFIHeapSatisfiesInEnv h' p env CC ->
  JFIHeapSatisfiesInEnv h' q env CC.
Proof.
  intros gamma env h h' p q CC.
  intros h'_subheap gamma_match_env p_implies_q h'_satisfies_p.
  destruct (RestrictEnvToHeap env h') as (env' & env'_restricted).
  assert (gamma_match_env' := RestrictedEnvMatchesGamma _ _ _ _ _ gamma_match_env h'_subheap env'_restricted).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env') in h'_satisfies_p; try assumption.
  assert (h'_satisfies_q := p_implies_q env' h' gamma_match_env' h'_satisfies_p).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env'); try assumption.
Qed.

Lemma SepIntroSoundness : forall decls gamma p1 q1 p2 q2,
  let CC := JFIDeclsProg decls in
  JFISemanticallyImplies gamma p1 q1 CC ->
  JFISemanticallyImplies gamma p2 q2 CC ->
  JFISemanticallyImplies gamma (JFISep p1 p2) (JFISep q1 q2) CC.
Proof.
  intros decls gamma p1 q1 p2 q2 CC.
  intros p1_implies_q1 p2_implies_q2.
  intros env h gamma_match_env h_satisfies_sep.
  destruct h_satisfies_sep as (h1 & h2 & (union_h1_h2 & disjoint_h1_h2) & h1_satisfies_p1 & h2_satisfies_p2).

  exists h1, h2.
  split; split; try assumption.
  + apply ImplicationToRestrictedImplication with (gamma := gamma) (h := h) (p := p1); try assumption.
    exact (proj1 union_h1_h2).
  + apply ImplicationToRestrictedImplication with (gamma := gamma) (h := h) (p := p2); try assumption.
    exact (proj1 (proj2 union_h1_h2)).
Qed.
Hint Resolve SepIntroSoundness : core.

Lemma SepIntroPersistentSoundness : forall decls gamma p q,
  let CC := (JFIDeclsProg decls) in
  JFITermPersistent p ->
  JFISemanticallyImplies gamma (JFIAnd p q) (JFISep p q) CC.
Proof.
  intros decls gamma p q CC.
  intros p_persistent.
  intros env h gamma_match_env h_satisfies_and.
  exists (Heap.empty Obj), h.
  split; split; try assumption.
  + apply UnionIdentity.
  + apply JFIEmptyHeapDisjoint.
  + apply EmptyHeapSatisfiesPersistentTerm with (h := h); try assumption.
    apply h_satisfies_and.
  + simpl in h_satisfies_and.
    apply h_satisfies_and.
Qed.
Hint Resolve SepIntroPersistentSoundness : core.

Lemma WandIntroSoundness : forall decls gamma p q r,
  let CC := JFIDeclsProg decls in
  JFISemanticallyImplies gamma (JFISep r p) q CC ->
  JFISemanticallyImplies gamma r (JFIWand p q) CC.
Proof.
  intros decls gamma p q r CC.
  intros sep_implies_q.
  intros env h gamma_match_env h_satisfies_r.
  intros h' h_disjoint h'_satisfies_p.
  destruct (ExistsUnion h h') as (h_h', union_h_h'); try assumption.
  exists h_h'.
  split; try assumption.
  apply (sep_implies_q env h_h').
  + unfold JFIGammaMatchEnv.
    intros var_name.
    destruct (gamma_match_env var_name) as (gamma_keys_match_env & types_match).
    split; try exact gamma_keys_match_env.
    intros var_loc var_type var_is_type var_is_loc.
    unfold JFILocOfType.
    destruct var_loc; try trivial.
    assert (var_name_type := types_match (JFLoc n) var_type var_is_type var_is_loc).
    unfold JFILocOfType in var_name_type.
    unfold JFIHeapsUnion, JFISubheap in union_h_h'.
    destruct union_h_h' as (h_subheap & h'_subheap & _).
    destruct (Classical_Prop.classic (exists o, Heap.find n h = Some o)).
    ++ destruct H as (o & n_is_o).
       assert (o_in_union := h_subheap n o).
       rewrite n_is_o in var_name_type.
       rewrite <- HeapFacts.find_mapsto_iff in n_is_o.
       apply o_in_union in n_is_o.
       rewrite HeapFacts.find_mapsto_iff in n_is_o.
       rewrite n_is_o.
       destruct o.
       exact var_name_type.
    ++ destruct (Heap.find n h); try destruct var_name_type.
       exfalso.
       apply H.
       exists o.
       trivial.
  + exists h, h'.
    split; split; try assumption.
Qed.
Hint Resolve WandIntroSoundness : core.

Lemma WandElimSoundness : forall decls gamma p q r1 r2,
  let CC := JFIDeclsProg decls in
  JFISemanticallyImplies gamma r1 (JFIWand p q) CC ->
  JFISemanticallyImplies gamma r2 p CC ->
  JFISemanticallyImplies gamma (JFISep r1 r2) q CC.
Proof.
  intros decls gamma p q r1 r2 CC.
  intros r1_implies_wand r2_implies_p.
  intros env h gamma_match_env h_satisfies_r.

  simpl in h_satisfies_r.
  destruct h_satisfies_r as (h1 & h2 & (union_h1_h2 & disjoint_h1_h2) & h1_satisfies_r1 & h2_satisfies_r2).

  destruct (RestrictEnvToHeap env h1) as (env1 & env1_restricted).
  assert (gamma_match_env1 := RestrictedEnvMatchesGamma gamma env h env1 h1 gamma_match_env (proj1 union_h1_h2) env1_restricted).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env1) in h1_satisfies_r1; try assumption.
  unfold JFISemanticallyImplies in r1_implies_wand.
  assert (h1_satisfies_wand := r1_implies_wand env1 h1 gamma_match_env1 h1_satisfies_r1).
  apply RestrictedEnvPreservesHeapSatisfying with (env := env) in h1_satisfies_wand; try assumption.

  destruct (RestrictEnvToHeap env h2) as (env2 & env2_restricted).
  assert (gamma_match_env2 := RestrictedEnvMatchesGamma gamma env h env2 h2 gamma_match_env (proj1 (proj2 union_h1_h2)) env2_restricted).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env2) in h2_satisfies_r2; try assumption.
  assert (h2_satisfies_p := r2_implies_p env2 h2 gamma_match_env2 h2_satisfies_r2).
  apply RestrictedEnvPreservesHeapSatisfying with (env := env) in h2_satisfies_p; try assumption.

  simpl in h1_satisfies_wand.
  destruct (h1_satisfies_wand h2 disjoint_h1_h2 h2_satisfies_p) as (h' & union_h1_h2_h' & h'_satisfies_q).
  apply EqualHeapsAreEquivalent with (h1 := h) (h2 := h'); try assumption.
  apply UnionUnique with (h1 := h1) (h2 := h2); assumption.
Qed.
Hint Resolve WandElimSoundness : core.


(* =============== Jafun reduction Lemmas =============== *)
Ltac Loc_dec_eq l1 l2 l1_eq_l2 :=
  destruct Loc_dec as [_ | l1_neq_l2];
  [ | exfalso; apply l1_neq_l2; exact l1_eq_l2].

Ltac Loc_dec_neq l1 l2 l1_neq_l2 :=
  destruct Loc_dec as [l1_eq_l2 | _];
  [exfalso; apply l1_neq_l2; exact l1_eq_l2 | ].

Lemma IfReductionEq : forall h l1 l2 e1 e2 Ctx Cc env CC,
  (l1 = l2) ->
   red CC (h, (Ctx[[ JFIExprSubstituteEnv env (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ]]_ None) :: Cc) = Some (h, Ctx[[JFIExprSubstituteEnv env e1]]_ None :: Cc).
Proof.
  intros h l1 l2 e1 e2 Ctx Cc env CC.
  intros l1_eq_l2.
  simpl.
  rewrite ValEnvSubstitutionPreservesVLoc.
  rewrite ValEnvSubstitutionPreservesVLoc.
  Loc_dec_eq l1 l2 l1_eq_l2.
  destruct Ctx.
  trivial.
  destruct j; trivial.
Qed.

Lemma IfReductionNeq : forall h l1 l2 e1 e2 Ctx Cc env CC,
  (l1 <> l2) ->
   red CC (h, (Ctx[[ JFIExprSubstituteEnv env (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ]]_ None) :: Cc) = Some (h, Ctx[[JFIExprSubstituteEnv env e2]]_ None :: Cc).
Proof.
  intros h l1 l2 e1 e2 Ctx Cc env CC.
  intros l1_neq_l2.
  simpl.
  rewrite ValEnvSubstitutionPreservesVLoc.
  rewrite ValEnvSubstitutionPreservesVLoc.
  Loc_dec_neq l1 l2 l1_neq_l2.
  destruct Ctx.
  trivial.
  destruct j; trivial.
Qed.

Lemma AllocSucceedsInCorrectProgram : forall prog h cn vs,
  exists newloc newheap, alloc_init prog h cn vs = Some (newloc, newheap).
Proof.
Admitted.

Lemma SuccessfullAllocIsNotNull : forall prog h cn vs newloc newheap,
  (alloc_init prog h cn vs = Some (newloc, newheap)) ->
   newloc <> null.
Proof.
Admitted.

Lemma SuccessfullAllocSetsFields : forall decls h cn vs newloc newheap objflds n field l,
  (alloc_init (JFIDeclsProg decls) h cn vs = Some (newloc, newheap)) ->
  (flds (JFIDeclsProg decls) (JFClass cn) = Some objflds) ->
  (nth_error objflds n = Some field) ->
  (nth_error vs n = Some l) ->
   JFIObjFieldEq newloc field l newheap.
Proof.
Admitted.

(* =============== JFIEval Lemmas =============== *)

Lemma CorrectEvaluationImpliesHoareTriple : forall h p e ex v q env CC,
  (exists confs hn res,
  (JFIHeapSatisfiesInEnv h p env CC) /\ (JFIEvalInEnv h e confs hn ex res env CC) /\ (JFIHeapSatisfiesInEnv hn q (StrMap.add v res env) CC)) ->
   JFIHeapSatisfiesInEnv h (JFIHoare p e ex v q) env CC.
Proof.
  intros h p e ex v q env CC.
  intros (confs & (hn & (res & (h_satisfies_p & (e_eval_hs & hn_satisfies_q))))).
  simpl.
  intros confs' hn' ex' res'.
  intros _ e_eval_confs'.
  set (deterministic := EvaluationIsDeterministic confs confs' h (JFIExprSubstituteEnv env e) hn hn' ex res ex' res' CC e_eval_hs e_eval_confs').
  destruct deterministic as (confs_eq_confs' & (hn_eq_hn' & ex_eq_ex' & res_eq_res')).
  symmetry in hn_eq_hn'.
  symmetry in res_eq_res'.
  rewrite hn_eq_hn', ex_eq_ex', res_eq_res'.
  split; trivial.
Qed.

Lemma HeapSatisfyingWithPreconditionImpliesHoareTriple : forall h p e ex v q env CC,
  ((JFIHeapSatisfiesInEnv h p env CC) -> JFIHeapSatisfiesInEnv h (JFIHoare p e ex v q) env CC) ->
    JFIHeapSatisfiesInEnv h (JFIHoare p e ex v q) env CC.
Proof.
  intros.
  destruct (Classical_Prop.classic (JFIHeapSatisfiesInEnv h p env CC)).
  + apply H.
    assumption.
  + simpl.
    intros.
    destruct (H0 H1).
Qed.

Lemma IfEvaluationStepEq : forall l1 l2 e1 e2 h h' st' confs hn ex res env CC,
  (l1 = l2) ->
  (JFIEvalInEnv h (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ((h', st')::confs) hn ex res env CC) ->
  (h = h' /\ JFIEvalInEnv h' e1 confs hn ex res env CC).
Proof.
  intros l1 l2 e1 e2 h h' st' confs hn ex res env CC.
  intros l1_eq_l2 if_eval.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval in if_eval.
  rewrite IfReductionEq in if_eval.
  + fold JFIPartialEval in if_eval.
    destruct if_eval as (h_eq_h' & (_ & e1_eval)).
    rewrite <- h_eq_h'.
    unfold JFIEval. 
    apply (conj eq_refl e1_eval).
  + exact l1_eq_l2.
Qed.

Lemma IfEvaluationStepNeq : forall l1 l2 e1 e2 h h' st' confs hn ex res env CC,
  (l1 <> l2) ->
  (JFIEvalInEnv h (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ((h', st')::confs) hn ex res env CC) ->
  (h = h' /\ JFIEvalInEnv h' e2 confs hn ex res env CC).
Proof.
  intros l1 l2 e1 e2 h h' st' confs hn ex res env CC.
  intros l1_eq_l2 if_eval.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval in if_eval.
  rewrite IfReductionNeq in if_eval.
  + fold JFIPartialEval in if_eval.
    destruct if_eval as (h_eq_h' & (_ & e2_eval)).
    rewrite <- h_eq_h'.
       unfold JFIEval.
       apply (conj eq_refl e2_eval).
  + exact l1_eq_l2.
Qed.

Lemma NewEvaluationStep : forall prog h ls newloc newheap mu cn vs env CC,
  (alloc_init prog h cn ls = Some (newloc, newheap)) ->
   JFIEvalInEnv h (JFNew mu cn vs) [(h, [ [] [[ JFIExprSubstituteEnv env (JFNew mu cn vs) ]]_ None])] newheap None newloc env CC.
Proof.
Admitted.

Lemma EvaluationPreservesGammaMatching : forall gamma env h e confs hn ex res CC,
  (JFIGammaMatchEnv h gamma env) ->
  (JFIEval h e confs hn ex res CC) ->
  (JFIGammaMatchEnv hn gamma env).
Proof.
Admitted.

Lemma EvaluationPreservesPersistentTerms : forall env s h e confs hn ex res CC,
  (JFITermPersistent s) ->
  (JFIHeapSatisfiesInEnv h s env CC) ->
  (JFIEval h e confs hn ex res CC) ->
   JFIHeapSatisfiesInEnv hn s env CC.
Proof.
Admitted.

(* =============== Soundness of Hoare triple rules =============== *)

Lemma EnsureValIsLoc : forall (v : JFVal),
  exists l, v = JFVLoc l.
Proof.
Admitted.

(* Lemma EnsureValIsLoc_real : forall prog class method e h hs hn v Xi Gamma C mu,
  (JFIPartialEval e h hs hn (JFVal1 v)) ->
  (types prog class method Xi Gamma e (C, mu)) ->
   exists l, v = JFVLoc l.
Proof.
  intros prog class method e h hs hn v Xi Gamma C mu.
  intros eval types_e.
Admitted.
 *)
Lemma EnsureValsMapIsLocsMap : forall vs env,
  exists ls, map (JFIValSubstituteEnv env) vs = map JFVLoc ls.
Proof.
Admitted.

Lemma EnsureValsListIsLocsList : forall ls vs n l env,
  map (JFIValSubstituteEnv env) vs = map JFVLoc ls ->
  (nth_error ls n = Some l <-> nth_error (map (JFIValSubstituteEnv env) vs) n = Some (JFVLoc l)).
(*   exists ls, forall n l, nth_error ls n = Some l <-> nth_error (map (JFIValSubstituteEnv env) vs) n = Some (JFVLoc l). *)
Proof.
  intros ls vs n l env.
  intros vs_is_ls.
  split.
  + intros nth_ls_is_l.
    rewrite vs_is_ls.
    apply List.map_nth_error.
    assumption.
  + intros nth_map.
    rewrite vs_is_ls in nth_map.
    set (JFVLoc_inverse := fun v =>
            match v with
            | JFVLoc l => l
            | _ => null
            end).
    replace l with (JFVLoc_inverse (JFVLoc l)).
    replace ls with (map JFVLoc_inverse (map JFVLoc ls)).
    ++ apply map_nth_error.
       exact nth_map.
    ++ rewrite List.map_map.
       simpl.
       rewrite List.map_id.
       trivial.
    ++ trivial.
Qed.

Lemma EnsureLocInHeap : forall h (n : nat),
  exists (o : Obj), Heap.find n h = Some o.
Proof.
Admitted.

Lemma HTRetRuleSoundness : forall gamma s v w CC,
  JFISemanticallyImplies gamma s
    (JFIHoare JFITrue (JFVal1 w) None v (JFIEq (JFSyn (JFVar v)) w)) CC.
Proof.
  intros gamma s v w CC.
  intros env h gamma_match_env h_satisfies_s.
  set (w_is_loc := EnsureValIsLoc w);
  destruct w_is_loc as (loc & w_is_loc).
  apply CorrectEvaluationImpliesHoareTriple.
  exists [], h, loc.
  split; [ | split].
  + simpl. trivial.
  + unfold JFIEvalInEnv, JFIEval, JFIPartialEval.
    rewrite w_is_loc.
    rewrite ExprEnvSubstitutionPreservesVLoc.
    auto.
  + simpl.
    rewrite StrMapFacts.add_eq_o; try apply eq_refl.
    rewrite w_is_loc.
    unfold JFIValToLoc.
    trivial.
Qed.

Lemma HTPreconditionStrenghtenSoundness : forall gamma s p p' e ex v q CC,
  (JFISemanticallyImplies gamma s (JFIImplies p p') CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare p' e ex v q) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e ex v q) CC.
Proof.
  intros gamma s p p' e ex v q CC.
  intros p_implies_p' hoare_p'.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros hs hn res_ex res.
  intros h_satisfies_p eval_e.
  set (h_satisfies_hoare_p' := hoare_p' env h gamma_match_env h_satisfies_s).
  simpl in h_satisfies_hoare_p'.
  apply (h_satisfies_hoare_p' hs hn res_ex res).
  + destruct (p_implies_p' env h gamma_match_env h_satisfies_s) as [not_h_satisfies_p | h_satisfies_p'].
    ++ destruct (not_h_satisfies_p h_satisfies_p).
    ++ exact h_satisfies_p'.
  + exact eval_e.
Qed.

Lemma HTPostconditionWeakenSoundness : forall gamma s p e ex v q q' cn u CC,
  (JFITermPersistent s) ->
  (JFISemanticallyImplies gamma s (JFIHoare p e ex v q') CC) ->
  (JFISemanticallyImplies gamma s
    (JFIForall cn u
      (JFIImplies (JFITermSubstituteVar v u q')
        (JFITermSubstituteVar v u q))) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e ex v q) CC.
Proof.
  intros gamma s p e ex v q q' cn u CC.
  intros s_persistent hoare_q' q_implies_q'.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros confs hn res_ex res.
  intros h_satisfies_p eval_e.
  assert (h_satisfies_q' := hoare_q' env h gamma_match_env h_satisfies_s confs hn res_ex res h_satisfies_p eval_e);
  fold JFIHeapSatisfiesInEnv in h_satisfies_q'.
  assert (gamma_match_env_in_hn := EvaluationPreservesGammaMatching gamma env h (JFIExprSubstituteEnv env e) confs hn res_ex res CC gamma_match_env eval_e).
  assert (hn_satisfies_s := EvaluationPreservesPersistentTerms env s h (JFIExprSubstituteEnv env e) confs hn res_ex res CC s_persistent h_satisfies_s eval_e).
  assert (h_satisfies_forall := q_implies_q' env hn gamma_match_env_in_hn hn_satisfies_s).
  simpl in h_satisfies_forall.
  destruct (h_satisfies_forall res) as [not_h_satisfies_q' | h_satisfies_q].
  + admit. (* TODO type of res *)
  + exfalso.
    apply not_h_satisfies_q'.
    apply VarNameChangePreservesHeapSatisfiying.
    apply h_satisfies_q'.
  + apply VarNameChangePreservesHeapSatisfiying with (u := u) in h_satisfies_q.
    split.
    ++ apply (proj1 h_satisfies_q').
    ++ apply h_satisfies_q.
Admitted.

Lemma HTCsqRuleSoundness : forall gamma s p p' e ex v q q' cn u CC,
  (JFITermPersistent s) ->
  (JFISemanticallyImplies gamma s (JFIImplies p p') CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare p' e ex v q') CC) ->
  (JFISemanticallyImplies gamma s
    (JFIForall cn u
      (JFIImplies (JFITermSubstituteVar v u q')
        (JFITermSubstituteVar v u q))) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e ex v q) CC.
Proof.
  intros gamma s p p' e ex v q q' cn u CC.
  intros s_persistent p_implies_p' hoare_p'q' q_implies_q'.
  apply HTPostconditionWeakenSoundness with (q':=q') (cn:=cn) (u:=u).
  + exact s_persistent.
  + apply HTPreconditionStrenghtenSoundness with (p':=p').
    ++ exact p_implies_p'.
    ++ exact hoare_p'q'.
  + exact q_implies_q'.
Qed.
Hint Resolve HTCsqRuleSoundness : core.

Lemma HTDisjIntroRuleSoundness : forall gamma s p q e ex v r CC,
  (JFISemanticallyImplies gamma s (JFIHoare p e ex v r) CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare q e ex v r) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare (JFIOr p q) e ex v r) CC.
Proof.
  intros gamma s p q e ex v r CC.
  intros hoare_p_r hoare_q_r.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros confs hn res_ex res.
  intros p_or_q e_eval.
  destruct p_or_q.
  + exact (hoare_p_r env h gamma_match_env h_satisfies_s confs hn res_ex res H e_eval).
  + exact (hoare_q_r env h gamma_match_env h_satisfies_s confs hn res_ex res H e_eval).
Qed.
Hint Resolve HTDisjIntroRuleSoundness : core.

Lemma HTDisjElimRuleSoundness : forall gamma s p q e ex v r CC,
  (JFISemanticallyImplies gamma s (JFIHoare (JFIOr p q) e ex v r) CC) ->
    (JFISemanticallyImplies gamma s (JFIHoare p e ex v r) CC) /\
    (JFISemanticallyImplies gamma s (JFIHoare q e ex v r) CC).
Proof.
  intros gamma s p q e ex v r CC.
  intros hoare_pq_r.
  split;
    intros env h gamma_match_env h_satisfies_s confs hn res_ex res;
    assert (asdf := hoare_pq_r env h gamma_match_env h_satisfies_s confs hn res_ex res);
    fold JFIHeapSatisfiesInEnv in asdf;
    simpl in *;
    intros h_satisfies_pre e_eval.
  + exact (asdf (or_introl h_satisfies_pre) e_eval).
  + exact (asdf (or_intror h_satisfies_pre) e_eval).
Qed.

Lemma HTDisjElimLRuleSoundness : forall gamma s p q e ex v r CC,
  (JFISemanticallyImplies gamma s (JFIHoare (JFIOr p q) e ex v r) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e ex v r) CC.
Proof.
  intros.
  apply HTDisjElimRuleSoundness with (q := q).
  assumption.
Qed.
Hint Resolve HTDisjElimLRuleSoundness : core.

Lemma HTDisjElimRRuleSoundness : forall gamma s p q e ex v r CC,
  (JFISemanticallyImplies gamma s (JFIHoare (JFIOr p q) e ex v r) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare q e ex v r) CC.
Proof.
  intros.
  apply HTDisjElimRuleSoundness with (p := p).
  assumption.
Qed.
Hint Resolve HTDisjElimRRuleSoundness : core.

Lemma HTEqRule1Soundness : forall gamma s p v1 v2 e ex v q CC,
  (JFISemanticallyImplies gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e ex v q) CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e ex v q) CC).
Proof.
  intros gamma s p v1 v2 e ex v q CC.
  intros p_eq_implies_hoare.
  intros env h gamma_match_env h_satisfies_s confs hn res_ex res.
  simpl.
  destruct (EnsureValIsLoc v1) as (l1 & v1_is_l1).
  destruct (EnsureValIsLoc v2) as (l2 & v2_is_l2).

  assert (hoare_p_q := p_eq_implies_hoare env h gamma_match_env).
  simpl in hoare_p_q.
  rewrite v1_is_l1, v2_is_l2 in *.
  unfold JFIValToLoc in *.
  intros (h_satisfies_p & l1_eq_l2) e_eval.
  exact (hoare_p_q (conj h_satisfies_s l1_eq_l2) confs hn res_ex res h_satisfies_p e_eval).
Qed.
Hint Resolve HTEqRule1Soundness : core.

Lemma HTEqRule2Soundness : forall gamma s p v1 v2 e ex v q CC,
  (JFISemanticallyImplies gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e ex v q) CC) ->
  (JFISemanticallyImplies gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e ex v q) CC).
Proof.
  intros gamma s p v1 v2 e ex v q CC.
  intros hoare_peq_q.
  intros env h gamma_match_env h_satisfies_s_eq confs hn res_ex res.
  simpl.
  intros h_satisfies_p e_eval.
  simpl in h_satisfies_s_eq.
  destruct h_satisfies_s_eq as (h_satisfies_s & l1_eq_l2).

  assert (hn_satisfies_q := hoare_peq_q env h gamma_match_env h_satisfies_s confs hn res_ex res).
  fold JFIHeapSatisfiesInEnv in hn_satisfies_q.
  simpl in hn_satisfies_q.

  destruct (EnsureValIsLoc v1) as (l1 & v1_is_l1).
  destruct (EnsureValIsLoc v2) as (l2 & v2_is_l2).
  rewrite v1_is_l1, v2_is_l2 in l1_eq_l2, hn_satisfies_q.
  unfold JFIValToLoc in l1_eq_l2, hn_satisfies_q.

  exact (hn_satisfies_q (conj h_satisfies_p l1_eq_l2) e_eval).
Qed.
Hint Resolve HTEqRule2Soundness : core.

Lemma HTNewNotNullRuleSoundness : forall gamma s p mu cn vs v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare p (JFNew mu cn vs) None v
     (JFIImplies (JFIEq (JFSyn (JFVar v)) JFnull) JFIFalse)) CC.
Proof.
  intros gamma s p mu cn vs v CC.
  intros env h gamma_match_env h_satisfies_s.
  destruct (EnsureValsMapIsLocsMap vs env) as (ls & vs_is_ls).
  destruct (AllocSucceedsInCorrectProgram CC h cn ls)
    as (newloc & (newheap & alloc_newloc_newheap)).
  apply HeapSatisfyingWithPreconditionImpliesHoareTriple.
  intros h_satisfies_p.
  apply CorrectEvaluationImpliesHoareTriple.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env (JFNew mu cn vs) ]]_ None])], newheap, newloc.
  split; [ | split].
  + exact h_satisfies_p.
  + apply NewEvaluationStep with (prog := CC) (ls := ls); assumption.
  + simpl.
    apply or_introl.
    rewrite StrMapFacts.add_eq_o.
    ++ apply (SuccessfullAllocIsNotNull CC h cn ls newloc newheap alloc_newloc_newheap).
    ++ trivial.
Qed.
Hint Resolve HTNewNotNullRuleSoundness : core.

Lemma HTNewFieldRuleSoundness : forall decls gamma cn objflds vs n field value s p mu v CC,
  (flds (JFIDeclsProg decls) (JFClass cn) = Some objflds) ->
  (nth_error objflds n = Some field) ->
  (nth_error vs n = Some value) ->
    JFISemanticallyImplies gamma s
      (JFIHoare p (JFNew mu cn vs) None v (JFIFieldEq (JFSyn (JFVar v)) field value)) CC.
Proof.
  intros decls gamma cn objflds vs n field value s p mu v CC.
  intros fdls_of_cn nth_field nth_value.
  intros env h gamma_match_env h_satisfies_s.
  destruct (EnsureValsMapIsLocsMap vs env) as (ls & vs_map_is_ls).
  destruct (EnsureValIsLoc value) as (l & value_is_l).
  set (vs_is_ls := EnsureValsListIsLocsList ls vs n l env vs_map_is_ls).
  destruct (AllocSucceedsInCorrectProgram (JFIDeclsProg decls) h cn ls)
    as (newloc & (newheap & alloc_newloc_newheap)).
  apply HeapSatisfyingWithPreconditionImpliesHoareTriple.
  intros h_satisfies_p.
  apply CorrectEvaluationImpliesHoareTriple.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env (JFNew mu cn vs) ]]_ None])], newheap, newloc.
  split; [assumption | split].
  + apply NewEvaluationStep with (prog := JFIDeclsProg decls) (ls := ls); assumption.
  + simpl.
    unfold JFIValToLoc.
    rewrite value_is_l.
    rewrite StrMapFacts.add_eq_o.
    ++ apply (SuccessfullAllocSetsFields decls h cn ls newloc newheap objflds n field l); try assumption.
       apply vs_is_ls.
       replace (JFVLoc l) with (JFIValSubstituteEnv env (JFVLoc l)).
       +++ apply List.map_nth_error.
           rewrite <- value_is_l.
           exact nth_value.
       +++ apply ValEnvSubstitutionPreservesVLoc.
    ++ trivial.
Qed.
Hint Resolve HTNewFieldRuleSoundness : core.

Lemma AddingFreshVarInsidePreservesHeapSatisfiying : forall q h env x1 l1 x2 l2 CC,
   (JFIVarFreshInTerm x2 q) ->
   (JFIHeapSatisfiesInEnv h q (StrMap.add x1 l1 (StrMap.add x2 l2 env)) CC) ->
    JFIHeapSatisfiesInEnv h q (StrMap.add x1 l1 env) CC.
Proof.
Admitted.

Lemma SubstituteLocIffSubstituteVarInEnv : forall h env x v l q CC,
  (JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x (JFVLoc l) q) env CC) <->
   JFIHeapSatisfiesInEnv h (JFITermSubstituteVar x v q) (StrMap.add v l env) CC.
Proof.
Admitted.

Lemma SubstituteEnvVarElim : forall x v l e env,
  JFIExprSubstituteEnv (StrMap.add v l env) (JFIExprSubstituteVar x v e) =
  JFIExprSubstituteEnv env (JFIExprSubstituteVal x (JFVLoc l) e).
Proof.
Admitted.

Lemma LetRuleE1Soundness : forall h' x e1_res q env CC,
  (JFIHeapSatisfiesInEnv h' q (StrMap.add x e1_res env) CC) ->
  JFIHeapSatisfiesInEnv h' (JFITermSubstituteVal x (JFVLoc e1_res) q) env CC.
Proof.
    intros h' x e1_res q env CC.
    intros h'_satisfies_q.
    apply (SubstituteLocIffSubstituteVarInEnv h' env x x e1_res q).
    unfold JFITermSubstituteVar.
    rewrite TermSubstituteIdentity.
    exact h'_satisfies_q.
Qed.

Lemma LetRuleE2Soundness : forall h' x e1_res e2 confs_e2 hn res_ex res class v q ex u r env CC,
  (JFILocOfType e1_res h' class) ->
  (JFIVarFreshInTerm v r) ->
  (JFIEvalInEnv h' (JFIExprSubstituteVal x (JFVLoc e1_res) e2) confs_e2 hn res_ex res env CC) ->
  (JFIHeapSatisfiesInEnv h' (JFITermSubstituteVal x (JFVLoc e1_res) q) env CC) ->
  (JFIHeapSatisfiesInEnv h' (JFIForall class v (JFIHoare (JFITermSubstituteVar x v q) (JFIExprSubstituteVar x v e2) ex u r)) env CC) ->
  (res_ex = ex /\ JFIHeapSatisfiesInEnv hn r (StrMap.add u res env) CC).
Proof.
  intros h' x e1_res e2 confs_e2 hn res_ex res class v q ex u r env CC.
  intros e1_res_type v_fresh_in_r e2_eval h'_satisfies_q h'_satisfies_forall.
  assert (tmp := h'_satisfies_forall e1_res e1_res_type confs_e2 hn res_ex res).
  fold JFIHeapSatisfiesInEnv in tmp.
  simpl in tmp.
  split.
  + apply tmp.
    ++ apply SubstituteLocIffSubstituteVarInEnv.
       assumption.
    ++ unfold JFIEvalInEnv.
       rewrite SubstituteEnvVarElim.
       assumption.
  + apply AddingFreshVarInsidePreservesHeapSatisfiying with (x2 := v) (l2 := e1_res); try assumption.
    apply tmp.
    ++ apply SubstituteLocIffSubstituteVarInEnv.
       assumption.
    ++ unfold JFIEvalInEnv.
       rewrite SubstituteEnvVarElim.
       assumption.
Qed.

Lemma HTLetRuleSoundness : forall gamma s p e1 e2 class x q v ex u r CC,
  (JFITermPersistent s) ->
  (JFIVarFreshInTerm v r) ->
  (JFISemanticallyImplies gamma s (JFIHoare p e1 None x q) CC) ->
  (JFISemanticallyImplies gamma s
          (JFIForall class v
             (JFIHoare
                (JFITermSubstituteVar x v q)
                (JFIExprSubstituteVar x v e2) ex u r)) CC) ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFLet class x e1 e2) ex u r) CC.
Proof.
  intros gamma s p e1 e2 class x q v ex u r CC.
  intros s_persistent v_fresh_in_r IH_e1 IH_e2.
  intros env h gamma_match_env.
  intros h_satisfies_s confs hn res_ex res new_env h_satisfies_p let_eval.

  set (let_evaluation := LetEvaluation h class x e1 e2 confs hn res res_ex env CC let_eval).
  destruct let_evaluation as
    [(confs_e1 & confs_e2 & h' & e1_res & e1_eval & e2_eval) | (confs_e1 & e1_ex & ex_eq & e1_eval)].
  + apply LetRuleE2Soundness with (h' := h') (x := x) (e1_res := e1_res) (e2 := e2)
      (confs_e2 := confs_e2) (class := class) (ex := ex) (v := v) (q := q).
    ++ admit. (* e1_res type *)
    ++ assumption.
    ++ assumption.
    ++ apply LetRuleE1Soundness.
       apply (IH_e1 env h gamma_match_env h_satisfies_s confs_e1 h' None e1_res); assumption.
    ++ apply IH_e2.
       +++ apply EvaluationPreservesGammaMatching with (h := h) (e := (JFIExprSubstituteEnv env e1))
             (confs := confs_e1) (ex := None) (res := e1_res) (CC := CC); assumption.
       +++ apply EvaluationPreservesPersistentTerms with (h := h) (e := (JFIExprSubstituteEnv env e1))
             (confs := confs_e1) (ex := None) (res := e1_res); assumption.
  + rewrite ex_eq in *.
    assert (some_is_none := IH_e1 env h gamma_match_env h_satisfies_s confs_e1 hn (Some e1_ex) res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in some_is_none.
    discriminate (proj1 some_is_none).
Admitted.
Hint Resolve HTLetRuleSoundness : core.

Lemma HTLetExSoundness : forall gamma s p class x e1 e2 ex u q CC,
  JFISemanticallyImplies gamma s (JFIHoare p e1 (Some ex) u q) CC ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFLet class x e1 e2) (Some ex) u q) CC.
Proof.
  intros gamma s p class x e1 e2 ex u q CC.
  intros IH_e1.
  intros env h gamma_match_env.
  intros h_satisfies_s confs hn res_ex res new_env h_satisfies_p let_eval.

  set (let_evaluation := LetEvaluation h class x e1 e2 confs hn res res_ex env CC let_eval).
  destruct let_evaluation as
    [(confs_e1 & confs_e2 & h' & e1_res & e1_eval & e2_eval) | (confs_e1 & e1_ex & ex_eq & e1_eval)].
  + assert (some_is_none := IH_e1 env h gamma_match_env h_satisfies_s confs_e1 h' None e1_res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in some_is_none.
    discriminate (proj1 some_is_none).
  + rewrite ex_eq in *.
    assert (e1_ex_eq_ex := IH_e1 env h gamma_match_env h_satisfies_s confs_e1 hn (Some e1_ex) res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in e1_ex_eq_ex.
    unfold new_env.
    destruct e1_ex_eq_ex as (e1_ex_eq_ex & asdf).
    split; trivial.
Qed.
Hint Resolve HTLetExSoundness : core.

Lemma HTFieldSetRuleSoundness : forall gamma s x field loc v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIImplies (JFIEq x JFnull) JFIFalse) (JFAssign (x, field) (JFVLoc loc))
     None v (JFIFieldEq x field (JFVLoc loc))) CC.
Proof.
  intros gamma s x field loc v CC.
  intros env h gamma_match_env h_satisfies_s.
  destruct (EnsureValIsLoc x) as (x_l & x_is_x_l).
  rewrite x_is_x_l.
  destruct (Classical_Prop.classic (exists n, x_l = JFLoc n)) as [(x_n & x_is_x_n) | x_null].
  + apply CorrectEvaluationImpliesHoareTriple.
    simpl.
    destruct (EnsureLocInHeap h x_n) as ((obj & cn) & x_points_to_o).
    set (new_obj := ((JFXIdMap.add field loc obj) , cn) : Obj).
    set (new_h := Heap.add x_n new_obj h).
    exists [(h, [ [] [[ (JFAssign (JFVLoc x_l, field) (JFVLoc loc)) ]]_ None])], new_h, loc.
    split.
    ++ apply or_introl.
       apply LocNotNullIff.
       exists x_n.
       assumption.
    ++ split.
       +++ unfold JFIEvalInEnv, JFIEval, JFIPartialEval.
           split; try trivial.
           unfold JFIExprSubstituteEnv.
           rewrite ValEnvSubstitutionPreservesVLoc.
           rewrite ValEnvSubstitutionPreservesVLoc.
           unfold red.
           rewrite x_is_x_n.
           rewrite x_points_to_o.
           split; try split.
           - fold new_obj.
             unfold new_h.
             trivial.
           - auto.
       +++ unfold JFIObjFieldEq.
           rewrite x_is_x_n.
           unfold new_h.
           rewrite HeapFacts.add_eq_o; try trivial.
           unfold new_obj.
           rewrite JFXIdMapFacts.add_eq_o; trivial.
  + simpl.
    intros * * * [x_not_null | false].
    ++ rewrite LocNotNullIff in x_null.
       destruct (x_null x_not_null).
    ++ destruct false.
Qed.
Hint Resolve HTFieldSetRuleSoundness : core.

Lemma ValEval : forall h v ex confs hn v' ex' CC,
  JFIPartialEval h [ [] [[JFVal1 v ]]_ ex] confs hn [ [] [[JFVal1 v' ]]_ ex'] CC ->
  (ex = ex' /\ v = v').
Proof.
  intros h v ex confs hn v' ex' CC.
  intros eval.
  unfold JFIPartialEval in eval.
  destruct confs.
  + destruct eval as (_ & st_eq).
    injection st_eq.
    intros ex_eq v_eq.
    rewrite ex_eq, v_eq.
    split; trivial.
  + destruct p.
    destruct eval as (_ & _ & val_red).
    fold JFIPartialEval in val_red.
    unfold red in val_red.
    destruct v, ex; destruct val_red.
Qed.

Lemma NPEEval : forall h confs hn res res_ex v env CC,
  JFIPartialEval h [ [] [[JFVal1 NPE_val ]]_ NPE_mode] confs hn
                   [ [] [[JFVal1 (JFVLoc res) ]]_ res_ex] CC ->
  (res_ex = NPE_mode /\ JFIHeapSatisfiesInEnv hn (JFIEq (JFSyn (JFVar v)) NPE_val) (StrMap.add v res env) CC).
Proof.
  intros h confs hn res res_ex v env CC.
  intros eval.
  apply ValEval in eval as (ex_is_npe & res_is_npe).
  split; try (symmetry; assumption).
  simpl.
  rewrite StrMapFacts.add_eq_o; trivial.
  unfold NPE_val in res_is_npe.
  injection res_is_npe as res_is_npe.
  rewrite res_is_npe.
  trivial.
Qed.

Lemma HTNullFieldSetRuleSoundness : forall gamma s x field loc v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFnull) (JFAssign (x, field) (JFVLoc loc))
     NPE_mode v (JFIEq (JFSyn (JFVar v)) NPE_val)) CC.
Proof.
  intros gamma s x field loc v CC.
  intros env h gamma_match_env h_satisfies_s.
  intros confs hn res_ex res newEnv x_is_null eval.
  unfold newEnv.
  simpl in x_is_null.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval, JFIExprSubstituteEnv in eval.
  destruct confs; try discriminate (proj2 eval).
  fold JFIPartialEval in *.
  destruct p in eval.
  destruct eval as (h_eq & st_eq & assign_red).
  destruct x as [ | x]; try destruct x.
  + unfold JFIValToLoc in x_is_null.
    rewrite x_is_null in *.
    rewrite ValEnvSubstitutionPreservesVLoc in assign_red.
    unfold red in assign_red.
    destruct (JFIValSubstituteEnv env (JFVLoc loc)); try destruct assign_red.
    apply NPEEval with (v := v) (env := env) in assign_red.
    exact assign_red.
  + unfold JFIValToLoc in x_is_null.
    rewrite ValEnvSubstitutionReplacesVarInEnv with (l := null) in assign_red.
    ++ unfold red in assign_red.
       destruct (JFIValSubstituteEnv env (JFVLoc loc)); try destruct assign_red.
       apply NPEEval with (v := v) (env := env) in assign_red.
       exact assign_red.
    ++ destruct (StrMap.find (elt:=Loc) x env); try destruct x_is_null.
       trivial.
  + unfold JFIValToLoc in x_is_null.
    discriminate x_is_null.
Qed.
Hint Resolve HTNullFieldSetRuleSoundness : core.

Lemma HTNullFieldGetRuleSoundness : forall gamma s x field v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFnull) (JFVal2 (x, field))
     NPE_mode v (JFIEq (JFSyn (JFVar v)) NPE_val)) CC.
Proof.
  intros gamma s x field v CC.
  intros env h gamma_match_env h_satisfies_s.
  intros confs hn res_ex res newEnv x_is_null eval.
  unfold newEnv.
  simpl in x_is_null.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval, JFIExprSubstituteEnv in eval.
  destruct confs; try discriminate (proj2 eval).
  fold JFIPartialEval in *.
  destruct p in eval.
  destruct eval as (h_eq & st_eq & assign_red).
  destruct x as [ | x]; try destruct x.
  + unfold JFIValToLoc in x_is_null.
    rewrite x_is_null in *.
    rewrite ValEnvSubstitutionPreservesVLoc in assign_red.
    unfold red in assign_red.
    apply NPEEval with (v := v) (env := env) in assign_red.
    exact assign_red.
  + unfold JFIValToLoc in x_is_null.
    rewrite ValEnvSubstitutionReplacesVarInEnv with (l := null) in assign_red.
    ++ unfold red in assign_red.
       apply NPEEval with (v := v) (env := env) in assign_red.
       exact assign_red.
    ++ destruct (StrMap.find (elt:=Loc) x env); try destruct x_is_null.
       trivial.
  + unfold JFIValToLoc in x_is_null.
    discriminate x_is_null.
Qed.
Hint Resolve HTNullFieldGetRuleSoundness : core.

Lemma HTIfRuleSoundness : forall gamma v1 v2 e1 e2 p q s ex u CC,
  (JFISemanticallyImplies gamma s 
    (JFIHoare (JFIAnd p (JFIEq v1 v2)) e1 ex u q) CC) ->
  (JFISemanticallyImplies gamma s
    (JFIHoare (JFIAnd p (JFIImplies (JFIEq v1 v2) JFIFalse)) e2 ex u q) CC) ->
   JFISemanticallyImplies gamma s
    (JFIHoare p (JFIf v1 v2 e1 e2) ex u q) CC.
Proof.
  intros gamma v1 v2 e1 e2 p q s ex u CC.
  intros IH_if_eq IH_if_neq.
  intros env h gamma_match_env h_satisfies_s.

  destruct (EnsureValIsLoc v1) as (l1 & v1_is_l1).
  destruct (EnsureValIsLoc v2) as (l2 & v2_is_l2).
  rewrite v1_is_l1.
  rewrite v2_is_l2.
  intros confs hn res_ex res env_res.
  intros h_satisfies_p eval_if.

  destruct confs as [ | (h', st') confs]; [destruct eval_if as (H & H0); discriminate H0 | ].
  destruct (Classical_Prop.classic (l1 = l2)) as [l1_eq_l2 | l1_neq_l2].
  + apply IfEvaluationStepEq in eval_if as (h_eq_h' & eval_e1).
    rewrite <- h_eq_h' in eval_e1.
    ++ set (if_eq_then_eval_e1_satisfies_q := IH_if_eq env h gamma_match_env h_satisfies_s confs hn res_ex res);
       fold JFIHeapSatisfiesInEnv in if_eq_then_eval_e1_satisfies_q;
       fold JFIPartialEval in if_eq_then_eval_e1_satisfies_q.
       apply if_eq_then_eval_e1_satisfies_q.
       +++ simpl; split.
           - exact h_satisfies_p.
           - rewrite v1_is_l1, v2_is_l2.
             exact l1_eq_l2.
       +++ exact eval_e1.
    ++ exact l1_eq_l2.
  + apply IfEvaluationStepNeq in eval_if as (h_eq_h' & eval_e2).
    rewrite <- h_eq_h' in eval_e2.
    ++ set (if_neq_then_eval_e2_satisfies_q := IH_if_neq env h gamma_match_env h_satisfies_s confs hn res_ex res);
       fold JFIHeapSatisfiesInEnv in if_neq_then_eval_e2_satisfies_q;
       fold JFIPartialEval in if_neq_then_eval_e2_satisfies_q.
       apply if_neq_then_eval_e2_satisfies_q.
       +++ simpl; split.
           - exact h_satisfies_p.
           - rewrite v1_is_l1, v2_is_l2.
             apply or_introl.
             exact l1_neq_l2.
       +++ exact eval_e2.
    ++ exact l1_neq_l2.
Qed.

Lemma HTNullInvokeSoundness : forall gamma s x mn vs v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFnull) (JFInvoke x mn vs)
     NPE_mode v (JFIEq (JFSyn (JFVar v)) NPE_val)) CC.
Proof.
  intros gamma s x mn vs v CC.
  intros env h gamma_match_env h_satisfies_s.
  intros confs hn res_ex res newEnv x_is_null eval.
  unfold newEnv.
  simpl in x_is_null.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval, JFIExprSubstituteEnv in eval.
  destruct confs; try discriminate (proj2 eval).
  fold JFIPartialEval in *.
  destruct p in eval.
  destruct eval as (h_eq & st_eq & assign_red).
  destruct x as [ | x]; try destruct x.
  + unfold JFIValToLoc in x_is_null.
    rewrite x_is_null in *.
    rewrite ValEnvSubstitutionPreservesVLoc in assign_red.
    unfold red in assign_red.
    apply NPEEval with (v := v) (env := env) in assign_red.
    exact assign_red.
  + unfold JFIValToLoc in x_is_null.
    rewrite ValEnvSubstitutionReplacesVarInEnv with (l := null) in assign_red.
    ++ unfold red in assign_red.
       apply NPEEval with (v := v) (env := env) in assign_red.
       exact assign_red.
    ++ destruct (StrMap.find (elt:=Loc) x env); try destruct x_is_null.
       trivial.
  + unfold JFIValToLoc in x_is_null.
    discriminate x_is_null.
Qed.
Hint Resolve HTNullInvokeSoundness : core.

Lemma HTThrowSoundness : forall decls gamma x cn s v CC,
  JFIRefType decls gamma x = Some cn ->
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIImplies (JFIEq (JFSyn x) JFnull) JFIFalse) (JFThrow (JFSyn x)) 
     (Some cn) v (JFIEq (JFSyn (JFVar v)) (JFSyn x))) CC.
Proof.
  intros decls gamma x cn s v CC.
  intros type_of_x.
  intros env h gamma_match_env h_satifsies_s.
  intros confs hn res_ex res newEnv x_not_null eval.
  simpl in x_not_null.
  destruct x_not_null as [x_not_null | x_null]; try destruct x_null.
  unfold newEnv.
  unfold JFIRefType in type_of_x.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval in eval.
  destruct confs; try discriminate (proj2 eval).
  fold JFIPartialEval in eval.
  destruct p.
  destruct eval as (h_eq & st_eq & throw_red).
  unfold JFIExprSubstituteEnv in throw_red.
  destruct x.
  + destruct (Classical_Prop.classic (exists l, StrMap.find x env = Some l)).
    ++ destruct H as (l & x_is_l).
       rewrite x_is_l in x_not_null.
       rewrite ValEnvSubstitutionReplacesVarInEnv with (l := l) in throw_red; try assumption.
       unfold red in throw_red.
       destruct l; try destruct (x_not_null (eq_refl null)).
       unfold class in throw_red.
       rewrite <- StrMapFacts.find_mapsto_iff in type_of_x, x_is_l.
       assert (type_of_n := (proj2 (gamma_match_env x)) (JFLoc n) cn type_of_x x_is_l).
       unfold JFILocOfType in type_of_n.
       destruct (NatMap.find (elt:=Obj) n h); try destruct throw_red.
       destruct o.
       rewrite <- type_of_n in throw_red.
       apply ValEval in throw_red as (ex_is_cn & res_x).
       split; try (symmetry; assumption).
       simpl.
       rewrite StrMapFacts.add_eq_o; trivial.
       destruct (Classical_Prop.classic (x = v)).
       +++ rewrite StrMapFacts.add_eq_o; trivial; symmetry; trivial.
       +++ rewrite StrMapFacts.add_neq_o; try (intros v_eq_x; symmetry in v_eq_x; destruct (H v_eq_x)).
           rewrite StrMapFacts.find_mapsto_iff in x_is_l.
           rewrite x_is_l.
           injection res_x as res_x.
           symmetry.
           exact res_x.
    ++ admit. (* TODO x in env *)
  + admit. (* TODO this *)
Admitted.
Hint Resolve HTThrowSoundness : core.

Lemma HTNullThrowSoundness : forall gamma x s v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq (JFSyn x) JFnull) (JFThrow (JFSyn x))
     NPE_mode v (JFIEq (JFSyn (JFVar v)) NPE_val)) CC.
Proof.
  intros gamma x s v CC.
  intros env h gamma_match_env h_satifsies_s.
  intros confs hn res_ex res newEnv x_is_null eval.
  unfold JFIEvalInEnv, JFIEval, JFIPartialEval, JFIExprSubstituteEnv in eval.
  destruct confs; try discriminate (proj2 eval).
  fold JFIPartialEval in *.
  destruct p in eval.
  destruct eval as (h_eq & st_eq & assign_red).
  destruct x.
  + unfold JFIValToLoc in x_is_null.
    rewrite ValEnvSubstitutionReplacesVarInEnv with (l := null) in assign_red.
    ++ unfold red in assign_red.
       apply NPEEval with (v := v) (env := env) in assign_red.
       exact assign_red.
    ++ simpl in x_is_null.
       destruct (StrMap.find (elt:=Loc) x env); try destruct x_is_null.
       trivial.
  + unfold JFIValToLoc in x_is_null.
    discriminate x_is_null.
Qed.
Hint Resolve HTNullThrowSoundness : core.

Lemma HTCatchNormalSoundness : forall gamma s p e1 mu ex x e2 u q CC,
  JFISemanticallyImplies gamma s (JFIHoare p e1 None u q) CC ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFTry e1 mu ex x e2) None u q) CC.
Proof.
  intros gamma s p e1 mu ex x e2 u q CC.
  intros hoare_p_q.
  intros env h gamma_match_env h_satisfies_s.
  intros confs hn res_ex res newEnv h_satisfies_p try_eval.
  destruct (TryEvaluation h e1 mu ex x e2 confs hn res_ex res env CC try_eval) as
    [  (res_ex_is_none & confs_e1 & e1_eval)
    | [(e1_ex & res_is_some & _ & confs_e1 & e1_eval)
    |  (e1_ex & _ & confs_e1 & confs_e2  & h' & e1_res & e1_eval & e2_eval)]
    ].
  + rewrite res_ex_is_none.
    split; trivial.
    assert (h_satisfies_hoare := hoare_p_q env h gamma_match_env h_satisfies_s).
    apply (h_satisfies_hoare confs_e1 hn None res h_satisfies_p e1_eval).
  + exfalso.
    assert (some_is_none := hoare_p_q env h gamma_match_env h_satisfies_s confs_e1 hn (Some e1_ex) res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in some_is_none.
    discriminate (proj1 some_is_none).
  + exfalso.
    assert (some_is_none := hoare_p_q env h gamma_match_env h_satisfies_s confs_e1 h' (Some e1_ex) e1_res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in some_is_none.
    discriminate (proj1 some_is_none).
Qed.
Hint Resolve HTCatchNormalSoundness : core.

Lemma HTCatchExSoundness : forall decls gamma s p e1 mu ex ex' ex'' x e2 u v r q,
  let CC := (JFIDeclsProg decls) in
  JFITermPersistent s ->
  JFIVarFreshInTerm v r ->
  Is_true (subtype_bool (JFIDeclsProg decls) (JFClass ex') (JFClass ex)) ->
  JFISemanticallyImplies gamma s (JFIHoare p e1 (Some ex') x q) CC ->
  JFISemanticallyImplies gamma s
    (JFIForall ex' v 
      (JFIHoare (JFITermSubstituteVar x v q) (JFIExprSubstituteVar x v e2) ex'' u r)) CC ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFTry e1 mu ex x e2) ex'' u r) CC.
Proof.
  intros decls gamma s p e1 mu ex ex' ex'' x e2 u v r q CC.
  intros s_persistent v_fresh_in_r is_subtype hoare_e1 hoare_e2.
  intros env h gamma_match_env h_satisfies_s.
  intros confs hn res_ex res newEnv h_satisfies_p try_eval.
  destruct (TryEvaluation h e1 mu ex x e2 confs hn res_ex res env CC try_eval) as
    [  (res_ex_is_none & confs_e1 & e1_eval)
    | [(e1_ex & res_is_some & not_subtype & confs_e1 & e1_eval)
    |  (e1_ex & _ & confs_e1 & confs_e2  & h' & e1_res & e1_eval & e2_eval)]
    ].
  + exfalso.
    assert (some_is_none := hoare_e1 env h gamma_match_env h_satisfies_s confs_e1 hn None res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in some_is_none.
    discriminate (proj1 some_is_none).
  + exfalso.
    unfold CC in is_subtype.
    assert (hoare_p_q_res := hoare_e1 env h gamma_match_env h_satisfies_s confs_e1 hn (Some e1_ex) res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in hoare_p_q_res.
    destruct hoare_p_q_res as (some_ex_eq & hn_satisfies_q).
    injection some_ex_eq as ex_eq.
    rewrite ex_eq in *.
    exact (not_subtype is_subtype).
  + assert (hoare_p_q_res := hoare_e1 env h gamma_match_env h_satisfies_s confs_e1 h' (Some e1_ex) e1_res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in hoare_p_q_res.
    destruct hoare_p_q_res as (ex_eq & h'_satisfies_q).
    unfold newEnv.
    apply LetRuleE2Soundness with (h' := h') (x := x) (e1_res := e1_res) (e2 := e2)
      (confs_e2 := confs_e2) (class := ex') (ex := ex'') (v := v) (q := q).
    ++ admit. (* e1_res type *)
    ++ assumption.
    ++ assumption.
    ++ apply LetRuleE1Soundness.
       apply (hoare_e1 env h gamma_match_env h_satisfies_s confs_e1 h' (Some e1_ex) e1_res); assumption.
    ++ apply hoare_e2.
       +++ apply EvaluationPreservesGammaMatching with (h := h) (e := (JFIExprSubstituteEnv env e1))
             (confs := confs_e1) (ex := (Some e1_ex)) (res := e1_res) (CC := CC); assumption.
       +++ apply EvaluationPreservesPersistentTerms with (h := h) (e := (JFIExprSubstituteEnv env e1))
             (confs := confs_e1) (ex := (Some e1_ex)) (res := e1_res); assumption.
Admitted.
Hint Resolve HTCatchExSoundness : core.

Lemma HTCatchPassExSoundness : forall decls gamma s p e1 mu ex ex' x e2 u q,
   let CC := (JFIDeclsProg decls) in
  ~Is_true (subtype_bool (JFIDeclsProg decls) (JFClass ex') (JFClass ex)) ->
   JFISemanticallyImplies gamma s (JFIHoare p e1 (Some ex') u q) CC ->
   JFISemanticallyImplies gamma s (JFIHoare p (JFTry e1 mu ex x e2) (Some ex') u q) CC.
Proof.
  intros decls gamma s p e1 mu ex ex' x e2 u q CC.
  intros not_subtype hoare_p_q.
  intros env h gamma_match_env h_satisfies_s.
  intros confs hn res_ex res newEnv h_satisfies_p try_eval.
  destruct (TryEvaluation h e1 mu ex x e2 confs hn res_ex res env CC try_eval) as
    [  (res_ex_is_none & confs_e1 & e1_eval)
    | [(e1_ex & res_is_some & _ & confs_e1 & e1_eval)
    |  (e1_ex & is_subtype & confs_e1 & confs_e2  & h' & e1_res & e1_eval & e2_eval)]
    ].
  + exfalso.
    assert (some_is_none := hoare_p_q env h gamma_match_env h_satisfies_s confs_e1 hn None res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in some_is_none.
    discriminate (proj1 some_is_none).
  + assert (hoare_p_q_res := hoare_p_q env h gamma_match_env h_satisfies_s confs_e1 hn (Some e1_ex) res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in hoare_p_q_res.
    destruct hoare_p_q_res as (ex_eq & hn_satisfies_q).
    rewrite res_is_some, ex_eq.
    split; trivial.
  + exfalso.
    unfold CC in is_subtype.
    assert (hoare_p_q_res := hoare_p_q env h gamma_match_env h_satisfies_s confs_e1 h' (Some e1_ex) e1_res h_satisfies_p e1_eval).
    fold JFIHeapSatisfiesInEnv in hoare_p_q_res.
    destruct hoare_p_q_res as (some_ex_eq & hn_satisfies_q).
    injection some_ex_eq as ex_eq.
    rewrite ex_eq in *.
    exact (not_subtype is_subtype).
Qed.
Hint Resolve HTCatchPassExSoundness : core.

(* =============== Main theorem =============== *)

Theorem JFISoundness : forall gamma decls p t,
  let CC := JFIDeclsProg decls in
  (JFIProves decls gamma p t) ->
   JFISemanticallyImplies gamma p t CC.
Proof.
  intros gamma decls p t CC.
  unfold CC in *.
  intros jfi_proof.
  induction jfi_proof as
  [
  (* JFIAsmRule *)
    decls gamma p
  (* JFITransRule *)
  | q decls gamma p r _ IH_p_proves_q _ IH_q_proves_r
  (* JFIEqReflRule *)
  | decls gamma p v
  (* JFIEqSymRule *)
  | decls gamma v1 v2 p _ IH_p_proves_v1_eq_v2
  (* JFIFalseElimRule *)
  | decls gamma p q _ IH_p_proves_false
  (* JFITrueIntroRule *)
  |  decls gamma p
  (* JFIAndIntroRule *)
  |  decls gamma p q r _ IH_r_proves_p _ IH_r_proves_q
  (* JFIAndElimLRule *)
  |  q decls gamma p r _ IH_r_proves_p_and_q
  (* JFIAndElimRRule *)
  |  p decls gamma q r _ IH_r_proves_p_and_q
  (* JFIOrIntroLRule *)
  |  decls gamma p q r _ IH_r_proves_p
  (* JFIOrIntroRRule *)
  |  decls gamma p q r _ IH_r_proves_q
  (* JFIOrElimRule *)
  |  decls gamma p q r s _ IH_s_proves_p_or_q _ IH_s_and_p_proves_r _ IH_s_and_q_proves_r
  (* JFIImpliesIntroRule *)
  |  decls gamma p q r _ IH_r_and_p_proves_q
  (* JFIImpliesElimRule *)
  |  p decls gamma q r _ IH_r_proves_p_implies_r _ IH_r_proves_p
  (* JFIForallIntroRule *)
  |  decls gamma gamma_x p q x type x_fresh_in_q gamma_add_new_x _ IH_q_with_x_proves_p
  (* JFIForallElimRule *)
  |  r decls gamma p q x v type
  (* JFIExistsIntroRule *)
  |  decls gamma p q x v type
  (* JFIExistsElimRule *)
  |  decls gamma p q r x type
  (* JFISepAssoc1Rule *)
  |  decls gamma p1 p2 p3
  (* JFISepAssoc2Rule *)
  |  decls gamma p1 p2 p3
  (* JFISepCommRule *)
  |  decls gamma p1 p2
  (* JFISepIntroRule *)
  |  decls gamma p1 p2 q1 q2
  (* JFISepIntroPersistentRule *)
  |  decls gamma p q
  (* JFIWandIntroRule *)
  |  decls gamma p q r
  (* JFIWandElimRule *)
  |  decls gamma p q r1 r2
  (* JFIHTFrameRule *)
  |  decls gamma p q r s e ex v
  (* JFIHTRetRule *)
  |  decls gamma s v w
  (* JFIHTCsqRule *)
  |  p' q' cn u decls gamma s p q ex v e s_persistent _ IH_p_implies_p' _ IH_HT_p'evq' _ IH_q'_implies_q
  (* JFIHTDisjIntroRule *)
  |  decls gamma s p q r e ex v
  (* JFIHTDisjElimLRule *)
  |  decls gamma s p q r e ex v
  (* JFIHTDisjElimRRule *)
  |  decls gamma s p q r e ex v
  (* JFIHTEqRule *)
  |  decls gamma s v1 v2 p e ex v q
  (* JFIHTEqRule *)
  |  decls gamma s v1 v2 p e ex v q
  (* JFIHTNewNotNullRule *)
  |  decls gamma s p mu cn vs v
  (* JFIHTNewFieldRule *)
  |  decls gamma s p mu cn vs v objflds n field value objflds_is_flds field_n value_n
  (* JFIHTLetRule *)
  |  v q decls gamma p r s e1 e2 x ex u class s_persistent v_fresh_in_r _ IH_e1 _ IH_e2
  (* JFIHTLetExRule *)
  | q decls gamma p s e1 e2 x ex u class
  (* JFIHTFieldSetRule *)
  |  decls gamma s x field v loc
  (* JFIHTNullFieldSetRule *)
  |  decls gamma s x field v loc
  (* JFIHTNullFieldGetRule *)
  |  decls gamma s x field v
  (* JFIHTIfRule *)
  |  decls gamma p v1 v2 e1 e2 ex u q s _ IH_if_eq _ IH_if_neq
  (* JFIHTInvokeRetRule *)
  |  cn method rettypeCN p' w q' x decls gamma s p q u v vs mn
  (* JFIHTInvokeNoRetRule *)
  |  cn method p' w q' decls gamma s p q u v vs mn
  (* JFIHTNullInvokeRule *)
  |  decls gamma s x mn vs v
  (* JFIHTThrowRule *)
  |  decls gamma s cn x v
  (* JFIHTNullThrowRule *)
  |  decls gamma s x v
  (* JFIHTCatchNormalRule *)
  | decls gamma s p e1 mu x e2 u q ex
  (* JFIHTCatchExRule *)
  | decls gamma s p r e1 mu x v e2 u q ex ex' ex''
  (* JFIHTCatchPassExRule *)
  | decls gamma s p e1 mu x e2 u q ex ex'
  ].
  (* JFIAsmRule *)
  + apply AsmRuleSoundness.
  (* JFITransRule *)
  + apply (TransRuleSoundness gamma p q r).
    ++ exact IH_p_proves_q.
    ++ exact IH_q_proves_r.
  (* JFIEqReflRule*)
  + apply EqReflRuleSoundness.
  (* JFIEqSymRule *)
  + apply EqSymRuleSoundness.
    exact IH_p_proves_v1_eq_v2.
  (* JFIFalseElimRule *)
  + apply FalseElimRuleSoundness.
    exact IH_p_proves_false.
  (* JFITrueIntroRule *)
  + apply TrueIntroRuleSoundness.
  (* JFIAndIntroRule *)
  + apply AndIntroRuleSoundness.
    ++ exact IH_r_proves_p.
    ++ exact IH_r_proves_q.
  (* JFIAndElimLRule *)
  + apply AndElimRuleSoundness with (q := q).
    ++ exact IH_r_proves_p_and_q.
  (* JFIAndElimRRule *)
  + apply AndElimRuleSoundness with (p := p).
    ++ exact IH_r_proves_p_and_q.
  (* JFIOrIntroLRule *)
  + apply OrIntroRuleSoundness.
    apply (or_introl IH_r_proves_p).
  (* JFIOrIntroRRule *)
  + apply OrIntroRuleSoundness.
    apply (or_intror IH_r_proves_q).
  (* JFIOrElimRule *)
  + apply OrElimRuleSoundness with (gamma := gamma) (p := p) (q := q).
    ++ exact IH_s_proves_p_or_q.
    ++ exact IH_s_and_p_proves_r.
    ++ exact IH_s_and_q_proves_r.
  (* JFIImpliesIntroRule *)
  + apply ImpliesIntroRuleSoundness.
    exact IH_r_and_p_proves_q.
  (* JFIImpliesElimRule *)
  + apply ImpliesElimRuleSoundness with (p := p).
    ++ exact IH_r_proves_p_implies_r.
    ++ exact IH_r_proves_p.
  (* JFIForallIntroRule *)
  + apply ForallIntroRuleSoundness with (gamma := gamma) (gamma_x := gamma_x).
    ++ exact x_fresh_in_q.
    ++ exact gamma_add_new_x.
    ++ exact IH_q_with_x_proves_p.
  (* JFIForallElimRule *)
  + eauto.
  (* JFIExistsIntroRule *)
  + eauto.
  (* JFIExistsElimRule *)
  + eauto.
  (* JFISepAssoc1Rule *)
  + eauto.
  (* JFISepAssoc2Rule *)
  + eauto.
  (* JFISepCommRule *)
  + eauto.
  (* JFISepIntroRule *)
  + eauto.
  (* JFISepIntroPersistentRule *)
  + eauto.
  (* JFIWandIntroRule *)
  + eauto.
  (* JFIWandElimRule *)
  + eauto.
  (* JFIHTFrameRule *)
  + admit. (* TODO *)
  (* JFIHTRetRule *)
  + apply HTRetRuleSoundness.
  (* JFIHTCsqRule: *)
  + eauto.
  (* JFIHTDisjIntroRule *)
  + eauto.
  (* JFIHTDisjElimLRule *)
  + eauto.
  (* JFIHTDisjElimRRule *)
  + eauto.
  (* JFIHTEqRule1 *)
  + eauto.
  (* JFIHTEqRule2 *)
  + eauto.
  (* JFIHTNewNotNullRule *)
  + eauto.
  (* JFIHTNewFieldRule *)
  + apply HTNewFieldRuleSoundness with (decls := decls) (objflds := objflds) (n := n); assumption.
  (* JFIHTLetRule *)
  + eauto.
  (* JFIHTLetExRule *)
  + eauto.
  (* JFIHTFieldSetRule *)
  + eauto.
  (* JFINullHTFieldSetRule *)
  + eauto.
  (* JFIHTNullFieldGetRule *)
  + eauto.
  (* JFIHTIfRule *)
  + apply HTIfRuleSoundness.
    ++ exact IH_if_eq.
    ++ exact IH_if_neq.
  (* JFIHTInvokeRetRule *)
  + admit. (* TODO *)
  (* JFIHTInvokeNoRetRule *)
  + admit. (* TODO *)
  (* JFIHTNullInvokeRule *)
  + eauto.
  (* JFIHTThrowRule *)
  + eauto.
  (* JFIHTNullThrowRule *)
  + eauto.
  (* JFIHTCatchNormalRule *)
  + eauto.
  (* JFIHTCatchExRule *)
  + eauto.
  (* JFIHTCatchPassExRule *)
  + eauto.
Admitted.

