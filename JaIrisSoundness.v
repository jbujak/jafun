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
Require Import Bool.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.


Module HeapFacts := Facts Heap.
Module StrMapFacts := Facts StrMap.
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
  intros var_name var_loc var_type.
  intros (same_vars & find_in_gamma_is_some) find_in_env_is_some.
  destruct (Classical_Prop.classic (var_name = x)) as [ var_name_eq_x | var_name_ne_x ].
  + replace (StrMap.find (elt:=Loc) var_name (StrMap.add x l env))
     with (Some l) in find_in_env_is_some.
    replace (StrMap.find (elt:=JFClassName) var_name (StrMap.add x type gamma))
     with (Some type) in find_in_gamma_is_some.
    ++ replace var_loc with l.
       replace var_type with type.
       +++ exact loc_of_type.
       +++ injection find_in_gamma_is_some. trivial.
       +++ injection find_in_env_is_some. trivial.
    ++ symmetry. apply StrMapFacts.add_eq_o.
       symmetry. exact var_name_eq_x.
    ++ symmetry. apply StrMapFacts.add_eq_o.
       symmetry. exact var_name_eq_x.
  + replace (StrMap.find (elt:=Loc) var_name (StrMap.add x l env))
     with (StrMap.find (elt:=Loc) var_name env) in find_in_env_is_some.
    replace (StrMap.find (elt:=JFClassName) var_name (StrMap.add x type gamma))
     with (StrMap.find (elt:=JFClassName) var_name gamma) in find_in_gamma_is_some.
    ++ unfold JFIGammaMatchEnv in gamma_match_env.
       apply (gamma_match_env var_name var_loc var_type).
       split. split.
       +++ intros var_name_in_gamma.
           apply StrMap_in_find_iff.
           exists var_loc.
           exact find_in_env_is_some.
       +++ intros var_name_in_env.
           apply StrMap_in_find_iff.
           exists var_type.
           exact find_in_gamma_is_some.
       +++ exact find_in_gamma_is_some.
       +++ exact find_in_env_is_some.
     ++ symmetry. apply StrMapFacts.add_neq_o.
        unfold not.
        intros x_eq_var_name.
        symmetry in x_eq_var_name.
        exact (var_name_ne_x x_eq_var_name).
     ++ symmetry. apply StrMapFacts.add_neq_o.
        unfold not.
        intros x_eq_var_name.
        symmetry in x_eq_var_name.
        exact (var_name_ne_x x_eq_var_name).
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
  unfold EnvEq.
  intros y.
  destruct (Classical_Prop.classic (x = y)) as [x_eq_y | x_neq_y].
  + rewrite x_eq_y.
    replace (StrMap.find y (StrMap.add y l env1)) with (Some l); symmetry.
    ++ apply StrMapFacts.add_eq_o.
       trivial.
    ++ apply StrMapFacts.add_eq_o.
       trivial.
  + replace (StrMap.find y (StrMap.add x l env1)) with (StrMap.find y env1).
    replace (StrMap.find y (StrMap.add x l env2)) with (StrMap.find y env2).
    ++ apply env1_eq_env2.
    ++ symmetry.
       apply StrMapFacts.add_neq_o.
       exact x_neq_y.
    ++ symmetry.
       apply StrMapFacts.add_neq_o.
       exact x_neq_y.
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
  intros (h1 & (h_h1 & (disjoint_union & (h1_satisfies_t1 & union_satisfies_t2)))).
  exists h1, h_h1.
  split; [ | split].
  + exact disjoint_union.
  + apply (t1_equivalence h1 env1 env2 env_eq).
    exact h1_satisfies_t1. 
  + apply (t2_equivalence h_h1 env1 env2 env_eq).
    exact union_satisfies_t2.
Qed.

Lemma EqualEnvsAreEquivalent : forall t CC h env1 env2,
  (EnvEq env1 env2) ->
    ((JFIHeapSatisfiesInEnv h t env1 CC) <-> (JFIHeapSatisfiesInEnv h t env2 CC)).
Proof.
  intros t CC.
  induction t as
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
    ]; intros h env1 env2 env1_eq_env2.
  (* JFITrue *)
  + split; simpl; trivial.
  (* JFIFalse *)
  + split; simpl; trivial.
  (* JFIAnd t1 t2 *)
  + split; apply EnvEqGivesAndImplication; try exact IH_t1; try exact IH_t2.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIOr t1 t2 *)
  + split; apply EnvEqGivesOrImplication; try exact IH_t1; try exact IH_t2.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIImplies t1 t2 *)
  + split; apply EnvEqGivesImpliesImplication; try exact IH_t1; try exact IH_t2.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIExists *)
  + split; apply EnvEqGivesExistsImplication; try exact IH_t.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIForall *)
  + split; apply EnvEqGivesForallImplication; try exact IH_t.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIHoare *)
  + admit.
  (* JFIEq *)
  + split; apply EnvEqGivesEqImplication.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIFieldEq *)
  + split; apply EnvEqGivesFieldEqImplication.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFISep*)
  + split; apply EnvEqGivesSepImplication; try exact IH_t1; try exact IH_t2.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIWand *)
  + split; apply EnvEqGivesWandImplication; try exact IH_t1; try exact IH_t2.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
Admitted.

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

Lemma AddingFreshVarPreservesHeapSatisfiying : forall h q x l CC env,
  (JFIVarFreshInTerm x q) ->
    ((JFIHeapSatisfiesInEnv h q env CC) <->
      JFIHeapSatisfiesInEnv h q (StrMap.add x l env) CC).
Proof.
  intros h q x l CC.
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
    ].
  (* JFITrue *)
  + simpl.
    split; trivial.
  (* JFIFalse *)
  + simpl.
    split; trivial.
  (* JFIAnd t1 t2 *)
  + simpl.
    intros env x_fresh.
    split; intros h_satisfies_q; split;
    destruct x_fresh as (t1_fresh & t2_fresh);
    try apply (IH_t1 env t1_fresh);
    try apply (IH_t2 env t2_fresh);
    try apply h_satisfies_q.
  (* JFIOr t1 t2 *)
  + simpl.
    intros env x_fresh.
    destruct x_fresh as (t1_fresh & t2_fresh).
    split; intros [ h_satisfies_t1 | h_satisfies_t2 ].
    ++ apply or_introl.
       apply (IH_t1 env t1_fresh); exact h_satisfies_t1.
    ++ apply or_intror.
       apply (IH_t2 env t2_fresh); exact h_satisfies_t2.
    ++ apply or_introl.
       apply (IH_t1 env t1_fresh); exact h_satisfies_t1.
    ++ apply or_intror.
       apply (IH_t2 env t2_fresh); exact h_satisfies_t2.
  (* JFIImplies t1 t2 *)
  + simpl.
    intros env x_fresh.
    destruct x_fresh as (t1_fresh & t2_fresh);
    split; intros [ not_h_satisfies_t1 | h_satisfies_t2 ].
    ++ apply or_introl.
       unfold not.
       intros h_satisfies_t1.
       apply (IH_t1 env t1_fresh) in h_satisfies_t1.
       exact (not_h_satisfies_t1 h_satisfies_t1).
    ++ apply or_intror.
       apply (IH_t2 env t2_fresh); exact h_satisfies_t2.
    ++ apply or_introl.
       unfold not.
       intros h_satisfies_t1.
       apply (IH_t1 env t1_fresh) in h_satisfies_t1.
       exact (not_h_satisfies_t1 h_satisfies_t1).
    ++ apply or_intror.
       apply (IH_t2 env t2_fresh); exact h_satisfies_t2.
  (* JFIExists *)
  + admit.
  (* JFIForall *)
  + intros env x_fresh.
    split.
    ++ simpl.
       intros h_satisfies_t loc loc_of_type.
       apply EnvOrderChangePreservesHeapSatisfiying.
       +++ apply neq_symmetry.
           apply FreshVarDifferentFromForallVar with (class := name) (t := t).
           exact x_fresh.
       +++ apply (IH_t (StrMap.add name loc env)).
           - simpl in x_fresh.
             destruct (String.eqb name x).
             -- destruct x_fresh.
             -- exact x_fresh.
           - exact (h_satisfies_t loc loc_of_type).
    ++ simpl.
       intros h_satisfies_t loc loc_of_type.
       set (h_satisfies_t' := h_satisfies_t loc loc_of_type).
       apply EnvOrderChangePreservesHeapSatisfiying in h_satisfies_t'.
       +++ apply (IH_t (StrMap.add name loc env)) in h_satisfies_t'.
           - exact h_satisfies_t'.
           - simpl in x_fresh.
             destruct (String.eqb name x).
             -- destruct x_fresh.
             -- exact x_fresh.
       +++ apply FreshVarDifferentFromForallVar with (class := name) (t := t).
           exact x_fresh.
  (* JFIHoare *)
  + admit.
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
  + admit.
  (* JFIWand *)
  + admit.
Admitted.

Lemma VarNameChangePreservesHeapSatisfiying : forall h t u v l env CC,
  (JFIHeapSatisfiesInEnv h t (StrMap.add v l env) CC) <->
   JFIHeapSatisfiesInEnv h (JFITermSubstituteVar v u t) (StrMap.add u l env) CC.
Proof.
Admitted.

(* =============== Substitution Lemmas =============== *)

Definition JFISubstitutionImplies x v1 v2 t h env CC :=
    JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v1 t) env CC ->
    JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v2 t) env CC.

Definition JFISubstitutionsEquivalent x v1 v2 t h env CC :=
  JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v1 t) env CC <->
  JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v2 t) env CC.

Lemma JFISubstitutionEquivalenceSymmetry : forall x v1 v2 t h env CC,
  (JFISubstitutionsEquivalent x v1 v2 t h env CC) ->
   JFISubstitutionsEquivalent x v2 v1 t h env CC.
Proof.
  intros x v1 v2 t h env CC.
  unfold JFISubstitutionsEquivalent.
  intros equivalence.
  symmetry.
  exact equivalence.
Qed.

Lemma JFISubstitutionsEquivalenceGivesAndImplication : forall v1 v2 x t1 t2 h env CC,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env CC) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env CC) ->
   JFISubstitutionImplies x v1 v2 (JFIAnd t1 t2) h env CC.
Proof.
  intros v1 v2 x t1 t2 h env CC.
  intros IH_t1 IH_t2.
  simpl.
  intros ( h_satisfies_subst_in_t1 & h_satisfies_subst_in_t2 ).
  split.
  + apply IH_t1.
    exact h_satisfies_subst_in_t1.
  + apply IH_t2.
    exact h_satisfies_subst_in_t2.
Qed.

Lemma JFISubstitutionsEquivalenceGivesOrImplication : forall v1 v2 x t1 t2 h env CC,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env CC) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env CC) ->
   JFISubstitutionImplies x v1 v2 (JFIOr t1 t2) h env CC.
Proof.
  intros v1 v2 x t1 t2 h env CC.
  intros IH_t1 IH_t2.
  intros [ h_satisfies_subst_in_t1 | h_satisfies_subst_in_t2 ]; simpl.
  + apply or_introl.
    apply IH_t1.
    exact h_satisfies_subst_in_t1.
  + apply or_intror.
    apply IH_t2.
    exact h_satisfies_subst_in_t2.
Qed.

Lemma JFISubstitutionsEquivalenceGivesImpliesImplication : forall v1 v2 x t1 t2 h env CC,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env CC) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env CC) ->
   JFISubstitutionImplies x v1 v2 (JFIImplies t1 t2) h env CC.
Proof.
  intros v1 v2 x t1 t2 h env CC.
  intros t1_equivalence t2_equivalence.
  intros h_satisfies_subst_in_implies; simpl; destruct h_satisfies_subst_in_implies as
      [ not_h_satisfies_subst_v1_in_t1 | h_satisfies_subst_v1_in_t2].
  + apply or_introl.
    unfold not.
    intros h_satisfies_subst_v2_in_t1.
    apply not_h_satisfies_subst_v1_in_t1.
    apply t1_equivalence.
    exact h_satisfies_subst_v2_in_t1.
  + apply or_intror.
    apply t2_equivalence.
    exact h_satisfies_subst_v1_in_t2.
Qed.

Lemma SubheapPreservesEquivalence : forall h1 x v1 v2 t h env CC,
  (JFISubstitutionsEquivalent x v1 v2 t h env CC) ->
  (JFISubheap h1 h) ->
   JFISubstitutionsEquivalent x v1 v2 t h1 env CC.
Proof.
  intros h1 x v1 v2 t h env CC.
  intros h_equivalence.
  intros h1_subheap.
  induction t as
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
    ].
  (* JFITrue *)
  + unfoldSubstitutions.
    split; trivial.
  (* JFIFalse *)
  + split; intros h_satisfies_false; elim h_satisfies_false.
  (* JFIAnd t1 t2 *)
  + split.
    ++ intros h1_satisfies_subst_v1_in_and.
        admit.
Admitted.

Lemma JFISubstitutionsEquivalenceGivesSepImplication : forall v1 v2 x t1 t2 h env CC,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env CC) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env CC) ->
   JFISubstitutionImplies x v1 v2 (JFISep t1 t2) h env CC.
Proof.
  intros v1 v2 x t1 t2 h env CC.
  intros t1_equivalence t2_equivalence.
  intros h_satisfies_subst_in_sep; simpl.
  destruct h_satisfies_subst_in_sep as
    ( h1 & h2 & (h_is_union &  disjoint_h1_h2) & (h1_satisfies_subst_v1_in_t1 & h2_satisfies_subst_v1_in_t2) ).
  exists h1.
  exists h2.
  split; split.
  + exact h_is_union.
  + exact disjoint_h1_h2.
  + apply (SubheapPreservesEquivalence h1) in t1_equivalence.
    ++ apply t1_equivalence.
       exact h1_satisfies_subst_v1_in_t1.
    ++ apply (SubheapOfUnion h1 h2 h).
       exact h_is_union.
  + apply (SubheapPreservesEquivalence h2) in t2_equivalence.
    ++ apply t2_equivalence.
       exact h2_satisfies_subst_v1_in_t2.
    ++ apply (SubheapOfUnion h2 h1 h).
       apply HeapsUnionSymmetry.
       exact h_is_union.
Qed.

Lemma ValEnvSubstitutionPreservesVLoc : forall env loc,
  JFIValSubstituteEnv env (JFVLoc loc) = JFVLoc loc.
Proof.
  intros env loc.
  unfold JFIValSubstituteEnv.
  rewrite StrMap.fold_1.
  induction (StrMap.elements (elt:=Loc) env); auto.
Qed.

Lemma ExprEnvSubstitutionPreservesVLoc : forall env loc,
  JFIExprSubstituteEnv env (JFVal1 (JFVLoc loc)) = JFVal1 (JFVLoc loc).
Proof.
  intros env loc.
  unfold JFIExprSubstituteEnv.
  rewrite ValEnvSubstitutionPreservesVLoc.
  trivial.
Qed.

Lemma ValSubstituteIdentity : forall x v,
  JFIValSubstituteVal x (JFSyn (JFVar x)) v = v.
Proof.
  intros x v.
  unfold JFIValSubstituteVal.
  destruct v; try trivial.
  destruct x0; try trivial.
  destruct (Classical_Prop.classic (x0 = x)).
  + apply String.eqb_eq in H as H1.
    rewrite H1.
    rewrite H.
    trivial.
  + apply String.eqb_neq in H.
    rewrite H.
    trivial.
Qed.

Lemma ValMapSubstituteIdentity : forall x vs,
  map (JFIValSubstituteVal x (JFSyn (JFVar x))) vs = vs.
Proof.
  intros x vs.
  induction vs; try trivial.
  rewrite List.map_cons.
  rewrite IHvs.
  rewrite ValSubstituteIdentity.
  trivial.
Qed.

Lemma ExprSubstituteIdentity : forall x e,
  JFIExprSubstituteVal x (JFSyn (JFVar x)) e = e.
Proof.
  intros x e.
  unfold JFIExprSubstituteVal.
  induction e; fold JFIExprSubstituteVal in *.
  + rewrite ValMapSubstituteIdentity.
    trivial.
  + destruct (String.eqb x0 x);
    try rewrite IHe1;
    try rewrite IHe2;
    trivial.
  + rewrite IHe1; rewrite IHe2.
    rewrite ValSubstituteIdentity; rewrite ValSubstituteIdentity.
    trivial.
  + rewrite ValMapSubstituteIdentity.
    rewrite ValSubstituteIdentity.
    trivial.
  + destruct vx.
    rewrite ValSubstituteIdentity; rewrite ValSubstituteIdentity.
    trivial.
  + rewrite ValSubstituteIdentity; trivial.
  + destruct vx.
    rewrite ValSubstituteIdentity.
    trivial.
  + rewrite ValSubstituteIdentity; trivial.
  + rewrite IHe1; rewrite IHe2.
    destruct (String.eqb x0 x); trivial.
Qed.

Lemma TermSubstituteIdentity : forall x q,
  JFITermSubstituteVal x (JFSyn (JFVar x)) q = q.
Proof.
  intros x q.
  unfold JFITermSubstituteVal.
  induction q; fold JFITermSubstituteVal in *.
  + trivial.
  + trivial.
  + rewrite IHq1; rewrite IHq2; trivial.
  + rewrite IHq1; rewrite IHq2; trivial.
  + rewrite IHq1; rewrite IHq2; trivial.
  + destruct (String.eqb name x); try trivial.
    rewrite IHq; trivial.
  + destruct (String.eqb name x); try trivial.
    rewrite IHq; trivial.
  + rewrite IHq1; rewrite IHq2; rewrite ExprSubstituteIdentity; trivial.
  + rewrite ValSubstituteIdentity; rewrite ValSubstituteIdentity; trivial.
  + rewrite ValSubstituteIdentity; rewrite ValSubstituteIdentity; trivial.
  + rewrite IHq1; rewrite IHq2; trivial.
  + rewrite IHq1; rewrite IHq2; trivial.
Qed.

Lemma StrMapKeyEqEquivalence : Equivalence (StrMap.eq_key_elt (elt:=Loc)).
Proof.
  unfold StrMap.eq_key_elt.
  unfold StrMap.Raw.Proofs.PX.eqke.

Admitted.

Lemma SubstituteEnvXNotInEnv : forall x env,
  ~StrMap.In x env ->
  JFIValSubstituteEnv env (JFSyn (JFVar x)) = (JFSyn (JFVar x)).
Proof.
  intros x env x_not_in_env.
  unfold JFIValSubstituteEnv.
  assert (x_not_in_elements : forall a, List.In a (StrMap.elements (elt:=Loc) env) -> x <> (fst a)).
  + intros (y, l) a_in_elements.
    intros x_is_y.
    simpl in x_is_y.
    rewrite <- x_is_y in *.
    assert (exists_element : exists e, InA (StrMap.eq_key_elt (elt:=Loc)) (x, e) (StrMap.elements (elt:=Loc) env)).
    ++ exists l.
       apply In_InA; try assumption.
       exact StrMapKeyEqEquivalence.
    ++ set (elements_in_iff := StrMapFacts.elements_in_iff env x).
       destruct elements_in_iff as (_ & exists_elements_then_in_env).
       set (x_in_env := exists_elements_then_in_env exists_element).
       exact (x_not_in_env x_in_env).
  + rewrite StrMap.fold_1.
    induction (StrMap.elements (elt:=Loc) env).
    ++ auto.
    ++ simpl.
       replace (String.eqb x (fst a)) with false.
       +++ apply IHl.
           intros a0 a0_in_l.
           apply x_not_in_elements.
           apply List.in_cons.
           exact a0_in_l.
      +++ symmetry.
          apply String.eqb_neq.
          apply x_not_in_elements.
          apply List.in_eq.
Qed.

Lemma SubstituteEnvXInEnv : forall x env,
  StrMap.In x env ->
  exists l, StrMap.find x env = Some l /\
    JFIValSubstituteEnv env (JFSyn (JFVar x)) = JFVLoc l.
Proof.
Admitted.

(* =============== Equality Lemmas =============== *)

Lemma EqualValuesGiveEqualLocations : forall h v1 v2 env CC,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env CC) ->
  JFIValToLoc v1 env = JFIValToLoc v2 env.
Proof.
  intros h v1 v2 env CC.
  intros h_satisfies_eq.
  unfold JFIHeapSatisfiesInEnv in h_satisfies_eq.
  destruct (JFIValToLoc v1 env), (JFIValToLoc v2 env).
  + replace l0 with l.
    trivial.
  + destruct h_satisfies_eq.
  + destruct h_satisfies_eq.
  + trivial.
Qed.

Lemma EqualValuesGiveEqualLocationsAfterSubstitution : forall h x v1 v2 val env CC,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env CC) ->
  (JFIValToLoc (JFIValSubstituteVal x v1 val) env)
    = (JFIValToLoc (JFIValSubstituteVal x v2 val) env).
Proof.
  intros h x v1 v2 val env CC.
  intros v1_eq_v2.
  unfold JFIValSubstituteVal.
  unfold JFIHeapSatisfiesInEnv.
  destruct val.
  + trivial.
  + destruct x0.
    ++ destruct (String.eqb x0 x).
       +++ apply EqualValuesGiveEqualLocations with (h := h) (CC := CC).
           exact v1_eq_v2.
       +++ trivial.
    ++ trivial.
Qed.

Ltac replace_two_values x v1 v2 env value1 value2 :=
  replace (JFIValToLoc (JFIValSubstituteVal x v2 value1) env)
     with (JFIValToLoc (JFIValSubstituteVal x v1 value1) env);
 [replace (JFIValToLoc (JFIValSubstituteVal x v2 value2) env)
     with (JFIValToLoc (JFIValSubstituteVal x v1 value2) env) |].

Lemma EqualityGivesEqImplication : forall x v1 v2 val1 val2 h env CC,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env CC) ->
   JFISubstitutionImplies x v1 v2 (JFIEq val1 val2) h env CC.
Proof.
  intros x v1 v2 val1 val2 h env CC.
  intros h_satisfies_v1_eq_v2.
  intros h_satisfies_subst_v1_in_eq.
  unfold JFITermSubstituteVal.
  unfold JFIHeapSatisfiesInEnv.
  unfold JFITermSubstituteVal in h_satisfies_subst_v1_in_eq.
  unfold JFIHeapSatisfiesInEnv in h_satisfies_subst_v1_in_eq.
  destruct val1, val2.
  + unfold JFIValSubstituteVal.
    unfold JFIValSubstituteVal in h_satisfies_subst_v1_in_eq.
    exact h_satisfies_subst_v1_in_eq.
  + replace_two_values x v1 v2 env (JFVLoc l) (JFSyn x0).
    ++ exact h_satisfies_subst_v1_in_eq.
    ++ apply EqualValuesGiveEqualLocationsAfterSubstitution with (h := h) (CC := CC).
       exact h_satisfies_v1_eq_v2.
    ++ apply EqualValuesGiveEqualLocationsAfterSubstitution with (h := h) (CC := CC).
       exact h_satisfies_v1_eq_v2.
  + replace_two_values x v1 v2 env (JFSyn x0) (JFVLoc l).
    ++ exact h_satisfies_subst_v1_in_eq.
    ++ apply EqualValuesGiveEqualLocationsAfterSubstitution with (h := h) (CC := CC).
       exact h_satisfies_v1_eq_v2.
    ++ apply EqualValuesGiveEqualLocationsAfterSubstitution with (h := h) (CC := CC).
       exact h_satisfies_v1_eq_v2.
  + replace_two_values x v1 v2 env (JFSyn x0) (JFSyn x1).
    ++ exact h_satisfies_subst_v1_in_eq.
    ++ apply EqualValuesGiveEqualLocationsAfterSubstitution with (h := h) (CC := CC).
       exact h_satisfies_v1_eq_v2.
    ++ apply EqualValuesGiveEqualLocationsAfterSubstitution with (h := h) (CC := CC).
       exact h_satisfies_v1_eq_v2.
Qed.

Ltac binop_equivalence_from_operands_implication lhs_implication rhs_implication binop_implication :=
  split;
  [
    apply binop_implication; [apply lhs_implication | apply rhs_implication]
  | apply binop_implication; apply JFISubstitutionEquivalenceSymmetry; [apply lhs_implication | apply rhs_implication]
  ].

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

Lemma JFIEqualValuesAreEquivalent : forall v1 v2 h x q env CC,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env CC) ->
  JFISubstitutionsEquivalent x v1 v2 q h env CC.
Proof.
  intros v1 v2 h x q env CC.
  intros h_satisfies_v1_eq_v2.

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
    ].
  (* JFITrue *)
  + unfoldSubstitutions.
    split; trivial.
  (* JFIFalse *)
  + split; intros h_satisfies_false; elim h_satisfies_false.
  (* JFIAnd t1 t2 *)
  + binop_equivalence_from_operands_implication IH_t1 IH_t2 JFISubstitutionsEquivalenceGivesAndImplication.
  (* JFIOr t1 t2 *)
  + binop_equivalence_from_operands_implication IH_t1 IH_t2 JFISubstitutionsEquivalenceGivesOrImplication.
  (* JFIImplies t1 t2 *)
  + binop_equivalence_from_operands_implication IH_t1 IH_t2 JFISubstitutionsEquivalenceGivesImpliesImplication.
  (* JFIExists *)
  + admit.
  (* JFIForall *)
  + admit.
  (* JFIHoare *)
  + admit.
  (* JFIEq *)
  + split.
    ++ apply EqualityGivesEqImplication.
       exact h_satisfies_v1_eq_v2.
    ++ apply EqualityGivesEqImplication.
       apply EqSymmetry.
       exact h_satisfies_v1_eq_v2.
  (* JFIFieldEq *)
  + admit.
  (* JFISep*)
  + binop_equivalence_from_operands_implication IH_t1 IH_t2 JFISubstitutionsEquivalenceGivesSepImplication.
  (* JFIWand *)
  + admit.
Admitted.

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

Lemma EqRuleSoundness : forall gamma x v1 v2 p q r CC,
  (r = JFITermSubstituteVal x v2 q) ->
  (JFISemanticallyImplies gamma p (JFITermSubstituteVal x v1 q) CC) ->
  (JFISemanticallyImplies gamma p (JFIEq v1 v2) CC) ->
   JFISemanticallyImplies gamma p r CC.
Proof.
  intros gamma x v1 v2 p q r CC.
  intros r_is_subst_v2 p_implies_subst_v1 p_implies_eq.
  intros env h gamma_match_env h_satisfies_p.
  rewrite r_is_subst_v2.
  apply (JFIEqualValuesAreEquivalent v1 v2).
  + apply p_implies_eq.
    exact gamma_match_env.
    exact h_satisfies_p.
  + apply p_implies_subst_v1.
    exact gamma_match_env.
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
  + apply AddingFreshVarPreservesHeapSatisfiying.
    ++ exact x_fresh_in_q.
    ++ exact h_satisfies_q.
Qed.

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

Lemma CorrectEvaluationImpliesHoareTriple : forall h p e v q env CC,
  (exists confs hn res,
  (JFIHeapSatisfiesInEnv h p env CC) /\ (JFIEvalInEnv h e confs hn res env CC) /\ (JFIHeapSatisfiesInEnv hn q (StrMap.add v res env) CC)) ->
   JFIHeapSatisfiesInEnv h (JFIHoare p e v q) env CC.
Proof.
  intros h p e v q env CC.
  intros (confs & (hn & (res & (h_satisfies_p & (e_eval_hs & hn_satisfies_q))))).
  simpl.
  intros confs' hn' res'.
  intros _ e_eval_confs'.
  set (deterministic := EvaluationIsDeterministic confs confs' h (JFIExprSubstituteEnv env e) hn hn' res res' CC e_eval_hs e_eval_confs').
  destruct deterministic as (confs_eq_confs' & (hn_eq_hn' & res_eq_res')).
  symmetry in hn_eq_hn'.
  symmetry in res_eq_res'.
  rewrite hn_eq_hn'.
  rewrite res_eq_res'.
  exact hn_satisfies_q.
Qed.

Lemma HeapSatisfyingWithPreconditionImpliesHoareTriple : forall h p e v q env CC,
  ((JFIHeapSatisfiesInEnv h p env CC) -> JFIHeapSatisfiesInEnv h (JFIHoare p e v q) env CC) ->
    JFIHeapSatisfiesInEnv h (JFIHoare p e v q) env CC.
Proof.
  intros.
  destruct (Classical_Prop.classic (JFIHeapSatisfiesInEnv h p env CC)).
  + apply H.
    assumption.
  + simpl.
    intros.
    destruct (H0 H1).
Qed.

Lemma IfEvaluationStepEq : forall l1 l2 e1 e2 h h' st' confs hn res env CC,
  (l1 = l2) ->
  (JFIEvalInEnv h (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ((h', st')::confs) hn res env CC) ->
  (h = h' /\ JFIEvalInEnv h' e1 confs hn res env CC).
Proof.
  intros l1 l2 e1 e2 h h' st' confs hn res env CC.
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

Lemma IfEvaluationStepNeq : forall l1 l2 e1 e2 h h' st' confs hn res env CC,
  (l1 <> l2) ->
  (JFIEvalInEnv h (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ((h', st')::confs) hn res env CC) ->
  (h = h' /\ JFIEvalInEnv h' e2 confs hn res env CC).
Proof.
  intros l1 l2 e1 e2 h h' st' confs hn res env CC.
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
   JFIEvalInEnv h (JFNew mu cn vs) [(h, [ [] [[ JFIExprSubstituteEnv env (JFNew mu cn vs) ]]_ None])] newheap newloc env CC.
Proof.
Admitted.
Hint Resolve NewEvaluationStep : core.

Lemma EvaluationPreservesGammaMatching : forall gamma env h e confs hn res CC,
  (JFIGammaMatchEnv h gamma env) ->
  (JFIEval h e confs hn res CC) ->
  (JFIGammaMatchEnv hn gamma env).
Proof.
Admitted.

Lemma EvaluationPreservesPersistentTerms : forall env s h e confs hn res CC,
  (JFITermPersistent s) ->
  (JFIHeapSatisfiesInEnv h s env CC) ->
  (JFIEval h e confs hn res CC) ->
   JFIHeapSatisfiesInEnv hn s env CC.
Proof.
Admitted.

(* =============== Soundness of Hoare triple rules =============== *)

Lemma HTFalseRuleSoundness : forall gamma s e v q CC,
 JFISemanticallyImplies gamma s (JFIHoare JFIFalse e v q) CC.
Proof.
  intros gamma s e v q CC.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros confs hn loc false.
  destruct false.
Qed.

Lemma HTTrueRuleSoundness : forall gamma s p e v CC,
  JFISemanticallyImplies gamma s (JFIHoare p e v JFITrue) CC.
Proof.
  intros.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros.
  trivial.
Qed.

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
    (JFIHoare JFITrue (JFVal1 w) v (JFIEq (JFSyn (JFVar v)) w)) CC.
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

Lemma HTPreconditionStrenghtenSoundness : forall gamma s p p' e v q CC,
  (JFISemanticallyImplies gamma s (JFIImplies p p') CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare p' e v q) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e v q) CC.
Proof.
  intros gamma s p p' e v q CC.
  intros p_implies_p' hoare_p'.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros hs hn res.
  intros h_satisfies_p eval_e.
  set (h_satisfies_hoare_p' := hoare_p' env h gamma_match_env h_satisfies_s).
  simpl in h_satisfies_hoare_p'.
  apply (h_satisfies_hoare_p' hs hn res).
  + destruct (p_implies_p' env h gamma_match_env h_satisfies_s) as [not_h_satisfies_p | h_satisfies_p'].
    ++ destruct (not_h_satisfies_p h_satisfies_p).
    ++ exact h_satisfies_p'.
  + exact eval_e.
Qed.

Lemma HTPostconditionWeakenSoundness : forall gamma s p e v q q' cn u CC,
  (JFITermPersistent s) ->
  (JFISemanticallyImplies gamma s (JFIHoare p e v q') CC) ->
  (JFISemanticallyImplies gamma s
    (JFIForall cn u
      (JFIImplies (JFITermSubstituteVar v u q')
        (JFITermSubstituteVar v u q))) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e v q) CC.
Proof.
  intros gamma s p e v q q' cn u CC.
  intros s_persistent hoare_q' q_implies_q'.
  intros env h gamma_match_env h_satisfies_s.
  simpl.
  intros confs hn res.
  intros h_satisfies_p eval_e.
  set (h_satisfies_q' := hoare_q' env h gamma_match_env h_satisfies_s confs hn res h_satisfies_p eval_e);
  fold JFIHeapSatisfiesInEnv in h_satisfies_q'.
  set (gamma_match_env_in_hn := EvaluationPreservesGammaMatching gamma env h (JFIExprSubstituteEnv env e) confs hn res CC gamma_match_env eval_e).
  set (hn_satisfies_s := EvaluationPreservesPersistentTerms env s h (JFIExprSubstituteEnv env e) confs hn res CC s_persistent h_satisfies_s eval_e).
  set (h_satisfies_forall := q_implies_q' env hn gamma_match_env_in_hn hn_satisfies_s).
  simpl in h_satisfies_forall.
  destruct (h_satisfies_forall res) as [not_h_satisfies_q' | h_satisfies_q].
  + admit. (* TODO type of res *)
  + exfalso.
    apply not_h_satisfies_q'.
    apply VarNameChangePreservesHeapSatisfiying.
    exact h_satisfies_q'.
  + apply VarNameChangePreservesHeapSatisfiying with (u := u).
    exact h_satisfies_q.
Admitted.

Lemma HTCsqRuleSoundness : forall gamma s p p' e v q q' cn u CC,
  (JFITermPersistent s) ->
  (JFISemanticallyImplies gamma s (JFIImplies p p') CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare p' e v q') CC) ->
  (JFISemanticallyImplies gamma s
    (JFIForall cn u
      (JFIImplies (JFITermSubstituteVar v u q')
        (JFITermSubstituteVar v u q))) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e v q) CC.
Proof.
  intros gamma s p p' e v q q' cn u CC.
  intros s_persistent p_implies_p' hoare_p'q' q_implies_q'.
  apply HTPostconditionWeakenSoundness with (q':=q') (cn:=cn) (u:=u).
  + exact s_persistent.
  + apply HTPreconditionStrenghtenSoundness with (p':=p').
    ++ exact p_implies_p'.
    ++ exact hoare_p'q'.
  + exact q_implies_q'.
Qed.
Hint Resolve HTCsqRuleSoundness : core.

Lemma HTNewNotNullRuleSoundness : forall gamma s p mu cn vs v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare p (JFNew mu cn vs) v
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
  + eauto.
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
      (JFIHoare p (JFNew mu cn vs) v (JFIFieldEq (JFSyn (JFVar v)) field value)) CC.
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
  + eauto.
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

Lemma LetRuleE2Soundness : forall h' x e1_res e2 confs_e2 hn res class v q u r env CC,
  (JFILocOfType e1_res h' class) ->
  (JFIVarFreshInTerm v r) ->
  (JFIEvalInEnv h' (JFIExprSubstituteVal x (JFVLoc e1_res) e2) confs_e2 hn res env CC) ->
  (JFIHeapSatisfiesInEnv h' (JFITermSubstituteVal x (JFVLoc e1_res) q) env CC) ->
  (JFIHeapSatisfiesInEnv h' (JFIForall class v (JFIHoare (JFITermSubstituteVar x v q) (JFIExprSubstituteVar x v e2) u r)) env CC) ->
   JFIHeapSatisfiesInEnv hn r (StrMap.add u res env) CC
.
Proof.
  intros h' x e1_res e2 confs_e2 hn res class v q u r env CC.
  intros e1_res_type v_fresh_in_r e2_eval h'_satisfies_q h'_satisfies_forall.
  set (tmp := h'_satisfies_forall e1_res e1_res_type confs_e2 hn res).
  fold JFIHeapSatisfiesInEnv in tmp.
  simpl in tmp.
  apply AddingFreshVarInsidePreservesHeapSatisfiying with (x2 := v) (l2 := e1_res); try assumption.
  apply tmp.
  + apply SubstituteLocIffSubstituteVarInEnv.
    assumption.
  + unfold JFIEvalInEnv.
    rewrite SubstituteEnvVarElim.
    assumption.
Qed.

Lemma HTLetRuleSoundness : forall gamma s p e1 e2 class x q v u r CC,
  (JFITermPersistent s) ->
  (JFIVarFreshInTerm v r) ->
  (JFISemanticallyImplies gamma s (JFIHoare p e1 x q) CC) ->
  (JFISemanticallyImplies gamma s
          (JFIForall class v
             (JFIHoare
                (JFITermSubstituteVar x v q)
                (JFIExprSubstituteVar x v e2) u r)) CC) ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFLet class x e1 e2) u r) CC.
Proof.
  intros gamma s p e1 e2 class x q v u r CC.
  intros s_persistent v_fresh_in_r IH_e1 IH_e2.
  intros env h gamma_match_env.
  intros h_satisfies_s confs hn res new_env h_satisfies_p let_eval.

  set (let_evaluation := LetEvaluation h class x e1 e2 confs hn res env CC let_eval).
  destruct let_evaluation as (confs_e1 & (confs_e2 & (h' & (e1_res & (e1_eval & e2_eval))))).

  apply LetRuleE2Soundness with (h' := h') (x := x) (e1_res := e1_res) (e2 := e2)
    (confs_e2 := confs_e2) (class := class) (v := v) (q := q).
  + admit. (* e1_res type *)
  + assumption.
  + assumption.
  + apply LetRuleE1Soundness.
    apply (IH_e1 env h gamma_match_env h_satisfies_s confs_e1); assumption.
  + apply IH_e2.
    ++ apply EvaluationPreservesGammaMatching with (h := h) (e := (JFIExprSubstituteEnv env e1))
          (confs := confs_e1) (res := e1_res) (CC := CC); assumption.
    ++ apply EvaluationPreservesPersistentTerms with (h := h) (e := (JFIExprSubstituteEnv env e1))
          (confs := confs_e1) (res := e1_res); assumption.
Admitted.
Hint Resolve HTLetRuleSoundness : core.

Lemma HTFieldSetRuleSoundness : forall gamma s x field loc v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIImplies (JFIEq x JFnull) JFIFalse) (JFAssign (x, field) (JFVLoc loc))
       v (JFIFieldEq x field (JFVLoc loc))) CC.
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

Lemma HTIfRuleSoundness : forall gamma v1 v2 e1 e2 p q s u CC,
  (JFISemanticallyImplies gamma s 
    (JFIHoare (JFIAnd p (JFIEq v1 v2)) e1 u q) CC) ->
  (JFISemanticallyImplies gamma s
    (JFIHoare (JFIAnd p (JFIImplies (JFIEq v1 v2) JFIFalse)) e2 u q) CC) ->
   JFISemanticallyImplies gamma s
    (JFIHoare p (JFIf v1 v2 e1 e2) u q) CC.
Proof.
  intros gamma v1 v2 e1 e2 p q s u CC.
  intros IH_if_eq IH_if_neq.
  intros env h gamma_match_env h_satisfies_s.

  destruct (EnsureValIsLoc v1) as (l1 & v1_is_l1).
  destruct (EnsureValIsLoc v2) as (l2 & v2_is_l2).
  rewrite v1_is_l1.
  rewrite v2_is_l2.
  intros confs hn res env_res.
  intros h_satisfies_p eval_if.

  destruct confs as [ | (h', st') confs];  [destruct eval_if as (H & H0); discriminate H0 | ].
  destruct (Classical_Prop.classic (l1 = l2)) as [l1_eq_l2 | l1_neq_l2].
  + apply IfEvaluationStepEq in eval_if as (h_eq_h' & eval_e1).
    rewrite <- h_eq_h' in eval_e1.
    ++ set (if_eq_then_eval_e1_satisfies_q := IH_if_eq env h gamma_match_env h_satisfies_s confs hn res);
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
    ++ set (if_neq_then_eval_e2_satisfies_q := IH_if_neq env h gamma_match_env h_satisfies_s confs hn res);
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

(* =============== Main theorem =============== *)

Theorem JFISoundness : forall gamma decls p t CC,
  (JFIProves decls gamma p t) ->
   JFISemanticallyImplies gamma p t CC.
Proof.
  intros gamma decls p t CC.
  intros jfi_proof.
  induction jfi_proof as
  [
  (* JFIAsmRule *)
    decls gamma p
  (* JFITransRule *)
  | q decls gamma p r _ IH_p_proves_q _ IH_q_proves_r
  (* JFIEqRule *)
  | q x v1 v2 r decls gamma p r_is_subst_v2 _ IH_p_proves_subst_v1 _ IH_p_proves_v1_eq_v2
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
  (* JFITypeAddRule *)
  |  x cn gamma decls gamma' s p
  (* JFISepWeakRule *)
  |  decls gamma p1 p2
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
  |  decls gamma p q r s e v
  (* JFIHTFalseRule *)
  |  decls gamma s q e v
  (* JFIHTTrueRule *)
  |  decls gamma s p e v
  (* JFIHTRetRule *)
  |  decls gamma s v w
  (* JFIHTCsqRule *)
  |  p' q' cn u decls gamma s p q v e s_persistent _ IH_p_implies_p' _ IH_HT_p'evq' _ IH_q'_implies_q
  (* JFIHTDisjIntroRule *)
  |  decls gamma s p q r e v
  (* JFIHTDisjElimLRule *)
  |  decls gamma s p q r e v
  (* JFIHTDisjElimRRule *)
  |  decls gamma s p q r e v
  (* JFIHTEqRule *)
  |  decls gamma s v1 v2 p e v q
  (* JFIHTEqRule *)
  |  decls gamma s v1 v2 p e v q
  (* JFIHTNewNotNullRule *)
  |  decls gamma s p mu cn vs v
  (* JFIHTNewFieldRule *)
  |  decls gamma s p mu cn vs v objflds n field value objflds_is_flds field_n value_n
  (* JFIHTLetRule *)
  |  v q decls gamma p r s e1 e2 x u class s_persistent v_fresh_in_r _ IH_e1 _ IH_e2
  (* JFIHTFieldSetRule *)
  |  decls gamma s x field v loc
  (* JFIHTIfRule *)
  |  decls gamma p v1 v2 e1 e2 u q s _ IH_if_eq _ IH_if_neq
  (* JFIHTInvokeRetRule *)
  |  cn method rettypeCN p' w q' x decls gamma s p q u v vs mn
  (* JFIHTInvokeNoRetRule *)
  |  cn method p' w q' decls gamma s p q u v vs mn
  ].
  (* JFIAsmRule *)
  + apply AsmRuleSoundness.
  (* JFITransRule *)
  + apply (TransRuleSoundness gamma p q r).
    ++ exact IH_p_proves_q.
    ++ exact IH_q_proves_r.
  (* JFIEqRule *)
  + apply EqRuleSoundness with (x := x) (v1 := v1) (v2 := v2) (q := q).
    ++ exact r_is_subst_v2.
    ++ exact IH_p_proves_subst_v1.
    ++ exact IH_p_proves_v1_eq_v2.
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
  + admit. (* TODO *)
  (* JFIExistsIntroRule *)
  + admit. (* TODO *)
  (* JFIExistsElimRule *)
  + admit. (* TODO *)
  (* JFITypeAddRule *)
  + admit. (* TODO *)
  (* JFISepWeakRule *)
  + admit. (* TODO *)
  (* JFISepAssoc1Rule *)
  + admit. (* TODO *)
  (* JFISepAssoc2Rule *)
  + admit. (* TODO *)
  (* JFISepCommRule *)
  + admit. (* TODO *)
  (* JFISepIntroRule *)
  + admit. (* TODO *)
  (* JFISepIntroPersistentRule *)
  + admit. (* TODO *)
  (* JFIWandIntroRule *)
  + admit. (* TODO *)
  (* JFIWandElimRule *)
  + admit. (* TODO *)
  (* JFIHTFrameRule *)
  + admit. (* TODO *)
  (* JFIHTFalseRule *)
  + apply HTFalseRuleSoundness.
  (* JFIHTTrueRule: *)
  + apply HTTrueRuleSoundness.
  (* JFIHTRetRule *)
  + apply HTRetRuleSoundness.
  (* JFIHTCsqRule: *)
  + eauto.
  (* JFIHTDisjIntroRule *)
  + admit. (* TODO *)
  (* JFIHTDisjElimLRule *)
  + admit. (* TODO *)
  (* JFIHTDisjElimRRule *)
  + admit. (* TODO *)
  (* JFIHTEqRule1 *)
  + admit. (* TODO *)
  (* JFIHTEqRule2 *)
  + admit. (* TODO *)
  (* JFIHTNewNotNullRule *)
  + eauto.
  (* JFIHTNewFieldRule *)
  + eauto.
  (* JFIHTLetRule *)
  + eauto.
  (* JFIHTFieldSetRule *)
  + eauto.
  (* JFIHTIfRule *)
  + apply HTIfRuleSoundness.
    ++ exact IH_if_eq.
    ++ exact IH_if_neq.
  (* JFIHTInvokeRetRule *)
  + admit. (* TODO *)
  (* JFIHTInvokeNoRetRule *)
  + admit. (* TODO *)
Admitted.

