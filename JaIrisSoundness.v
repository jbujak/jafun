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
Require Import JaIris.
Require Import Bool.
Require Import Classical_Prop.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module HeapFacts := Facts Heap.
Module StrMapFacts := Facts StrMap.

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

Lemma JFIEmptyHeapDisjoint: forall h, JFIHeapsDisjoint (Heap.empty Obj) h.
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

Lemma ShrinkedGammaMatchesShrinkedEnv : forall x l type env gamma h,
  (JFIGammaMatchEnv h gamma env) ->
  (JFILocOfType l h type) ->
  (JFIGammaMatchEnv h (StrMap.remove x gamma) ((StrMap.remove x env))).
Proof.
Admitted.

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

Lemma EqualValuesExistInEnv : forall h env val1 val2,
  (JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env) ->
   exists loc1 loc2, JFIValToLoc val1 env = Some loc1 /\ JFIValToLoc val2 env = Some loc2.
Proof.
  intros h env val1 val2.
  intros h_satisfies_eq.
  unfold JFIHeapSatisfiesInEnv in h_satisfies_eq.
  destruct (JFIValToLoc val1 env), (JFIValToLoc val2 env).
  + exists l, l0.
    split; trivial.
  + destruct h_satisfies_eq.
  + destruct h_satisfies_eq.
  + destruct h_satisfies_eq.
Qed.

Lemma ValToLocGivesSomeIffArgInEnv : forall env x,
  (exists loc, JFIValToLoc (JFSyn (JFVar x)) env = Some loc) <-> (StrMap.In x env).
Proof.
  intros env x.
  split; unfold JFIValToLoc; apply StrMap_in_find_iff.
Qed.

Lemma ExtendingEnvPreservesExistingVars : forall v x l loc env,
  (~ StrMap.In x env) ->
  (JFIValToLoc v env = Some loc) ->
   JFIValToLoc v env = JFIValToLoc v (StrMap.add x l env).
Proof.
  intros v x l loc env.
  intros x_not_in_env v_in_env.
  unfold JFIValToLoc.
  destruct v.
  + trivial.
  + destruct x0.
    ++ symmetry.
       destruct (Classical_Prop.classic (x = x0)) as [ x_eq_x0 | x_ne_x0 ].
       +++ replace x0 with x in v_in_env.
           - exfalso.
             destruct (ValToLocGivesSomeIffArgInEnv env x) as ( _ & H ).
             apply (ex_intro (fun (y : Loc) => JFIValToLoc (JFSyn (JFVar x)) env = Some y)) in v_in_env.
             apply (ValToLocGivesSomeIffArgInEnv env x) in v_in_env.
             apply x_not_in_env.
             apply v_in_env.
       +++ apply StrMapFacts.add_neq_o.
           exact x_ne_x0.
    ++ trivial. (* TODO this *)
Qed.

Lemma EnvAddNewGivesSomeThenItIsJustAdd : forall x l env env_x,
  (JFIEnvAddNew x l env = Some env_x) ->
    (StrMap.add x l env) = env_x.
Proof.
  intros x l env env_x.
  intros add_x_to_env.
  unfold JFIEnvAddNew in add_x_to_env.
  destruct (StrMap.mem (elt:=Loc) x env).
    ++ discriminate add_x_to_env.
    ++ injection add_x_to_env.
       trivial.
Qed.

Lemma EnvAddNewPreservesExistingVars : forall v x l loc env env_x,
  (JFIEnvAddNew x l env = Some env_x) ->
  (JFIValToLoc v env = Some loc) ->
   JFIValToLoc v env = JFIValToLoc v env_x.
Proof.
  intros v x l loc env env_x.
  intros add_x_to_env v_is_some_loc.
  unfold JFIEnvAddNew in add_x_to_env.
  fold JFIEnvAddNew in add_x_to_env.
  replace env_x with (StrMap.add x l env).
  + apply ExtendingEnvPreservesExistingVars with (loc := loc).
    ++ unfold not.
       intros x_in_env.
       apply StrMapFacts.mem_in_iff in x_in_env.
       destruct (StrMap.mem (elt:=Loc) x env).
       +++ discriminate add_x_to_env.
       +++ discriminate x_in_env.
    ++ exact v_is_some_loc.
  + apply EnvAddNewGivesSomeThenItIsJustAdd.
    exact add_x_to_env.
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

Lemma ExtendingEnvPreservesHeapSatisfiyingEq : forall val1 val2 x l env env_x h,
  (JFIEnvAddNew x l env = Some env_x) ->
  (JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env) ->
   JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env_x.
Proof.
  intros val1 val2 x l env env_x h.
  intros add_env_x h_satisfies_eq.
  simpl.
  replace (JFIValToLoc val1 env_x) with (JFIValToLoc val1 env);
    replace (JFIValToLoc val2 env_x) with (JFIValToLoc val2 env).
  + exact h_satisfies_eq.
  + unfold JFIHeapSatisfiesInEnv in h_satisfies_eq.
    destruct (JFIValToLoc val1 env) in h_satisfies_eq.
    ++ apply EnvAddNewPreservesExistingVars with (x := x) (l := l) (loc := l0).
       exact add_env_x.
       +++ destruct (JFIValToLoc val2 env).
           - replace l0 with l1.
             trivial.
           - destruct h_satisfies_eq.
    ++ destruct h_satisfies_eq.
  + unfold JFIHeapSatisfiesInEnv in h_satisfies_eq.
    destruct (JFIValToLoc val2 env) in h_satisfies_eq.
    ++ apply EnvAddNewPreservesExistingVars with (x := x) (l := l) (loc := l0).
       +++ exact add_env_x.
       +++ destruct (JFIValToLoc val1 env).
           - replace l0 with l1.
              trivial.
           - destruct h_satisfies_eq.
    ++ destruct (JFIValToLoc val1 env); destruct h_satisfies_eq.
  + unfold JFIHeapSatisfiesInEnv in h_satisfies_eq.
    destruct (JFIValToLoc val1 env) in h_satisfies_eq.
    ++ apply EnvAddNewPreservesExistingVars with (x := x) (l := l) (loc := l0).
       +++ exact add_env_x.
       +++ destruct (JFIValToLoc val2 env).
           - replace l0 with l1.
              trivial.
           - destruct h_satisfies_eq.
    ++ destruct h_satisfies_eq.
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

Lemma AddingFreshVarPreservesHeapSatisfiyingEq : forall val1 val2 x l env h,
  (JFIVarFreshInTerm x (JFIEq val1 val2)) ->
    ((JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env) <->
      JFIHeapSatisfiesInEnv h (JFIEq val1 val2) (StrMap.add x l env)).
Proof.
  intros val1 val2 x l env h.
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

Lemma AddingFreshVarPreservesHeapSatisfiyingFieldEq : forall obj field val x l env h,
  (JFIVarFreshInTerm x (JFIFieldEq obj field val)) ->
    ((JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env) <->
      JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) (StrMap.add x l env)).
Proof.
  intros obj field val x l env h.
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

Definition EqualEnvsEquivalentInTermForHeap (t : JFITerm) (h : Heap) :=
  forall env1 env2, 
    (EnvEq env1 env2) -> ((JFIHeapSatisfiesInEnv h t env1) <-> (JFIHeapSatisfiesInEnv h t env2)).

Lemma EnvEqSymmetry : forall env1 env2,
  (EnvEq env1 env2) -> (EnvEq env2 env1).
Proof.
Admitted.

Lemma AddPreservesEnvEq : forall x l env1 env2,
  (EnvEq env1 env2) -> (EnvEq (StrMap.add x l env1) (StrMap.add x l env2)).
Proof.
Admitted.

Lemma AddOrderChangePreservesEnvEq : forall x1 l1 x2 l2 env,
  EnvEq (StrMap.add x1 l1 (StrMap.add x2 l2 env)) (StrMap.add x2 l2 (StrMap.add x1 l1 env)).
Proof.
Admitted.

Lemma EnvEqGivesExistsImplication : forall h type x t env1 env2,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t h) ->
  (JFIHeapSatisfiesInEnv h (JFIExists type x t) env1) ->
   JFIHeapSatisfiesInEnv h (JFIExists type x t) env2.
Proof.
  intros h type x t env1 env2.
  intros env1_eq_env2 t_equivalence h_satisfies_exists_t.
  simpl.
  simpl in h_satisfies_exists_t.
  destruct h_satisfies_exists_t as ( loc & (loc_of_type & h_satisfies_t)).
  unfold EqualEnvsEquivalentInTermForHeap in t_equivalence.
  exists loc.
  split.
  + exact loc_of_type.
  + apply (t_equivalence (StrMap.add x loc env1) (StrMap.add x loc env2)).
    ++ apply AddPreservesEnvEq.
       exact env1_eq_env2.
    ++ exact h_satisfies_t.
Qed.

Lemma EnvEqGivesForallImplication : forall h type x t env1 env2,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t h) ->
  (JFIHeapSatisfiesInEnv h (JFIForall type x t) env1) ->
   JFIHeapSatisfiesInEnv h (JFIForall type x t) env2.
Proof.
  intros h type x t env1 env2.
  intros env1_eq_env2 t_equivalence h_satisfies_t.
  simpl.
  intros loc loc_of_type.
  unfold EqualEnvsEquivalentInTermForHeap in t_equivalence.
  apply (t_equivalence (StrMap.add x loc env1) (StrMap.add x loc env2)).
  + apply AddPreservesEnvEq.
    exact env1_eq_env2.
  + exact (h_satisfies_t loc loc_of_type).
Qed.

Lemma EqualEnvsAreEquivalent : forall h t env1 env2,
  (EnvEq env1 env2) ->
    ((JFIHeapSatisfiesInEnv h t env1) <-> (JFIHeapSatisfiesInEnv h t env2)).
Proof.
  intros h t.
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
  + admit.
  (* JFIFalse *)
  + admit.
  (* JFIAnd t1 t2 *)
  + admit.
  (* JFIOr t1 t2 *)
  + admit.
  (* JFIImplies t1 t2 *)
  + admit.
  (* JFIExists *)
  + intros env1 env2.
    intros env1_eq_env2.
    split; apply EnvEqGivesExistsImplication; try exact IH_t.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIForall *)
  + intros env1 env2.
    intros env1_eq_env2.
    split; apply EnvEqGivesForallImplication; try exact IH_t.
    ++ exact env1_eq_env2.
    ++ exact (EnvEqSymmetry env1 env2 env1_eq_env2).
  (* JFIHoare *)
  + admit.
  (* JFIEq *)
  + admit.
  (* JFIFieldEq *)
  + admit.
  (* JFISep*)
  + admit.
  (* JFIWand *)
  + admit.
Admitted.

Lemma EnvOrderChangePreservesHeapSatisfiying : forall h t x1 l1 x2 l2 env,
  (x1 <> x2) ->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x1 l1 (StrMap.add x2 l2 env))) <->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x2 l2 (StrMap.add x1 l1 env))).
Proof.
  intros h t x1 l1 x2 l2 env.
  intros x1_neq_x2.
  apply EqualEnvsAreEquivalent.
  apply AddOrderChangePreservesEnvEq.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfiying : forall h q x l env,
  (JFIVarFreshInTerm x q) ->
    ((JFIHeapSatisfiesInEnv h q env) <->
      JFIHeapSatisfiesInEnv h q (StrMap.add x l env)).
Proof.
  intros h q x l.
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
  +intros env x_fresh.
    split;
    apply AddingFreshVarPreservesHeapSatisfiyingFieldEq with (x := x) (l := l);
    exact x_fresh.
  (* JFISep*)
  + admit.
  (* JFIWand *)
  + admit.
Admitted.

Lemma ExtendingEnvPreservesHeapSatisfiying : forall h q x l env env_x,
  (JFIEnvAddNew x l env = Some env_x) ->
    ((JFIHeapSatisfiesInEnv h q env) <->
      JFIHeapSatisfiesInEnv h q env_x).
Proof.
  intros h q x l env env_x.
  intros add_env_x.
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
    split; intros (h_satisfies_t1 & h_satisfies_t2); split.
    ++ apply IH_t1; exact h_satisfies_t1.
    ++ apply IH_t2; exact h_satisfies_t2.
    ++ apply IH_t1; exact h_satisfies_t1.
    ++ apply IH_t2; exact h_satisfies_t2.
  (* JFIOr t1 t2 *)
  + simpl.
    split; intros [ h_satisfies_t1 | h_satisfies_t2 ].
    ++ apply or_introl.
       apply IH_t1; exact h_satisfies_t1.
    ++ apply or_intror.
       apply IH_t2; exact h_satisfies_t2.
    ++ apply or_introl.
       apply IH_t1; exact h_satisfies_t1.
    ++ apply or_intror.
       apply IH_t2; exact h_satisfies_t2.
  (* JFIImplies t1 t2 *)
  + simpl.
    split; intros [ not_h_satisfies_t1 | h_satisfies_t2 ].
    ++ apply or_introl.
       unfold not.
       intros h_satisfies_t1.
       apply IH_t1 in h_satisfies_t1.
       exact (not_h_satisfies_t1 h_satisfies_t1).
    ++ apply or_intror.
       apply IH_t2; exact h_satisfies_t2.
    ++ apply or_introl.
       unfold not.
       intros h_satisfies_t1.
       apply IH_t1 in h_satisfies_t1.
       exact (not_h_satisfies_t1 h_satisfies_t1).
    ++ apply or_intror.
       apply IH_t2; exact h_satisfies_t2.
  (* JFIExists *)
  + admit.
  (* JFIForall *)
  + admit.
  (* JFIHoare *)
  + admit.
  (* JFIEq *)
  + split.
    ++ apply ExtendingEnvPreservesHeapSatisfiyingEq with (x := x) (l := l).
       exact add_env_x.
    ++ admit.
  (* JFIFieldEq *)
  + admit.
  (* JFISep*)
  + admit.
  (* JFIWand *)
  + admit.
Admitted.



Lemma GammaAddRemove : forall x type gamma gamma_x,
  (JFIGammaAddNew x type gamma = Some gamma_x) ->
   StrMap.remove x gamma_x = gamma.
Proof.
Admitted.

Lemma EnvAddRemove : forall x l env,
  (StrMap.find x env = Some l) ->
   EnvEq env (StrMap.add x l (StrMap.remove x env)).
Proof.
Admitted.

Lemma VarFromGammaIsInMatchingEnv : forall x x_type gamma env_x h,
  (JFIGammaMatchEnv h gamma env_x) ->
   exists l, StrMap.find x env_x = Some l /\ JFILocOfType l h x_type.
Proof.
Admitted.

Lemma GammaAddNewSimple : forall x type gamma gamma_x,
  (JFIGammaAddNew x type gamma = Some gamma_x) ->
   StrMap.add x type gamma = gamma_x.
Proof.
Admitted.

Lemma ExistsShrinkedEnv : forall gamma x x_type gamma_x env_x h,
  (JFIGammaAddNew x x_type gamma = Some gamma_x) ->
  (JFIGammaMatchEnv h gamma_x env_x) ->
  exists env l, JFIGammaMatchEnv h gamma env /\ EnvEq env_x (StrMap.add x l env).
Proof.
  intros gamma x type gamma_x env_x h.
  intros gamma_add_x gamma_x_match_env_x.
  exists (StrMap.remove x env_x).
  set (exists_l := VarFromGammaIsInMatchingEnv x type gamma_x env_x h gamma_x_match_env_x).
  destruct exists_l as (l & (find_x_gives_some_l & l_of_type)).
  exists l.
  split.
  + replace gamma with (StrMap.remove x gamma_x).
    ++ apply ShrinkedGammaMatchesShrinkedEnv with (l := l) (type := type).
       +++ exact gamma_x_match_env_x.
       +++ exact l_of_type.
    ++ unfold JFIGammaAdd.
       apply GammaAddRemove with (type := type).
       exact gamma_add_x.
  + apply EnvAddRemove.
    exact find_x_gives_some_l.
Qed.

Lemma ExtendingGammaPreservesSoundness : forall h q x x_type gamma gamma_x,
  (JFIVarFreshInTerm x q) ->
  (JFIGammaAddNew x x_type gamma = Some gamma_x) ->
    ((JFIHeapSatisfies h q gamma) <-> (JFIHeapSatisfies h q gamma_x)).
Proof.
  intros h q x x_type gamma gamma_x.
  intros x_fresh gamma_add_new_x.
  split.
  + intros h_satisfies_q.
    unfold JFIHeapSatisfies.
    intros env_x gamma_x_match_env_x.
    apply ExistsShrinkedEnv
      with (gamma := gamma) (x := x) (x_type := x_type)
      in gamma_x_match_env_x
      as (env & l & (gamma_match_env & env_x_eq_env_with_x)).
    ++ apply EqualEnvsAreEquivalent with (env1 := env_x) (env2 := (StrMap.add x l env)).
       +++ exact env_x_eq_env_with_x.
       +++ apply AddingFreshVarPreservesHeapSatisfiying.
           - exact x_fresh.
           - apply h_satisfies_q.
             exact gamma_match_env.
    ++ exact gamma_add_new_x.
  + intros h_satisfies_q.
    unfold JFIHeapSatisfies.
    intros env gamma_match_env.
    apply (AddingFreshVarPreservesHeapSatisfiying h q x null env).
    ++ exact x_fresh.
    ++ apply h_satisfies_q.
       apply StrictlyExtendedGammaMatchesExtendedEnv with (type := x_type) (gamma := gamma).
       +++ exact gamma_match_env.
       +++ unfold JFILocOfType. trivial.
       +++ exact gamma_add_new_x.
Qed.

(* =============== Substitution Lemmas =============== *)

Definition JFISubstitutionImplies x v1 v2 t h env :=
    JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v1 t) env ->
    JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v2 t) env.

Definition JFISubstitutionsEquivalent x v1 v2 t h env :=
  JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v1 t) env <->
  JFIHeapSatisfiesInEnv h (JFITermSubstituteVal x v2 t) env.

Lemma JFISubstitutionEquivalenceSymmetry : forall x v1 v2 t h env,
  (JFISubstitutionsEquivalent x v1 v2 t h env) ->
   JFISubstitutionsEquivalent x v2 v1 t h env.
Proof.
  intros x v1 v2 t h env.
  unfold JFISubstitutionsEquivalent.
  intros equivalence.
  symmetry.
  exact equivalence.
Qed.

Lemma JFISubstitutionsEquivalenceGivesAndImplication : forall v1 v2 x t1 t2 h env,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env) ->
   JFISubstitutionImplies x v1 v2 (JFIAnd t1 t2) h env.
Proof.
  intros v1 v2 x t1 t2 h env.
  intros IH_t1 IH_t2.
  simpl.
  intros ( h_satisfies_subst_in_t1 & h_satisfies_subst_in_t2 ).
  split.
  + apply IH_t1.
    exact h_satisfies_subst_in_t1.
  + apply IH_t2.
    exact h_satisfies_subst_in_t2.
Qed.

Lemma JFISubstitutionsEquivalenceGivesOrImplication : forall v1 v2 x t1 t2 h env,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env) ->
   JFISubstitutionImplies x v1 v2 (JFIOr t1 t2) h env.
Proof.
  intros v1 v2 x t1 t2 h env.
  intros IH_t1 IH_t2.
  intros [ h_satisfies_subst_in_t1 | h_satisfies_subst_in_t2 ]; simpl.
  + apply or_introl.
    apply IH_t1.
    exact h_satisfies_subst_in_t1.
  + apply or_intror.
    apply IH_t2.
    exact h_satisfies_subst_in_t2.
Qed.

Lemma JFISubstitutionsEquivalenceGivesImpliesImplication : forall v1 v2 x t1 t2 h env,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env) ->
   JFISubstitutionImplies x v1 v2 (JFIImplies t1 t2) h env.
Proof.
  intros v1 v2 x t1 t2 h env.
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

Lemma SubheapPreservesEquivalence : forall h1 x v1 v2 t h env,
  (JFISubstitutionsEquivalent x v1 v2 t h env) ->
  (JFISubheap h1 h) ->
   JFISubstitutionsEquivalent x v1 v2 t h1 env.
Proof.
  intros h1 x v1 v2 t h env.
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

Lemma JFISubstitutionsEquivalenceGivesSepImplication : forall v1 v2 x t1 t2 h env,
  (JFISubstitutionsEquivalent x v1 v2 t1 h env) ->
  (JFISubstitutionsEquivalent x v1 v2 t2 h env) ->
   JFISubstitutionImplies x v1 v2 (JFISep t1 t2) h env.
Proof.
  intros v1 v2 x t1 t2 h env.
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

(* =============== Equality Lemmas =============== *)

Lemma EqualValuesGiveEqualLocations : forall h v1 v2 env,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env) ->
  JFIValToLoc v1 env = JFIValToLoc v2 env.
Proof.
  intros h v1 v2 env.
  intros h_satisfies_eq.
  unfold JFIHeapSatisfiesInEnv in h_satisfies_eq.
  destruct (JFIValToLoc v1 env), (JFIValToLoc v2 env).
  + replace l0 with l.
    trivial.
  + destruct h_satisfies_eq.
  + destruct h_satisfies_eq.
  + trivial.
Qed.

Lemma EqualValuesGiveEqualLocationsAfterSubstitution : forall h x v1 v2 val env,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env) ->
  (JFIValToLoc (JFIValSubstituteVal x v1 val) env)
    = (JFIValToLoc (JFIValSubstituteVal x v2 val) env).
Proof.
  intros h x v1 v2 val env.
  intros v1_eq_v2.
  unfold JFIValSubstituteVal.
  unfold JFIHeapSatisfiesInEnv.
  destruct val.
  + trivial.
  + destruct x0.
    ++ destruct (String.eqb x0 x).
       +++ apply (EqualValuesGiveEqualLocations h).
           exact v1_eq_v2.
       +++ trivial.
    ++ trivial.
Qed.

Ltac replace_two_values x v1 v2 env value1 value2 :=
  replace (JFIValToLoc (JFIValSubstituteVal x v2 value1) env)
     with (JFIValToLoc (JFIValSubstituteVal x v1 value1) env);
 [replace (JFIValToLoc (JFIValSubstituteVal x v2 value2) env)
     with (JFIValToLoc (JFIValSubstituteVal x v1 value2) env) |].

Lemma EqualityGivesEqImplication : forall x v1 v2 val1 val2 h env,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env) ->
   JFISubstitutionImplies x v1 v2 (JFIEq val1 val2) h env.
Proof.
  intros x v1 v2 val1 val2 h env.
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
    ++ apply (EqualValuesGiveEqualLocationsAfterSubstitution h).
       exact h_satisfies_v1_eq_v2.
    ++ apply (EqualValuesGiveEqualLocationsAfterSubstitution h).
       exact h_satisfies_v1_eq_v2.
  + replace_two_values x v1 v2 env (JFSyn x0) (JFVLoc l).
    ++ exact h_satisfies_subst_v1_in_eq.
    ++ apply (EqualValuesGiveEqualLocationsAfterSubstitution h).
       exact h_satisfies_v1_eq_v2.
    ++ apply (EqualValuesGiveEqualLocationsAfterSubstitution h).
       exact h_satisfies_v1_eq_v2.
  + replace_two_values x v1 v2 env (JFSyn x0) (JFSyn x1).
    ++ exact h_satisfies_subst_v1_in_eq.
    ++ apply (EqualValuesGiveEqualLocationsAfterSubstitution h).
       exact h_satisfies_v1_eq_v2.
    ++ apply (EqualValuesGiveEqualLocationsAfterSubstitution h).
       exact h_satisfies_v1_eq_v2.
Qed.

Ltac binop_equivalence_from_operands_implication lhs_implication rhs_implication binop_implication :=
  split;
  [
    apply binop_implication; [apply lhs_implication | apply rhs_implication]
  | apply binop_implication; apply JFISubstitutionEquivalenceSymmetry; [apply lhs_implication | apply rhs_implication]
  ].

Lemma EqSymmetry: forall h v1 v2 env,
  ((JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env) -> (JFIHeapSatisfiesInEnv h (JFIEq v2 v1) env)).
Proof.
  intros h v1 v2 env.
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

Lemma EqReflexivity: forall v h env,
   JFIHeapSatisfiesInEnv h (JFIEq v v) env.
Proof.
  intros h v env.
  unfold JFIHeapSatisfiesInEnv.
  destruct (JFIValToLoc h env).
  + trivial.
  + admit. (* TODO zapewnic obecnosc zmiennej w srodowisku *)
Admitted.

Lemma JFIEqualValuesAreEquivalent : forall v1 v2 h x q env,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env) ->
  JFISubstitutionsEquivalent x v1 v2 q h env.
Proof.
  intros v1 v2 h x q env.
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

Lemma FalseElimRuleSoundness : forall q h env,
  (JFIHeapSatisfiesInEnv h JFIFalse env) ->
   JFIHeapSatisfiesInEnv h q env.
Proof.
  intros q h env.
  intros h_satisfies_false.
  simpl in h_satisfies_false.
  destruct h_satisfies_false.
Qed.

Lemma TrueIntroRuleSoundness : forall h env,
  JFIHeapSatisfiesInEnv h JFITrue env.
Proof.
  intros h env.
  unfold JFIHeapSatisfiesInEnv.
  trivial.
Qed.

Lemma AndIntroRuleSoundness : forall r h env p q,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h p env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h q env) ->
   JFIHeapSatisfiesInEnv h (JFIAnd p q) env.
Proof.
  intros h env p q r.
  intros h_satisfies_r r_implies_p r_implies_q.
  simpl.
  split.
  + apply r_implies_p.
    exact h_satisfies_r.
  + apply r_implies_q.
    exact h_satisfies_r.
Qed.

Lemma AndElimLRuleSoundness : forall q r h env p,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h (JFIAnd p q) env) ->
   JFIHeapSatisfiesInEnv h p env.
Proof.
  intros q h env p r.
  intros h_satisfies_r r_implies_p_and_q.
  apply r_implies_p_and_q.
  exact h_satisfies_r.
Qed.

Lemma AndElimRRuleSoundness : forall p r h env q,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h (JFIAnd p q) env) ->
   JFIHeapSatisfiesInEnv h q env.
Proof.
  intros q h env p r.
  intros h_satisfies_r r_implies_p_and_q.
  apply r_implies_p_and_q.
  exact h_satisfies_r.
Qed.

Lemma OrIntroLRuleSoundness : forall r p q h env,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h p env) ->
   JFIHeapSatisfiesInEnv h (JFIOr p q) env.
Proof.
  intros r p q h env.
  intros h_satisfies_r r_implies_p.
  simpl.
  apply or_introl.
  apply r_implies_p.
  exact h_satisfies_r.
Qed.

Lemma OrIntroRRuleSoundness : forall r p q h env,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h q env) ->
   JFIHeapSatisfiesInEnv h (JFIOr p q) env.
Proof.
  intros r p q h env.
  intros h_satisfies_r r_implies_q.
  simpl.
  apply or_intror.
  apply r_implies_q.
  exact h_satisfies_r.
Qed.

Lemma OrElimRuleSoundness : forall p q s r h env,
  (JFIHeapSatisfiesInEnv h s env) ->
  (JFIHeapSatisfiesInEnv h s env -> JFIHeapSatisfiesInEnv h (JFIOr p q) env) ->
  (JFIHeapSatisfiesInEnv h (JFIAnd s p) env -> JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h (JFIAnd s q) env -> JFIHeapSatisfiesInEnv h r env) ->
   JFIHeapSatisfiesInEnv h r env.
Proof.
  intros p q s r h env.
  intros h_satisfies_s s_implies_p_or_q s_and_p_implies_r s_and_q_implies_r.
  apply s_implies_p_or_q in h_satisfies_s as h_satisfies_p_or_q.
  simpl in h_satisfies_p_or_q.
  destruct h_satisfies_p_or_q as [ h_satisfies_p | h_satisfies_q ].
  + apply s_and_p_implies_r.
    simpl.
    split.
    ++ exact h_satisfies_s.
    ++ exact h_satisfies_p.
  + apply s_and_q_implies_r.
    simpl.
    split.
    ++ exact h_satisfies_s.
    ++ exact h_satisfies_q.
Qed.

Lemma ImpliesIntroRuleSoundness : forall r p q h env,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h (JFIAnd r p) env -> JFIHeapSatisfiesInEnv h q env) ->
   JFIHeapSatisfiesInEnv h (JFIImplies p q) env.
Proof.
  intros r p q h env.
  intros h_satisfies_r r_and_p_implies_q.
  simpl.
  simpl in r_and_p_implies_q.
  apply Classical_Prop.imply_to_or.
  intros h_satisfies_p.
  apply r_and_p_implies_q.
  apply (conj h_satisfies_r h_satisfies_p).
Qed.

Lemma ImpliesElimRuleSoundness : forall p r q h env,
  (JFIHeapSatisfiesInEnv h r env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h (JFIImplies p q) env) ->
  (JFIHeapSatisfiesInEnv h r env -> JFIHeapSatisfiesInEnv h p env) ->
   JFIHeapSatisfiesInEnv h q env.
Proof.
  intros p r q h env.
  intros h_satisfies_r r_implies_p_implies_q r_implies_p.
  simpl in r_implies_p_implies_q.
  apply (Classical_Prop.or_to_imply (JFIHeapSatisfiesInEnv h p env)).
  + apply r_implies_p_implies_q.
    exact h_satisfies_r.
  + apply r_implies_p.
    exact h_satisfies_r.
Qed.

Lemma ForallIntroRuleSoundndess : forall x type p q h gamma gamma_x env,
  (JFIVarFreshInTerm x q) ->
  (JFIGammaAddNew x type gamma = Some gamma_x) ->
  (JFIHeapSatisfies h q gamma) ->
  (JFIHeapSatisfies h q gamma_x ->
      JFIHeapSatisfies h p gamma_x) ->
  (JFIGammaMatchEnv h gamma env) -> 
   JFIHeapSatisfiesInEnv h (JFIForall type x p) env.
Proof.
  intros x type p q h gamma gamma_x env.
  intros x_fresh_in_q gamma_add_new_x h_satisfies_q q_implies_p gamma_match_env.
  simpl.
  intros l l_of_type.
  apply q_implies_p.
  + apply (ExtendingGammaPreservesSoundness h q x type gamma gamma_x x_fresh_in_q gamma_add_new_x).
    exact h_satisfies_q.
  + apply StrictlyExtendedGammaMatchesExtendedEnv with (type := type) (gamma := gamma).
    ++ exact gamma_match_env.
    ++ exact l_of_type.
    ++ exact gamma_add_new_x.
Qed.

(* =============== Main theorem =============== *)

Theorem JFISoundness : forall gamma decls h p t,
  (JFIProves decls gamma p t) ->
  (JFIHeapSatisfies h p gamma) ->
   JFIHeapSatisfies h t gamma.
Proof.
  intros gamma decls h p t.
  intros jfi_proof.
  intros h_satisfies_p. (* TODO wrzucić do indukcji *)
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
  |  p' q' cn u decls gamma s p q v e
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
  (* JFIHTLetRule *)
  |  v q decls gamma p r s e1 e2 x u class
  (* JFIHTFieldAssignRule *)
  |  decls gamma s x field v loc
  (* JFIHTIfRule *)
  |  decls gamma p v1 v2 e1 e2 u q s
  (* JFIHTInvokeRetRule *)
  |  cn method rettypeCN p' w q' x decls gamma s p q u v vs mn
  (* JFIHTInvokeNoRetRule *)
  |  cn method p' w q' decls gamma s p q u v vs mn
  ]; intros env gamma_match_env.

  (* JFIAsmRule *)
  + apply h_satisfies_p.
    exact gamma_match_env.
  (* JFITransRule *)
  + apply IH_q_proves_r.
    ++ intros env' gamma_match_env'.
       apply IH_p_proves_q.
       +++ exact h_satisfies_p.
       +++ exact gamma_match_env'.
    ++ exact gamma_match_env.
  (* JFIEqRule *)
  + rewrite r_is_subst_v2.
    apply (JFIEqualValuesAreEquivalent v1 v2).
    ++ apply IH_p_proves_v1_eq_v2.
       exact h_satisfies_p.
       exact gamma_match_env.
    ++ apply IH_p_proves_subst_v1.
       exact h_satisfies_p.
       exact gamma_match_env.
  (* JFIEqReflRule*)
  + apply EqReflexivity.
  (* JFIEqSymRule *)
  + apply EqSymmetry.
    apply IH_p_proves_v1_eq_v2.
    exact h_satisfies_p.
    exact gamma_match_env.
  (* JFIFalseElimRule *)
  + apply FalseElimRuleSoundness.
    apply (IH_p_proves_false h_satisfies_p).
    exact gamma_match_env.
  (* JFITrueIntroRule *)
  + apply TrueIntroRuleSoundness.
  (* JFIAndIntroRule *)
  + apply (AndIntroRuleSoundness r).
    ++ exact (h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_r_proves_p h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_r_proves_q h_satisfies_p env gamma_match_env).
  (* JFIAndElimLRule *)
  + apply (AndElimLRuleSoundness q r).
    ++ exact (h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_r_proves_p_and_q h_satisfies_p env gamma_match_env).
  (* JFIAndElimRRule *)
  + apply (AndElimRRuleSoundness p r).
    ++ exact (h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_r_proves_p_and_q h_satisfies_p env gamma_match_env).
  (* JFIOrIntroLRule *)
  + apply (OrIntroLRuleSoundness r).
    ++ exact (h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_r_proves_p h_satisfies_p env gamma_match_env).
  (* JFIOrIntroRRule *)
  + apply (OrIntroRRuleSoundness r).
    ++ exact (h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_r_proves_q h_satisfies_p env gamma_match_env).
  (* JFIOrElimRule *)
  + (* apply (OrElimRuleSoundness p q s).
    ++ exact (h_satisfies_p env gamma_match_env).
    ++ intros _.
       exact (IH_s_proves_p_or_q h_satisfies_p env gamma_match_env).
    ++ intros h_satisfies_s_and_p.
       exact (IH_s_and_p_proves_r h_satisfies_ env gamma_match_env).
    ++ intros _.
       exact (IH_s_and_q_proves_r h_satisfies_p env gamma_match_env). *) admit.
  (* JFIImpliesIntroRule *)
  + (* apply (ImpliesIntroRuleSoundness r).
    ++ exact h_satisfies_p.
    ++ intros h_satisfies_r.
       exact (IH_r_and_p_proves_q h_satisfies_r gamma_match_env). *) admit.
  (* JFIImpliesElimRule *)
  + (* apply (ImpliesElimRuleSoundness p r).
    ++ exact h_satisfies_p.
    ++ intros h_satisfies_r.
       exact (IH_r_proves_p_implies_r h_satisfies_r gamma_match_env).
    ++ intros h_satisfies_r.
       exact (IH_r_proves_p h_satisfies_r gamma_match_env). *) admit.
  (* JFIForallIntroRule *)
  + apply ForallIntroRuleSoundndess with (q := q) (gamma := gamma) (gamma_x := gamma_x).
    ++ exact x_fresh_in_q.
    ++ exact gamma_add_new_x.
    ++ exact h_satisfies_p.
    ++ exact IH_q_with_x_proves_p.
    ++ exact gamma_match_env. 
  (* JFIForallElimRule *)
  + admit. (* TODO *)
  (* JFIExistsIntroRule *)
  + admit. (* TODO *)
  (* JFIExistsElimRule <=================================================== dzisiaj*)
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
  + admit. (* TODO *)
  (* JFIHTTrueRule: *)
  + admit. (* TODO *)
  (* JFIHTRetRule *)
  + admit. (* TODO *)
  (* JFIHTCsqRule: *)
  + admit. (* TODO *)
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
  + admit. (* TODO *)
  (* JFIHTLetRule *)
  + admit. (* TODO *)
  (* JFIHTFieldAssignRule *)
  + admit. (* TODO *)
  (* JFIHTIfRule *)
  + admit. (* TODO *)
  (* JFIHTInvokeRetRule *)
  + admit. (* TODO *)
  (* JFIHTInvokeNoRetRule *)
  + admit. (* TODO *)
Admitted.

