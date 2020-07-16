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
Require Import JaIrisPermutation.
Require Import JaEval.
Require Import JaIris.
Require Import JaSubtype.
Require Import Bool.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.


Module HeapFacts := JaIrisCommon.HeapFacts.
Module StrMapFacts := JaIrisCommon.StrMapFacts.
Module NatMapFacts := JaIrisCommon.NatMapFacts.
Module JFXIdMapFacts := Facts JFXIdMap.

Definition JFISemanticallyImplies (gamma : JFITypeEnv) (s : JFITerm) (p : JFITerm) (CC : JFProgram) :=
  forall env this h,
    (JFIGammaMatchEnv h gamma env) ->
    (JFIHeapSatisfiesInEnv h s env this CC) ->
     JFIHeapSatisfiesInEnv h p env this CC.

Definition JFISemanticallyImpliesOuter (gamma : JFITypeEnv) (s : JFIOuterTerm) (p : JFIOuterTerm) (CC : JFProgram) :=
  forall env this h,
    (JFIGammaMatchEnv h gamma env) ->
    (JFIHeapSatisfiesOuterInEnv h s env this CC) ->
     JFIHeapSatisfiesOuterInEnv h p env this CC.

Ltac unfoldSubstitutions :=
  unfold JFITermSubstituteVals;
  unfold JFITermSubstituteVar;
  unfold JFITermSubstituteVal;
  unfold JFIExprSubstituteVar;
  unfold JFIValSubstituteVal;
  unfold JFIStringSubstitute;
  simpl.

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


(* Framework for heap satisfying equivalence lemmas *)

Definition HeapEnvEquivalent h h' env env' this this' t CC :=
  JFIHeapSatisfiesInEnv h t env this CC <-> JFIHeapSatisfiesInEnv h' t env' this' CC.

Definition HeapEnvEquivalentOuter h h' env env' this this' t CC :=
  JFIHeapSatisfiesOuterInEnv h t env this CC <-> JFIHeapSatisfiesOuterInEnv h' t env' this' CC.

Lemma TrueEquivalence : forall h h' env env' this this' CC,
  HeapEnvEquivalent h h' env env' this this' JFITrue CC.
Proof.
  intros.
  easy.
Qed.
Hint Resolve TrueEquivalence : core.

Lemma FalseEquivalence : forall h h' env env' this this' CC,
  HeapEnvEquivalent h h' env env' this this' JFIFalse CC.
Proof.
  intros.
  easy.
Qed.
Hint Resolve FalseEquivalence : core.

Lemma AndPreservesEquivalence : forall h h' env env' this this' t1 t2 CC,
  HeapEnvEquivalent h h' env env' this this' t1 CC ->
  HeapEnvEquivalent h h' env env' this this' t2 CC ->
  HeapEnvEquivalent h h' env env' this this' (JFIAnd t1 t2) CC.
Proof.
  intros h h' env env' this this' t1 t2 CC.
  intros t1_equivalence t2_equivalence.
  unfold HeapEnvEquivalent in *.
  split; intro; split; destruct H.
  + now apply t1_equivalence.
  + now apply t2_equivalence.
  + now apply t1_equivalence.
  + now apply t2_equivalence.
Qed.
Hint Resolve AndPreservesEquivalence : core.

Lemma OrPreservesEquivalence : forall h h' env env' this this' t1 t2 CC,
  HeapEnvEquivalent h h' env env' this this' t1 CC ->
  HeapEnvEquivalent h h' env env' this this' t2 CC ->
  HeapEnvEquivalent h h' env env' this this' (JFIOr t1 t2) CC.
Proof.
  intros h h' env env' this this' t1 t2 CC.
  intros t1_equivalence t2_equivalence.
  unfold HeapEnvEquivalent in *.
  split; intro; simpl; destruct H.
  + apply or_introl; now apply t1_equivalence.
  + apply or_intror; now apply t2_equivalence.
  + apply or_introl; now apply t1_equivalence.
  + apply or_intror; now apply t2_equivalence.
Qed.
Hint Resolve OrPreservesEquivalence : core.

Lemma ImpliesPreservesEquivalence : forall h h' env env' this this' t1 t2 CC,
  HeapEnvEquivalent h h' env env' this this' t1 CC ->
  HeapEnvEquivalent h h' env env' this this' t2 CC ->
  HeapEnvEquivalent h h' env env' this this' (JFIImplies t1 t2) CC.
Proof.
  intros h h' env env' this this' t1 t2 CC.
  intros t1_equivalence t2_equivalence.
  unfold HeapEnvEquivalent in *.
  split; intro; simpl; destruct H.
  + apply or_introl. intro. apply H. now apply t1_equivalence.
  + apply or_intror; now apply t2_equivalence.
  + apply or_introl. intro. apply H. now apply t1_equivalence.
  + apply or_intror; now apply t2_equivalence.
Qed.
Hint Resolve ImpliesPreservesEquivalence : core.

(* =============== Env Lemmas =============== *)

Lemma DifferentVarIsFresh : forall v w,
  (w <> JFIVar v) -> JFIVarFreshInVal v w.
Proof.
  intros v w.
  intros w_is_not_v.
  unfold JFIVarFreshInVal.
  destruct w; try trivial.
  unfold not.
  intros v_eq_x.
  apply f_equal with (f := fun x => JFIVar x) in v_eq_x.
  symmetry in v_eq_x.
  exact (w_is_not_v v_eq_x).
Qed.

Lemma AddingFreshVarPreservesValToLoc : forall x l val env this,
  (JFIVarFreshInVal x val) ->
   JFIValToLoc val env this = JFIValToLoc val (StrMap.add x l env) this.
Proof.
  intros x l val env this.
  intros x_fresh.
  unfold JFIValToLoc.
  destruct val as [ |  | loc]; trivial.
  + symmetry.
    apply StrMapFacts.add_neq_o.
    unfold JFIVarFreshInVal in x_fresh.
    exact x_fresh.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfyingEq : forall val1 val2 x l env this h CC,
  (JFIVarFreshInTerm x (JFIEq val1 val2)) ->
    ((JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env this CC) <->
      JFIHeapSatisfiesInEnv h (JFIEq val1 val2) (StrMap.add x l env) this CC).
Proof.
  intros val1 val2 x l env this h CC.
  intros x_fresh.
  split.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    replace (JFIValToLoc val1 (StrMap.add x l env) this) with (JFIValToLoc val1 env this).
    replace (JFIValToLoc val2 (StrMap.add x l env) this) with (JFIValToLoc val2 env this).
    ++ exact h_satisfies_eq.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh.
    ++ apply AddingFreshVarPreservesValToLoc.
       apply x_fresh.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    now rewrite <-2!AddingFreshVarPreservesValToLoc with (x := x) (l := l) in h_satisfies_eq; try apply x_fresh.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfyingFieldEq : forall obj field val x l env this h CC,
  (JFIVarFreshInTerm x (JFIFieldEq obj field val)) ->
    ((JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env this CC) <->
      JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) (StrMap.add x l env) this CC).
Proof.
  intros obj field val x l env this h CC.
  intros (x_fresh_in_obj & x_fresh_in_val).
  split.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    now rewrite <-2!AddingFreshVarPreservesValToLoc.
  + intros h_satisfies_eq.
    simpl.
    simpl in h_satisfies_eq.
    now rewrite <-2!AddingFreshVarPreservesValToLoc in h_satisfies_eq.
Qed.

Definition EnvEq (env1 : JFITermEnv) (env2 : JFITermEnv) := 
  forall x, StrMap.find x env1 = StrMap.find x env2.

Definition EqualEnvsEquivalentInTermForHeap (t : JFITerm) CC :=
  forall h env1 env2 this, 
    (EnvEq env1 env2) -> ((JFIHeapSatisfiesInEnv h t env1 this CC) <-> (JFIHeapSatisfiesInEnv h t env2 this CC)).

Definition EqualEnvsEquivalentInOuterTermForHeap (t : JFIOuterTerm) CC :=
  forall h env1 env2 this, 
    (EnvEq env1 env2) -> ((JFIHeapSatisfiesOuterInEnv h t env1 this CC) <-> (JFIHeapSatisfiesOuterInEnv h t env2 this CC)).

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

Lemma EnvEqGivesValSubstEnvEq : forall env1 env2 this v,
  (EnvEq env1 env2) ->
  (JFIValSubstituteEnv env1 this v = JFIValSubstituteEnv env2 this v).
Proof.
  intros env1 env2 this v.
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
  + now rewrite 2!ValEnvSubstitutionSubstitutesThis.
Qed.

Lemma EnvEqGivesMapValSubstEq : forall env1 env2 this vs,
  (EnvEq env1 env2) ->
  (map (JFIValSubstituteEnv env1 this) vs = map (JFIValSubstituteEnv env2 this) vs).
Proof.
  intros env1 env2 this vs.
  intros env_eq.
  induction vs; try trivial.
  rewrite 2!List.map_cons.
  rewrite IHvs.
  rewrite EnvEqGivesValSubstEnvEq with (env2 := env2); trivial.
Qed.

Lemma EnvEqGivesExprSubstEnvEq : forall e env1 env2 this,
  (EnvEq env1 env2) ->
  (JFIExprSubstituteEnv env1 this e =  JFIExprSubstituteEnv env2 this e).
Proof.
  intros e.
  induction e; intros env1 env2 this env_eq; simpl;
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

Lemma EnvEqGivesEvalEq : forall confs h e hn ex res env1 env2 this CC,
  (EnvEq env1 env2) ->
  (JFIEvalInEnv h e confs hn ex res env1 this CC) ->
  (JFIEvalInEnv h e confs hn ex res env2 this CC).
Proof.
  intros confs.
  induction confs; intros h e hn ex res env1 env2 this CC env_eq.
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

Lemma EnvEqGivesExistsImplication : forall h type x t env1 env2 this CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInOuterTermForHeap t CC) ->
  (JFIHeapSatisfiesOuterInEnv h (JFIExists type x t) env1 this CC) ->
   JFIHeapSatisfiesOuterInEnv h (JFIExists type x t) env2 this CC.
Proof.
  intros h type x t env1 env2 this CC.
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

Lemma EnvEqGivesHoareImplication : forall h t1 e ex v t2 env1 env2 this CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIHoare t1 e ex v t2) env1 this CC) ->
   JFIHeapSatisfiesInEnv h (JFIHoare t1 e ex v t2) env2 this CC.
Proof.
  intros h t1 e ex v t2 env1 env2 this CC.
  intros env_eq t1_equivalence t2_equivalence.
  simpl.
  intros h_satisfies_hoare h_satisfies_t1.
  assert (h_satisfies_t1_in_env1 := proj2 (t1_equivalence h env1 env2 this env_eq) h_satisfies_t1).
  destruct (h_satisfies_hoare h_satisfies_t1_in_env1) as
    (confs & hn & res_ex & res & eval & ex_eq & hn_satisfies_t2).
  exists confs, hn, res_ex, res.
  split; try split; try easy.
  + now apply EnvEqGivesEvalEq with (env1 := env1).
  + apply (t2_equivalence hn (StrMap.add v res env1) (StrMap.add v res env2)); try assumption.
    now apply AddPreservesEnvEq.
Qed.

Lemma EnvEqGivesEqualValToLoc : forall val env1 env2 this,
  (EnvEq env1 env2) ->
  (JFIValToLoc val env1 this) = (JFIValToLoc val env2 this).
Proof.
  unfold JFIValToLoc.
  now destruct val.
Qed.

Lemma EnvEqGivesEqImplication : forall h env1 env2 this val1 val2 CC,
  (EnvEq env1 env2) ->
  (JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env1 this CC) ->
   JFIHeapSatisfiesInEnv h (JFIEq val1 val2) env2 this CC.
Proof.
  intros h env1 env2 this val1 val2 CC.
  intros env_eq.
  apply EnvEqSymmetry in env_eq.
  simpl.
  now rewrite EnvEqGivesEqualValToLoc with (val := val1) (env2 := env2),
              EnvEqGivesEqualValToLoc with (val := val2) (env2 := env2).
Qed.

Lemma EnvEqGivesFieldEqImplication : forall h env1 env2 this obj field val CC,
  (EnvEq env1 env2) ->
  (JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env1 this CC) ->
   JFIHeapSatisfiesInEnv h (JFIFieldEq obj field val) env2 this CC.
Proof.
  intros h env1 env2 this obj field val CC.
  intros env_eq.
  apply EnvEqSymmetry in env_eq.
  simpl.
  now rewrite EnvEqGivesEqualValToLoc with (val := obj) (env2 := env2),
              EnvEqGivesEqualValToLoc with (val := val) (env2 := env2).
Qed.

Lemma EnvEqGivesSepImplication : forall h t1 t2 env1 env2 this CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFISep t1 t2) env1 this CC) ->
   JFIHeapSatisfiesInEnv h (JFISep t1 t2) env2 this CC.
Proof.
  intros h t1 t2 env1 env2 this CC.
  intros env_eq t1_equivalence t2_equivalence.
  simpl.
  intros (h1 & (h2 & (disjoint_unions & (h1_satisfies_t1 & h2_satisfies_t2)))).
  exists h1, h2.
  split.
  + exact disjoint_unions.
  + split.
    now apply (t1_equivalence h1 env1 env2).
    now apply (t2_equivalence h2 env1 env2).
Qed.

Lemma EnvEqGivesWandImplication : forall h t1 t2 env1 env2 this CC,
  (EnvEq env1 env2) ->
  (EqualEnvsEquivalentInTermForHeap t1 CC) ->
  (EqualEnvsEquivalentInTermForHeap t2 CC) ->
  (JFIHeapSatisfiesInEnv h (JFIWand t1 t2) env1 this CC) ->
   JFIHeapSatisfiesInEnv h (JFIWand t1 t2) env2 this CC.
Proof.
  intros h t1 t2 env1 env2 this CC.
  intros env_eq t1_equivalence t2_equivalence.
  simpl.
  intros wand h' disjoint_h_h' h'_satisfies_t1.
  unfold EqualEnvsEquivalentInTermForHeap in t1_equivalence.
  apply (t1_equivalence h' env1 env2 this env_eq) in h'_satisfies_t1.
  destruct (wand h' disjoint_h_h' h'_satisfies_t1) as (h_h' & union_h_h' & h_h'_satisfies_t2).
  apply (t2_equivalence h_h' env1 env2 this env_eq) in h_h'_satisfies_t2.
  now exists h_h'.
Qed.

Lemma EqualEnvsAreEquivalent : forall t CC h env1 env2 this,
  (EnvEq env1 env2) -> HeapEnvEquivalent h h env1 env2 this this t CC.
Proof.
  intros t CC.
  induction t; intros h env1 env2 this env1_eq_env2; auto.
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

Lemma EnvOrderChangePreservesHeapSatisfying : forall h t x1 l1 x2 l2 env this CC,
  (x1 <> x2) ->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x1 l1 (StrMap.add x2 l2 env)) this CC) <->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x2 l2 (StrMap.add x1 l1 env)) this CC).
Proof.
  intros h t x1 l1 x2 l2 env this CC.
  intros x1_neq_x2.
  apply EqualEnvsAreEquivalent.
  apply AddOrderChangePreservesEnvEq.
  apply neq_symmetry.
  exact x1_neq_x2.
Qed.

Lemma FreshEnvOrderChangePreservesHeapSatisfying : forall h t x1 l1 x2 l2 env this CC,
  (JFIVarFreshInTerm x1 t) ->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x1 l1 (StrMap.add x2 l2 env)) this CC) <->
  (JFIHeapSatisfiesInEnv h t (StrMap.add x2 l2 (StrMap.add x1 l1 env)) this CC).
Proof.
Admitted.

Definition FreshVarPreservesTermSatysfying t CC :=
forall h x l env this,
        JFIVarFreshInTerm x t ->
        JFIHeapSatisfiesInEnv h t env this CC <->
        JFIHeapSatisfiesInEnv h t (StrMap.add x l env) this CC.

Lemma FreshVarPreservesEval : forall h e confs hn ex res x l env this CC,
  JFIVarFreshInExpr x e ->
  JFIEvalInEnv h e confs hn ex res env this CC <->
  JFIEvalInEnv h e confs hn ex res (StrMap.add x l env) this CC.
Proof.
Admitted.

Lemma FreshVarPreservesHoareSatystying : forall t1 e ex v t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFIHoare t1 e ex v t2) CC.
Proof.
  intros t1 e ex v t2 CC.
  intros IH_t1 IH_t2.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env this x_fresh_in_hoare.
  simpl in x_fresh_in_hoare.
  destruct (String.eqb v x); destruct x_fresh_in_hoare.
  destruct H0 as (x_fresh_in_t2 & x_fresh_in_e).
  assert (t1_preserves := IH_t1 h x l env this H).
  simpl.
  split.
  + intros h_satisfies_hoare_in_env.
    intros h_satisfies_t1.
    apply t1_preserves in h_satisfies_t1.
    destruct (h_satisfies_hoare_in_env h_satisfies_t1)
      as (confs & hn & res_ex & res & eval & ex_eq & hn_satisfies_t2).
    exists confs, hn, res_ex, res.
    assert (t2_preserves := IH_t2 hn x l (StrMap.add v res env) this x_fresh_in_t2).
    split; try split; try easy.
    ++ now apply FreshVarPreservesEval.
    ++ apply FreshEnvOrderChangePreservesHeapSatisfying with (x1 := x); try assumption.
       now apply t2_preserves.
  + intros h_satisfies_hoare_in_env.
    intros h_satisfies_t1.
    apply t1_preserves in h_satisfies_t1.
    destruct (h_satisfies_hoare_in_env h_satisfies_t1)
      as (confs & hn & res_ex & res & eval & ex_eq & hn_satisfies_t2).
    exists confs, hn, res_ex, res.
    assert (t2_preserves := IH_t2 hn x l (StrMap.add v res env) this x_fresh_in_t2).
    split; try split; try easy.
    ++ now apply FreshVarPreservesEval in eval.
    ++ apply t2_preserves.
       now apply FreshEnvOrderChangePreservesHeapSatisfying.
Qed.

Lemma FreshVarPreservesSepSatystying : forall t1 t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFISep t1 t2) CC.
Proof.
  intros t1 t2 CC.
  intros t1_preserves t2_preserves.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env this (x_fresh_in_t1 & x_fresh_in_t2).
  split.
  + simpl.
    intros (h1 & h2 & disjoint_union & h1_satisfies_t1 & h2_satisfies_t2).
    assert (h1_satisfies_t1_in_env_x := proj1 (t1_preserves h1 x l env this x_fresh_in_t1) h1_satisfies_t1).
    assert (h2_satisfies_t2_in_env_x := proj1 (t2_preserves h2 x l env this x_fresh_in_t2) h2_satisfies_t2).
    now exists h1, h2.
  + simpl.
    intros (h1 & h2 & disjoint_union & h1_satisfies_t1 & h2_satisfies_t2).
    assert (h1_satisfies_t1_in_env := proj2 (t1_preserves h1 x l env this x_fresh_in_t1) h1_satisfies_t1).
    assert (h2_satisfies_t2_in_env := proj2 (t2_preserves h2 x l env this x_fresh_in_t2) h2_satisfies_t2).
    now exists h1, h2.
Qed.

Lemma FreshVarPreservesWandSatystying : forall t1 t2 CC,
  FreshVarPreservesTermSatysfying t1 CC ->
  FreshVarPreservesTermSatysfying t2 CC ->
  FreshVarPreservesTermSatysfying (JFIWand t1 t2) CC.
Proof.
  intros t1 t2 CC.
  intros t1_preserves t2_preserves.
  unfold FreshVarPreservesTermSatysfying.
  intros h x l env this (x_fresh_in_t1 & x_fresh_in_t2).
  split.
  + intros h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1.
    apply t1_preserves in h'_satisfies_t1; try assumption.
    destruct (h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1) as (h_h' & h_h'_union & h_h'_satisfies_t2).
    exists h_h'.
    unfold FreshVarPreservesTermSatysfying in t2_preserves.
    now apply t2_preserves with (x := x) (l := l) in h_h'_satisfies_t2; try assumption.
  + intros h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1.
    apply t1_preserves with (x := x) (l := l) in h'_satisfies_t1; try assumption.
    destruct (h_satisfies_wand h' h_h'_disjoint h'_satisfies_t1) as (h_h' & h_h'_union & h_h'_satisfies_t2).
    exists h_h'.
    unfold FreshVarPreservesTermSatysfying in t2_preserves.
    now apply t2_preserves with (x := x) (l := l) in h_h'_satisfies_t2; try assumption.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfying : forall q CC h x l env this,
  JFIVarFreshInTerm x q ->
  HeapEnvEquivalent h h env (StrMap.add x l env) this this q CC.
Proof.
  intros t CC.
  induction t; intros h x l env this x_fresh; try destruct x_fresh; auto.
  (* JFIHoare *)
  + apply FreshVarPreservesHoareSatystying; assumption.
  (* JFIEq *)
  + split;
    now apply AddingFreshVarPreservesHeapSatisfyingEq with (x := x) (l := l).
  (* JFIFieldEq *)
  + split;
    apply AddingFreshVarPreservesHeapSatisfyingFieldEq with (x := x) (l := l);
    exact (conj H H0).
  (* JFISep*)
  + now apply FreshVarPreservesSepSatystying.
  (* JFIWand *)
  + now apply FreshVarPreservesWandSatystying.
Qed.

Lemma AddingFreshVarPreservesHeapSatisfyingOuter : forall q CC h x l env this,
  JFIVarFreshInOuterTerm x q ->
  HeapEnvEquivalentOuter h h env (StrMap.add x l env) this this q CC.
Proof.
Admitted.

Lemma RemovingFreshVarPreservesHeapSatisfyig : forall h p x l env this CC x0,
  (JFIVarFreshInTerm x0 p) ->
  (JFIHeapSatisfiesInEnv h p (StrMap.add x l env) this CC) ->
   JFIHeapSatisfiesInEnv h p (StrMap.add x l (StrMap.remove (elt:=Loc) x0 env)) this CC.
Proof.
Admitted.

Lemma VarNameChangePreservesHeapSatisfying : forall h t u v l env this CC,
  (JFIHeapSatisfiesInEnv h t (StrMap.add v l env) this CC) <->
   JFIHeapSatisfiesInEnv h (JFITermSubstituteVar v u t) (StrMap.add u l env) this CC.
Proof.
Admitted.

Lemma HeapSatisfiesSubstIffVarMovedToEnv : forall h x v l p env this CC,
  (StrMap.find v env = Some l) ->
  (JFIHeapSatisfiesOuterInEnv h (JFIOuterTermSubstituteVal x (JFIVar v) p) env this CC <->
   JFIHeapSatisfiesOuterInEnv h p (StrMap.add x l env) this CC).
Proof.
Admitted.

Lemma HeapSatisfiesSubstIffThisMovedToEnv : forall h p x env this CC,
  JFIHeapSatisfiesOuterInEnv h (JFIOuterTermSubstituteVal x JFIThis p) env this CC <->
  JFIHeapSatisfiesOuterInEnv h p (StrMap.add x (JFLoc this) env) this CC.
Proof.
Admitted.

(* =============== Equality Lemmas =============== *)

Lemma EqSymmetry : forall h v1 v2 env this CC,
  (JFIHeapSatisfiesInEnv h (JFIEq v1 v2) env this CC) -> 
   JFIHeapSatisfiesInEnv h (JFIEq v2 v1) env this CC.
Proof.
  intros h v1 v2 env this CC.
  intros v1_eq_v2.
  unfold JFIHeapSatisfiesInEnv.
  unfold JFIHeapSatisfiesInEnv in v1_eq_v2.
  now destruct (JFIValToLoc v1 env), (JFIValToLoc v2 env).
Qed.

(* =============== Soundness of basic logical rules =============== *)

Lemma AsmRuleSoundness : forall gamma p CC,
  JFISemanticallyImplies gamma p p CC.
Proof.
  intros gamma p CC.
  intros env this h gamma_match_env h_satisfies_p.
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
  intros env this h gamma_match_env h_satisfies_p.
  apply (q_implies_r env this h gamma_match_env).
  apply (p_implies_q env this h gamma_match_env).
  exact h_satisfies_p.
Qed.

Lemma EqReflRuleSoundness : forall gamma p v CC,
  JFISemanticallyImplies gamma p (JFIEq v v) CC.
Proof.
  intros gamma p v CC.
  intros env this h gamma_match_env h_satisfies_p.
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
  intros env this h gamma_match_env h_satisfies_p.
  apply EqSymmetry.
  apply (v1_eq_v2 env this h).
  + exact gamma_match_env.
  + exact h_satisfies_p.
Qed.

Lemma FalseElimRuleSoundness : forall gamma p q CC,
  (JFISemanticallyImplies gamma p JFIFalse CC) ->
   JFISemanticallyImplies gamma p q CC.
Proof.
  intros gamma p q CC.
  intros p_implies_false.
  intros env this h gamma_match_env h_satisfies_p.
  set (h_satisfies_false := p_implies_false env this h gamma_match_env h_satisfies_p).
  simpl in h_satisfies_false.
  destruct h_satisfies_false.
Qed.

Lemma TrueIntroRuleSoundness : forall gamma p CC,
  JFISemanticallyImplies gamma p JFITrue CC.
Proof.
  intros gamma p CC.
  intros env this h gamma_match_env h_satisfies_p.
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
  intros env this h gamma_match_env h_satisfies_r.
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
  intros env this h gamma_match_env h_satisfies_r;
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
  intros [r_implies_p | r_implies_q]; intros env this h gamma_match_env h_satisfies_r; simpl.
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
  intros env this h gamma_match_env h_satisfies_s.
  set (p_or_q := s_implies_p_or_q env this h gamma_match_env h_satisfies_s).
  destruct p_or_q as [h_satisfies_p | h_satisfies_q].
  + apply (s_and_p_implies_r env this h gamma_match_env).
    simpl.
    exact (conj h_satisfies_s h_satisfies_p).
  + apply (s_and_q_implies_r env this h gamma_match_env).
    simpl.
    exact (conj h_satisfies_s h_satisfies_q).
Qed.

Lemma ImpliesIntroRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImplies gamma (JFIAnd r p) q CC) ->
   JFISemanticallyImplies gamma r (JFIImplies p q) CC.
Proof.
  intros gamma p q r CC.
  intros r_and_p_implies_q.
  intros env this h gamma_match_env h_satisfies_r.
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
  intros env this h gamma_match_env h_satisfies_r.
  apply (Classical_Prop.or_to_imply (JFIHeapSatisfiesInEnv h p env this CC)).
  + apply r_implies_p_implies_q.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
  + apply r_implies_p.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
Qed.

(* =============== Separation rules soundness ===============*)

Lemma EqualHeapsAreEquivalent : forall t CC h1 h2 env this,
  (HeapEq h1 h2) ->
    ((JFIHeapSatisfiesInEnv h1 t env this CC) <-> (JFIHeapSatisfiesInEnv h2 t env this CC)).
Proof.
Admitted.

Lemma InSuperheap : forall h1 h2 l,
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
           now apply (InSuperheap h1 h12 l).
       +++ destruct (H6 l l_in_h23) as [l_in_h2 | l_in_h3].
           - apply or_introl.
             now apply (InSuperheap h2 h12 l).
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
             now apply (InSuperheap h2 h23 l).
       +++ apply or_intror.
           now apply (InSuperheap h3 h23 l).
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

Definition EnvRestrictedToHeap (env : JFITermEnv) (h' : Heap)  (env' : JFITermEnv):=
  (forall x, StrMap.In x env <-> StrMap.In x env') /\
  (forall x l, StrMap.MapsTo x (JFLoc l) env' -> Heap.In l h') /\
  (forall x l, StrMap.MapsTo x (JFLoc l) env' -> StrMap.MapsTo x (JFLoc l) env).

Definition RestrictEnv (env : JFITermEnv) (h' : Heap) :=
  StrMap.map (fun l =>
    match l with
    | null => null
    | JFLoc n => if Heap.mem n h' then l else null
    end
  ) env.

Lemma ExistsRestrictedEnv : forall env h', exists env', EnvRestrictedToHeap env h' env'.
Proof.
  intros env h'.
  exists (RestrictEnv env h').
  unfold EnvRestrictedToHeap, RestrictEnv.
  split; [ | split].
  + intros x.
    split;
    apply StrMapFacts.map_in_iff with (x := x) (m := env).
  + intros x n.
    intros x_mapsto_n.
    apply StrMapFacts.map_mapsto_iff in x_mapsto_n.
    destruct x_mapsto_n as (l & match_is_loc & x_mapsto_l).
    apply HeapFacts.mem_in_iff.
    destruct l; try discriminate match_is_loc.
    assert (n_eq_n0 : n = n0).
    ++ destruct (Heap.mem (elt:=Obj) n0 h'); try discriminate match_is_loc.
       now injection match_is_loc as n_eq_n0.
    ++ rewrite <-n_eq_n0 in *.
       now destruct (Heap.mem (elt:=Obj) n h'); try discriminate match_is_loc.
  + intros x n x_n_env'.
    apply StrMapFacts.map_mapsto_iff in x_n_env'.
    destruct x_n_env' as (l & match_is_loc & x_mapsto_l).
    destruct l; try discriminate match_is_loc.
    destruct (Heap.mem n0 h'); try discriminate match_is_loc.
    injection match_is_loc as n_eq_n0.
    now rewrite n_eq_n0.
Qed.

Lemma RestrictedEnvMatchesGamma : forall gamma env h env' h',
  JFIGammaMatchEnv h gamma env ->
  JFISubheap h' h ->
  EnvRestrictedToHeap env h' env' ->
  JFIGammaMatchEnv h' gamma env'.
Proof.
  intros gamma env h env' h'.
  intros gamma_match_env subheap_h'_h env'_restricted.
  intros x.
  split; try split.
  + intros x_in_gamma.
    apply env'_restricted.
    now apply gamma_match_env.
  + intros x_in_env'.
    apply env'_restricted in x_in_env'.
    now apply gamma_match_env.
  + intros loc type.
    intros t_type_gamma x_loc_env'.
    destruct env'_restricted as (same_vars & env'_match_h' & env'_subenv).
    destruct loc; try easy.
    assert (n_of_type := proj2 (gamma_match_env x) (JFLoc n) type t_type_gamma (env'_subenv x n x_loc_env')).
    apply env'_match_h' in x_loc_env'.
    simpl.
    simpl in n_of_type.
    apply HeapFacts.elements_in_iff in x_loc_env'.
    destruct x_loc_env' as (o & l_o_h').
    apply HeapFacts.elements_mapsto_iff in l_o_h'.
    assert (l_o_h := l_o_h').
    apply subheap_h'_h in l_o_h.
    apply HeapFacts.find_mapsto_iff in l_o_h'.
    apply HeapFacts.find_mapsto_iff in l_o_h.
    rewrite l_o_h'.
    now rewrite l_o_h in n_of_type.
Qed.

Lemma AddingNullPreservesRestrictedEnv : forall env h env' name,
  EnvRestrictedToHeap env h env' ->
  EnvRestrictedToHeap (StrMap.add name null env) h (StrMap.add name null env').
Proof.
Admitted.

Lemma AddingHeapLocPreservesRestrictedEnv : forall env h env' name n,
  Heap.In n h ->
  EnvRestrictedToHeap env h env' ->
  EnvRestrictedToHeap (StrMap.add name (JFLoc n) env) h (StrMap.add name (JFLoc n) env').
Proof.
Admitted.

Lemma LocOfTypeImpliesLocInHeap : forall n h type,
  JFILocOfType (JFLoc n) h type -> Heap.In n h.
Proof.
Admitted.

Lemma LocOfTypeImpliesExtendedRestricted : forall name l h type env env',
  JFILocOfType l h type ->
  EnvRestrictedToHeap env h env' ->
  EnvRestrictedToHeap (StrMap.add name l env) h (StrMap.add name l env').
Proof.
  intros name l h type env env' env_restricted l_of_type.
  destruct l.
  now apply AddingNullPreservesRestrictedEnv.
  apply AddingHeapLocPreservesRestrictedEnv; try assumption.
  now apply LocOfTypeImpliesLocInHeap with (type := type).
Qed.

Lemma RestrictedEnvPreservesHeapSatisfying : forall p h env env' this CC,
  EnvRestrictedToHeap env h env' ->
  (JFIHeapSatisfiesInEnv h p env this CC <-> JFIHeapSatisfiesInEnv h p env' this CC).
Proof.
  intros p.
  induction p; intros h env env' this CC env_restricted.
  + split; auto.
  + split; auto.
  + split.
    ++ simpl.
       intros (h_satisfies_p1 & h_satisfies_p2).
        split.
        now apply (IHp1 h env).
        now apply (IHp2 h env).
    ++ simpl.
       intros (h_satisfies_p1 & h_satisfies_p2).
        split.
        now apply (IHp1 h env env').
        now apply (IHp2 h env env').
  + split; simpl.
    ++ destruct 1.
       apply or_introl. now apply (IHp1 h env).
       apply or_intror. now apply (IHp2 h env).
    ++ destruct 1.
       apply or_introl. now apply (IHp1 h env env').
       apply or_intror. now apply (IHp2 h env env').
  + split; simpl.
    ++ destruct 1.
       apply or_introl.
       intros h_p1_env.
       apply H. now apply (IHp1 h env env').
       apply or_intror.
       now apply (IHp2 h env env').
    ++ destruct 1.
       apply or_introl.
       intros h_p1_env.
       apply H. now apply (IHp1 h env env').
       apply or_intror.
       now apply (IHp2 h env env'). 
  + admit.
  + split. (* TODO to moze nie zadzialac *)
Admitted.

Lemma EveryHeapSatisfiesPersistentTerm : forall p h h' env this CC,
  JFITermPersistent p ->
  (JFIHeapSatisfiesInEnv h  p env this CC <->
   JFIHeapSatisfiesInEnv h' p env this CC).
Proof.
Admitted.

Lemma SepAssoc1Soundness : forall decls gamma p1 p2 p3,
  JFISemanticallyImplies gamma
    (JFISep p1 (JFISep p2 p3))
    (JFISep (JFISep p1 p2) p3) (JFIDeclsProg decls).
Proof.
  intros decls gamma p1 p2 p3.
  intros env this h gamma_match_env h_satisfies_q.
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
  intros env this h gamma_match_env h_satisfies_q.
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
  intros env this h gamma_match_env h_satisfies_sep.
  destruct h_satisfies_sep as (h1 & h2 & (union_h2_h2 & disjoint_h1_h2) & h_satisfies_p1 & h2_satisfies_p2).
  exists h2, h1.
  split; split; try assumption.
  + apply UnionSymmetry.
    assumption.
  + apply DisjointSymmetry.
    assumption.
Qed.
Hint Resolve SepCommRuleSoundness : core.

Lemma ImplicationToRestrictedImplication : forall gamma env this h h' p q CC,
  JFISubheap h' h ->
  JFIGammaMatchEnv h gamma env ->
  JFISemanticallyImplies gamma p q CC ->
  JFIHeapSatisfiesInEnv h' p env this CC ->
  JFIHeapSatisfiesInEnv h' q env this CC.
Proof.
  intros gamma env this h h' p q CC.
  intros h'_subheap gamma_match_env p_implies_q h'_satisfies_p.
  destruct (ExistsRestrictedEnv env h') as (env' & env'_restricted).
  assert (gamma_match_env' := RestrictedEnvMatchesGamma _ _ _ _ _ gamma_match_env h'_subheap env'_restricted).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env') in h'_satisfies_p; try assumption.
  assert (h'_satisfies_q := p_implies_q env' this h' gamma_match_env' h'_satisfies_p).
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
  intros env this h gamma_match_env h_satisfies_sep.
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
  intros env this h gamma_match_env h_satisfies_and.
  exists (Heap.empty Obj), h.
  split; split; try assumption.
  + apply UnionIdentity.
  + apply JFIEmptyHeapDisjoint.
  + apply EveryHeapSatisfiesPersistentTerm with (h := h); try assumption.
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
  intros env this h gamma_match_env h_satisfies_r.
  intros h' h_disjoint h'_satisfies_p.
  destruct (ExistsUnion h h') as (h_h', union_h_h'); try assumption.
  exists h_h'.
  split; try assumption.
  apply (sep_implies_q env this h_h').
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
  intros env this h gamma_match_env h_satisfies_r.

  simpl in h_satisfies_r.
  destruct h_satisfies_r as (h1 & h2 & (union_h1_h2 & disjoint_h1_h2) & h1_satisfies_r1 & h2_satisfies_r2).

  destruct (ExistsRestrictedEnv env h1) as (env1 & env1_restricted).
  assert (gamma_match_env1 := RestrictedEnvMatchesGamma gamma env h env1 h1 gamma_match_env (proj1 union_h1_h2) env1_restricted).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env1) in h1_satisfies_r1; try assumption.
  unfold JFISemanticallyImplies in r1_implies_wand.
  assert (h1_satisfies_wand := r1_implies_wand env1 this h1 gamma_match_env1 h1_satisfies_r1).
  apply RestrictedEnvPreservesHeapSatisfying with (env := env) in h1_satisfies_wand; try assumption.

  destruct (ExistsRestrictedEnv env h2) as (env2 & env2_restricted).
  assert (gamma_match_env2 := RestrictedEnvMatchesGamma gamma env h env2 h2 gamma_match_env (proj1 (proj2 union_h1_h2)) env2_restricted).
  apply RestrictedEnvPreservesHeapSatisfying with (env' := env2) in h2_satisfies_r2; try assumption.
  assert (h2_satisfies_p := r2_implies_p env2 this h2 gamma_match_env2 h2_satisfies_r2).
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

Lemma IfReductionEq : forall h l1 l2 e1 e2 Ctx Cc env this CC,
  (l1 = l2) ->
   red CC (h, (Ctx[[ JFIExprSubstituteEnv env this (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ]]_ None) :: Cc) = Some (h, Ctx[[JFIExprSubstituteEnv env this e1]]_ None :: Cc).
Proof.
  intros h l1 l2 e1 e2 Ctx Cc env this CC.
  intros l1_eq_l2.
  simpl.
  rewrite ValEnvSubstitutionPreservesVLoc.
  rewrite ValEnvSubstitutionPreservesVLoc.
  Loc_dec_eq l1 l2 l1_eq_l2.
  destruct Ctx.
  trivial.
  destruct j; trivial.
Qed.

Lemma IfReductionNeq : forall h l1 l2 e1 e2 Ctx Cc env this CC,
  (l1 <> l2) ->
   red CC (h, (Ctx[[ JFIExprSubstituteEnv env this (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ]]_ None) :: Cc) = Some (h, Ctx[[JFIExprSubstituteEnv env this e2]]_ None :: Cc).
Proof.
  intros h l1 l2 e1 e2 Ctx Cc env this CC.
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

Lemma IfEvaluationStepEq : forall l1 l2 e1 e2 h h' st' confs hn ex res env this CC,
  (l1 = l2) ->
  (JFIEvalInEnv h (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ((h', st')::confs) hn ex res env this CC) ->
  (h = h' /\ JFIEvalInEnv h' e1 confs hn ex res env this CC).
Proof.
  intros l1 l2 e1 e2 h h' st' confs hn ex res env this CC.
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

Lemma IfEvaluationStepNeq : forall l1 l2 e1 e2 h h' st' confs hn ex res env this CC,
  (l1 <> l2) ->
  (JFIEvalInEnv h (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ((h', st')::confs) hn ex res env this CC) ->
  (h = h' /\ JFIEvalInEnv h' e2 confs hn ex res env this CC).
Proof.
  intros l1 l2 e1 e2 h h' st' confs hn ex res env this CC.
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

Lemma NewEvaluationStep : forall prog h ls newloc newheap mu cn vs env this CC,
  (alloc_init prog h cn ls = Some (newloc, newheap)) ->
   JFIEvalInEnv h (JFNew mu cn vs) [(h, [ [] [[ JFIExprSubstituteEnv env this (JFNew mu cn vs) ]]_ None])] newheap None newloc env this CC.
Proof.
Admitted.

Lemma EvaluationPreservesGammaMatching : forall gamma env h e confs hn ex res CC,
  (JFIGammaMatchEnv h gamma env) ->
  (JFIEval h e confs hn ex res CC) ->
  (JFIGammaMatchEnv hn gamma env).
Proof.
Admitted.

Lemma EvaluationPreservesPersistentTerms : forall env this s h e confs hn ex res CC,
  (JFITermPersistent s) ->
  (JFIHeapSatisfiesInEnv h s env this CC) ->
  (JFIEval h e confs hn ex res CC) ->
   JFIHeapSatisfiesInEnv hn s env this CC.
Proof.
Admitted.

(* =============== Soundness of Hoare triple rules =============== *)

Lemma JFIExistsValToLoc : forall v v_expr env this,
  v_expr = JFIValToJFVal v ->
  exists l, JFIValToLoc v env this = Some l /\ JFIValSubstituteEnv env this v_expr = (JFVLoc l).
Proof.
  intros v v_expr env this v_expr_val.
  destruct v; simpl in v_expr_val; rewrite v_expr_val.
  + exists null.
    split; trivial.
    unfold JFIExprSubstituteEnv.
    now rewrite ValEnvSubstitutionPreservesVLoc.
  + exists (JFLoc this).
    split; try easy.
    admit. (* TODO this val substitute env *)
  + assert (exists l, StrMap.find var env = Some l). admit. (* TODO var in env *)
    destruct H as (l & var_l_env).
    exists l.
    unfold JFIValToLoc.
    now rewrite var_l_env, ValEnvSubstitutionReplacesVarInEnv with (l := l).
Admitted.

Lemma ValToLoc_neq_o : forall x u v env this,
  x <> (JFIVar u) ->
  JFIValToLoc x (StrMap.add u v env) this = JFIValToLoc x env this.
Proof.
  intros.
  destruct x; try easy.
  simpl.
  rewrite StrMapFacts.add_neq_o; trivial.
  intros u_eq_var.
  apply H.
  now rewrite u_eq_var.
Qed.

Lemma EnsureValIsLoc : forall (v : JFVal),
  exists l, v = JFVLoc l.
Proof.
Admitted.

Lemma EnsureVarInEnv : forall x (env : JFITermEnv),
  exists l, StrMap.find x env = Some l.
Proof.
Admitted.

Lemma EnsureValsMapIsLocsMap : forall vs env this,
  exists ls, map (JFIValSubstituteEnv env this) vs = map JFVLoc ls.
Proof.
Admitted.

Lemma EnsureValsListIsLocsList : forall ls vs n l env this,
  map (JFIValSubstituteEnv env this) vs = map JFVLoc ls ->
  (nth_error ls n = Some l <-> nth_error (map (JFIValSubstituteEnv env this) vs) n = Some (JFVLoc l)).
(*   exists ls, forall n l, nth_error ls n = Some l <-> nth_error (map (JFIValSubstituteEnv env) vs) n = Some (JFVLoc l). *)
Proof.
  intros ls vs n l env this.
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

(* Heaps and envs permutation *)

Definition PermutationPreservesSatisfying t :=
  forall h h_perm env env_perm this pi CC,
    HeapsPermuted h h_perm pi ->
    EnvsPermuted env env_perm pi ->
    HeapEnvEquivalent h h_perm env env_perm this this t CC.

Definition PermutationPreservesSatisfyingOuter t :=
  forall h h_perm env env_perm this pi CC,
    HeapsPermuted h h_perm pi ->
    EnvsPermuted env env_perm pi ->
    HeapEnvEquivalentOuter h h_perm env env_perm this this t CC.

Lemma PermutationPreservesExistsSatisfying : forall type x t,
  PermutationPreservesSatisfyingOuter t ->
  PermutationPreservesSatisfyingOuter (JFIExists type x t).
Proof.
  intros type name t IHt h h_perm env env_perm this pi CC pi_h pi_env.
  split.
  + intros (l & l_of_type & h_satisfies_t).
    destruct (PiMapsToSameType h h_perm pi l type pi_h l_of_type)
      as (l_perm & pi_l & l_perm_of_type).
    exists l_perm.
    simpl.
    split; trivial.
    set (env' := StrMap.add name l env).
    set (env_perm' := StrMap.add name l_perm env_perm).
    apply (IHt h h_perm env' env_perm' this pi CC); trivial.
    unfold env', env_perm'.
    now apply ExtendedEnvsPermuted.
  + intros (l_perm & l_perm_of_type & h_satisfies_t).
    destruct (InvertPermutation pi) as (pi' & pi'_heaps & pi'_envs).
    apply pi'_heaps in pi_h.
    apply pi'_envs in pi_env.
    destruct (PiMapsToSameType h_perm h pi' l_perm type pi_h l_perm_of_type)
      as (l & pi_l & l_of_type).
    exists l.
    simpl.
    split; trivial.
    set (env' := StrMap.add name l env).
    set (env_perm' := StrMap.add name l_perm env_perm).
    apply (IHt h_perm h env_perm' env' this pi' CC); trivial.
    unfold env', env_perm'.
    now apply ExtendedEnvsPermuted.
Qed.

Lemma ExistsVarInEnvPerm : forall env env_perm pi var l,
  EnvsPermuted env env_perm pi ->
  StrMap.MapsTo var l env ->
  exists l', StrMap.MapsTo var l' env_perm.
Proof.
  intros env env_perm pi var l.
  intros pi_env env_eq.
  destruct pi_env as (bijection & same_vars & pi_env).
  assert (var_in_env_perm : StrMap.In var env_perm).
  apply same_vars.
  apply StrMapFacts.elements_in_iff.
  exists l.
  now apply StrMapFacts.elements_mapsto_iff.
  apply StrMapFacts.elements_in_iff in var_in_env_perm as (l' & var_l'_env_perm).
  apply StrMapFacts.elements_mapsto_iff in var_l'_env_perm.
  now exists l'.
Qed.

Lemma PermutationPreservesValToLocEq : forall x1 x2 env env_perm this pi,
  EnvsPermuted env env_perm pi ->
  JFIValToLoc x1 env this = JFIValToLoc x2 env this ->
  JFIValToLoc x1 env_perm this = JFIValToLoc x2 env_perm this.
Proof.
  intros x1 x2 env env_perm this pi.
  intros pi_env env_eq.
  unfold JFIValToLoc in *.
  assert (pi_this : PiMapsTo (JFLoc this) (JFLoc this) pi).
    admit. (* TODO this pi mapsto this*)
  assert (pi_env' : forall x l1 l2, PiMapsTo l1 l2 pi -> StrMap.MapsTo x l1 env -> StrMap.MapsTo x l2 env_perm).
    admit. (* TODO this extend permuted envs definition*)
  destruct pi_env as (bijection & same_vars & pi_env).
  destruct x1, x2; try discriminate env_eq; trivial.
  + symmetry in env_eq.
    apply StrMapFacts.find_mapsto_iff in env_eq.
    destruct (ExistsVarInEnvPerm env env_perm pi var null) as (l & var_l_env); try easy.
    assert (l_mapsto := pi_env var null l env_eq var_l_env).
    unfold PiMapsTo in l_mapsto.
    destruct l; try destruct l_mapsto.
    now apply StrMapFacts.find_mapsto_iff in var_l_env.
  + symmetry in env_eq |- *.
    rewrite <-StrMapFacts.find_mapsto_iff in env_eq |- *.
    now apply pi_env' with (l1 := (JFLoc this)).
  + apply StrMapFacts.find_mapsto_iff in env_eq.
    destruct (ExistsVarInEnvPerm env env_perm pi var null) as (l & var_l_env); try easy.
    assert (l_mapsto := pi_env var null l env_eq var_l_env).
    unfold PiMapsTo in l_mapsto.
    destruct l; try destruct l_mapsto.
    now apply StrMapFacts.find_mapsto_iff in var_l_env.
  + rewrite <-StrMapFacts.find_mapsto_iff in env_eq |- *.
    now apply pi_env' with (l1 := (JFLoc this)).
  + destruct (Classical_Prop.classic (exists l0, StrMap.find var0 env = Some l0))
      as [(l & var0_l_env) | ].
    ++ apply StrMapFacts.find_mapsto_iff in var0_l_env.
       destruct (ExistsVarInEnvPerm env env_perm pi var0 l) as (l' & var0_l'_env); try easy.
       assert (l_l' := pi_env var0 l l' var0_l_env var0_l'_env).
       apply StrMapFacts.find_mapsto_iff in var0_l'_env.
       rewrite var0_l'_env.
       apply StrMapFacts.find_mapsto_iff in var0_l_env.
       rewrite var0_l_env in env_eq.
       apply StrMapFacts.find_mapsto_iff in env_eq.
       destruct (ExistsVarInEnvPerm env env_perm pi var l) as (l'' & var_l''_env); try easy.
       assert (l_l'' := pi_env var l l'' env_eq var_l''_env).
       assert (l_eq : l' = l'').
       +++ unfold PiMapsTo in l_l', l_l''.
           destruct l, l', l''; try easy.
           apply NatMapFacts.find_mapsto_iff in l_l'.
           apply NatMapFacts.find_mapsto_iff in l_l''.
           rewrite l_l'' in l_l'.
           injection l_l' as n_eq.
           now rewrite n_eq.
       +++ apply StrMapFacts.find_mapsto_iff in var_l''_env.
           rewrite var_l''_env.
           now rewrite l_eq.
    ++ assert (var0_not_in_env : ~StrMap.In var0 env).
       intros var0_in_env.
       apply H.
       apply StrMapFacts.elements_in_iff in var0_in_env as (l0 & var0_l0_env).
       apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff in var0_l0_env.
       now exists l0.
       assert (var0_not_in_env_perm : ~StrMap.In var0 env_perm).
       intros var0_in_env_perm.
       now apply var0_not_in_env, same_vars.
       apply StrMapFacts.not_find_mapsto_iff in var0_not_in_env_perm.
       rewrite var0_not_in_env_perm.
       apply StrMapFacts.not_find_mapsto_iff in var0_not_in_env.
       rewrite <-env_eq in var0_not_in_env.
       apply StrMapFacts.not_find_mapsto_iff in var0_not_in_env.
       assert (var_not_in_env_perm : ~StrMap.In var env_perm).
       intros var_in_env_perm.
       now apply var0_not_in_env, same_vars.
       now apply StrMapFacts.not_find_mapsto_iff in var_not_in_env_perm.
Admitted.

Lemma PermutationPreservesElements : forall x env env_perm pi,
  EnvsPermuted env env_perm pi ->
  (exists l, StrMap.find x env = Some l) ->
  exists l_perm, StrMap.find x env_perm = Some l_perm.
Proof.
  intros x env env_perm pi pi_env (l & x_l_env).
  destruct pi_env as (bijection & same_vars & pi_env).
  apply StrMapFacts.find_mapsto_iff in x_l_env.
  destruct (ExistsVarInEnvPerm env env_perm pi x l) as (l' & x_l'_env); try easy.
  apply StrMapFacts.find_mapsto_iff in x_l'_env.
  now exists l'.
Qed.

Lemma ExistsInEnvPerm : forall var env env_perm l pi,
  EnvsPermuted env env_perm pi ->
  StrMap.find var env = Some l ->
  (exists l_perm, StrMap.find var env_perm = Some l_perm /\ PiMapsTo l l_perm pi).
Proof.
  intros var env env_perm l pi (bijection & same_vars & pi_env) var_l_env.
  apply StrMapFacts.find_mapsto_iff in var_l_env.
  destruct (ExistsVarInEnvPerm env env_perm pi var l) as (l' & var_l'_env); try easy.
  apply StrMapFacts.find_mapsto_iff in var_l'_env.
  exists l'.
  split; trivial.
  apply StrMapFacts.find_mapsto_iff in var_l'_env.
  now apply pi_env with (x := var).
Qed.

Lemma PermutationEqImplication : forall h h' x1 x2 env env_perm this pi CC,
  EnvsPermuted env env_perm pi ->
  JFIHeapSatisfiesInEnv h (JFIEq x1 x2) env this CC ->
  JFIHeapSatisfiesInEnv h' (JFIEq x1 x2) env_perm this CC.
Proof.
  intros h h' x1 x2 env env_perm this pi CC.
  simpl.
  intros pi_env eq_in_env.
  rewrite <-PermutationPreservesValToLocEq with (x1 := x1) (x2 := x2) (env := env) (pi := pi); trivial.
  + unfold JFIValToLoc in eq_in_env |- *.
    destruct x1; try destruct l; trivial.
    destruct (Classical_Prop.classic (exists l_perm, StrMap.find var env_perm = Some l_perm))
      as [(l_perm & x_l_perm_env) | not_exists_l_perm].
    ++ now rewrite x_l_perm_env.
    ++ exfalso; apply not_exists_l_perm.
       apply PermutationPreservesElements with (env := env) (pi := pi); trivial.
       destruct (StrMap.find var env); try destruct eq_in_env.
       now exists l.
  + destruct (JFIValToLoc x1 env), (JFIValToLoc x2 env); try easy.
    now rewrite eq_in_env.
Qed.

Lemma PermutationPreservesEqSatisfying : forall x1 x2,
  PermutationPreservesSatisfying (JFIEq x1 x2).
Proof.
  intros x1 x2 h h_perm env env_perm this pi CC pi_h pi_env.
  split.
  + now apply PermutationEqImplication with (pi := pi).
  + destruct (InvertPermutation pi) as (pi' & pi'_heaps & pi'_envs).
    apply pi'_envs in pi_env.
    now apply PermutationEqImplication with (pi := pi').
Qed.

Lemma PermFieldEq : forall o o' f v v' h h' pi,
  JFIObjFieldEq o f v h ->
  HeapsPermuted h h' pi ->
  PiMapsTo o o' pi ->
  PiMapsTo v v' pi ->
  JFIObjFieldEq o' f v' h'.
Proof.
  intros o o' f v v' h h' pi.
  intros field_eq pi_h pi_o pi_v.
  unfold JFIObjFieldEq in *.
  destruct o as [ | n], o' as [ | n']; try easy.
  destruct pi_h as (bijection & fst_h & snd_h & objs_h).
  destruct (Classical_Prop.classic (exists o', Heap.find n' h' = Some o'))
    as [(o' & n'_o'_h') | ].
  + rewrite n'_o'_h'.
    destruct o' as (o' & cn').
    unfold LocsPermuted in fst_h.
    assert (n'_in_h' : Heap.In n' h').
      apply HeapFacts.elements_in_iff.
      apply HeapFacts.find_mapsto_iff in n'_o'_h'.
      apply HeapFacts.elements_mapsto_iff in n'_o'_h'.
      now exists (o', cn').
    destruct (snd_h n' n'_in_h') as (n'' & n'_n''_pi & n''_in_h).
    unfold PiMapsTo in pi_o.
    apply bijection in pi_o.
    apply NatMapFacts.find_mapsto_iff in n'_n''_pi.
    apply NatMapFacts.find_mapsto_iff in pi_o.
    unfold NatMap.key in pi_o.
    rewrite n'_n''_pi in pi_o.
    injection pi_o as n_eq.
    rewrite n_eq in *.
    apply NatMapFacts.elements_in_iff in n''_in_h as (o & n_o_h).
    apply NatMapFacts.elements_mapsto_iff in n_o_h.
    apply NatMapFacts.find_mapsto_iff in n_o_h.
    rewrite n_o_h in field_eq.
    destruct o as (o & cn).
    assert (JFXIdMap.find (elt:=Loc) f o = Some v) as f_v_o.
      destruct (JFXIdMap.find (elt:=Loc) f o); try destruct field_eq; trivial.
    unfold ObjsPermuted in *.
    apply NatMapFacts.find_mapsto_iff, bijection in n'_n''_pi as n_n'_pi.
    apply HeapFacts.find_mapsto_iff in n_o_h.
    apply HeapFacts.find_mapsto_iff in n'_o'_h'.
    destruct (objs_h n n' (o, cn) (o', cn')) as (cn_eq & fields_results); trivial.
    destruct (fields_results f) as (o1_fields & o2_fields & fields_map).
    apply JFXIdMapFacts.find_mapsto_iff in f_v_o.
    destruct (o1_fields v f_v_o) as (v'' & f_v''_o').
    apply JFXIdMapFacts.find_mapsto_iff in f_v''_o'.
    rewrite f_v''_o'.
    apply JFXIdMapFacts.find_mapsto_iff in f_v''_o'.
    assert (v_v'' := fields_map v v'' f_v_o f_v''_o').
    unfold PiMapsTo in v_v'', pi_v.
    destruct v, v', v''; try easy.
    apply NatMapFacts.find_mapsto_iff in pi_v.
    apply NatMapFacts.find_mapsto_iff in v_v''.
    rewrite pi_v in v_v''.
    injection v_v'' as n1_eq.
    now rewrite n1_eq.
  + exfalso.
    apply H.
    unfold LocsPermuted in fst_h.
    destruct (Classical_Prop.classic (exists o, Heap.find n h = Some o)) as [(o & n_o_h) | ].
    ++ apply HeapFacts.find_mapsto_iff, HeapFacts.elements_mapsto_iff in n_o_h.
       assert (n_in_h : Heap.In n h).
         apply HeapFacts.elements_in_iff.
         now exists o.
       destruct (fst_h n) as (n'' & n_n''_pi & n''_in_h'); trivial.
       unfold PiMapsTo in pi_o.
       apply NatMapFacts.find_mapsto_iff in n_n''_pi.
       apply NatMapFacts.find_mapsto_iff in pi_o.
       rewrite n_n''_pi in pi_o.
       injection pi_o as n_eq.
       rewrite n_eq in n''_in_h'.
       apply NatMapFacts.elements_in_iff in n''_in_h' as (o' & n'_o'_h').
       apply NatMapFacts.elements_mapsto_iff, NatMapFacts.find_mapsto_iff in n'_o'_h'.
       now exists o'.
    ++ exfalso.
       apply H0.
       destruct (Heap.find (elt:=Obj) n h); try destruct field_eq.
       now exists o.
Qed.

Lemma FieldEqFindObj : forall env env_perm h h_perm var l l_perm f pi,
  EnvsPermuted env env_perm pi ->
  HeapsPermuted h h_perm pi ->
  PiMapsTo l l_perm pi ->
  match StrMap.find var env with
  | Some objLoc => JFIObjFieldEq objLoc f l h
  | None => False
  end ->
  match StrMap.find var env_perm with
  | Some objLoc => JFIObjFieldEq objLoc f l_perm h_perm
  | None => False
  end.
Proof.
  intros env env_perm h h_perm var l l_perm f pi.
  intros pi_env pi_h pi_l env_eq.
  assert (exists o, StrMap.find var env = Some o).
    destruct (StrMap.find var env); try destruct env_eq.
    now exists l0.
  destruct H as (l' & var_l'_env).
  destruct (ExistsInEnvPerm var env env_perm l' pi pi_env var_l'_env) as (l'_perm & var_l'_env_perm & pi_l').
    rewrite var_l'_env_perm.
    rewrite var_l'_env in env_eq.
    now apply PermFieldEq with (o := l') (v := l) (h := h) (pi := pi).
Qed.

Lemma FieldEqFindVal : forall env env_perm h h_perm var o o_perm f pi,
  EnvsPermuted env env_perm pi ->
  HeapsPermuted h h_perm pi ->
  PiMapsTo o o_perm pi ->
  match StrMap.find var env with
  | Some valLoc => JFIObjFieldEq o f valLoc h
  | None => False
  end ->
  match StrMap.find var env_perm with
  | Some valLoc => JFIObjFieldEq o_perm f valLoc h_perm
  | None => False
  end.
Proof.
  intros env env_perm h h_perm var o o_perm f pi.
  intros pi_env pi_h pi_o env_eq.
  assert (exists o, StrMap.find var env = Some o).
    destruct (StrMap.find var env); try destruct env_eq.
    now exists l.
  destruct H as (l & var_l_env).
  destruct (ExistsInEnvPerm var env env_perm l pi pi_env var_l_env) as (l_perm & var_l_env_perm & pi_l).
  rewrite var_l_env_perm.
  rewrite var_l_env in env_eq.
  now apply PermFieldEq with (o := o) (v := l) (h := h) (pi := pi).
Qed.

Lemma PermutationFieldEqImplication : forall h h_perm o f v env env_perm this pi CC,
  EnvsPermuted env env_perm pi ->
  HeapsPermuted h h_perm pi ->
  JFIHeapSatisfiesInEnv h (JFIFieldEq o f v) env this CC ->
  JFIHeapSatisfiesInEnv h_perm (JFIFieldEq o f v) env_perm this CC.
Proof.
  intros h h_perm o f v env env_perm this pi CC.
  intros pi_env pi_h env_eq.
  simpl in *.
  unfold EnvsPermuted in pi_env.
  unfold HeapsPermuted in pi_h.
  unfold JFIValToLoc in *.
  assert (pi_this : PiMapsTo (JFLoc this) (JFLoc this) pi).
    admit. (* TODO this pi mapsto this*)
  destruct o, v; try easy.
  + now apply FieldEqFindVal with (env := env) (h := h) (o := null) (pi := pi).
  + now apply PermFieldEq with (h := h) (o := (JFLoc this)) (v := null) (pi := pi).
  + now apply PermFieldEq with (h := h) (o := (JFLoc this)) (v := (JFLoc this)) (pi := pi); try easy.
  + now apply FieldEqFindVal with (env := env) (h := h) (o := (JFLoc this)) (pi := pi).
  + now apply FieldEqFindObj with (env := env) (h := h) (l := null) (pi := pi).
  + now apply FieldEqFindObj with (env := env) (h := h) (l := (JFLoc this)) (pi := pi).
  + destruct (Classical_Prop.classic (exists l, StrMap.find var env = Some l)) as [ (o & var_o_env) | not_find ].
    ++ destruct (ExistsInEnvPerm var env env_perm o pi pi_env var_o_env) as (o_perm & var_o_env_perm & pi_o).
       rewrite var_o_env_perm.
       rewrite var_o_env in env_eq.
       now apply FieldEqFindVal with (env := env) (h := h) (o := o) (pi := pi).
    ++ exfalso.
       apply not_find.
       destruct (StrMap.find (elt:=Loc) var env).
       now exists l.
       destruct env_eq.
Admitted.

Lemma PermutationPreservesFieldEqSatisfying : forall o f v,
  PermutationPreservesSatisfying (JFIFieldEq o f v).
Proof.
  intros o f v h h_perm env env_perm this pi CC pi_h pi_env.
  split.
  + now apply PermutationFieldEqImplication with (pi := pi).
  + destruct (InvertPermutation pi) as (pi' & pi'_heaps & pi'_envs).
    apply pi'_envs in pi_env.
    apply pi'_heaps in pi_h.
    now apply PermutationFieldEqImplication with (pi := pi').
Qed.

Lemma PermutationSepImplication : forall t1 t2 h h_perm env env_perm this pi CC,
  PermutationPreservesSatisfying t1 ->
  PermutationPreservesSatisfying t2 ->
  HeapsPermuted h h_perm pi ->
  EnvsPermuted env env_perm pi ->
  JFIHeapSatisfiesInEnv h (JFISep t1 t2) env this CC ->
  JFIHeapSatisfiesInEnv h_perm (JFISep t1 t2) env_perm this CC.
Proof.
  intros t1 t2 h h_perm env env_perm this pi CC IH_t1 IH_t2 pi_h pi_env.
  intros sep_in_env.
  assert (pi_correct := proj1 pi_h).
  destruct sep_in_env as (h1 & h2 & disj_union & h1_satisfies_t1 & h2_satisfies_t2).
  assert (covers_h := PermutedHeapCovered h h_perm pi pi_h).
  destruct (proj1 (PermutationCoversUnion h1 h2 h pi (proj1 disj_union)) covers_h).
  destruct (ExistsPermutedHeap h1 pi) as (h1_perm & pi_h1); trivial.
  destruct (ExistsPermutedHeap h2 pi) as (h2_perm & pi_h2); trivial.
  exists h1_perm, h2_perm.
  split.
  now apply DisjointUnionPermuted with (h1 := h1) (h2 := h2) (h := h) (pi := pi).
  split.
  now apply (IH_t1 h1 h1_perm env env_perm this pi CC).
  now apply (IH_t2 h2 h2_perm env env_perm this pi CC).
Qed.

Lemma PermutationPreservesSepSatisfying : forall t1 t2,
  PermutationPreservesSatisfying t1 ->
  PermutationPreservesSatisfying t2 ->
  PermutationPreservesSatisfying (JFISep t1 t2).
Proof.
  intros t1 t2 IH_t1 IH_t2 h h_perm env env_perm this pi CC pi_h pi_env.
  split.
  + now apply PermutationSepImplication with (pi := pi).
  + destruct (InvertPermutation pi) as (pi' & pi'_heaps & pi'_envs).
    apply pi'_envs in pi_env.
    apply pi'_heaps in pi_h.
    now apply PermutationSepImplication with (pi := pi').
Qed.

Lemma PermutationWandImplication : forall t1 t2 h h_perm env env_perm this pi CC,
  PermutationPreservesSatisfying t1 ->
  PermutationPreservesSatisfying t2 ->
  HeapsPermuted h h_perm pi ->
  EnvsPermuted env env_perm pi ->
  JFIHeapSatisfiesInEnv h (JFIWand t1 t2) env this CC ->
  JFIHeapSatisfiesInEnv h_perm (JFIWand t1 t2) env_perm this CC.
Proof.
  intros t1 t2 h h_perm env env_perm this pi CC IH_t1 IH_t2 pi_h pi_env.
  intros wand_in_env.
  assert (bijection := proj1 pi_h).
  intros h'_perm disj_perm h'_satisfies_t1.
  destruct (InvertPermutation pi) as (pi' & pi'_heaps & pi'_envs).
  assert (pi'_h := pi_h).
  apply pi'_heaps in pi'_h.
  destruct (ExistsPermutedHeap h'_perm pi') as (h' & pi_h'); trivial.
  now apply pi'_h.
  apply pi'_heaps in pi'_h.
  admit. (* TODO extend pi' *)
  assert (h_h'_disj : JFIHeapsDisjoint h h').
  now apply DisjointPermuted with (h1 := h_perm) (h2 := h'_perm) (pi := pi').

  simpl in wand_in_env.
  assert (pi'_h' := pi_h').
  apply pi'_heaps in pi_h'.
  assert (pi'_env := pi_env).
  apply pi'_envs in pi'_env.
  apply (IH_t1 h'_perm h' env_perm env this pi' CC) in h'_satisfies_t1; try easy.
  destruct (wand_in_env h' h_h'_disj h'_satisfies_t1) as (h_h' & union_h_h' & h_h'_satisfies_t2).
  assert (covers_h := PermutedHeapCovered h h_perm pi pi_h).
  assert (covers_h' := PermutedHeapCovered h' h'_perm pi pi_h').
  assert (covers_h_h' : PiCoversHeap pi h_h').
  now apply (PermutationCoversUnion h h' h_h' pi union_h_h').
  destruct (ExistsPermutedHeap h_h' pi) as (h_h'_perm & pi_h_h'); trivial.
  exists h_h'_perm.
  split; trivial.
  now apply UnionPermuted with (h1 := h) (h2 := h') (h := h_h') (pi := pi).
  now apply (IH_t2 h_h' h_h'_perm env env_perm this pi CC).
Admitted.

Lemma PermutationPreservesWandSatisfying : forall t1 t2,
  PermutationPreservesSatisfying t1 ->
  PermutationPreservesSatisfying t2 ->
  PermutationPreservesSatisfying (JFIWand t1 t2).
Proof.
  intros t1 t2 IH_t1 IH_t2 h h_perm env env_perm this pi CC pi_h pi_env.
  split.
  + now apply PermutationWandImplication with (pi := pi).
  + destruct (InvertPermutation pi) as (pi' & pi'_heaps & pi'_envs).
    apply pi'_envs in pi_env.
    apply pi'_heaps in pi_h.
    now apply PermutationWandImplication with (pi := pi').
Qed.

Lemma PermutationPreservesHeapSatisfying : forall t,
  PermutationPreservesSatisfying t .
Proof.
  intros t.
  induction t; intros h h_perm env env_perm this pi CC pi_h pi_env; eauto.
  + admit. (* TODO hoare *)
  + now apply PermutationPreservesEqSatisfying with (pi := pi).
  + now apply PermutationPreservesFieldEqSatisfying with (pi := pi).
  + now apply PermutationPreservesSepSatisfying with (pi := pi).
  + now apply PermutationPreservesWandSatisfying with (pi := pi).
Admitted.

Lemma AddingNullPreservesHeapSatisfying : forall h t x env this CC,
  JFIHeapSatisfiesInEnv h t env this CC ->
  JFIHeapSatisfiesInEnv h t (StrMap.add x null env) this CC.
Proof.
Admitted.

Lemma HTFrameRuleSoundness : forall decls gamma s p r e ex v q,
  let CC := JFIDeclsProg decls in
  JFITermPersistent s ->
  JFIVarFreshInTerm v r ->
  JFISemanticallyImplies gamma s (JFIHoare         p    e ex v         q   ) CC ->
  JFISemanticallyImplies gamma s (JFIHoare (JFISep p r) e ex v (JFISep q r)) CC.
Proof.
  intros decls gamma s p r e ex v q CC.
  intros s_persistent v_fresh_in_r hoare_p_e_q.
  intros env this h gamma_match_env h_satisfies_s.
  intros h_satisfies_sep.
  destruct h_satisfies_sep as (hp & hr & union_hp_hr &
    hp_satisfies_p & hr_satisfies_r).
  assert (fake_gamma_match_env : JFIGammaMatchEnv hp gamma env). admit.
  assert (hp_satisfies_s := h_satisfies_s).
  apply (proj2 (EveryHeapSatisfiesPersistentTerm s hp h env this CC s_persistent)) in hp_satisfies_s.
  assert (hp_satisfies_hoare := hoare_p_e_q env this hp fake_gamma_match_env hp_satisfies_s).
  assert (hp_eval := hp_satisfies_hoare hp_satisfies_p).
  fold JFIHeapSatisfiesInEnv in hp_eval.
  destruct hp_eval as (confs & hn & res_ex & res & hp_eval & ex_eq & hn_satisfies_q).
  rewrite ex_eq in *; clear ex_eq res_ex.
  destruct (EvaluationOnExtendedHeap hp hr h e confs hn ex res env this CC)
    as (confs_ext & hn_perm & hn_ext & res_ext & pi & eval_ext); try easy.
    admit. (* TODO hp consistent *)
    admit. (* TODO no hardcoded locs in e *)
    admit. (* TODO free vars in e are in hp *)
  destruct eval_ext as
    (hn_pi & env_pi & res_pi & union_hn_perm_hr & eval_ext).
  exists confs_ext, hn_ext, ex, res_ext.
  simpl.
  split; try split; try easy.
  exists hn_perm, hr.
  split; split.
  + apply union_hn_perm_hr.
  + apply union_hn_perm_hr.
  + apply (PermutationPreservesHeapSatisfying _  hn _ (StrMap.add v res env) _ _ pi CC); try easy.
    now apply ExtendPermutedEnvs.
  + destruct res_ext.
    ++ now apply AddingNullPreservesHeapSatisfying.
    ++ now apply AddingFreshVarPreservesHeapSatisfying.
Admitted.
Hint Resolve HTFrameRuleSoundness : core.

Lemma HTRetRuleSoundness : forall gamma s v w w_expr CC,
  w_expr = JFIValToJFVal w ->
  JFISemanticallyImplies gamma s
    (JFIHoare JFITrue (JFVal1 w_expr) None v (JFIEq (JFIVar v) w)) CC.
Proof.
  intros gamma s v w w_expr CC.
  intros expr_val env this h gamma_match_env h_satisfies_s h_satisfies_true.

  destruct (JFIExistsValToLoc w w_expr env this) as (l & w_is_l & subst_w); trivial.
  exists [], h, None, l.
  unfold JFIEvalInEnv, JFIExprSubstituteEnv.
  rewrite subst_w.
  split; try split; try easy.
  simpl.
  rewrite StrMapFacts.add_eq_o; trivial.
  unfold JFIValToLoc in w_is_l |- *.
  destruct w; try now injection w_is_l.
  destruct (Classical_Prop.classic (v = var)).
  + now rewrite StrMapFacts.add_eq_o.
  + rewrite StrMapFacts.add_neq_o; trivial.
    now rewrite w_is_l.
Qed.

Lemma HTPreconditionStrenghtenSoundness : forall gamma s p p' e ex v q CC,
  (JFISemanticallyImplies gamma s (JFIImplies p p') CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare p' e ex v q) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e ex v q) CC.
Proof.
  intros gamma s p p' e ex v q CC.
  intros p_implies_p' hoare_p'.
  intros env this h gamma_match_env h_satisfies_s.
  simpl.
  intros h_satisfies_p.
  set (h_satisfies_hoare_p' := hoare_p' env this h gamma_match_env h_satisfies_s).
  simpl in h_satisfies_hoare_p'.
  apply h_satisfies_hoare_p'.
  destruct (p_implies_p' env this h gamma_match_env h_satisfies_s) as [not_h_satisfies_p | h_satisfies_p'].
    + destruct (not_h_satisfies_p h_satisfies_p).
    + exact h_satisfies_p'.
Qed.

Lemma HTPostconditionWeakenSoundness : forall gamma s p e ex v q q' cn CC,
  (JFITermPersistent s) ->
  (JFIVarFreshInTerm v s) ->
  (JFISemanticallyImplies gamma s (JFIHoare p e ex v q') CC) ->
  (JFISemanticallyImplies (JFIGammaAdd v cn gamma) s (JFIImplies q' q) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare p e ex v q) CC.
Proof.
  intros gamma s p e ex v q q' cn CC.
  intros s_persistent v_fresh hoare_q' q'_implies_q.
  intros env this h gamma_match_env h_satisfies_s.
  simpl.
  intros h_satisfies_p.
  destruct (hoare_q' env this h gamma_match_env h_satisfies_s h_satisfies_p ) as
    (confs & hn & res_ex & res & eval_e & res_eq & h_satisfies_q').
  fold JFIHeapSatisfiesInEnv in h_satisfies_q'.
  assert (gamma_match_env_in_hn := EvaluationPreservesGammaMatching gamma env h (JFIExprSubstituteEnv env this e) confs hn res_ex res CC gamma_match_env eval_e).
  assert (hn_satisfies_s := EvaluationPreservesPersistentTerms env this s h (JFIExprSubstituteEnv env this e) confs hn res_ex res CC s_persistent h_satisfies_s eval_e).
  apply AddingFreshVarPreservesHeapSatisfying with (x := v) (l := res) in hn_satisfies_s; trivial.
  assert (gamma_v_match_env : JFIGammaMatchEnv hn (JFIGammaAdd v cn gamma) (StrMap.add v res env)). admit.
  assert (hn_satisfies_implies := q'_implies_q (StrMap.add v res env) this hn gamma_v_match_env hn_satisfies_s).
  exists confs, hn, res_ex, res.
  split; try split; try easy.
  simpl in hn_satisfies_implies.
  now destruct hn_satisfies_implies.
Admitted.

Lemma HTCsqRuleSoundness : forall gamma s p p' e ex v q q' cn CC,
  (JFITermPersistent s) ->
  (JFIVarFreshInTerm v s) ->
  (JFISemanticallyImplies gamma s (JFIImplies p p') CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare p' e ex v q') CC) ->
  (JFISemanticallyImplies (JFIGammaAdd v cn gamma) s (JFIImplies q' q) CC) -> JFISemanticallyImplies gamma s (JFIHoare p e ex v q) CC.
Proof.
  intros gamma s p p' e ex v q q' cn CC.
  intros s_persistent p_implies_p' q_implies_q' hoare_p'q'.
  apply HTPostconditionWeakenSoundness with (q':=q') (cn:=cn) (v:=v); try easy.
  now apply HTPreconditionStrenghtenSoundness with (p':=p'); try easy.
Qed.
Hint Resolve HTCsqRuleSoundness : core.

Lemma HTDisjIntroRuleSoundness : forall gamma s p q e ex v r CC,
  (JFISemanticallyImplies gamma s (JFIHoare p e ex v r) CC) ->
  (JFISemanticallyImplies gamma s (JFIHoare q e ex v r) CC) ->
   JFISemanticallyImplies gamma s (JFIHoare (JFIOr p q) e ex v r) CC.
Proof.
  intros gamma s p q e ex v r CC.
  intros hoare_p_r hoare_q_r.
  intros env this h gamma_match_env h_satisfies_s.
  simpl.
  intros p_or_q.
  destruct p_or_q.
  + exact (hoare_p_r env this h gamma_match_env h_satisfies_s H).
  + exact (hoare_q_r env this h gamma_match_env h_satisfies_s H).
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
    intros env this h gamma_match_env h_satisfies_s h_satisfies_p;
    apply (hoare_pq_r env this h gamma_match_env h_satisfies_s);
    auto.
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
  intros env this h gamma_match_env h_satisfies_s (h_satisfies_p & h_satisfies_eq).
  simpl.
  now apply p_eq_implies_hoare.
Qed.
Hint Resolve HTEqRule1Soundness : core.

Lemma HTEqRule2Soundness : forall gamma s p v1 v2 e ex v q CC,
  (JFISemanticallyImplies gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e ex v q) CC) ->
  (JFISemanticallyImplies gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e ex v q) CC).
Proof.
  intros gamma s p v1 v2 e ex v q CC.
  intros p_eq_implies_hoare.
  intros env this h gamma_match_env (h_satisfies_s & h_satisfies_eq) h_satisfies_p.
  now apply p_eq_implies_hoare.
Qed.
Hint Resolve HTEqRule2Soundness : core.

Lemma HTNewNotNullRuleSoundness : forall gamma s p mu cn vs v CC,
  JFISemanticallyImplies gamma s
    (JFIHoare p (JFNew mu cn vs) None v
     (JFIImplies (JFIEq (JFIVar v) JFINull) JFIFalse)) CC.
Proof.
  intros gamma s p mu cn vs v CC.
  intros env this h gamma_match_env h_satisfies_s.
  destruct (EnsureValsMapIsLocsMap vs env this) as (ls & vs_is_ls).
  destruct (AllocSucceedsInCorrectProgram CC h cn ls)
    as (newloc & (newheap & alloc_newloc_newheap)).
  intros h_satisfies_p.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFNew mu cn vs) ]]_ None])],
    newheap, None, newloc.
  split; [ | split].
  + apply NewEvaluationStep with (prog := CC) (ls := ls); assumption.
  + trivial.
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
  (nth_error vs n = Some (JFIValToJFVal value)) ->
  (value <> (JFIVar v)) ->
    JFISemanticallyImplies gamma s
      (JFIHoare p (JFNew mu cn vs) None v (JFIFieldEq (JFIVar v) field value)) CC.
Proof.
  intros decls gamma cn objflds vs n field value s p mu v CC.
  intros fdls_of_cn nth_field nth_value value_not_v.
  intros env this h gamma_match_env h_satisfies_s h_satisfies_p.
  destruct (EnsureValsMapIsLocsMap vs env this) as (ls & vs_map_is_ls).
  simpl.
  unfold JFIHeapSatisfiesInEnv.

  destruct (JFIExistsValToLoc value (JFIValToJFVal value) env this) as (l & value_is_l & subst_value); trivial.
  assert (vs_is_ls := EnsureValsListIsLocsList ls vs n l env this vs_map_is_ls).
  destruct (AllocSucceedsInCorrectProgram (JFIDeclsProg decls) h cn ls)
    as (newloc & (newheap & alloc_newloc_newheap)).
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFNew mu cn vs) ]]_ None])], newheap, None, newloc.
  split; [ | split]; trivial.
  + apply NewEvaluationStep with (prog := JFIDeclsProg decls) (ls := ls); assumption.
  + rewrite StrMapFacts.add_eq_o; trivial.
    rewrite ValToLoc_neq_o; trivial.
    rewrite value_is_l.
    apply (SuccessfullAllocSetsFields decls h cn ls newloc newheap objflds n field l); try assumption.
    apply vs_is_ls.
    rewrite <-subst_value.
    now apply List.map_nth_error.
Qed.
Hint Resolve HTNewFieldRuleSoundness : core.

Lemma AddingFreshVarInsidePreservesHeapSatisfying : forall q h env this x1 l1 x2 l2 CC,
   (JFIVarFreshInTerm x2 q) ->
    JFIHeapSatisfiesInEnv h q (StrMap.add x1 l1 env) this CC <->
   (JFIHeapSatisfiesInEnv h q (StrMap.add x1 l1 (StrMap.add x2 l2 env)) this CC).
Proof.
Admitted.

Lemma HTLetRuleSoundness : forall gamma s p e1 e2 class x q ex u r CC,
  (JFITermPersistent s) ->
  (JFIVarFreshInTerm x s) ->
  (JFIVarFreshInTerm x r) ->
  (JFISemanticallyImplies gamma s (JFIHoare p e1 None x q) CC) ->
  (JFISemanticallyImplies (JFIGammaAdd x class gamma) s (JFIHoare q e2 ex u r) CC) ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFLet class x e1 e2) ex u r) CC.
Proof.
  intros gamma s p e1 e2 class x q ex u r CC.
  intros s_persistent x_fresh_in_s x_fresh_in_r IH_e1 IH_e2.
  intros env this h gamma_match_env.
  intros h_satisfies_s h_satisfies_p.

  assert (tmp := IH_e1 env this h gamma_match_env h_satisfies_s h_satisfies_p).
  fold JFIHeapSatisfiesInEnv in tmp.
  destruct tmp as (e1_confs & h' & e1_ex & e1_res & e1_eval & e1_ex_is_none & h'_satisfies_q).
  rewrite e1_ex_is_none in *; clear e1_ex_is_none.

  assert (h'_gamma_match_env : JFIGammaMatchEnv h' (JFIGammaAdd x class gamma) (StrMap.add x e1_res env)).
    admit.
  assert (h'_satisfies_s : JFIHeapSatisfiesInEnv h' s (StrMap.add x e1_res env) this CC).
  apply EvaluationPreservesPersistentTerms with (h := h) (e := (JFIExprSubstituteEnv env this e1))
    (confs := e1_confs) (ex := None) (res := e1_res); try easy.
  now apply AddingFreshVarPreservesHeapSatisfying.
  assert (tmp := IH_e2 (StrMap.add x e1_res env) this h' h'_gamma_match_env h'_satisfies_s h'_satisfies_q).
  fold JFIHeapSatisfiesInEnv in tmp.
  simpl in tmp.
  destruct tmp as (e2_confs & hn & res_ex & res & e2_eval & res_ex_eq & hn_satisfies_r).
  rewrite res_ex_eq in *; clear res_ex_eq.
  destruct (LetEvaluationNormal _ _ _ class _ _ _ _ _ _ _ _ _ _ _ e1_eval e2_eval)
    as (let_confs & let_eval).
  exists let_confs, hn, ex, res.
  simpl.
  split; [ | split]; trivial.
  now apply AddingFreshVarInsidePreservesHeapSatisfying with (x2 := x) (l2 := e1_res).
Admitted.
Hint Resolve HTLetRuleSoundness : core.

Lemma HTLetExSoundness : forall gamma s p class x e1 e2 ex u q CC,
  JFISemanticallyImplies gamma s (JFIHoare p e1 (Some ex) u q) CC ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFLet class x e1 e2) (Some ex) u q) CC.
Proof.
  intros gamma s p class x e1 e2 ex u q CC.
  intros IH_e1.
  intros env this h gamma_match_env.
  intros h_satisfies_s h_satisfies_p.

  assert (tmp := IH_e1 env this h gamma_match_env h_satisfies_s h_satisfies_p).
  fold JFIHeapSatisfiesInEnv in tmp.
  destruct tmp as (e1_confs & hn & e1_ex & e1_res & e1_eval & ex_eq & h'_satisfies_q).
  rewrite ex_eq in *.

  destruct (LetEvaluationEx _ _ class x e1 e2 _ _ _ _ _ _ e1_eval) as (let_confs & let_eval).
  exists let_confs, hn, e1_ex, e1_res.
  simpl.
  now rewrite ex_eq in *.
Qed.
Hint Resolve HTLetExSoundness : core.

Lemma HTFieldSetRuleSoundness : forall gamma s x x_expr field u v v_expr CC,
  x_expr = JFIValToJFVal x ->
  v_expr = JFIValToJFVal v ->
  x <> (JFIVar u) ->
  v <> (JFIVar u) ->
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIImplies (JFIEq x JFINull) JFIFalse) (JFAssign (x_expr, field) v_expr)
     None u (JFIFieldEq x field v)) CC.
Proof.
  intros gamma s x x_expr field u v v_expr CC.
  intros x_expr_val v_expr_val x_not_u v_not_u.
  intros env this h gamma_match_env h_satisfies_s h_satisfies_p.

  destruct (JFIExistsValToLoc x x_expr env this) as (xl & x_is_xl & subst_x); trivial.
  destruct (JFIExistsValToLoc v v_expr env this) as (vl & v_is_vl & subst_v); trivial.
  destruct xl as [ | xn].
  + destruct h_satisfies_p; try easy. exfalso. apply H. simpl. now rewrite x_is_xl.
  + destruct (EnsureLocInHeap h xn) as ((obj & cn) & x_points_to_o).
    set (new_obj := ((JFXIdMap.add field vl obj), cn)).
    set (new_h := Heap.add xn new_obj h).
    exists [(h, [ [] [[ (JFAssign (JFVLoc (JFLoc xn), field) (JFVLoc vl)) ]]_ None])], new_h, None, vl.
    simpl.
    split; [ | split]; trivial.
    ++ unfold JFIEvalInEnv, JFIEval, JFIPartialEval.
       split; try trivial.
       unfold JFIExprSubstituteEnv.
       rewrite subst_x, subst_v.
       split; trivial.
       unfold red.
       rewrite x_points_to_o.
       now split.
    ++ simpl.
       rewrite 2!ValToLoc_neq_o; trivial.
       rewrite x_is_xl, v_is_vl.
       unfold JFIObjFieldEq.
       unfold new_h.
       rewrite HeapFacts.add_eq_o; try trivial.
       unfold new_obj.
       rewrite JFXIdMapFacts.add_eq_o; trivial.
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

Lemma HTNullFieldSetRuleSoundness : forall gamma s x x_expr field loc v CC,
  x_expr = JFIValToJFVal x ->
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFINull) (JFAssign (x_expr, field) (JFVLoc loc))
     NPE_mode v JFITrue) CC.
Proof.
  intros gamma s x x_expr field loc v CC.
  intros x_expr_val.
  intros env this h gamma_match_env h_satisfies_s.
  intros x_is_null.
  simpl in x_is_null.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFAssign (x_expr, field) (JFVLoc loc)) ]]_ None])],
    h, NPE_mode, (JFLoc NPE_object_loc).
  simpl.
  split; try split; try split; trivial.
  destruct x; rewrite x_expr_val.
  + simpl.
    now rewrite 2!ValEnvSubstitutionPreservesVLoc.
  + discriminate x_is_null.
  + simpl in x_is_null.
    simpl.
    rewrite ValEnvSubstitutionReplacesVarInEnv with (l := null); trivial.
    now rewrite ValEnvSubstitutionPreservesVLoc.
    destruct (StrMap.find var env); try easy.
    now rewrite x_is_null.
Qed.
Hint Resolve HTNullFieldSetRuleSoundness : core.

Lemma HTNullFieldGetRuleSoundness : forall gamma s x x_expr field v CC,
  x_expr = JFIValToJFVal x ->
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFINull) (JFVal2 (x_expr, field))
     NPE_mode v JFITrue) CC.
Proof.
  intros gamma s x x_expr field v CC.
  intros x_expr_val.
  intros env this h gamma_match_env h_satisfies_s.
  intros x_is_null.
  simpl in x_is_null.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFVal2 (x_expr, field)) ]]_ None])],
    h, NPE_mode, (JFLoc NPE_object_loc).
  simpl.
  split; try split; try split; trivial.
  destruct x; rewrite x_expr_val.
  + simpl.
    now rewrite ValEnvSubstitutionPreservesVLoc.
  + discriminate x_is_null.
  + simpl in x_is_null.
    simpl.
    rewrite ValEnvSubstitutionReplacesVarInEnv with (l := null); try easy.
    destruct (StrMap.find var env); try easy.
    now rewrite x_is_null.
Qed.
Hint Resolve HTNullFieldGetRuleSoundness : core.

Lemma HTIfRuleSoundness : forall gamma v1 v1_expr v2 v2_expr e1 e2 p q s ex u CC,
  (v1_expr = JFIValToJFVal v1) -> (v2_expr = JFIValToJFVal v2) ->
  (JFISemanticallyImplies gamma s 
    (JFIHoare (JFIAnd p (JFIEq v1 v2)) e1 ex u q) CC) ->
  (JFISemanticallyImplies gamma s
    (JFIHoare (JFIAnd p (JFIImplies (JFIEq v1 v2) JFIFalse)) e2 ex u q) CC) ->
   JFISemanticallyImplies gamma s
    (JFIHoare p (JFIf v1_expr v2_expr e1 e2) ex u q) CC.
Proof.
  intros gamma v1 v1_expr v2 v2_expr e1 e2 p q s ex u CC.
  intros v1_expr_val v2_expr_val IH_if_eq IH_if_neq.
  intros env this h gamma_match_env h_satisfies_s h_satisfies_p.

  destruct (JFIExistsValToLoc v1 v1_expr env this) as (l1 & v1_is_l1 & v1_subst_eq); trivial.
  destruct (JFIExistsValToLoc v2 v2_expr env this) as (l2 & v2_is_l2 & v2_subst_eq); trivial.

  destruct (Classical_Prop.classic (l1 = l2)) as [l1_eq_l2 | l1_neq_l2].
  + assert (h_satisfies_and : JFIHeapSatisfiesInEnv h (JFIAnd p (JFIEq v1 v2)) env this CC).
    simpl.
    now rewrite v1_is_l1, v2_is_l2.
    assert (e1_eval := IH_if_eq env this h gamma_match_env h_satisfies_s h_satisfies_and).
    fold JFIHeapSatisfiesInEnv in e1_eval.
    destruct e1_eval as (e1_confs & hn & res_ex & res & e1_eval & res_eq & hn_satisfies_q).
    set (first_st := [ [] [[JFIExprSubstituteEnv env this (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ]]_ None]).
    exists ((h, first_st)::e1_confs), hn, res_ex, res.
    unfold first_st.
    rewrite <-l1_eq_l2.
    split; try split; try split; trivial; simpl.
    rewrite ValEnvSubstitutionPreservesVLoc.
    now rewrite v1_subst_eq, v2_subst_eq, l1_eq_l2.
    simpl.
    rewrite v1_subst_eq, v2_subst_eq, <-l1_eq_l2.
    Loc_dec_eq l1 l1 (eq_refl l1).
    now unfold JFIEvalInEnv, JFIEval in e1_eval.
  + assert (h_satisfies_and : JFIHeapSatisfiesInEnv h
      (JFIAnd p (JFIImplies (JFIEq v1 v2) JFIFalse)) env this CC).
    simpl. rewrite v1_is_l1, v2_is_l2. simpl. split; trivial. now apply or_introl.
    assert (e2_eval := IH_if_neq env this h gamma_match_env h_satisfies_s h_satisfies_and).
    fold JFIHeapSatisfiesInEnv in e2_eval.
    destruct e2_eval as (e2_confs & hn & res_ex & res & e2_eval & res_eq & hn_satisfies_q).
    set (first_st := [ [] [[JFIExprSubstituteEnv env this (JFIf (JFVLoc l1) (JFVLoc l2) e1 e2) ]]_ None]).
    exists ((h, first_st)::e2_confs), hn, res_ex, res.
    unfold first_st.
    simpl. split; try split; try split; trivial.
    simpl.
    rewrite 2!ValEnvSubstitutionPreservesVLoc.
    now rewrite v1_subst_eq, v2_subst_eq.
    simpl.
    rewrite v1_subst_eq, v2_subst_eq.
    Loc_dec_neq l1 l2 l1_neq_l2.
    now unfold JFIEvalInEnv, JFIEval in e2_eval.
Qed.

Lemma HTNullInvokeSoundness : forall gamma s x x_expr mn vs v CC,
  x_expr = JFIValToJFVal x ->
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFINull) (JFInvoke x_expr mn vs)
     NPE_mode v JFITrue) CC.
Proof.
  intros gamma s x x_expr mn vs v CC.
  intros x_expr_val env this h gamma_match_env h_satisfies_s.
  intros x_is_null.
  simpl in x_is_null.
  destruct (JFIExistsValToLoc x x_expr env this) as (l & x_is_l & x_subst_eq); trivial.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFInvoke x_expr mn vs) ]]_ None])],
    h, NPE_mode, (JFLoc NPE_object_loc).
  simpl.
  split; try split; try split; trivial.
  simpl.
  unfold JFIValToLoc in x_is_null, x_is_l.
  rewrite x_subst_eq.
  destruct l.
  destruct x; try discriminate x_is_null; try easy.
  destruct x; try easy.
  now rewrite x_is_l in x_is_null.
Qed.
Hint Resolve HTNullInvokeSoundness : core.


Lemma HTThrowSoundness : forall decls gamma x x_expr cn s v CC,
  x_expr = JFIValToJFVal x ->
  JFIValType decls gamma x = Some cn ->
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIImplies (JFIEq x JFINull) JFIFalse) (JFThrow x_expr) 
     (Some cn) v (JFIEq (JFIVar v) x)) CC.
Proof.
  intros decls gamma x x_expr cn s v CC.
  intros x_expr_val type_of_x.
  intros env this h gamma_match_env h_satifsies_s.
  intros x_not_null.
  simpl in x_not_null.
  destruct x_not_null as [x_not_null | x_null]; try destruct x_null.

  destruct (JFIExistsValToLoc x x_expr env this) as (l & x_is_l & x_subst_eq); trivial.
  rewrite x_is_l in x_not_null.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFThrow x_expr) ]]_ None])],
    h, (Some cn), l.
  simpl.
  split; try split; try split; trivial.
  + simpl.
    rewrite x_subst_eq.
    destruct l; try easy.
    unfold class.
    unfold JFIValType in type_of_x.
    destruct x; try discriminate type_of_x.
    ++ admit. (* TODO this type *)
    ++ simpl in x_is_l.
       rewrite <- StrMapFacts.find_mapsto_iff in type_of_x, x_is_l.
       assert (type_of_n := (proj2 (gamma_match_env var)) (JFLoc n) cn type_of_x x_is_l).
       unfold JFILocOfType in type_of_n.
       destruct (Heap.find (elt:=Obj) n h); try destruct type_of_n.
       destruct o.
       now rewrite type_of_n.
  + rewrite StrMapFacts.add_eq_o; trivial.
    destruct x; try discriminate type_of_x.
    ++ simpl in x_is_l |- *.
       now injection x_is_l.
    ++ simpl in x_is_l |- *.
       destruct (Classical_Prop.classic (var = v)).
       +++ rewrite StrMapFacts.add_eq_o; trivial; symmetry; trivial.
       +++ rewrite StrMapFacts.add_neq_o; try (intros v_eq_x; symmetry in v_eq_x; destruct (H v_eq_x)).
           now rewrite x_is_l.
Admitted.
Hint Resolve HTThrowSoundness : core.

Lemma HTNullThrowSoundness : forall gamma x x_expr s v CC,
  x_expr = JFIValToJFVal x -> 
  JFISemanticallyImplies gamma s
    (JFIHoare (JFIEq x JFINull) (JFThrow x_expr)
     NPE_mode v JFITrue) CC.
Proof.
  intros gamma x x_expr s v CC.
  intros x_expr_val env this h gamma_match_env h_satifsies_s.
  intros x_is_null.
  simpl in x_is_null.
  destruct (JFIExistsValToLoc x x_expr env this) as (l & x_is_l & x_subst_eq); trivial.
  exists [(h, [ [] [[ JFIExprSubstituteEnv env this (JFThrow x_expr) ]]_ None])],
    h, NPE_mode, (JFLoc NPE_object_loc).
  simpl.
  split; try split; try split; trivial.
  + simpl.
    unfold JFIValToLoc in x_is_null.
    rewrite x_subst_eq.
  destruct l.
  destruct x; try discriminate x_is_null; try easy.
  destruct x; try easy.
  simpl in x_is_l.
  now rewrite x_is_l in x_is_null.
Qed.
Hint Resolve HTNullThrowSoundness : core.

Lemma HTCatchNormalSoundness : forall gamma s p e1 mu ex x e2 u q CC,
  JFISemanticallyImplies gamma s (JFIHoare p e1 None u q) CC ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFTry e1 mu ex x e2) None u q) CC.
Proof.
  intros gamma s p e1 mu ex x e2 u q CC.
  intros hoare_p_q.
  intros env this h gamma_match_env h_satisfies_s.
  intros h_satisfies_p.
  assert (tmp := hoare_p_q env this h gamma_match_env h_satisfies_s h_satisfies_p).
  fold JFIHeapSatisfiesInEnv in tmp.
  destruct tmp as (e1_confs & hn & e1_ex & e1_res & e1_eval & e1_ex_eq & hn_satisfies_q).
  rewrite e1_ex_eq in *.
  destruct (TryEvaluationNormal h hn mu ex x e1 e2 e1_confs e1_res env this CC e1_eval)
    as (try_confs & try_eval).
  now exists try_confs, hn, None, e1_res.
Qed.
Hint Resolve HTCatchNormalSoundness : core.

Lemma HTCatchExSoundness : forall decls gamma s p e1 mu ex ex' ex'' x e2 u r q,
  let CC := (JFIDeclsProg decls) in
  JFITermPersistent s ->
  JFIVarFreshInTerm x s ->
  JFIVarFreshInTerm x r ->
  Is_true (subtype_bool (JFIDeclsProg decls) (JFClass ex') (JFClass ex)) ->
  JFISemanticallyImplies gamma s (JFIHoare p e1 (Some ex') x q) CC ->
  JFISemanticallyImplies (JFIGammaAdd x ex gamma) s (JFIHoare q e2 ex'' u r) CC ->
  JFISemanticallyImplies gamma s (JFIHoare p (JFTry e1 mu ex x e2) ex'' u r) CC.
Proof.
  intros decls gamma s p e1 mu ex ex' ex'' x e2 u r q CC.
  intros s_persistent x_fresh_in_s x_fresh_in_r is_subtype hoare_e1 hoare_e2.
  intros env this h gamma_match_env h_satisfies_s.
  intros h_satisfies_p.

  assert (tmp := hoare_e1 env this h gamma_match_env h_satisfies_s h_satisfies_p).
  fold JFIHeapSatisfiesInEnv in tmp.
  destruct tmp as (e1_confs & h' & e1_ex & e1_res & e1_eval & e1_ex_is_none & h'_satisfies_q).
  rewrite e1_ex_is_none in *; clear e1_ex_is_none.

  assert (h'_gamma_match_env : JFIGammaMatchEnv h' (JFIGammaAdd x ex gamma) (StrMap.add x e1_res env)).
    admit.

  assert (h'_satisfies_s : JFIHeapSatisfiesInEnv h' s (StrMap.add x e1_res env) this CC).
    apply EvaluationPreservesPersistentTerms with (h := h) (e := (JFIExprSubstituteEnv env this e1))
    (confs := e1_confs) (ex := (Some ex')) (res := e1_res); trivial.
    now apply AddingFreshVarPreservesHeapSatisfying.
  assert (tmp := hoare_e2 (StrMap.add x e1_res env) this h' h'_gamma_match_env h'_satisfies_s h'_satisfies_q).
  fold JFIHeapSatisfiesInEnv in tmp.
  simpl in tmp.
  destruct tmp as (e2_confs & hn & res_ex & res & e2_eval & res_ex_eq & hn_satisfies_r).
  rewrite res_ex_eq in *; clear res_ex_eq.
  destruct (TryEvaluationExCatch h h' hn mu ex' ex'' ex x e1 e2
    e1_confs e2_confs e1_res res env this CC is_subtype e1_eval e2_eval) as (try_confs & try_eval).
  exists try_confs, hn, ex'', res.
  split; try split; try split; try easy.
  now apply AddingFreshVarInsidePreservesHeapSatisfying with (x2 := x) (l2 := e1_res).
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
  intros env this h gamma_match_env h_satisfies_s.
  intros h_satisfies_p.
  assert (tmp := hoare_p_q env this h gamma_match_env h_satisfies_s h_satisfies_p).
  fold JFIHeapSatisfiesInEnv in tmp.
  destruct tmp as (e1_confs & hn & e1_ex & e1_res & e1_eval & e1_ex_eq & hn_satisfies_q).
  rewrite e1_ex_eq in *.
  destruct (TryEvaluationExPass h hn mu ex' ex x e1 e2 e1_confs e1_res env this CC not_subtype e1_eval)
    as (try_confs & try_eval).
  now exists try_confs, hn, (Some ex'), e1_res.
Qed.
Hint Resolve HTCatchPassExSoundness : core.

(* Soundness of weak rule *)

Definition EnvMapsToHeap env (h : Heap) := forall x l,
  StrMap.MapsTo x l env -> LocMapsToHeap l h.

Definition FreeVarsInEnv t (env : JFITermEnv) := forall x,
  VarFreeInTerm x t -> StrMap.In x env.

Definition ValInEnv x (env : JFITermEnv) :=
  match x with
  | JFIVar x => StrMap.In x env
  | _ => True
  end.

Lemma SubenvValToLocEq : forall v env1 env2 this,
  Subenv env1 env2 ->
  ValInEnv v env1 ->
  JFIValToLoc v env1 this = JFIValToLoc v env2 this.
Proof.
  intros v env1 env2 this subenv v_env1.
  destruct v as [ | | x ]; try easy.
  simpl.
  simpl in v_env1.
  apply StrMapFacts.elements_in_iff in v_env1 as (l & x_l_env1).
  apply StrMapFacts.elements_mapsto_iff in x_l_env1.
  assert (x_l_env2 := subenv x l x_l_env1).
  rewrite StrMapFacts.find_mapsto_iff in x_l_env1, x_l_env2.
  now rewrite x_l_env1, x_l_env2.
Qed.

Lemma SubheapFieldEq : forall h1 h2 n f v,
  JFISubheap h1 h2 ->
  Heap.In n h1 ->
  (JFIObjFieldEq (JFLoc n) f v h1 <-> JFIObjFieldEq (JFLoc n) f v h2).
Proof.
  intros h1 h2 l f v subheap n_in_h1.
  unfold JFIObjFieldEq.
  apply HeapFacts.elements_in_iff in n_in_h1 as (o & l_o_h1).
  apply HeapFacts.elements_mapsto_iff in l_o_h1.
  assert (l_o_h2 := subheap l o l_o_h1).
  rewrite HeapFacts.find_mapsto_iff in l_o_h1, l_o_h2.
  now rewrite l_o_h1, l_o_h2.
Qed.

Lemma FreeVarsInHoarePoscondition : forall t1 e ex v t2 env res,
  FreeVarsInEnv (JFIHoare t1 e ex v t2) env ->
  FreeVarsInEnv t2 (StrMap.add v res env).
Proof.
  intros t1 e ex v t2 env res.
  intros free_vars_hoare.
  intros x x_free_in_t2.
  destruct (Classical_Prop.classic (v = x)).
  + apply StrMapFacts.elements_in_iff.
    exists res.
    now apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff, StrMapFacts.add_eq_o.
  + assert (x_in_env := free_vars_hoare x).
    apply StrMapFacts.elements_in_iff in x_in_env as (l & x_e).
    ++ apply StrMapFacts.elements_in_iff.
       exists l.
       rewrite <-StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff in x_e |- *.
       now rewrite StrMapFacts.add_neq_o.
    ++ simpl.
       apply or_intror, or_intror.
       assert ((v =? x)%string = true -> False).
       +++ intros v_eq_x.
           apply H.
           now rewrite String.eqb_eq in v_eq_x.
       +++ now destruct ((v =? x)%string).
Qed.

Lemma ExtendingHeapPreservesHoareSatisfying : forall t1 e ex v t2 h1 env1 h2 h env this CC,
  let t := JFIHoare t1 e ex v t2 in
  EnvMapsToHeap env1 h1 ->
  EnvMapsToHeap env h ->
  Subenv env1 env ->
  JFIDisjointUnion h1 h2 h ->
  FreeVarsInEnv t env1 ->
  HeapEnvEquivalent h1 h env1 env this this t CC.
Proof.
  intros t1 e ex v t2 h1 env1 h2 h env this CC t.
  intros env1_h1 env_h subenv union free_vars.
  unfold HeapEnvEquivalent.
  assert (IHt1 : HeapEnvEquivalent h1 h env1 env this this t1 CC). admit.
  assert (IHt2 : forall (h1 : Heap) (env1 : StrMap.t Loc) 
         (h2 h : Heap) (env : StrMap.t Loc) 
         (CC : JFProgram),
       EnvMapsToHeap env1 h1 ->
       EnvMapsToHeap env h ->
       Subenv env1 env ->
       JFIDisjointUnion h1 h2 h ->
       FreeVarsInEnv t2 env1 ->
       HeapEnvEquivalent h1 h env1 env this this t2 CC). admit.
  unfold t in *.
  clear t.
  split; simpl.
  + admit. (* evaluation on extended heap *)
  + intros h_satisfies_hoare h1_satisfies_t1.
    destruct h_satisfies_hoare as (confs & hn & res_ex & res & h_eval & ex_eq & hn_satisfies_t2).
      now apply IHt1.
    destruct (EvaluationDependsOnFreeVars h1 h2 (Heap.empty Obj) h h1 e confs hn res_ex res env this CC)
      as (hn_base & confs1 & hn1_base & hn1 & res1 & pi &
          pi_env & pi_res & res_in_base & pi_hn_base & union_hn & union_hn1 & h1_eval);
      try easy.
      admit. (* h1 consistent *)
      admit. (* no hardcoded locs in e *)
      admit. (* free vars in h1 *)
    now apply DisjointUnionSymmetry, DisjointUnionIdentity.
    exists confs1, hn1, res_ex, res1.
    split; [ | split]; trivial.
    ++ admit. (* eval on restricted env *)
    ++ apply (IHt2 hn_base (StrMap.add v res env1) h2 hn (StrMap.add v res env) CC)
         in hn_satisfies_t2; try easy.
       +++ apply (PermutationPreservesHeapSatisfying t2 hn_base hn1 (StrMap.add v res env1) (StrMap.add v res1 env1) this pi CC); try easy.
           - now apply EqPermuted2 with (h2 := hn1_base), UnionWithEmptyEq, union_hn1.
           - apply ExtendPermutedEnvs; try easy.
             now apply SubenvPermuted with (env2 := env).
       +++ admit. (* res in hn_base *)
       +++ admit. (* res in hn *)
       +++ now apply ExtendingSubenv.
       +++ now apply FreeVarsInHoarePoscondition with (t1 := t1) (e := e) (ex := ex).
Admitted.

Lemma ExtendingHeapPreservesHeapSatisfying : forall t h1 env1 h2 h env this CC,
  EnvMapsToHeap env1 h1 ->
  EnvMapsToHeap env h ->
  Subenv env1 env ->
  JFIDisjointUnion h1 h2 h ->
  FreeVarsInEnv t env1 ->
  HeapEnvEquivalent h1 h env1 env this this t CC.
Proof.
  intros t.
  induction t; intros h1 env1 h2 h env this CC env1_h1 env_h subenv union free_vars; eauto.
  + admit. (* easy *)
  + admit. (* easy *)
  + admit. (* easy *)
  + now apply ExtendingHeapPreservesHoareSatisfying with (h2 := h2).
  + unfold HeapEnvEquivalent.
    simpl.
    rewrite !SubenvValToLocEq with (env1 := env1) (env2 := env); try easy.
    now destruct val2; try easy; apply free_vars; apply or_intror.
    now destruct val1; try easy; apply free_vars; apply or_introl.
  + destruct union as ((subheap_h1 & subheap_h2 & same_keys) & disjoint).
    unfold HeapEnvEquivalent.
    simpl.
    rewrite <-!SubenvValToLocEq with (env1 := env1) (env2 := env); try easy.
    destruct obj.
    ++ now destruct (JFIValToLoc v env).
    ++ destruct (JFIValToLoc v env1 this), (JFIValToLoc JFIThis env1 this); try easy.
           destruct l0; try easy.
           apply SubheapFieldEq; try easy.
           unfold EnvMapsToHeap in env_h.
           admit. (* TODO this in heap*)
    ++ simpl.
       destruct (Classical_Prop.classic (StrMap.In var env1)).
       +++ apply StrMapFacts.elements_in_iff in H as (l & var_l).
           apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff in var_l.
           rewrite var_l.
           destruct (JFIValToLoc v env1); try easy.
           destruct l; try easy.
           apply SubheapFieldEq; try easy.
           unfold EnvMapsToHeap in env_h.
           apply (env1_h1 var (JFLoc n)).
           now apply StrMapFacts.find_mapsto_iff.
       +++ apply StrMapFacts.not_find_mapsto_iff in H.
           now rewrite H.
    ++ now destruct v; try easy; apply free_vars; apply or_intror.
    ++ now destruct obj; try easy; apply free_vars; apply or_introl.
  + unfold HeapEnvEquivalent.
    simpl.
    split.
    ++ intros (h11 & h12 & disjoint_union_h1 & h11_satisfies_t1 & h12_satisfies_t2).
       destruct (ExistsUnion h11 h2) as (h11_h2 & union_h11_h2). admit.
       exists h11_h2, h12.
       split; [ | split].
       +++ admit.
       +++ apply (IHt1 h11 env1 h2 h11_h2 env this CC); try easy.
           - admit. (* TODO envs in sep *)
           - admit. (* TODO envs in sep *)
           - admit.
           - intros x x_free.
             now apply free_vars, or_introl.
       +++ admit. (* TODO envs in sep *)
    ++ admit.
  + admit.
Admitted.

Lemma GammaMatchEnvImpliesEnvMapsToHeap : forall h gamma env,
  JFIGammaMatchEnv h gamma env ->
  EnvMapsToHeap env h.
Proof.
  intros h gamma env gamma_match_env.
  intros x l x_l.
  unfold JFIGammaMatchEnv in gamma_match_env.
  destruct (gamma_match_env x) as (same_keys & types_match).
  clear gamma_match_env.
  assert (x_in_gamma : StrMap.In x gamma).
    apply same_keys.
    apply StrMapFacts.elements_in_iff.
    exists l.
    now apply StrMapFacts.elements_mapsto_iff.
  apply StrMapFacts.elements_in_iff in x_in_gamma as (cn & x_cn).
  apply StrMapFacts.elements_mapsto_iff in x_cn.
  assert (type_of_l := types_match l cn x_cn x_l).
  unfold JFILocOfType in type_of_l.
  destruct l; try easy.
  apply HeapFacts.elements_in_iff.
  assert (exists o, Heap.find n h = Some o).
    destruct (Heap.find n h); try now destruct type_of_l.
    now exists o.
  destruct H as (o & n_o).
  exists o.
  now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
Qed.

Lemma WeakRuleSoundness : forall gamma p1 p2 CC,
  JFISemanticallyImplies gamma (JFISep p1 p2) p1 CC.
Proof.
  intros gamma p1 p2 CC.
  intros env this h gamma_match_env h_satisfies_sep.
  destruct h_satisfies_sep as (h1 & h2 & disjoint_union & h1_satisfies_p1 & h2_satisfies_p2).
  apply (ExtendingHeapPreservesHeapSatisfying p1 h1 env h2 h env); try easy.
  + admit. (* TODO envs in sep *)
  + now apply GammaMatchEnvImpliesEnvMapsToHeap with (gamma := gamma).
  + admit. (* TODO JFI proof implies all free vars are in env *)
Admitted.
Hint Resolve WeakRuleSoundness : core.

(* Soudness of outer terms *)

Lemma OuterExistsIntroRuleSoundness : forall x v type decls gamma p q CC,
  (JFIValType decls gamma v = Some type) ->
  (JFISemanticallyImpliesOuter gamma q
                (JFIOuterTermSubstituteVal x v p) CC) ->
   JFISemanticallyImpliesOuter gamma q (JFIExists type x p) CC.
Proof.
  intros x v type decls gamma p q CC.
  intros type_of_v q_implies_p.
  intros env this h gamma_match_env h_satisfies_q.
  simpl.
  simpl in type_of_v.

  destruct v as [ | | v].
  + exists null.
    now split.
  + exists (JFLoc this).
    split.
    ++ admit. (* TODO this type *)
    ++ unfold JFISemanticallyImplies in q_implies_p.
       apply q_implies_p in h_satisfies_q; trivial.
       now apply HeapSatisfiesSubstIffThisMovedToEnv.
  + destruct (proj1 (gamma_match_env v)) as (gamma_implies_env & _).
    assert (v_in_gamma : StrMap.In v gamma);
      try (apply StrMap_in_find_iff; exists type; assumption).
    apply gamma_implies_env in v_in_gamma.
    apply StrMap_in_find_iff in v_in_gamma.
    destruct v_in_gamma as (l & v_is_l).
    exists l.
    split.
    ++ simpl in type_of_v.
       rewrite <- StrMapFacts.find_mapsto_iff in type_of_v, v_is_l.
       exact (proj2 (gamma_match_env v) l type type_of_v v_is_l).
    ++ unfold JFISemanticallyImplies in q_implies_p.
       apply (HeapSatisfiesSubstIffVarMovedToEnv h x v l p env this CC v_is_l).
       now apply q_implies_p.
Admitted.
Hint Resolve OuterExistsIntroRuleSoundness : core.

Lemma OuterExistsElimRuleSoundness : forall gamma decls p q r type x,
  let CC := JFIDeclsProg decls in
  JFIVarFreshInOuterTerm x r ->
  JFIVarFreshInOuterTerm x q ->
  JFISemanticallyImpliesOuter gamma r (JFIExists type x p) CC ->
  JFISemanticallyImpliesOuter (JFIGammaAdd x type gamma) (JFIOuterAnd r p) q CC ->
  JFISemanticallyImpliesOuter gamma r q CC.
Proof.
  intros gamma decls p q r type x CC.
  intros x_fresh_in_r x_fresh_in_q r_implies_exists and_implies_q.
  intros env this h gamma_match_env h_satisfies_r.
  assert (h_satisfies_exists := r_implies_exists env this h gamma_match_env h_satisfies_r).
  destruct h_satisfies_exists as (l & l_of_type & h_satisfies_p).
  assert (h_satisfies_q := and_implies_q (StrMap.add x l env) this h).
  apply AddingFreshVarPreservesHeapSatisfyingOuter with (x := x) (l := l); try assumption.
  apply h_satisfies_q.
  + apply ExtendedGammaMatchesExtendedEnv; assumption.
  + simpl.
    split.
    ++ apply AddingFreshVarPreservesHeapSatisfyingOuter; assumption.
    ++ exact h_satisfies_p.
Qed.
Hint Resolve OuterExistsElimRuleSoundness : core.

Lemma OuterAndIntroRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImpliesOuter gamma r p CC) ->
  (JFISemanticallyImpliesOuter gamma r q CC) ->
   JFISemanticallyImpliesOuter gamma r (JFIOuterAnd p q) CC.
Proof.
  intros gamma p q r CC.
  intros r_implies_p r_implies_q.
  intros env this h gamma_match_env h_satisfies_r.
  simpl.
  split.
  + apply r_implies_p.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
  + apply r_implies_q.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
Qed.
Hint Resolve OuterAndIntroRuleSoundness : core.

Lemma OuterAndElimRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImpliesOuter gamma r (JFIOuterAnd p q) CC) ->
   JFISemanticallyImpliesOuter gamma r p CC /\ JFISemanticallyImpliesOuter gamma r q CC.
Proof.
  intros gamma p q r CC.
  intros r_implies_p_and_q.
  split;
  intros env this h gamma_match_env h_satisfies_r;
  apply r_implies_p_and_q.
  + exact gamma_match_env.
  + exact h_satisfies_r.
  + exact gamma_match_env.
  + exact h_satisfies_r.
Qed.

Lemma OuterOrIntroRuleSoundness : forall gamma p q r CC,
  (JFISemanticallyImpliesOuter gamma r p CC \/ JFISemanticallyImpliesOuter gamma r q CC) ->
   JFISemanticallyImpliesOuter gamma r (JFIOuterOr p q) CC.
Proof.
  intros gamma p q r CC.
  intros [r_implies_p | r_implies_q]; intros env this h gamma_match_env h_satisfies_r; simpl.
  + apply or_introl.
    apply r_implies_p.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
  + apply or_intror.
    apply r_implies_q.
    ++ exact gamma_match_env.
    ++ exact h_satisfies_r.
Qed.

Lemma OuterOrElimRuleSoundness : forall gamma p q r s CC,
  (JFISemanticallyImpliesOuter gamma s (JFIOuterOr p q) CC) ->
  (JFISemanticallyImpliesOuter gamma (JFIOuterAnd s p) r CC) ->
  (JFISemanticallyImpliesOuter gamma (JFIOuterAnd s q) r CC) ->
   JFISemanticallyImpliesOuter gamma s r CC.
Proof.
  intros gamma p q r s CC.
  intros s_implies_p_or_q s_and_p_implies_r s_and_q_implies_r.
  intros env this h gamma_match_env h_satisfies_s.
  set (p_or_q := s_implies_p_or_q env this h gamma_match_env h_satisfies_s).
  destruct p_or_q as [h_satisfies_p | h_satisfies_q].
  + apply (s_and_p_implies_r env this h gamma_match_env).
    simpl.
    exact (conj h_satisfies_s h_satisfies_p).
  + apply (s_and_q_implies_r env this h gamma_match_env).
    simpl.
    exact (conj h_satisfies_s h_satisfies_q).
Qed.
Hint Resolve OuterOrElimRuleSoundness : core.

(* =============== Main theorems =============== *)

Theorem JFISoundness : forall gamma decls p t,
  let CC := JFIDeclsProg decls in
  (JFIProves decls gamma p t) ->
   JFISemanticallyImplies gamma p t CC.
Proof.
  intros gamma decls p t CC.
  unfold CC in *.
  intros proof.
  induction proof.
  (* JFIAsmRule *)
  + apply AsmRuleSoundness.
  (* JFITransRule *)
  + now apply (TransRuleSoundness gamma p q r).
  (* JFIEqReflRule*)
  + apply EqReflRuleSoundness.
  (* JFIEqSymRule *)
  + now apply EqSymRuleSoundness.
  (* JFIFalseElimRule *)
  + now apply FalseElimRuleSoundness.
  (* JFITrueIntroRule *)
  + now apply TrueIntroRuleSoundness.
  (* JFIAndIntroRule *)
  + now apply AndIntroRuleSoundness.
  (* JFIAndElimLRule *)
  + now apply AndElimRuleSoundness with (q := q).
  (* JFIAndElimRRule *)
  + now apply AndElimRuleSoundness with (p := p).
  (* JFIOrIntroLRule *)
  + now apply OrIntroRuleSoundness, or_introl.
  (* JFIOrIntroRRule *)
  + now apply OrIntroRuleSoundness, or_intror.
  (* JFIOrElimRule *)
  + now apply OrElimRuleSoundness with (gamma := gamma) (p := p) (q := q).
  (* JFIImpliesIntroRule *)
  + now apply ImpliesIntroRuleSoundness.
  (* JFIImpliesElimRule *)
  + now apply ImpliesElimRuleSoundness with (p := p).
  (* JFIWeakRule *)
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
  + eauto.
  (* JFIHTRetRule *)
  + now apply HTRetRuleSoundness.
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
  + now apply HTIfRuleSoundness with (v1 := v1) (v2 := v2).
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

Theorem JFIOuterSoundness : forall gamma decls p t,
  let CC := JFIDeclsProg decls in
  (JFIProvesOuter decls gamma p t) ->
   JFISemanticallyImpliesOuter gamma p t CC.
Proof.
  intros gamma decls p t CC.
  unfold CC in *.
  intros proof.
  induction proof; eauto.
  (* JFIInnerOuterRule *)
  + now apply JFISoundness.
  (* JFIAndElimLRule *)
  + now apply OuterAndElimRuleSoundness with (q := q).
  (* JFIAndElimRRule *)
  + now apply OuterAndElimRuleSoundness with (p := p).
  (* JFIOrIntroLRule *)
  + now apply OuterOrIntroRuleSoundness, or_introl.
  (* JFIOrIntroRRule *)
  + now apply OuterOrIntroRuleSoundness, or_intror.
Qed.
