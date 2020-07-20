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
Require Import JaIris.
Require Import Classical_Prop.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module StrMap := JaIrisCommon.StrMap.

Definition FreeVarsInTermAreInGammaOrX e (gamma : JFITypeEnv) x :=
  forall y, VarFreeInTerm y e -> (y = x \/ StrMap.In y gamma).

Lemma FreeVarsInTrue : forall gamma,
  FreeVarsInTermAreInGamma JFITrue gamma <-> True.
Proof.
Admitted.

Lemma FreeVarsInFalse : forall gamma,
  FreeVarsInTermAreInGamma JFIFalse gamma <-> True.
Proof.
Admitted.

Lemma FreeVarsInAnd : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIAnd p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
Admitted.

Lemma FreeVarsInOr : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIOr p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
Admitted.

Lemma FreeVarsInImplies : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIImplies p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
Admitted.

Lemma FreeVarsInHoare : forall gamma p e ex v q,
  FreeVarsInTermAreInGamma (JFIHoare p e ex v q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInExprAreInGamma e gamma /\
    (FreeVarsInTermAreInGammaOrX q gamma v)).
Proof.
Admitted.

Lemma FreeVarsInEq : forall gamma v1 v2,
  FreeVarsInTermAreInGamma (JFIEq v1 v2) gamma <->
  (FreeVarsInValAreInGamma v1 gamma /\ FreeVarsInValAreInGamma v2 gamma).
Proof.
Admitted.
Hint Resolve FreeVarsInEq : free_vars_in_gamma.

Lemma FreeVarsInFieldEq : forall gamma o f v,
  FreeVarsInTermAreInGamma (JFIFieldEq o f v) gamma <->
  (FreeVarsInValAreInGamma o gamma /\ FreeVarsInValAreInGamma v gamma).
Proof.
Admitted.
Hint Resolve FreeVarsInEq : free_vars_in_gamma.

Lemma FreeVarsInSep : forall gamma p q,
  FreeVarsInTermAreInGamma (JFISep p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
Admitted.

Lemma FreeVarsInWand : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIWand p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
Admitted.


Ltac try_solve_free_vars :=
  try rewrite !FreeVarsInAnd in *;
  try rewrite !FreeVarsInOr in *;
  try rewrite !FreeVarsInImplies in *;
  try rewrite !FreeVarsInEq in *;
  try rewrite !FreeVarsInFieldEq in *;
  try rewrite !FreeVarsInSep in *;
  try rewrite !FreeVarsInWand in *;
  try rewrite !FreeVarsInTrue in *;
  try rewrite !FreeVarsInFalse in *;
  try easy.

Lemma FreeVarsAreInGamma : forall decls gamma p q,
  JFIProves decls gamma p q ->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  intros decls gamma p q proof.
  induction proof; try_solve_free_vars.
  (* TODO Hoare *)
Admitted.