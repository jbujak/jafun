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

Ltac free_vars_in_binop :=
  intros gamma p q;
  split;
  [ intros free_vars;
    split; intros x x_free; apply (free_vars x);
    [ now apply or_introl
    | now apply or_intror]
  | intros (free_in_p & free_in_q);
    intros x x_free;
    destruct x_free;
    [ now apply (free_in_p x)
    | now apply (free_in_q x)
    ]
  ].

Lemma FreeVarsInAnd : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIAnd p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  free_vars_in_binop.
Qed.

Lemma FreeVarsInOr : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIOr p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  free_vars_in_binop.
Qed.

Lemma FreeVarsInImplies : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIImplies p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  free_vars_in_binop.
Qed.

Lemma FreeVarsInHoare : forall gamma p e ex v q,
  FreeVarsInTermAreInGamma (JFIHoare p e ex v q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInExprAreInGamma e gamma /\
    (FreeVarsInTermAreInGammaOrX q gamma v)).
Proof.
  intros gamma p e ex v q.
  split.
  + intros free_in_hoare.
    split; [ | split]; intros x x_free.
    ++ apply (free_in_hoare x).
       now apply or_introl.
    ++ apply (free_in_hoare x).
       now apply or_intror, or_introl.
    ++ destruct (Classical_Prop.classic (v = x)).
         now apply or_introl.
       apply or_intror, (free_in_hoare x).
       simpl.
       apply or_intror, or_intror.
       apply String.eqb_neq in H.
       now rewrite H.
  + intros (free_in_p & free_in_e & free_in_q_or_v).
    unfold FreeVarsInTermAreInGamma.
    intros x x_free.
    destruct (x_free) as [ x_free_in_p | [ x_free_in_e | x_free_in_q_or_v]].
    ++ now apply free_in_p.
    ++ now apply free_in_e.
    ++ assert (v <> x).
         intros H.
         apply String.eqb_eq in H.
         now rewrite H in x_free_in_q_or_v.
       rewrite (proj2 (String.eqb_neq v x) H) in x_free_in_q_or_v.
       destruct (free_in_q_or_v x x_free_in_q_or_v); try easy.
       exfalso.
       now apply H.
Qed.

Lemma FreeVarsInEq : forall gamma v1 v2,
  FreeVarsInTermAreInGamma (JFIEq v1 v2) gamma <->
  (FreeVarsInValAreInGamma v1 gamma /\ FreeVarsInValAreInGamma v2 gamma).
Proof.
  free_vars_in_binop.
Qed.

Lemma FreeVarsInFieldEq : forall gamma o f v,
  FreeVarsInTermAreInGamma (JFIFieldEq o f v) gamma <->
  (FreeVarsInValAreInGamma o gamma /\ FreeVarsInValAreInGamma v gamma).
Proof.
free_vars_in_binop.
Qed.

Lemma FreeVarsInSep : forall gamma p q,
  FreeVarsInTermAreInGamma (JFISep p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  free_vars_in_binop.
Qed.

Lemma FreeVarsInWand : forall gamma p q,
  FreeVarsInTermAreInGamma (JFIWand p q) gamma <->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  free_vars_in_binop.
Qed.

Ltac try_solve_free_vars :=
  try rewrite !FreeVarsInAnd in *;
  try rewrite !FreeVarsInOr in *;
  try rewrite !FreeVarsInImplies in *;
  try rewrite !FreeVarsInEq in *;
  try rewrite !FreeVarsInFieldEq in *;
  try rewrite !FreeVarsInSep in *;
  try rewrite !FreeVarsInWand in *;
  try easy.

Lemma FreeVarsAreInGamma : forall decls gamma p q,
  JFIProves decls gamma p q ->
  (FreeVarsInTermAreInGamma p gamma /\ FreeVarsInTermAreInGamma q gamma).
Proof.
  intros decls gamma p q proof.
  induction proof; try_solve_free_vars.
  (* TODO Hoare *)
Admitted.