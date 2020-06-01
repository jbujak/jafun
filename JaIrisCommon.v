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
Require Import Classical_Prop.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module StrMap := FMapAVL.Make(String_as_OT).
Module StrMapFacts := Facts StrMap.
Module NatMapFacts := Facts NatMap.

Definition JFITermEnv : Type := StrMap.t Loc.
Definition JFITypeEnv : Type := StrMap.t JFClassName.
Definition HeapInjection : Type := NatMap.t nat.
Definition HeapPermutation : Type :=  (HeapInjection * HeapInjection).

Inductive JFIVal : Type :=
  | JFINull
  | JFIThis
  | JFIVar (var : string).

Definition JFIValToJFVal val :=
  match val with
  | JFINull => JFVLoc null
  | JFIThis => JFSyn JFThis
  | JFIVar var => JFSyn (JFVar var)
  end.

Definition JFIValsToJFVals vals := List.map JFIValToJFVal vals.

Inductive JFITerm : Set :=
| JFITrue
| JFIFalse
| JFIAnd (t1 : JFITerm) (t2 : JFITerm)
| JFIOr (t1 : JFITerm) (t2 : JFITerm)
| JFIImplies (t1 : JFITerm) (t2 : JFITerm)
| JFIExists (type : JFClassName) (name : string) (t : JFITerm)
| JFIForall (type : JFClassName) (name : string) (t : JFITerm)
| JFIHoare (t1 : JFITerm) (e : JFExpr) (ex : JFEvMode)  (value : string) (t2 : JFITerm)
| JFIEq (val1 : JFIVal) (val2 : JFIVal)
| JFIFieldEq (obj : JFIVal) (field : string) (v : JFIVal)
| JFISep (t1 : JFITerm) (t2 : JFITerm)
| JFIWand (t1 : JFITerm) (t2 : JFITerm).

(* Substitutions *)

Definition JFIStringSubstitute : string -> string -> string -> string :=
  fun str from to => if String.eqb str from then to else str.

Definition JFValSubstituteVal (from : string) (to : JFVal) (val : JFVal) :=
  match val with
  | JFVLoc _ => val
  | JFSyn x =>
    match x with
    | JFVar y => if String.eqb y from then to else val
    | JFThis => val
    end
  end.

Definition JFIValSubstituteVal (from : string) (to : JFIVal) (val : JFIVal) :=
  match val with
  | JFIVar x => if String.eqb x from then to else val
  | _ => val
  end.

Definition JFIValSubstituteVar (from : string) (to : string) (val : JFVal) :=
  JFValSubstituteVal from (JFSyn (JFVar to)) val.

Fixpoint JFIExprSubstituteVal (from : string) (to : JFVal) (e : JFExpr) : JFExpr :=
  match e with
  | JFNew mu C vs => JFNew mu C (List.map (JFValSubstituteVal from to) vs)
  | JFLet C x e1 e2 =>
    if String.eqb x from then
      JFLet C x (JFIExprSubstituteVal from to e1) e2
    else
      JFLet C x (JFIExprSubstituteVal from to e1) (JFIExprSubstituteVal from to e2)
  | JFIf v1 v2 e1 e2 =>
    JFIf (JFValSubstituteVal from to v1) (JFValSubstituteVal from to v2)
         (JFIExprSubstituteVal from to e1) (JFIExprSubstituteVal from to e2)
  | JFInvoke v1 m vs =>
    JFInvoke (JFValSubstituteVal from to v1) m (List.map (JFValSubstituteVal from to) vs)
  | JFAssign (v1,fld) v2 =>
    JFAssign (JFValSubstituteVal from to v1, fld) (JFValSubstituteVal from to v2)
  | JFVal1 v1 =>
    JFVal1 (JFValSubstituteVal from to v1)
  | JFVal2 (v1, fld) =>
    JFVal2 (JFValSubstituteVal from to v1, fld)
  | JFThrow v1 =>
    JFThrow  (JFValSubstituteVal from to v1)
  | JFTry e1 mu C x e2 =>
    if String.eqb x from then
      JFTry (JFIExprSubstituteVal from to e1) mu C x e2
    else
      JFTry (JFIExprSubstituteVal from to e1) mu C x (JFIExprSubstituteVal from to e2)
  end.

Definition JFIExprSubstituteVar (from : string) (to : string) (e : JFExpr) : JFExpr :=
  JFIExprSubstituteVal from (JFSyn (JFVar to)) e.

Fixpoint JFIExprSubstituteVals (froms : list string) (tos: list JFVal) (e : JFExpr) : option JFExpr :=
  match (froms, tos) with
  | ([], []) => Some e
  | (from :: froms1, to :: tos1) => JFIExprSubstituteVals froms1 tos1 (JFIExprSubstituteVal from to e)
  | _ => None
  end.

Fixpoint JFITermSubstituteVal (from : string) (to : JFIVal) (t : JFITerm) : JFITerm :=
    match t with
    | JFITrue => JFITrue
    | JFIFalse => JFIFalse
    | JFIAnd t1 t2 => JFIAnd (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIOr t1 t2 => JFIOr (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIImplies t1 t2 => JFIImplies (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIExists class name term => if String.eqb name from then t else JFIExists class name (JFITermSubstituteVal from to term)
    | JFIForall class name term => if String.eqb name from then t else JFIForall class name (JFITermSubstituteVal from to term)
    | JFIHoare t1 e ex valueName t2 =>
        JFIHoare
          (JFITermSubstituteVal from to t1)
          (JFIExprSubstituteVal from (JFIValToJFVal to) e)
           ex
           valueName
          (JFITermSubstituteVal from to t2)
    | JFIEq val1 val2 => JFIEq (JFIValSubstituteVal from to val1) (JFIValSubstituteVal from to val2)
    | JFIFieldEq obj fieldName val => JFIFieldEq (JFIValSubstituteVal from to obj) fieldName (JFIValSubstituteVal from to val)
    | JFISep t1 t2 => JFISep (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIWand t1 t2 => JFIWand (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    end.

Fixpoint JFITermSubstituteVals (froms : list string) (tos : list JFIVal) (t : JFITerm) : JFITerm :=
  match froms with
    | [] => t
    | from :: froms' =>
      match tos with
        | [] => t
        | to :: tos' => JFITermSubstituteVals froms' tos' (JFITermSubstituteVal from to t)
      end
  end.

Definition JFITermSubstituteVar (from : string) (to : string) (t : JFITerm) : JFITerm :=
    JFITermSubstituteVal from (JFIVar to) t.

Definition JFIValSubstituteEnv (env : JFITermEnv) (val : JFVal)  :=
  StrMap.fold (fun k v a => JFValSubstituteVal k (JFVLoc v) a) env val.

Fixpoint JFIExprSubstituteEnv (env : JFITermEnv) (e : JFExpr) : JFExpr :=
  match e with
  | JFNew mu C vs => JFNew mu C (List.map (JFIValSubstituteEnv env) vs)
  | JFLet C x e1 e2 =>
      JFLet C x (JFIExprSubstituteEnv env e1) (JFIExprSubstituteEnv (StrMap.remove x env) e2)
  | JFIf v1 v2 e1 e2 =>
    JFIf (JFIValSubstituteEnv env v1) (JFIValSubstituteEnv env v2)
         (JFIExprSubstituteEnv env e1) (JFIExprSubstituteEnv env e2)
  | JFInvoke v1 m vs =>
    JFInvoke (JFIValSubstituteEnv env v1) m (List.map (JFIValSubstituteEnv env) vs)
  | JFAssign (v1,fld) v2 =>
    JFAssign (JFIValSubstituteEnv env v1, fld) (JFIValSubstituteEnv env v2)
  | JFVal1 v1 =>
    JFVal1 (JFIValSubstituteEnv env v1)
  | JFVal2 (v1, fld) =>
    JFVal2 (JFIValSubstituteEnv env v1, fld)
  | JFThrow v1 =>
    JFThrow  (JFIValSubstituteEnv env v1)
  | JFTry e1 mu C x e2 =>
      JFTry (JFIExprSubstituteEnv env e1) mu C x (JFIExprSubstituteEnv (StrMap.remove x env) e2)
  end.


Lemma ValEnvSubstitutionPreservesVLoc : forall env loc,
  JFIValSubstituteEnv env (JFVLoc loc) = JFVLoc loc.
Proof.
  intros env loc.
  unfold JFIValSubstituteEnv.
  rewrite StrMap.fold_1.
  induction (StrMap.elements (elt:=Loc) env); auto.
Qed.

Lemma ValEnvSubstitutionPreservesThis : forall env,
  JFIValSubstituteEnv env (JFSyn JFThis) = JFSyn JFThis.
Proof.
  intros env.
  unfold JFIValSubstituteEnv.
  rewrite StrMap.fold_1.
  induction (StrMap.elements (elt:=Loc) env); auto.
Qed.

Lemma StrMapEqKeyEltEquivalence : Equivalence (StrMap.eq_key_elt (elt:=Loc)).
Proof.
  unfold StrMap.eq_key_elt.
  unfold StrMap.Raw.Proofs.PX.eqke.
  split; try firstorder.
  split;
  destruct H, H0.
  + now rewrite H, H0.
  + now rewrite H1, H2.
Qed.

Lemma HeapEqKeyEquivalence : Equivalence (Heap.eq_key (elt:=Obj)).
Proof.
  unfold Heap.eq_key.
  unfold Heap.Raw.Proofs.PX.eqk.
  split; try firstorder.
Qed.

Lemma HeapEqKeyEltEquivalence : Equivalence (Heap.eq_key_elt (elt:=Obj)).
Proof.
  unfold StrMap.eq_key_elt.
  unfold StrMap.Raw.Proofs.PX.eqke.
  split; try firstorder.
  split;
  destruct H, H0.
  + now rewrite H, H0.
  + now rewrite H1, H2.
Qed.

Lemma JFXIdMapEqKeyEltEquivalence : Equivalence (JFXIdMap.eq_key_elt (elt:=Loc)).
Proof.
  unfold StrMap.eq_key_elt.
  unfold StrMap.Raw.Proofs.PX.eqke.
  split; try firstorder.
  split;
  destruct H, H0.
  + now rewrite H, H0.
  + now rewrite H1, H2.
Qed.

Lemma ValEnvSubstitutionPreservesVarNotInEnv : forall env x,
  ~StrMap.In x env ->
  JFIValSubstituteEnv env (JFSyn (JFVar x)) = JFSyn (JFVar x).
Proof.
  intros env x x_not_in_env.
  unfold JFIValSubstituteEnv.
  assert (x_not_in_elements : forall a, List.In a (StrMap.elements (elt:=Loc) env) -> x <> (fst a)).
  + intros (y, l) a_in_elements.
    intros x_is_y.
    simpl in x_is_y.
    rewrite <- x_is_y in *.
    assert (exists_element : exists e, InA (StrMap.eq_key_elt (elt:=Loc)) (x, e) (StrMap.elements (elt:=Loc) env)).
    ++ exists l.
       apply In_InA; try assumption.
       exact StrMapEqKeyEltEquivalence.
    ++ set (elements_in_iff := StrMapFacts.elements_in_iff env x).
       destruct elements_in_iff as (_ & exists_elements_then_in_env).
       set (x_in_env := exists_elements_then_in_env exists_element).
       exact (x_not_in_env x_in_env).
  + rewrite StrMap.fold_1.
    induction (StrMap.elements (elt:=Loc) env); auto.
    unfold fold_left.
    unfold JFValSubstituteVal.
    replace (String.eqb x (fst a)) with false.
    ++ apply IHl.
       intros a0 a0_in_l.
       apply x_not_in_elements.
       apply List.in_cons.
       exact a0_in_l.
    ++ symmetry.
       apply String.eqb_neq.
       apply x_not_in_elements.
       apply List.in_eq.
Qed.

Lemma ValEnvSubstitutionReplacesVarInEnv : forall env x l,
  StrMap.find x env = Some l ->
  JFIValSubstituteEnv env (JFSyn (JFVar x)) = JFVLoc l.
Proof.
Admitted.

Lemma ValEnvSubstitutionReplacesNthVarInEnv : forall var env l vs n,
  StrMap.find var env = Some l ->
  nth_error vs n = Some (JFSyn (JFVar var)) ->
  nth_error (map (JFIValSubstituteEnv env) vs) n = Some (JFVLoc l).
Proof.
Admitted.

Lemma ExprEnvSubstitutionPreservesVLoc : forall env loc,
  JFIExprSubstituteEnv env (JFVal1 (JFVLoc loc)) = JFVal1 (JFVLoc loc).
Proof.
  intros env loc.
  unfold JFIExprSubstituteEnv.
  rewrite ValEnvSubstitutionPreservesVLoc.
  trivial.
Qed.

Lemma ValSubstituteIdentity : forall x v,
  JFValSubstituteVal x (JFSyn (JFVar x)) v = v.
Proof.
  intros x v.
  unfold JFValSubstituteVal.
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
  map (JFValSubstituteVal x (JFSyn (JFVar x))) vs = vs.
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


Lemma ValSubstitutePreservesDifferentVar : forall x y v,
  x <> y -> JFValSubstituteVal x v (JFSyn (JFVar y)) = (JFSyn (JFVar y)).
Proof.
Admitted.

Lemma SubstExprEqExprSubstituteVal : forall e from to,
  substExpr (JFVar from) to e = JFIExprSubstituteVal from (JFVLoc to) e.
Proof.
  admit. (* TODO *)
Admitted.

Lemma SubstituteValEnvComm : forall x l v env,
  ~StrMap.In x env ->
  (JFIValSubstituteEnv env (JFValSubstituteVal x (JFVLoc l) v)) =
  (JFValSubstituteVal x (JFVLoc l) (JFIValSubstituteEnv env v)).
Proof.
  intros x l v env.
  intros x_not_in_env.
  destruct v.
  + unfold JFValSubstituteVal.
    rewrite ValEnvSubstitutionPreservesVLoc.
    trivial.
  + destruct x0.
    ++ destruct (Classical_Prop.classic (x = x0)) as [x_eq_x0 | x_ne_x0].
       +++ rewrite <- x_eq_x0 in *.
           rewrite ValEnvSubstitutionPreservesVarNotInEnv; try assumption.
           unfold JFValSubstituteVal.
           destruct (String.eqb x x).
           - rewrite ValEnvSubstitutionPreservesVLoc.
             trivial.
           - rewrite ValEnvSubstitutionPreservesVarNotInEnv; try assumption.
             trivial.
       +++ rewrite ValSubstitutePreservesDifferentVar; try assumption.
           admit.
    ++ unfold JFValSubstituteVal.
       rewrite ValEnvSubstitutionPreservesThis.
       trivial.
Admitted.

Lemma SubstituteExprEnvComm : forall x l e env,
  ~StrMap.In x env ->
  JFIExprSubstituteEnv env (JFIExprSubstituteVal x (JFVLoc l) e) =
  JFIExprSubstituteVal x (JFVLoc l) (JFIExprSubstituteEnv env e).
Proof.
  intros x l e env.
  intros not_x_in_env.
  induction e.
  + simpl.
    induction vs.
    ++ auto.
    ++ unfold map.
       rewrite SubstituteValEnvComm; try apply not_x_in_env.
       injection IHvs as map_eq.
       unfold map in map_eq.
       rewrite map_eq.
       trivial.
  + 
Admitted.

Lemma RemoveVarFromEnv : forall x v l e env,
  JFIExprSubstituteVal x (JFVLoc l) (JFIExprSubstituteEnv (StrMap.remove x env) e) =
  JFIExprSubstituteEnv (StrMap.add v l env) (JFIExprSubstituteVar x v e).
Proof.
Admitted.


