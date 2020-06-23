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
Module HeapFacts := Facts Heap.

Definition JFITermEnv : Type := StrMap.t Loc.
Definition JFITypeEnv : Type := StrMap.t JFClassName.
Definition HeapInjection : Type := NatMap.t nat.
Definition HeapPermutation : Type :=  (HeapInjection * HeapInjection).

Definition JFIHeapsDisjoint (h1 : Heap) (h2 : Heap) : Prop := forall l : nat,
  (~(Heap.In l h1 /\ Heap.In l h2)).

Definition JFISubheap (h1 : Heap) (h2 : Heap) : Prop := forall (l : nat) o,
  Heap.MapsTo l o h1 -> Heap.MapsTo l o h2.

Definition JFIHeapsUnion (h1 : Heap) (h2 : Heap) (h : Heap) : Prop :=
  JFISubheap h1 h /\ JFISubheap h2 h /\ forall l, Heap.In l h -> (Heap.In l h1 \/ Heap.In l h2).

Definition JFIDisjointUnion (h1 : Heap) (h2 : Heap) (h : Heap) : Prop :=
  JFIHeapsUnion h1 h2 h /\ JFIHeapsDisjoint h1 h2.

Definition HeapConsistent (h : Heap) := forall n obj f f_n,
  Heap.MapsTo n obj h ->
  JFXIdMap.MapsTo f (JFLoc f_n) (fst obj) ->
  exists obj', Heap.MapsTo f_n obj' h.

Definition JFILocOfType (l : Loc) (h : Heap) (c : JFClassName) : Prop :=
  match l with
    | null => True
    | JFLoc n =>
      match (Heap.find n h) with
        | Some (_, objClass) => c = objClass (* TODO also subclasses *)
        | None => False
      end
  end.

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
| JFIHoare (t1 : JFITerm) (e : JFExpr) (ex : JFEvMode)  (value : string) (t2 : JFITerm)
| JFIEq (val1 : JFIVal) (val2 : JFIVal)
| JFIFieldEq (obj : JFIVal) (field : string) (v : JFIVal)
| JFISep (t1 : JFITerm) (t2 : JFITerm)
| JFIWand (t1 : JFITerm) (t2 : JFITerm).

Inductive JFIOuterTerm : Set :=
| JFIOuterAnd (t1 : JFIOuterTerm) (t2 : JFIOuterTerm)
| JFIOuterOr (t1 : JFIOuterTerm) (t2 : JFIOuterTerm)
| JFIExists (type : JFClassName) (name : string) (t : JFIOuterTerm)
| JFIInner (t : JFITerm).

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

Fixpoint JFIOuterTermSubstituteVal (from : string) (to : JFIVal) (t : JFIOuterTerm) : JFIOuterTerm :=
  match t with
  | JFIOuterAnd t1 t2 => JFIOuterAnd (JFIOuterTermSubstituteVal from to t1) (JFIOuterTermSubstituteVal from to t2)
  | JFIOuterOr t1 t2 => JFIOuterOr (JFIOuterTermSubstituteVal from to t1) (JFIOuterTermSubstituteVal from to t2)
  | JFIExists class name term =>
      if String.eqb name from then t else JFIExists class name (JFIOuterTermSubstituteVal from to term)
  | JFIInner t => JFIInner (JFITermSubstituteVal from to t)
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

Definition HeapEq (h1 h2 : Heap) :=
  forall n, Heap.find n h1 = Heap.find n h2.

Lemma EqImpliesHeapEq : forall h1 h2,
  h1 = h2 -> HeapEq h1 h2.
Proof.
Admitted.

Lemma HeapEqTrans : forall h1 h2 h3,
  HeapEq h1 h2 ->
  HeapEq h2 h3 ->
  HeapEq h1 h3.
Proof.
Admitted.

Lemma HeapEqSym : forall h1 h2,
  HeapEq h1 h2 -> HeapEq h2 h1.
Proof.
Admitted.

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

Lemma HeapsUnionSymmetry : forall h1 h2 h,
  JFIHeapsUnion h1 h2 h -> JFIHeapsUnion h2 h1 h.
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

Lemma DisjointUnionSymmetry : forall h1 h2 h,
  JFIDisjointUnion h1 h2 h -> JFIDisjointUnion h2 h1 h.
Proof.
  intros h1 h2 h (union & disjoint).
  split.
  now apply HeapsUnionSymmetry.
  intros n (n_in_h2 & n_in_h1).
  now apply (disjoint n).
Qed.

Lemma SubheapOfUnion : forall h1 h2 h, JFIHeapsUnion h1 h2 h -> JFISubheap h1 h.
Proof.
  intros h1 h2 h h_is_union.
  unfold JFIHeapsUnion in h_is_union.
  apply h_is_union.
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

Lemma SubstExprComm : forall f1 f2 l1 l2 e,
  f1 <> f2 ->
  substExpr f1 l1 (substExpr f2 l2 e) = substExpr f2 l2 (substExpr f1 l1 e).
Proof.
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

Lemma SubsituteVarIdentity : forall x e,
  JFIExprSubstituteVar x x e = e.
Proof.
Admitted.

Lemma neq_symmetry : forall t (x : t) (y : t), x <> y -> y <> x.
Proof.
  intros t x y.
  intros x_neq_y.
  unfold not.
  intros y_eq_x.
  symmetry in y_eq_x.
  exact (x_neq_y y_eq_x).
Qed.

Ltac Loc_dec_eq l1 l2 l1_eq_l2 :=
  destruct Loc_dec as [_ | l1_neq_l2];
  [ | exfalso; apply l1_neq_l2; exact l1_eq_l2].

Ltac Loc_dec_neq l1 l2 l1_neq_l2 :=
  destruct Loc_dec as [l1_eq_l2 | _];
  [exfalso; apply l1_neq_l2; exact l1_eq_l2 | ].

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

Lemma FindInUnion : forall h1 h2 h n o,
  JFIDisjointUnion h1 h2 h ->
  Heap.find n h1 = Some o ->
  Heap.find n h = Some o.
Proof.
  intros h1 h2 h n o.
  intros disjoint n_o.
  destruct disjoint as ((subheap & _) & _).
  rewrite <-HeapFacts.find_mapsto_iff in *.
  now apply subheap.
Qed.

Lemma ExtendDisjointUnion : forall h1 h2 h n o,
  JFIDisjointUnion h1 h2 h ->
  (~Heap.In n h2) ->
  JFIDisjointUnion (Heap.add n o h1) h2 (Heap.add n o h).
Proof.
  intros h1 h2 h n o.
  intros union n_not_in_h2.
  destruct union as ((h1_subheap & h2_subheap & union) & disjoint).
  split; [ split; [| split] |].
  + intros n' o'.
    rewrite !HeapFacts.find_mapsto_iff.
    destruct (Classical_Prop.classic (n = n')).
    ++ now rewrite !HeapFacts.add_eq_o.
    ++ rewrite !HeapFacts.add_neq_o; trivial.
       assert (subheap := h1_subheap n' o').
       now rewrite !HeapFacts.find_mapsto_iff in subheap.
  + intros n' o' n'_o'.
    destruct (Classical_Prop.classic (n = n')).
    ++ exfalso.
       apply n_not_in_h2.
       rewrite <-H in n'_o'.
       apply HeapFacts.elements_in_iff.
       apply HeapFacts.elements_mapsto_iff in n'_o'.
       now exists o'.
    ++ apply HeapFacts.find_mapsto_iff.
       rewrite !HeapFacts.add_neq_o; trivial.
       apply HeapFacts.find_mapsto_iff.
       now apply h2_subheap.
  + intros l l_in_add.
    apply HeapFacts.elements_in_iff in l_in_add as (o' & l_o').
    apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in l_o'.
    destruct (Classical_Prop.classic (n = l)).
    ++ apply or_introl.
       rewrite H.
       apply HeapFacts.elements_in_iff.
       exists o.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
       now rewrite HeapFacts.add_eq_o.
    ++ rewrite HeapFacts.add_neq_o in l_o'; trivial.
       destruct (union l).
       +++ apply HeapFacts.elements_in_iff.
           exists o'.
           now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
       +++ apply or_introl.
           apply HeapFacts.elements_in_iff in H0 as (o'' & l_o'').
           apply HeapFacts.elements_in_iff.
           exists o''.
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
           rewrite HeapFacts.add_neq_o; trivial.
           now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in l_o''.
       +++ now apply or_intror.
  + intros l l_in_both.
    destruct (Classical_Prop.classic (n = l)).
    ++ rewrite H in *.
       now apply n_not_in_h2.
    ++ destruct l_in_both as (l_in_h1 & l_in_h2).
       apply (disjoint l).
       split; trivial.
       apply HeapFacts.elements_in_iff in l_in_h1 as (o' & l_o').
       apply HeapFacts.elements_in_iff.
       exists o'.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in l_o'.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
       now rewrite HeapFacts.add_neq_o in l_o'.
Qed.


