Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.
Require Import JaSyntax.
Require Import Jafun.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module StrMap := FMapAVL.Make(String_as_OT).

Inductive JFIVarType : Set :=
| JFILoc
| JFIObj.

Inductive JFITermEnvItem : Type :=
| JFIEnvLoc (l : Loc)
| JFIEnvObj (o : Obj).

Definition JFITermEnv : Type := StrMap.t JFITermEnvItem.

Inductive JFITerm : Set :=
| JFITrue
| JFIFalse
| JFIAnd (t1 : JFITerm) (t2 : JFITerm)
| JFIOr (t1 : JFITerm) (t2 : JFITerm)
| JFIExists (type : JFIVarType) (name : string) (t : JFITerm)
| JFIForall (type : JFIVarType) (name : string) (t : JFITerm)
| JFIHoare (t1 : JFITerm) (e : JFExpr) (t2 : JFITerm)
| JFISep (t1 : JFITerm) (t2 : JFITerm)
| JFIWand (t1 : JFITerm) (t2 : JFITerm)
| JFIEq (type : JFIVarType) (var1 : string) (var2 : string)
| JFIPointsTo (loc : string) (obj : string).

Definition JFEval : JFExpr -> Heap -> list Heap -> Heap -> Prop :=
  fun e h0 hs hn => True.

Fixpoint JFIHeapSatisfies (h : Heap) (t : JFITerm) (env : JFITermEnv) : Prop :=
  match t with
    | JFITrue => True
    | JFIFalse => False
    | JFIAnd t1 t2 => JFIHeapSatisfies h t1 env /\ JFIHeapSatisfies h t2 env
    | JFIOr t1 t2 => JFIHeapSatisfies h t1 env \/ JFIHeapSatisfies h t2 env
    | JFIExists JFILoc name term => exists l : Loc,
        let env1 := StrMap.add name (JFIEnvLoc l) env in JFIHeapSatisfies h term env1
    | JFIExists JFIObj name term => True (* TODO *)
    | JFIForall type name term => True (* TODO *)
    | JFIHoare t1 e t2 =>
        forall h0 hs hn, (JFIHeapSatisfies h0 t1 env) -> (JFEval e h0 hs hn) -> (JFIHeapSatisfies hn t2 env)
    | JFISep t1 t2 => True (* TODO *)
    | JFIWand t1 t2 => True (* TODO *)
    | JFIEq JFILoc loc1 loc2 => True (* TODO *)
    | JFIEq JFIObj obj1 obj2 => True (* TODO *)
    | JFIPointsTo loc obj => True (* TODO *)
  end.

Inductive JFIProof : Set := (* TODO *)
| JFIEmpty.

Definition JFIProofValid : JFIProof -> JFITerm -> Prop := (* TODO *)
  fun p t => True.

Theorem JFISoundness : forall p t h, (JFIProofValid p t) -> (JFIHeapSatisfies h t (StrMap.empty JFIQuantifierVar)).
Proof.
admit. (*TODO*)
Admitted.