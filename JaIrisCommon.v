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

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module StrMap := FMapAVL.Make(String_as_OT).

Definition JFITermEnv : Type := StrMap.t Loc.
Definition JFITypeEnv : Type := StrMap.t JFClassName.

Inductive JFITerm : Set :=
| JFITrue
| JFIFalse
| JFIAnd (t1 : JFITerm) (t2 : JFITerm)
| JFIOr (t1 : JFITerm) (t2 : JFITerm)
| JFIImplies (t1 : JFITerm) (t2 : JFITerm)
| JFIExists (type : JFClassName) (name : string) (t : JFITerm)
| JFIForall (type : JFClassName) (name : string) (t : JFITerm)
| JFIHoare (t1 : JFITerm) (e : JFExpr) (value : string) (t2 : JFITerm)
| JFIEq (val1 : JFVal) (val2 : JFVal)
| JFIFieldEq (obj : JFVal) (field : string) (v : JFVal)
| JFISep (t1 : JFITerm) (t2 : JFITerm)
| JFIWand (t1 : JFITerm) (t2 : JFITerm).

(* Substitutions *)

Definition JFIStringSubstitute : string -> string -> string -> string :=
  fun str from to => if String.eqb str from then to else str.

Definition JFIValSubstituteVal (from : string) (to : JFVal) (val : JFVal) :=
  match val with
  | JFVLoc _ => val
  | JFSyn x =>
    match x with
    | JFVar y => if String.eqb y from then to else val
    | JFThis => val
    end
  end.

Definition JFIValSubstituteVar (from : string) (to : string) (val : JFVal) :=
  JFIValSubstituteVal from (JFSyn (JFVar to)) val.

Fixpoint JFIExprSubstituteVal (from : string) (to : JFVal) (e : JFExpr) : JFExpr :=
  match e with
  | JFNew mu C vs => JFNew mu C (List.map (JFIValSubstituteVal from to) vs)
  | JFLet C x e1 e2 =>
    if String.eqb x from then
      JFLet C x (JFIExprSubstituteVal from to e1) e2
    else
      JFLet C x (JFIExprSubstituteVal from to e1) (JFIExprSubstituteVal from to e2)
  | JFIf v1 v2 e1 e2 =>
    JFIf (JFIValSubstituteVal from to v1) (JFIValSubstituteVal from to v2)
         (JFIExprSubstituteVal from to e1) (JFIExprSubstituteVal from to e2)
  | JFInvoke v1 m vs =>
    JFInvoke (JFIValSubstituteVal from to v1) m (List.map (JFIValSubstituteVal from to) vs)
  | JFAssign (v1,fld) v2 =>
    JFAssign (JFIValSubstituteVal from to v1, fld) (JFIValSubstituteVal from to v2)
  | JFVal1 v1 =>
    JFVal1 (JFIValSubstituteVal from to v1)
  | JFVal2 (v1, fld) =>
    JFVal2 (JFIValSubstituteVal from to v1, fld)
  | JFThrow v1 =>
    JFThrow  (JFIValSubstituteVal from to v1)
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

Fixpoint JFITermSubstituteVal (from : string) (to : JFVal) (t : JFITerm) : JFITerm :=
    match t with
    | JFITrue => JFITrue
    | JFIFalse => JFIFalse
    | JFIAnd t1 t2 => JFIAnd (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIOr t1 t2 => JFIOr (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIImplies t1 t2 => JFIImplies (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIExists class name term => if String.eqb name from then t else JFIExists class name (JFITermSubstituteVal from to term)
    | JFIForall class name term => if String.eqb name from then t else JFIForall class name (JFITermSubstituteVal from to term)
    | JFIHoare t1 e valueName t2 =>
        JFIHoare
          (JFITermSubstituteVal from to t1)
          (JFIExprSubstituteVal from to e)
          valueName
          (JFITermSubstituteVal from to t2)
    | JFIEq val1 val2 => JFIEq (JFIValSubstituteVal from to val1) (JFIValSubstituteVal from to val2)
    | JFIFieldEq obj fieldName val => JFIFieldEq (JFIValSubstituteVal from to obj) fieldName (JFIValSubstituteVal from to val)
    | JFISep t1 t2 => JFISep (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    | JFIWand t1 t2 => JFIWand (JFITermSubstituteVal from to t1) (JFITermSubstituteVal from to t2)
    end.

Fixpoint JFITermSubstituteVals (froms : list string) (tos : list JFVal) (t : JFITerm) : JFITerm :=
  match froms with
    | [] => t
    | from :: froms' =>
      match tos with
        | [] => t
        | to :: tos' => JFITermSubstituteVals froms' tos' (JFITermSubstituteVal from to t)
      end
  end.

Definition JFITermSubstituteVar (from : string) (to : string) (t : JFITerm) : JFITerm :=
    JFITermSubstituteVal from (JFSyn (JFVar to)) t.


Definition JFIValSubstituteEnv (env : JFITermEnv) (val : JFVal)  :=
  StrMap.fold (fun k v a => JFIValSubstituteVal k (JFVLoc v) a) env val.

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
