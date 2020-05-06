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
Require Import Bool.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module StrMap := JaIrisCommon.StrMap.
Module HeapFacts := Facts Heap.

(* Heaps *)

Definition JFIHeapsDisjoint (h1 : Heap) (h2 : Heap) : Prop := forall l : nat,
  (~(Heap.In l h1 /\ Heap.In l h2)).

Definition JFISubheap (h1 : Heap) (h2 : Heap) : Prop := forall l : nat,
  Heap.In l h1 -> Heap.In l h2.

Definition JFIHeapsUnion (h1 : Heap) (h2 : Heap) (h : Heap) : Prop :=
  JFISubheap h1 h /\ JFISubheap h2 h /\ forall l, Heap.In l h -> (Heap.In l h1 \/ Heap.In l h2).


Definition JFIObjFieldEq (objLoc : Loc) (fieldName : string) (loc : Loc) (h : Heap) : Prop :=
  match objLoc with
    | null => False
    | JFLoc n =>
        match (Heap.find n h) with
          | None => False
          | Some obj => 
              match obj with
                | (rawObj, className) =>
                  match (JFXIdMap.find fieldName rawObj) with
                    | Some val => val = loc
                    | None => False
                  end
              end
        end
   end.

Definition JFIRawObjEq (obj1 : RawObj) (obj2 : RawObj) : Prop :=
  forall id, match (JFXIdMap.find id obj1, JFXIdMap.find id obj2) with
    | (Some l1, Some l2) => l1 = l2
    | (None, None) => True
    | _ => False
  end.

Definition JFIObjEq (obj1 : Obj) (obj2 : Obj) : Prop := 
  match (obj1, obj2) with
    | ((rawObj1, className1), (rawObj2, className2)) => className1 = className2 /\ JFIRawObjEq rawObj1 rawObj2
  end.

Definition JFIGetLocType (n : nat) (h : Heap) : option JFClassName :=
  match (Heap.find n h) with
    | None => None
    | Some (_, objClass) => Some objClass
  end.

Definition JFILocOfType (l : Loc) (h : Heap) (c : JFClassName) : Prop :=
  match l with
    | null => True
    | JFLoc n =>
      match (Heap.find n h) with
        | Some (_, objClass) => c = objClass (* TODO also subclasses *)
        | None => False
      end
  end.

Definition JFIValToLoc (val : JFVal) (env : JFITermEnv) : option Loc :=
  match val with
    | JFVLoc loc => Some loc
    | JFSyn (JFVar x) => StrMap.find x env
    | JFSyn JFThis => Some null (* TODO *)
  end.


(* Semantics *)

Fixpoint JFIHeapSatisfiesInEnv (h : Heap) (t : JFITerm) (env : JFITermEnv) (CC : JFProgram) : Prop :=
  match t with
    | JFITrue => True
    | JFIFalse => False
    | JFIAnd t1 t2 => JFIHeapSatisfiesInEnv h t1 env CC /\ JFIHeapSatisfiesInEnv h t2 env CC
    | JFIOr t1 t2 => JFIHeapSatisfiesInEnv h t1 env CC \/ JFIHeapSatisfiesInEnv h t2 env CC
    | JFIImplies t1 t2 => ~(JFIHeapSatisfiesInEnv h t1 env CC) \/ JFIHeapSatisfiesInEnv h t2 env CC
    | JFIExists class name term => exists l : Loc,
        let env1 := StrMap.add name l env
        in JFILocOfType l h class /\ JFIHeapSatisfiesInEnv h term env1 CC
    | JFIForall class name term => forall l : Loc,
        let env1 := StrMap.add name l env
        in JFILocOfType l h class -> JFIHeapSatisfiesInEnv h term env1 CC
    | JFIHoare t1 e valueName t2 => forall confs hn res,
        let newEnv := StrMap.add valueName res env
        in (JFIHeapSatisfiesInEnv h t1 env CC) ->
           (JFIEvalInEnv h e confs hn res env CC) ->
            JFIHeapSatisfiesInEnv hn t2 newEnv CC
    | JFIEq val1 val2 =>
        let l1 := JFIValToLoc val1 env
        in let l2 := JFIValToLoc val2 env
        in match (l1, l2) with
           | (Some loc1, Some loc2) => loc1 = loc2
           | _ => False
        end
    | JFIFieldEq obj fieldName val =>
        let l1 := JFIValToLoc obj env
        in let l2 := JFIValToLoc val env
        in match (l1, l2) with
          | (Some objLoc, Some valLoc) => JFIObjFieldEq objLoc fieldName valLoc h
          | _ => False
        end
    | JFISep t1 t2 => exists (h1 : Heap) (h2 : Heap),
        (JFIHeapsUnion h1 h2 h /\ JFIHeapsDisjoint h1 h2) /\
        (JFIHeapSatisfiesInEnv h1 t1 env CC /\ JFIHeapSatisfiesInEnv h2 t2 env CC)
    | JFIWand t1 t2 => exists (h1 : Heap) (h_h1 : Heap),
        (JFIHeapsDisjoint h h1 /\ JFIHeapsUnion h h1 h_h1) /\ 
        (JFIHeapSatisfiesInEnv h1 t1 env CC /\ JFIHeapSatisfiesInEnv h_h1 t2 env CC)
  end.

Definition JFIGammaMatchEnv (h : Heap) (gamma : JFITypeEnv) (env : JFITermEnv) :=
  forall var_name var_loc var_type,
    (StrMap.In var_name gamma <-> StrMap.In var_name env) /\
    ((StrMap.find var_name gamma = Some var_type) ->
    (StrMap.find var_name env = Some var_loc) ->
     JFILocOfType var_loc h var_type).

Definition JFIHeapSatisfies (h : Heap) (t : JFITerm) (gamma : JFITypeEnv) (CC : JFProgram) : Prop :=
  forall env, JFIGammaMatchEnv h gamma env -> JFIHeapSatisfiesInEnv h t env CC.

(* Persistence *)

Fixpoint JFITermPersistent (t : JFITerm) : Prop :=
  match t with
  | JFITrue => True
  | JFIFalse => True
  | JFIAnd t1 t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIOr t1 t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIImplies t1 t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIExists class name term => JFITermPersistent term
  | JFIForall class name term => JFITermPersistent term
  | JFIHoare t1 e valueName t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIEq val1 val2 => True
  | JFIFieldEq obj fieldName val => False
  | JFISep t1 t2 => False
  | JFIWand t1 t2 => False
  end.

(* Program structure for proofs *)

Inductive JFIInvariantType : Type :=
| JFIInvariant (cn : string) (mn : string) (precondition : JFITerm) (var : string) (postcondition : JFITerm).

Inductive JFIDeclsType : Type :=
| JFIDecls (prog : JFProgram) (invariants : list JFIInvariantType) (class : JFClassDeclaration) (method : JFMethodDeclaration).

Definition JFIDeclsProg (decls : JFIDeclsType) : JFProgram :=
  match decls with JFIDecls prog _ _ _ => prog end.
Definition JFIDeclsInvariants (decls : JFIDeclsType) : list JFIInvariantType :=
  match decls with JFIDecls _ invariants _ _ => invariants end.
Definition JFIDeclsCDecl (decls : JFIDeclsType) : JFClassDeclaration :=
  match decls with JFIDecls _ _ class _ => class end.
Definition JFIDeclsMD (decls : JFIDeclsType) : JFMethodDeclaration :=
  match decls with JFIDecls _ _ _ method => method end.

(* Types *)

Definition JFITypes : JFIDeclsType -> JFExEnv -> JFEnv -> JFExpr -> JFCId -> Prop :=
  fun decls exEnv env expr cid =>
    types (JFIDeclsProg decls) (JFIDeclsCDecl decls) (JFIDeclsMD decls) exEnv env expr (cid, JFrwr).

Definition JFIRefType (decls : JFIDeclsType) (gamma : JFITypeEnv) (ref : JFRef) : option JFClassName :=
  match ref with
  | JFVar v => StrMap.find v gamma
  | JFThis => Some (name_of_cd (JFIDeclsCDecl decls))
  end.

(* TODO do wywalenia *)
Definition JFIGammaAdd (x : string) (type : JFClassName) (gamma : JFITypeEnv) : JFITypeEnv :=
  StrMap.add x type gamma.

Definition JFIGammaAddNew (x : string) (type : JFClassName) (gamma : JFITypeEnv) : option JFITypeEnv :=
  if StrMap.mem x gamma then None else Some (StrMap.add x type gamma).

Definition JFIEnvAddNew (x : string) (l : Loc) (env : JFITermEnv) : option JFITermEnv :=
  if StrMap.mem x env then None else Some (StrMap.add x l env).

Definition JFIVarFreshInVal (x : string) (v : JFVal) :=
  match v with
    | JFVLoc _ => True
    | JFSyn (JFVar y) => x <> y
    | JFSyn JFThis => True
  end.

Fixpoint JFIVarFreshInTerm (x : string) (t : JFITerm) :=
  match t with
    | JFITrue => True
    | JFIFalse => True
    | JFIAnd t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
    | JFIOr t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
    | JFIImplies t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
    | JFIExists class name term => (* TODO maybe allow x = name *)
        if String.eqb name x then False else JFIVarFreshInTerm x term
    | JFIForall class name term => (* TODO maybe allow x = name *)
        if String.eqb name x then False else JFIVarFreshInTerm x term
    | JFIHoare t1 e name t2 => (* TODO maybe allow x = name *)
        if String.eqb name x then False else (JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2)
    | JFIEq val1 val2 => JFIVarFreshInVal x val1 /\ JFIVarFreshInVal x val2
    | JFIFieldEq obj fieldName val => JFIVarFreshInVal x obj /\ JFIVarFreshInVal x val
    | JFISep t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
    | JFIWand t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
  end.

Definition JFIRefFreshInTerm (v : JFRef) (t : JFITerm) :=
  match v with
  | JFVar x => JFIVarFreshInTerm x t
  | JFThis => True
  end.

Inductive JFIProves : JFIDeclsType -> JFITypeEnv -> JFITerm -> JFITerm -> Prop :=

(* Rules for intuitionistic logic with equality *) 

| JFIAsmRule :
    forall decls gamma p,
      (*-----------------*)
      JFIProves decls gamma p p

| JFITransRule :
    forall q decls gamma p r,
      (JFIProves decls gamma p q) ->
      (JFIProves decls gamma q r) ->
      (*----------------*)
      JFIProves decls gamma p r

| JFIEqRule :
    forall q x v1 v2 r decls gamma p,
      (r = JFITermSubstituteVal x v2 q) ->
      (JFIProves decls gamma p (JFITermSubstituteVal x v1 q)) ->
      (JFIProves decls gamma p (JFIEq v1 v2)) ->
      (*------------------------------------------*)
      JFIProves decls gamma p r

| JFIEqReflRule :
    forall decls gamma p v,
      (*----------------------------------*)
      JFIProves decls gamma p (JFIEq v v)

| JFIEqSymRule :
    forall decls gamma v1 v2 p,
      (JFIProves decls gamma p (JFIEq v1 v2)) ->
      (*-----------------------------------*)
      JFIProves decls gamma p (JFIEq v2 v1)

| JFIFalseElimRule :
    forall decls gamma p q, 
      (JFIProves decls gamma p JFIFalse) ->
      (*-----------------*)
      JFIProves decls gamma p q

| JFITrueIntroRule :
    forall decls gamma p,
      (*----------------------*)
      JFIProves decls gamma p JFITrue

| JFIAndIntroRule :
    forall decls gamma p q r,
      (JFIProves decls gamma r p) ->
      (JFIProves decls gamma r q) ->
      (*----------------------------*)
      JFIProves decls gamma r (JFIAnd p q)

| JFIAndElimLRule :
    forall q decls gamma p r,
      (JFIProves decls gamma r (JFIAnd p q)) ->
      (*----------------*)
      JFIProves decls gamma r p

| JFIAndElimRRule :
    forall p decls gamma q r,
      (JFIProves decls gamma r (JFIAnd p q)) ->
      (*-----------------*)
      JFIProves decls gamma r q

| JFIOrIntroLRule :
    forall decls gamma p q r,
      (JFIProves decls gamma r p) ->
      (*--------------------------*)
      JFIProves decls gamma r (JFIOr p q)

| JFIOrIntroRRule :
    forall decls gamma p q r,
      (JFIProves decls gamma r q) ->
      (*--------------------------*)
      JFIProves decls gamma r (JFIOr p q)

| JFIOrElimRule :
    forall decls gamma p q r s,
      (JFIProves decls gamma s (JFIOr p q)) ->
      (JFIProves decls gamma (JFIAnd s p) r) ->
      (JFIProves decls gamma (JFIAnd s q) r) ->
      (*-----------------*)
      JFIProves decls gamma s r

| JFIImpliesIntroRule :
    forall decls gamma p q r,
      (JFIProves decls gamma (JFIAnd r p) q) ->
      (*--------------------------------------*)
      JFIProves decls gamma r (JFIImplies p q)

| JFIImpliesElimRule:
    forall p decls gamma q r,
      (JFIProves decls gamma r (JFIImplies p q)) ->
      (JFIProves decls gamma r p) ->
      (*-----------------------*)
      JFIProves decls gamma r q

| JFIForallIntroRule :
    forall decls gamma gamma_x p q x type,
      (JFIVarFreshInTerm x q) ->
      (JFIGammaAddNew x type gamma = Some gamma_x) ->
      (JFIProves decls gamma_x q p) ->
      (*-----------------------------------*)
      JFIProves decls gamma q (JFIForall type x p)

| JFIForallElimRule :
    forall r decls gamma p q x v type,
      (r = JFITermSubstituteVal x (JFSyn v) p) ->
      (JFIProves decls gamma q (JFIForall type x p)) ->
      (JFIRefType decls gamma v = Some type) ->
      (JFIRefFreshInTerm v p) ->
      (*----------------------------------------*)
      JFIProves decls gamma q r

| JFIExistsIntroRule :
    forall decls gamma p q x v type,
      (JFIProves decls (JFIGammaAdd v type gamma) q (JFITermSubstituteVal x (JFSyn (JFVar v)) p)) ->
      (*-----------------------------------*)
      JFIProves decls gamma q (JFIExists type x p)

| JFIExistsElimRule :
    forall decls gamma p q r x type,
      (JFIProves decls gamma r (JFIExists type x p)) ->
      (JFIProves decls (JFIGammaAdd x type gamma) (JFIAnd r p) q) ->
      (*----------------*)
      JFIProves decls gamma r q

| JFITypeAddRule :
    forall x cn gamma decls gamma' s p,
      (JFIProves decls gamma s p) ->
      (gamma' = (JFIGammaAdd x cn gamma)) ->
      (*---------------------------------------------------*)
      JFIProves decls gamma' s p

(* Rules for separation logic *)

| JFISepWeakRule :
    forall decls gamma p1 p2,
      (*---------------------------------*)
      JFIProves decls gamma (JFISep p1 p2) p1

| JFISepAssoc1Rule :
    forall decls gamma p1 p2 p3,
      (*------------------------------------------------------------------*)
      JFIProves decls gamma (JFISep p1 (JFISep p2 p3)) (JFISep (JFISep p1 p2) p3)

| JFISepAssoc2Rule :
    forall decls gamma p1 p2 p3,
      (*------------------------------------------------------------------*)
      JFIProves decls gamma (JFISep (JFISep p1 p2) p3) (JFISep p1 (JFISep p2 p3))

| JFISepCommRule :
    forall decls gamma p1 p2,
      (*-----------------------------------------*)
      JFIProves decls gamma (JFISep p1 p2) (JFISep p2 p1)

| JFISepIntroRule :
    forall decls gamma p1 p2 q1 q2,
      (JFIProves decls gamma p1 q1) ->
      (JFIProves decls gamma p2 q1) ->
      (*------------------------------------------*)
      JFIProves decls gamma (JFISep p1 p2) (JFISep q1 q2)

| JFISepIntroPersistentRule :
    forall decls gamma p q,
      (JFITermPersistent p) ->
      (*---------------------------------------------*)
      JFIProves decls gamma (JFIAnd p q) (JFISep p q)

| JFIWandIntroRule :
    forall decls gamma p q r,
      (JFIProves decls gamma (JFISep r p) q) ->
      (*----------------------------*)
      JFIProves decls gamma r (JFIWand p q)

| JFIWandElimRule :
    forall decls gamma p q r1 r2,
      (JFIProves decls gamma r1 (JFIWand p q)) ->
      (JFIProves decls gamma r2 p) ->
      (*------------------------------*)
      JFIProves decls gamma (JFISep r1 r2) q

(* Structural rules for Hoare triples *)

| JFIHTFrameRule :
    forall decls gamma p q r s e v,
      (JFIProves decls gamma s (JFIHoare p e v q)) ->
      (*-------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare (JFISep p r) e v (JFISep q r))

| JFIHTFalseRule :
    forall decls gamma s q e v,
      (*----------------------------------------*)
      JFIProves decls gamma s (JFIHoare JFIFalse e v q)

| JFIHTTrueRule:
    forall decls gamma s p e v,
      (*----------------------------------------*)
      JFIProves decls gamma s (JFIHoare p e v JFITrue)

| JFIHTRetRule :
    forall decls gamma s v w,
      (*--------------------------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare JFITrue (JFVal1 w) v (JFIEq (JFSyn (JFVar v)) w))

(* TODO HT-Bind *)

| JFIHTCsqRule:
    forall p' q' cn u decls gamma s p q v e,
      (JFITermPersistent s) ->
      (JFIProves decls gamma s (JFIImplies p p')) ->
      (JFIProves decls gamma s (JFIHoare p' e v q')) ->
      (JFIProves decls gamma s (JFIForall cn u (JFIImplies (JFITermSubstituteVar v u q') (JFITermSubstituteVar v u q)))) ->
      (*------------------------------*)
      JFIProves decls gamma s (JFIHoare p e v q)

| JFIHTDisjIntroRule :
    forall decls gamma s p q r e v,
      (JFIProves decls gamma s (JFIHoare p e v r)) ->
      (JFIProves decls gamma s (JFIHoare q e v r)) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare (JFIOr p q) e v r)

| JFIHTDisjElimLRule :
    forall decls gamma s p q r e v,
      (JFIProves decls gamma s (JFIHoare (JFIOr p q) e v r)) ->
      (*---------------------------------------------*)
      (JFIProves decls gamma s (JFIHoare p e v r))

| JFIHTDisjElimRRule :
    forall decls gamma s p q r e v,
      (JFIProves decls gamma s (JFIHoare (JFIOr p q) e v r)) ->
      (*---------------------------------------------*)
      (JFIProves decls gamma s (JFIHoare p e v r))

(* TODO HT-Exist *)

| JFIHTEqRule1 :
    forall decls gamma s v1 v2 p e v q,
      (JFIProves decls gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e v q)) ->
      (*----------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e v q)

| JFIHTEqRule2 :
    forall decls gamma s v1 v2 p e v q,
      (JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e v q)) ->
      (*----------------------------------------------------------------*)
      JFIProves decls gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e v q)

(* TODO HT-HT *)

(* Rules for basic constructs of Jafun *)

| JFIHTNewNotNullRule :
    forall decls gamma s p mu cn vs v,
      JFIProves decls gamma s (JFIHoare p (JFNew mu cn vs) v (JFIImplies (JFIEq (JFSyn (JFVar v)) JFnull) JFIFalse))

| JFIHTNewFieldRule :
    forall decls gamma s p mu cn vs v objflds n field value,
      (flds (JFIDeclsProg decls) (JFClass cn) = Some objflds) ->
      (nth_error objflds n = Some field) ->
      (nth_error vs n = Some value) ->
       JFIProves decls gamma s (JFIHoare p (JFNew mu cn vs) v (JFIFieldEq (JFSyn (JFVar v)) field value))

| JFIHTLetRule :
    forall v q decls gamma p r s e1 e2 x u class,
      (JFITermPersistent s) ->
      (JFIVarFreshInTerm v r) ->
      (JFIProves decls gamma s (JFIHoare p e1 x q)) ->
      (JFIProves decls gamma s (JFIForall class v
          (JFIHoare (JFITermSubstituteVar x v q) (JFIExprSubstituteVar x v e2) u r))) ->
      (*------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFLet class x e1 e2) u r )

| JFIHTFieldSetRule :
    forall decls gamma s x field v loc,
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare
          (JFIImplies (JFIEq x JFnull) JFIFalse)
          (JFAssign (x, field) (JFVLoc loc))
          v (JFIFieldEq x field (JFVLoc loc)))

(* TODO JFIHTFieldGetRule *)

(* TODO JFIHTNullFieldAccessRule *)

| JFIHTIfRule :
    forall decls gamma p v1 v2 e1 e2 u q s,
      (JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e1 u q)) ->
      (JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIImplies (JFIEq v1 v2) JFIFalse)) e2 u q)) ->
      (*---------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFIf v1 v2 e1 e2) u q)

| JFIHTInvokeRetRule :
    forall cn method rettypeCN p' w q' x decls gamma s p q u v vs mn,
      (JFIRefType decls gamma v = Some cn) ->
      (methodLookup (JFIDeclsProg decls) cn mn = Some method) ->
      (fst (rettyp_of_md method) = JFClass rettypeCN) ->
      (In (JFIInvariant cn mn p' w q') (JFIDeclsInvariants decls)) ->
      (JFIProves decls gamma (JFIAnd s p) (JFIImplies (JFIEq (JFSyn v) JFnull) JFIFalse)) ->
      (JFIProves decls gamma s (JFIImplies p (JFITermSubstituteVals (params_of_md method) vs p'))) ->
      (JFIProves decls gamma s (JFIForall rettypeCN x
          (JFIImplies
            (JFITermSubstituteVals (params_of_md method) vs (JFITermSubstituteVar w x q'))
            (JFITermSubstituteVar u x q)))) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFInvoke (JFSyn v) mn vs) u q) (* TODO null *)

| JFIHTInvokeNoRetRule :
    forall cn method p' w q' decls gamma s p q u v vs mn,
      (JFIRefType decls gamma v = Some cn) ->
      (methodLookup (JFIDeclsProg decls) cn mn = Some method) ->
      (In (JFIInvariant cn mn p' w q') (JFIDeclsInvariants decls)) ->
      (JFIProves decls gamma (JFIAnd s p) (JFIImplies (JFIEq (JFSyn v) JFnull) JFIFalse)) ->
      (JFIProves decls gamma s (JFIImplies p (JFITermSubstituteVals (params_of_md method) vs p'))) ->
      (JFIProves decls gamma s (JFIImplies (JFITermSubstituteVals (params_of_md method) vs q') q)) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFInvoke (JFSyn v) mn vs) u q) (* TODO null *)

(* TODO JFIHTNullInvokeRule *)

(* TODO JFIHTThrowRule *)

(* TODO JFIHTTryCathRule *)
.


