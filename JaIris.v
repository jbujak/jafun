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
Require Import JaSubtype.
Require Import Bool.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.

Module StrMap := JaIrisCommon.StrMap.
Module HeapFacts := Facts Heap.

(* Heaps *)
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

Definition JFIValToLoc (val : JFIVal) (env : JFITermEnv) (this : nat) : option Loc :=
  match val with
  | JFINull => Some null
  | JFIThis => Some (JFLoc this)
  | JFIVar x => StrMap.find x env
  end.

(* Semantics *)

Fixpoint JFIHeapSatisfiesInEnv (h : Heap) (t : JFITerm) (env : JFITermEnv) (this : nat) (CC : JFProgram) : Prop :=
  match t with
    | JFITrue => True
    | JFIFalse => False
    | JFIAnd t1 t2 => JFIHeapSatisfiesInEnv h t1 env this CC /\ JFIHeapSatisfiesInEnv h t2 env this CC
    | JFIOr t1 t2 => JFIHeapSatisfiesInEnv h t1 env this CC \/ JFIHeapSatisfiesInEnv h t2 env this CC
    | JFIImplies t1 t2 => ~(JFIHeapSatisfiesInEnv h t1 env this CC) \/ JFIHeapSatisfiesInEnv h t2 env this CC
    | JFIHoare t1 e ex valueName t2 => JFIHeapSatisfiesInEnv h t1 env this CC -> exists confs hn res_ex res,
        let newEnv := StrMap.add valueName res env
        in (JFIEvalInEnv h e confs hn res_ex res env this CC) /\
           (res_ex = ex /\ JFIHeapSatisfiesInEnv hn t2 newEnv this CC)
    | JFIEq val1 val2 =>
        let l1 := JFIValToLoc val1 env this
        in let l2 := JFIValToLoc val2 env this
        in match (l1, l2) with
           | (Some loc1, Some loc2) => loc1 = loc2
           | _ => False
        end
    | JFIFieldEq obj fieldName val =>
        let l1 := JFIValToLoc obj env this
        in let l2 := JFIValToLoc val env this
        in match (l1, l2) with
          | (Some objLoc, Some valLoc) => JFIObjFieldEq objLoc fieldName valLoc h
          | _ => False
        end
    | JFISep t1 t2 => exists (h1 h2 : Heap),
        (JFIHeapsUnion h1 h2 h /\ JFIHeapsDisjoint h1 h2) /\
        (JFIHeapSatisfiesInEnv h1 t1 env this CC /\ JFIHeapSatisfiesInEnv h2 t2 env this CC)
    | JFIWand t1 t2 => forall h', JFIHeapsDisjoint h h' -> JFIHeapSatisfiesInEnv h' t1 env this CC ->
        (exists h_h', JFIHeapsUnion h h' h_h' /\ JFIHeapSatisfiesInEnv h_h' t2 env this CC) 
  end.

Fixpoint JFIHeapSatisfiesOuterInEnv (h : Heap) (t : JFIOuterTerm) (env : JFITermEnv) (this : nat) (CC : JFProgram) : Prop :=
  match t with
  | JFIOuterAnd t1 t2 => JFIHeapSatisfiesOuterInEnv h t1 env this CC /\ JFIHeapSatisfiesOuterInEnv h t2 env this CC
  | JFIOuterOr t1 t2 => JFIHeapSatisfiesOuterInEnv h t1 env this CC \/ JFIHeapSatisfiesOuterInEnv h t2 env this CC
  | JFIExists class name term => exists l : Loc,
      let env1 := StrMap.add name l env
      in JFILocOfType l h class /\ JFIHeapSatisfiesOuterInEnv h term env1 this CC
  | JFIInner t => JFIHeapSatisfiesInEnv h t env this CC
  end.

Definition JFIGammaMatchEnv (h : Heap) (gamma : JFITypeEnv) (env : JFITermEnv) :=
  forall var_name,
    (StrMap.In var_name gamma <-> StrMap.In var_name env) /\
    (forall var_loc var_type,
      (StrMap.MapsTo var_name var_type gamma) ->
      (StrMap.MapsTo var_name var_loc env) ->
       JFILocOfType var_loc h var_type).

Definition JFIHeapSatisfies (h : Heap) (t : JFITerm) (gamma : JFITypeEnv) (CC : JFProgram) : Prop :=
  forall env this, JFIGammaMatchEnv h gamma env -> JFIHeapSatisfiesInEnv h t env this CC.

(* Persistence *)

Fixpoint JFITermPersistent (t : JFITerm) : Prop :=
  match t with
  | JFITrue => True
  | JFIFalse => True
  | JFIAnd t1 t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIOr t1 t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIImplies t1 t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIHoare t1 e ex valueName t2 => JFITermPersistent t1 /\ JFITermPersistent t2
  | JFIEq val1 val2 => True
  | JFIFieldEq obj fieldName val => False
  | JFISep t1 t2 => False
  | JFIWand t1 t2 => False
  end.

Fixpoint JFIOuterTermPersistent (t : JFIOuterTerm) : Prop :=
  match t with
  | JFIOuterAnd t1 t2 => JFIOuterTermPersistent t1 /\ JFIOuterTermPersistent t2
  | JFIOuterOr t1 t2 => JFIOuterTermPersistent t1 /\ JFIOuterTermPersistent t2
  | JFIExists class name term => JFIOuterTermPersistent term
  | JFIInner t => JFITermPersistent t
  end.

(* Program structure for proofs *)

Inductive JFIInvariantType : Type :=
| JFIInvariant (cn : string) (mn : string) (precondition : JFITerm) (ex : JFEvMode) (var : string) (postcondition : JFITerm).

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

Definition JFIValType (decls : JFIDeclsType) (gamma : JFITypeEnv) (ref : JFIVal) : option JFClassName :=
  match ref with
  | JFIVar v => StrMap.find v gamma
  | JFIThis => Some (name_of_cd (JFIDeclsCDecl decls))
  | JFINull => None
  end.

(* TODO do wywalenia *)
Definition JFIGammaAdd (x : string) (type : JFClassName) (gamma : JFITypeEnv) : JFITypeEnv :=
  StrMap.add x type gamma.

Definition JFIGammaAddNew (x : string) (type : JFClassName) (gamma : JFITypeEnv) : option JFITypeEnv :=
  if StrMap.mem x gamma then None else Some (StrMap.add x type gamma).

Definition JFIEnvAddNew (x : string) (l : Loc) (env : JFITermEnv) : option JFITermEnv :=
  if StrMap.mem x env then None else Some (StrMap.add x l env).

Definition JFIVarFreshInVal (x : string) (v : JFIVal) :=
  match v with
  | JFIVar y => x <> y
  | _ => True
  end.

Fixpoint JFIVarFreshInExpr (x : string) (e : JFExpr) := (* TODO pewnie wywalic *)
  match e with
    | JFNew mu C vs => True
    | JFLet C x e1 e2 => True
    | JFIf v1 v2 e1 e2 => True
    | JFInvoke v1 m vs => True
    | JFAssign (v1,fld) v2 => True
    | JFVal1 v1 => True
    | JFVal2 (v1, fld) => True
    | JFThrow v1 => True
    | JFTry e1 mu C x e2 => True
  end.

Fixpoint JFIVarFreshInTerm (x : string) (t : JFITerm) :=
  match t with
  | JFITrue => True
  | JFIFalse => True
  | JFIAnd t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
  | JFIOr t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
  | JFIImplies t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
  | JFIHoare t1 e ex name t2 => (* TODO maybe allow x = name *)
      if String.eqb name x then False else
        (JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2 /\ JFIVarFreshInExpr x e)
  | JFIEq val1 val2 => JFIVarFreshInVal x val1 /\ JFIVarFreshInVal x val2
  | JFIFieldEq obj fieldName val => JFIVarFreshInVal x obj /\ JFIVarFreshInVal x val
  | JFISep t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
  | JFIWand t1 t2 => JFIVarFreshInTerm x t1 /\ JFIVarFreshInTerm x t2
  end.

Fixpoint JFIVarFreshInOuterTerm (x : string) (t : JFIOuterTerm) :=
  match t with
  | JFIOuterAnd t1 t2 => JFIVarFreshInOuterTerm x t1 /\ JFIVarFreshInOuterTerm x t2
  | JFIOuterOr t1 t2 => JFIVarFreshInOuterTerm x t1 /\ JFIVarFreshInOuterTerm x t2
  | JFIExists class name term => (* TODO maybe allow x = name *)
      if String.eqb name x then False else JFIVarFreshInOuterTerm x term
  | JFIInner t => JFIVarFreshInTerm x t
  end.

Definition JFIValFreshInTerm (v : JFIVal) (t : JFITerm) :=
  match v with
  | JFIVar x => JFIVarFreshInTerm x t
  | JFIThis => True
  | JFINull => True
  end.

Inductive JFIProves : JFIDeclsType -> JFITypeEnv -> JFITerm -> JFITerm -> Prop :=

(* Rules for intuitionistic logic with equality *) 

| JFIAsmRule :
    forall decls gamma p,
      (FreeVarsInTermAreInGamma p gamma) ->
      (*-----------------*)
      JFIProves decls gamma p p

| JFITransRule :
    forall q decls gamma p r,
      (JFIProves decls gamma p q) ->
      (JFIProves decls gamma q r) ->
      (*----------------*)
      JFIProves decls gamma p r

| JFIEqReflRule :
    forall decls gamma p v,
      (FreeVarsInTermAreInGamma p gamma) ->
      (FreeVarsInValAreInGamma v gamma) ->
      (*----------------------------------*)
      JFIProves decls gamma p (JFIEq v v)

| JFIEqSymRule :
    forall decls gamma v1 v2 p,
      (JFIProves decls gamma p (JFIEq v1 v2)) ->
      (*-----------------------------------*)
      JFIProves decls gamma p (JFIEq v2 v1)

| JFIFalseElimRule :
    forall decls gamma p q,
      (FreeVarsInTermAreInGamma q gamma) ->
      (JFIProves decls gamma p JFIFalse) ->
      (*-----------------*)
      JFIProves decls gamma p q

| JFITrueIntroRule :
    forall decls gamma p,
      (FreeVarsInTermAreInGamma p gamma) ->
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
      (FreeVarsInTermAreInGamma q gamma) ->
      (JFIProves decls gamma r p) ->
      (*--------------------------*)
      JFIProves decls gamma r (JFIOr p q)

| JFIOrIntroRRule :
    forall decls gamma p q r,
      (FreeVarsInTermAreInGamma p gamma) ->
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

(* Rules for separation logic *)

| JFIWeakRule :
    forall decls gamma p1 p2,
      (FreeVarsInTermAreInGamma p1 gamma) ->
      (FreeVarsInTermAreInGamma p2 gamma) ->
      (*------------------------------------*)
      JFIProves decls gamma (JFISep p1 p2) p1

| JFISepAssoc1Rule :
    forall decls gamma p1 p2 p3,
      (FreeVarsInTermAreInGamma p1 gamma) ->
      (FreeVarsInTermAreInGamma p2 gamma) ->
      (FreeVarsInTermAreInGamma p3 gamma) ->
      (*------------------------------------------------------------------*)
      JFIProves decls gamma (JFISep p1 (JFISep p2 p3)) (JFISep (JFISep p1 p2) p3)

| JFISepAssoc2Rule :
    forall decls gamma p1 p2 p3,
      (FreeVarsInTermAreInGamma p1 gamma) ->
      (FreeVarsInTermAreInGamma p2 gamma) ->
      (FreeVarsInTermAreInGamma p3 gamma) ->
      (*------------------------------------------------------------------*)
      JFIProves decls gamma (JFISep (JFISep p1 p2) p3) (JFISep p1 (JFISep p2 p3))

| JFISepCommRule :
    forall decls gamma p1 p2,
      (FreeVarsInTermAreInGamma p1 gamma) ->
      (FreeVarsInTermAreInGamma p2 gamma) ->
      (*-----------------------------------------*)
      JFIProves decls gamma (JFISep p1 p2) (JFISep p2 p1)

| JFISepIntroRule :
    forall decls gamma p1 p2 q1 q2,
      (JFIProves decls gamma p1 q1) ->
      (JFIProves decls gamma p2 q2) ->
      (*------------------------------------------*)
      JFIProves decls gamma (JFISep p1 p2) (JFISep q1 q2)

| JFISepIntroPersistentRule :
    forall decls gamma p q,
      (FreeVarsInTermAreInGamma p gamma) ->
      (FreeVarsInTermAreInGamma q gamma) ->
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
    forall decls gamma p q r s e ex v,
      (JFITermPersistent s) ->
      (JFIVarFreshInTerm v r) ->
      (JFIProves decls gamma s (JFIHoare p e ex v q)) ->
      (*-------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare (JFISep p r) e ex v (JFISep q r))

| JFIHTRetRule :
    forall decls gamma s v w w_expr,
      w_expr = JFIValToJFVal w ->
      (*--------------------------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare JFITrue (JFVal1 w_expr) None v (JFIEq (JFIVar v) w))

| JFIHTCsqRule:
    forall p' q' cn decls gamma s p q ex v e,
      (JFITermPersistent s) ->
      (JFIVarFreshInTerm v s) ->
      (JFIProves decls gamma s (JFIImplies p p')) ->
      (JFIProves decls gamma s (JFIHoare p' e ex v q')) ->
      (JFIProves decls (JFIGammaAdd v cn gamma) s (JFIImplies q' q)) ->
      (*------------------------------*)
      JFIProves decls gamma s (JFIHoare p e ex v q)

| JFIHTDisjIntroRule :
    forall decls gamma s p q r e ex v,
      (JFIProves decls gamma s (JFIHoare p e ex v r)) ->
      (JFIProves decls gamma s (JFIHoare q e ex v r)) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare (JFIOr p q) e ex v r)

| JFIHTDisjElimLRule :
    forall decls gamma s p q r e ex v,
      (JFIProves decls gamma s (JFIHoare (JFIOr p q) e ex v r)) ->
      (*---------------------------------------------*)
      (JFIProves decls gamma s (JFIHoare p e ex v r))

| JFIHTDisjElimRRule :
    forall decls gamma s p q r e ex v,
      (JFIProves decls gamma s (JFIHoare (JFIOr p q) e ex v r)) ->
      (*---------------------------------------------*)
      (JFIProves decls gamma s (JFIHoare p e ex v r))

(* TODO HT-Exist *)

| JFIHTEqRule1 :
    forall decls gamma s v1 v2 p e ex v q,
      (JFIProves decls gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e ex v q)) ->
      (*----------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e ex v q)

| JFIHTEqRule2 :
    forall decls gamma s v1 v2 p e ex v q,
      (JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e ex v q)) ->
      (*----------------------------------------------------------------*)
      JFIProves decls gamma (JFIAnd s (JFIEq v1 v2)) (JFIHoare p e ex v q)

(* TODO HT-HT *)

(* Rules for basic constructs of Jafun *)

| JFIHTNewNotNullRule :
    forall decls gamma s p mu cn vs v,
      JFIProves decls gamma s (JFIHoare p (JFNew mu cn vs) None v (JFIImplies (JFIEq (JFIVar v) JFINull) JFIFalse))

| JFIHTNewFieldRule :
    forall decls gamma s p mu cn vs v objflds n field value,
      (flds (JFIDeclsProg decls) (JFClass cn) = Some objflds) ->
      (nth_error objflds n = Some field) ->
      (nth_error vs n = Some (JFIValToJFVal value)) ->
      (value <> (JFIVar v)) ->
      (*----------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFNew mu cn vs) None v (JFIFieldEq (JFIVar v) field value))

| JFIHTLetRule :
    forall q decls gamma p r s e1 e2 x ex u class,
      (JFITermPersistent s) ->
      (JFIVarFreshInTerm x s) ->
      (JFIVarFreshInTerm x r) ->
      (JFIProves decls gamma s (JFIHoare p e1 None x q)) ->
      (JFIProves decls (JFIGammaAdd x class gamma) s (JFIHoare q e2 ex u r)) ->
      (*------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFLet class x e1 e2) ex u r )

| JFIHTLetExRule :
    forall q decls gamma p s e1 e2 x ex u class,
      (JFIProves decls gamma s (JFIHoare p e1 (Some ex) u q)) ->
      (*------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFLet class x e1 e2) (Some ex) u q )

| JFIHTFieldSetRule :
    forall decls gamma s x x_expr field u v v_expr,
      (x_expr = JFIValToJFVal x) ->
      (v_expr = JFIValToJFVal v) ->
      (x <> (JFIVar u)) ->
      (v <> (JFIVar u)) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare
          (JFIImplies (JFIEq x JFINull) JFIFalse)
          (JFAssign (x_expr, field) v_expr)
           None u (JFIFieldEq x field v))

| JFIHTNullFieldSetRule :
    forall decls gamma s x x_expr field v loc,
      (x_expr = JFIValToJFVal x) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare (JFIEq x JFINull)
          (JFAssign (x_expr, field) (JFVLoc loc))
           NPE_mode v JFITrue)

(* TODO JFIHTFieldGetRule *)

| JFIHTNullFieldGetRule :
    forall decls gamma s x x_expr field v,
      (x_expr = JFIValToJFVal x) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare (JFIEq x JFINull)
          (JFVal2 (x_expr, field))
           NPE_mode v JFITrue)

| JFIHTIfRule :
    forall decls gamma p v1 v1_expr v2 v2_expr e1 e2 ex u q s,
      (v1_expr = JFIValToJFVal v1) -> (v2_expr = JFIValToJFVal v2) ->
      (JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIEq v1 v2)) e1 ex u q)) ->
      (JFIProves decls gamma s (JFIHoare (JFIAnd p (JFIImplies (JFIEq v1 v2) JFIFalse)) e2 ex u q)) ->
      (*---------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFIf v1_expr v2_expr e1 e2) ex u q)

| JFIHTInvokeRetRule :
    forall cn method rettypeCN p' ex w q' decls gamma s p q u v v_expr vs vs_expr mn,
      (v_expr = JFIValToJFVal v) -> (vs_expr = JFIValsToJFVals vs) ->
      (JFIValType decls gamma v = Some cn) ->
      (methodLookup (JFIDeclsProg decls) cn mn = Some method) ->
      (fst (rettyp_of_md method) = JFClass rettypeCN) ->
      (In (JFIInvariant cn mn p' ex w q') (JFIDeclsInvariants decls)) ->
      (JFIProves decls gamma (JFIAnd s p) (JFIImplies (JFIEq v JFINull) JFIFalse)) ->
      (JFIProves decls gamma s (JFIImplies p (JFITermSubstituteVals (params_of_md method) vs p'))) -> (* TODO substitute this *)
      (forall x gamma_x,
         JFIVarFreshInTerm x s ->
         JFIGammaAddNew x rettypeCN gamma = Some gamma_x ->
         JFIProves decls gamma_x s
           (JFIImplies
             (JFITermSubstituteVals (params_of_md method) vs (JFITermSubstituteVar w x q'))
             (JFITermSubstituteVar u x q))) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFInvoke v_expr mn vs_expr) ex u q)

| JFIHTNullInvokeRule :
    forall decls gamma s x x_expr mn vs v,
      (x_expr = JFIValToJFVal x) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare (JFIEq x JFINull)
          (JFInvoke x_expr mn vs)
           NPE_mode v JFITrue)

| JFIHTThrowRule :
    forall decls gamma s cn x x_expr v,
      (x_expr = JFIValToJFVal x) ->
      (JFIValType decls gamma x = Some cn) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare (JFIImplies (JFIEq x JFINull) JFIFalse)
           (JFThrow x_expr)
           (Some cn) v (JFIEq (JFIVar v) x))

| JFIHTNullThrowRule :
    forall decls gamma s x x_expr v,
      (x_expr = JFIValToJFVal x) ->
      (*--------------------------------------------------*)
      JFIProves decls gamma s
        (JFIHoare (JFIEq x JFINull)
           (JFThrow x_expr)
            NPE_mode v JFITrue)

| JFIHTCatchNormalRule :
    forall decls gamma s p e1 mu x e2 u q ex,
      (JFIProves decls gamma s (JFIHoare p e1 None u q)) ->
      (*------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFTry e1 mu ex x e2) None u q )

| JFIHTCatchExRule :
    forall decls gamma s p r e1 mu x e2 u q ex ex' ex'',
      (JFITermPersistent s) ->
      (JFIVarFreshInTerm x s) ->
      (JFIVarFreshInTerm x r) ->
      (JFIProves decls gamma s (JFIHoare p e1 (Some ex') x q)) ->
      (JFIProves decls (JFIGammaAdd x ex gamma) s (JFIHoare q e2 ex'' u r)) ->
      (Is_true (subtype_bool (JFIDeclsProg decls) (JFClass ex') (JFClass ex))) ->
      (*------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFTry e1 mu ex x e2) ex'' u r )

| JFIHTCatchPassExRule :
    forall decls gamma s p e1 mu x e2 u q ex ex',
      (JFIProves decls gamma s (JFIHoare p e1 (Some ex') u q)) ->
       ~Is_true (subtype_bool (JFIDeclsProg decls) (JFClass ex') (JFClass ex)) ->
      (*------------------------------------------------------------*)
      JFIProves decls gamma s (JFIHoare p (JFTry e1 mu ex x e2) (Some ex') u q )
.

Inductive JFIProvesOuter : JFIDeclsType -> JFITypeEnv -> JFIOuterTerm -> JFIOuterTerm -> Prop :=
| JFIExistsIntroRule :
    forall decls gamma p q x v type,
      (JFIValType decls gamma v = Some type) ->
      (JFIProvesOuter decls gamma q (JFIOuterTermSubstituteVal x v p)) ->
      (*-----------------------------------*)
      JFIProvesOuter decls gamma q (JFIExists type x p)

| JFIExistsElimRule :
    forall decls gamma p q r x type,
      (JFIVarFreshInOuterTerm x r) ->
      (JFIVarFreshInOuterTerm x q) ->
      (JFIProvesOuter decls gamma r (JFIExists type x p)) ->
      (JFIProvesOuter decls (JFIGammaAdd x type gamma) (JFIOuterAnd r p) q) ->
      (*----------------*)
      JFIProvesOuter decls gamma r q

| JFIOuterInnerRule :
    forall decls gamma p q,
      (JFIProves decls gamma p q) ->
      (JFIProvesOuter decls gamma (JFIInner p) (JFIInner q))

| JFIOuterAndIntroRule :
    forall decls gamma p q r,
      (JFIProvesOuter decls gamma r p) ->
      (JFIProvesOuter decls gamma r q) ->
      (*----------------------------*)
      JFIProvesOuter decls gamma r (JFIOuterAnd p q)

| JFIOuterAndElimLRule :
    forall q decls gamma p r,
      (JFIProvesOuter decls gamma r (JFIOuterAnd p q)) ->
      (*----------------*)
      JFIProvesOuter decls gamma r p

| JFIOuterAndElimRRule :
    forall p decls gamma q r,
      (JFIProvesOuter decls gamma r (JFIOuterAnd p q)) ->
      (*-----------------*)
      JFIProvesOuter decls gamma r q

| JFIOuterOrIntroLRule :
    forall decls gamma p q r,
      (JFIProvesOuter decls gamma r p) ->
      (*--------------------------*)
      JFIProvesOuter decls gamma r (JFIOuterOr p q)

| JFIOuterOrIntroRRule :
    forall decls gamma p q r,
      (JFIProvesOuter decls gamma r q) ->
      (*--------------------------*)
      JFIProvesOuter decls gamma r (JFIOuterOr p q)

| JFIOuterOrElimRule :
    forall decls gamma p q r s,
      (JFIProvesOuter decls gamma s (JFIOuterOr p q)) ->
      (JFIProvesOuter decls gamma (JFIOuterAnd s p) r) ->
      (JFIProvesOuter decls gamma (JFIOuterAnd s q) r) ->
      (*-----------------*)
      JFIProvesOuter decls gamma s r
.
