Require Import JaSyntax.
Require Import JaTypes.
Require Import JaIris.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope string_scope.

Require Import FMapFacts.
Module StrMapFacts := Facts StrMap.

Ltac unfoldSubstitutions :=
  unfold JFITermSubstituteVals;
  unfold JFITermSubstituteVar;
  unfold JFITermSubstituteVal;
  unfold JFIExprSubstituteVar;
  unfold JFIValSubstituteVal;
  unfold JFIStringSubstitute;
  simpl.

(* Derived rules *)

(*
  s |- p => p'           s |- {p'} e { \v . q } 
  ---------------------------------------------
             s |- {p} e { \v / q }
*)
Theorem HTStrenghtenPrecondition : forall p' decls gamma s p e v q,
    (JFIProves decls gamma s (JFIImplies p p')) ->
    (JFIProves decls gamma s (JFIHoare p' e v q)) ->
    (*----------------------------------------*)
    JFIProves decls gamma s (JFIHoare p e v q).
Proof.
intros.
apply (JFIHTCsqRule p' q "" v).
  + assumption.
  + assumption.
  + apply JFIForallIntroRule.
    apply JFIImpliesIntroRule.
    apply (JFIAndElimRRule s).
    apply JFIAsmRule.
Qed.

(* 
   s |- {p /\ true} e { \ v . q }
   ------------------------------
        s |- {p} e { \v . q } 
*)
Theorem HTFrameAddTrue : forall decls gamma s p e v q,
    (JFIProves decls gamma s (JFIHoare (JFIAnd JFITrue p) e v q)) ->
    (*-----------------------------------------*)
    JFIProves decls gamma s (JFIHoare p e v q).
Proof.
intros.
apply (HTStrenghtenPrecondition (JFIAnd JFITrue p)).
  + apply JFIImpliesIntroRule.
    apply JFIAndIntroRule.
    ++ apply JFITrueIntroRule.
    ++ apply (JFIAndElimRRule s).
       apply JFIAsmRule.
  + assumption.
Qed.

Theorem HTLetDet : forall v q decls gamma x cn u p r s e1 e2,
    (JFIProves decls gamma s (JFIHoare p e1 x (JFIAnd q (JFIEq (JFSyn (JFVar x)) (JFSyn (JFVar v)))))) ->
    (JFIProves decls gamma s (JFIHoare (JFITermSubstituteVar x v q) (JFIExprSubstituteVar x v e2) u r)) ->
    (*----------------------------------------------------------*)
    JFIProves decls gamma s (JFIHoare p (JFLet cn x e1 e2) u r).
Proof.
intros.
apply (JFIHTLetRule v (JFIAnd q (JFIEq (JFSyn (JFVar x)) (JFSyn (JFVar v))))).
  + assumption.
  + apply JFIForallIntroRule.
    apply (HTStrenghtenPrecondition (JFITermSubstituteVar x v q)).
   ++ apply JFIImpliesIntroRule.
      unfold JFITermSubstituteVar.
      unfold JFITermSubstituteVal.
      apply (JFIAndElimLRule (JFIEq
           (JFIValSubstituteVal x (JFSyn (JFVar v)) (JFSyn (JFVar x)))
           (JFIValSubstituteVal x (JFSyn (JFVar v)) (JFSyn (JFVar v))))).
      apply (JFIAndElimRRule s).
      apply JFIAsmRule.
   ++ apply (JFITypeAddRule v cn gamma).
      +++ assumption.
      +++ trivial.
Qed. 


(* p |- p \/ q *)
Theorem p_proves_p_or_q : forall decls gamma p q, JFIProves decls gamma p (JFIOr p q).
Proof.
intros decls gamma p q.
apply JFIOrIntroLRule.
apply JFIAsmRule.
Qed.

(* p |- q -* r  ->  p * q |- r *)
Theorem simpler_wand_elim_rule : forall decls gamma p q r, (JFIProves decls gamma p (JFIWand q r)) -> JFIProves decls gamma (JFISep p q) r.
Proof.
intros decls gamma p q r.
intros p_wand_q_r.
apply (JFIWandElimRule decls gamma q r p q).
assumption.
apply JFIAsmRule.
Qed.

(* p * q |- p /\ q *)
Theorem sep_proves_and : forall p q decls gamma, JFIProves decls gamma (JFISep p q) (JFIAnd p q).
Proof.
intros.
apply JFIAndIntroRule.
  (* p * q |- p *)
  apply JFISepWeakRule.
  
  (* p * q |- q *)
  apply (JFITransRule (JFISep q p)).
  apply JFISepCommRule.
  apply JFISepWeakRule.
Qed.


(* |- forall x, {x != null} x.a = null {x.a = null} *)
Theorem null_assignment_works : forall gamma decls p v, JFIProves decls gamma p 
  (JFIForall "class" "x"
    (JFIHoare
      (JFIImplies (JFIEq (JFSyn (JFVar "x")) JFnull) JFIFalse)
      (JFAssign (JFSyn (JFVar "x"), "a") JFnull)
      v (JFIFieldEq (JFSyn (JFVar "x")) "a" JFnull))).
Proof.
intros gamma decls p v.
apply JFIForallIntroRule.
apply JFIHTFieldAssignRule.
Qed.

(* |- {True} let x = null in x { \u . u = null } *)
Theorem let_x_in_x_works : forall gamma decls p cn, JFIProves decls gamma p
      (JFIHoare
        JFITrue
        (JFLet cn "x" (JFVal1 JFnull) (JFVal1 (JFSyn (JFVar "x"))))
        "u" (JFIEq (JFSyn (JFVar "u")) JFnull)).
Proof.
intros gamma decls p cn.
apply (JFIHTLetRule "v" (JFIEq (JFSyn (JFVar "x")) JFnull)).

  (* |- {True} null {x . x = null} *)
  apply JFIHTRetRule.

  (* |- forall v, {v = null} v {u . u = null} *)
  apply JFIForallIntroRule.
  unfoldSubstitutions.
  apply HTFrameAddTrue.
  apply JFIHTEqRule1.
  apply (JFIEqRule
    (JFIHoare JFITrue (JFVal1 (JFSyn (JFVar "z"))) "u" (JFIEq (JFSyn (JFVar "u")) JFnull))
    "z"
    JFnull
    (JFSyn (JFVar "v"))
  ).

    (* correct substitution *) 
    unfoldSubstitutions.
    trivial.

    (* v = null |- {True} null { \u . u = null } *)
    unfold JFITermSubstituteVal.
    unfold JFIValSubstituteVal.
    simpl.
    apply JFIHTRetRule.

    (* p /\ v = null |- v = null *)
    apply JFIEqSymRule.
    apply (JFIAndElimRRule p).
    apply JFIAsmRule.
Qed.

(* |- {x = null /\ y != null} if x == x then x else y { \u . u = x } *)
Theorem if_true_works : forall gamma decls s, JFIProves decls gamma s
    (JFIHoare
      (JFIAnd (JFIEq (JFSyn (JFVar "x")) JFnull) (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))
      (JFIf (JFSyn (JFVar "x")) (JFSyn (JFVar "x")) (JFVal1 (JFSyn (JFVar "x"))) (JFVal1 (JFSyn (JFVar "y"))))
      "u" (JFIEq (JFSyn (JFVar "u")) (JFSyn (JFVar "x")))).
Proof.
intros.
apply JFIHTIfRule.
+ apply (HTStrenghtenPrecondition JFITrue).
  ++ apply JFIImpliesIntroRule; apply JFITrueIntroRule.
  ++ apply JFIHTRetRule.
+ apply (HTStrenghtenPrecondition JFIFalse).
  ++ apply JFIImpliesIntroRule.
     apply (JFITransRule (JFIImplies (JFIEq (JFSyn (JFVar "x")) (JFSyn (JFVar "x"))) JFIFalse)).
     +++ apply (JFIAndElimRRule (JFIAnd (JFIEq (JFSyn (JFVar "x")) JFnull)
           (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))).
         apply (JFIAndElimRRule s).
         apply JFIAsmRule.
     +++ apply (JFIImpliesElimRule (JFIEq (JFSyn (JFVar "x")) (JFSyn (JFVar "x")))).
         ++++ apply JFIAsmRule.
         ++++ apply JFIEqReflRule.
  ++ apply JFIHTFalseRule.
Qed.

(* |- {x = null /\ y != null} if x == y then x else y { \u . u = y } *)
Theorem if_false_works : forall gamma decls s, JFIProves decls gamma s
    (JFIHoare
      (JFIAnd (JFIEq (JFSyn (JFVar "x")) JFnull) (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))
      (JFIf (JFSyn (JFVar "x")) (JFSyn (JFVar "y")) (JFVal1 (JFSyn (JFVar "x"))) (JFVal1 (JFSyn (JFVar "y"))))
      "u" (JFIEq (JFSyn (JFVar "u")) (JFSyn (JFVar "y")))).
Proof.
intros.
apply JFIHTIfRule.
+ apply (HTStrenghtenPrecondition JFIFalse).
  ++ apply JFIImpliesIntroRule.
     apply (JFITransRule (JFIAnd
        (JFIAnd (JFIEq (JFSyn (JFVar "x")) JFnull)
           (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))
        (JFIEq (JFSyn (JFVar "x")) (JFSyn (JFVar "y"))))).
     +++ apply (JFIAndElimRRule s); apply JFIAsmRule.
     +++ apply (JFIImpliesElimRule (JFIEq (JFSyn (JFVar "y")) JFnull)).
         - apply (JFIAndElimRRule (JFIEq (JFSyn (JFVar "x")) JFnull)).
           apply (JFIAndElimLRule (JFIEq (JFSyn (JFVar "x")) (JFSyn (JFVar "y")))).
           apply JFIAsmRule.
         - apply JFIEqSymRule.
           apply (JFIEqRule (JFIEq (JFSyn (JFVar "z")) (JFSyn (JFVar "y"))) "z" (JFSyn (JFVar "x")) JFnull); unfoldSubstitutions.
           -- trivial.
           -- apply (JFIAndElimRRule (JFIAnd (JFIEq (JFSyn (JFVar "x")) JFnull)
                (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))).
              apply JFIAsmRule.
           -- apply (JFIAndElimLRule (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse)).
              apply (JFIAndElimLRule (JFIEq (JFSyn (JFVar "x")) (JFSyn (JFVar "y")))).
              apply JFIAsmRule.
  ++ apply JFIHTFalseRule.
+ apply (HTStrenghtenPrecondition JFITrue).
  ++ apply JFIImpliesIntroRule; apply JFITrueIntroRule.
  ++ apply JFIHTRetRule.
Qed.


(* class::method(class x) { return null; } *)   
Definition method : JFMethodDeclaration := JFMDecl0 (JFClass "class") "method" [("x", JFClass "class")] [] (JFVal1 JFnull).
Definition class : JFClassDeclaration := JFCDecl "class" None [JFFDecl false (JFClass "class") "field"] [method].

(* subclass::method(class x) { if(x == null) { return null;} else { x.field = null; return new class();}} *)
Definition method_override : JFMethodDeclaration := JFMDecl0 (JFClass "class") "method" [("x", JFClass "class")] [] 
  (JFIf (JFSyn (JFVar "x")) JFnull
    (* true *) (JFVal1 JFnull)
    (* false *)(JFLet "class" "y" (JFAssign (JFSyn (JFVar "x"), "field") JFnull) (JFNew JFrwr "class" []))
  ).
Definition subclass : JFClassDeclaration := JFCDecl "subclass" (Some "class") [JFFDecl false (JFClass "class") "field"] [method_override].

Definition program : JFProgram := [ class; subclass ].
Definition invariants : list JFIInvariantType :=
 [
    (* {x == null}    class.method(x) {\v . v == null} *)
    JFIInvariant "class" "method" (JFIEq (JFSyn (JFVar "x")) JFnull) "v" (JFIEq (JFSyn (JFVar "v")) JFnull);
    (* {x == null} subclass.method(x) {\v . v == null} *)
    JFIInvariant "subclass" "method" (JFIEq (JFSyn (JFVar "x")) JFnull) "v" (JFIEq (JFSyn (JFVar "v")) JFnull);
    (* {x != null} subclass.method(x) {\v . x.field = null *)
    JFIInvariant "subclass" "method" (JFIImplies (JFIEq (JFSyn (JFVar "x")) JFnull) JFIFalse) "v" (JFIFieldEq (JFSyn (JFVar "x")) "field" JFnull)
 ].

(* |- {} let class y = new subclass() in y.method(null) { \u . u == null } *)
Theorem polymorphism_works : forall gamma s, JFIProves (JFIDecls program invariants class method) gamma s
    (JFIHoare
      JFITrue
      (JFLet "class" "y" (JFNew JFrwr "subclass" []) (JFInvoke (JFSyn (JFVar "y")) "method" [JFnull]))
      "u" (JFIEq (JFSyn (JFVar "u")) JFnull)).
Proof.
intros.
apply (JFIHTLetRule "y" (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse)).
+ apply JFIHTNewNotNullRule.
+ apply JFIForallIntroRule.
  unfoldSubstitutions.
  apply (JFIHTInvokeRetRule "class" method "class" (JFIEq (JFSyn (JFVar "x")) JFnull) "v" (JFIEq (JFSyn (JFVar "v")) JFnull) "ret").
  ++ unfold JFIRefType.
     unfold JFIGammaAdd.
     apply StrMapFacts.add_o.
  ++ compute.
     trivial.
  ++ compute.
     trivial.
  ++ compute.
     apply or_introl.
     trivial.
  ++ apply (JFIAndElimRRule s).
     apply JFIAsmRule.
  ++ apply JFIImpliesIntroRule.
     unfold method.
     unfold params_of_md.
     unfoldSubstitutions.
     apply JFIEqReflRule.
  ++ apply JFIForallIntroRule.
     apply JFIImpliesIntroRule.
     unfoldSubstitutions.
     apply (JFIAndElimRRule s).
     apply JFIAsmRule.
Qed.

(* |- {} let subclass y = new subclass() in let subclass z = new subclass() in y.method(z) { \u . z.field == null } *)
Theorem side_effects_are_visible : forall gamma s, JFIProves (JFIDecls program invariants class method) gamma s
    (JFIHoare
      JFITrue
      (JFLet "subclass" "y" (JFNew JFrwr "subclass" [])
        (JFLet "subclass" "z" (JFNew JFrwr "subclass" [])
          (JFInvoke (JFSyn (JFVar "y")) "method" [(JFSyn (JFVar "z"))])))
      "u" (JFIFieldEq (JFSyn (JFVar "z")) "field" JFnull)).
Proof.
intros.
apply (JFIHTLetRule "y"
    (JFISep JFITrue (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))).
+ apply (JFIHTCsqRule
            JFITrue
            (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse)
        "subclass" "x").
  ++ apply JFIImpliesIntroRule.
     apply (JFIAndElimRRule s).
     apply JFIAsmRule.
  ++ apply JFIHTNewNotNullRule.
  ++ apply JFIForallIntroRule.
     apply JFIImpliesIntroRule.
     unfoldSubstitutions.
     apply (JFITransRule (JFIAnd JFITrue (JFIImplies (JFIEq (JFSyn (JFVar "x")) JFnull) JFIFalse))).
     +++ apply JFIAndIntroRule.
         - apply JFITrueIntroRule.
         - apply (JFIAndElimRRule s).
           apply JFIAsmRule. 
     +++ apply JFISepIntroPersistentRule.
         compute.
         trivial.
+ apply JFIForallIntroRule.
  unfoldSubstitutions.
  apply (JFIHTLetRule "z"
    (JFISep (JFIImplies (JFIEq (JFSyn (JFVar "z")) JFnull) JFIFalse) (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))).
  ++ apply JFIHTFrameRule.
     apply JFIHTNewNotNullRule.
  ++ apply JFIForallIntroRule.
     unfoldSubstitutions.
     apply (JFIHTInvokeRetRule "subclass" method_override "class" (JFIImplies (JFIEq (JFSyn (JFVar "x")) JFnull) JFIFalse) "v" (JFIFieldEq (JFSyn (JFVar "x")) "field" JFnull) "a").
     +++ unfold JFIRefType.
         unfold JFIGammaAdd.
         etransitivity; apply StrMapFacts.add_o.
     +++ compute.
         trivial.
     +++ compute.
         trivial.
     +++ compute.
         apply or_intror.
         apply or_intror.
         apply or_introl.
         trivial.
     +++ apply (JFITransRule
                      (JFISep
                      (JFIImplies (JFIEq (JFSyn (JFVar "z")) JFnull) JFIFalse)
                      (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))).
         - apply (JFIAndElimRRule s).
           apply JFIAsmRule.
         - apply (JFITransRule
                      (JFISep
                      (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse)
                      (JFIImplies (JFIEq (JFSyn (JFVar "z")) JFnull) JFIFalse))).
           -- apply JFISepCommRule.
           -- apply JFISepWeakRule.
     +++ apply JFIImpliesIntroRule.
         unfold method_override; unfoldSubstitutions.
         apply (JFITransRule
            (JFISep
            (JFIImplies (JFIEq (JFSyn (JFVar "z")) JFnull) JFIFalse)
            (JFIImplies (JFIEq (JFSyn (JFVar "y")) JFnull) JFIFalse))).
         - apply (JFIAndElimRRule s).
           apply JFIAsmRule.
         - apply JFISepWeakRule.
     +++ unfoldSubstitutions.
         apply JFIForallIntroRule.
         apply JFIImpliesIntroRule.
         apply (JFIAndElimRRule s).
         apply JFIAsmRule.
Qed.




