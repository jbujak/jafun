
Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Coq.Program.Equality.

Require Import Lists.List.
Import ListNotations.
Require Import JaUtils.
Require Import JaSyntax.
Require Import JaProgram.
Require Import JaSubtype.
Require Import JaProgramWf.
Require Import Jafun.
Require Import JaTactics.
Require Import JaUnique.
Require Import JaEnvs.
Open Scope list_scope.
Open Scope nat_scope.

From Hammer Require Import Reconstr.



Section TypingInProgram.

Variable P : JFProgram.

(*
Hypothesis WFP: Well_formed_program P.
*)




Inductive implies: list bool -> list bool -> Prop :=
| implies_nil:
    implies [] []
| implies_false_whatever:
    forall x tl tl',
      implies tl tl' ->
      implies (false :: tl) (x :: tl')
| implies_true_true:
    forall tl tl',
      implies tl tl' ->
      implies (true :: tl) (true :: tl').

Fixpoint get_types (vs:list JFVal) (gt:nat -> option JFACId) (n:nat) :=
  match vs with
  | [] => []
  | v1 :: tl => (gt n) :: (get_types tl gt (n+1))
  end.


Section TypingInClass.

(* Variable C: JFCId. *)

(* Variable cname: JFClassName. *)
Variable cdecl: JFClassDeclaration.

(* Hypothesis CCname : C = JFClass cname. *)
(*
Hypothesis CdeclInP : find_class P cname = Some cdecl.
*)
(* Variable ex : option JFClassName.
Variable flds : list JFFieldDeclaration.
Variable mthds : list JFMethodDeclaration. *)
(*
Hypothesis CdeclContents : cdecl = JFCDecl cname ex flds mthds.
*)
Section TypingInMethod.

Variable md : JFMethodDeclaration.

(* Hypothesis MethodDeclOK : find_method mthds m = Some md. *)



(*
usunięte
Hypothesis CdeclForC: forall cd,  find_class P cname = Some cd -> cd = cdecl.
Hypothesis CnameForC: forall ex flds mthds,  cdecl = JFCDecl cname ex flds mthds.
Hypothesis ClassInP: exists cd,  find_class P cname = Some cd.
Hypothesis MethodInC: forall cname ex flds mthds,
                        find_class P cname = Some (JFCDecl cname ex flds mthds) -> exists md, (find_method mthds m = Some md).
*)

(**
   The condition between JFACids used in the second part of the ThrOK
   property.
   TODO: w def ThrOK jest chyba błądzik w naszej pracy, bo dwa razy pojawia się C 
         - raz jako parametr ThrOK, a raz w drugiej linijce definicji 

 *)
Definition thrOKCond cacid dacid :=
  match cacid with
  | (C', muC') =>
    match dacid with
    | (D, muD) =>
      subtyping P C' D -> (* subtyping between C' and D *)
        leqAnnLS P (JFClass (name_of_cd cdecl)) (name_of_md md) muC' muD  (* mu compared according to isLS of C,m *)
    end
  end.


(**
   The predicate ThrOK as defined in Section {sec:type-system}.
 *)
Definition thrOK Xi :=
  (isLeqIncluded (leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md)) [(JFNPE,JFatm)] Xi)
  /\
  Forall (fun cacid => Forall (fun dacid => thrOKCond cacid dacid) Xi) Xi.



(*
Reserved Notation "Xi ; Gamma |- E : Acid" (at level 20, no associativity, Gamma at level 60, E at level 60, Acid at level 60).
*)

Inductive types: JFExEnv -> JFEnv -> JFExpr -> JFACId -> Prop :=
| JFtypesNew:
    forall Xi Gamma mu D dname decl vs flds mtps,
      JFClass dname = D ->
      Some decl = find_class P dname -> 
      flds_overline P D  = Some flds -> (* połączenie między flds a mtps *)
      (* Musi zachodzić równość pomiędzy klasą z mtds i flds. Tak jest w papierze. *)
      map class_of_fd flds = map fst mtps -> 
      (isLS md ->
      forall mus, mus = map snd mtps ->
      implies (map ann_of_fd flds) (map (geqAnn_bool mu) mus)) -> 
      typesList Xi Gamma vs (map Some mtps) ->
      (*----------------------------------------*)
      types Xi Gamma (JFNew mu dname vs) (D, mu)

| JFtypesLet:
    forall Xi Gamma mu1 mu2 C1 C2 x E1 E2 xv cname cdecl,
      xv = (JFSyn (JFVar x)) -> 
      Some cdecl = find_class P cname ->
      C1 = JFClass cname ->
      types Xi Gamma E1 (C1, mu1) ->
      types Xi ((xv,(C1,mu1)) :: Gamma) E2 (C2, mu2) ->
      (*--------------------------------------------    TODO: tu powinno być wsadzanie z wywalaniem starego x'a*)
      types Xi Gamma (JFLet cname x E1 E2) (C2, mu2)

| JFtypesIf:
    forall Xi Gamma x1 C1 mu1 x2 mu2 E3 C2 mu3 E4,
      types Xi Gamma (JFVal1 x1) (C1, mu1) ->
      types Xi Gamma (JFVal1 x2) (C1, mu2) ->
      types Xi Gamma E3 (C2, mu3) ->
      types Xi Gamma E4 (C2, mu3) ->
      (*-----------------------------------------*)
      types Xi Gamma (JFIf x1 x2 E3 E4) (C2, mu3)

| JFtypesCall:
    forall Xi Gamma C v m m' vs D dname mu D' mu' mthrs rettyp,
      C = JFClass (name_of_cd cdecl) ->
      m = name_of_md md ->
      D = JFClass dname ->
      (* C, m; Ξ; Γ ⊢ v : ⟨D, μ⟩ *)
      types Xi Gamma (JFVal1 v) (D, mu) ->
      (* ⟨D, μ⟩ ≤: isLS(C,m) parTypM(D, m', 0) *)
      parTypM P D m' 0 = Some (D', mu') ->
      leqIsLS P C m (D, mu) (D', mu') ->
      
      (* thrs(D, m') ≤: isLS(C,m) Ξ *)
      thrs P D m' = Some mthrs ->
      isLeqIncluded (leqIsLS P C m) mthrs Xi ->

      (* isLS(C, m) =⇒ isLS(D, m') *)
      ((isLS md) -> isLSForId P dname m') ->

      (* C, m; Ξ; Γ ⊢ v i : parTypM(D, m', i) for i = 1,..., n *)
      typesList Xi Gamma vs (get_types vs (parTypM P D m') 1) -> 
      retTypM P D m' = Some rettyp ->
      (*--------------------------------------*)
      types Xi Gamma (JFInvoke v m' vs) rettyp

| JFtypesArep:
    forall Xi Gamma v1 D1 D2 x v2 C' fldlst,
      types Xi Gamma (JFVal1 v1) (D1, JFrwr) ->
      (flds_overline P D1) = Some fldlst ->
      In (JFFDecl true C' x) fldlst -> (* TODO: a może użyć searcha efektywnego *)
      (isLS md) ->
      types Xi Gamma (JFVal1 v2) (D2, JFrwr) ->
      subtyping P D2 C' -> (* TODO: a może subtype_class_bool? *)
      (*---------------------------------------------*)
      types Xi Gamma (JFAssign (v1,x) v2) (C', JFrwr)

| JFtypesAreg:
    forall Xi Gamma v1 x v2 C' D1 D2 mu2 fldlst,
      types Xi Gamma (JFVal1 v1) (D1, JFrwr) ->
      (flds_overline P D1) = Some fldlst ->
      In (JFFDecl false C' x) fldlst -> (* TODO: a może użyć searcha efektywnego *)
      (isLS md) ->
      types Xi Gamma (JFVal1 v2) (D2, mu2) ->
      subtyping P D2 C' -> (* TODO: a może subtype_class_bool? *)
      (*-------------------------------------------*)
      types Xi Gamma (JFAssign (v1,x) v2) (C', mu2)

| JFtypesAnls:
    forall Xi Gamma v1 x v2 C' phi D1 mu1 D2 mu2 fldlst,
      types Xi Gamma (JFVal1 v1) (D1, mu1) ->
      (flds_overline P D1) = Some fldlst ->
      In (JFFDecl phi C' x) fldlst -> (* TODO: a może użyć searcha efektywnego *)
      (~ (isLS md)) ->
      types Xi Gamma (JFVal1 v2) (D2, mu2) ->
      subtyping P D2 C' -> (* TODO: a może subtype_class_bool? *)
      (*---------------------------------------------*)
      types Xi Gamma (JFAssign (v1,x) v2) (C', JFrwr)

| JFtypesFrep:
    forall Xi Gamma v x C'' mu C' fldlst,
      types Xi Gamma (JFVal1 v) (C', mu) ->
      leqAnn mu JFrd ->
      (isLS md) ->
      (flds_overline P C') = Some fldlst ->
      In (JFFDecl true C'' x) fldlst -> (* TODO: a może użyć searcha efektywnego *)
      (*-------------------------------------*)
      types Xi Gamma (JFVal2 (v,x)) (C'', mu)
            
| JFtypesFreg:
    forall Xi Gamma v x C'' mu C' fldlst,
      types Xi Gamma (JFVal1 v) (C', mu) ->
      leqAnn mu JFrd ->
      (isLS md) ->
      (flds_overline P C') = Some fldlst ->
      In (JFFDecl false C'' x) fldlst -> (* TODO: a może użyć searcha efektywnego *)
      (*----------------------------------------*)
      types Xi Gamma (JFVal2 (v,x)) (C'', JFatm)


| JFtypesFnls:
    forall Xi Gamma v x C'' mu C' fldlst phi,
      types Xi Gamma (JFVal1 v) (C', mu) ->
      (~ (isLS md)) ->
      (flds_overline P C') = Some fldlst ->
      In (JFFDecl phi C'' x) fldlst -> (* TODO: a może użyć searcha efektywnego *)
      (*----------------------------------------*)
      types Xi Gamma (JFVal2 (v,x)) (C'', JFrwr)

| JFtypesNull:
    forall Xi Gamma,
      (*------------------------------------------------*)
      types Xi Gamma (JFVal1 JFnull) (JFBotClass, JFrwr)

| JFtypesVar:
    forall Xi Gamma x C' mu,
      In (x,(C',mu)) Gamma ->
      (*--------------------------------*)
      types Xi Gamma (JFVal1 x) (C', mu)
            
| JFtypesSubsume:
    forall Xi Gamma C E D' mu' D mu m,
      m = name_of_md md ->
      C = JFClass (name_of_cd cdecl) ->
      leqIsLS P C m (D, mu) (D', mu') ->   
      types Xi Gamma E (D, mu) ->
      (*--------------------------------*)
      types Xi Gamma E (D', mu')

| JFtypesThr:
    forall Xi Gamma C v D mu m,
      m = name_of_md md ->
      C = JFClass (name_of_cd cdecl) ->
      types Xi Gamma (JFVal1 v) (D, mu) ->
      isLeqIncluded (leqIsLS P C m) [(D,mu)] ((JFNPE,JFatm) :: Xi)->
      (*--------------------------------*)
      types Xi Gamma (JFThrow v) (JFBotClass, JFrwr)

| JFtypesTry:
    forall Xi1 Gamma1 E1 mu1 C1 c1name decl x xv E2 C2 mu2 Xi2 Gamma2,
      (* Ξ 2 = Ξ 1 ⊎ ⟨C 1 , μ 1 ⟩ *)
      Xi2 = sumPlus P Xi1 (C1, mu1) ->
      (* ThrOK(C, m; Ξ 2 ) *)
      thrOK Xi2 ->
      (* Γ 2 = Γ 1 , x : ⟨C 1 , μ 1 ⟩ *)
      Some decl = find_class P c1name ->
      C1 = JFClass c1name ->
      xv = JFSyn (JFVar x) ->
      Gamma2 = (xv,(C1, mu1)) :: Gamma1 ->
      (* C, m; Ξ 2 ; Γ 1 ⊢ E 1 : ⟨C 2 , μ 2 ⟩ *)
      types Xi2 Gamma1 E1 (C2, mu2) ->
      (* C, m; Ξ 1 ; Γ 2 ⊢ E 2 : ⟨C 2 , μ 2 ⟩ *)
      types Xi1 Gamma2 E2 (C2, mu2) ->
      (*--------------------------------*)
      (* C, m; Ξ 1 ; Γ 1 ⊢ try {E 1 } catch (μ 1 C 1 x) {E 2 } : ⟨C 2 , μ 2 ⟩ *)
      types Xi1 Gamma1 (JFTry E1 mu1 c1name x E2) (C2, mu2)

with
(* A nie lepiej to zastąpić przez Forall? 
   Chyba nie, bo są kłopoty z negatywnością predykatów *)
typesList: JFExEnv -> JFEnv ->  list JFVal -> list (option JFACId) -> Prop :=
| JFtypesListNil:
    (*--------------------------------------*)
    forall Xi Gamma, typesList Xi Gamma [] []

| JFtypesListCons:
    forall Xi Gamma v vs D mu tps,
      types Xi Gamma  (JFVal1 v) (D, mu) ->
      typesList Xi Gamma vs tps ->
      (*------------------------------------------*)
      typesList Xi Gamma (v :: vs) ( Some (D, mu) :: tps)
.

(*
where
"Xi ; Gamma |- E : Acid" := (types Xi Gamma E Acid).
 *)

Notation "[|  Xi ; Gamma |- E : Acid  |]" := (types Xi Gamma E Acid)
  (at level 0, no associativity, Gamma at level 60, E at level 60, Acid at level 60) : type_scope.

(*   format " '[ |' Xi ';' Gamma '|-' E ':' Acid '|]' ") : type_scope. *)

Notation "[|  Xi ; Gamma |- EE _:_ Acids  |]" := (typesList Xi Gamma EE Acids) (at level 0, no associativity, Gamma at level 60, EE at level 60, Acids at level 60) : type_scope.


(* chwilowo rezygnujemy z odwrotnej (od list) notacji dla Gamma ! *)

(* wydaje się, że w 8.8 będzie można powiedzieć, że Gamma to nie jest
constr tylko cos innego i w ten sposób zakodować listę zupełnie
inaczej *)

(* Notation "Gamma , x : ( C , mu ) " := (cons (x,(C, mu)) Gamma) (at level 59, left associativity, x at level 0, C at level 0, mu at level 0) : env_list_scope.

Notation "Gamma , x : Acid " := (@cons _ (@pair JFVal _ x Acid) Gamma) (at level 59, left associativity, x at level 10, Acid at level 10) : env_list_scope.

Notation "( x , y )" := (@pair _ _ x y) (at level 0, x at level 10, y at level 10, no associativity).
*)




Delimit Scope env_list_scope with env.

Bind Scope env_list_scope with JFEnv.

(* Print JFEnv.

(* Arguments types Xi Gamma%env E Acid. *)

Print types.

Print Grammar constr.
*)
(* 
Open Scope env_list_scope.
 *)

Goal (forall Xi Gamma x E C mu C1 mu1, [| Xi ; (x, (C1, mu1))::Gamma  |- E : (C, mu) |] ->  [| Xi ; (x, (C1,mu1))::Gamma |- [x; x] _:_ [Some (C1,mu1); Some (C1,mu1)]|]).
  intros.
(*  destruct Acid1. *)
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
Qed.


(*
Check (1::2::[ ]).

Check ([(1,2)],[(2,3)])%list.

Print Grammar constr.
*)


(* Tu być może powinniśmy dodać wymaganie, żeby argumenty metody miały różne nazwy *)

Inductive JFmethodTypes : Prop :=
| JFmethodOK:
    forall Xi Gamma,
      thrs_of_md md = Xi ->
      thrOK Xi ->
      par2env cdecl md = Gamma ->
      types Xi Gamma (body_of_md md) (rettyp_of_md md) ->
      (*------------------------------------------*)
      JFmethodTypes.



(** Weakening *)

Hypothesis CdeclInP : find_class P (name_of_cd cdecl) = Some cdecl.



Scheme types_mind := Induction for types Sort Prop with typesList_mind := Induction for typesList Sort Prop.


Lemma weakening_subenv : forall Xi Gamma2 E Acid,
    types Xi Gamma2 E Acid -> forall Gamma1, subenv P cdecl md Gamma1 Gamma2 -> types Xi Gamma1 E Acid.
Proof.
  intros until 1.
  pattern Xi, Gamma2, E, Acid, H.
  eapply types_mind with
  (P1 := (fun Xi Gamma2 EE AA _ =>
            forall Gamma1 : JFEnv, subenv P cdecl md Gamma1 Gamma2 ->
                                   typesList Xi Gamma1 EE AA));
    clear Xi E Acid H; auto 1; try solve [intros; try econstructor; eauto 2].
(* (_ : typesList Xi Gamma EE AA) => *)
  * (* JFLet *)
    intros.
    econstructor; eauto 2.
    apply H0.
    now apply subenv_cons.
  * (* JFVal1 *)
    unfold subenv.
    intros until 1; intros ? H.
    edestruct H as ((D,mu1),H1); try eassumption.
    clear H.
    destruct H1.
    eapply JFtypesSubsume; eauto.
    constructor; auto.
  * (* JFTry *)
    intros until Gamma1; intros.
    eapply JFtypesTry; eauto 2.
    subst Gamma0.
    eauto using subenv_cons.
Qed.  
(*
      types Xi Gamma (JFVal1 JFnull) (JFBotClass, JFrwr)
*)

Hypothesis method_present : methodLookup P (name_of_cd cdecl) (name_of_md md) = Some md.
                                                         
Lemma types_null : forall Gamma Xi Acid, types Xi Gamma (JFVal1 JFnull) Acid.
Proof.
  intros.
  destruct Acid.
  eapply JFtypesSubsume; eauto 1; swap 1 2.
  constructor.
  eapply minimalIsLS.
  eauto.
Qed.


(* Potrzeba sporo jakichś założeń... 
Lemma types_exc : forall Gamma Xi Acid, types Xi Gamma (JFThrow NPE_val) Acid.
Proof.
  intros.
  destruct Acid.
  eapply JFtypesSubsume; eauto 1; swap 1 2.
  eapply JFtypesThr; eauto 1.
  eapply minimalIsLS.
  eauto.
Qed.
*)



(* Semantyka: *)
(* typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid === 
      types Xi1 Gamma E Acid1  i  ta derywacja jest podderywacją derywacji 
      types Xi Gamma (JFExpr_of_JFContext E Ctx) Acid *)

(* W skrócie będziemy to zapisywać C[[E:Acid1]]:Acid *)

(* aktualnie dodana jest reguła subsumpcji, ale nie jest jasne, czy w ogólności potrzebnie *)

(* Subsumpcja jest na pewno potrzebna dla lematu przekształcającego typowanie całego kontekstu 
   w takie właśnie typesCtxExt  (typesCtx_typesCtxExt).

   To jest w sumie taki lemat mówiący, że podwyrażenia się typują 
   - w tej wersji wyłącznie dla podwyrażeń na pozycjach otrzymywalnych kontekstem 
*) 
   

Inductive typesCtxExt :  
  JFExEnv -> JFExEnv -> JFEnv -> JFExpr -> JFACId -> JFContext -> JFACId -> Prop :=

| JFCtypesExpr :
    forall Xi Gamma E Acid,
      types Xi Gamma E Acid ->
      (*-------------------------------------------*)
      typesCtxExt Xi Xi Gamma E Acid [] Acid

| JFCtypesLet :
    forall Xi1 Xi Gamma mu1 mu2 C1 C2 x Ctx E E2 Acid xv cname cdecl,
      xv = (JFSyn (JFVar x)) ->
      Some cdecl = find_class P cname ->
      C1 = JFClass cname ->
      types Xi1 Gamma E (C1, mu1) ->
      types Xi1 ((xv,(C1,mu1)) :: Gamma) E2 (C2, mu2) ->
      typesCtxExt Xi1 Xi Gamma (JFLet cname x E E2) (C2, mu2) Ctx Acid ->
      (*--------------------------------------------*)
      typesCtxExt Xi1 Xi Gamma E (C1, mu1) ((JFCtxLet cname x __ E2)::Ctx) Acid

| JFCtypesTry:
    forall Xi1 Gamma1 Xi Ctx E mu1 C1 c1name decl x xv E2 C2 mu2 Xi2 Gamma2 Acid,
      (* Ξ 2 = Ξ 1 ⊎ ⟨C 1 , μ 1 ⟩ *)
      Xi2 = sumPlus P Xi1 (C1, mu1) ->
      (* ThrOK(C, m; Ξ 2 ) *)
      thrOK Xi2 ->
      (* Γ 2 = Γ 1 , x : ⟨C 1 , μ 1 ⟩ *)
      Some decl = find_class P c1name ->
      C1 = JFClass c1name ->
      xv = JFSyn (JFVar x) ->
      Gamma2 = (xv,(C1, mu1)) :: Gamma1 ->
      (* C, m; Ξ 2 ; Γ 1 ⊢ E 1 : ⟨C 2 , μ 2 ⟩ *)
      types Xi2 Gamma1 E (C2, mu2) ->
      (* C, m; Ξ 1 ; Γ 2 ⊢ E 2 : ⟨C 2 , μ 2 ⟩ *)
      types Xi1 Gamma2 E2 (C2, mu2) -> 
      typesCtxExt Xi1 Xi Gamma1 (JFTry E mu1 c1name x E2) (C2, mu2) Ctx Acid ->
      (*--------------------------------*)
      (* C, m; Ξ 1 ; Γ 1 ⊢ try {E 1 } catch (μ 1 C 1 x) {E 2 } : ⟨C 2 , μ 2 ⟩ *)
      typesCtxExt Xi2 Xi Gamma1 E (C2, mu2) ((JFCtxTry __ mu1 c1name x E2)::Ctx) Acid


| JFCtypesSubsume:
    forall Xi1 Xi Gamma C m E Acid1 Acid1' Ctx Acid,
      m = name_of_md md ->
      C = JFClass (name_of_cd cdecl) ->
      types Xi1 Gamma E Acid1 ->
      leqIsLS P C m Acid1 Acid1' ->   
      typesCtxExt Xi1 Xi Gamma E Acid1' Ctx Acid ->
      (*--------------------------------*)
      typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid.


Notation "[|  Xi ; Gamma |- Ctx [[ Xii ; |- E : Acid1 ]]  : Acid  |]" := (typesCtxExt Xii Xi Gamma E Acid1 Ctx Acid) (at level 0, Xi at level 60, Gamma at level 60, Ctx at level 60, Xii at level 60) : type_scope.


(** [JFExpr_of_JFContext] translates a contextual expression to [JFExpr] *)

Fixpoint JFExpr_of_JFContext (E : JFExpr) (Ctx : JFContext) : JFExpr :=
   match Ctx with
   | [] => E
   | JFCtxLet C x _ E2 :: Ctx' => JFExpr_of_JFContext (JFLet C x E E2) Ctx' 
   | JFCtxTry _ mu C x E2 :: Ctx' => JFExpr_of_JFContext (JFTry E mu C x E2) Ctx' 
   end.

(* C[[E]]:Acid *)
Definition typesCtx (Xi:JFExEnv) (Gamma:JFEnv) (E:JFExpr) (Ctx:JFContext) (Acid:JFACId) : Prop :=
  types Xi Gamma (JFExpr_of_JFContext E Ctx) Acid.


(* C[[E:Acid1]]:Acid -> E:Acid1 *)
Lemma typesCtxExt_types : forall Xi1 Xi Gamma E Acid1 Ctx Acid,
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid -> types Xi1 Gamma E Acid1.
induction 1; trivial.
Qed.

(* C[[E:Acid1]]:Acid -> C[[E]]:Acid1 *)
Lemma typesCtxExt_typesCtx : forall Xi1 Xi Gamma E Acid1 Ctx Acid,
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid -> typesCtx Xi Gamma E Ctx Acid.
induction 1; trivial.
Qed.

(** typing in the empty context: [Xi] is the same *)
Lemma typesCtxExt_noCtx : forall Xi1 Xi Gamma E Acid1 Acid,
    typesCtxExt Xi1 Xi Gamma E Acid1 [] Acid -> Xi = Xi1.
Proof.
  intros.
  dependent induction H; auto.
Qed.

(** typing in the empty context: [[E:Acid1]]:Acid  ->  Acid1 <: Acid *)
Lemma typesCtxExt_noCtx_leq : forall Xi1 Xi Gamma E Acid1 Acid,
    program_contains P JFObjectName = true ->
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    typesCtxExt Xi1 Xi Gamma E Acid1 [] Acid ->
      leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) Acid1 Acid.
Proof.
  intros until 4. intros Htc.
  dependent induction Htc; eauto 3.
Qed.  

(* lemat o tłumaczeniu na Expr łączenia kontekstów *)
(* C'·C[[E]] = C'[[ C[[E]] ]] *)
Lemma JFExpr_of_JFContext_app :
  forall Ctx Ctx' E, JFExpr_of_JFContext E (Ctx ++ Ctx') = JFExpr_of_JFContext (JFExpr_of_JFContext E Ctx) Ctx'.
induction Ctx.
+ trivial.
+ destruct a; intros; simpl; auto.
Qed.  





(* jeśli kontekst da się podzielić, to obie części się ładnie typują *)
(* C·C₁[[E:Acid1]]:Acid ->  ∃ Acid2, C₁[[E:Acid1]]:Acid2  ∧  C[[ C₁[[E]]:Acid2 ]]:Acid *)

Lemma typesCtxExt_typesCtxExt : forall Xi1 Xi Gamma E Acid1 Ctxx Acid, 
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctxx Acid ->
    forall Ctx1 Ctx, Ctxx = Ctx1 ++ Ctx ->
      exists Xi2 Acid2, typesCtxExt Xi1 Xi2 Gamma E Acid1 Ctx1 Acid2
                   /\ typesCtxExt Xi2 Xi Gamma (JFExpr_of_JFContext E Ctx1) Acid2 Ctx Acid.
Proof.
induction 1.
+ intros.
  edestruct app_eq_nil; eauto 1.
  subst.
  do 2 eexists.
  simpl.
  now repeat econstructor.
+ intros.
  edestruct app_cons_alt as [(?,?)|(Ctx1',(?,EQind))]; eauto 1.
  * subst.
    do 2 eexists.
    split.
    **
      now constructor.
    **
      econstructor; eauto 1.
  * symmetry in EQind.
    eapply IHtypesCtxExt in EQind.
    destruct EQind as (Xi2, (Acid2, (?, ?))).
    do 2 eexists; eauto.
    subst Ctx1.
    split.
    ** 
      econstructor; eauto.
    **
      assumption.
+ intros.      
  edestruct app_cons_alt as [(?,?)|(Ctx1',(?,EQind))]; eauto 1.
  * subst.
    do 2 eexists.
    split.
    **
      now constructor.
    **
      econstructor; eauto 1.
  * symmetry in EQind.
    eapply IHtypesCtxExt in EQind.
    destruct EQind as (Xi2', (Acid2, (?, ?))).
    do 2 eexists; eauto.
    subst Ctx1.
    split.
    ** 
      econstructor; eauto.
    **
      assumption.
+ intros until 0.
  intro EQind.
  eapply IHtypesCtxExt in EQind.
  destruct EQind as (Xi2', (Acid2, (?, ?))).
  do 2 eexists; eauto.
  split; try eassumption.
  econstructor; eassumption.
Qed.



    
(* kontekst można rozszerzyć o inny kontekst *)
(* C₁[[E:Acid1]]:Acid2  ∧  C[[ C₁[[E]]:Acid2 ]]:Acid  →  C·C₁[[E:Acid1]]:Acid  *)
Lemma typesCtxExt_concat : forall Xi1 Xi2 Gamma E Acid1 Ctx1 Acid2, 
    typesCtxExt Xi1 Xi2 Gamma E Acid1 Ctx1 Acid2 ->
      forall Xi Ctx Acid, typesCtxExt Xi2 Xi Gamma (JFExpr_of_JFContext E Ctx1) Acid2 Ctx Acid
                     -> typesCtxExt Xi1 Xi Gamma E Acid1 (Ctx1++Ctx) Acid.
Proof.
induction 1. 
+ trivial.
+ simpl.
  intros.
  econstructor; eauto 1.
  auto.
+ simpl.
  intros.
  econstructor; eauto 1.
  auto.
+ simpl.
  intros.
  econstructor; eauto 1.
  auto.
Qed.   
  

      
(* można podmienić E w typowaniu kontekstowym *)
(* C[[E:Acid1]]:Acid  ∧  E':Acid1  →  C[[E':Acid1]]:Acid *)
Lemma typesCtxExt_replaceE : forall Xi1 Xi Gamma E Acid1 Ctx Acid, 
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid ->
    forall E',
    types Xi1 Gamma E' Acid1 ->
    typesCtxExt Xi1 Xi Gamma E' Acid1 Ctx Acid.
Proof.
induction 1.
+ intros; now constructor.
+ intros.
  econstructor; eauto 1.
  apply IHtypesCtxExt.
  econstructor; eauto 1.
+ intros.
  econstructor; eauto 1.
  apply IHtypesCtxExt.
  eapply JFtypesTry; eauto 1.
+ intros.
  econstructor; eauto 1.
  apply IHtypesCtxExt.
  destruct Acid1.
  destruct Acid1'.
  econstructor; eauto 1.
Qed.    



(* wewnętrzną część kontekstu można podmienić... *)
(* CC₁[[E:Acid1]]:Acid  →  C₁[[E:Acid1]]:Acid2  →  C[[ C₁[[E]]:Acid2 ]]:Acid 
                        → C₁'[[E':Acid1']]:Acid2 → CC₁'[[E':Acid1']]:Acid   *)

Lemma typesCtxExt_replaceCtx : forall Xi1 Xi Gamma E Acid1 Ctxx Acid, 
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctxx Acid ->
    forall Ctx1 Ctx, Ctxx = Ctx1 ++ Ctx ->
      forall Xi2 Acid2, typesCtxExt Xi1 Xi2 Gamma E Acid1 Ctx1 Acid2
         -> typesCtxExt Xi2 Xi Gamma (JFExpr_of_JFContext E Ctx1) Acid2 Ctx Acid ->
           forall Xi1' E' Ctx1' Acid1', typesCtxExt Xi1' Xi2 Gamma E' Acid1' Ctx1' Acid2
              -> typesCtxExt Xi1' Xi Gamma E' Acid1' (Ctx1'++Ctx) Acid.
Proof.
  intros.
  clear H1.
  eapply typesCtxExt_concat; eauto 1.
  eapply typesCtxExt_replaceE; eauto 1.
  eapply typesCtxExt_typesCtx; eauto 1.
Qed.



(* Lematy i taktyki o tym jak wygląda kontekst i wyrażenie w nim, jeśli całość jest jakaś, np: *)
(* C[[E]]=New  →  E=New ∧  C=[] *) 
Lemma JFExpr_of_JFContext_JFNew :
  forall Ctx E mu cn vs, JFNew mu cn vs = JFExpr_of_JFContext E Ctx ->
    JFNew mu cn vs = E  /\  Ctx = [].
induction Ctx as [ | a ? IHCtx]; simpl.
+ auto.
+ intros until 0; intro H; destruct a; apply IHCtx in H; destruct H as [H _]; discriminate H.
Qed.     

Local Ltac simplify_wrong_context Ctx :=
  let H:=fresh in
  induction Ctx as [ |a ? IHCtx]; simpl; [
    auto
  | intros until 0; intro H; destruct a; apply IHCtx in H; destruct H as [H _]; discriminate H].


Lemma JFExpr_of_JFContext_JFIf :
  forall Ctx E v1 v2 E1 E2, JFIf v1 v2 E1 E2 = JFExpr_of_JFContext E Ctx ->
    JFIf v1 v2 E1 E2 = E  /\  Ctx = [].
simplify_wrong_context Ctx.
Qed.

Lemma JFExpr_of_JFContext_JFInvoke :
  forall Ctx E v m vs, JFInvoke v m vs = JFExpr_of_JFContext E Ctx ->
    JFInvoke v m vs = E  /\  Ctx = [].
simplify_wrong_context Ctx.
Qed.

Lemma JFExpr_of_JFContext_JFAssign :
  forall Ctx E vx v, JFAssign vx v = JFExpr_of_JFContext E Ctx ->
    JFAssign vx v = E  /\  Ctx = [].
simplify_wrong_context Ctx.
Qed.

Lemma JFExpr_of_JFContext_JFVal1 :
  forall Ctx E v, JFVal1 v = JFExpr_of_JFContext E Ctx ->
    JFVal1 v = E  /\  Ctx = [].
simplify_wrong_context Ctx.
Qed.

Lemma JFExpr_of_JFContext_JFVal2 :
  forall Ctx E vx, JFVal2 vx = JFExpr_of_JFContext E Ctx ->
    JFVal2 vx = E  /\  Ctx = [].
simplify_wrong_context Ctx.
Qed.

Lemma JFExpr_of_JFContext_JFThrow :
  forall Ctx E v, JFThrow v = JFExpr_of_JFContext E Ctx ->
    JFThrow v = E  /\  Ctx = [].
simplify_wrong_context Ctx.
Qed.

(* zamiana zmiennych typu unit na konstruktory tt (aka __) *)
Ltac dunit := match goal with [ u : unit |- _ ] => destruct u end.


(* C[[E]]=Let  →  E=Let ∧  C=[]    ∨    C[[E]]=Let·C'[[E]] *) 
Lemma JFExpr_of_JFContext_JFLet : 
  forall Ctx E C v E1 E2, JFLet C v E1 E2 = JFExpr_of_JFContext E Ctx ->
      JFLet C v E1 E2 = E  /\  Ctx = []    \/
      exists Ctx', Ctx = Ctx' ++ [JFCtxLet C v __ E2]  /\  E1 = JFExpr_of_JFContext E Ctx'. 
induction Ctx as [ |a ? IHCtx].
+ simpl; auto.
+ intros until 0. intro H. right. destruct a.
  * apply IHCtx in H.
    destruct H as [(H,?) | ?].
    **
      subst Ctx.
      exists [].
      simpl.
      dunit.
      split; congruence.
    **
      destruct H as [Ctx' [? ? ] ].
      evar (c : JFContextNode).
      exists (c :: Ctx').
      subst c.
      sauto.

  * apply IHCtx in H.
    destruct H as [? | ?].
    **
      sauto.
    **
      destruct H as [Ctx' [? ? ] ].
      evar (c : JFContextNode). 
      exists (c :: Ctx').
      subst c.
      sauto.
Qed.

(* C[[E]]=Try  →  E=Try ∧  C=[]    ∨    C[[E]]=Try·C'[[E]] *) 
Lemma JFExpr_of_JFContext_JFTry : 
  forall Ctx E mu C v E1 E2, JFTry E1 mu C v E2 = JFExpr_of_JFContext E Ctx ->
      JFTry E1 mu C v E2 = E  /\  Ctx = []    \/
      exists Ctx', Ctx = Ctx' ++ [JFCtxTry __ mu C v E2]  /\  E1 = JFExpr_of_JFContext E Ctx'. 
induction Ctx as [ |a ? IHCtx].
+ simpl; auto.
+ intros until 0. intro H. right. destruct a.
  * apply IHCtx in H.
    destruct H as [? | ?].
    **
      sauto. 
    **
      destruct H as [Ctx' [? ?] ].
      evar (c : JFContextNode). 
      exists (c :: Ctx').
      subst c.
      sauto.

  * apply IHCtx in H.
    destruct H as [(H,?) | ?].
    **
      subst Ctx.
      exists [].
      simpl.
      dunit.
      split; congruence.
    **
      destruct H as [Ctx' [? ?] ].
      evar (c : JFContextNode). 
      exists (c :: Ctx').
      subst c.
      sauto.
Qed.



(* wybór lematu upraszczającego *)
Local Ltac do_simplify_EC H E Ctx t :=
  match t with
  | JFNew _ _ _ => (* idtac "JFNew"; *) apply JFExpr_of_JFContext_JFNew in H
  | JFIf _ _ _ _ => (* idtac "JFIf"; *) apply JFExpr_of_JFContext_JFIf in H
  | JFInvoke _ _ _ => (* idtac "JFInvoke"; *) apply JFExpr_of_JFContext_JFInvoke in H
  | JFAssign _ _ => (* idtac "JFAssign"; *) apply JFExpr_of_JFContext_JFAssign in H
  | JFVal1 _ => (* idtac "JFVal1"; *) apply JFExpr_of_JFContext_JFVal1 in H
  | JFVal2 _ => (* idtac "JFVal2"; *) apply JFExpr_of_JFContext_JFVal2 in H
  | JFThrow _ => (* idtac "JFThrow"; *) apply JFExpr_of_JFContext_JFThrow in H
  | JFLet _ _ _ _ => (* idtac "JFLet"; *) apply JFExpr_of_JFContext_JFLet in H; destruct H as [H|H]
  | JFTry _ _ _ _ _ => (* idtac "JFTry"; *) apply JFExpr_of_JFContext_JFTry in H; destruct H as [H|H]
  end.

(* jeśli H : C[[E]]=coś to uprość odp lematem w zależności od coś *)
Ltac simplify_EC_hyp H :=
  match type of H with
  | (JFExpr_of_JFContext ?E ?Ctx = ?t) => symmetry in H; do_simplify_EC H E Ctx t
  | (?t = JFExpr_of_JFContext ?E ?Ctx) => do_simplify_EC H E Ctx t
  end.


(* znajdź H: C[[E]]=coś i uprość oraz posprzątaj *)
Ltac simplify_EC :=
  match goal with
  | [ H : (JFExpr_of_JFContext ?E ?Ctx = ?t) |- _ ] =>
    symmetry in H;
    do_simplify_EC H E Ctx t;
    destruct H;
    try subst Ctx;
    try subst E
  | [ H : (?t = JFExpr_of_JFContext ?E ?Ctx) |- _ ] =>
    do_simplify_EC H E Ctx t;
    destruct H;
    try subst Ctx;
    try subst E
  end.

(* da się zwiększyć typ całościowy typowania w kontekście *)
(* C[[E:Acid1]]:Acid'  →  Acid' ≤: Acid  →  C[[E:Acid1]]:Acid *)
Lemma typesCtxExt_subsume : forall Xi1 Xi Gamma E Acid1 Ctx Acid' Acid,
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid' ->
    leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) Acid' Acid ->
    typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid.
Proof.
  intros until 0; intros H Hleq.
  replace Ctx with (Ctx++[]) by auto with datatypes.
  (* na tym [] robimy subsumpcję! :) *)
  eapply typesCtxExt_concat; try eassumption.
  eapply typesCtxExt_typesCtx in H.
  eapply JFCtypesSubsume; eauto 1.  
  econstructor.
  destruct Acid.
  destruct Acid'.
  eapply JFtypesSubsume; eauto 1.
Qed.  




(* Nie jestem pewien czy to potrzebne, ale powinno zachodzić... *)

(* Poniżej założenia dla leqIsLS_refl i leqIsLS_trans *) 
Hypothesis cdeclOK : find_class P (name_of_cd cdecl) = Some cdecl.


(* Z typowania kontekstu wynika typowanie w kontekście *)
(* C[[E]]:Acid → ∃ Acid1, C[[E:Acid1]]:Acid *)
Lemma typesCtx_typesCtxExt :
  forall Xi Gamma E Ctx Acid, typesCtx Xi Gamma E Ctx Acid ->
    exists Xi1 Acid1, typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid.
Proof.
  unfold typesCtx.
  intros until 0.
  intro H.
  dependent induction H; try (
    simplify_EC;
    do 2 eexists;
    econstructor; econstructor; eassumption
  ).
  
  * (* Let *)
    clear IHtypes2.
    simplify_EC_hyp x.
    **
      destruct x.
      subst E.
      subst Ctx.
      do 2 eexists;
        econstructor; econstructor; eassumption.
    **
      destruct x as (Ctx', (?, EqE1)).
      subst Ctx.
      edestruct IHtypes1 as (Xi1,(Acid1,HtEC')); try eassumption.
      do 2 eexists.
      eapply typesCtxExt_concat.
      ***
        eassumption.
      ***
        rewrite <- EqE1.
        eapply JFCtypesSubsume; [eauto | eauto | ..]; swap 2 3.
        ****
          apply typesCtxExt_typesCtx in HtEC'.
          red in HtEC'.      
          now rewrite <- EqE1 in HtEC'.
        ****
          econstructor; eauto 1.
          econstructor.
          econstructor; eassumption.
        ****
          eapply leqIsLS_refl; eauto 1.

  * (* Subsume *)
    edestruct IHtypes as (Xi1,(Acid1,HtEC')); eauto 1.
    do 2 eexists.
    eapply typesCtxExt_subsume; eassumption.

  * (* Try *)
    clear IHtypes2.
    simplify_EC_hyp x.
    **
      destruct x.
      subst E.
      subst Ctx.
      do 2 eexists;
        econstructor; econstructor; eassumption.
    **
      destruct x as (Ctx', (?, EqE1)).
      subst Ctx.
      edestruct IHtypes1 as (Xi1',(Acid1,HtEC')); try eassumption.
      do 2 eexists.
      eapply typesCtxExt_concat.
      ***
        eassumption.
      ***
        rewrite <- EqE1.
        eapply JFCtypesSubsume; [eauto | eauto | ..]; swap 2 3.
        ****
          apply typesCtxExt_typesCtx in HtEC'.
          red in HtEC'.      
          now rewrite <- EqE1 in HtEC'.
        ****
          econstructor; eauto 1.
          econstructor.
          econstructor; eassumption.
        ****
          eapply leqIsLS_refl; eauto 1.
Qed.


(* To jest potrzebne dla leqIsLS_trans *)

Hypothesis progObj : 
 program_contains P JFObjectName = true.
Hypothesis progNamesUniq : 
 names_unique P.
Hypothesis progObjNotExt : 
 object_is_not_extended P.
Hypothesis progExtAllButObj :
 extensions_in_all_but_object P.

(* Pierwsza wersja lematu typesCtx_typesCtxExt, w którym typ wynikowy może być nieco mniejszy... *)
(* Chyba aktualnie do usunięcia *)
(* C[[E]]:Acid  →  ∃ Acid1 Acid',  C[[E:Acid1]]:Acid'  ∧  Acid' ≤: Acid ∧ Xi1 = (sumPlusCtx Xi Ctx) *)
Lemma typesCtx_typesCtxExt_leq :
  forall Xi Gamma E Ctx Acid, typesCtx Xi Gamma E Ctx Acid ->
    exists Xi1 Acid1 Acid', typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid' /\
                            leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) Acid' Acid /\
                            Xi1 = (sumPlusCtx P Xi Ctx).
Proof.
  unfold typesCtx.
  intros until 0.
  intro H.
  dependent induction H; try ( 
    simplify_EC;
    do 3 eexists;
    split; [econstructor; econstructor; eassumption|
            split; [eapply leqIsLS_refl; eauto 1|simpl;auto 2] ]).
  
  * (* Let *)
    clear IHtypes2.
    simplify_EC_hyp x.
    **
      destruct x.
      subst E.
      subst Ctx.
      do 3 eexists;
        split; [
          econstructor; econstructor; eassumption
        | split; [eapply leqIsLS_refl; eauto 1|simpl;auto 2] ].
    **
      destruct x as (Ctx', (?, EqE1)).
      subst Ctx.
      edestruct IHtypes1 as (Xi1,(Acid1,(Acid',(HtEC',(LeqIsLS,?))))); try eassumption.
      do 3 eexists.
      split.
      ***
        eapply typesCtxExt_concat.
        ****
          eassumption.
        ****
          rewrite <- EqE1.
          eapply JFCtypesSubsume; [eauto | eauto | ..].
          *****
            apply typesCtxExt_typesCtx in HtEC'.
            red in HtEC'.      
            now rewrite <- EqE1 in HtEC'.
          *****
            eassumption.
          *****
            econstructor; eauto 1.
            econstructor.
            econstructor; eassumption.
      ***
        split;try eapply leqIsLS_refl; eauto 1.
        rewrite sumPlusCtxLet;eauto 1.

  * (* Subsume *)
    edestruct IHtypes as (Xi1,(Acid1,(Acid',(HtEC',(LeqIsLs,?))))); eauto 1.
    do 3 eexists.
    split. (* ; swap 1 2. *)
    **
      eassumption.
    **
      split; try eapply leqIsLS_trans; eauto 1. 

  * (* Try *)
    clear IHtypes2.
    simplify_EC_hyp x.
    **
      destruct x.
      subst E.
      subst Ctx.
      do 3 eexists;
        split; [
          econstructor; econstructor; eassumption
        | split; [eapply leqIsLS_refl; eauto 1|simpl;auto] ].
    **
      destruct x as (Ctx', (?, EqE1)).
      subst Ctx.
      edestruct IHtypes1 as (Xi1',(Acid1,(Acid',(HtEC',(LeqIsLS,?))))); try eassumption.
      do 3 eexists.
      split.
      ***
        eapply typesCtxExt_concat.
        ****
          eassumption.
        ****
          rewrite <- EqE1.
          eapply JFCtypesSubsume; [eauto | eauto | ..].
          + apply typesCtxExt_typesCtx in HtEC'.
            red in HtEC'.      
            now rewrite <- EqE1 in HtEC'.

          + eassumption.
            
          + econstructor; eauto 1.
            econstructor.
            econstructor; eassumption.
      ***
        split;try eapply leqIsLS_refl; eauto 1.
        subst Xi2 Xi1' C1.
        rewrite sumPlusCtxTry;eauto.
Qed.


(* Lemat typesCtx_typesCtxExt jako konsekwencja typesCtx_typesCtxExt_leq i typesCtxExt_subsume *)
(* C[[E]]:Acid → ∃ Acid1, C[[E:Acid1]]:Acid *)
Lemma typesCtx_typesCtxExt1 :
  forall Xi Gamma E Ctx Acid, typesCtx Xi Gamma E Ctx Acid ->
    exists Xi1 Acid1, typesCtxExt Xi1 Xi Gamma E Acid1 Ctx Acid.
Proof.
  intros until 0.
  intros H.
  apply typesCtx_typesCtxExt_leq in H.
  destruct H as (Xi1, (Acid1, (Acid', (?, (?, ?))))).
  do 2 eexists.
  eapply typesCtxExt_subsume in H; eassumption.
Qed.
  

(** weakening for context expressions *)
Lemma typesCtx_subenv : forall Gamma1 Gamma2 Xi E Ctx Acid,
      subenv P cdecl md Gamma1 Gamma2 ->
      typesCtx Xi Gamma2 E Ctx Acid -> typesCtx Xi Gamma1 E Ctx Acid.
Proof.
  intros.
  eapply weakening_subenv; eauto 1.
Qed.


(** weakening for context expressions *)
Lemma typesCtxExt_subenv : forall Gamma1 Gamma2 Xi1 Xi E Ctx Acid Acid1,
      subenv P cdecl md Gamma1 Gamma2 ->
      typesCtxExt Xi1 Xi Gamma2 E Acid1 Ctx Acid ->
      typesCtxExt Xi1 Xi Gamma1 E Acid1 Ctx Acid.
Proof.
  intros until 1.
  induction 1.
  + constructor; eauto using weakening_subenv.
  + econstructor; eauto using weakening_subenv, subenv_cons.
  + econstructor; subst; eauto using weakening_subenv, subenv_cons.
  + econstructor; eauto using weakening_subenv, subenv_cons.
Qed.


(** replacing expression and environment for context expressions *)
Lemma typesCtxExt_replaceEG : forall Gamma2 Xi1 Xi E Ctx Acid Acid1,
    typesCtxExt Xi1 Xi Gamma2 E Acid1 Ctx Acid ->
    forall Gamma1 E',
      subenv P cdecl md Gamma1 Gamma2 ->
      types Xi1 Gamma1 E' Acid1 -> 
      typesCtxExt Xi1 Xi Gamma1 E' Acid1 Ctx Acid.
Proof.
  induction 1.
  - now constructor.
  - intros * Hsub ?.
    eapply subenv_cons in Hsub as Hsubc.
    econstructor 2; eauto 1.
    + eapply weakening_subenv; eauto 1.
    + apply IHtypesCtxExt; eauto 1.
      eapply JFtypesLet; eauto 1.
      eapply weakening_subenv; eauto 1.
  - intros * Hsub ?.
    subst Gamma2.
    eapply subenv_cons in Hsub as Hsubc.
    econstructor 3; eauto 1.
    + eapply weakening_subenv; eauto 1.
    + apply IHtypesCtxExt; eauto 1.
      eapply JFtypesTry; eauto 1.
      eapply weakening_subenv; eauto 1.
  - intros * Hsub ?.
    econstructor 4; eauto 1.
    apply IHtypesCtxExt; eauto 1.
    destruct Acid1, Acid1'.
    eapply JFtypesSubsume; eauto 1.
Qed.

    
(** Inversion lemmas *)

Lemma Inversion_JFNew :
  forall Xi Gamma mu dname vs Acid,
    types Xi Gamma (JFNew mu dname vs) Acid ->
    exists flds mtps decl D,
      JFClass dname = D /\
      Some decl = find_class P dname /\  
      flds_overline P D  = Some flds /\
      map class_of_fd flds = map fst mtps /\
      (isLS md -> 
      forall mus, mus = map snd mtps ->
      implies (map ann_of_fd flds) (map (geqAnn_bool mu) mus)) /\
      typesList Xi Gamma vs (map Some mtps) /\
      (*----------------------------------------*)
      types Xi Gamma (JFNew mu dname vs) (D, mu) /\
      leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) (D,mu) Acid.

Proof.      
  intros * H.
  dependent induction H.
  + repeat eexists; eauto 2.
    eapply JFtypesNew; eauto 1.
  + edestruct IHtypes as (flds & mtps & decl & D0 & H); eauto 1.
    decompose_and H.
    subst D0.
    repeat eexists; eauto 2.
Qed.    

Lemma Inversion_JFIf :
    forall Xi Gamma x1 x2 E3 E4 Acid,
      types Xi Gamma (JFIf x1 x2 E3 E4) Acid -> 
      exists C1 mu1 mu2 C2 mu3,
      types Xi Gamma (JFVal1 x1) (C1, mu1) /\
      types Xi Gamma (JFVal1 x2) (C1, mu2) /\
      types Xi Gamma E3 (C2, mu3) /\
      types Xi Gamma E4 (C2, mu3) /\
      (*----------------------------------------*)
      types Xi Gamma (JFIf x1 x2 E3 E4) (C2, mu3) /\
      leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) (C2,mu3) Acid. 
Proof.
  intros until 0.
  intro H.
  dependent induction H.
  + 
    clear IHtypes1 IHtypes2 IHtypes3 IHtypes4.
    do 5 eexists.
    repeat (split; try eassumption). 
    * econstructor; eassumption.
    * eapply leqIsLS_refl; eauto 1.
  +
    edestruct IHtypes as [C1 H]; eauto.
    clear IHtypes.
    decompose_ex H.
    decompose [and] H; clear H.
    do 5 eexists.
    repeat (split; try eassumption).
    eapply leqIsLS_trans; eauto 1.
Qed.

Lemma inversion_JFInvoke:
  forall C m Xi Gamma v m' vs C'' mu'',
    Well_formed_program P ->
    C = JFClass (name_of_cd cdecl) ->
    find_class P (name_of_cd cdecl) = Some cdecl ->
    m = name_of_md md ->
    types Xi Gamma (JFInvoke v m' vs) (C'', mu'') ->
    exists D dname mu D' mu' mthrs rettyp,
      D = JFClass dname /\
      types Xi Gamma (JFVal1 v) (D, mu) /\
      parTypM P D m' 0 = Some (D', mu') /\
      leqIsLS P C m (D, mu) (D', mu') /\
      thrs P D m' = Some mthrs   /\
      isLeqIncluded (leqIsLS P C m) mthrs Xi /\
      ((isLS md) -> isLSForId P dname m') /\
      typesList Xi Gamma vs (get_types vs (parTypM P D m') 1) /\
      retTypM P D m' = Some rettyp /\
      leqIsLS P C m rettyp (C'', mu'') /\
      (*--------------------------------------*)
      types Xi Gamma (JFInvoke v m' vs) rettyp.
Proof.
  intros C m Xi Gamma v m' vs C'' mu'' Wfp Ceq FclsPC meq Tps.
  unfold Well_formed_program in Wfp.
  destruct Wfp as [Neq [PCObj [PCNPE [Onextd [Extns Swfd] ] ] ] ].
  dependent induction Tps.
  + (* JFtypesCall *)
    clear IHTps.
    do 7 eexists.
    repeat split; eauto 1.
    * eapply leqIsLS_refl; eauto 1.
    * eapply JFtypesCall; eauto 1.
  + (* JFtypesSubsume *)
    edestruct IHTps as (D0, (dname, (mu0, (D', (mu', (mthrs, (rettyp, IHTps1))))))); eauto 1.
    decompose [and] IHTps1.
    subst D0.
    do 7 eexists.
    repeat split; eauto 1.
    eapply leqIsLS_trans; eauto 1.
Qed.       


Lemma Inversion_JFAssign :
  Well_formed_program P -> 
  forall Xi Gamma v1 x v2 Acid, 
    types Xi Gamma (JFAssign (v1,x) v2) Acid ->
    exists D1 mu1 fldlst C' phi D2 mu2 mu3 ,
      types Xi Gamma (JFVal1 v1) (D1, mu1) /\
      (flds_overline P D1) = Some fldlst /\
      In (JFFDecl phi C' x) fldlst /\ 
      (isLS md -> mu1 = JFrwr /\ mu2 = mu3 /\ (phi = true -> mu2 = JFrwr (* = mu3 *) )) /\
      (~ isLS md -> mu3 = JFrwr) /\
      types Xi Gamma (JFVal1 v2) (D2, mu2) /\
      subtyping P D2 C' /\
      (*----------------------------------------*)
      types Xi Gamma (JFAssign (v1,x) v2) (C', mu3) /\
      leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) (C',mu3) Acid.
Proof.
  intros WfP * H.
  dependent induction H.
  - clear IHtypes1 IHtypes2.
    do 8 eexists.
    repeat (ssplit; eauto 2).
    + intuition. 
    + eapply JFtypesArep; eauto 1.
  - clear IHtypes1 IHtypes2.
    do 8 eexists.
    ssplit; try eassumption; cycle 2.
    + eapply JFtypesAreg; eauto 1.
    + eauto 2.
    + intuition.
    + intuition.
  - clear IHtypes1 IHtypes2.
    do 8 eexists.
    ssplit; try eassumption; cycle 2.
    + eapply JFtypesAnls; eauto 1.
    + eauto 2.
    + intuition.
    + intuition.
  - edestruct IHtypes as (D1,Htmp); eauto 2.
    decompose_ex Htmp.
    decompose_and Htmp.
    do 8 eexists.
    ssplit; eauto 1.
    eapply leqIsLS_trans; eauto 1.
Qed.    


Lemma Inversion_JFVal2 : forall Xi Gamma v x Acid,
    types Xi Gamma (JFVal2 (v,x)) Acid ->
    exists C' C'' mu mu' fldlst rep,
      types Xi Gamma (JFVal1 v) (C', mu) /\
      (isLS md -> leqAnn mu JFrd) /\
      flds_overline P C' = Some fldlst /\
      In (JFFDecl rep C'' x) fldlst /\ (* TODO: a może użyć searcha efektywnego *)
      (isLS md -> mu' = if rep then mu else JFatm) /\
      (~isLS md -> mu' = JFrwr) /\
      (*-------------------------------------*)
      types Xi Gamma (JFVal2 (v,x)) (C'', mu') /\
      leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) (C'',mu') Acid.
Proof.      
  intros until 0.
  intro H.
  dependent induction H.
  + clear IHtypes.
    do 6 eexists.
    repeat (split; eauto 1).
    * tauto.
    * eapply JFtypesFrep; eauto 1.
    * eapply leqIsLS_refl; eauto 1.
  + clear IHtypes.
    do 6 eexists.
    repeat (split; eauto 1).
    * tauto.
    * eapply JFtypesFreg; eauto 1.
    * eapply leqIsLS_refl; eauto 1.
  + clear IHtypes.
    do 6 eexists.
    repeat (apply conj; try eassumption).
    * contradiction.
    * contradiction.
    * eauto 1.
    * eapply JFtypesFnls; eauto 1.
    * eapply leqIsLS_refl; eauto 1.
  + edestruct IHtypes as [C' H]; eauto.
    clear IHtypes.
    decompose_ex H.
    decompose [and] H; clear H.
    do 6 eexists.
    repeat (split; try eassumption).
    eapply leqIsLS_trans; eauto 1.
Qed.    




Lemma Inversion_JFVal1 :
  forall Xi Gamma x Acid,
    Well_formed_program P ->
    types Xi Gamma (JFVal1 x) Acid ->
    x = JFnull
    \/
    exists C' mu,
      In (x, (C', mu)) Gamma /\
      types Xi Gamma (JFVal1 x) (C', mu) /\
      leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) (C',mu) Acid.
Proof.
  intros * Hwf H.
  dependent induction H.
  + auto.
  + right.
    eapply JFtypesVar in H as H'.
    do 2 eexists; eauto 4.
  + edestruct IHtypes as [?|H]; eauto 2.
    right.
    decompose_ex H.
    decompose_and H.
    do 2 eexists; ssplit; eauto 2.
Qed.    

Lemma inversion_JFVal1_nonnull:
  forall Xi Gamma x C' mu' cname mname,
    Well_formed_program P ->
    types Xi Gamma (JFVal1 x) (C', mu') ->
    cname = name_of_cd cdecl ->
    mname = name_of_md md ->
    find_class P cname = Some cdecl ->
    x <> JFnull ->
    exists C'' mu'',
      leqIsLS P (JFClass cname) mname (C'', mu'') (C', mu') /\
      In (x,(C'',mu'')) Gamma /\
      (*--------------------------------*)
      types Xi Gamma (JFVal1 x) (C'', mu'').
Proof.
  intros Xi Gamma x C' mu' cname mname Wfp Tps cneq mneq Fcls nonull.
  unfold Well_formed_program in Wfp.
  decompose [and] Wfp.
  clear Wfp.
  dependent induction Tps.
  + contradiction.
  + (* JFVal1 rule *)
    exists C', mu'.
    repeat split; eauto using JFtypesVar.
  + (* JFtypesSubsume *)
    assert (exists (C'' : JFCId) (mu'' : JFAMod),
               leqIsLS P (JFClass cname) mname (C'', mu'') (D, mu) /\
               In (x, (C'', mu'')) Gamma /\
               types Xi Gamma (JFVal1 x) (C'', mu'')) by auto.
    destruct H6 as [C''];destruct H6 as [mu''].
    exists C'', mu''.
    decompose [and] H6.
    split; [ |split].
    ++ subst.
       eapply leqIsLS_trans; try apply Fcls; try apply H7; auto.
    ++ auto.
    ++ auto.
Qed.



Lemma inversion_Throw:
  forall Xi Gamma v D mu,
    types Xi Gamma (JFThrow v) (D, mu) ->
    exists m C D' mu',
           m = name_of_md md /\
           C = JFClass (name_of_cd cdecl) /\
           types Xi Gamma (JFVal1 v) (D', mu') /\
           isLeqIncluded (leqIsLS P C m) [(D',mu')] ((JFNPE,JFatm) :: Xi) /\
           (*--------------------------------*)
           types Xi Gamma (JFThrow v) (JFBotClass, JFrwr).
Proof.
  intros Xi Gamma v D mu Tps.
  exists (name_of_md md).
  exists (JFClass (name_of_cd cdecl)).
  dependent induction Tps.
  * (* subtyping *)
    assert (exists (D' : JFCId) (mu' : JFAMod),
            name_of_md md = name_of_md md /\
            JFClass (name_of_cd cdecl) = JFClass (name_of_cd cdecl) /\
            types Xi Gamma (JFVal1 v) (D', mu') /\
            isLeqIncluded
              (leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md))
              [(D', mu')] ((JFNPE, JFatm) :: Xi) /\
            types Xi Gamma (JFThrow v) (JFBotClass, JFrwr)).
    (*    apply (IHTps v D0 mu0); try auto. *)
    eapply IHTps; eauto 1.
    destruct H as [D1].
    destruct H as [mu1].
    exists D1, mu1.
    auto.
  * (* JFThrow rule *)
    clear IHTps.
    exists D0, mu0.
    repeat split; try auto; eapply JFtypesThr; eauto.
Qed.






End TypingInMethod.





Definition JFFieldClassInProg (fd:JFFieldDeclaration) :=
  match fd with
  |  JFFDecl _ (JFClass dname) _ =>
     let ddecl := find_class P dname
     in match ddecl with
        | Some _ => True
        | None => False
        end
  |  JFFDecl _ JFBotClass _ => False
  end.


(** fields from Cflds (defined in class C) do no occur in supertypes classes *)
Definition fresh_fields_from_supertypes C Cflds :=
  forall Did Dflds,
    subtyping P C (JFClass Did) ->
    C <> JFClass Did ->
    flds_overline P (JFClass Did) = Some Dflds ->
    Forall (fun fd => Flds.name_occ Dflds (name_of_fd fd) = 0) Cflds.

Definition method_in_subclass_consistent md md' :=
  match md, md' with
  | JFMDecl D mu mn vs excs _, JFMDecl D' mu' mn' vs' excs' _ =>
    D' = D /\ mu' = mu /\ mn' = mn /\ vs' = vs /\ excs' = excs 
  | JFMDecl0 D mn vs excs _, JFMDecl0 D' mn' vs' excs' _  => 
    D' = D /\ mn' = mn /\ vs' = vs /\ excs' = excs 
  | _, _ => False
  end.
          
Definition methods_in_subclass_exists_consistent Cn :=
  forall Dn m md,
    subtyping P (JFClass Cn) (JFClass Dn) ->
    methodLookup P Dn m = Some md ->
    exists md', methodLookup P Cn m = Some md' /\ method_in_subclass_consistent md md'.
                                                                      

(** Rule (CLASS) from Fig. 4 *)
Inductive JFclassTypes : Prop :=
| JFclassOK:
    forall C ex flds mthds,
      (* class C ext C ′ {F M} ∈ C *)
      cdecl = JFCDecl C ex flds mthds ->
      In cdecl P -> 
      (*  C <: D ⇒ ∀x ∈ F. x ̸∈ D *)
      fresh_fields_from_supertypes (JFClass C) flds ->
      (* Field names are unique (silent assumption) *)
      Flds.names_unique flds ->
      (*  C <: D ⇒ ∀m ∈ M. m ∈ D ⇒ pars(C, m) = pars(D, m) ∧
          retTypM(C, m) = retTypM(D, m) ∧ thrs(C, m) = thrs(D, m) *)
      methods_in_subclass_exists_consistent C ->
      (* ∀x ∈ F. φ D x ∈ C ⇒ D ∈ C*)
      (Forall (fun fd : JFFieldDeclaration => JFFieldClassInProg fd) flds) ->
      (* ∀m ∈ M. C ⊢ m : ok *)
      (Forall (fun md : JFMethodDeclaration => JFmethodTypes md) mthds) ->
      (*------------------------------------------*)
      JFclassTypes

| JFclassObjectOK:
    forall flds mthds,
      (* Object is OK *)
      cdecl = JFCDecl JFObjectName None flds mthds ->
      In cdecl P -> 
      (* Field names are unique *)
      Flds.names_unique flds ->
      (* ∀m ∈ M. C ⊢ m : ok *)
      (Forall (fun md : JFMethodDeclaration => JFmethodTypes md) mthds) ->
      (*------------------------------------------*)
      JFclassTypes.


Lemma method_in_subclass_consistent_LS : forall md md',
    method_in_subclass_consistent md md' -> isLS md <-> isLS md'.
Proof.
  destruct md, md'; sauto.
Qed.

Hint Resolve -> method_in_subclass_consistent_LS.
Hint Resolve <- method_in_subclass_consistent_LS.


Lemma method_in_subclass_consistent_isLSForId : forall Cn, 
    methods_in_subclass_exists_consistent Cn ->
    forall Dn m md,
      subtyping P (JFClass Cn) (JFClass Dn) ->
      methodLookup P Dn m = Some md ->
      isLSForId P Dn m <-> isLSForId P Cn m.
Proof.
  intros ? H * ? HD.
  edestruct H as (md1 & Hlp & Hcons); eauto 1.
  split.
  + inversion_clear 1.
    eqf.
    econstructor; subst; eauto.
  + inversion_clear 1.
    eqf.
    econstructor; subst; eauto.
Qed.




End TypingInClass.



(* nazwy automatyczne z wcześniejszych hintów *)
Hint Resolve method_in_subclass_consistent_LS_proj_l2r.
Hint Resolve method_in_subclass_consistent_LS_proj_r2l.
(* Hint Resolve -> method_in_subclass_consistent_LS.
   Hint Resolve <- method_in_subclass_consistent_LS.
 *)

Hint Resolve -> method_in_subclass_consistent_isLSForId.
Hint Resolve <- method_in_subclass_consistent_isLSForId.



(* TODO: jak to się ma do subtyping_well_founded ? *)
Inductive JFclassSubTypes : JFClassDeclaration -> Prop :=
| JFclassSubObjectOK:
    forall ex flds mthds,
    (*------------------------------------------*)
    JFclassSubTypes (JFCDecl JFObjectName ex flds mthds)
| JFclassSubOK:
    forall cdecl cname cex cflds cmthds ddecl dname dex dflds dmthds,
      (* C ∈ C *)
      In cdecl P ->
      (* ext(C) = D *)
      cdecl = JFCDecl cname cex cflds cmthds ->
      ddecl = JFCDecl dname dex dflds dmthds ->
      extends P cname dname ->
      JFclassSubTypes ddecl ->
      (* ⊢ D : subok *)
    (*------------------------------------------*)
    JFclassSubTypes cdecl.

(*
Definition JFclassTypesForCdecl (cdecl:JFClassDeclaration) :=
  match cdecl with
  | JFCDecl D ex flds mthds => JFclassTypes cdecl 
  end.
*)


(* TODO: Do tego chyba trzeba dopisać Well_formed_program  *)
Inductive JFprogTypes : Prop :=
| JFprogOK:
    (* ∀C ∈ C. ⊢ C : subok *)
    Forall (fun (cdecl:JFClassDeclaration) => JFclassSubTypes cdecl) P ->
    (* ∀C ∈ C. ⊢ C : ok *)
    Forall JFclassTypes P ->
    (*------------------------------------------*)
    JFprogTypes.

(*
Lemma xxx:
  forall Cn Dn m md md',
    JFclassTypes ->
    subtyping P (JFClass Cn) (JFClass Dn) ->
    methodLookup P Cn m = Some md ->
    methodLookup P Dn m = Some md' ->
    method_in_subclass_consistent md md'.
Proof.
  intros * JFCt Sub MthdCn MthdDn.
  admit.
Admitted.
*)

End TypingInProgram.
