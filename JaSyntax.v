Require Import Omega.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.

From Hammer Require Import Reconstr.


(** Syntactical category of reference annotations. It contains
    _rwr_, _rd_ and _atm_ annotations.

    Defined in Figure {fig:syntax} as the set \mmod. *)
Inductive JFAMod : Set :=
| JFrwr
| JFrd
| JFatm.

Definition JFAMod_dec : forall v v' : JFAMod, {v=v'}+{~v=v'}.
  destruct v;destruct v'; try (left;congruence); try (right;congruence).
Defined.
Hint Resolve JFAMod_dec : dec.


(** Partial order on annotations.

    Defined in Section {sec:syntax-semantics}. *)
Inductive leqAnn : JFAMod -> JFAMod -> Prop  :=
| refl:  forall mu, leqAnn mu mu
| rwrrd: leqAnn JFrwr JFrd
| rdatm: leqAnn JFrd JFatm
| rwratm: leqAnn JFrwr JFatm.

Hint Constructors leqAnn : myhints.

Lemma leqAnn_dec:
  forall mu mu',
    leqAnn mu mu' \/ ~leqAnn mu mu'.
Proof.
  destruct mu, mu';sauto.
Qed.

(** Upper bound for annotations.

    Defined in Section {sec:syntax-semantics}. *)
Definition supAnn (mu1 mu2:JFAMod) : JFAMod :=
  match mu1 with
  | JFrwr => mu2
  | JFrd => match mu2 with
            | JFrwr => JFrd
            | JFrd => JFrd
            | JFatm => JFatm
            end
  | JFatm => JFatm
  end.

(** Lower bound for annotations.

    Defined in Section {sec:syntax-semantics}. *)
Definition infAnn (mu1 mu2:JFAMod) : JFAMod :=
  match mu1 with
  | JFrwr => JFrwr
  | JFrd => match mu2 with
            | JFrwr => JFrwr
            | JFrd => JFrd
            | JFatm => JFrd
            end
  | JFatm => mu2
  end.


Lemma rwr_bottom:
  forall mu, leqAnn JFrwr mu.
Proof.
  destruct mu; auto with myhints.
Qed.

Lemma rwr_eq:
  forall mu, leqAnn mu JFrwr -> mu = JFrwr.
Proof.
  intros.
  destruct mu; auto; inversion H.
Qed.


Lemma atm_top:
  forall mu, leqAnn mu JFatm.
Proof.
  intros.
  destruct mu; auto with myhints.
Qed.


Lemma atm_eq:
  forall mu, leqAnn JFatm mu -> mu = JFatm.
Proof.
  intros.
  destruct mu; auto; inversion H.
Qed.


Lemma leqAnn_trans:
  forall (mu1 mu2 mu3:JFAMod),
    leqAnn mu1 mu2 -> leqAnn mu2 mu3 -> leqAnn mu1 mu3.
Proof.
  scrush.
Qed.

Lemma infAnn_leq_l:
  forall mu1 mu2 mu3,
    infAnn mu1 mu2 = mu3 ->
    leqAnn mu3 mu1.
Proof.
  scrush.
Qed.

Lemma infAnn_leq_r:
  forall mu1 mu2 mu3,
    infAnn mu1 mu2 = mu3 ->
    leqAnn mu3 mu2.
Proof.
  scrush.
Qed.

Lemma infAnn_inf:
  forall mu1 mu2 mu,
      leqAnn mu mu1 ->
      leqAnn mu mu2 ->
      leqAnn mu (infAnn mu1 mu2).
Proof.
  scrush.
Qed.

Hint Resolve atm_top rwr_bottom leqAnn_trans infAnn_leq_l infAnn_leq_r infAnn_inf: myhints.

(**
   Effective version of the partial order on annotations that
   returns booleans instead predicting the property.
*)
Fixpoint leqAnn_bool (mu1 mu2:JFAMod) : bool  :=
  match mu1 with
    | JFrwr => true
    | JFrd => match mu2 with
                | JFrwr => false
                | _ => true
              end
    | JFatm => match mu2 with
                 | JFatm => true
                 | _ => false
               end
  end.

(**
   The reverse of the effective version of the partial order on
   annotations. It returns booleans instead predicting the property.
*)
Definition geqAnn_bool mu1 mu2 := leqAnn_bool mu2 mu1.


(** Alias name for class names. We represet them as
    Coq strings. *)
Definition JFClassName := string.

Hint Resolve string_dec : dec.

(** Decidable equality on [JFClassName]. *)
Definition JFClassName_dec : forall v v' : JFClassName, {v=v'}+{~v=v'}.
  exact string_dec.
Defined.
Hint Resolve JFClassName_dec : dec.

Lemma jfclassname_commutative:
  forall cn dn,
    (if JFClassName_dec cn dn then true else false) =
    if JFClassName_dec dn cn then true else false.
Proof.
  scrush.
Qed.

(** Syntactical category of class identifiers. The
  identifier JFBotClass does not occur in the source
  code.

  Defined in Figure {fig:syntax} as the set \Cname. *)
Inductive JFCId : Set :=
| JFClass (cn:JFClassName)
| JFBotClass.

(** Decidable equality on [JFCId]. *)
Definition JFCId_dec : forall v v' : JFCId, {v=v'}+{~v=v'}.
  decide equality.
  auto with dec.
Defined.
Hint Resolve JFCId_dec : dec.

(** The class name of the _Object_ class.

    Defined in Figure {fig:auxiliary-notation} in
    the second row as \objecttype. *)
Definition JFObjectName := "Object"%string.

(** The class name of the _NullPointerException_ class.

    Defined in Figure {fig:auxiliary-notation} in
    the second row as \npetype. *)
Definition JFNPEName := "NullPointerException"%string.

(** The class identifier of _Object_. *)
Definition JFObject := JFClass (JFObjectName).

(** The class identifier of _NullPointerException_. *)
Definition JFNPE := JFClass (JFNPEName).

(** Syntactical category of method identifiers.

  Defined in Figure {fig:syntax} as the set _m_. *)
Definition JFMId := string.

(** Decidable equality on [JFMId]. *)
Definition JFMId_dec : forall v v' : JFMId, {v=v'}+{~v=v'}.
  exact string_dec.
Defined.
Hint Resolve JFMId_dec : dec.

(** Syntactical category of variable identifiers.

  Defined in Figure {fig:syntax} as the set _x_. *)
Definition JFXId := string.

(** Decidable equality on [JFCId]. *)
Definition JFXId_dec : forall v v' : JFXId, {v=v'}+{~v=v'}.
  exact string_dec.
Defined.
Hint Resolve JFXId_dec : dec.

(** Semantical category of locations. It is defined in the
    syntax part since the small step reduction of Jafun
    semantics uses locations in expressions being reduced.
    Locations are either the _null_ location or an address.

    Defined in Section {sec:syntax-semantics} as the set \Loc. *)  
Inductive Loc : Set :=
| null
| JFLoc (n:nat).

Hint Resolve Nat.eq_dec : dec.

(** Decidable equality on locations [Loc]. *)
Definition Loc_dec : forall l l' : Loc, {l=l'}+{~l=l'}.
  decide equality.
  auto with dec.
Defined.
Hint Resolve Loc_dec : dec.



(** Syntactic reference: variable or _this_. *)
Inductive JFRef :=
| JFVar (x:JFXId)
| JFThis.

(** Decidable equality on references [JFRef]. *)
Definition JFRef_dec : forall v v' : JFRef, {v=v'}+{~v=v'}.
  decide equality.
  auto with dec.
Defined.
Hint Resolve JFRef_dec : dec.

(** Values: locations or syntactic references *)
Inductive JFVal :=
| JFVLoc (l:Loc)
| JFSyn (x:JFRef).

(* now substitutions substitute locations for syntactic references *)

(** "Syntactic" _null_ is directly represented by the "semantic" one. *)
Notation JFnull := (JFVLoc null).


(** Decidable equality on primitive values [JFVal]. *)
Definition JFVal_dec : forall v v' : JFVal, {v=v'}+{~v=v'}.
  decide equality; auto with dec.
Defined.
Hint Resolve JFVal_dec : dec.

(** Check if the value is a location. *)
Definition isLoc (v:JFVal) := 
match v with
| JFnull => True
| JFVLoc (JFLoc _) => True
| JFSyn _ => False
end.

(** Check if the value is _null_. *)
Definition isNonNullLoc (v:JFVal) := 
match v with
| JFnull => False
| JFVLoc (JFLoc _) => True
| JFSyn _ => False
end.


(**
   The representation of subexpression in which an object refers to
   its field. This is a type of subexpressions that helps to define
   the main syntactic category.
 *)
Definition JFFieldref :Set :=  (JFVal * JFXId)%type.

(** The representation of Jafun expressions.

    Defined in Figure {fig:syntax} as the syntactic
    category _E_. *)
Inductive JFExpr : Set :=
| JFNew (mu:JFAMod) (cn:JFClassName) (vs : list JFVal)
| JFLet (cn:JFClassName) (x:JFXId) (E1:JFExpr) (E2:JFExpr)
| JFIf (v1 v2:JFVal) (E1:JFExpr) (E2:JFExpr)
| JFInvoke (v:JFVal) (m:JFMId) (vs:list JFVal)
| JFAssign (vx:JFFieldref) (v:JFVal)
| JFVal1 (v:JFVal)
| JFVal2 (vx:JFFieldref)
| JFThrow (v:JFVal)
| JFTry (E1:JFExpr) (mu:JFAMod) (cn:JFClassName) (x:JFXId) (E2:JFExpr).

(* make an alpha equivalent of [x.E] not using [vv]; TODO: maybe this should return a pair *)
Parameter alphaExpr : forall (x:JFXId) (vv:list JFXId) (E:JFExpr), JFExpr.
Parameter alphaVal : forall (x:JFXId) (vv:list JFXId) (E:JFVal), JFVal.

(** Substitute the value [l] for [v] in [x] (i.e. _"x{l/v}"_). *)
Definition substVal (v : JFRef) (l:Loc) (x : JFVal) :=
  match x with
  | JFVLoc _ => x
  | JFSyn y => if JFRef_dec v y then JFVLoc l else x
  end.



(** Substitute the location [l] for the occurrences of the reference [v]
    in the expression [E] (i.e. _"E{l/v}"_). 
 *)
Fixpoint substExpr (v:JFRef) (l:Loc) (E:JFExpr) {struct E} : JFExpr :=
  match E with
  | JFNew mu C vs => JFNew mu C (List.map (substVal v l) vs)
  | JFLet C x E1 E2 =>
    if JFRef_dec (JFVar x) v then
      JFLet C x (substExpr v l E1) E2
    else
      JFLet C x (substExpr v l E1) (substExpr v l E2)
  | JFIf v1 v2 E1 E2 =>
    JFIf (substVal v l v1) (substVal v l v2)
         (substExpr v l E1) (substExpr v l E2)
  | JFInvoke v1 m vs =>
    JFInvoke (substVal v l v1) m (List.map (substVal v l) vs)
  | JFAssign (v1,fld) v2 =>
    JFAssign (substVal v l v1, fld) (substVal v l v2)
  | JFVal1 v1 =>
    JFVal1 (substVal v l v1)
  | JFVal2 (v1, fld) =>
    JFVal2 (substVal v l v1, fld)
  | JFThrow v1 =>
    JFThrow  (substVal v l v1)
  | JFTry E1 mu C x E2 =>
    if JFRef_dec (JFVar x) v then
      JFTry (substExpr v l E1) mu C x E2
    else
      JFTry (substExpr v l E1) mu C x (substExpr v l E2)
  end.

(** Substitute the variables from the list [vs] by respective values
    in the list [fs] in [E] (i.e. _"E{fs/vs}"_). 
 *)
(* Fixpoint substList fs vs E {struct fs} :=
  match fs with
    | [] => Some E
    | v1 :: tl =>
      match vs with
        | [] => None
        | v2 :: tl' =>
          match v2 with
            | JFVLoc l => substList tl tl' (substExpr v1 l E)
            | _ => None
          end
      end            
  end.
 *)
Fixpoint substList fs vs E {struct fs} :=
  match (fs, vs) with
    | ([], []) => Some E
    | (v1 :: tl, v2::tl') =>
        match v2 with
          | JFVLoc l => substList tl tl' (substExpr v1 l E)
          | _ => None
        end
    | _ => None
  end.

(** A class type combinded with an annotation.
    
    The type system uses the pairs in the   
    sequence: class first, annotation second. *)
Definition JFACId : Set := (JFCId * JFAMod)%type.

Definition JFACId_dec : forall v v' : JFACId, {v=v'}+{~v=v'}.
  decide equality; auto with dec.
Defined.
Hint Resolve JFACId_dec : dec.

(** The representation of method declarations. There are two kinds 
    of declarations: with access mode annotations (local state ones) 
    [JFMDecl] and without [JFMDecl0].
    
    Defined in Figure {fig:syntax} as the syntactic
    category \mathbf{M}.
 *)
Inductive JFMethodDeclaration : Set :=
| JFMDecl (C:JFACId) (mu:JFAMod) (m:JFMId) (vs:list (JFXId * JFACId)) (thrws:list JFACId) (E:JFExpr)
| JFMDecl0 (C:JFCId) (m:JFMId) (vs:list (JFXId * JFCId)) (thrws:list JFCId) (E:JFExpr).

(** Decidable equality on method declarations [JFMethodDeclaration]. *)
Definition JFMethodDeclaration_dec : forall v v' : JFMethodDeclaration, {v=v'}+{~v=v'}.
  repeat (decide equality; auto with dec).
Defined.
Hint Resolve JFMethodDeclaration_dec : dec.

Section methodProjections.

(** Retrives the type of the value returned from the given
    method declared as [md]. *)
Definition rettyp_of_md (md: JFMethodDeclaration) : JFACId :=
  match md with
  | JFMDecl cn mu mn vs excs E => cn
  | JFMDecl0 cn mn vs excs E => (cn, JFrwr)
  end.

(** Retrives the annotation of _this_ for the given
    method declared as [md]. It returns [Some] value in case
    the method is local-sensitive and [None] otherwise. *)
Definition mode_of_md (md: JFMethodDeclaration) : option JFAMod :=
  match md with
  | JFMDecl cn mu mn vs excs E => Some mu
  | JFMDecl0 cn mn vs excs E => None
  end.
  
(** Retrives the name of the method from the given
    method declaration [md]. *)
Definition name_of_md (md: JFMethodDeclaration) : JFMId :=
  match md with
  | JFMDecl _ _ mn _ _ _ => mn
  | JFMDecl0 _ mn _ _ _ => mn
  end.

(** Retrives the formal parameters of the method from the given
    method declaration [md]. *)
Definition params_of_md md :=
  match md with
    | JFMDecl _ _ _ vs _ _ => map fst vs
    | JFMDecl0 _ _ vs _ _ => map fst vs
  end.
  
(** Retrives the list of types of exceptions being thrown by 
    the method [md]. The function returns an annotated type, i.e.
    [JFACid]. In case of non-local sensitive methods it returns
    _rwr_ annotations. *)
Definition thrs_of_md (md: JFMethodDeclaration) : list JFACId :=
  match md with
  | JFMDecl cn mu mn vs excs E => excs
  | JFMDecl0 cn mn vs excs E => map (fun dn => (dn, JFrwr)) excs
  end.

(** Retrives the expression which is the body of the given
    method declaration [md]. *)
Definition body_of_md (md:JFMethodDeclaration) : JFExpr :=
  match md with
    | JFMDecl _ _ _ _ _ E => E
    | JFMDecl0 _ _ _ _ E => E
  end.

(** Checks if the given method [md] is a declaration of a local-sensitive
    method. The method checks the way the declaration [md] is constructed. *)
Definition isLS (md:JFMethodDeclaration) : Prop :=
  match md with
  | JFMDecl _ _ _ _ _ _ => True
  | JFMDecl0 _ _ _ _ _ => False
  end.

Lemma isLS_dec : forall md, {isLS md} + {~isLS md}.
Proof.
  destruct md; simpl; auto.
Qed.
End methodProjections.

(** Finds a declaration of a method with the given name [m] in
    the list of method declarations [mthds]. It returns [None] in
    case there is no method declaration of the given name and
    [Some] value in case the method declaration is found. *)
Fixpoint find_method mthds m {struct mthds} :=
  match mthds with
    | [] => None
    | (JFMDecl cn mu mn vs excs E) :: tl =>
      if JFMId_dec m mn
      then Some (JFMDecl cn mu mn vs excs E)
      else find_method tl m
    | (JFMDecl0 cn mn vs excs E) :: tl =>
      if JFMId_dec m mn
      then Some (JFMDecl0 cn mn vs excs E)
      else find_method tl m
  end.

(** Syntactical category of field declarations.
    The _phi_ argument is [true] when there is a _rep_
    modifier attached to the field. It is [false] otherwise.

  Defined in Figure {fig:syntax} as the set \mathbf{F}.
 *)
Inductive JFFieldDeclaration : Set :=
| JFFDecl (phi:bool) (C:JFCId) (x:JFXId).

(** Decidable equality on field declarations [JFFieldDeclaration]. *)
Definition JFFieldDeclaration_dec : forall v v' : JFFieldDeclaration, {v=v'}+{~v=v'}.
  repeat decide equality.
Defined.

Section fieldProjections.

(** Retrives the name of the given field [fd]. *)
Definition name_of_fd fd :=
  match fd with
    | JFFDecl _ _ x => x
  end.

(** Retrives the class of the given field [fd]. *)
Definition class_of_fd fd :=
  match fd with
    | JFFDecl _ Cid _ => Cid
  end.

(** Retrives the annotation of the given field [fd]. *)
Definition ann_of_fd fd :=
  match fd with
    | JFFDecl phi _ _ => phi
  end.

End fieldProjections.


(** Syntactical category of class declarations.

    Defined in Figure {fig:syntax} as the set \mathbf{C}.

    As written in Java Language Specification Section 8.1.4,
    the extends clause is optional. This is modelled by the
    *option* type in the argument [ex].
 *)
Inductive JFClassDeclaration : Set :=
| JFCDecl (cn:JFClassName) (ex:option JFClassName)
          (fields:list JFFieldDeclaration) (methods:list JFMethodDeclaration).

(** Decidable equality on class declarations [JFClassDeclaration]. *)
Definition JFClassDeclaration_dec : forall v v' : JFClassDeclaration, {v=v'}+{~v=v'}.
  repeat decide equality.
Defined.


Section classProjections.

(** Retrives the name of the given class [cd]. *)
Definition name_of_cd (cd: JFClassDeclaration) :=
  match cd with
  | JFCDecl cn _ _ _ => cn
  end.

(** Retrives the field declarations in the given class [cd]. 
    This method does not traverse the inheritance hierarchy. *)
Definition flds_of_cd (cd: JFClassDeclaration) :=
  match cd with
  | JFCDecl _ _ fields _ => fields
  end.

(** Retrives the method declarations in the given class [cd]. 
    This method does not traverse the inheritance hierarchy. *)
Definition mthds_of_cd (cd: JFClassDeclaration) :=
  match cd with
  | JFCDecl _ _ _ mthds => mthds
  end.

(** Retrives the extends clause in the given class [cd]. 
    It returns [None] in case the current class is not extended.
    This should happen only in the case of the [Object] class. *)
Definition extds_of_cd (cd:JFClassDeclaration) :=
  match cd with
  | JFCDecl _ extds _ _ => extds
  end.


End classProjections.

(** The general structure of Jafun programs. It is a list of classes. 
    We assume the preloading view, where programs come as a list. *)
Definition JFProgram : Set := list JFClassDeclaration.

(** Finds a declaration of a class with the given name [cn] in
    the program [CC]. It returns [None] in case there is no class
    declaration of the given name and [Some] value in case the class
    declaration is found. *)
Fixpoint find_class (CC:JFProgram) (cn:JFClassName) :=
  match CC with
  | [] => None
  | (JFCDecl dn ex fields methods) :: CC' => 
    if (JFClassName_dec dn cn)
    then Some (JFCDecl dn ex fields methods)
    else find_class CC' cn
  end.

Lemma find_class_eq:
  forall CC cn ex fields methods,
    find_class (JFCDecl cn ex fields methods :: CC) cn =
    Some (JFCDecl cn ex fields methods).
Proof.
  sauto.
Qed.

Lemma find_class_further_neq:
  forall CC cn dn  ex fields methods cd,
  cn<>dn ->
  find_class (JFCDecl cn ex fields methods :: CC) dn = Some cd ->
  find_class CC dn = Some cd.
Proof.
  sauto.
Qed.


Lemma find_class_in:
  forall CC cn dn ex fields methods,
    find_class CC cn = Some (JFCDecl dn ex fields methods) ->
    In (JFCDecl cn ex fields methods) CC.
Proof.
  induction CC; sauto.
Qed.


Lemma find_class_same:
  forall CC cn dn ex fields methods cd,
  cn <> dn ->
  find_class CC dn = Some cd ->
  find_class (JFCDecl cn ex fields methods :: CC) dn = Some cd.
Proof.
  sauto.
Qed.

Lemma find_class_eq_name:
  forall CC cn dn ex fields methods,
  find_class CC cn = Some (JFCDecl dn ex fields methods) ->
  cn = dn.
Proof.
  induction CC; sauto.
Qed.
Check find_class.
Lemma find_class_decompose_program:
  forall CC cn cd,
    find_class CC cn = Some cd ->
    exists CC0 CC1,
      CC = CC0 ++ (cd :: CC1).
Proof.
  induction CC; sauto.
  +  exists [], CC; auto.
  +  assert (exists CC0 CC1 : list JFClassDeclaration,
                CC = CC0 ++ cd :: CC1) by eauto.
     destruct H0 as [CC0 [CC1 HH]].
     exists (JFCDecl cn0 ex fields methods :: CC0), CC1.
     sauto.
Qed.

Lemma find_class_lift_cons:
  forall CC cn cd dd,
    find_class CC cn = Some cd ->
    exists cd',
      find_class (dd :: CC) cn = Some cd'.
Proof.
  sauto.
Qed.

Lemma find_class_lift:
  forall CC1 CC2 cn cd,
    find_class CC2 cn = Some cd ->
    exists cd',
      find_class (CC1 ++ CC2) cn = Some cd'.
Proof.
  induction CC1; sauto.
Qed.

Lemma find_class_lift_cons_inside:
  forall CC1 CC2 cn cd dd,
    find_class (CC1 ++ CC2) cn = Some cd ->
    exists cd',
      find_class (CC1 ++ dd::CC2) cn = Some cd'.
Proof.
  induction CC1; sauto.
Qed.

  
(** Checks if the given program [P] contains a class declaration of the
    given name [cname].
*)
Fixpoint program_contains (CC:JFProgram) (cn:JFClassName) : bool :=
  match CC with
    | [] => false
    | JFCDecl dn _ _ _ :: CC' => if JFClassName_dec cn dn then true else program_contains CC' cn
  end.

Lemma program_contains_further_neq:
  forall CC cn dn ex fields methods, 
    cn <> dn ->
    program_contains (JFCDecl cn ex fields methods :: CC) dn = true ->
    program_contains CC dn = true.
Proof.
  sauto.
Qed.

Lemma program_contains_further:
  forall CC cn dn ex fields methods, 
    program_contains CC dn = true ->
    program_contains (JFCDecl cn ex fields methods :: CC) dn = true.
Proof.
  sauto.
Qed.

Lemma program_contains_find_class:
  forall CC cn, 
    program_contains CC cn = true ->
    exists cd, find_class CC cn = Some cd.
Proof.
  induction CC; sauto.
Qed.

Lemma find_class_program_contains:
  forall CC cn cd,
    find_class CC cn = Some cd ->
    program_contains CC cn = true.
Proof.
  induction CC; sauto.
Qed.

(** Finds the method [m] in the class of the name [cn] in the program [CC],
    traversing the inheritance hierarchy of [cn] in the program [CC].
    In case the program [CC] does not contain a class with name [cn]
    the function returns [None]. In case the class does not contain
    the method [m], it returns [None] too. Otherwise, [Some] method
    declaration is returned.
*)
Fixpoint methodLookup (CC:JFProgram) (cn:JFClassName)
           (m:JFMId)  : option JFMethodDeclaration :=
  match CC with
  | [] => None
  | (JFCDecl dn ex _ mthds) :: CC1 =>
    if JFClassName_dec cn dn
    then match find_method mthds m with
         | None => match ex with
                   | None => None
                   | Some en => methodLookup CC1 en m
                   (* Correction: semantically CC in place of CC1
                      changes the meaning in case cn=dn=en and there
                              is no m in mthds, which occurs only in
                              non-wellformeed programs. So we can
                              redefine it. *)
                   end
         | Some md => Some md
         end
    else
      methodLookup CC1 cn m
  end.

Lemma methodLookup_raw_empty:
  forall cn m,
    methodLookup [] cn m = None.
Proof.
  intros. simpl; auto.
Qed.

Lemma methodLookup_prog_monotone_eq:
  forall CC dd cn dn m md,
    cn = (name_of_cd dd) ->
    find_method (mthds_of_cd dd) m = None ->
    extds_of_cd dd = Some dn ->
    methodLookup CC dn m = Some md ->
    methodLookup (dd :: CC) cn m = Some md.
Proof.
  sauto.
Qed.

Lemma methodLookup_raw_neq:
  forall cn dn CC m md fields methods,
    cn <> dn ->
    methodLookup CC dn m = Some md ->
    methodLookup (JFCDecl cn (Some dn) fields methods :: CC) dn m = Some md.
Proof.
  sauto.
Qed.


Lemma methodLookup_find_class:
  forall CC cn m mdcl,
    methodLookup CC cn m = Some mdcl ->
    exists cdcl, find_class CC cn = Some cdcl.
Proof.
  induction CC; sauto.
Qed.

(** Predicate that checks if the given method in the class declaration
    is local sensitive. *)
Inductive isLSForId : JFProgram -> JFClassName -> JFMId -> Prop  :=
| isLStrue : forall CC cn m md,
    methodLookup CC cn m = Some md  ->
    isLS md ->
    isLSForId CC cn m.

Lemma isLSForId_dec:
  forall CC cn m, isLSForId CC cn m \/ ~ isLSForId CC cn m.
Proof.
  intros.
  destruct (methodLookup CC cn m) eqn:?.
  + destruct j.
    ++ pose isLStrue; scrush.
    ++ right; intro H; inversion H; scrush.
  + scrush.
Qed.

Lemma isLSForId_neg:
  forall CC cn m md,
    ~ isLSForId CC cn m ->
    ~ (methodLookup CC cn m = Some md  /\ isLS md).
Proof.
  intros.
  intro.
  apply H.
  destruct H0.
  eapply isLStrue;eauto.
Qed.

Hint Resolve find_class_eq find_class_in isLSForId_dec find_class_lift_cons find_class_lift isLSForId_neg: myhints.
