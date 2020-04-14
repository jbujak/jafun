Require Import String.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.
Require Import JaSyntax.
Require Import JaProgram.
Require Import JaTactics.
Open Scope list_scope.
Require Import NPeano.
Require Import PeanoNat.
Open Scope nat_scope.
Require Import Coq.Program.Equality.

From Hammer Require Import Reconstr.


(**
  By [extends CC cn dn] we mean that in the program [CC] the class of name [cn] is declared
  as a direct subclass of [dn]. This is the formalisation of the *direct subtype relation, <_1* 
  as defined in Section 4.10 of Java Language Specification.
*)
Inductive extends : JFProgram -> JFClassName -> JFClassName -> Prop  :=
| base : forall cn dn fields methods CC ex fields' methods',
           In (JFCDecl dn ex fields' methods') CC ->
           extends ((JFCDecl cn (Some dn) fields methods) :: CC)%list cn dn
(** As written in Section 8.1.4 of Java Language Specification,
    "The optional extends clause in a normal class declaration specifies the direct 
    superclass of the current class."
    We add here the check of the accessibility of the superclass as further it
    is written that
    "The ClassType must name an accessible class type (§6.6), or a compile-time 
    error occurs." *)
| ind  : forall cn1 cn2 dn1 dn2 fields methods CC, 
           extends CC cn2 dn2 ->
           extends ((JFCDecl cn1 dn1 fields methods) :: CC)%list cn2 dn2.
(** The extension of the direct subtype relation to the whole program. *)


Hint Constructors extends : myhints.

Lemma extends_in_first:
  forall CC cn dn,
    extends CC cn dn ->
    (exists flds mthds,  In (JFCDecl cn (Some dn) flds mthds) CC).
Proof.
  induction CC; scrush.
Qed.

Lemma extends_in_second:
  forall CC cn dn,
    extends CC cn dn ->
    (exists ex flds mthds,  In (JFCDecl dn ex flds mthds) CC).
Proof.
  induction CC; scrush.
Qed.

Lemma extends_in_second_second:
  forall CC cn dn,
    extends CC cn dn ->
    forall CC' cd,
      CC = cd :: CC' ->
      (exists ex fields' methods',  In (JFCDecl dn ex fields' methods') CC').
Proof.
  induction 1.
  + sauto.
  + destruct CC; scrush.
Qed.

Lemma base_deep:
  forall CC DD cn dn dd fields methods,
    find_class DD dn = Some dd ->
    extends (CC ++ JFCDecl cn (Some dn) fields methods :: DD) cn dn.
Proof.
  induction CC.
  + intros.
    simpl.
    destruct dd.
    generalize H;intros;eapply find_class_eq_name in H0;subst.
    eapply find_class_in in H.
    eapply base; eauto.
  + intros.
    simpl.
    destruct a.
    eapply ind.
    eauto.
Qed.
    

Lemma in_exists_decl_dec:
  forall CC cn,  
    (exists ex flds mthds, In (JFCDecl cn ex flds mthds) CC) \/
    ~ (exists ex flds mthds, In (JFCDecl cn ex flds mthds) CC).
Proof.    
  induction CC.
  + intros.
    right.
    sauto.
  + intros.
    destruct a.
    destruct (JFClassName_dec cn0 cn).
    ++ subst.
       left.
       sauto.
    ++ destruct (IHCC cn).
       +++ left.
           sauto.
       +++ right.
           intro.
           apply H.
           decompose_ex H0.
           inversion H0;sauto.
Qed.
    

Lemma extends_dec:
  forall CC cn dn,
    extends CC cn dn \/ ~extends CC cn dn.
Proof.
  induction CC.
  + sauto.
  + destruct a.
    intros.
    destruct (JFClassName_dec cn0 cn).
    ++ subst.
       destruct (IHCC cn dn).
       +++ left.
           eauto using ind.
       +++ destruct ex.
           ++++ pose (in_exists_decl_dec CC dn).
                destruct o.
                * decompose_ex H0.
                  destruct (JFClassName_dec dn j).
                  ** left.
                     rewrite e.
                     eapply base.
                     sauto.
                  ** right.
                     intro.
                     inversion H1.
                     *** congruence.
                     *** contradiction.
                * right.
                  intro.
                  inversion H1.
                  ** subst.
                     eapply H0.
                     sauto.
                  ** contradiction.
           ++++ right.
                intro.
                inversion H0.
                contradiction.
    ++ destruct (IHCC cn0 dn).
       +++ left.
           constructor 2.
           assumption.
       +++ right.
           intro.
           inversion H0;sauto.
Qed.

Lemma extends_narrower:
  forall (CC : list JFClassDeclaration) (cn dn en : JFClassName)
    (ex : option JFClassName) (fields : list JFFieldDeclaration)
    (methods : list JFMethodDeclaration),
    extends (JFCDecl cn ex fields methods :: CC) dn en ->
    dn<>cn ->
    extends CC dn en.
Proof.
  scrush.
Qed.

Lemma extends_neq:
  forall CC D1 C D0 ex fields methods,
  names_unique (JFCDecl D1 ex fields methods :: CC) ->
  (exists cname dname : JFClassName,
         C = JFClass cname /\
         D0 = JFClass dname /\
         extends (JFCDecl D1 ex fields methods :: CC) cname dname) ->
  D0 <> JFClass D1.
Proof.
  intros.
  destruct H0, H0.
  decompose [and] H0; clear H0.
  eapply extends_in_second_second  in H4; [idtac | reflexivity].
  pose names_unique_zero; pose count_occ_not_In; scrush.
Qed.

Lemma extends_neq_none:
  forall CC D1 cname dname fields methods,
    names_unique (JFCDecl D1 None fields methods :: CC) ->
    extends (JFCDecl D1 None fields methods :: CC) cname dname ->
    D1 <> cname.
Proof.
  assert (forall L cname dname,
             names_unique L ->
             extends L cname dname ->
             forall CC D1 fields methods, L = JFCDecl D1 None fields methods :: CC ->
             D1 <> cname); [idtac | scrush].
  induction 2.
  + sauto.
  + intros ? ? ? ? H2.
    injection H2.
    pose extends_in_first; pose count_occ_zero_is_class_name_false; scrush.
Qed.

Lemma extends_equals_first:
  forall C D E fields methods CC, 
    names_unique (JFCDecl C (Some D) fields methods :: CC) ->
      extends (JFCDecl C (Some D) fields methods :: CC) C E ->
      E = D.
Proof.
  intros C D E fields methods CC Nuq Ext.
  inversion Ext.
  * auto.
  * subst.
    assert (forall x, In x CC -> decl_once CC x).
    assert (names_unique CC) by scrush.
    apply Forall_forall; auto.
    pose extends_in_first; scrush.
Qed.


Lemma names_unique_extends_non_refl:
  forall CC C D,
    names_unique CC -> extends CC C D -> C <> D.
Proof.
  intros CC C D Nuq H.
  induction H.
  pose count_occ_In; scrush.
  eauto.
Qed.

Lemma extends_not_extends:
  forall CC cn dn,
    extends CC cn dn ->
    forall hd DD,
      CC = (hd :: DD) ->
      ~ extends DD cn dn ->
      exists fields methods,
        hd = JFCDecl cn (Some dn)  fields methods.
Proof.
  induction 1.
  + intros.
    injection H0;intros.
    subst.
    do 2 eexists.
    eauto.
  + intros.
    injection H0;intros;subst.
    contradiction.
Qed.

Lemma extends_monotone:
  forall CC cname dname,
    extends CC cname dname ->
    forall CC' DD  E,
    CC = (CC' ++ DD) ->
    extends (CC' ++ E :: DD) cname dname.
Proof.
  induction 1.
  + intros.
    destruct CC'.
    ++ simpl in *.
       rewrite <- H0.
       destruct E.
       eapply ind.
       eapply base;eauto.
    ++ simpl in H0.
       injection H0;intros.
       subst.
       simpl.
       eapply base.
       eapply in_or_app.
       eapply in_app_or in H.
       sauto.
  + inversion H.
    ++ subst.
       intros.
       induction CC'.
       +++ simpl in *.
           subst.
           destruct E.
           apply ind.
           apply ind.
           eauto.
       +++ simpl in *.
           injection H1;intros.
           subst.
           apply ind.
           eauto.
    ++ intros.
       subst.
       destruct CC'.
       +++ simpl in *.
           subst.
           destruct E.
           apply ind.
           apply ind.
           auto.
       +++ simpl in *.
           injection H4;intros.
           subst.
           apply ind.
           eauto.
Qed.

Lemma names_unique_extends_eq:
  forall CC D1 j fields methods dname,
    names_unique (JFCDecl D1 (Some j) fields methods :: CC) ->
    extends (JFCDecl D1 (Some j) fields methods :: CC) D1 dname ->
    j = dname.
Proof.
  intros.
  inversion H0.
  - auto.
  - assert  (exists
                (ex0 : JFClassName) (fields' : list JFFieldDeclaration) 
                (methods' : list JFMethodDeclaration),
                In (JFCDecl D1 (Some ex0) fields' methods') CC)
      by eauto using extends_in_first.
    destruct H9. destruct H9. destruct H9.
    assert (count_occ Bool.bool_dec (map (is_class_name D1) CC) true = 0)
      by eauto using names_unique_count_zero.
    apply <- count_occ_not_In in H10.
    assert False.
    replace true with (is_class_name D1 (JFCDecl D1 (Some x) x0 x1)) in H10.
    apply H10.
    apply in_map.
    auto.
    apply is_class_name_name.
    tauto.
Qed.

Lemma extends_unique_dir:
  forall CC cn dn en,
    names_unique CC ->
    extends CC cn dn ->
    extends CC cn en -> dn = en.
Proof.
  induction CC.
  + intros.
    inversion H0.
  + intros.
    inversion H0;subst.
    ++ inversion H1;subst.
       +++ auto.
       +++ eapply extends_equals_first in H1;eauto.
    ++ inversion H1;subst.
       +++ eapply extends_equals_first in H0;eauto.
       +++ eauto.
Qed.

Lemma double_extends:
  forall CC cname dname,
    names_unique CC ->
    extends CC cname dname ->
    extends CC dname cname -> cname = dname.
Proof.
  induction 2.
  + intros.
    destruct (JFClassName_dec cn dn);auto.
    eapply extends_narrower in H1;try congruence.
    eapply extends_in_second in H1.
    decompose_ex H1.
    eapply names_unique_in_neq in H;eauto.
    contradiction.
  + intros.
    destruct (JFClassName_dec cn1 dn2).
    ++ subst.
       eapply extends_in_second in H0.
       decompose_ex H0.
       eapply names_unique_in_neq in H;eauto.
       contradiction.
    ++ eapply extends_narrower in H1;try congruence.
       eauto.
Qed.


Hint Resolve extends_equals_first extends_narrower names_unique_extends_non_refl base_deep extends_monotone extends_unique_dir : myhints.
Hint Resolve extends_equals_first extends_narrower names_unique_extends_non_refl base_deep extends_monotone extends_unique_dir.

Lemma extends_narrower_deep_eqfirst:
  forall CC cn en,
    extends CC cn en ->
    forall CC' CC'' dn flds mthds,
           CC = (CC' ++ JFCDecl cn (Some dn) flds mthds :: CC'') ->
           dn <> en ->
           cn <> en ->
           extends (CC' ++ CC'') cn en.
Proof.
  induction 1.
  + intros.
    destruct CC'.
    ++ simpl in *.
       injection H0;intros.
       subst;contradiction.
    ++ simpl in H0; injection H0;intros.
       subst j.
       simpl.
       eapply base.
       rewrite H3 in H.
       eapply in_app_or in H.
       destruct H.
       eapply in_or_app.
       left; eauto.
       eapply in_or_app.
       right.
       simpl in H.
       destruct H.
       injection H;intros;congruence.
       eauto.
  + intros.
    destruct CC'.
    ++ simpl in H0.
       injection H0;intros;subst.
       simpl.
       auto.
    ++ simpl in *.
       injection H0;intros;subst j.
       eapply IHextends in H3;eauto.
       replace (JFCDecl cn1 dn1 fields methods :: CC' ++ CC'') with ([] ++ (JFCDecl cn1 dn1 fields methods :: CC' ++ CC''))
         by eauto using app_nil_l.
       eauto.
Qed.

Lemma extends_narrower_deep_neqfirst:
  forall CC cn en,
    extends CC cn en ->
    forall CC' CC'' dn ex flds mthds,
           CC = (CC' ++ JFCDecl dn ex flds mthds :: CC'') ->
           cn <> dn ->
           dn <> en ->
           extends (CC' ++ CC'') cn en.
Proof.
  induction 1.
  + intros.
    destruct CC'.
    ++ simpl in *.
       injection H0;intros;subst.
       contradiction.
    ++ simpl in *.
       injection H0;intros;subst.
       eapply base.
       eapply in_app_or in H.
       destruct H.
       eapply in_or_app.
       eauto.
       eapply in_or_app.
       simpl in H.
       eauto.
       destruct H; try (injection H;intros;subst;congruence).
       eauto.
  + intros.
    destruct CC'.
    ++ simpl in *.
       injection H0;intros;subst;clear H0.
       auto.
    ++ simpl in *.
       injection H0;intros;subst.
       generalize H1;intros.
       eapply IHextends in H1;eauto.
       eapply ind. auto.
Qed.


Hint Resolve extends_narrower_deep_neqfirst extends_narrower_deep_eqfirst : myhints.
Hint Resolve extends_narrower_deep_neqfirst extends_narrower_deep_eqfirst.

    
Fixpoint number_of_extends (CC:JFProgram) (cn:JFClassName) :=
  match CC with
    | [] => None
    | (JFCDecl x (Some ex) fields' methods') :: CC' =>
      if JFClassName_dec x cn
      then match (number_of_extends CC' ex) with
             | None => None
             | Some n => Some (n+1)
           end
      else number_of_extends CC' cn
    | (JFCDecl x None fields' methods') :: CC' =>
      if JFClassName_dec x JFObjectName
      then if JFClassName_dec cn JFObjectName
           then Some 0
           else number_of_extends CC' cn
      else None
  end.

Lemma number_of_extends_compose:
  forall ex flds mthds CC C D n,
    D<>C ->
    number_of_extends CC C = Some n ->
    number_of_extends ((JFCDecl D (Some ex) flds mthds) :: CC) C = Some n.
Proof.
  scrush.
Qed.


Lemma number_of_extends_compose_eq:
  forall flds mthds CC C D n,
    number_of_extends CC C = Some n ->
    number_of_extends ((JFCDecl D (Some C) flds mthds) :: CC) D = Some (n+1).
Proof.
  scrush.
Qed.




Lemma number_of_extends_decompose:
  forall ex flds mthds CC C n,
    number_of_extends ((JFCDecl C (Some ex) flds mthds) :: CC) C = Some n ->
    number_of_extends CC ex = Some (n-1) /\ n > 0.
Proof.
  intros.
  unfold number_of_extends in H.
  destruct (JFClassName_dec C C).
  fold (number_of_extends CC ex) in H.
  destruct (number_of_extends CC ex).
  + injection H.
    intros.
    rewrite <- H0.
    auto with zarith.
  + discriminate H.
  + tauto.
Qed.


Lemma number_of_extends_decompose_neq:
  forall ex flds mthds CC C D n,
    C<>D ->
    number_of_extends ((JFCDecl C ex flds mthds) :: CC) D = Some n ->
    number_of_extends CC D = Some n.
Proof.
  scrush.
Qed.

Lemma number_of_extends_none:
  forall CC D fields methods,
    D <> JFObjectName ->
    number_of_extends (JFCDecl D None fields methods :: CC) D = None.
Proof.
  scrush.
Qed.


Lemma number_of_extends_find_class_simple:
  forall CC j n,
    number_of_extends CC j = Some (n) ->
         exists x, find_class CC j = Some x.
Proof.
  induction CC.
  * sauto.
  * intros.
    unfold number_of_extends in H.
    destruct a.
    destruct ex.
    destruct (JFClassName_dec cn j).
    clear H.
    scrush.
    scrush.
    fold (number_of_extends CC j) in H.
    destruct (JFClassName_dec j JFObjectName).
    scrush.
    scrush.
Qed.

Lemma number_of_extends_zero:
  forall CC cn,
    number_of_extends CC cn = Some 0 ->
    cn = JFObjectName.
Proof.
  induction CC; scrush.
Qed.

Lemma number_of_extends_object:
  forall CC C n,
    number_of_extends CC C = Some n ->
    program_contains CC JFObjectName = true.
Proof.
  induction CC.
  + intros.
    discriminate H.
  + intros.
    simpl in H.
    destruct a.
    destruct ex.
    ++ destruct (JFClassName_dec cn C).
       +++ subst.
           destruct (number_of_extends CC j) eqn:?; try discriminate H.
           eapply IHCC in Heqo.
           eauto using program_contains_further.
       +++ eapply IHCC in H.
           eauto using program_contains_further.
    ++ destruct (JFClassName_dec cn JFObjectName); try discriminate H.
       destruct (JFClassName_dec C JFObjectName); try discriminate H; try (subst;auto).
Qed.



   
Lemma names_unique_number_of_extends_loop:
  forall C flds mthds CC,
         names_unique ((JFCDecl C (Some C) flds mthds) :: CC) ->
         number_of_extends ((JFCDecl C (Some C) flds mthds) :: CC) C = None.
Proof.
  pose number_of_extends_find_class_simple; pose names_unique_zero;
    pose find_class_program_contains; pose program_contains_counts_occ;
      scrush.
Qed.


Hint Resolve number_of_extends_compose number_of_extends_compose_eq number_of_extends_decompose
     number_of_extends_decompose_neq number_of_extends_none : myhints.
  




Lemma number_of_extends_find_class:
  forall (CC:JFProgram) (cn dn:JFClassName) fields methods (n:nat),
    names_unique (JFCDecl cn (Some dn) fields methods :: CC) ->
    number_of_extends (JFCDecl cn (Some dn) fields methods :: CC) cn =
       Some n ->
  exists dd : JFClassDeclaration,
    find_class (JFCDecl cn (Some dn) fields methods :: CC) dn = Some dd.
Proof.
  induction CC.
  - sauto.
  - intros.
    destruct a.
    assert ({cn0=dn}+{cn0<>dn}) by auto using JFClassName_dec.
    destruct H1.
    * subst cn0. (* cn0 = dn *)
      assert (cn<>dn). {
        eapply names_unique_extends_non_refl;eauto.
        eapply base.
        simpl.
        left;eauto.
      }
      eapply find_class_lift_cons.
      simpl.
      destruct (JFClassName_dec dn dn);try contradiction.
      auto.
    * assert ({cn=dn} + {cn<>dn}) by apply JFClassName_dec.
      destruct H1.
      + rewrite e in *.
        simpl.
        destruct (JFClassName_dec dn dn).
        exists (JFCDecl dn (Some dn) fields methods).
        auto.
        tauto.
      + assert (exists dd : JFClassDeclaration,
                  find_class (JFCDecl cn (Some dn) fields methods :: CC) dn = 
                  Some dd). {
          apply (IHCC cn dn fields methods n);eauto.
          apply number_of_extends_decompose in H0;eauto.
          destruct H0.
          eapply number_of_extends_decompose_neq in H0;eauto.
          eapply number_of_extends_compose_eq in H0;eauto.
          replace (n -1 + 1) with n in H0 by (rewrite  Nat.sub_add; eauto).
          eauto.
        }
        decompose_ex H1.
        eapply find_class_further_neq in H1;eauto.
        exists dd.
        eapply find_class_same in H1;try apply n0;eauto.
        eapply find_class_same in H1;eauto.
Qed.
    
Definition subtype_well_founded (CC:JFProgram) :=
  forall (C:JFClassName) (cd:JFClassDeclaration),
    find_class CC C = Some cd -> exists (n:nat), number_of_extends CC C = Some n.


  
Lemma subtype_well_founded_further:
  forall CC cd,
    names_unique (cd::CC) ->
    subtype_well_founded (cd :: CC) -> subtype_well_founded CC.
Proof.
  intros.
  unfold subtype_well_founded in *.
  intros.
  destruct cd. 
  assert (count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0) by
      (apply (names_unique_count_zero CC cn ex fields methods); auto).
  assert (C <> cn) by
      (try apply (is_class_and_occ_zero CC C cn cd0);
       auto using (names_unique_further CC (JFCDecl cn ex fields methods))).
  destruct ex.
  assert ({j=C} + {j<>C}) by apply JFClassName_dec.
  destruct H4.
  - rewrite e in *.
    lapply (H0 cn (JFCDecl cn (Some C) fields methods)).
    intros.
    destruct H4.
    exists (x-1).
    apply (number_of_extends_decompose C fields methods CC cn x); auto.
    unfold find_class.
    destruct (JFClassName_dec cn cn).
    trivial.
    tauto.
  - lapply (H0 C cd0); intros.
    destruct H4.
    exists x.
    auto using (number_of_extends_decompose_neq (Some j) fields methods CC cn C).
    apply find_class_same; auto.
  - assert ( exists n : nat,
               number_of_extends (JFCDecl cn None fields methods :: CC) C = Some n).
    apply (H0 C cd0).
    apply (find_class_same CC cn C None fields methods cd0).
    auto.
    auto.
    destruct H4.
    unfold number_of_extends in H4.
    destruct (JFClassName_dec cn JFObjectName).
    destruct (JFClassName_dec C JFObjectName).
    rewrite e in *.
    rewrite e0 in *.
    tauto.
    fold (number_of_extends CC C) in H4.
    exists x; auto.
    discriminate H4.
Qed.

Lemma subtype_well_founded_decompose_program:
  forall CC CC',
    names_unique (CC ++ CC') ->
    subtype_well_founded (CC ++ CC') -> subtype_well_founded CC'.
Proof.
  induction CC.
  + sauto. 
  + pose subtype_well_founded_further; scrush.
Qed.

Lemma subtype_get_superclass:
  forall (CC:JFProgram) (C x ex:JFClassName) fields methods,
      names_unique CC ->
      subtype_well_founded CC ->
      find_class CC C = Some (JFCDecl x (Some ex) fields methods) ->
      exists cd,
      find_class CC ex = Some cd.
Proof.
  induction CC.
  + intros.
    compute in H0.
    discriminate H1.
  +  intros.
    destruct a.
    assert ({cn=ex}+{cn<>ex}) by apply JFClassName_dec; destruct H2; auto.
    ++ exists (JFCDecl cn ex0 fields0 methods0).
       simpl.
       rewrite e.
       destruct (JFClassName_dec ex ex); auto.
       tauto.
    ++ assert ({C=cn} + {C <> cn}) by apply JFClassName_dec; destruct H2; auto.
       +++ subst C.
           simpl in H1.
           destruct (JFClassName_dec cn cn);try contradiction.
           injection H1;auto.
           intros.
           subst x.
           unfold subtype_well_founded in H0.
           assert ({cn=ex}+{cn<>ex}) by apply JFClassName_dec; destruct H5; auto.
           ++++ rewrite e0 in *.
                exists (JFCDecl ex ex0 fields0 methods0).
                simpl.
                destruct (JFClassName_dec ex ex); try contradiction.
           ++++ assert ( exists n : nat,
                           number_of_extends (JFCDecl cn ex0 fields0 methods0 :: CC) cn = Some n).
                apply (H0 cn (JFCDecl cn ex0 fields0 methods0)).
                simpl.
                destruct (JFClassName_dec cn cn); try contradiction.
                auto.
                destruct H5.
                rewrite H4 in *.
                eapply number_of_extends_find_class;eauto.
       +++ simpl.
           destruct (JFClassName_dec cn ex);try contradiction.
           eapply IHCC;eauto 4 using subtype_well_founded_further, find_class_further_neq.
Qed.

    
Lemma subtype_well_founded_superclass:
  forall (CC:JFProgram) (C D:JFClassName) (ex:option JFClassName) fields methods,
    subtype_well_founded CC ->
    names_unique CC ->
    find_class CC C = Some (JFCDecl D ex fields methods) ->
    C <> JFObjectName ->
    exists D',
      find_class CC C = Some (JFCDecl D (Some D') fields methods).
Proof.
  induction CC.
  + intros.
    simpl in H1.
    discriminate H1.
  + intros.
    simpl.
    destruct a.
    simpl in H1.
    destruct (JFClassName_dec cn C).
    ++ subst.
       unfold subtype_well_founded in H.
       simpl in H1.
       assert (exists n : nat, number_of_extends (JFCDecl C ex0 fields0 methods0 :: CC) C = Some n).
       {
         eapply (H C).
         unfold find_class.
         destruct (JFClassName_dec C C); try contradiction.
         auto.
       } 
       unfold number_of_extends in H3.
       fold number_of_extends in H3.
       injection H1;clear H1;intros;subst.
       destruct ex.
       +++ eexists. auto.
       +++ simpl in H3.
           destruct (JFClassName_dec D JFObjectName); try contradiction.
           destruct H3.
           discriminate H1.
    ++ eapply IHCC; eauto.
       eapply subtype_well_founded_further; eauto.
Qed.

Lemma find_class_extends:
  forall CC cname name dname fields methods D,
    find_class CC cname = Some (JFCDecl name (Some dname) fields methods) ->
    find_class CC dname = Some D ->
    subtype_well_founded CC ->
    names_unique CC ->
    cname <> dname ->
    extends CC cname dname.
Proof.
  induction CC.
  + intros.
    simpl in H.
    discriminate H.
  + intros.
    destruct a.
    simpl in H.
    destruct (JFClassName_dec cn cname).
    ++ (* cn = cname *)
      subst.
      injection H;intros;clear H;subst.
      destruct D. 
      assert (dname=cn) by eauto using find_class_eq_name.
      subst.
      eapply find_class_in in H0.
      apply in_inv in H0.
      destruct H0.
      +++ injection H;intros;clear H;subst.
          contradiction.
      +++ eauto using base.
    ++ (* cn <> cname *)
      apply ind.
      assert (exists CC0 CC1,
                  CC = CC0 ++ ((JFCDecl name (Some dname) fields methods) :: CC1))
         by eauto using find_class_decompose_program.
      destruct H4 as [CC0 [CC1 H4]].
      rewrite H4 in *.
      assert (exists D', find_class
                           (JFCDecl name (Some dname) fields methods ::CC1)
                           dname = Some D').
      {
        rewrite app_comm_cons in H1.
        assert (subtype_well_founded
                  (JFCDecl name (Some dname) fields methods :: CC1))
          by (rewrite app_comm_cons in H2;
              eauto using subtype_well_founded_decompose_program).
        eapply subtype_get_superclass;eauto 3 using subtype_well_founded_further.
        assert (find_class (JFCDecl name (Some dname) fields methods :: CC1)
                           name =
                Some (JFCDecl name (Some dname) fields methods)).
        simpl.
        destruct (JFClassName_dec name name); try contradiction;auto.
        apply H6.
      }
      destruct H5.
      assert (exists C',
                 find_class
                   (CC0 ++ (JFCDecl name (Some dname) fields methods) :: CC1)
                   dname = Some C') by eauto with myhints.
      destruct H6.
      eapply IHCC; eauto 2 using subtype_well_founded_further.
Qed.


Lemma subtype_well_founded_contains_object:
  forall CC name cl,
    names_unique CC ->
    subtype_well_founded CC ->
    find_class CC name = Some cl ->
    program_contains CC JFObjectName = true.
Proof.
  induction CC.
  * intros.
    unfold find_class in H1.
    discriminate H1.
  * intros.
    destruct a.
    destruct (JFClassName_dec cn JFObjectName).
    rewrite e.
    unfold program_contains.
    destruct (JFClassName_dec JFObjectName JFObjectName).
    - auto.
    - intuition.
    - destruct (JFClassName_dec cn name).
      destruct CC.
      (* CC = [] *)
      -- unfold subtype_well_founded in H0.
         destruct ex.
         unfold number_of_extends in H0.
         lapply (H0 cn cl); intros.
         destruct H2.
         destruct (JFClassName_dec cn cn).
         discriminate H2.
         discriminate H2.
         rewrite e in *.
         auto.
         unfold number_of_extends in H0.
         lapply (H0 cn cl); intros.
         destruct (JFClassName_dec cn JFObjectName).
         auto.
         destruct H2.
         discriminate H2.
         lapply (H0 cn cl); intros.
         destruct (JFClassName_dec cn JFObjectName).
         intuition.
         destruct H2.
         discriminate H2.
         auto.
         rewrite e in *.
         auto.
      (* CC = hd :: tl *)
      -- destruct j.
         lapply (IHCC cn0 (JFCDecl cn0 ex0 fields0 methods0));intros.
         assert (program_contains (JFCDecl cn0 ex0 fields0 methods0 :: CC) JFObjectName = true).
         apply H2.
         + eapply subtype_well_founded_further.
           apply H.
           apply H0.
         + apply find_class_eq.
         + eapply program_contains_further.
           auto.
         + eapply names_unique_further.
           apply H.
      -- assert (program_contains CC JFObjectName = true). {
           apply (IHCC name cl);eauto using subtype_well_founded_further, find_class_further_neq.
         }
         eauto using program_contains_further.
Qed.

Lemma subtype_well_founded_program_contains_further:
  forall CC a b,
    names_unique (a::b::CC) ->
    (program_contains (a::b::CC) JFObjectName) = true ->
    subtype_well_founded (a::b::CC) ->
    (program_contains (b::CC) JFObjectName) = true.
Proof.
  induction CC.
  * intros.
    destruct a.
    destruct b.
    destruct (JFClassName_dec cn JFObjectName).
    ** subst.
       assert (JFObjectName <> cn0)
         by (eapply names_unique_in_neq;eauto;apply in_eq).
       unfold subtype_well_founded in H1.
       assert (exists n : nat,
                  number_of_extends
                    [JFCDecl JFObjectName ex fields methods;
                     JFCDecl cn0 ex0 fields0 methods0] cn0 = Some n).
       eapply H1.
       eapply find_class_same;eauto 2.
       apply find_class_eq.
       unfold number_of_extends in H3.
       destruct ex.
       *** destruct (JFClassName_dec JFObjectName cn0);try contradiction.
           destruct ex0.
           destruct (JFClassName_dec cn0 cn0);destruct H3;discriminate H3.
           destruct (JFClassName_dec cn0 JFObjectName);
             try (rewrite e in *;contradiction).
           destruct H3.
           discriminate H3.
       *** destruct (JFClassName_dec JFObjectName JFObjectName);
             try contradiction.
           clear e.
           destruct H3.
           destruct (JFClassName_dec cn0 JFObjectName);
             try rewrite e in *;try contradiction.
           destruct ex0.
           destruct (JFClassName_dec cn0 cn0);discriminate H3.
           discriminate H3.
    ** eapply program_contains_further_neq;eauto.
  * intros.
    destruct b.
    eapply subtype_well_founded_contains_object;eauto 2.
    eauto using subtype_well_founded_further.
    eapply find_class_eq.
Qed.

Lemma number_of_extends_compose_none_eq:
  forall flds mthds CC C D n,
    subtype_well_founded ((JFCDecl D None flds mthds) :: CC) ->
    number_of_extends CC C = Some n ->
    C<>D ->
    number_of_extends ((JFCDecl D None flds mthds) :: CC) C = Some n.
Proof.
  intros.
  simpl.
  destruct (JFClassName_dec D JFObjectName).
  + subst.
    destruct (JFClassName_dec C JFObjectName);try contradiction;auto.
  + unfold subtype_well_founded in H.
    pose find_class_eq.
    eapply H in e.
    decompose_ex e.
    scrush.
Qed.


Lemma number_of_extends_some:
  forall CC dcl CC0,
    names_unique CC ->
    subtype_well_founded CC ->
    CC = dcl :: CC0 ->
    exists n C, number_of_extends CC C = Some n.
Proof.
  induction CC.
  + intros. discriminate H1.
  + intros.
    injection H1;intros;subst. clear H1.
    destruct dcl.
    destruct CC0.
    ++ simpl.
       unfold subtype_well_founded in H0.
       pose find_class_eq.
       eapply H0 in e.
       decompose_ex e.
       simpl in e.
       destruct ex; try (destruct (JFClassName_dec cn cn);try contradiction; try discriminate e).
       destruct (JFClassName_dec cn JFObjectName); try discriminate e.
       exists 0, cn.
       destruct (JFClassName_dec cn JFObjectName);try contradiction;auto.
    ++ generalize H0;intros.
       eapply subtype_well_founded_further in H1;eauto.
       eapply IHCC in H1;eauto.
       decompose_ex H1.
       destruct (JFClassName_dec C cn).
       +++ subst.
           eapply number_of_extends_find_class_simple in H1;eauto.
           decompose_ex H1.
           destruct x.
           generalize H1;intros.
           eapply find_class_eq_name in H2.
           subst.
           eapply find_class_in in H1.
           eapply names_unique_in_neq in H1;eauto.
           contradiction.
       +++ exists n, C.
           destruct ex.
           ++++ eapply number_of_extends_compose;
                  auto with zarith.
           ++++ eapply number_of_extends_compose_none_eq;eauto.
Qed.
  
Lemma subtype_well_founded_neq:
  forall CC name name' fields methods,
    names_unique  (JFCDecl name (Some name') fields methods :: CC) ->
    subtype_well_founded (JFCDecl name (Some name') fields methods :: CC) ->
    name <> name'.
Proof.
  intros.
  unfold subtype_well_founded in H0.
  intro.
  subst name'.
  specialize H0 with name (JFCDecl name (Some name) fields methods).
  lapply H0;intros.
  destruct H1.
  assert (number_of_extends CC name = Some (x - 1) /\ x > 0) by eauto using number_of_extends_decompose.
  assert (exists x : JFClassDeclaration, find_class CC name = Some x).
  eapply number_of_extends_find_class_simple.
  decompose [and] H2;clear H2.
  apply H3.
  assert (count_occ Bool.bool_dec (map (is_class_name name) CC) true = 0) by eauto.
  destruct H3.
  assert (name<>name) by eauto 3 using is_class_and_occ_zero.
  tauto.
  apply find_class_eq.
Qed.

Lemma subtype_well_founded_find_class_neq:
  forall CC name name' fields methods,
    names_unique  CC ->
    subtype_well_founded CC ->
    find_class CC name = Some (JFCDecl name (Some name') fields methods) ->
    name <> name'.
Proof.
  induction CC.
  + intros.
    discriminate H1.
  + intros.
    destruct a.
    simpl in H1.
    destruct (JFClassName_dec cn name).
    ++ subst.
       injection H1;intros.
       subst.
       eauto using subtype_well_founded_neq.
    ++ eauto 4 using subtype_well_founded_further.
Qed.



(** The property that all class names occur in the program uniquely. *)
Definition if_not_extended_then_object (cd:JFClassDeclaration) :=
  match cd with
    | JFCDecl cn None _ _ => cn = JFObjectName
    | JFCDecl _ (Some _) _ _ => cd = cd
  end.

(** The property that only Object class is not an extension of another class *)
Definition extensions_in_all_but_object (CC:JFProgram) :=
  Forall (if_not_extended_then_object) CC.

Lemma extensions_in_all_but_object_further:
forall (CC:JFProgram) (cd:JFClassDeclaration),
    extensions_in_all_but_object (cd::CC) ->
    extensions_in_all_but_object CC.
Proof.
  intros.
  unfold extensions_in_all_but_object in *.
  apply Forall_forall.
  assert (forall x : JFClassDeclaration, In x (cd::CC) -> if_not_extended_then_object x).
  apply Forall_forall.
  auto.
  firstorder.
Qed.

Lemma names_unique_subtype_well_founded_extensions_in_all_but_object:
forall (CC:JFProgram) (cd:JFClassDeclaration),
  names_unique CC ->
  subtype_well_founded CC ->
  extensions_in_all_but_object CC.
Proof.
  induction CC.
  + intros.
    unfold extensions_in_all_but_object.
    auto.
  + intros.
    destruct a.
    destruct (JFClassName_dec cn JFObjectName).
    ++ subst.
       unfold extensions_in_all_but_object.
       eapply Forall_cons;eauto.
       +++ simpl.
           destruct ex;auto.
       +++ fold (extensions_in_all_but_object CC).
           unfold subtype_well_founded in H0.
           eapply IHCC;eauto using subtype_well_founded_further.
    ++ unfold extensions_in_all_but_object.
       eapply Forall_cons;eauto.
       +++ simpl.
           destruct ex; eauto.
           unfold subtype_well_founded in H0.
           pose find_class_eq as Fcl.
           apply H0 in Fcl.
           decompose_ex Fcl.
           simpl in Fcl.
           destruct (JFClassName_dec cn JFObjectName);try contradiction.
           inversion Fcl.
       +++ fold (extensions_in_all_but_object CC).
           unfold subtype_well_founded in H0.
           eapply IHCC;eauto using subtype_well_founded_further.
Qed.

Hint Resolve  extensions_in_all_but_object_further subtype_well_founded_further subtype_well_founded_decompose_program.
  
(** The property that Object class is not extended. As
    Java Language Specification says in Section 8.1.4:
    "The extends clause must not appear in the definition 
    of the class Object, or a compile-time error occurs, 
    because it is the primordial class and has no direct superclass." *)
Definition object_not_extended (cd:JFClassDeclaration) :=
  match cd with
    | JFCDecl cn ex _ _ => cn = JFObjectName -> ex = None
  end.


(** A single check that Object is not extended is
    lifted to the whole program. *)
Definition object_is_not_extended (CC:JFProgram) :=
  Forall (object_not_extended) CC.

Lemma object_is_not_extended_further:
forall (CC:JFProgram) (cd:JFClassDeclaration),
    object_is_not_extended (cd::CC) ->
    object_is_not_extended CC.
Proof.
  intros.
  unfold object_is_not_extended in *.
  apply Forall_forall.
  assert (forall x : JFClassDeclaration, In x (cd::CC) -> object_not_extended x).
  apply Forall_forall.
  auto.
  firstorder.
Qed.

Lemma object_is_not_extended_first:
  forall (CC:JFProgram) cn x fs ms,
    object_is_not_extended (JFCDecl cn (Some x) fs ms :: CC) ->
    cn <> JFObjectName.
Proof.
  intros.
  unfold object_is_not_extended in H.
  apply Forall_inv in H.
  unfold object_not_extended in H.
  intro.
  lapply H; intros.
  discriminate H1.
  auto.
Qed.

Lemma extends_further_object:
  forall (CC:JFProgram) (cd:JFClassDeclaration) (cn dn:JFClassName),
   object_is_not_extended (cd :: CC) ->
   JFObject = JFClass cn -> extends (cd :: CC) cn dn -> extends CC cn dn.
Proof.
  induction CC.
  + intros.
    destruct cd.
    unfold object_is_not_extended in *.
    apply Forall_inv in H.
    unfold object_not_extended in *.
    inversion H1.
    repeat destruct H9.
    auto.
  + intros.
    inversion H1.
    unfold JFObject in H0.
    injection H0; intros.
    rewrite <- H7 in *.
    unfold object_is_not_extended in H.
    apply Forall_inv in H.
    rewrite <- H2 in H.
    unfold object_not_extended in H.
    lapply H.
    intros.
    discriminate H8.
    auto.
    auto.
Qed.

Lemma object_is_not_extended_extends_neq:
  forall CC cn dn,
    object_is_not_extended CC ->
    extends CC cn dn ->
    cn <> JFObjectName.
Proof.
  induction 2.
  + eauto 2 using object_is_not_extended_first.
  + eauto 3 using object_is_not_extended_further.
Qed.

Lemma number_of_extends_object_is_not_extended:
  forall CC cd CC0,
    names_unique CC ->
    subtype_well_founded CC ->
    CC = cd :: CC0 ->
    object_is_not_extended CC.
Proof.
  induction CC.
  + intros cd CC0 Nuq.
    intros.
    discriminate H0.
  + intros cd CC0 Nuq.
    intros.
    rename H into GH0.
    generalize GH0;intros.
    destruct a.
    destruct ex.
    ++ unfold subtype_well_founded in GH1.
       pose find_class_eq.
       eapply GH1 in e.
       decompose_ex e.
       simpl in e.
       destruct (JFClassName_dec cn cn);try contradiction.
       destruct (number_of_extends CC j) eqn:?; try congruence.
       +++ generalize Heqo;intros.
           eapply number_of_extends_object in Heqo0;eauto.
           destruct (JFClassName_dec cn JFObjectName).
           ++++ subst.
                eapply program_contains_find_class in Heqo0.
                decompose_ex Heqo0.
                destruct cd0.
                generalize Heqo0;intros.
                eapply find_class_eq_name in Heqo1.
                subst.
                eapply find_class_in in Heqo0.
                eapply names_unique_in_neq in Heqo0;eauto 1.
                contradiction.
           ++++ unfold object_is_not_extended.
                eapply Forall_cons; try (simpl;contradiction).
                fold (object_is_not_extended CC).
                destruct CC; try discriminate Heqo0.
                eauto.
    ++ destruct (JFClassName_dec cn JFObjectName).
       +++ subst.
           unfold object_is_not_extended.
           apply Forall_cons; simpl;auto.
           fold (object_is_not_extended CC).
           destruct CC.
           ++++ unfold object_is_not_extended;auto.
           ++++ destruct j.
                unfold subtype_well_founded in GH0.
                assert (JFObjectName <> cn). {
                  intro.
                  rewrite H in Nuq.
                  eapply names_unique_in_neq in Nuq.
                  eapply Nuq.
                  trivial. 
                  eapply in_eq.
                }
                eauto.
       +++ unfold object_is_not_extended.
           apply Forall_cons; simpl;auto.
           destruct CC.
           ++++ auto.
           ++++ eapply IHCC;eauto 2.
Qed.

Hint Resolve  object_is_not_extended_extends_neq extends_further_object object_is_not_extended_first object_is_not_extended_further.
    

Inductive subtyping (CC: JFProgram) : JFCId -> JFCId -> Prop :=
| subrefl  : forall (C:JFCId), subtyping CC C C
| subobj   : forall (C:JFCId), subtyping CC C JFObject
| botobj   : forall (C:JFCId), subtyping CC JFBotClass C
| substep  : forall (C:JFCId) (D:JFCId) (E:JFCId)
                    (cn:JFClassName) (dn:JFClassName),
               C = JFClass cn -> D = JFClass dn ->
               extends CC cn dn ->
               subtyping CC D E -> subtyping CC C E.

Hint Constructors subtyping.

  
Lemma subtyping_further:
  forall (CC:JFProgram) (C:JFCId) (D:JFCId) (cd:JFClassDeclaration),
    subtyping CC C D -> subtyping (cd :: CC) C D.
Proof. 
  induction 1.
  * auto.
  * apply subobj.
  * auto.
  * eapply (substep (cd :: CC) C D E).
    + eauto.
    + eauto.
    + inversion H1.
      - destruct cd.
        apply ind.
        rewrite <- H5 in *.
        rewrite <- H6 in *.
        rewrite H4.
        auto.
      - destruct cd. apply ind.
        rewrite H4.
        auto.
    + auto.
Qed.

Lemma subtyping_further_deep:
  forall (CC:JFProgram) (CC':JFProgram) (DD:JFProgram) (C:JFCId) (D:JFCId) (cd:JFClassDeclaration),
    subtyping CC C D ->
    CC = CC' ++ DD ->
    subtyping (CC' ++ cd :: DD) C D.
Proof.
  induction 1; eauto.
Qed.

Lemma substep_deep:
  forall DD dn decl CC cn fields methods,
    find_class DD dn = Some decl ->
    subtyping (CC ++ JFCDecl cn (Some dn) fields methods :: DD) (JFClass cn) (JFClass dn).
Proof.
  induction CC.
  + intros.
    simpl.
    eapply substep; try trivial.
    destruct decl.
    generalize H;intros; eapply find_class_eq_name in H0; subst.
    eapply base; eauto using find_class_in.
  + intros.
    simpl.
    eapply subtyping_further.
    eauto.
Qed.

Lemma subtyping_first_in:
  forall CC C D cn dn,
    subtyping CC C D ->
    C = (JFClass cn) ->
    D = (JFClass dn) ->
    D <> JFObject ->
    cn <> dn ->
    exists ex flds mthds,
      In (JFCDecl cn ex flds mthds) CC.
Proof.
  induction 1;try congruence.
  intros.
  subst.
  eapply extends_in_first in H1.
  injection H3;clear H3;intros;subst.
  sauto.
Qed.

Lemma subtyping_find_class_further:
  forall CC D E,
    subtyping CC D E ->
    forall  CC0 cd cn' ex fields methods dn en,
      CC = (cd :: CC0) ->
      cd = JFCDecl cn' ex fields methods ->
      D = (JFClass dn) ->
      E = (JFClass en) ->
      E <> JFObject ->
      dn <> en ->
      dn <> cn' ->
      exists cd, find_class CC0 dn = Some cd.
Proof.
  intros CC D E.
  intro.
  induction H.
  * intros.
    congruence.
  * intros.
    contradiction.
  * intros.
    congruence.
  * intros.
    subst.
    injection H5;intros;clear H5.
    subst.
    eapply extends_in_first in H1.
    destruct H1. destruct H.
    eapply in_inv in H.
    destruct H.
    ** congruence.
    ** eapply in_find_class_raw in H.
       do 3 destruct H.
       clear -H.
       firstorder.
Qed.



    
Lemma object_is_not_subtype:
  forall (CC:JFProgram) (C:JFCId),
    names_unique CC -> 
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    subtyping CC JFObject C -> C = JFObject.
Proof.
  intros until 3.
  cut (forall D, subtyping CC D C -> D = JFObject -> C = JFObject); eauto.
  induction 1; intros; trivial; try discriminate.
  apply IHsubtyping.
  unfold JFObject in *.
  match goal with
    [ H : (extends _ _ _) |- _ ] => apply object_is_not_extended_extends_neq in H; eauto 1
  end.
  congruence.
Qed.

Lemma subtrans : forall (CC:JFProgram) (C:JFCId) (D:JFCId) (E:JFCId),
                   (program_contains CC JFObjectName) = true ->
                   names_unique CC -> 
                   object_is_not_extended CC ->
                   extensions_in_all_but_object CC ->
                   subtyping CC C D -> subtyping CC D E -> subtyping CC C E.
Proof.
  induction 5.
  * trivial.
  * intro Hsub.
    apply object_is_not_subtype in Hsub; eauto 1.
    subst.
    constructor.
  * intros; constructor.
  * intros.
    eauto.
Qed.



Lemma subtyping_less:
  forall CC C D,
    subtyping CC C D ->
    forall  dn en,
    subtyping CC C (JFClass en) ->
    D = (JFClass dn) ->
    dn <> en ->
    dn <> JFObjectName ->
    en <> JFObjectName ->
    names_unique CC ->
    (subtyping CC D (JFClass en)) \/ (subtyping CC (JFClass en) D) \/ (C = JFBotClass).
Proof.
  induction 1.
  + intros.
    left;auto.
  + intros.
    inversion H;subst.
    ++ right;left;auto.
    ++ contradiction.
    ++ right;right;auto.
    ++ unfold JFObject in H0.
       congruence.
  + intros.
    right;right;auto.
  + intros.
    inversion H3;subst.
    ++ injection H10;intros.
       subst.
       right;left.
       eapply substep;try apply H1;eauto.
    ++ contradiction.
    ++ discriminate H9.
    ++ injection H9;intros.
       subst.
       eapply extends_unique_dir in H11;try eapply H1;eauto.
       subst.
       eapply IHsubtyping in H12;eauto 1.
       destruct H12 as [H12|H12];try tauto.
       destruct H12 as [H12|H12];try tauto.
       discriminate H12.
Qed.

    
Lemma subtyping_greater_in:
  forall CC C D,
    subtyping CC C D ->
    forall cn dn,
    C = (JFClass cn) ->
    D = (JFClass dn) ->
    names_unique CC ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    cn <> dn ->
    dn <> JFObjectName ->
    exists ex fields methods,
      In (JFCDecl dn ex fields methods) CC.
Proof.
  intros CC C D.
  intro.
  induction H.
  * intros.
    congruence.
  * intros.
    injection H0;intros.
    rewrite H6 in *.
    contradiction.
  * intros.
    discriminate H.
  * intros.
    subst. 
    injection H3;intros;clear H3;subst.
    destruct (JFClassName_dec dn dn0).
    ** subst.
       destruct CC.
       *** inversion H1.
       *** assert (exists
                      (ex : option JFClassName)
                      (fields : list JFFieldDeclaration) 
                      (methods : list JFMethodDeclaration),
                      In (JFCDecl dn0 ex fields methods) CC).
           eapply extends_in_second_second;eauto.
           do 3 destruct H.
           exists x, x0, x1.
           eauto using in_cons.
    ** eapply IHsubtyping;eauto.
Qed.
               
       
Lemma subtyping_further_neq:
  forall CC CC0 D E,
    subtyping CC0 D E ->
    names_unique CC0 -> 
    forall cn ex fields methods,
      CC0 = (JFCDecl cn ex fields methods :: CC) ->
      D <> JFClass cn ->
      subtyping CC D E.
Proof.
  induction 1.
  - auto.
  - auto.
  - auto.
  - intros.
    eapply substep.
    + eauto.
    + apply H0.
    + eapply extends_narrower.
      rewrite H4 in H1.
      eauto.
      congruence.
    + assert (D <> JFClass cn0).
      eapply extends_neq.
      rewrite H4 in H3.
      eauto.
      exists cn,dn.
      rewrite H4 in H1.
      eauto.
      eapply IHsubtyping.
      * eauto.
      * eauto.
      * auto.
Qed.




Lemma subtyping_not_bot:
  forall CC C D,
    subtyping CC C D -> D = JFBotClass  -> C = JFBotClass.
Proof.
  induction 1.
  + auto.
  + intros.
    discriminate H.
  + auto.
  + intros.
    lapply IHsubtyping.
    intros.
    subst D.
    discriminate H4.
    auto.
Qed.




Lemma extends_subtyping_eq:
  forall CC C D,
    subtyping CC D C ->
    forall cn dn,
      D = (JFClass dn) ->
      C = (JFClass cn) ->
      names_unique CC ->
      object_is_not_extended CC ->
      extensions_in_all_but_object CC ->
      extends CC cn dn ->
      cn = dn.
Proof.
  induction CC.
  + intros.
    inversion H5.
  + intros.
    destruct a.
    destruct (JFClassName_dec cn cn0).
    ++ subst.
       destruct (JFClassName_dec dn cn0).
       +++ subst;auto.
       +++ eapply subtyping_further_neq in H;eauto 2;try congruence.
           eapply subtyping_greater_in in H;eauto 2;try congruence.
           decompose_ex H.
           eapply names_unique_in_neq in H;eauto 1.
           contradiction.
    ++ subst.
       destruct (JFClassName_dec cn0 dn).
       +++ subst.
           eapply extends_narrower in H5;eauto 2.
           eapply extends_in_second in H5;eauto 2.
           decompose_ex H5.
           eapply names_unique_in_neq in H5;eauto 1.
           contradiction.
       +++ eapply extends_narrower in H5;eauto 2.
           eapply subtyping_further_neq in H;eauto 2;try congruence.
           eauto 5.
Qed.
           
Lemma subantisymm :
  forall CC C D,
    names_unique CC ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    subtyping CC C D -> subtyping CC D C -> C = D.
Proof.
  induction CC.
  * intros.
    inversion H2;eauto 2;subst.
    ** eauto 2 using object_is_not_subtype.
    ** eapply subtyping_not_bot in H3;eauto 2.
    ** inversion H6.
  * intros.
    destruct a.
    destruct C;try (eapply subtyping_not_bot in H3;eauto 2;congruence).
    destruct D;eauto 2 using subtyping_not_bot.
    destruct (JFClassName_dec cn cn0).
    ** subst.
       destruct (JFClassName_dec cn1 cn0);try congruence.
       destruct (JFClassName_dec cn0 JFObjectName); try (subst; eapply object_is_not_subtype in H2;eauto 2).
       eapply subtyping_further_neq in H3;eauto 2;try congruence.
       eapply subtyping_greater_in in H3;eauto 2;try congruence.
       decompose_ex H3.
       eapply names_unique_in_neq in H3;eauto 1.
       contradiction.
    ** destruct (JFClassName_dec cn cn1).
       *** subst.
           generalize H1;intros.
           destruct (JFClassName_dec cn1 JFObjectName); try (subst; eapply object_is_not_subtype in H1;eauto 2).
           eapply subtyping_further_neq in H2;eauto 2;try congruence.
           eapply subtyping_greater_in in H2;eauto 2;try congruence.
           decompose_ex H2.
           eapply names_unique_in_neq in H2;eauto 1.
           contradiction.
       *** eapply subtyping_further_neq in H2;eauto 2;try congruence.
           eapply subtyping_further_neq in H3;eauto 2;try congruence.
           eauto.
Qed.
           
Lemma subtyping_compl_monotone:
  forall CC' C D,
    subtyping CC' C D ->
    forall d CC DD E,
      CC' = (d :: CC) ++ DD ->
      subtyping ((d :: CC) ++ E :: DD) C D.
Proof.
  induction 1;eauto.
Qed.
  

Lemma subtyping_monotone:
  forall CC C D,
    subtyping CC C D ->
    forall CC' DD E,
      CC = (CC' ++ DD) ->
      subtyping (CC' ++ E :: DD) C D.
Proof.
  induction 1;eauto.
Qed.


(* subtyping decidability *)

Lemma skipping_extends_loop:
  forall (CC : JFProgram) (C E : JFCId),
    subtyping CC C E ->
    forall D cn dn,
      C <> E ->
      E <> JFObject ->
      C = JFClass cn ->
      D = JFClass dn ->
      extends CC cn dn ->
      subtyping CC D E ->
      exists dn', extends CC cn dn' /\ subtyping CC (JFClass dn') E /\ dn' <> cn.
Proof.
  induction 1.
  + intros.
    subst. congruence.
  + congruence.
  + intros.
    discriminate H1.
  + intros ? cn0 dn0.
    intros.
    subst.
    destruct (JFClassName_dec cn0 dn0).
    ++ subst.
       injection H5;clear H5;intro;subst.
       inversion H2; try (subst; exists dn; repeat split;eauto;congruence).
       subst.
       injection H; clear H;intro;subst.
       destruct (JFClassName_dec cn dn0).
       +++ subst;eapply IHsubtyping;eauto.
       +++ exists cn.
           intuition.
    ++ exists dn0;intuition.
Qed.

    


Inductive subtyping_witness : JFProgram -> JFProgram -> JFClassName -> JFClassName -> Prop  :=
| empty_witness : forall CC cn, subtyping_witness [] CC cn cn
| head_witness :
    forall DD DD' DD'' CC cn cn' dn fields methods cd,
      DD = DD' ++ (JFCDecl cn (Some cn') fields methods :: DD'') ->
      ~ In (JFCDecl cn (Some cn') fields methods) DD' ->
      find_class DD'' cn' = Some cd ->
      subtyping_witness CC DD cn' dn ->
      subtyping_witness (JFCDecl cn (Some cn') fields methods :: CC) DD cn dn.

Hint Constructors subtyping_witness : myhints.
Hint Constructors subtyping_witness.

Lemma subtyping_witness_only_some:
  forall CC DD cn dn en ex flds mthds,
    subtyping_witness CC DD cn dn ->
    In (JFCDecl en ex flds mthds) CC -> exists dn, ex = Some dn.
Proof.
  induction CC.
  + intros.
    inversion H0.
  + intros.
    inversion H.
    subst.
    simpl in H0.
    destruct H0.
    ++ injection H0;clear H0;intros;subst.
       eexists;eauto.
    ++ eapply IHCC in H0;eauto.
Qed.
       
Lemma decompose_double_app:
  forall A,
  forall n (DD:list A) DD' EE EE',
    length DD = n ->
    DD ++ DD' = EE ++ EE' ->
    (exists DD'', DD = EE ++ DD'' /\ EE' = DD'' ++ DD') \/
    (exists DD'', EE = DD ++ DD'' /\ DD' = DD'' ++ EE').
Proof.
  induction n.
  + intros.
    eapply length_zero_iff_nil in H.
    subst.
    right.
    exists EE.
    simpl in *.
    eauto.
  + intros.
    destruct DD; try inversion H.
    assert (length EE <= n+1 \/ n+1 < length EE)
      by eauto using Nat.le_gt_cases.
    destruct H1.
    ++ left.
       generalize H1.
       generalize H0.
       generalize EE.
       induction EE0.
       +++ exists (a :: DD).
           simpl in *.
           eauto.
       +++ intros.
           simpl in H3.
           injection H3;intros.
           subst.
           eapply IHn in H5;eauto.
           destruct H5.
           ++++ decompose_ex H2.
                decompose_and H2.
                subst.
                eexists.
                simpl.
                auto.
           ++++ simpl in H4.
                decompose_ex H2.
                decompose_and H2.
                eapply f_equal in H5.
                rewrite app_length in H5.
                rewrite H5 in H4.
                assert (length DD'' =0) by eauto with zarith.
                apply length_zero_iff_nil in H2.
                subst.
                simpl in H3.
                injection H3;intros;subst.
                eapply app_inv_tail in H2.
                subst.
                exists [].
                simpl.
                rewrite app_nil_r.
                eauto.
    ++ right.
       generalize H0.
       generalize H1.
       generalize EE.
       induction EE0.
       +++ intros.
           simpl in H3.
           eauto with zarith.
           pose (NPeano.Nat.nlt_0_r (n+1)).
           contradiction.
       +++ intros.
           simpl in H4.
           injection H4;intros;subst a0.
           eapply IHn in H5;eauto.
           destruct H5.
           ++++ decompose_ex H5.
                decompose_and H5.
                subst.
                rewrite app_assoc in H0.
                eapply app_inv_tail in H0.
                rewrite app_comm_cons in H0.
                eapply app_inv_tail in H0.
                subst EE.
                simpl in H1.
                rewrite app_length in H1.
                assert (length DD'' < 0) by eauto with zarith.
                pose (Nat.nlt_0_r (Datatypes.length DD'')).
                contradiction.
           ++++ decompose_ex H5.
                decompose_and H5.
                subst.
                exists DD'';eauto.
Qed.
                
Lemma subtyping_witness_monotone:
  forall CC DD DD' cn dn,
    subtyping_witness CC (DD ++ DD') cn dn ->
    forall dd,
    subtyping_witness CC (DD ++ dd :: DD') cn dn.
Proof.
  induction CC.
  + intros.
    inversion H.
    subst.
    eauto.
  + intros.
    inversion H.
    subst.
    eapply decompose_double_app in H2;eauto.
    destruct H2.
    ++ decompose_ex H0.
       decompose_and H0.
       subst DD.
       destruct DD''0.
       +++ simpl in H2. subst DD'.
           destruct (JFClassDeclaration_dec dd (JFCDecl cn (Some cn') fields methods)).
           ++++ subst dd.
                eapply find_class_lift_cons in H4.
                decompose_ex H4.
                eapply head_witness; try eapply H4; try eapply H3.
                simpl in *.
                rewrite app_nil_r.
                eauto.
                eapply IHCC;eauto.
           ++++ assert (~ In (JFCDecl cn (Some cn') fields methods) (DD'0 ++ [dd])). {
                  intro.
                  apply H3.
                  eapply in_app_or in H0.
                  simpl in H0.
                  destruct H0;eauto.
                  destruct H0;eauto; try contradiction.
                } 
                eapply head_witness; try eapply H4; try eapply H0.
                rewrite app_nil_r.
                fold (app [dd] (JFCDecl cn (Some cn') fields methods :: DD'')).
                rewrite app_assoc.
                auto.
                eapply IHCC;eauto.
       +++ simpl in H2.
           injection H2;intros.
           subst j.
           subst DD''.
           eapply find_class_lift_cons_inside in H4.
           decompose_ex H4.
           eapply head_witness; try apply H3;try apply H4.
           rewrite <- app_assoc.
           simpl.
           eauto.
           eapply IHCC;eauto.
    ++ decompose_ex H0.
       decompose_and H0.
       subst DD'.
       destruct DD''0.
       +++ rewrite app_nil_r in H1. subst DD'0.
           destruct (JFClassDeclaration_dec dd (JFCDecl cn (Some cn') fields methods)).
           ++++ subst dd.
                eapply find_class_lift_cons in H4.
                decompose_ex H4.
                eapply head_witness; try eapply H4; try eapply H3.
                simpl in *.
                eauto.
                eapply IHCC;eauto.
           ++++ assert (~ In (JFCDecl cn (Some cn') fields methods) (DD ++ [dd])). {
                  intro.
                  apply H3.
                  eapply in_app_or in H0.
                  simpl in H0.
                  destruct H0; eauto.
                  destruct H0;eauto; try contradiction.
                }
                eapply head_witness; try eapply H4; try eapply H0.
                simpl.
                fold (app [dd] (JFCDecl cn (Some cn') fields methods :: DD'')).
                rewrite app_assoc.
                auto.
                eapply IHCC;eauto.
       +++ destruct (JFClassDeclaration_dec dd (JFCDecl cn (Some cn') fields methods)).
           ++++ subst dd.
                assert (~ In (JFCDecl cn (Some cn') fields methods) DD). {
                  intro.
                  apply H3.
                  subst.
                  eapply in_or_app.
                  left;eauto.
                }
                subst DD'0.
                eapply find_class_lift_cons in H4.
                decompose_ex H4.
                eapply find_class_lift in H4.
                decompose_ex H4.
                rewrite <- app_comm_cons.
                eapply head_witness; try apply H4;try apply H0.
                rewrite app_comm_cons.
                eauto.
                eapply IHCC;eauto.
           ++++ assert (~ In (JFCDecl cn (Some cn') fields methods) (DD ++ dd :: (j :: DD''0))). {
                  intro.
                  apply H3.
                  subst.
                  eapply in_app_or in H0.
                  apply in_or_app.
                  destruct H0.
                  + left;eauto.
                  + simpl in H0.
                    destruct H0.
                    ++ contradiction.
                    ++ simpl.
                       eauto.
                }
                subst DD'0.
                eapply head_witness; try apply H4;try apply H0.
                rewrite app_comm_cons.
                rewrite app_assoc.
                eauto.
                eapply IHCC;eauto.
Qed.


Lemma subtyping_witness_smaller_none:
  forall CC DD cn0 fields methods cn dn,
  subtyping_witness CC (JFCDecl cn0 None fields methods :: DD) cn dn ->
  subtyping_witness CC DD cn dn.
Proof.
  induction CC.
  + intros.
    inversion H.
    subst.
    eauto.
  + intros.
    inversion H.
    subst.
    destruct DD'.
    ++ simpl in H2.
       injection H2;intros;eauto.
       inversion H6.
    ++ simpl in H2.
       injection H2;intros.
       eapply head_witness;try eapply H0;eauto.
       intro.
       eapply H3.
       simpl.
       eauto.
Qed.


Lemma in_split_notfirst:
  forall A (eq_dec: forall (x:A) (y:A), {x=y} + {x<>y}),
  forall l (x:A),
    In x l -> exists l1 l2, l = l1 ++ (x :: l2) /\ ~ (In x l1).
Proof.
  induction l.
  + intros.
    inversion H.
  + intros.
    destruct (eq_dec x a).
    ++ subst.
       exists [], l.
       split;simpl;auto.
    ++ simpl in H.
       destruct H; try congruence.
       eapply IHl in H.
       decompose_ex H.
       decompose [and] H.
       subst.
       do 2 eexists.
       split.
       rewrite app_comm_cons.
       auto.
       intro.
       apply H1.
       simpl in H0.
       destruct H0; try congruence.
Qed.

Lemma not_in_first_eq:
  forall A,
  forall l1 l1' l2 l2' (x:A) ,
    l1 ++ x :: l1' = l2 ++ x :: l2' ->
    ~ In x l1 ->
    ~ In x l2 ->
    l1 = l2 /\ l1' = l2'.
Proof.
  induction l1.
  + intros.
    simpl in H.
    destruct l2.
    ++ simpl in H.
       injection H;intros.
       subst.
       auto.
    ++ simpl in H.
       simpl in H1.
       injection H;intros;subst.
       assert False.
       apply H1.
       left;auto.
       contradiction.
  + intros.
    simpl in H.
    destruct l2.
    ++ simpl in H.
       injection H;intros.
       subst.
       simpl in H0.
       assert False.
       apply H0;left;auto.
       contradiction.
    ++ simpl in H.
       injection H;intros.
       subst a0.
       eapply IHl1 in H2.
       decompose [and] H2.
       subst.
       auto.
       eauto using in_cons.
       eauto using in_cons.
Qed.


Lemma subtyping_witness_dec:
  forall CC DD cn dn,
    subtyping_witness CC DD cn dn \/ ~ subtyping_witness CC DD cn dn.
Proof.
  induction CC.
  + intros.
    destruct (JFClassName_dec cn dn).
    ++ subst.
       left.
       auto.
    ++ right.
       sauto.
  + intros.
    destruct a eqn:?.
    destruct (JFClassName_dec cn0 cn); [|right;intro;inversion H; try contradiction].
    subst cn0.
    destruct ex; [|right;intro;inversion H].
    destruct (in_dec JFClassDeclaration_dec a DD).
    ++ eapply in_split_notfirst in i.
        decompose_ex i.
        decompose [and] i; clear i.
        subst DD.
        destruct (find_class l2 j) eqn:?.
        +++ edestruct (IHCC (l1 ++ a :: l2)).
             ++++ left. eapply head_witness.
                  subst a; eauto.
                  subst a; eauto.
                  eauto.
                  eauto.
             ++++ right.
                  intro.
                  inversion H1.
                  subst.
                  eapply not_in_first_eq in H11;eauto.
        +++ right.
            intro.
            inversion H.
            subst.
            eapply not_in_first_eq in H10;eauto.
            destruct H10.
            subst.
            rewrite Heqo in H11;discriminate H11.
        +++ eapply JFClassDeclaration_dec.
    ++ right.
       intro.
       inversion H.
       subst.
       apply n.
       eapply in_or_app.
       right.
       simpl.
       auto.
Qed.


Lemma subtyping_witness_trans:
  forall CC DD CC0 cn dn en,
    subtyping_witness CC DD cn dn ->
    subtyping_witness CC0 DD dn en ->
    subtyping_witness (CC ++ CC0) DD cn en.
Proof.
  induction 1.
  + intros.
    simpl;eauto.
  + intros.
    simpl.
    eapply head_witness;try apply H0;try apply H1;trivial.
    eauto.
Qed.

Lemma subtyping_witness_find_class:
  forall CC DD cn dn,
    subtyping_witness CC DD cn dn ->
    cn <> dn ->
    exists cd, find_class DD dn = Some cd.
Proof.
  induction 1.
  + intros;contradiction.
  + intros.
    destruct (JFClassName_dec cn' dn).
    ++ subst cn'.
       subst.
       eapply find_class_lift_cons in H1.
       decompose_ex H1.
       eapply find_class_lift in H1.
       decompose_ex H1.
       eexists;eauto.
    ++ eapply IHsubtyping_witness;eauto.
Qed.


Lemma subtyping_witness_skip_result:
  forall CC' CC DD CC'' cn cn' dn dn' fields methods,
    subtyping_witness CC DD cn cn' ->
    CC = CC' ++ (JFCDecl dn (Some dn') fields methods) :: CC'' ->
    subtyping_witness CC'' DD dn' cn'.
Proof.
  induction CC'.
  + intros.
    simpl in H0.
    inversion H.
    ++ subst.
       inversion H1.
    ++ subst.
       injection H5;clear H5;intros;subst.
       auto.
  + intros.
    inversion H; subst.
    ++ simpl in H1.
       inversion H1.
    ++ simpl in H5.
       injection H5;clear H5;intros;subst.
       eapply IHCC' in H4;eauto.
Qed.

Lemma subtyping_witness_last_decl:
  forall CC DD cn cn' a CC',
    subtyping_witness CC DD cn cn' ->
    CC = a :: CC' ->
    exists CC'' dn fields methods,
      CC = CC'' ++ [JFCDecl dn (Some cn') fields methods].
Proof.
  induction CC.
  + intros.
    inversion H0.
  + intros.
    inversion H; subst.
    destruct CC.
    ++ inversion H9;subst.
       exists [].
       do 3 eexists.
       simpl;eauto.
    ++ eapply IHCC in H9;auto.
       decompose_ex H9.
       do 4 eexists.
       rewrite H9.
       rewrite app_comm_cons.
       eauto.
Qed.

Lemma subtyping_witness_skip_loop:
  forall CC DD CC' CC'' cn cn' dn fields methods,
    subtyping_witness CC DD cn' dn ->
    CC = CC' ++ (JFCDecl cn (Some cn') fields methods) :: CC'' ->
    subtyping_witness CC'' DD cn' dn.
Proof.
  induction CC''.
  + intros.
    assert (exists j CC'', CC = j :: CC''). {
      destruct CC'.
      ++ simpl in H0.
         eexists;eexists.
         subst;eauto.
      ++ simpl in H0.
         eexists;eexists.
         subst;eauto.
    }
    decompose_ex H1.
    eapply subtyping_witness_last_decl in H;eauto.
    decompose_ex H.
    clear H1.
    subst.
    eapply app_inj_tail in H.
    decompose_and H.
    injection H1;intros;subst.
    eauto.
  + intros.
    inversion H.
    ++ subst.
       destruct CC'.
       +++ simpl in H1.
           inversion H1.
       +++ simpl in H1.
           inversion H1.
    ++ subst.
       destruct CC'.
       +++ simpl in H5.
           injection H5;intros.
           subst.
           auto.
       +++ eapply subtyping_witness_skip_result in H4.
           eauto.
           simpl in H5.
           injection H5;intros.
           eauto.
Qed.

Lemma is_name_in_or_out:
  forall cn CC,
    (exists ex fields' methods', In (JFCDecl cn ex fields' methods') CC) \/
    (forall ex (fields' : list JFFieldDeclaration) (methods' : list JFMethodDeclaration),
        ~ In (JFCDecl cn ex fields' methods') CC).
Proof.
  induction CC.
  * right.
    intros.
    simpl.
    auto.
  * destruct IHCC.
    ** left.
       decompose_ex H.
       do 3 eexists.
       simpl.
       right.
       eauto.
    ** destruct a.
       destruct (JFClassName_dec cn cn0).
       *** subst.
           left.
           do 3 eexists.
           simpl.
           left.
           eauto.
       *** right.
           intros.
           intro.
           eapply H.
           simpl in H0.
           destruct H0;try congruence.
           eauto.
Qed.

Lemma in_exists_last:
  forall CC cn ex fields methods,
    In (JFCDecl cn ex fields methods) CC ->
    exists CC' CC'' ex' fields' methods',
      CC = CC' ++ (JFCDecl cn ex' fields' methods') :: CC'' /\
      forall ex'' fields'' methods'', ~ In (JFCDecl cn ex'' fields'' methods'') CC''.
Proof.
  induction CC.
  + intros.
    inversion H.
  + intros *. destruct (JFClassDeclaration_dec a  (JFCDecl cn ex fields methods)).
    ++ subst a.
       intros.
       pose (is_name_in_or_out cn CC) as H0.
       destruct H0.
       +++ decompose_ex H0.
           eapply IHCC in H0.
           destruct H0.
           decompose_ex H0.
           decompose_and H0.
           do 5 eexists.
           split; try eapply H2.
           rewrite H1.
           rewrite app_comm_cons.
           auto.
       +++  exists [];do 4 eexists.
            split; try eapply H0.
            simpl.
            eauto.
    ++ intro.
       simpl in H.
       destruct H;try congruence.
       eapply IHCC in H.
       decompose_ex H.
       decompose_and H.
       do 5 eexists.
       split; try apply H1.
       subst CC.
       rewrite app_comm_cons.
       auto.
Qed.


Lemma inversion_subtyping_witness:
  forall CC' CC'' DD cn dn fields methods cn' dn',
    subtyping_witness (CC' ++ JFCDecl cn (Some dn) fields methods :: CC'') DD cn' dn' ->
    exists DD' DD'' cd,
      DD = DD' ++ JFCDecl cn (Some dn) fields methods :: DD'' /\
      ~ In (JFCDecl cn (Some dn) fields methods) DD' /\
      find_class DD'' dn = Some cd.
Proof.
  induction CC'.
  + intros.
    simpl in *.
    inversion H.
    subst.
    eexists;eauto.
  + intros.
    simpl in H.
    inversion H.
    subst.
    eapply IHCC' in H8.
    decompose_ex H8.
    decompose_and H8.
    eexists;eauto.
Qed.

Lemma subtyping_witness_loop_exit:
  forall n CC,
    length CC <= n ->
    forall  DD cn dn,
      length CC > 0 ->
    subtyping_witness CC DD cn dn ->
    exists CC' CC'' cn' fields methods, subtyping_witness (JFCDecl cn (Some cn') fields methods :: CC') DD cn dn /\
                                        CC = CC'' ++ JFCDecl cn (Some cn') fields methods :: CC' /\
                                        forall cn'' fields' methods', ~ In (JFCDecl cn (Some cn'') fields' methods') CC'.
Proof.
  induction n.
  + intros.
    eapply le_n_0_eq in H.
    symmetry in H.
    eapply length_zero_iff_nil in H.
    subst.
    auto with zarith.
    simpl in H0.
    eapply gt_irrefl in H0.
    contradiction.
  + intros.
    destruct CC.
    ++ intros.
       inversion H0;subst;contradiction.
    ++ pose (is_name_in_or_out cn CC) as H2.
       destruct H2.
       +++ decompose_ex H2. (* exists cn in CC *)
           generalize H1;intros.
           eapply subtyping_witness_only_some in H3;simpl;eauto.
           decompose_ex H3.
           subst ex.
           generalize H2;intros.
           eapply in_exists_last in H3.
           decompose_ex H3.
           decompose_and H3. (* we've found the last occurrence of cn in CC *)
           generalize H1;intros.
           subst CC.
           assert (In (JFCDecl cn ex' fields'0 methods'0) (j :: CC' ++ JFCDecl cn ex' fields'0 methods'0 :: CC'')). {
             rewrite app_comm_cons.
             eapply in_or_app.
             right.
             simpl.
             left;trivial.
           }
           eapply subtyping_witness_only_some in H3; try apply H4.
           decompose_ex H3.
           subst ex'.
           generalize H1;intros.
           eapply subtyping_witness_skip_result in H3; try (subst; rewrite app_comm_cons;trivial).
           do 5 eexists.
           split;[|split];eauto.
           rewrite app_comm_cons in H1.
           eapply inversion_subtyping_witness in H1.
           decompose_ex H1.
           decompose_and H1.           
           eapply head_witness;eauto.
       +++ generalize H1;intros.
           inversion H3.
           subst.
           exists CC, [].
           do 3 eexists.
           eauto.
Qed.

Lemma subtyping_witness_find_class_first:
  forall CC DD cn dn,
    subtyping_witness CC DD cn dn ->
    cn <> dn ->
    exists cd, find_class DD cn = Some cd.
Proof.
  induction 1.
  + intros;contradiction.
  + intros.
    subst DD.
    eapply find_class_lift.
    eapply find_class_eq.
Qed.


Lemma new_is_in:
  forall CC DD cn dn cd cn0 ex fields methods,
  (forall CC' : JFProgram, ~ subtyping_witness CC' DD cn dn) ->
  subtyping_witness (cd :: CC) (JFCDecl cn0 ex fields methods :: DD) cn dn ->
  exists CC0 CC1,
    cd :: CC = CC0 ++ (JFCDecl cn0 ex fields methods) :: CC1.
Proof.
  induction CC.
  + intros.
    inversion H0;subst.
    inversion H9;subst.
    destruct DD'.
    ++ simpl in H3.
       injection H3;intros;subst.
       exists [], [];simpl;eauto.
    ++ simpl in H3.
       injection H3;intros.
       eapply head_witness in H1;eauto.
       +++ eapply H in H1.
           contradiction.
       +++ intro.
           eapply H4.
           simpl.
           eauto.
  + intros.
    inversion H0.
    subst.
    destruct DD'.
    ++ injection H3;intros;subst.
       exists [].
       eexists.
       simpl.
       eauto.
    ++ eapply IHCC in H9.
       +++ decompose_ex H9.
           do 2 eexists;rewrite H9.
           rewrite app_comm_cons.
           eauto.
       +++ intros.
           intro.
           eapply H.
           simpl in H3.
           injection H3;intros.
           subst DD.
           eapply head_witness in H1;trivial;try apply H5; try apply H1;simpl in H4;eauto.
Qed.

Lemma subtyping_witness_following_decl:
  forall CC CC' DD cn dn fields methods j2 cn' dn',
    subtyping_witness (CC ++ JFCDecl cn (Some dn) fields methods :: j2 :: CC') DD cn' dn' ->
    exists ex fields' methods', j2 = JFCDecl dn ex fields' methods'.
Proof.
  induction CC.
  + intros.
    simpl in H.
    inversion H.
    subst.
    inversion H11.
    subst.
    do 3 eexists; eauto.
  + intros.
    inversion H.
    subst.
    eapply IHCC in H8.
    decompose_ex H8.
    subst.
    do 3 eexists; eauto.
Qed.

Lemma subtyping_witness_incl:
  forall CC DD cn dn,
    subtyping_witness CC DD cn dn ->
    incl CC DD.
Proof.
  induction CC.
  + intros.
    unfold incl.
    intros.
    inversion H0.
  + intros.
    inversion H.
    subst.
    eapply IHCC in H8.
    unfold incl in *.
    intros.
    simpl in H0.
    destruct H0.
    ++ subst.
       eapply in_or_app.
       right;simpl;auto.
    ++ eauto.
Qed.

Lemma subtyping_witness_subtyping_witness_beginning:
  forall CC cn dn fields methods CC' DD cn' dn',
    subtyping_witness (CC ++ JFCDecl cn (Some dn) fields methods :: CC') DD cn' dn' ->
    subtyping_witness CC DD cn' cn.
Proof.
  induction CC.
  + intros.
    simpl in H.
    inversion H.
    subst.
    eauto.
  + intros.
    inversion H.
    subst.
    eapply IHCC in H8.
    decompose_ex H8.
    eapply head_witness in H8;eauto.
Qed.

Lemma subtyping_witness_narrowing:
  forall CC dn ex fields methods CC' DD cn,
    subtyping_witness (CC ++ JFCDecl dn ex fields methods :: CC') (JFCDecl dn ex fields methods :: DD) cn dn ->
    cn <> dn ->
    ~ In (JFCDecl dn ex fields methods) CC ->
    incl CC DD ->
    exists CC'', subtyping_witness CC'' DD cn dn.
Proof.
  induction CC.
  * intros.
    simpl in H.
    inversion H.
    subst.
    contradiction.
  * intros.
    inversion H.
    subst.
    destruct (JFClassName_dec cn' dn).
    ** subst.
       destruct DD'.
       *** simpl in H5.
           injection H5;intros;subst.
           exists [];eauto.
       *** exists [JFCDecl cn (Some dn) fields0 methods0].
           simpl in H5.
           injection H5;intros.
           eapply head_witness;try eapply H3;eauto.
           intro.
           apply H6.
           simpl;eauto.
    ** destruct DD'.
       *** simpl in H5.
           injection H5;intros;subst.
           contradiction.
       *** eapply IHCC in H11;eauto.
           **** decompose_ex H11.
                simpl in H5.
                injection H5;intros.
                eapply head_witness in H11; try eapply H7; try eapply H3.
                eexists;eapply H11.
                intro;apply H6;right;auto.
           **** intro;apply H1;right;auto.
           **** unfold incl in *.
                intros.
                apply H2.
                simpl. auto.
Qed.

Lemma incl_app_left:
  forall A, forall (CC:list A) DD EE,
    incl (CC ++ DD) EE ->
    incl CC EE.
Proof.
  induction CC.
  + intros.
    unfold incl.
    intros. inversion H0.
  + intros.
    simpl in H.
    eapply incl_cons.
    ++ unfold incl in H.
       eapply H.
       simpl.
       eauto.
    ++ unfold incl in *.
       intros.
       eapply H.
       eauto using in_cons, in_or_app.
Qed.
       
Lemma subtyping_witness_strong_dec:
  forall DD cn dn,
    (exists CC,subtyping_witness CC DD cn dn) \/ (forall CC,~ subtyping_witness CC DD cn dn).
Proof.
  induction DD.
  + intros.
    destruct (JFClassName_dec cn dn).
    ++ subst.
       left.
       eexists.
       auto.
    ++ right.
       intro. intro.
       inversion H.
       +++ subst.
           contradiction.
       +++ subst. 
           eapply f_equal in H0.
           rewrite app_length in H0.
           simpl in H0.
           rewrite Nat.add_succ_r in H0.
           congruence.
  + intros.
    pose (IHDD cn dn) as IHDDcndn.
    destruct IHDDcndn.
    ++ decompose_ex H.
       left.
       exists CC.
       rewrite <- (app_nil_l (a :: DD)).
       eauto using subtyping_witness_monotone.
    ++ destruct a.
       destruct ex.
       +++ pose (IHDD cn cn0) as IHDDcncn0.
           destruct IHDDcncn0.
           ++++ pose (IHDD j dn) as IHDDjdn.
                destruct IHDDjdn.
                * decompose_ex H0.
                  decompose_ex H1.
                  destruct (find_class DD j) eqn:?.
                  ** left.
                     eapply (subtyping_witness_monotone CC [] DD) in H0.
                     eapply (subtyping_witness_monotone CC0 [] DD) in H1.
                     eapply head_witness in H1;try apply Heqo;trivial;auto.
                     simpl in *.
                     eapply (subtyping_witness_trans CC (JFCDecl cn0 (Some j) fields methods :: DD) (JFCDecl cn0 (Some j) fields methods :: CC0)) in H0;
                       [|apply H1].
                     eexists;eauto.
                  ** right.
                     intros.
                     intro.
                     destruct (JFClassName_dec cn dn);[subst;eapply H;eauto|].
                     generalize H2;intros.
                     eapply subtyping_witness_find_class in H2;eauto.
                     decompose_ex H2.
                     destruct (JFClassName_dec dn cn0).
                     *** subst. eauto.
                         eapply H;eauto.
                     *** eapply find_class_further_neq in H2;eauto.
                         destruct (JFClassName_dec j dn).
                         **** subst j.
                              rewrite H2 in *.
                              inversion  Heqo.
                         **** eapply subtyping_witness_find_class_first in H1;eauto.
                              decompose_ex H1.
                              rewrite H1 in *.
                              inversion Heqo.
                * right.
                  intro.
                  intro.
                  destruct CC.
                  ** inversion H2;subst.
                     eapply H.
                     eauto.
                  ** generalize H2;intro.
                     eapply new_is_in in H2;eauto.
                     decompose_ex H2.
                     rewrite H2 in *.
                     eapply subtyping_witness_skip_result in H3;eauto.
                     generalize H3;intro.
                     destruct CC1.
                     *** inversion H4;subst.
                         eapply H1.
                         eauto.
                     *** destruct (JFClassName_dec j dn);try (subst;eapply H1;eauto).
                         eapply subtyping_witness_loop_exit in H4;simpl; eauto with zarith.
                         decompose_ex H4.
                         decompose_and H4.
                         generalize H5;intros.
                         eapply new_is_in in H5;eauto.
                         decompose_ex H5.
                         rewrite H5 in H4.
                         destruct CC3.
                         **** assert (exists a CC, CC2 ++ [JFCDecl cn0 (Some j) fields methods] = a :: CC) by
                               (destruct CC2; simpl; do 2 eexists; eauto).
                              decompose_ex H6.
                              eapply subtyping_witness_last_decl in H4;eauto.
                              decompose_ex H4.
                              eapply app_inj_tail in H4.
                              decompose_and H4.
                              injection H10;intros;contradiction.
                         **** generalize H4;intros.
                              eapply subtyping_witness_following_decl in H6;eauto.
                              decompose_ex H6.
                              subst.
                              assert (forall (cn'' : JFClassName) (fields0' : list JFFieldDeclaration) (methods0' : list JFMethodDeclaration),
                                         ~ In (JFCDecl j (Some cn'') fields0' methods0') (JFCDecl j ex fields' methods' :: CC3)). {
                                destruct CC2.
                                + simpl in H5. injection H5;intros.
                                  intro.
                                  eapply H8.
                                  rewrite H6.
                                  apply H13.
                                + simpl in H5.   injection H5;intros.
                                  intro.
                                  eapply H8.
                                  rewrite H6.
                                  eapply in_or_app.
                                  right.
                                  simpl.
                                  eauto.
                              }
                              assert (In (JFCDecl j ex fields' methods') (CC2 ++ JFCDecl cn0 (Some j) fields methods :: JFCDecl j ex fields' methods' :: CC3))
                                by (eapply in_app_iff;simpl; eauto).
                              eapply subtyping_witness_only_some in H4; try eapply H9.
                              decompose_ex H4.
                              subst.
                              pose (H6 dn0 fields' methods') as dead.
                              simpl in dead.
                              assert False.
                              apply dead. left;trivial.
                              contradiction.
                         ++++ right.
                              intros.
                              intro.
                              generalize H1;intros.
                              destruct CC; [inversion H1;subst; eapply H; auto|].
                              eapply new_is_in in H2;eauto.
                              decompose_ex H2.
                              rewrite H2 in H1.
                              eapply subtyping_witness_subtyping_witness_beginning in H1.
                              generalize H1;intros.
                              destruct CC0;[inversion H3;subst;eapply H0;eauto|].
                              generalize H3;intros.
                              eapply new_is_in in H3;eauto.
                              decompose_ex H3.
                              assert (In (JFCDecl cn0 (Some j) fields methods) (j1 :: CC0))
                                by (rewrite H3; eapply in_app_iff; simpl; eauto).
                              eapply in_split_notfirst in H5;try apply JFClassDeclaration_dec.
                              decompose_ex H5.
                              decompose_and H5.
                              rewrite H6 in H1.
                              destruct (JFClassName_dec cn cn0); [subst;eapply H0;eauto|].
                              eapply subtyping_witness_narrowing in H1;eauto.
                              decompose_ex H1.
                              eapply H0;eauto.
                              eapply subtyping_witness_incl in H1.
                              eapply incl_app_left in H1.
                              unfold incl.
                              intros.
                              unfold incl in H1.
                              simpl in H1.
                              generalize H5;intros.
                              eapply H1 in H5.
                              destruct H5.
                              * subst a.
                                contradiction.
                              * auto.
                     +++ right.
                         intros.
                         intro.
                         destruct CC.
                         ++++ inversion H0.
                              subst.
                              eapply H.
                              eauto.
                         ++++ generalize H0;intros.
                              eapply new_is_in in H0;eauto.
                              decompose_ex H0.
                              assert (In (JFCDecl cn0 None fields methods) (j::CC))
                                by (rewrite H0; eapply in_app_iff; simpl;eauto).
                              eapply subtyping_witness_only_some in H1; try apply H2.
                              decompose_ex H1;inversion H1.
                              Unshelve.
                              eapply [].
Qed.

Lemma subtyping_witness_subtyping:
  forall CC DD cn dn,
    subtyping_witness CC DD cn dn -> subtyping DD (JFClass cn) (JFClass dn).
Proof.
  induction 1.
  + auto.
  + eapply substep.
    trivial.
    Focus 2.
    subst DD.
    eapply base_deep;eauto.
    trivial.
    subst DD.
    eauto using subtyping_further_deep.
Qed.




Lemma extends_notfirst_find_class:
  forall CC cn dn,
    extends CC cn dn ->
    exists CC' CC'' flds mthds dd,
      CC = CC' ++ (JFCDecl cn (Some dn) flds mthds) :: CC'' /\
      ~ In (JFCDecl cn (Some dn) flds mthds) CC' /\
      find_class CC'' dn = Some dd.
Proof.
  induction 1.
  + intros.
    eapply in_find_class_raw in H.
    decompose_ex H.
    exists [].
    do 4 eexists.
    simpl.
    split;eauto.
  + decompose_ex IHextends.
    decompose_and IHextends.
    destruct CC'.
    ++ simpl in *.
       subst.
       destruct (JFClassDeclaration_dec (JFCDecl cn1 dn1 fields methods) (JFCDecl cn2 (Some dn2) flds mthds)).
       +++ injection e;intros;clear e.
           subst.
           exists  [].
           eapply find_class_lift_cons in H3.
           decompose_ex H3.
           do 4 eexists.
           simpl.
           split.
           trivial.
           split.
           trivial.
           eapply H3.
       +++ exists [JFCDecl cn1 dn1 fields methods].
           do 4 eexists.
           simpl.
           split.
           trivial.
           split.
           tauto.
           eapply H3.
    ++ destruct (JFClassDeclaration_dec (JFCDecl cn1 dn1 fields methods) (JFCDecl cn2 (Some dn2) flds mthds)).
       +++ injection e;intros;clear e.
           subst.
           exists  [].
           eapply find_class_lift_cons in H3.
           decompose_ex H3.
           eapply find_class_lift in H3.
           decompose_ex H3.
           do 4 eexists.
           simpl.
           split.
           trivial.
           split.
           tauto.
           rewrite app_comm_cons.
           eapply H3.
       +++ subst CC.
           exists (JFCDecl cn1 dn1 fields methods :: (j :: CC')).
           exists CC''.
           do 3 eexists.
           split.
           simpl.
           trivial.
           split.
           intro.
           apply H2.
           simpl in H0.
           destruct H0;try contradiction.
           eauto.
Qed.  


Lemma subtyping_subtyping_witness:
  forall DD,
    forall  cid did,
      subtyping DD cid did ->
       forall cn dn,
    cid = (JFClass cn) ->
    did = (JFClass dn) ->
    cid <> did ->
    did <> JFObject -> exists CC, subtyping_witness CC DD cn dn.
Proof.
  induction 1.
  + intros; contradiction.
  + intros; contradiction.
  + intros; congruence.
  + intros.
    subst.
    injection H3; clear H3;intros;subst.
    destruct (JFClassName_dec dn dn0).
    ++ subst.
       generalize H1;intros.
       eapply extends_notfirst_find_class in H1.
       decompose_ex H1.
       decompose_and H1.
       eexists.
       eapply head_witness;eauto using JFClassDeclaration_dec.
    ++ assert (JFClass dn <> JFClass dn0) by congruence.
       eapply IHsubtyping in H ; trivial;try congruence.
       decompose_ex H.
       generalize H1;intros.
       eapply extends_notfirst_find_class in H1.
       decompose_ex H1.
       decompose_and H1.
       eexists.
       eapply head_witness.
       apply H3.
       apply H7.
       apply H8.
       apply H.
Qed.

Lemma subtyping_dec:
  forall CC C D,
    subtyping CC C D \/ ~ subtyping CC C D.
Proof.
  intros *.
  destruct C; eauto.
  destruct D; [|right;intro;eapply subtyping_not_bot in H;inversion H;auto].
  pose (subtyping_witness_strong_dec CC cn cn0) as Sdec.
  destruct Sdec.
  * decompose_ex H.
    left.
    eauto using subtyping_witness_subtyping.
  * destruct (JFClassName_dec cn cn0).
    ** subst; left; eauto.
    ** destruct (JFClassName_dec cn0 JFObjectName).
       *** subst; left; eauto.
       *** right.
           intro.
           eapply subtyping_subtyping_witness in H0;eauto;try congruence.
           **** decompose_ex H0.
                eapply H;eauto.
           **** unfold JFObject;congruence.
Qed.


Lemma subtyping_find_class:
  forall CC C D cn,
    C <> D -> 
    D <> JFObject ->
    JFClass cn = C ->
    names_unique CC ->
    subtyping CC C D ->
    exists cd, find_class CC cn = Some cd.
Proof.
  intros.
  inversion H3.
  + intuition.
  + congruence.
  + congruence.
  + assert (exists
               (ex0 : JFClassName) (fields' : list JFFieldDeclaration) 
               (methods' : list JFMethodDeclaration),
               In (JFCDecl cn0 (Some ex0) fields' methods') CC)
      by eauto 3 using  extends_in_first.
    destruct H10, H10, H10.
    assert (cn0=cn) by congruence.
    subst cn0.
    exists (JFCDecl cn (Some x) x0 x1).
    eauto 2.
Qed.

    
    
Lemma subtyping_find_class_gt:
  forall CC C D dn,
    C <> D ->
    C <> JFBotClass ->
    JFClass dn = D ->
    names_unique CC ->
    subtype_well_founded CC ->
    program_contains CC JFObjectName = true ->
    subtyping CC C D ->
    exists dd, find_class CC dn = Some dd.
Proof.
  induction CC.
  + intros.
    simpl in H4.
    discriminate H4.
  + intros C D dn CDneq CJFB DidD Nuq Swf PctsObj Sub.
    inversion Sub.
    ++ contradiction.
    ++ subst.
       injection H0;intros.
       subst.
       apply program_contains_find_class;auto.
    ++ subst. contradiction.
    ++ subst.
       destruct a.
       unfold find_class.
       destruct (JFClassName_dec cn0 dn).
       +++ eexists;eauto.
       +++ fold (find_class CC dn).
           assert (exists
                      (ex0 : option JFClassName)
                      (fields' : list JFFieldDeclaration) 
                      (methods' : list JFMethodDeclaration),
                      In (JFCDecl dn0 ex0 fields' methods') CC)
             by eauto using extends_in_second_second.
           do 3 destruct H.
           destruct (JFClassName_dec cn0 cn).
           * subst.
             destruct (JFClassName_dec cn dn0).
             ** subst.
                assert (JFClass dn0 <> JFClass dn0).
                eapply extends_neq;eauto.
                contradiction.
             ** assert (JFClass cn <> JFClass dn) by congruence.
                destruct (JFClassName_dec dn0 dn).
                *** subst; eauto.
                *** assert (subtyping CC (JFClass dn0) (JFClass dn)) by
                      (eapply subtyping_further_neq ;
                       try apply H2;eauto 2; congruence).
                    eapply IHCC;
                      try apply H3; try apply CDneq;
                        try apply CJFB;try congruence;eauto 2.
                    {
                      destruct CC.
                      * inversion H.
                      * eauto using subtype_well_founded_program_contains_further.
                    }
           * subst.
             assert (JFClass dn <> JFClass cn0) by congruence.
             destruct (JFClassName_dec dn0 dn).
             ** subst; eauto.
             ** assert (JFClass dn0 <> JFClass dn) by congruence.
                eapply IHCC; try eapply H4; eauto 2.
                *** discriminate.
                *** destruct CC.
                    **** inversion H.
                    **** eauto using subtype_well_founded_program_contains_further.
                *** eapply subtyping_further_neq; eauto.
                    eapply extends_neq;eauto.
Qed.

Lemma subtyping_neq_object:
  forall CC dn D,
    object_is_not_extended CC ->
    (JFClass dn) <> D  ->
    subtyping CC (JFClass dn) D ->
    JFClass dn <> JFObject.
Proof.
  intros.
  inversion H1.
  + tauto.
  + congruence.
  + injection.
    eapply object_is_not_extended_extends_neq.
    eauto.
    assert (dn=cn) by congruence.
    rewrite H9 in *.
    eauto.
Qed.

             
Hint Resolve subtyping_further object_is_not_subtype subtrans subtyping_further_neq subtyping_find_class.

  
Lemma subtyping_object_supremum:
  forall CC C,
    names_unique CC ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
      subtype_well_founded CC ->
    subtyping CC JFObject C ->
    C = JFObject.
Proof.
  induction CC.
  * intros.
    inversion H3.
    ** auto.
    ** auto.
    ** subst.
       inversion H6.
  * intros.
    apply IHCC;eauto 2.
    destruct a.
    destruct (JFCId_dec (JFClass cn) JFObject).
    assert (C = JFObject).
    eapply object_is_not_subtype;
      try apply H;eauto.
    rewrite H4.
    apply subrefl.
    eauto 2.
Qed.

Hint Resolve  subtyping_neq_object subtyping_object_supremum.



(**
   Effective version of the subtyping that returns booleans
   instead predicting the property. The function is correct
   only when the program is well formed.
*)
Fixpoint subtype_class_bool (CC:JFProgram) (cn dn: JFClassName) : bool :=
  if JFClassName_dec cn dn
  then true
  else if JFClassName_dec dn JFObjectName
       then true
       else
         match CC with
           | [] => false
           | JFCDecl cn' (Some dn') _ _ :: CC' =>
             if JFClassName_dec cn cn'
             then if JFClassName_dec dn' dn
                  then true
                  else subtype_class_bool CC' dn' dn
             else subtype_class_bool CC' cn dn
           | JFCDecl cn' None _ _ :: CC' =>
             if JFClassName_dec cn cn'
             then false
             else subtype_class_bool CC' cn dn
         end.



Lemma subtype_class_bool_simple:
  forall CC cn dn fields methods,
    subtype_class_bool (JFCDecl cn (Some dn) fields methods :: CC) cn dn = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct (JFClassName_dec cn dn).
  * auto.
  * destruct (JFClassName_dec dn JFObjectName); try auto.
    destruct (JFClassName_dec cn cn); try contradiction.
    destruct (JFClassName_dec dn dn); try contradiction.
    auto.
Qed.

Lemma subtype_class_bool_same:
  forall CC cn,
    subtype_class_bool CC cn cn = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct CC;destruct (JFClassName_dec cn cn); auto.
Qed.

Lemma subtype_class_bool_object:
  forall CC cn,
    subtype_class_bool CC cn JFObjectName = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct CC;destruct (JFClassName_dec cn JFObjectName); auto.
Qed.

Hint Resolve subtype_class_bool_same subtype_class_bool_object.

Lemma subtype_class_bool_direct_extends:
  forall CC cn dn flds mthds,
    subtype_class_bool (JFCDecl cn (Some dn) flds mthds :: CC) cn dn = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct (JFClassName_dec cn dn); try subst cn; auto.
  destruct (JFClassName_dec dn JFObjectName); try subst dn; auto.
  destruct (JFClassName_dec cn cn); try tauto.
  destruct (JFClassName_dec dn dn); try tauto.
Qed.

Hint Resolve subtype_class_bool_direct_extends.


Lemma subtype_class_bool_eq:
  forall CC cn cn' dn' flds mthds,
  subtype_class_bool CC cn' dn' = true ->
  subtype_class_bool (JFCDecl cn (Some cn') flds mthds :: CC) cn dn'=true.
Proof.
  destruct CC.
  * unfold subtype_class_bool.
    intros.
    destruct (JFClassName_dec cn dn'); auto.
    destruct (JFClassName_dec dn' JFObjectName); auto.
    destruct (JFClassName_dec cn cn); auto.
    destruct (JFClassName_dec cn' dn'); auto.
  * intros.
    unfold subtype_class_bool.
    unfold subtype_class_bool in H.
    destruct (JFClassName_dec cn dn'); try subst cn; auto.
    destruct (JFClassName_dec dn' JFObjectName); try subst dn'; auto.
    destruct (JFClassName_dec cn cn); try tauto.
    destruct (JFClassName_dec cn' dn'); try auto.
Qed.


Hint Resolve subtype_class_bool_eq.


Lemma subtype_class_bool_neq:
  forall CC cn dn en ex flds mthds,
    subtype_class_bool CC cn dn = true ->
    cn<>en ->
    subtype_class_bool (JFCDecl en ex flds mthds :: CC) cn dn = true.
Proof.
  destruct CC.
  - intros.
    simpl in H.
    simpl.
    destruct (JFClassName_dec cn dn); eauto 2.
    destruct (JFClassName_dec dn JFObjectName); eauto 2.
    discriminate H.
  - intros.
    destruct (JFClassName_dec cn dn); try rewrite e; eauto 2. 
    destruct (JFClassName_dec dn JFObjectName); try rewrite e; eauto 2.
    destruct ex.
    + unfold subtype_class_bool.
      unfold subtype_class_bool in H.
      destruct (JFClassName_dec cn dn); try rewrite e; eauto 2.
      destruct (JFClassName_dec dn JFObjectName); try rewrite e; eauto 2.
      destruct (JFClassName_dec cn en); eauto 3.
    + unfold subtype_class_bool.
      unfold subtype_class_bool in H.
      destruct (JFClassName_dec cn dn); try rewrite e; eauto 2.
      destruct (JFClassName_dec dn JFObjectName); try rewrite e; eauto 2.
      destruct (JFClassName_dec cn en); eauto 3.
Qed.

Lemma subtype_class_bool_object_left:
  forall CC cn,
    subtype_well_founded CC ->
    names_unique CC ->
    subtype_class_bool CC JFObjectName cn = true ->
    cn = JFObjectName.
Proof.
  induction CC.
  + intros cn Swf Nuq H0.
    unfold subtype_class_bool in H0.
    destruct (JFClassName_dec JFObjectName cn);
      destruct (JFClassName_dec cn JFObjectName); auto.
    try discriminate H0.
  + intros cn Swf Nuq H0.
    generalize H0;intros.
    unfold subtype_class_bool in H0.
    fold subtype_class_bool in H0.
    destruct (JFClassName_dec JFObjectName cn);
      destruct (JFClassName_dec cn JFObjectName); auto.
    destruct a;destruct ex.
    ++ destruct (JFClassName_dec JFObjectName cn0).
       +++ subst.
           unfold subtype_well_founded in Swf.
           pose find_class_eq.
           apply Swf in e.
           decompose_ex e.
           eapply number_of_extends_decompose in e.
           destruct e.
           eapply number_of_extends_object in H.
           eapply program_contains_find_class in H.
           decompose_ex H.
           destruct cd.
           generalize H;intros.
           eapply find_class_eq_name in H3;subst.
           eapply find_class_in in H.
           eapply names_unique_in_neq in Nuq;eauto.
           contradiction.
       +++ eapply IHCC in H0;eauto.
    ++ destruct (JFClassName_dec JFObjectName cn0); try discriminate H0.
       eapply IHCC in H0;eauto.
Qed.
    

Hint Resolve subtype_class_bool_neq.




Lemma extends_subtype_bool_complete:
  forall CC cn dn,
    names_unique CC ->
    program_contains CC JFObjectName = true ->
    object_is_not_extended CC ->
    subtype_well_founded CC ->
    JFClass cn <> JFObject ->
    extends CC cn dn ->
    subtype_class_bool CC cn dn = true.
Proof.
  induction CC.
  - intros.
    inversion H4.
  - intros. inversion H4.
    + eauto. 
    + assert (  exists
                 (ex0 : JFClassName) (fields' : list JFFieldDeclaration) 
                 (methods' : list JFMethodDeclaration),
                 In (JFCDecl cn (Some ex0) fields' methods') CC) by eauto using extends_in_first.
      decompose_ex H10.
      subst.
      assert (cn1<>cn) by eauto 2 with myhints.
      eapply subtype_class_bool_neq.
      eapply IHCC; eauto 3.
      eapply subtype_well_founded_contains_object;eauto 3.
      auto.
Qed.

Lemma decompose_subtype_class_bool:
  forall CC cn dn en xn fields methods,
    (cn = en -> subtype_class_bool CC xn dn = true) ->
    (cn <> en -> subtype_class_bool CC cn dn = true) ->
    subtype_class_bool (JFCDecl en (Some xn) fields methods :: CC) cn dn = true.
Proof.
  intros.
  simpl.
  destruct (JFClassName_dec cn dn); eauto 2.
  destruct (JFClassName_dec dn JFObjectName); eauto 2.
  destruct (JFClassName_dec cn en).
  - destruct (JFClassName_dec xn dn).
    * auto.
    * auto.
  - apply H0.
    auto.
Qed.

Lemma decompose_subtype_class_bool_none:
  forall CC cn dn en fields methods,
    cn <> en ->
    subtype_class_bool CC cn dn = true ->
    subtype_class_bool (JFCDecl en None fields methods :: CC) cn dn = true.
Proof.
  intros.
  simpl.
  destruct (JFClassName_dec cn dn); eauto 2.
  destruct (JFClassName_dec dn JFObjectName); eauto 2.
  destruct (JFClassName_dec cn en).
  + congruence.
  + auto.
Qed.


Lemma subtype_class_bool_find_class:
  forall cn dn,
    cn <> dn ->
    dn <> JFObjectName ->
    forall CC,
    subtype_class_bool CC cn dn = true ->
    exists cd, find_class CC cn = Some cd.
Proof.
  induction CC;intros.
  + simpl in H1.
    destruct (JFClassName_dec cn dn).
    congruence.
    destruct (JFClassName_dec dn JFObjectName).
    congruence.
    discriminate H1.
  + destruct a.
    destruct (JFClassName_dec cn0 cn).
    * subst cn0.
      exists (JFCDecl cn ex fields methods).
      eapply find_class_eq.
    * unfold subtype_class_bool in H1.
      destruct (JFClassName_dec cn dn).
      - subst dn.
        tauto.
      - destruct (JFClassName_dec dn JFObjectName).
        { subst dn.
          lapply IHCC; intros.
          destruct H2.
          exists x.
          eapply find_class_same; eauto.
          eauto.
        }
        { destruct ex.
          + destruct (JFClassName_dec cn cn0).
            * congruence.
            * lapply IHCC; eauto.
              intros.
              destruct H2.
              exists x.
              clear H1.
              eauto using find_class_same.
          + fold (subtype_class_bool CC cn dn) in H1.
            lapply IHCC; eauto 2; intros.
            ++ destruct H2.
               exists x.
               clear H1.
               eauto using find_class_same.
            ++ destruct (JFClassName_dec cn cn0); eauto.
        }
Qed.




Lemma subtype_class_bool_find_class_second:
  forall CC cn dn,
    cn <> dn ->
    dn <> JFObjectName ->
    subtype_well_founded CC ->
    names_unique CC ->
    subtype_class_bool CC cn dn = true ->
    exists dd, find_class CC dn = Some dd.
Proof.
  induction CC.
  + scrush.
  + intros Cn Dn CnDn DnObj Swf Nuq Scb.
    destruct a.
    destruct (JFClassName_dec Cn Dn); try contradiction.
    generalize Swf;intros.
    simpl in Scb.
    destr_discr Scb; try contradiction.
    destr_discr Scb; try contradiction.
    destruct ex.
    destruct (JFClassName_dec Cn cn).
    ++ subst.
       destruct (JFClassName_dec j Dn).
       +++ subst.
           eapply subtype_get_superclass in Swf0;eauto 2;
             try eapply find_class_eq.
       +++ generalize Scb;intros.
           eapply IHCC in Scb0;eauto 2.
           sauto.
    ++ eapply IHCC in Scb;eauto 2.
       sauto.
    ++ destruct (JFClassName_dec Cn cn);try congruence.
       eapply IHCC in Scb;eauto 2.
       sauto.
Qed.

Lemma subtype_class_bool_refl:
  forall CC cn dn,
    subtype_well_founded CC ->
    names_unique CC ->
    subtype_class_bool CC cn dn = true ->
    subtype_class_bool CC dn cn = true ->
    cn = dn.
Proof.
  induction CC.
  + intros Cn Dn Swf Nuq H H0.
    simpl in H.
    simpl in H0.
    destruct (JFClassName_dec Cn Dn);
      destruct (JFClassName_dec Dn Cn); try contradiction; auto 2.
    destruct (JFClassName_dec Dn JFObjectName);
      destruct (JFClassName_dec Cn JFObjectName); subst; try contradiction;
        try discriminate H0; try discriminate H.
  + intros  Cn Dn Swf Nuq H H0.
    generalize H;
      generalize H0;intros.
    simpl in H.
    simpl in H0.
    destruct (JFClassName_dec Cn Dn);
      destruct (JFClassName_dec Dn Cn); try contradiction; auto 2.
    destruct (JFClassName_dec Dn JFObjectName);
      destruct (JFClassName_dec Cn JFObjectName); subst; try contradiction;
        try discriminate H0; try discriminate H.
    ++ eapply subtype_class_bool_object_left in H1;eauto 2.
    ++ eapply subtype_class_bool_object_left in H2;eauto 2.
    ++ destruct a; destruct ex.
       +++ destruct (JFClassName_dec Cn cn);
             destruct (JFClassName_dec Dn cn);subst;try contradiction.
           ++++ eapply subtype_class_bool_find_class_second in H0;eauto 2.
                destruct H0.
                destruct x.
                generalize H0;intros.
                eapply find_class_eq_name in H3;subst.
                eapply find_class_in in H0;auto 2.
                eapply names_unique_in_neq in Nuq;eauto 2;contradiction.
           ++++ eapply subtype_class_bool_find_class_second in H;eauto 2.
                destruct H.
                destruct x.
                generalize H;intros.
                eapply find_class_eq_name in H3;subst.
                eapply find_class_in in H;auto 2.
                eapply names_unique_in_neq in Nuq;eauto 2;contradiction.
           ++++ eapply IHCC in H0;eauto 2.
       +++ destruct (JFClassName_dec Cn cn); try discriminate H.
           destruct (JFClassName_dec Dn cn); try discriminate H0.
           eapply IHCC in H0;eauto 2.
Qed.


Lemma subtype_class_bool_subtyping:
  forall CC cn dn,
    names_unique CC ->
    subtype_well_founded CC ->
    subtype_class_bool CC cn dn = true ->
    subtyping CC (JFClass cn) (JFClass dn).
Proof.
  induction CC.
  + intros.
    sauto.
  + intros cn dn.
    intros Nuq Swf Scb.
    simpl in Scb.
    repeat destr_discr Scb;auto.
    ++ sauto.
    ++ sauto.
    ++ subst.
       eapply substep;eauto 1.
       unfold subtype_well_founded in Swf.
       pose find_class_eq as FclsD.
       apply Swf in FclsD.
       decompose_ex FclsD.
       simpl in FclsD.
       destruct (JFClassName_dec cn0 cn0); try contradiction.
       destruct (number_of_extends CC dn) eqn:?.
       +++ eapply number_of_extends_find_class_simple in Heqo.
           decompose_ex Heqo.
           destruct x.
           eapply find_class_in in Heqo;eauto.
           eapply base;eauto.
       +++ inversion FclsD.
    ++ subst.
       generalize Swf;intros.
       eapply subtype_well_founded_neq in Swf0;eauto.
       destruct (JFClassName_dec JFObjectName dn).
       +++ subst; eauto.
       +++ generalize Scb;intros.
           eapply IHCC in Scb0;eauto 2.
           generalize Scb0;intros.
           eapply subtyping_further in Scb1.
           eapply subtyping_find_class in Scb0;eauto 2; unfold JFObject; try congruence.
           decompose_ex Scb0.
           destruct cd.
           generalize Scb0;intros.
           eapply find_class_in in Scb0.
           eapply base in Scb0.
           eapply substep; try eapply Scb1; try eapply Scb0; auto 1.
    ++ eapply subtyping_further.
       generalize Scb;intros.
       eapply subtype_class_bool_find_class_second in Scb0;eauto.
    ++ eapply subtyping_further.
       generalize Scb;intros.
       eapply subtype_class_bool_find_class_second in Scb0;eauto.
Qed.
       
Hint Resolve subtype_class_bool_simple decompose_subtype_class_bool
     extends_subtype_bool_complete decompose_subtype_class_bool_none
     subtype_class_bool_subtyping.





Hint Resolve names_unique_count_zero.



Lemma subtype_class_bool_complete :
  forall CC C D,
    names_unique CC ->
    subtype_well_founded CC ->
    subtyping CC C D  ->
    forall  cn dn,
      C = (JFClass cn) ->
      D = (JFClass dn) ->
      JFClass cn <> JFObject ->
      cn <> dn ->
        subtype_class_bool CC cn dn = true.
Proof.
  induction CC; intros C D H  H2 H3 Cid Did H4 H5 H6 H8.
  + inversion H3.
    ++ subst. injection H1;intros;subst.
       contradiction.
    ++ subst. injection H1;intros;subst.
       simpl.
       destruct (JFClassName_dec Cid JFObjectName); try contradiction;auto.
    ++ subst. inversion H0.
    ++ subst.
       inversion H7.
  + inversion H3.
    - congruence.
    - assert (Did = JFObjectName) by (unfold JFObject in *; congruence).
      subst.
      eauto.
    - subst. 
      discriminate H0.
    - destruct a.
      subst.
      destruct ex.
      -- apply decompose_subtype_class_bool.
         --- intros.
             assert (cn = cn0) by congruence.
             subst.
             assert (dn=j) by eauto. 
             subst j.
             destruct (JFClassName_dec dn Did); try rewrite e; eauto 2.
             eapply subtyping_further_neq in H9;eauto 2.
             eapply IHCC;eauto 2. (* subtype_class_bool CC j Did = true *)
             ---- subst.
                  eapply (subtyping_neq_object (JFCDecl cn0 (Some dn) fields methods :: CC) dn (JFClass Did));
                    auto;try congruence.
                  unfold subtype_well_founded in H2.
                  pose find_class_eq as Fceq.
                  apply H2 in Fceq.
                  decompose_ex Fceq.
                  eapply number_of_extends_object_is_not_extended;eauto 2.
             ---- eapply extends_neq;eauto.
         --- intros.
             { destruct (JFClassName_dec Cid Did); eauto 3.
               destruct (JFClassName_dec Did JFObjectName); try rewrite e; eauto 2.
               eapply subtyping_further_neq in H3;eauto 2; try congruence.
               injection H0;intros;subst cn;clear H0.
               eapply IHCC;  eauto 2.
             }
      -- assert (Cid=cn) by congruence.
         subst Cid.
         eapply extends_neq_none in H7;eauto 2.
         apply decompose_subtype_class_bool_none;eauto 2.
         eapply subtyping_further_neq in H3;eauto 2; try congruence.
         eapply IHCC; eauto 2 using find_class_further_neq.
Qed.





(** This is the `lifting' of the class subtyping to subtyping on class
    identifiers.
 *)
Definition subtype_bool (CC:JFProgram) (C D: JFCId) : bool := 
  match C, D with
  | JFBotClass, _ => true
  | _, JFBotClass => false
  | JFClass cn, JFClass dn => subtype_class_bool CC cn dn
  end.


Inductive leqAnnLS : JFProgram -> JFCId -> JFMId -> JFAMod -> JFAMod -> Prop:=
| isLSTrueAnn : forall (CC:JFProgram) (C:JFCId) (cn:JFClassName) (m:JFMId) (ra:JFAMod) (rb:JFAMod),
    C = JFClass cn ->
    isLSForId CC cn m ->
    leqAnn ra rb ->
    leqAnnLS CC C m ra rb
| isLSFalseAnn : forall (CC:JFProgram) (C:JFCId) (cn:JFClassName) (m:JFMId) (ra:JFAMod) (rb:JFAMod),
    C = JFClass cn ->
    ~ isLSForId CC cn m ->
    leqAnnLS CC C m ra rb.


(**
   We have two related orders on JFACIds that depend on whether the method
   local sensitive or not local sensitive. It is defined as 
   <:^{\isLocalSensitive(C,m)} in Section~{sec:type-system}.
*)
Inductive leqIsLS : JFProgram -> JFCId -> JFMId -> JFACId -> JFACId -> Prop :=
| isLSTrue : forall (CC:JFProgram) (Cid:JFCId) (cn:JFClassName)
                    (mid:JFMId) (ls:JFACId) (lc:JFCId) (la:JFAMod) (rs:JFACId) (rc:JFCId) (ra:JFAMod),
    Cid = JFClass cn ->
    isLSForId CC cn mid ->
    ls = (lc, la) ->
    rs = (rc, ra) ->
    subtyping CC lc rc ->
    leqAnn la ra ->
    leqIsLS CC Cid mid ls rs
| isLSFalse : forall (CC:JFProgram) (Cid:JFCId) (cn:JFClassName)
                    (mid:JFMId) (ls:JFACId) (lc:JFCId) (la:JFAMod) (rs:JFACId) (rc:JFCId) (ra:JFAMod),
    Cid = JFClass cn ->
    ~ isLSForId CC cn mid ->
    ls = (lc, la) ->
    rs = (rc, ra) ->
    subtyping CC lc rc ->
    leqIsLS CC Cid mid ls rs.

Lemma leqIsLS_refl:
  forall CC C cn mid ls,
    C = JFClass cn ->
    leqIsLS CC C mid ls ls.
Proof.
  intros.
  assert (isLSForId CC cn mid \/ ~isLSForId CC cn mid) by auto with myhints.
  destruct ls.
  destruct H0.
  + eapply isLSTrue;eauto with myhints.
  + eapply isLSFalse;eauto with myhints.
Qed.

Lemma leqIsLS_trans:
  forall CC C cn mid mu mu' mu'',
    (program_contains CC JFObjectName) = true ->
    names_unique CC -> 
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    C = JFClass cn ->
    leqIsLS CC C mid mu mu' ->
    leqIsLS CC C mid mu' mu'' ->
    leqIsLS CC C mid mu mu''.
Proof.
  intros CC Cid cname mid mu mu' mu''.
  intros Pctns Nuq Oine Einabo Cideq LeqISLSmumu' LeqISLSmu'mu''.
  assert (isLSForId CC cname mid \/ ~isLSForId CC cname mid)
    as IsLSDec by auto with myhints.
  destruct mu as [C md].
  destruct mu'' as [C'' md''].
  destruct LeqISLSmumu' as [CC cname0 mid ls lc la rs rc ra
                              Cideq' IsLSForcname0 lseq rseq Sub LeqAnn|
                            CC' cid cname0 mid ls lc la rs rc ra
                               Cideq'
                               IsLSForcname0 lseq rseq Sub].
  + subst.
    injection IsLSForcname0;intros;clear IsLSForcname0;subst.
    eapply isLSTrue;try apply Cideq;auto;
    try (inversion LeqISLSmu'mu'' as [CC' Cid cname mid0 ls0 lc la0 rs0 rc ra0
                                       Mideq IsLSForIdcname raeq C''eq Sub'
                                       LeqAnn'|
                                    CC' Cid cname mid0 ls0 lc la0 rs0 rc ra0
                                       Mideq IsLSForIdcname raeq C''eq Sub'];
         (subst;
          injection Mideq;intros;clear Mideq;
          injection raeq;intros;clear raeq;
          injection C''eq;intros;clear C''eq;
          subst;
          subst)).
    ++ eauto using subtrans.
    ++ eauto using subtrans.
    ++ eauto using leqAnn_trans.
    ++ contradiction.
  + subst.
    injection Cideq';intros;clear Cideq';subst.
    eapply isLSFalse;try apply IsLSForcname0;auto.
    inversion LeqISLSmu'mu'' as [CC'' Cid cname mid0 ls0 lc' la0 rs0 rc' ra0
                                    Mideq IsLSForIdcname raeq C''eq Sub'
                                    LeqAnn'|
                                 CC'' Cid cname mid0 ls0 l'c la0 rs0 rc' ra0
                                    Mideq IsLSForIdcname raeq C''eq Sub'];
    (subst;
         injection Mideq;intros;clear Mideq;
           injection raeq;intros;clear raeq;
            injection C''eq;intros;clear C''eq;
              subst;
       eauto using subtrans).
Qed.

Lemma minimalIsLS:
  forall CC m C amod cn md,
    methodLookup CC cn m = Some md ->
    leqIsLS CC (JFClass cn) m (JFBotClass,  JFrwr) (C, amod).
Proof.
  intros.
  edestruct (isLSForId_dec CC cn m).
  * inversion H0.
    eapply isLSTrue; eauto with myhints.
  * eapply isLSFalse; eauto.
Qed.

Hint Resolve minimalIsLS leqIsLS_refl leqIsLS_trans.

(**
   Lifting of an inequality predicate that compares using a given parameter predicate [P] an element
   of JFACId with a list of JFACId's. It holds true when at least one comparison holds.
*)
Inductive isLeqIn : (JFACId -> JFACId -> Prop) -> JFACId -> list JFACId -> Prop :=
  | consNotIn : forall  (P:JFACId -> JFACId -> Prop) (caid:JFACId) (daid:JFACId) (l:list JFACId),
      ~P caid daid ->
      isLeqIn P caid l ->
      isLeqIn P caid (daid :: l)
  | consIsIn : forall  (P:JFACId -> JFACId -> Prop) (caid:JFACId) (daid:JFACId) (l:list JFACId),
      P caid daid ->
      isLeqIn P caid (daid :: l).




Lemma sub_leq_leqIsLS : forall CC Cid Cname mid mu1 mu2 D1 D2,
    Cid = JFClass Cname ->
    leqAnn mu1 mu2 ->
    subtyping CC D1 D2 ->
    leqIsLS CC Cid mid (D1,mu1) (D2,mu2).
Proof.
  intros.
  assert (isLSForId CC Cname mid \/ ~isLSForId CC Cname mid)
    as IsLSDec by auto with myhints.
  destruct IsLSDec.
  + econstructor 1; eauto 1.
  + econstructor 2; eauto 1.  
Qed.

Lemma sub_leq_not_leqIsLS : forall CC Cid Cname mid mu1 mu2 D1 D2,
    Cid = JFClass Cname ->
    ~isLSForId CC Cname mid ->
    subtyping CC D1 D2 ->
    leqIsLS CC Cid mid (D1,mu1) (D2,mu2).
Proof.
  intros.
  + econstructor 2; eauto 1.  
Qed.

Lemma leqIsLS_sub : forall CC Cid mid mu1 mu2 D1 D2,
    leqIsLS CC Cid mid (D1,mu1) (D2,mu2) ->
    subtyping CC D1 D2.
Proof.
  inversion 1; sauto.
Qed.

Lemma leqIsLS_dec : forall CC Cid mid d d',
    leqIsLS CC Cid mid d d' \/ ~leqIsLS CC Cid mid d d'.
Proof.
  intros.
  destruct d.
  destruct d'.
  destruct (subtyping_dec CC j j1).
  + destruct (leqAnn_dec j0 j2).
    ++ destruct Cid.
       +++ destruct (isLSForId_dec CC cn mid).
           ++++ left; eapply isLSTrue;eauto.
           ++++ left; eapply isLSFalse;eauto.
       +++ right.
           intro.
           inversion H1; congruence.
    ++ destruct Cid.
       +++ destruct (isLSForId_dec CC cn mid).
           ++++ right.
                intro.
                inversion H2; try congruence.
           ++++ left; eapply isLSFalse;eauto.
       +++ right.
           intro.
           inversion H1; congruence.
  + right.
    intro.
    apply H.
    inversion H0;subst;injection H3;intros;injection H4;intros;subst;eauto.
Qed.

Hint Resolve leqIsLS_sub.
                        
Lemma leqIsLS_leqAnn :
  forall CC Cid mid C1 mu1 C2 mu2,
    leqIsLS CC (JFClass Cid) mid (C1,mu1) (C2,mu2) ->
    isLSForId CC Cid mid ->                           
    leqAnn mu1 mu2.
Proof.
  inversion 1; congruence.
Qed.

Hint Resolve leqIsLS_leqAnn.

Definition leqACId (CC:JFProgram) (C D:JFACId) : Prop :=
  let (Cc,Can) := C in
  let (Dc,Dan) := D in
  subtyping CC Cc Dc /\ leqAnn Can Dan.

Lemma leqACId_refl:
  forall (CC:JFProgram) (C:JFACId),
    leqACId CC C C.
Proof.
  intros.
  unfold leqACId.
  destruct C.
  auto with myhints.
Qed.

Lemma leqACId_trans:
  forall (CC:JFProgram) (C D E:JFACId),
    (program_contains CC JFObjectName) = true ->
    names_unique CC -> 
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    leqACId CC C D -> leqACId CC D E -> leqACId CC C E.
Proof.
  intros CC C D E Pcont Nu Onex extns lCD lDE.
  unfold leqACId in *.
  destruct C.
  destruct D.
  destruct E.
  intuition.
  + inversion H.
    ++ rewrite H4 in *.
      eapply subtrans;eauto 2.
    ++ rewrite <- H4 in *.
       eauto 2.
    ++ rewrite <- H4 in *.
       eauto 2.
    ++ eapply subtrans;eauto 2.
  + eauto 2 with myhints.
Qed.

Hint Resolve leqACId_refl leqACId_trans.


Lemma leqACId_leqIsLS :
  forall CC Cn mid Acid1 Acid2, leqACId CC Acid1 Acid2 -> leqIsLS CC (JFClass Cn) mid Acid1 Acid2.
Proof.
  destruct Acid1 as (C1,mu1).
  destruct Acid2 as (C2,mu2).
  
  destruct 1.
  edestruct isLSForId_dec.
  + econstructor 1; eauto 1.
  + econstructor 2; eauto 1.
Qed.

Hint Resolve leqACId_leqIsLS.


(** The lower bound operation for the lattice of class types. *)
(** [Cid ⊓ Did = Some Eid] iff [Cid Did ∈ CC] *)
Definition infClass (CC:JFProgram) (Cid Did:JFCId) :=
  match Cid with
  | JFClass cn => match Did with
                  | JFClass dn =>
                    if subtype_class_bool CC cn dn
                    then JFClass cn
                    else if subtype_class_bool CC dn cn
                         then JFClass dn
                         else JFBotClass
                  | JFBotClass => JFBotClass
                  end
  | JFBotClass => JFBotClass
  end.


Lemma infClass_comm:
  forall CC Cid Did C,
    subtype_well_founded CC ->
    names_unique CC ->
    infClass CC Cid Did = C ->
    infClass CC Did Cid = C.
Proof.
  intros CC Cid Did C Swf Nuq H.
  unfold infClass in H.
  unfold infClass.
  destruct Cid, Did;eauto.
  destruct (JFClassName_dec cn cn0);
    destruct (JFClassName_dec cn0 cn);
    subst; auto.
  destruct (subtype_class_bool CC cn cn0) eqn:?;
           destruct (subtype_class_bool CC cn0 cn) eqn:?; try auto.
  eapply subtype_class_bool_refl in Heqb;eauto.
  subst;auto.
Qed.

Lemma infClass_subtype_class_bool:
  forall CC Cn Dn En,
    infClass CC (JFClass Cn) (JFClass Dn) = JFClass En ->
    subtype_class_bool CC En Cn = true.
Proof.
  intros.
  simpl in H.
  destruct (subtype_class_bool CC Cn Dn) eqn:?; simplify_eq H;intros;subst;eauto 2.
  destruct (subtype_class_bool CC Dn Cn) eqn:?; simplify_eq H;intros;subst;eauto 2.
Qed.

(** [C1 ≤: C1 ⊓ C2] *)
Lemma infClass_subL : forall CC Cid Cid1 Cid2,
    names_unique CC ->
    subtype_well_founded CC ->
    infClass CC Cid1 Cid2 = Cid -> subtyping CC Cid Cid1.
Proof.
  intros.
  unfold infClass in H1.
  destruct Cid1, Cid2;subst;eauto 1.
  destruct (subtype_class_bool CC cn cn0) eqn:?;eauto 1.
  destruct (subtype_class_bool CC cn0 cn) eqn:?;eauto 1.
  destruct (JFClassName_dec cn cn0);subst;eauto 1.
  destruct (JFClassName_dec cn JFObjectName);eauto 1.
  + subst. auto.
  + generalize Heqb0;intros.
    eapply subtype_class_bool_find_class_second in Heqb1; eauto 2.
Qed.


(** [C2 ≤: C1 ⊓ C2] *)
Lemma infClass_subR : forall CC Cid Cid1 Cid2,
    names_unique CC ->
    subtype_well_founded CC ->
    infClass CC Cid1 Cid2 = Cid -> subtyping CC Cid Cid2.
Proof.
  intros.
  eapply infClass_comm in H1;eauto 2.
  eapply infClass_subL;eauto 2.
Qed.


(** [C ≤: C1 -> C ≤: C2 -> C ≤: C1 ⊓ C2] *)
Lemma infClass_inf : forall CC Cid Cid' Cid1 Cid2,
    subtyping CC Cid Cid1 -> subtyping CC Cid Cid2 ->
    names_unique CC ->
    subtype_well_founded CC ->
    infClass CC Cid1 Cid2 = Cid' -> subtyping CC Cid Cid'.
Proof.
  intros.
  destruct Cid1, Cid2.
  + simpl in H3.
    destruct (subtype_class_bool CC cn cn0) eqn:?.
    ++ subst;eauto 2.
    ++ destruct (subtype_class_bool CC cn0 cn) eqn:?.
       +++ subst;eauto 2.
       +++ subst.
           destruct (JFClassName_dec cn JFObjectName);
             subst. try (rewrite subtype_class_bool_object in Heqb0; discriminate Heqb0).
           destruct (JFClassName_dec cn0 JFObjectName);
             subst; try (rewrite subtype_class_bool_object in Heqb; discriminate Heqb).
           destruct (JFClassName_dec cn cn0);
             subst; try (rewrite subtype_class_bool_same in Heqb; discriminate Heqb).
           eapply subtyping_less in H;eauto 2.
           destruct H.
           * destruct CC.
             ** inversion H;subst.
                *** contradiction.
                *** rewrite subtype_class_bool_object in Heqb0.
                    discriminate Heqb0.
                *** inversion H5.
             ** generalize H1;intros.
                eapply number_of_extends_some in H3;eauto 2.
                decompose_ex H3.
                generalize H1;intros.
                eapply number_of_extends_object_is_not_extended in H4;eauto 2.
                generalize H1;intros.
                eapply subtyping_find_class in H5;eauto 2;unfold JFObject; try congruence.
                decompose_ex H5.
                eapply subtype_class_bool_complete in H;eauto 2;unfold JFObject;try congruence.
           * destruct H.
             ** destruct CC.
                *** inversion H;subst.
                    **** contradiction.
                    **** contradiction.
                    **** inversion H5.
                *** generalize H1;intros.
                    eapply number_of_extends_some in H3;eauto 2.
                    decompose_ex H3.
                    generalize H1;intros.
                    eapply number_of_extends_object_is_not_extended in H4;eauto 2.
                    generalize H1;intros.
                    eapply subtyping_find_class in H5;eauto 2;unfold JFObject; try congruence.
                    decompose_ex H5.
                    eapply subtype_class_bool_complete in H;eauto 2;unfold JFObject;try congruence.
             ** subst;eauto 2.
  + sauto.
  + sauto.
  + sauto.
Qed.

Lemma infClass_trichotomy:
  forall CC Cid Did,
    infClass CC Cid Did = Cid \/ infClass CC Cid Did = Did \/ infClass CC Cid Did = JFBotClass.
Proof.
  intros.
  unfold infClass.
  destruct Cid;eauto.
  destruct Did;eauto.
  destruct (subtype_class_bool CC cn cn0);eauto.
  destruct (subtype_class_bool CC cn0 cn);eauto.
Qed.
  
(** Greatest lower bound of [acid1] and [acid2] *)
(** [acid1 ⊓ acid2 = Some acid] iff [acid, acid2 ∈ CC] *)

Definition infACId (CC:JFProgram) (acid1 acid2:JFACId) :=
  let (tp1,an1) := acid1 in
  let (tp2,an2) := acid2 in
  (infClass CC tp1 tp2, infAnn an1 an2).


Lemma infACId_infClass : forall CC Cid1 mu1 Cid2 mu2 Cid mu,
    infACId CC (Cid1,mu1) (Cid2,mu2) = (Cid,mu) ->
    infClass CC Cid1 Cid2 = Cid.
Proof.
  intros until 0.
  unfold infACId.
  congruence.
Qed.

Lemma infACId_infAnn : forall CC Cid1 mu1 Cid2 mu2 Cid mu,
    infACId CC (Cid1,mu1) (Cid2,mu2) = (Cid,mu) ->
    infAnn mu1 mu2 = mu.
Proof.
  intros until 0.
  unfold infACId.
  congruence.
Qed.



Lemma infACId_comm:
  forall CC Cid Did C,
    subtype_well_founded CC ->
    names_unique CC ->
    infACId CC Cid Did = C ->
    infACId CC Did Cid = C.
Proof.
  intros.
  unfold infACId in H1.
  unfold infACId.
  destruct Did, Cid.
  destruct (infClass CC j1 j) eqn:?;try discriminate H1.
  + eapply infClass_comm in Heqj3;eauto.
    rewrite Heqj3.
    rewrite <- H1.
    replace (infAnn j0 j2) with (infAnn j2 j0);auto.
    unfold infAnn.
    destruct j2;destruct j0;eauto.
  + eapply infClass_comm in Heqj3;eauto.
    rewrite Heqj3.
    replace (infAnn j0 j2) with (infAnn j2 j0);auto.
    unfold infAnn.
    destruct j2;destruct j0;eauto.
Qed.

(** [acid1 ≤: acid1 ⊓ acid2] *)
Lemma infACId_leqIsLS_L:
  forall CC acid1 acid2 acid Cn mid,
    names_unique CC ->
    subtype_well_founded CC -> 
    infACId CC acid1 acid2 = acid ->
    leqIsLS CC (JFClass Cn) mid acid acid1.
Proof.
  intros CC acid1 acid2 acid Cn mid.
  intros Nuq Swf.
  intros.
  destruct acid1 as (C1,mu1).
  destruct acid2 as (C2,mu2).
  simpl in H.
  destruct acid as (C,mu).
  injection H;intros.
  edestruct isLSForId_dec.
  + econstructor 1;eauto 2 with myhints.
    destruct C; eauto 1.
    destruct C1, C2; try discriminate H1.
    eapply infClass_subtype_class_bool in H1;eauto 2.
  + econstructor 2;eauto 2.
    destruct C; eauto 2.
    destruct C1, C2; try discriminate H1.
    eapply infClass_subtype_class_bool in H1;eauto 2.
Qed.


(** [acid2 ≤: acid1 ⊓ acid2] *)
Lemma infACId_leqIsLS_R:
  forall CC acida acidb acidc Cn mid,
    names_unique CC ->
    subtype_well_founded CC -> 
    infACId CC acida acidb = acidc ->
    leqIsLS CC (JFClass Cn) mid acidc acidb.
Proof.
  intros CC acida acidb acidc Cn mid.
  intros Nuq Swf.
  intros.
  eapply infACId_comm in H;eauto 2.
  eapply infACId_leqIsLS_L in H;eauto 2.
Qed.

(** [acid ≤: acid1 -> acid ≤: acid2 -> acid ≤: acid1 ⊓ acid2] *)
Lemma infACId_leqIsLS_largest:
  forall CC acid acid' acid1 acid2 Cn mid,
    names_unique CC ->
    subtype_well_founded CC -> 
    leqIsLS CC (JFClass Cn) mid acid acid1 ->
    leqIsLS CC (JFClass Cn) mid acid acid2 ->
    infACId CC acid1 acid2 = acid' ->
    leqIsLS CC (JFClass Cn) mid acid acid'.
Proof.
  intros CC acid acid' acid1 acid2 Cn mid.
  intros Nuq Swf.
  intros Leq0 Leq1 InfACId.
  destruct acid, acid'.
  destruct acid1, acid2.
  generalize InfACId;intros.
  eapply infACId_infAnn in InfACId0.
  generalize InfACId;intros.
  eapply infACId_infClass in InfACId1.
  destruct (isLSForId_dec CC Cn mid).
  + eapply sub_leq_leqIsLS;eauto.
    ++ inversion Leq0; try congruence.
       simplify_eq H2;
         simplify_eq H3;intros.
       subst.
       clear H2 H3.
       inversion Leq1; try congruence.
       simplify_eq H6;
         simplify_eq H7;intros.
       subst.
       clear H6 H7;eauto using infAnn_inf.
    ++ inversion Leq0; try congruence.
       simplify_eq H2;
         simplify_eq H3;intros.
       subst.
       clear H2 H3.
       inversion Leq1; try congruence.
       simplify_eq H6;
         simplify_eq H7;intros.
       subst.
       clear H6 H7.
       eapply infClass_inf.
       apply H4.
       apply H8.
       auto.
       auto.
       auto.
  + eapply sub_leq_not_leqIsLS;eauto 2.
    inversion Leq0; try congruence.
    simplify_eq H2;
      simplify_eq H3;intros.
    subst.
    clear H2 H3.
    inversion Leq1; try congruence.
    simplify_eq H5;
      simplify_eq H6;intros.
    subst.
    clear H5 H6.
    eapply infClass_inf.
    apply H4.
    apply H7.
    auto.
    auto.
    auto.
Qed.


(**
   Lifting of an inequality predicate that compares using a given parameter predicate P a list
   of JFACId's with a list of JFACId's. It holds true when at least one comparison holds.
*)
Inductive isLeqIncluded : (JFACId -> JFACId -> Prop) -> list JFACId -> list JFACId -> Prop :=
  | emptyFirst : forall  (CC:JFACId -> JFACId -> Prop) (l2:list JFACId),
      isLeqIncluded CC [] l2
  | consFirst : forall  (CC:JFACId -> JFACId -> Prop) (caid:JFACId) (l1:list JFACId) (l2:list JFACId),
      isLeqIn CC caid l2 ->
      isLeqIncluded CC l1 l2 ->
      isLeqIncluded CC (caid :: l1) l2.

Lemma leqISLS_isLeqIn:
  forall l CC C m a a' cname,
    program_contains CC JFObjectName = true ->
    names_unique CC ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    C = JFClass cname ->
    leqIsLS CC C m a a' ->
    isLeqIn (leqIsLS CC C m) a' l ->
    isLeqIn (leqIsLS CC C m) a l.
Proof.
  induction l.
  + intros CC C m a a' cname Pcont Nuq Oine Eiabo Ceq. intros.
    inversion H0.
  + intros CC C m a0 a' cname Pcont Nuq Oine Eiabo Ceq. intros.
    inversion H0.
    ++ subst.
       eapply IHl in H6; try apply H;eauto.
       destruct (leqIsLS_dec CC (JFClass cname) m a0 a).
       +++ constructor 2;eauto.
       +++ constructor 1;eauto.
    ++ subst.
       constructor 2;eauto 2.
Qed.

Lemma leqIsLS_isLeqIncluded:
  forall CC cid m C mu D nu,
    leqIsLS CC cid m (C, mu) (D, nu) ->
    isLeqIncluded (leqIsLS CC cid m) [(C,mu)] [(D, nu)].
Proof.
  intros.
  eapply consFirst;eauto.
  eapply consIsIn;eauto.
  constructor.
Qed.
  
Lemma isLeqIncluded_monotone:
  forall CC C m a l1 l2,
    isLeqIncluded (leqIsLS CC C m) (a :: l1) l2 ->
    isLeqIncluded (leqIsLS CC C m) l1 l2.
Proof.
  destruct l1.
  + sauto.
  + intros.
    constructor 2.
    ++ inversion H.
       subst.
       inversion H5.
       auto.
    ++ inversion H.
       subst.
       inversion H5.
       auto.
Qed.

Lemma isLeqIn_isLeqIncluded:
  forall CC C cn m a l1 l2,
    program_contains CC JFObjectName = true ->
    names_unique CC ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    C = JFClass cn ->
    isLeqIn (leqIsLS CC C m) a l1 ->
    isLeqIncluded (leqIsLS CC C m) l1 l2 ->
    isLeqIn (leqIsLS CC C m) a l2.
Proof.
  induction l1.
  + intros.
    inversion H4.
  + intros.
    inversion H4.
    ++ subst.
       eapply IHl1;eauto.
       inversion H5.
       subst.
       eauto using isLeqIncluded_monotone.
    ++ subst.
       inversion H5.
       subst.
       eauto 2 using leqISLS_isLeqIn.
Qed.

Lemma isLeqIncluded_trans:
  forall CC C cn m l1 l2 l3,
    program_contains CC JFObjectName = true ->
    names_unique CC ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC ->
    C = JFClass cn ->
    isLeqIncluded (leqIsLS CC C m) l1 l2 ->
    isLeqIncluded (leqIsLS CC C m) l2 l3 ->
    isLeqIncluded (leqIsLS CC C m) l1 l3.
Proof.
  intros.
  induction l1.
  + constructor.
  + constructor 2.
    inversion H4.
    subst.
    eauto using isLeqIn_isLeqIncluded.
    eauto using isLeqIncluded_monotone.
Qed.

Definition leqAcid_bool (CC:JFProgram) (acid1:JFACId) (acid2:JFACId) :=
  match acid1 with
  | (C,mu) => match acid2 with
              | (C',mu') => andb (subtype_bool CC C C') (leqAnn_bool mu mu')
              end
  end.

