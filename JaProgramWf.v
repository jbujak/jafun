Require Import JaSyntax.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import NPeano.
Require Import PeanoNat.
Require Export Arith.
Open Scope nat_scope.
Require Import JaSyntax.
Require Import JaProgram.
Require Import JaSubtype.
Require Import JaTactics.



(**
   - all class names are unique
   - contains Object
   - contains NPE
   - Object is not extended
   - if class is not extension then it is the class of Object
   - subtyping is well founded
*)
Definition Well_formed_program (CC:JFProgram) :=
  names_unique CC /\
  (program_contains CC JFObjectName) = true /\
  (program_contains CC JFNPEName) = true /\
  object_is_not_extended CC /\
  extensions_in_all_but_object CC /\
  subtype_well_founded CC.

Lemma well_formed_program_names_unique:
  forall CC,
    Well_formed_program CC -> names_unique CC.
Proof.
  intros. red in H.
  intuition.
Qed.  

Lemma well_formed_program_contains_object:
  forall CC,
    Well_formed_program CC -> (program_contains CC JFObjectName) = true.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_contains_npe:
  forall CC,
    Well_formed_program CC -> (program_contains CC JFNPEName) = true.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_object_is_not_extended:
  forall CC,
    Well_formed_program CC ->   object_is_not_extended CC.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_extensions_in_all_but_object:
  forall CC,
    Well_formed_program CC -> extensions_in_all_but_object CC.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_subtype_well_founded:
  forall CC,
    Well_formed_program CC -> subtype_well_founded CC.
Proof.
  intros. red in H.
  intuition.
Qed.

Hint Resolve well_formed_program_names_unique  well_formed_program_contains_object
     well_formed_program_contains_npe well_formed_program_object_is_not_extended
     well_formed_program_extensions_in_all_but_object well_formed_program_subtype_well_founded.
     



Lemma well_formed_program_further:
  forall C CC,
    program_contains CC JFObjectName = true ->
    program_contains CC JFNPEName = true ->
    Well_formed_program (C :: CC) ->
    Well_formed_program CC.
Proof.
  intros.
  unfold Well_formed_program in *.
  decompose [and] H1; clear H1.
  repeat split.
  + apply (names_unique_further CC C); auto 1.
  + auto 1.
  + auto 1.
  + apply (object_is_not_extended_further CC C); auto 1.
  + apply (extensions_in_all_but_object_further CC C); auto 1.
  + apply (subtype_well_founded_further CC C); auto 1.
Qed.
    
(* -------------------------------------------------------------- *)

Lemma flds_aux_decompose_object:
  forall m CC fl fl' fldlst dname decl n flds',
    flds_aux CC JFObjectName n fl = Some (fl++fldlst) ->
    (program_contains CC JFObjectName) = true ->
    find_class CC dname = Some decl ->
    flds_aux CC dname m fl' = Some (fl'++flds') ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    names_unique CC ->
    exists flds'', flds' = flds'' ++ fldlst.
Proof.
  induction m.
  + intros CC fl fl' fldlst dname decl n flds'.
    intros FldsAuxO PcontObj Fcls FldsAuxD Swf Eiabo Nuq.
    simpl in FldsAuxD.
    rewrite Fcls in FldsAuxD.
    destruct decl.
    generalize Fcls;intros.
    eapply find_class_eq_name in Fcls0;subst.
    generalize Fcls;intros.
    eapply find_class_in in Fcls0.
    unfold extensions_in_all_but_object in Eiabo.
    generalize Fcls;intros.
    eapply Forall_forall in Fcls0;try eapply Eiabo.
    destruct ex;try discriminate FldsAuxD.
    unfold if_not_extended_then_object in Fcls0.
    subst.
    injection FldsAuxD.
    intros.
    destruct n.
    ++ simpl in FldsAuxO.
       rewrite Fcls1 in FldsAuxO.
       injection FldsAuxO;intros;subst.
       eapply program_contains_find_class in PcontObj.
       destruct PcontObj.
       exists [].
       rewrite app_nil_l.
       eapply  app_inv_head in H.
       eapply  app_inv_head in H0.
       congruence.
    ++ simpl in FldsAuxO.
       rewrite Fcls in FldsAuxO.
       injection FldsAuxO;intros;subst.
       exists [];auto.
       rewrite app_nil_l.
       eapply  app_inv_head in H.
       eapply  app_inv_head in H0.
       congruence.
  + intros CC fl fl' fldlst dname decl n flds'.
    intros FldsAuxO PcontObj Fcls FldsAuxD Swf Eiabo Nuq.
    generalize FldsAuxD;intros.
    simpl in FldsAuxD0.
    rewrite Fcls in FldsAuxD0.
    destruct decl.
    destruct ex.
    ++ generalize FldsAuxD0;intros.
       eapply flds_aux_decompose_acc in FldsAuxD1.
       destruct FldsAuxD1.
       rewrite H in FldsAuxD0.
       generalize Fcls;intros.
       eapply subtype_get_superclass in Fcls0;eauto 1.
       destruct Fcls0.

       eapply IHm in FldsAuxD0; eauto 2.
       rewrite app_ass in H.
       apply app_inv_head in H.
       rewrite H.
       destruct FldsAuxD0.
       rewrite H1.
       replace (flds_of_cd (JFCDecl cn (Some j) fields methods) ++ x1 ++ fldlst)
       with ((flds_of_cd (JFCDecl cn (Some j) fields methods) ++ x1) ++ fldlst)
         by (rewrite app_ass;auto).
       eexists;eauto.
    ++ generalize Fcls;intros.
       eapply find_class_eq_name in Fcls0.
       subst.
       generalize Fcls;intros.
       unfold extensions_in_all_but_object in Eiabo.
       eapply find_class_in in Fcls0.
       eapply Forall_forall in Fcls0; try eapply Eiabo.
       unfold if_not_extended_then_object in Fcls0.
       subst.
       assert (flds_aux CC JFObjectName (S m) fl = Some (fl ++ flds')). {
         replace fl with (fl ++ []) by eauto using app_nil_r.
         rewrite app_ass.
         eapply flds_aux_decompose_second_same.
         replace fl' with (fl' ++ []) in FldsAuxD by eauto using app_nil_r.
         rewrite app_ass in FldsAuxD.
         eauto.
       }
       assert (Some (fl ++ flds') = Some (fl ++ fldlst)). {
         assert (S m <= n \/ n < S m) by auto using NPeano.Nat.le_gt_cases.
         destruct H0.
         assert (S m < n \/ S m = n) by  eauto using le_lt_or_eq.
         destruct H1.
         eapply flds_monotone_n in H1;eauto.
         rewrite H1 in FldsAuxO.
         auto.
         rewrite H1 in H.
         rewrite H in FldsAuxO.
         auto.
         eapply flds_monotone_n in FldsAuxO;eauto.
         rewrite FldsAuxO in H.
         auto.
       }
       injection H0;intros.
       apply app_inv_head in H1.
       subst.
       exists [].
       rewrite app_nil_l.
       auto.
 Qed.



Lemma flds_aux_decompose_program_neq:
  forall n fds fd CC cname dname x fields methods,
    names_unique ((JFCDecl cname x fields methods) :: CC) ->
    subtype_well_founded ((JFCDecl cname x fields methods) :: CC) ->
    flds_aux ((JFCDecl cname x fields methods) :: CC) dname n fd = Some fds ->
    cname <> dname ->
    flds_aux CC dname n fd = Some fds.
Proof.
  induction n.
  * intros fds fd CC cname dname x fields methods.
    intros Nuq SbWfd FldsAux cneq.
    simpl in FldsAux.
    simpl.
    destruct (JFClassName_dec cname dname);try contradiction.
    destruct (find_class CC dname); try discriminate FldsAux.
    destruct j.
    destruct ex;try discriminate FldsAux.
    auto.
  * intros fds fd CC cname dname x fields methods.
    intros Nuq SbWfd FldsAux Neq.
    simpl; simpl in FldsAux.
    destruct (JFClassName_dec cname dname);try contradiction.
    destruct (find_class CC dname) eqn:?; try discriminate FldsAux.
    destruct j.
    destruct ex;auto.
    assert (cname <>j). {
         assert (exists CCC : JFClassDeclaration, find_class CC j = Some CCC) by eauto 4 using subtype_get_superclass.
         destruct H.
         destruct x0.
         erewrite <- (find_class_eq_name CC j cn0) in H.
         assert (In (JFCDecl j ex fields1 methods1) CC) by eauto 2 using find_class_in.
         eauto 2 using names_unique_in_neq.
         eauto 1.
       }
    eapply IHn;eauto 1.
Qed.

Lemma flds_monotone_P:
  forall CC n dname cname ex flds mths fd fds,
    flds_aux CC dname n fd = Some fds ->
    cname <> dname ->
    names_unique (JFCDecl cname ex flds mths :: CC) ->
    subtype_well_founded ((JFCDecl cname ex flds mths) :: CC) ->
    flds_aux (JFCDecl cname ex flds mths :: CC) dname n fd = Some fds.
Proof.
  induction n.
  + intros.
    simpl.
    simpl in H.
    destruct (JFClassName_dec cname dname); try contradiction.
    auto.
  + intros.
    simpl.
    simpl in H.
    destruct (JFClassName_dec cname dname); try contradiction.
    destruct (find_class CC dname) eqn:?;try discriminate H.
    destruct j.
    destruct ex0; try discriminate H.
    assert (cname <> j). {
      assert (exists CCC,find_class CC j = Some CCC) by eauto 4 using subtype_get_superclass.
      destruct H3.
      destruct x.
      assert (j=cn0) by eauto 2 using find_class_eq_name.
      subst cn0.
      eauto 3 using names_unique_in_neq with myhints.
    }
    apply IHn;auto.
    auto.
Qed.


Lemma flds_aux_extends:
  forall CC n,
  forall cname dname fl fl',
    extends CC cname dname ->
    flds_aux CC dname n fl = Some (fl ++ fl') ->
    names_unique CC ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    exists flds',
      flds_aux CC cname (n+1) fl = Some (fl ++ flds' ++ fl').
Proof.
  Opaque flds_of_cd.
  induction n. 
  + induction 1.
    ++ intros Flds Nuq Swf Eiabo.
       replace (0 + 1) with (S 0) by auto 1 with zarith.
       simpl.
       simpl in Flds.
       destruct_eq.
       assert (cn<>dn) by eauto 2 using names_unique_in_neq.
       destruct (JFClassName_dec cn dn); try contradiction.
       destruct (find_class CC dn); try discriminate Flds.
       destruct j.
       destruct ex0;  try discriminate Flds.
       injection Flds;intros.
       apply app_inv_head in H1.
       rewrite H1.
       eexists. rewrite app_assoc.
       auto 1.
    ++ intros Flds Nuq Swf Eiabo.
       assert (cn1 <> dn2).  {
         assert (exists (ex0 : option JFClassName)
                        (fields' : list JFFieldDeclaration)
                        (methods' : list JFMethodDeclaration),
                    In (JFCDecl dn2 ex0 fields' methods') CC) by eauto using extends_in_second.
         destruct H0 as [ex0 [fields' [methods']]].
         eauto 2 using names_unique_in_neq.
       }
       assert (flds_aux CC dn2 0 fl = Some (fl ++ fl')) by eauto using
                                                                flds_aux_decompose_program_neq.
       assert (exists flds', flds_aux CC cn2 (0 + 1) fl = Some (fl ++ flds' ++ fl'))
         by eauto 5.
       destruct H2 as [flds'].
       eexists.
       assert (exists (fields' : list JFFieldDeclaration)
                      (methods' : list JFMethodDeclaration),
                  In (JFCDecl cn2 (Some dn2) fields' methods') CC) by eauto 2 using extends_in_first.
       destruct H3 as [fields' [methods']].
       apply flds_monotone_P; eauto 2 with myhints.
  + intros cname dname fl fl' Ext Flds Nuq Swf Eiabo.
    replace (S n + 1) with (S (n + 1)) by auto 1 with zarith.
    simpl in Flds.
    destruct (find_class CC dname) eqn:?;try discriminate Flds.
    destruct j.
    assert (dname = cn) by eauto using find_class_eq_name.
    subst cn.

    generalize Ext;intro.
    apply extends_in_first in Ext0.
    destruct Ext0 as [fields' [methods']].
    apply in_find_class in H;eauto 1.
    
    destruct ex; try discriminate Flds. 
    ++ generalize Flds; intro.
       apply flds_aux_decompose_acc in Flds0.
       destruct Flds0.
       rewrite <- app_assoc in H0.
       apply app_inv_head in H0.
       generalize Heqo;intro.
       eapply subtype_get_superclass in Heqo0;eauto 1.
       assert (exists CCC, find_class CC j = Some CCC) by eauto using subtype_get_superclass. 
       destruct H1.
       
       assert (extends CC dname j). {
         eapply find_class_extends; eauto 2.
         assert (exists CC0 CC1 : list JFClassDeclaration, CC = CC0 ++ (JFCDecl dname (Some j) fields methods) :: CC1) by
               eauto 2 using find_class_decompose_program.
           destruct H2 as [CC0 [CC1]].
           assert (exists CCC, find_class (JFCDecl dname (Some j) fields methods :: CC1) j = Some CCC). {
             eapply subtype_get_superclass.
             rewrite H2 in Swf, Nuq.
             eauto 2 using names_unique_decompose_program.
             rewrite H2 in Swf, Nuq.
             eauto 2 using subtype_well_founded_decompose_program.
             eapply find_class_eq.
           }
           destruct H3.
           eapply subtype_well_founded_neq.
           rewrite H2 in Nuq.
           eauto 2 using names_unique_decompose_program.
           rewrite H2 in Nuq, Swf.
           eauto 2 using subtype_well_founded_decompose_program.
       }

       generalize Flds;intros.
       rewrite H0 in Flds0.
       generalize H2;intros.
       rewrite app_assoc in Flds0.
       eapply IHn in H2; eauto 2.

       simpl.
       rewrite H.
       destruct H2.
       replace ((fl ++ flds_of_cd (JFCDecl dname (Some j) fields methods)) ++ x1 ++ x)
       with (fl ++ flds_of_cd (JFCDecl dname (Some j) fields methods) ++ (x1 ++ x)) in H2 by
           (rewrite app_assoc; auto 1).
       eapply flds_aux_decompose_first_same in H2.
       rewrite H2.
       rewrite H0.
       assert (flds_aux CC dname (n + 1) fl =  Some (fl  ++ x1 ++ x)).
       {
         replace fl with (fl ++ []) by (rewrite app_nil_r; auto 1).
         rewrite <- app_assoc.
         eapply flds_aux_decompose_first_same.
         apply H2.
       }
       replace (n+1) with (S n) in H4 by auto 1 with zarith.
       simpl in H4.
       rewrite Heqo in H4.
       rewrite Flds0 in H4.
       injection H4;intros.
       rewrite <- app_assoc in H5.
       apply app_inv_head in H5.
       apply app_inv_tail in H5.
       rewrite H5.
       eexists.
       eauto 1.
    ++ simpl.
       rewrite H.
       replace (n+1) with (S n) by auto 1 with zarith.
       simpl.
       rewrite Heqo.
       injection Flds;intros.
       apply app_inv_head in H0.
       rewrite H0.
       rewrite <- app_assoc.
       eexists. auto 1.
Qed.





(* -------------------------- *)

Lemma subtype_bool_complete :
  forall CC Cid Did, Well_formed_program CC ->
                    subtyping CC Cid Did ->
                    subtype_bool CC Cid Did = true.
Proof.
  intuition.
    unfold subtype_bool.
    destruct Cid.
    destruct Did.
    + unfold JFObject.
      unfold Well_formed_program in H.
      decompose [and] H.
      destruct (JFClassName_dec cn cn0); [rewrite e; eauto 1|].
      destruct (JFClassName_dec cn0 JFObjectName); [rewrite e; eauto 1|].
      destruct (JFClassName_dec cn JFObjectName).
      subst cn.
      assert (JFClass cn0 = JFObject).
      eapply object_is_not_subtype; eauto 1.
      unfold JFObject in H6. congruence.
      assert (exists CCC : JFClassDeclaration, find_class CC cn = Some CCC).
      { eapply subtyping_find_class.
        assert (JFClass cn <> JFClass cn0) by congruence.
        apply H6.
        unfold JFObject.
        congruence.
        congruence.
        auto 1.
        auto 1.
      }
      destruct H6.
      eapply subtype_class_bool_complete; eauto 1.
      unfold JFObject.
      congruence.
    + inversion H0.
      assert (D= JFBotClass).
      eapply subtyping_not_bot.
      apply H4.
      auto 1.
      congruence.
    + auto 1.
Qed.

Lemma subtype_bool_correct_technical:
  forall CC Cid Did,
    names_unique CC ->
    program_contains CC JFObjectName = true ->
    object_is_not_extended CC ->
    extensions_in_all_but_object CC -> subtype_well_founded CC ->
    subtype_bool CC Cid Did = true ->
    subtyping CC Cid Did.
Proof.
  induction CC; intros.
  - unfold Well_formed_program in H.
    unfold program_contains in H0.
    discriminate H0.
  - unfold subtype_bool in H4.
    destruct Cid.
    + destruct Did.
      unfold subtype_class_bool in H4.
      destruct (JFClassName_dec cn cn0); [rewrite e; eauto 1|].
      destruct (JFClassName_dec cn0 JFObjectName); [rewrite e; eauto 1|].
      { destruct a.
        - destruct ex.
          fold (subtype_class_bool CC cn cn0) in H4.
          fold (subtype_class_bool CC j cn0) in H4.
          destruct (JFClassName_dec cn cn1).
          + destruct (JFClassName_dec j cn0).
            * subst cn1.
              subst j.
              eapply substep.
              eauto 1.
              assert (JFClass cn0 = JFClass cn0) by auto 1.
              apply H5.

              assert (exists CCC : JFClassDeclaration, find_class (JFCDecl cn (Some cn0) fields methods :: CC) cn0 = Some CCC).
              { eapply subtype_get_superclass;eauto 2.
                assert (find_class
                          (JFCDecl cn (Some cn0) fields methods :: CC) cn =
                        Some (JFCDecl cn (Some cn0) fields methods)).
                apply find_class_eq.
                apply H5.
              }
              destruct H5.
              assert (find_class CC cn0 = Some x). {
                eapply find_class_further_neq.
                apply n.
                apply H5.
              }
              destruct x.
              eapply base.
              eapply find_class_in; eauto 1.
              apply subrefl.
            * subst cn1.
              eapply substep.
              auto 1.
              assert (JFClass j = JFClass j) by auto 1.
              apply H5.
              
              assert (exists CCC : JFClassDeclaration, find_class (JFCDecl cn (Some j) fields methods :: CC) j = Some CCC).
              { eapply subtype_get_superclass;eauto 1.
                assert (find_class
                          (JFCDecl cn (Some j) fields methods :: CC) cn =
                        Some (JFCDecl cn (Some j) fields methods)).
                apply find_class_eq.
                apply H5.
              }
              destruct H5.
              assert (find_class CC j = Some x). {
                eapply find_class_further_neq.
                assert (cn<>j) by eauto 2 using subtype_well_founded_neq.
                apply H6.
                apply H5.
              }
              destruct x.
              eapply base.
              eapply find_class_in; eauto 1.
              apply subtyping_further.
              eapply IHCC; eauto 2.
              assert (cn<>JFObjectName) by eauto 2.
              eauto 2 using program_contains_further_neq.
          + apply subtyping_further.
            apply IHCC; eauto 2.
            assert (cn1<>JFObjectName) by eauto 2.
            eauto 2 using program_contains_further_neq.
          + destruct (JFClassName_dec cn cn1).
            discriminate H4.
            fold (subtype_class_bool CC cn cn0) in H4.
            apply subtyping_further.
            apply IHCC; eauto 2.
            assert (exists cl, find_class CC cn = Some cl) by eauto 2 using subtype_class_bool_find_class.
            destruct H5.
            eapply subtype_well_founded_contains_object; eauto 2.
      }
      discriminate H4.
  + auto 2.
Qed.

Lemma subtype_bool_correct:
  forall CC Cid Did,
    Well_formed_program CC ->
    subtype_bool CC Cid Did = true ->
    subtyping CC Cid Did.
Proof.
  intros.
  unfold Well_formed_program in *.
  decompose [and] H; clear H.
  eauto 2 using subtype_bool_correct_technical.
Qed.

Lemma extends_get_class_height:
      forall CC name dname,
        extends CC name dname ->
        names_unique CC ->
        (get_class_height CC name) = S (get_class_height CC dname).
Proof.
  induction CC.
  * intros.
    inversion H.
  * intros.
    inversion H.
    ** subst.
       simpl.
       destruct (JFClassName_dec name name);try contradiction.
       eapply names_unique_extends_non_refl in H;auto 1.
       destruct (JFClassName_dec name dname);try contradiction.
       auto 1.
    ** subst.
       assert (cn1 <> name).
       {
         eapply extends_in_first in H5.
         decompose_ex H5.
         eauto 2 using names_unique_in_neq.
       }
       assert (cn1 <> dname).
       {
         eapply extends_in_second in H5.
         decompose_ex H5.
         eauto 2 using names_unique_in_neq.
       }
       generalize H5;intro.
       eapply IHCC in H3;eauto 2.
       simpl.
       destruct dn1 eqn:?.
       *** destruct (JFClassName_dec cn1 name); try contradiction.
           destruct (JFClassName_dec cn1 dname); try contradiction.
           auto 1.
       *** destruct (JFClassName_dec cn1 name); try contradiction.
           destruct (JFClassName_dec cn1 dname); try contradiction.
           auto 1.
Qed.


Lemma find_class_get_class_height_find_class:
  forall CC cn dn en fields methods,
    find_class CC cn = Some (JFCDecl dn (Some en) fields methods) ->
    names_unique CC ->
    subtype_well_founded CC ->
    exists edecl,
      find_class CC en = Some edecl.
Proof.
  destruct CC.
  + intros.
    discriminate H.
  + intros.
    destruct j.
    simpl.
    generalize H;intros.
    simpl in H.
    destruct (JFClassName_dec cn0 cn).
    +++ subst.
        injection H;intros.
        subst.
        generalize H2;intros.
        eapply subtype_get_superclass in H3;eauto.
    +++ eapply find_class_further_neq in H2;eauto 2.
        eapply subtype_get_superclass in H2;eauto 2.
        destruct (JFClassName_dec cn0 en);eauto 2.
Qed.

Lemma find_class_flds_aux:
  forall n CC cn C flds,
    find_class CC cn = Some C ->
    get_class_height CC cn = n ->
    subtype_well_founded CC ->
    names_unique CC ->
    exists flds', flds_aux CC cn n flds = Some flds'.
Proof.
  induction n.
  + intros.
    eapply find_class_get_class_height in H.
    congruence.
  + intros.
    simpl.
    rewrite H.
    destruct C.
    destruct ex.
    ++ generalize H;intros.
       eapply find_class_get_class_height_find_class in H;eauto.
       destruct H.
       assert (extends CC cn j). {
         eapply find_class_extends;eauto 1. 
         assert (cn=cn0) by eauto 2 using find_class_eq_name.
         subst.
         eauto 2 using subtype_well_founded_find_class_neq.
       }
       generalize H4;intros.
       eapply extends_in_second in H4.
       destruct H4 as [ex0 [fields' [methods' Inj]]].
       eapply in_find_class in Inj;eauto.
       eapply extends_get_class_height in H5;eauto.
       rewrite H0 in H5.
       injection H5;intros.
       eapply IHn;eauto 2.
    ++ eauto 2.
Qed.


Lemma flds_overline_extends_decompose:
  forall CC cname dname fldlst,
    extends CC cname dname ->
    object_is_not_extended CC ->
    names_unique CC ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    flds_overline CC (JFClass dname) = Some fldlst ->
    exists fldsn,
      flds_overline CC (JFClass cname) = Some (fldsn ++ fldlst).
Proof.
  intros.
  simpl.
  simpl in H3.
  destruct (get_class_height CC cname) eqn:?.
  + assert
      (exists (fields : list JFFieldDeclaration) (methods : list JFMethodDeclaration), In (JFCDecl cname (Some dname) fields methods) CC)
      by eauto 2 using extends_in_first.
    destruct H5 as [fields [methods]].
    assert (get_class_height CC cname <> 0) by eauto 2 using get_class_height_non_zero.
    contradiction.
  + replace fldlst with ([] ++ fldlst) in H4 by apply app_nil_l.
    generalize H;intros.
    eapply flds_aux_extends in H; eauto 1.
    replace (S n) with (n+1) by auto 1 using NPeano.Nat.add_1_r.
    destruct H.
    eexists.

    erewrite extends_get_class_height in Heqn; try apply H; eauto 1.
    injection Heqn;intros.
    rewrite <- H6. eauto 1.
Qed.


Lemma ex_not_circular :
  forall CC cname dname flds mthds,
    In (JFCDecl cname (Some dname) flds mthds) CC ->
    names_unique CC ->
    subtype_well_founded CC ->
    cname <> dname.
Proof.      
  induction CC; auto.
  intros until 0; intros [|].
  + subst.
    intros Hu Hs.
    red in Hs.
    edestruct (Hs cname) as [n Hd].
    { simpl.
      destruct JFClassName_dec; try contradiction.
      eauto.
    }
    intro.
    subst.
    rewrite names_unique_number_of_extends_loop in Hd; congruence; eauto 1.
  + eauto 4 using subtype_well_founded_further, names_unique_further.
Qed.


Lemma flds_overline_decl_extends_decompose:
  forall CC cname dname fldlst flds mthds,
    In (JFCDecl cname (Some dname) flds mthds) CC ->
    object_is_not_extended CC ->
    names_unique CC ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    flds_overline CC (JFClass dname) = Some fldlst ->
      flds_overline CC (JFClass cname) = Some (flds ++ fldlst).
Proof.
  intros until 0.
  intros HIn ? ? ? ? Hdf.
  simpl.
  destruct (get_class_height CC cname) eqn:?.
  + eapply get_class_height_non_zero in Heqn; eauto 1; contradiction.
  + assert (exists ddecl, find_class CC dname = Some ddecl) as Hfd.
    { 
      simpl in Hdf.
      unfold flds_aux in Hdf;
      destruct get_class_height in Hdf; destruct find_class eqn:Hfceq; try congruence; eauto.
    }
    destruct Hfd as [ddecl Hfd].
    generalize HIn; intro Hfc.
    eapply in_find_class in Hfc; eauto 1.
    assert (extends CC cname dname) as Hext.
    {
      eapply find_class_extends; eauto 1.
      eapply ex_not_circular; eauto 1.
    }
    simpl.
    rewrite Hfc.
    Transparent flds_of_cd.
    simpl.
    simpl in Hdf.
    generalize Hext; intro Hext'.
    apply extends_get_class_height in Hext'; eauto 1.
    rewrite Heqn in Hext'.
    injection Hext'; clear Hext'; intro Heq.
    rewrite <- (app_nil_l []) in Hdf.
    replace fldlst with ([] ++ [] ++ fldlst) in Hdf by trivial. 
    eapply flds_aux_decompose_first_same in Hdf.
    simpl in Hdf.
    rewrite Heq; eassumption.
Qed.


Lemma flds_overline_decompose:
  forall CC C D fldlst,
    subtyping CC D C ->
    flds_overline CC C = Some fldlst ->
    object_is_not_extended CC ->
    names_unique CC ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    C <> JFObject ->
    D <> JFBotClass ->
    exists fldsn,
      flds_overline CC D = Some (fldsn ++ fldlst).
Proof.
  induction 1.
  + eexists.
    replace fldlst with ([] ++ fldlst) in H by eauto using app_nil_l.
    eauto 1.
  + contradiction.
  + contradiction.
  + intros.
    assert (exists fldsn, flds_overline CC D = Some (fldsn ++ fldlst)). {
      eapply IHsubtyping;eauto 1.
      rewrite H0.
      discriminate.
    }
    destruct H10.
    rewrite H0 in H10.
    rewrite H.
    eapply flds_overline_extends_decompose in H1; try apply H10; eauto 1.
    destruct H1.
    rewrite H1.
    eexists.
    rewrite app_assoc.
    auto 1.
Qed.


Lemma flds_overline_find_class_decompose:
    forall CC C D,
      subtyping CC D C ->
      forall dname decl fldlst,
        D = (JFClass dname) ->
        flds_overline CC C = Some fldlst ->
        object_is_not_extended CC ->
        names_unique CC ->
        subtype_well_founded CC ->
        extensions_in_all_but_object CC ->
        find_class CC dname = Some decl ->
        exists fldsn,
          flds_overline CC (JFClass dname) = Some (fldsn ++ fldlst).
Proof.
  induction 1.
  + eexists.
    rewrite H in H0.
    replace fldlst with ([] ++ fldlst) in H0 by eauto using app_nil_l.
    eauto 1.
  + intros.
    assert (subtyping CC C C);eauto.
    generalize H5;intros.
    eapply find_class_flds_aux in H5;eauto.
    destruct H5.
    replace (get_class_height CC dname + 0) with (get_class_height CC dname) in H5 by auto with zarith.
    replace (flds_aux CC dname (get_class_height CC dname) [])
    with (flds_overline CC C) in H5 by (rewrite H;simpl;auto).
    destruct (JFCId_dec C JFObject).
    ++ subst.
       rewrite e in *.
       replace fldlst with ([] ++ fldlst) in H0 by eauto using app_nil_l.
       eexists;eauto.
    ++ eapply flds_overline_decompose in H6;eauto; try (rewrite H;congruence).
       simpl.
       assert (exists flds', flds_aux CC dname (get_class_height CC dname) [] = Some flds'). {
         eapply find_class_flds_aux;eauto.
       }
       simpl in H0.
       replace fldlst with ([] ++ fldlst) in H0 by eauto using app_nil_l.
       destruct H8.
       replace x0 with ([] ++ x0) in H8 by eauto using app_nil_l.
       generalize H8;intros.
       eapply flds_aux_decompose_object in H8;eauto.
       rewrite H9.
       destruct H8.
       rewrite H8.
       rewrite <- app_ass.
       eexists;eauto.
       eapply subtype_well_founded_contains_object; eauto.
  + intros. discriminate H.
  + intros. 
    generalize H0;intros.
    generalize H1;intros.
    eapply  extends_in_second in H11;eauto.
    destruct H11 as [ex0 [fields' [methods']]].
    eapply in_find_class in H11;eauto.
    eapply IHsubtyping in H10;eauto.
    simpl.
    rewrite H in H3;injection H3;intros;subst;clear H3.
    replace (get_class_height CC dname) with ((get_class_height CC dn) +1) by
        (replace (get_class_height CC dn + 1) with (S (get_class_height CC dn)) by
            auto with zarith;
         symmetry;
         eapply extends_get_class_height;eauto).
    generalize H1;intros.
    destruct H10.
    simpl in H.
    replace  (x ++ fldlst) with  ([] ++ x ++ fldlst) in H by eauto using app_nil_l.
    eapply flds_aux_extends in H0;eauto.
    destruct H0.
    rewrite H0.
    rewrite app_nil_l.
    rewrite <- app_ass.
    eexists;eauto.
Qed.

  
Lemma flds_overline_subtyping:
  forall CC C D,
    subtyping CC C D ->
    subtype_well_founded CC ->
    names_unique CC ->
    extensions_in_all_but_object CC ->
    forall cname flds,
    flds_overline CC D = Some flds ->
    D <> JFObject -> 
    C = JFClass cname ->
    exists flds',
    flds_overline CC (JFClass cname) = Some flds'.
Proof.
  intros CC C D. 
  induction 1  using subtyping_ind.
  + intros Swf Nuq Eiabo cname flds Flds Dneq Ceq.
    exists flds.
    subst.
    auto 1.
  + contradiction.
  + intros. discriminate H4.
  + subst. intros Swf Nuq Eiabo name flds.
    intros Flds' Eneq Nameq.
    injection Nameq;intros;clear Nameq.
    subst.
    destruct E.
    ++ eapply IHsubtyping in Flds'; try trivial.
       destruct Flds'.
       unfold flds_overline in H.
       simpl.
       generalize H1;intros.
       eapply extends_get_class_height in H0;eauto 1.
       rewrite H0.
       replace  (S (get_class_height CC dn)) with ((get_class_height CC dn) + 1)  by auto 1 using NPeano.Nat.add_1_r.
       generalize H1;intros.
       replace x with ([] ++ x) in H by auto 1 using app_nil_l.
       eapply flds_aux_extends in H3; try apply H;eauto 1.
       destruct H3.
       rewrite H3.
       eexists.
       auto 1.
    ++ simpl in Flds'.
       discriminate Flds'.
Qed.


Lemma lookup_cons_neq:
  forall CC cn dn ex fields methods m md,
    cn <> dn ->
    methodLookup (JFCDecl cn ex fields methods :: CC) dn m = Some md ->
    methodLookup  CC dn m = Some md.
Proof.
  intros.
  unfold methodLookup in H0.
  fold methodLookup in *.
  destruct (JFClassName_dec dn cn); try congruence.
Qed.

Lemma lookup_in_supertype_subtype_extends:
  forall CC cname dname m md,
    names_unique CC ->
    extends CC cname dname ->
    methodLookup CC dname m = Some md ->
    exists md' : JFMethodDeclaration,
      methodLookup CC cname m = Some md'.
Proof.
  induction CC; intros cname dname m md.
  * intros Nuq Exts mthLkp.
    inversion Exts.
  * intros Nuq Exts mthLkp.
    unfold methodLookup in mthLkp.
    unfold methodLookup.
    fold methodLookup in *.
    destruct a.
    destruct (JFClassName_dec cname cn).
    ** destruct (find_method methods m).
       *** exists j. auto.
       *** destruct ex.
           + subst.
             destruct (JFClassName_dec dname cn).
             ++ firstorder.
             ++ assert (dname = j) by eauto using extends_equals_first.
                rewrite H in mthLkp.
                firstorder.
           + subst.
             inversion Exts.
             subst.
             assert (count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0) by eauto.
             assert (exists (ex0 : JFClassName) (fields' : list JFFieldDeclaration) (methods' : list JFMethodDeclaration),
                        In (JFCDecl cn (Some ex0) fields' methods') CC) by eauto using extends_in_first.
             destruct H0 as [ex0 [fields' [methods' H0]]].
             assert (names_unique CC) by eauto 2.
             unfold names_unique in H1.
             assert (forall x, In x CC -> decl_once CC x).
             apply Forall_forall;auto.
             apply H2 in H0.
             unfold decl_once in H0.
             unfold name_once in H0.
             congruence.
   ** destruct (JFClassName_dec dname cn).
      *** subst. clear -Nuq Exts n.
          assert (exists (ex0 : option JFClassName) (fields' : list JFFieldDeclaration) (methods' : list JFMethodDeclaration),
                     In (JFCDecl cn ex0 fields' methods') CC).
          eapply extends_in_second_second.
          apply Exts.
          eauto.
          destruct H as [ex0 [fields' [methods' H]]].
          assert (names_unique CC) by eauto.
          unfold names_unique in H0.
          assert (forall x, In x CC -> decl_once CC x).
          apply Forall_forall;auto.
          apply H1 in H.
          unfold decl_once in H.
          unfold name_once in H.
          assert (count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0) by eauto.
          congruence.
      *** inversion Exts.
           + subst. contradiction.
           + subst.
             eapply IHCC;eauto 2.
Qed.

Lemma lookup_in_object_subtype:
  forall CC cn m md cd,
    names_unique CC ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    methodLookup CC JFObjectName m = Some md ->
    find_class CC cn = Some cd ->
    exists md' : JFMethodDeclaration, methodLookup CC cn m = Some md'.
Proof.
  induction CC.
  * intros.
    simpl in H2.
    discriminate H2.
  * intros.
    destruct a.
    destruct (JFClassName_dec JFObjectName cn0).
    ** subst.
       destruct (JFClassName_dec JFObjectName cn).
       *** subst. firstorder.
       *** assert (program_contains CC JFObjectName = true).
           assert (find_class CC cn = Some cd)
             by eauto using find_class_further_neq.
           eapply subtype_well_founded_contains_object;eauto 2.
           assert (count_occ Bool.bool_dec
                             (map (is_class_name JFObjectName) CC) true > 0)
             by eauto using program_contains_counts_occ.
           apply names_unique_zero in H.
           rewrite H in H5.
           apply Gt.gt_irrefl in H5.
           contradiction.
    ** unfold methodLookup in H2.
       unfold methodLookup.
       fold methodLookup in *.
       destruct (JFClassName_dec JFObjectName cn0); try contradiction.
       destruct (JFClassName_dec cn cn0).
       *** subst.
           destruct (find_method methods m).
           + exists j;trivial.
           + destruct ex.
             ++ assert (exists jd : JFClassDeclaration,
                           find_class (JFCDecl cn0 (Some j) fields methods :: CC)
                                      j = Some jd).
                {
                  destruct cd.
                  assert (ex = Some j).
                  {
                    simpl in H3.
                    destruct (JFClassName_dec cn0 cn0);try contradiction.
                    injection H3;intros;intuition.
                  }
                  eapply subtype_get_superclass;try apply H3;eauto 2.
                  subst.
                  apply H3.
                }
                destruct H4.
                apply(IHCC j m md x);eauto 2.
                destruct (JFClassName_dec cn0 j).
                +++ subst.
                    assert (j<>j) by eauto 2 using subtype_well_founded_neq.
                    contradiction.
                +++ eauto using find_class_further_neq.
             ++ unfold extensions_in_all_but_object in H1.
                apply Forall_inv in H1.
                simpl in H1.
                rewrite H1 in *. contradiction.
         *** eapply IHCC;eauto 2.
             eapply find_class_further_neq;eauto 2.
Qed.

                    
Lemma lookup_in_supertype_subtype:
  forall CC C D, 
    subtyping CC C D ->
    names_unique CC ->
    object_is_not_extended CC ->
    subtype_well_founded CC ->
    extensions_in_all_but_object CC ->
    forall cn dn m md cd,
    C = JFClass cn ->
    D = JFClass dn ->
    find_class CC cn = Some cd ->
    methodLookup CC dn m = Some md ->
    exists md',
      methodLookup CC cn m = Some md'.
Proof.
  intros CC C D.
  intro.
  induction H.
  * intros.
    subst.
    assert (cn=dn) by congruence.
    subst.
    clear -H6.
    firstorder.
  * intros.
    eapply lookup_in_object_subtype;eauto.
    injection H4;intros.
    rewrite <- H7 in *.
    eauto.
  * intros.
    inversion H3.
  * intros.
    subst.
    injection H7;intros;clear H7;subst.
    destruct (JFClassName_dec dn cn0).
    ** subst.
       assert (cn0<>cn0) by eauto using names_unique_extends_non_refl.
       contradiction.
    ** assert (exists cd, find_class CC dn = Some cd).
       assert (exists
                  (ex0 : option JFClassName)
                  (fields' : list JFFieldDeclaration) 
                  (methods' : list JFMethodDeclaration),
                  In (JFCDecl dn ex0 fields' methods') CC)
         by eauto using extends_in_second.
       do 3 destruct H.
       exists (JFCDecl dn x x0 x1).
       eauto using in_find_class.
       destruct H.
       assert (exists md' : JFMethodDeclaration,
                 methodLookup CC dn m = Some md').
       eapply IHsubtyping;try apply H10;
         eauto using lookup_in_supertype_subtype_extends.
       destruct H0.
       eauto using lookup_in_supertype_subtype_extends.
Qed.
