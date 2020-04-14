Require Import JaSyntax.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import NPeano.
Require Import PeanoNat.
Require Export Arith.
Open Scope nat_scope.
Require Import JaTactics.

From Hammer Require Import Reconstr.



(* Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zorder. *)


(** The boolean function that returns [true] when [cname] is the name of the class declared as [cdecl]. *)
Definition is_class_name cn cd :=
  match cd with
    | JFCDecl dn _ _ _ => if JFClassName_dec dn cn then true else false
  end.

Lemma is_class_name_name:
  forall cn ex fields methods,
    is_class_name cn (JFCDecl cn ex fields methods) = true.
Proof.
  intros.
  unfold is_class_name.
  destruct (JFClassName_dec cn cn).
  auto.
  tauto.
Qed.

Lemma is_class_name_name_cd:
  forall cd,
    is_class_name (name_of_cd cd) cd = true.
Proof.
  intros.
  destruct cd.
  unfold name_of_cd.
  unfold is_class_name.
  destruct (JFClassName_dec cn cn); try contradiction;auto.
Qed.


Lemma is_class_name_neq:
  forall cn dn ex fields methods,
    cn<>dn ->
    is_class_name cn (JFCDecl dn ex fields methods) = false.
Proof.
  intros.
  unfold is_class_name.
  destruct (JFClassName_dec dn cn).
  auto.
  rewrite e in *.
  tauto.
  auto.
Qed.


Lemma is_class_name_equal:
  forall cn dn ex fields methods,
    is_class_name cn (JFCDecl dn ex fields methods) = true ->
    cn = dn.
Proof.
  intros.
  unfold is_class_name in H.
  destruct (JFClassName_dec dn cn).
  auto.
  discriminate H.
Qed.

Lemma is_class_name_nequal:
  forall cn dn ex fields methods,
    is_class_name cn (JFCDecl dn ex fields methods) = false ->
    cn <> dn.
Proof.
  intros.
  unfold is_class_name in H.
  destruct (JFClassName_dec dn cn).
  discriminate H.
  auto.
Qed.

Lemma program_contains_counts_occ:
  forall CC cn, 
    program_contains CC cn = true ->
    (count_occ Bool.bool_dec (map (is_class_name cn) CC) true > 0)%nat.
Proof.
  induction CC.
  * intros.
    simpl in H.
    discriminate H.
  * intros.
    destruct a.
    destruct (JFClassName_dec cn0 cn).
    ** subst.
       rewrite map_cons.
       unfold is_class_name.
       destruct (JFClassName_dec cn cn); try contradiction.
       rewrite count_occ_cons_eq; auto. 
       auto with zarith.
    ** rewrite map_cons.
       unfold is_class_name.
       destruct (JFClassName_dec cn0 cn); subst; try contradiction.
       rewrite count_occ_cons_neq; auto.
       fold (is_class_name cn0).
       apply IHCC;eauto 2.
       eapply program_contains_further_neq;eauto.
Qed.

(** The property to check that class name [cname] occurs only once in the program [P]. *)
Definition name_once (CC:JFProgram) (cn:JFClassName) :=
 count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 1%nat.

Lemma in_head_not_in_tail:
  forall (CC:JFProgram) (cn:JFClassName) (cd:JFClassDeclaration),
    (is_class_name cn cd) = true ->
    name_once (cd :: CC) cn -> ~ name_once CC cn.
Proof.
  induction CC.
  * intros.
    compute.
    intro.
    discriminate H1.
  * intros.
    unfold name_once in H0.
    rewrite map_cons in H0.
    rewrite H in H0.
    rewrite count_occ_cons_eq in H0.
    set (XX := (count_occ Bool.bool_dec (map (is_class_name cn) (a :: CC)) true)) in H0.
    injection H0.
    intros.
    unfold XX in *.
    intro.
    unfold name_once in H2.
    rewrite H1 in H2.
    discriminate H2.
    auto.
Qed.

Lemma name_once_further:
  forall cn dn CC ex fields methods,
  cn<>dn ->
  name_once (JFCDecl cn ex fields methods :: CC) dn -> name_once CC dn.
Proof.
  intros.
  unfold name_once in H0.
  rewrite map_cons in H0.
  rewrite is_class_name_neq in H0.
  rewrite count_occ_cons_neq in H0.
  auto.
  auto.
  auto.
Qed.

Lemma name_once_further_neq:
  forall cn dn CC ex ms fs,
    cn <> dn ->
    name_once CC dn ->
    name_once (JFCDecl cn ex ms fs :: CC) dn.
Proof.
  intros.
  unfold name_once in *.
  rewrite map_cons.
  rewrite is_class_name_neq; auto.
Qed.

Lemma name_once_further_eq:
  forall cn CC ex fields methods,
    count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0%nat ->
    name_once (JFCDecl cn ex fields methods :: CC) cn.
Proof.
  unfold name_once.
  intros.
  rewrite map_cons.
  rewrite is_class_name_name.
  rewrite count_occ_cons_eq; auto.
Qed.

Lemma count_occ_zero_is_class_name_false:
  forall CC cn cd,
    count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0%nat ->
    In cd CC ->
    is_class_name cn cd = false.
Proof.
  induction CC.
  * intros.
    unfold In in H0.
    tauto.
  * intros.
    apply in_inv in H0.
    destruct H0.
    - rewrite H0 in *.
      rewrite map_cons in H.
      apply <- count_occ_not_In in H.
      apply not_in_cons in H.
      destruct H.
      destruct (is_class_name cn cd).
      + tauto.
      + auto.
    - apply IHCC.
      rewrite map_cons in H.
      assert (is_class_name cn a <> true).
      apply <- count_occ_not_In in H.
      apply not_in_cons in H.
      intuition.
      rewrite <- (count_occ_cons_neq  Bool.bool_dec (map (is_class_name cn) CC) H1).
      auto.
      trivial.
Qed.



(** The property to check that declaraion [cdecl] occurs only once in the program [P]. *)
Definition decl_once (CC:JFProgram) (cd:JFClassDeclaration) :=
  match cd with
    | JFCDecl cn _ _ _ => name_once CC cn
  end.

Lemma count_occ_zero_decl_once:
  forall CC cn ex ms fs ex1 ms1 fs1,
    count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0%nat ->                                                         
    decl_once (JFCDecl cn ex ms fs :: CC) (JFCDecl cn ex1 ms1 fs1).
Proof.
  intros.
  unfold decl_once.
  apply name_once_further_eq.
  auto.
Qed.

Lemma decl_in_head_not_in_tail:
  forall (CC:JFProgram) (cn:JFClassName) (cd:JFClassDeclaration),
    (is_class_name cn cd) = true ->
    (decl_once (cd :: CC) cd) ->
    ~ (decl_once CC cd).
Proof.
  intros.
  unfold decl_once in *.
  destruct cd.
  unfold is_class_name in H.
  destruct (JFClassName_dec cn0 cn).
  rewrite e in *.
  apply (in_head_not_in_tail CC cn (JFCDecl cn ex fields methods)).
  apply is_class_name_name.
  auto.
  discriminate H.
Qed.



Lemma decl_in_head_false_in_tail:
  forall (CC:JFProgram) (cn:JFClassName) (cd:JFClassDeclaration),
    (is_class_name cn cd) = true ->
    (decl_once (cd :: CC) cd) ->
    Forall (fun x0 => is_class_name cn x0 = false) CC.
Proof.
  intros.
  unfold decl_once in *.
  destruct cd.
  apply is_class_name_equal in H.
  rewrite H in *.
  unfold name_once in H0.
  rewrite map_cons in H0.
  rewrite is_class_name_name in H0.
  rewrite count_occ_cons_eq in H0; auto.
  injection H0; intros.
  apply Forall_forall.
  intros.
  eapply count_occ_zero_is_class_name_false; try apply H1; auto.
Qed.

Lemma decs_once_monotone:
  forall (CC:JFProgram) (cd:JFClassDeclaration)
         (dd:JFClassDeclaration) (cn:JFClassName),
    decl_once (cd :: CC) dd ->
    is_class_name cn cd = true ->
    is_class_name cn dd = false ->
    decl_once CC dd.
Proof.
  intros.
  unfold decl_once.
  destruct dd.
  unfold decl_once in H.
  destruct cd.
  apply is_class_name_equal in H0.
  rewrite H0 in *.
  eapply name_once_further.
  apply is_class_name_nequal in H1.
  eapply H1.
  apply H.
Qed.
  
(** The property that all class names occur in the program uniquely. *)
Definition names_unique (CC:JFProgram) :=
  Forall (decl_once CC) CC.

Lemma names_unique_zero:
  forall CC cn ex fields methods,
    names_unique (JFCDecl cn ex fields methods :: CC) ->
    count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0%nat.
Proof.
  intros.
  unfold names_unique in H.
  apply Forall_inv in H.
  unfold decl_once in H.
  unfold name_once in H.
  rewrite map_cons in H.
  rewrite is_class_name_name in H.
  rewrite count_occ_cons_eq in H; auto.
Qed.

Lemma names_unique_cons:
  forall CC cn ex ms fs,
    count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0%nat ->
    names_unique CC ->
    names_unique (JFCDecl cn ex ms fs :: CC).
Proof.
  intros.
  unfold names_unique.
  apply Forall_cons.
  + apply count_occ_zero_decl_once.
    auto.
  + apply Forall_forall.
    intros.
    unfold names_unique in H0.
    assert (forall y, In y CC -> (decl_once CC) y).
    apply (Forall_forall (decl_once CC) CC).
    auto.
    destruct x.
    assert (is_class_name cn (JFCDecl cn0 ex0 fields methods) = false). {
      eapply count_occ_zero_is_class_name_false.
      apply H.
      auto.
    }
    apply (is_class_name_nequal) in H3.
    unfold decl_once.
    apply name_once_further_neq; auto.
    assert (decl_once CC (JFCDecl cn0 ex0 fields methods)).
    apply H2; auto.
    unfold decl_once in H4; auto.
Qed.

Lemma names_unique_further:
  forall (CC:JFProgram) (cd:JFClassDeclaration),
    names_unique (cd :: CC) ->
    names_unique CC.
Proof.
  intros.
  unfold names_unique in H.
  inversion H.
  unfold names_unique.
  assert (forall x, In x CC -> (decl_once CC) x).
  intros.
  assert (forall x, In x CC -> (decl_once (cd :: CC)) x).
  apply -> (Forall_forall (decl_once (cd :: CC)) CC).
  auto.
  assert (decl_once (cd :: CC) x0).
  apply H5.
  auto.
  destruct cd.
  apply (decs_once_monotone CC (JFCDecl cn ex fields methods) x0 cn).
  auto.
  unfold is_class_name.
  destruct (JFClassName_dec cn cn).
  auto.
  tauto.
  assert (Forall (fun x0 => is_class_name cn x0 = false) CC).
  apply (decl_in_head_false_in_tail CC cn (JFCDecl cn ex fields methods)).
  unfold is_class_name.
  destruct (JFClassName_dec cn cn);auto.
  auto.
  assert (forall x, In x CC -> (is_class_name cn x = false)).
  apply Forall_forall.
  auto.
  apply H8.
  auto.
  apply Forall_forall.
  auto.
Qed.

Lemma names_unique_decompose_program:
  forall (CC1 CC2:JFProgram),
    names_unique (CC1 ++ CC2) ->
    names_unique CC2.
Proof.
  induction CC1.
  + intros.
    simpl in *.
    auto.
  + intros.
    simpl in H.
    unfold names_unique in H.
    apply IHCC1.
    unfold names_unique.
    assert (forall x, In x (a :: CC1 ++ CC2) -> (decl_once (a :: CC1 ++ CC2)) x)
      by (apply -> Forall_forall;auto).
    apply <- Forall_forall.
    intros.
    destruct (JFClassName_dec (name_of_cd a) (name_of_cd x)).
    ++ subst.
       assert (decl_once (a :: CC1 ++ CC2) a) by eauto using in_eq.
       assert (decl_once (a :: CC1 ++ CC2) x).
       {
         unfold decl_once.
         unfold decl_once in H2.
         destruct x.
         destruct a.
         simpl in e.
         rewrite <- e.
         auto.
       }
       assert (decl_once (x :: CC1 ++ CC2) x).
       {
         unfold decl_once.
         unfold decl_once in H3.
         destruct x.
         destruct a.
         simpl in e.
         rewrite e in H3.
         unfold name_once.
         unfold name_once in H3.
         simpl in H3.
         simpl.
         auto.
       }
       assert (~ decl_once (CC1 ++ CC2) x).
       {
         apply (decl_in_head_not_in_tail (CC1 ++ CC2) (name_of_cd x)).
         apply is_class_name_name_cd; auto.
         auto.
       } 
       destruct x.
       assert (In (is_class_name cn (JFCDecl cn ex fields methods))
                  (map (is_class_name cn) (CC1 ++ CC2))) by eauto using in_map.
       assert (count_occ Bool.bool_dec (map (is_class_name cn) (CC1 ++ CC2))
                         (is_class_name cn (JFCDecl cn ex fields methods)) > 0)
         by (apply count_occ_In; eauto).
       unfold decl_once in H4.
       unfold name_once in H4.
       simpl in H4.
       simpl in H7.
       destruct (JFClassName_dec cn cn);try contradiction.
       destruct (Bool.bool_dec true true);try contradiction.
       injection H4;intros.
       rewrite H8 in H7.
       apply gt_irrefl in H7.
       contradiction.
    ++ eapply decs_once_monotone.
       apply H0.
       apply in_cons;auto.
       apply is_class_name_name_cd.
       unfold is_class_name.
       destruct x.
       destruct (JFClassName_dec cn (name_of_cd a)).
       +++ rewrite <-  e in n.
           simpl in n.
           contradiction.
       +++ trivial.
Qed.

Lemma names_unique_further_further:
  forall (CC:JFProgram) (cd dd:JFClassDeclaration),
    names_unique (cd::dd::CC) ->
    names_unique (cd::CC).
Proof.
  intros.
  destruct cd.
  apply  names_unique_cons.
  - apply (names_unique_zero CC cn ex fields methods).
    apply (names_unique_cons).
    assert (count_occ Bool.bool_dec (map (is_class_name cn)
                                         (dd :: CC)) true = 0). {
      apply (names_unique_zero (dd :: CC) cn ex fields methods).
      auto.
    }
    rewrite map_cons in H0.
    destruct (is_class_name cn dd).
    rewrite count_occ_cons_eq in H0; discriminate H0; auto.
    rewrite count_occ_cons_neq in H0; auto.
    eauto using names_unique_further.
  - eauto using names_unique_further.
Qed.

Lemma count_zero_count_nzero:
  forall CC cn ex fields methods,
         count_occ JFClassDeclaration_dec CC
         (JFCDecl cn ex fields methods) > 0 ->
         count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0 ->
         False.
Proof.
  induction CC; intros.
  - rewrite count_occ_nil in H.
    assert (0<>0).
    apply Lt.lt_0_neq.
    auto.
    tauto.
  - destruct a.
    destruct (JFClassName_dec cn0 cn).
    + rewrite e in *.
      rewrite map_cons in H0.
      rewrite is_class_name_name in H0.
      rewrite count_occ_cons_eq in H0.
      discriminate H0.
      auto.
    + rewrite map_cons in H0.
      rewrite is_class_name_neq in H0.
      rewrite count_occ_cons_neq in H0.
      rewrite count_occ_cons_neq in H.
      eauto using IHCC.
      congruence.
      congruence.
      auto.
Qed.

Lemma names_unique_find_class_unique:
  forall CC cn cd cd',
         names_unique CC ->
         find_class CC cn = Some cd ->
         find_class CC cn = Some cd' ->
         cd = cd'.
Proof.
  induction CC.
  + intros.
    simpl in H0.
    discriminate H0.
  + intros.
    destruct a.
    destruct (JFClassName_dec cn cn0).
    ++ subst.
       simpl in H1.
       simpl in H0.
       destruct (JFClassName_dec cn0 cn0); try contradiction.
       rewrite H0 in *.
       injection H1.
       tauto.
    ++ apply find_class_further_neq in H0; auto.
       apply find_class_further_neq in H1; auto.
       eapply IHCC;eauto using names_unique_further.
Qed.
  
Hint Resolve names_unique_zero names_unique_cons names_unique_further names_unique_further_further names_unique_decompose_program count_zero_count_nzero is_class_name_name is_class_name_name_cd names_unique_find_class_unique.
     
Lemma in_names_unique_eq:
  forall CC cn ex fields methods ex0 fields0 methods0,
    In (JFCDecl cn ex fields methods)
       (JFCDecl cn ex0 fields0 methods0 :: CC) ->
    names_unique  (JFCDecl cn ex0 fields0 methods0 :: CC) ->
    (ex = ex0 /\ fields = fields0 /\ methods = methods0).
Proof.
  intros.
  simpl in H.
  destruct H.
  - injection H; auto.
  - apply -> (count_occ_In JFClassDeclaration_dec) in H.
    apply names_unique_zero in H0.
    clear -H H0.
    auto with zarith.
    assert False by eauto.
    tauto.
Qed.

Hint Resolve  in_names_unique_eq.

Lemma is_class_and_occ_zero:
  forall CC cn dn cd, names_unique CC ->
            find_class CC cn = Some cd ->
            count_occ Bool.bool_dec (map (is_class_name dn) CC) true = 0 ->
            cn <> dn.
Proof.
  induction CC.
  + sauto.
  + intros.
    destruct a.
    assert ({cn=dn} + {cn<>dn}) by apply JFClassName_dec.
    destruct H2.
    * rewrite e in *.
      rewrite map_cons in H1.
      unfold is_class_name in H1.
      destruct (JFClassName_dec cn0 dn).
      - pose count_occ_cons_eq; scrush.
      - pose count_occ_cons_neq; pose names_unique_further;
          pose find_class_further_neq; scrush.
    * auto.
Qed.

Lemma names_unique_count_class_name:
  forall CC cn ex flds mthds,
    names_unique CC ->
    count_occ Bool.bool_dec (map (is_class_name cn) CC)
              true = 0 ->
    count_occ JFClassDeclaration_dec CC (JFCDecl cn ex flds mthds) = 0.
Proof.
  induction CC.
  - intros; simpl; auto.
  - intros.
    rewrite map_cons in H0.
    destruct (Bool.bool_dec (is_class_name cn a) true).
    + rewrite count_occ_cons_eq in H0; auto.
      discriminate H0.
    + rewrite count_occ_cons_neq.
      eapply IHCC.
      eauto using names_unique_further.
      rewrite count_occ_cons_neq in H0; auto.
      destruct a.
      assert (is_class_name cn (JFCDecl cn0 ex fields methods) = false).
      simpl in n.
      destruct (JFClassName_dec cn0 cn).
      tauto.
      simpl. destruct (JFClassName_dec cn0 cn); tauto.
      apply is_class_name_nequal in H1.
      congruence.
Qed.      

Lemma in_find_class_raw:
  forall CC cn ex fields methods,
    In (JFCDecl cn ex fields methods) CC ->
    exists ex1 fields1 methods1,
    find_class CC cn = Some (JFCDecl cn ex1 fields1 methods1).
Proof.
  induction CC.
  * intros.
    inversion H.
  *  intros.
     destruct (JFClassDeclaration_dec (JFCDecl cn ex fields methods) a).
     ** rewrite <- e.
        simpl.
        destruct (JFClassName_dec cn cn); try contradiction.
        clear.
        do 3 eexists.
        auto.
     ** simpl.
        destruct a.
        destruct (JFClassName_dec cn0 cn).
        *** subst.
            clear. do 3 eexists. auto.
        *** eapply IHCC.
            eapply in_inv in H.
            destruct H.
            + injection H;intros;clear H.
              contradiction.
            + eauto.
Qed.    

Lemma in_find_class:
  forall CC cn ex fields methods,
    names_unique CC ->
    In (JFCDecl cn ex fields methods) CC ->
    find_class CC cn = Some (JFCDecl cn ex fields methods).
Proof.
  induction CC;intros.
  - assert (~ In (JFCDecl cn ex fields methods) []) by  auto using in_nil.
    tauto.
  - destruct (JFClassDeclaration_dec (JFCDecl cn ex fields methods) a).
    + rewrite <- e. simpl.
      destruct (JFClassName_dec cn cn); eauto.
      tauto.
    + destruct a.
      simpl.
      destruct (JFClassName_dec cn0 cn).
      rewrite e in *.
      assert (ex = ex0 /\ fields = fields0 /\ methods = methods0)
        by eauto.
      decompose [and] H1; clear H1.
      congruence.
      apply in_inv in H0.
      destruct H0.
      injection H0;intros.
      tauto.
      eapply IHCC; eauto.
Qed.

Hint Resolve in_find_class.


Lemma names_unique_in_neq:
  forall CC cn dn ex fields methods ex1 fields1 methods1,
    names_unique (JFCDecl cn ex fields methods :: CC) ->
    In (JFCDecl dn ex1 fields1 methods1) CC ->
    cn <> dn.
Proof.
  intros.
  assert (dn<>cn).
  assert (count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0) by eauto.
  assert (find_class CC dn = Some (JFCDecl dn ex1 fields1 methods1)) by eauto.
  eapply is_class_and_occ_zero.
  eapply names_unique_further; eauto.
  eauto.
  eauto.
  auto.
Qed.



Hint Resolve names_unique_in_neq : myhints.

Lemma names_unique_count_zero:
  forall CC cn ex fields methods,
    names_unique (JFCDecl cn ex fields methods :: CC) ->
    count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0.
Proof.
  scrush.
Qed.




Lemma names_unique_neq_but_in:
  forall CC cd dd,
         In cd (cd :: CC) ->
         dd <> cd ->
         names_unique (cd :: CC) ->
         In dd CC -> name_of_cd dd <> name_of_cd cd.
Proof.
  intros.
  destruct cd.
  destruct dd.
  simpl.
  assert (count_occ Bool.bool_dec (map (is_class_name cn) CC) true = 0) by eauto.
  assert (count_occ Bool.bool_dec (map (is_class_name cn0) CC) true > 0).
  apply count_occ_In.
  assert (names_unique CC) by eauto using names_unique_further.
  unfold names_unique in H4.
  assert (forall x,In x CC -> decl_once CC x) by (apply Forall_forall; auto).
  assert (decl_once CC (JFCDecl cn0 ex0 fields0 methods0)) by auto.
  unfold decl_once in H6.
  unfold name_once in H6.
  assert (count_occ Bool.bool_dec (map (is_class_name cn0) CC) true >0) by
      try (rewrite H6; apply Gt.gt_Sn_O).
  apply <- count_occ_In; eauto.
  intro.
  rewrite H5 in *.
  rewrite H3 in H4.
  apply (Gt.gt_irrefl 0 H4).
Qed.
  

Lemma in_find_class_eq:
  forall CC cd cd',
    names_unique CC ->
    In cd CC ->
    find_class CC (name_of_cd cd) = Some cd' -> cd = cd'.
Proof.
  induction CC;intros.
  - assert (~ In cd []) by  auto using in_nil.
    tauto.
  - destruct (JFClassDeclaration_dec cd a).
    + simpl in H1. rewrite e in *.
      destruct a.
      simpl in H1.
      destruct (JFClassName_dec cn cn);
      try injection H1;
      tauto.
    + assert (names_unique CC) by eauto using names_unique_further.
      assert (a = cd \/ In cd CC) by eauto.
      destruct H3. symmetry in H3. contradiction.
      assert (name_of_cd cd <> name_of_cd a).
      apply (names_unique_neq_but_in CC a cd); auto.
      auto using in_eq.
      assert (find_class CC (name_of_cd cd) = Some cd').
      destruct a.
      eapply find_class_further_neq.
      simpl in H4.
      assert (cn <> name_of_cd cd) by auto.
      eauto.
      eauto.
      apply IHCC; auto.
Qed.



(**
   Calculates the list of fields in an object of the given class name
   [cname] traversing recursively its subtyping hierarchy up to _Object_.
   The parameter [n] is added to ensure the correcntess of
   structural recursion. The parameter [res] contains the triples
   of fields collected so far in possibly earlier computation.

   The function returns [Some] value in case its calculation is
   correct. In case the calculation is not correct (when
   - the structural induction parameter is too small,
   - there is a non _Object_ class, which is not extended,
   - there is no class of the given name in the program),
   the function returns [None].
 *)
Fixpoint flds_aux (CC:JFProgram) cn n res {struct n} : option (list JFFieldDeclaration) := 
  match find_class CC cn with
  | None => None
  | Some cd => 
    let fr := flds_of_cd cd in
    match cd with
    | JFCDecl _ None _ _ => Some (res ++ fr)
    | JFCDecl _ (Some ex) _ _ => 
      match n with
      | 0 => None
      | S k => flds_aux CC ex k (res ++ fr)
      end
    end
  end.


    


Lemma flds_aux_not_object_not_find_class:
  forall CC cn n fds,
    find_class CC cn = None ->
    cn <> JFObjectName ->
    flds_aux CC cn n fds = None.
Proof.
  destruct n.
  * intros. simpl.
    rewrite H.
    auto.
  * intros. simpl.
    rewrite H.
    auto.
Qed.

Lemma flds_aux_not_object_find_class_ex_zero:
  forall CC cn dn fields methods fds,
    find_class CC cn = Some (JFCDecl cn (Some dn) fields methods) ->
    flds_aux CC cn 0 fds = None.
Proof.
  intros.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma flds_aux_not_object_in_first_none:
  forall CC n cn fields methods fds,
    exists flds',
    flds_aux ((JFCDecl cn None fields methods) :: CC) cn n fds = Some flds'.
Proof.
  intros.
  destruct n.
  + simpl.
    destruct_eq.
    eexists.
    auto.
  + simpl.
    destruct_eq.
    eexists.
    auto.
Qed.


Lemma flds_aux_nil:
    forall n CC cn fds, 
      flds_aux CC cn n fds = Some [] ->
      fds = [].
Proof.
  induction n.
  * intros.
    simpl in H.
    destruct (find_class CC cn).
    ** destruct j.
       destruct ex.
       *** discriminate H.
       *** injection H;intros Hnil.
           apply app_eq_nil in Hnil.
           intuition.
    ** discriminate H.
  * intros.
    simpl in H.
    destruct (find_class CC cn).
    ** destruct j.
       destruct ex.
       + assert (fds ++ (flds_of_cd (JFCDecl cn0 (Some j) fields methods))
                 = []) as Hnil by (eapply IHn; eassumption).
         apply app_eq_nil in Hnil.
         intuition.
       + injection H;intros Hnil.
         eapply app_eq_nil in Hnil.
         intuition.
    ** discriminate H.
Qed.

Lemma flds_monotone_n_Sn:
  forall CC n cn fd fds,
         flds_aux CC cn n fd = Some fds ->
         flds_aux CC cn (S n) fd = Some fds.
Proof.
  induction n.
  + intros.
    simpl in H.
    simpl.
    destruct (find_class CC cn); try discriminate H.
    destruct j.
    destruct ex; try discriminate H.
    auto.
  + intros.
    unfold flds_aux.
    fold flds_aux.
    simpl in H.
    destruct (find_class CC cn); try discriminate H.
    destruct j.
    destruct ex; try discriminate H.
    assert (flds_aux CC j (S n) (fd ++ flds_of_cd (JFCDecl cn0 (Some j) fields methods)) = Some fds).
    auto.
    Opaque flds_of_cd.
    simpl in H0.
    auto.
    auto.
Qed.  

Lemma flds_monotone_n:
  forall CC n m cn fd fds,
    flds_aux CC cn n fd = Some fds ->
    m > n ->
    flds_aux CC cn m fd = Some fds.
Proof.
  induction m.
  + intros.
    assert (n >=0) by auto with zarith.
    assert (0 > 0) by auto with zarith.
    assert (0<>0) by auto with zarith.
    contradiction.
  + intros.
    apply flds_monotone_n_Sn.
    assert (m > n \/ n=m) by auto using gt_S.
    destruct H1.
    ++ apply IHm; auto.
    ++ rewrite <- H1.
       auto.
Qed.



Lemma flds_aux_decompose_acc:
  forall n fds fd CC cn, 
    flds_aux CC cn n fd = Some fds ->
    exists fds',
      fds = fd ++ fds'.
Proof.
  induction n.
  * intros.
    simpl in H.
    destruct (find_class CC cn).
    ** destruct j.
       destruct ex.
       *** discriminate H.
       *** injection H;intros.
           rewrite <- H0.
           eexists;auto.
    ** discriminate H.
  * intros.
    simpl in H.
    destruct (find_class CC cn).
    ** destruct j.
       destruct ex.
       *** assert ( exists fds', fds =
                            (fd ++ flds_of_cd (JFCDecl cn0 (Some j) fields methods)) ++ fds').
           {
             eapply IHn.
             apply H. }
           destruct H0.
           rewrite H0.
           eexists.
           auto using app_assoc.
       *** injection H;intros.
           rewrite <- H0.
           eexists. auto.
    ** discriminate H.
Qed.

Lemma flds_aux_decompose_second_same:
  forall n fd1 fd2 fd1' fd' CC cn, 
    flds_aux CC cn n (fd1 ++ fd1') = Some (fd1 ++ fd1' ++ fd') ->
    flds_aux CC cn n (fd2 ++ fd1') = Some (fd2 ++ fd1' ++ fd').
Proof.
  induction n.
  * simpl.
    intros.
    destruct (find_class CC cn); try discriminate H.
    destruct j.
    destruct ex;try discriminate H.
    injection H;intros.
    rewrite app_assoc in H0.
    apply app_inv_head in H0.
    rewrite H0.
    rewrite app_assoc.
    auto.
  * simpl.
    intros.
    destruct (find_class CC cn); try discriminate H.
    destruct j.
    destruct ex;try discriminate H.
    **  rewrite <- 1 app_assoc in H.
        assert (exists ff, fd1 ++ fd1' ++ fd' = (fd1 ++ fd1' ++ (flds_of_cd (JFCDecl cn0 (Some j) fields methods))) ++ ff)
          by eauto 2 using flds_aux_decompose_acc.
        destruct H0.
        rewrite <- 2 app_assoc in H0.
        apply app_inv_head in H0.
        apply app_inv_head in H0.
        rewrite <- app_assoc.
        assert (flds_aux CC j n (fd2 ++ fd1' ++ flds_of_cd (JFCDecl cn0 (Some j) fields methods)) =
               Some (fd2 ++ (fd1'  ++ flds_of_cd (JFCDecl cn0 (Some j) fields methods)) ++ x)). {
         eapply IHn.
         rewrite H.
         rewrite H0.
         repeat rewrite app_assoc.
         auto 1.
        }
        rewrite H1.
        rewrite H0.
        repeat rewrite app_assoc.
        auto 1.
    ** injection H. intros.
       rewrite <- app_assoc in H0.
       apply app_inv_head in H0.
       apply app_inv_head in H0.
       rewrite H0.
       rewrite app_assoc.
       congruence.
Qed.

Lemma flds_aux_decompose_first_same:
  forall (n : nat) (fd1 fd1' fd2' fd' : list JFFieldDeclaration) (CC : JFProgram) (cn : JFClassName),
    flds_aux CC cn n (fd1 ++ fd1') = Some (fd1 ++ fd1' ++ fd') ->
    flds_aux CC cn n (fd1 ++ fd2') = Some (fd1 ++ fd2' ++ fd').
Proof.
  intros.
  rewrite app_assoc in H.
  replace (fd1 ++ fd1') with ((fd1 ++ fd1') ++ []) in H by
      (rewrite <- app_assoc;rewrite app_nil_r;auto).
  replace (((fd1 ++ fd1') ++ []) ++ fd') with ((fd1 ++ fd1') ++ [] ++ fd') in H
    by (rewrite app_assoc;rewrite app_nil_r;auto).
  eapply flds_aux_decompose_second_same in H.
  rewrite app_nil_r in H.
  rewrite H.
  repeat rewrite app_assoc.
  rewrite app_nil_r.
  auto 1.
Qed.
    
Lemma flds_aux_flds_aux:
  forall n CC cn fds x7 x7',
    flds_aux CC cn n x7 = Some fds ->
    (exists fds',
        flds_aux CC cn n x7' = Some fds').
Proof.
  induction n.
  * intros.
    simpl.
    simpl in H.
    destruct (find_class CC cn).
    ** destruct j.
       destruct ex.
       *** discriminate H.
       *** eexists. auto 1.
    ** discriminate H.
  * intros.
    simpl.
    simpl in H.
    destruct (find_class CC cn).
    ** destruct j.
       destruct ex.
       *** eapply IHn.
           apply H.
       *** eexists. auto 1.
    ** discriminate H.
Qed.
    
(** How many extends steps there are to reach Object. *)
Fixpoint get_class_height (CC:JFProgram) (cn:JFClassName) : nat :=
  match CC with
  | [] => 0
  | (JFCDecl name (Some name') _ _) :: CC' =>
    if (JFClassName_dec name cn)
    then S (get_class_height CC' name')
    else get_class_height CC' cn
  | (JFCDecl name None _ _) :: CC' =>
    if (JFClassName_dec name cn)
    then 1
    else get_class_height CC' cn
  end.

Lemma get_class_height_non_zero:
  forall CC cn ex fields methods,
  In (JFCDecl cn ex fields methods) CC ->
         get_class_height CC cn <> 0.
Proof.
  induction CC.
  + intros.
    auto 2 using in_nil.
  + intros.
    simpl.
    destruct a.
    destruct ex0.
    ++ destruct (JFClassName_dec cn0 cn).
       +++ auto 1.
       +++ apply in_inv in H.
           destruct H.
           ++++ injection H;intros;contradiction.
           ++++ eauto 2.
    ++ destruct (JFClassName_dec cn0 cn).
       +++ auto 1.
       +++ apply in_inv in H.
           destruct H.
           ++++ injection H;intros;contradiction.
           ++++ eauto 2.
Qed.


Lemma find_class_get_class_height:
  forall CC cn cd,
    find_class CC cn = Some cd ->
    get_class_height CC cn <> 0.
Proof.
  induction CC.
  + intros.
    discriminate H.
  + intros.
    destruct a.
    simpl.
    simpl in H.
    intro.
    destruct (JFClassName_dec cn0 cn).
    +++ destruct ex;discriminate H0.
    +++ destruct ex;eapply IHCC;eauto.
Qed.


(** Calculates the list of field declarations in an object of the given
    class identifier [C]. In case [C] is the bottom class
    the function returns [None]. Otherwise it traverses the
    object hierarchy and collects filelds.

    Defined in Figure {fig:auxiliary-notation} as the function flds with overline bar. *)
Definition flds_overline (CC:JFProgram) (C:JFCId)
: option (list JFFieldDeclaration) :=
  match C with
    | JFClass cn =>
      flds_aux CC cn (get_class_height CC cn) []
    | JFBotClass => None
  end.

Lemma flds_overline_find_class :
  forall CC C flds,
    flds_overline CC (JFClass C) = Some flds ->
    exists cdecl, find_class CC C = Some cdecl.
Proof.
  intros ? ? ? Htmp.
  simpl in Htmp.
  destruct get_class_height in Htmp.
  + simpl in Htmp.
    destruct find_class; eauto 2.
    discriminate Htmp.
  + simpl in Htmp.
    destruct find_class; eauto 2.
    discriminate Htmp.
Qed.

Hint Resolve flds_overline_find_class.


(** Calculates the list of field identifiers in an object of the given
    class identifier [C]. In case [C] is the bottom class
    the function returns [None]. Otherwise it traverses the
    object hierarchy and collects filelds.

    Defined in Figure {fig:syntax} as the function flds. *)
Definition flds (CC:JFProgram) (C:JFCId) :=
  match flds_overline CC C with
  | Some fields => Some (map name_of_fd fields)
  | None => None
  end.


(** Calculates the type of the parameter [n] in the method [md] in
    the class [C]. In case [C] is the bottom class the function
    returns [None]. Otherwise it looks up the method [md] in the class
    declaration of [C] in [CC]. If it succeeds it returns the type
    of the paramter. Otherwise it returns None. We use here the
    operation (.)^rwr in case method has no annotations. The value
    n=0 is for the type of this.

    Defined in Figure {fig:auxiliary-notation} as the function parTypM.
  *)
Definition parTypM_of_md (C:JFCId) (md: JFMethodDeclaration) (n:nat) : JFACId :=
  match md with
  | JFMDecl D mu mn vs excs E =>
    match n with
    | 0 => (C, mu)
    | _ => nth (n-1) (map snd vs) (JFObject, JFrwr)
    end
  | JFMDecl0 D mn vs excs E =>
    match n with
    | 0 => (C, JFrwr)
    | _ => (nth (n-1) (map snd vs) JFObject, JFrwr)
    end
  end.


Definition parTypM (CC:JFProgram) (C:JFCId) (m:JFMId) (n:nat)
  : option JFACId :=
  match C with
    | JFClass cn =>
      let mdo := methodLookup CC cn m in
      match mdo with
      | Some md => Some (parTypM_of_md C md n)
      | None => None
      end
    | JFBotClass => None
  end.


Definition retTypM (CC:JFProgram) (C:JFCId) (m:JFMId)
  : option JFACId :=
  match C with
    | JFClass cn =>
      let mdo := methodLookup CC cn m in
      match mdo with
        | Some md => Some (rettyp_of_md md)
        | None => None
      end
    | JFBotClass => None
  end.


Definition thrs (CC:JFProgram) (C:JFCId) (m:JFMId)
  : option (list JFACId) :=
  match C with
    | JFClass cn =>
      let mdo := methodLookup CC cn m in
      match mdo with
        | Some md => Some (thrs_of_md md)
        | None => None
      end
    | JFBotClass => None
  end.


Lemma thrs_thrs_of_md:
  forall CC cn md,
    methodLookup CC cn (name_of_md md) = Some md ->
    thrs CC (JFClass cn) (name_of_md md) =
    Some (thrs_of_md md).
Proof.
  intros.
  simpl.
  rewrite H.
  auto.
Qed.

Definition body (CC:JFProgram) (C:JFCId) (m:JFMId)
  : option JFExpr :=
  match C with
    | JFClass cname =>
      let mdo := methodLookup CC cname m in
      match mdo with
        | Some md =>
          Some (body_of_md md)
        | None => None
      end
    | JFBotClass => None
  end.
