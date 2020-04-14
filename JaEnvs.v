Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Coq.Program.Equality.

Require Import Lists.List.
Import ListNotations.
Require Import JaSyntax.
Require Import JaProgram.
Require Import JaSubtype.
Require Import JaProgramWf.
Require Import Jafun.
Require Import JaTactics.
Require Import JaUnique.
Open Scope list_scope.
Open Scope nat_scope.

From Hammer Require Import Reconstr.



Module VarName <: Name.
  Definition name := JFVal.
  Definition name_dec := JFVal_dec.
End VarName.

Module VarInEnv <: Declaration.
  Include VarName.
  Definition decl := (JFVal * JFACId)%type.
  Definition name_of_decl : decl -> name := fst.
End VarInEnv.

Module Env := VarInEnv <+ ListUniq.



Definition JFEnv := Env.t.

Definition JFExEnv := list JFACId.

Section EnvsInProgram.

  Variable P : JFProgram.
  Variable cdecl: JFClassDeclaration.
  Variable md : JFMethodDeclaration.
    
(**
   The operation of ⊎ as defined in Section {sec:type-system}.
   TODO: definicja zgodna z papierem, ale w papierze wyrażenie poprawne,
         ale źle przedstawiające intencje.
*)
Fixpoint sumPlus (exs:JFExEnv) (ext:JFACId) :=
  match ext with
  | (C, cmod) =>
    match exs with
    | [] => [ext]
    | (D, dmod) :: tl =>
      if subtype_bool P D C
      then sumPlus tl ext
      else (D, dmod) :: (sumPlus tl ext)
    end
  end.


Fixpoint sumPlus' (exs:JFExEnv) (ext:JFACId) :=
  match exs with
  | [] => [ext]
  | ext' :: tl =>
    if JFACId_dec ext ext'
    then ext :: tl
    else ext' :: (sumPlus tl ext)
  end.

Fixpoint sumPlusCtx (exs:JFExEnv) (Ctx:JFContext) :=
  match Ctx with
  | [] => exs
  | cnode :: Ctx' => match cnode with
                     | JFCtxLet cn x _ E2 => sumPlusCtx exs Ctx'
                     | JFCtxTry _ mu cn x E2 => sumPlus (sumPlusCtx exs Ctx') (JFClass cn, mu)
                     end
  end.

Lemma sumPlusCtxLet:
  forall Ctx Xi cn x E,
    sumPlusCtx Xi (Ctx ++ [JFCtxLet cn x __ E]) = sumPlusCtx Xi Ctx.
Proof.
  induction Ctx.
  * intros.
    simpl.
    auto.
  * intros.
    destruct a.
    ** simpl.
       eauto.
    ** simpl.
       rewrite IHCtx.
       eauto.
Qed.

Lemma sumPlusCtxTry:
  forall Ctx Xi mu cn x E,
    sumPlusCtx Xi (Ctx ++ [JFCtxTry __ mu cn x E]) = sumPlusCtx (sumPlus Xi (JFClass cn, mu)) Ctx.
Proof.
  induction Ctx.
  * intros.
    simpl.
    auto.
  * intros.
    simpl.
    destruct a;eauto 2.
    rewrite (IHCtx Xi);eauto 2.
Qed.
    
(**
   The operation of ⊕ as defined in Appendix {sec:metatheory}.
*)
Fixpoint oPlus (env:JFEnv) (l:Loc) (acid:JFACId) {struct env} :=
  match l with
  | null => env
  | JFLoc _ =>
    match env with
    | [] => [((JFVLoc l), acid)]
    | (v, acid') :: tl => if JFVal_dec v (JFVLoc l)
                        then
                          (v, infACId P acid acid') :: tl
                        else
                          (v, acid') :: (oPlus tl l acid)
    end
  end.


Lemma oplus_decompose_eq:
  forall l acid1 acid2 Gamma,
    l <> null ->
    oPlus ((JFVLoc l, acid1) :: Gamma) l acid2 = (JFVLoc l, infACId P acid2 acid1) :: Gamma.
Proof.
  intros.
  destruct l; try contradiction.
  unfold oPlus.
  destruct (JFVal_dec (JFVLoc (JFLoc n)) (JFVLoc (JFLoc n)));try contradiction.
  trivial.
Qed.

Lemma oPlus_neq:
  forall l l' a a' Gamma,
    JFVLoc l <> l' ->
    oPlus ((l', a') :: Gamma) l a =
    (l', a') :: (oPlus Gamma l a).
Proof.
  destruct Gamma.
  + intros.
    destruct l.
    ++ simpl. trivial.
    ++ destruct l'.
       +++ unfold oPlus.
           destruct (JFVal_dec (JFVLoc l) (JFVLoc (JFLoc n))); try congruence.
       +++ unfold oPlus.
           destruct (JFVal_dec (JFSyn x) (JFVLoc (JFLoc n))); try congruence.
  + intros.
    destruct l.
    ++ simpl. trivial.
    ++ destruct l'.
       +++ unfold oPlus.
           destruct (JFVal_dec (JFVLoc l) (JFVLoc (JFLoc n))); try congruence.
       +++ unfold oPlus.
           destruct  (JFVal_dec (JFSyn x) (JFVLoc (JFLoc n))); try congruence.
Qed.

Lemma In_oPlus_Gamma:
  forall Gamma v C mu D nu,
    Env.names_unique Gamma ->
    In (JFVLoc v, (C, mu)) (oPlus Gamma v (D, nu)) ->
    exists mu', In (JFVLoc v, (C,mu')) Gamma \/
                C = D \/ C = JFBotClass.
Proof.
  induction Gamma.
  + intros.
    simpl in H0.
    destruct v.
    ++ inversion H0.
    ++ simpl in H0.
       destruct H0;try contradiction.
       injection H0;intros;subst.
       eauto.
  + intros.
    simpl in H0.
    destruct v.
    ++ eauto.
    ++ destruct a.
       destruct (JFVal_dec j (JFVLoc (JFLoc n))).
       +++ subst.
           destruct j0.
           eapply Env.names_unique_zero in H;simpl;trivial.
           pose (infClass_trichotomy P D j) as Tricho.
           destruct Tricho as [Tricho|Tricho] ;try destruct Tricho as [Tricho|Tricho].
           ++++ simpl in H0.
                destruct H0;eauto.
                injection H0;intros.
                eexists. right;left.
                congruence.
           ++++ simpl in H0.
                destruct H0;eauto.
                injection H0;intros.
                exists j0;left;left.
                rewrite <- H2.
                rewrite <- Tricho at 1.
                auto.
           ++++ simpl in H0.
                destruct H0;eauto.
                injection H0;intros.
                eexists;right;right.
                rewrite <- H2.
                rewrite Tricho.
                auto.
       +++ simpl in H0.
           destruct H0;try congruence.
           eapply IHGamma in H0;eauto.
           destruct H0.
           exists x.
           simpl.
           destruct H0;eauto.
           Unshelve. auto. auto. auto.
Qed.           
       
Lemma in_oplus_eq:
  forall l acid1 Gamma acid2 Cid Cn cdecl mid,
    names_unique P ->
    subtype_well_founded P ->
    Cid = JFClass Cn ->
    find_class P Cn = Some cdecl ->
    Env.names_unique Gamma ->
    l <> null ->
    In (JFVLoc l, acid1) (oPlus Gamma l acid2) ->
    leqIsLS P Cid mid acid1 acid2.
Proof.
  induction Gamma.
  + intros * ? ? ? ? ? ? HIn.
    simpl in HIn.
    destruct l.
    ++ eapply in_nil in HIn; contradiction.
    ++ apply in_inv in HIn.
       destruct HIn as [ [= ->] | HIn].
       +++ eauto.
       +++ sauto.
  + intros * ? ? ? ? Heu ? HIn.
    destruct a as (x, Acid).
    destruct (JFVal_dec x (JFVLoc l)).
    ++ subst.
       rewrite oplus_decompose_eq in HIn;eauto 2.
       simpl in HIn.
       destruct HIn as [ [=] | HIn]; eauto 2.
       +++ eapply infACId_leqIsLS_L; eauto.
       +++ eapply Env.names_unique_zero in Heu; eauto 1.
           simpl in Heu.
           eapply Env.name_noocc_In_decl_neq in Heu; eauto 1.
           simpl in Heu.
           contradiction.
    ++ rewrite oPlus_neq in HIn;eauto 1.
       simpl in HIn.
       destruct HIn as [ [=] | HIn]; try congruence.
       eapply IHGamma in HIn; eauto 1.
Qed.

Lemma in_oplus_neq:
  forall Gamma l l' acid1 acid2,
    l <> l' ->
    In (JFVLoc l, acid1) (oPlus Gamma l' acid2) ->
    In (JFVLoc l, acid1) Gamma.
Proof.
  induction Gamma.
  + intros.
    simpl in H0.
    destruct l'.
    ++ inversion H0.
    ++ simpl in H0.
       simpl.
       destruct H0.
       +++ congruence.
       +++ auto.
  + intros.
    simpl in H0.
    destruct l'.
    ++ simpl.
       simpl in H0.
       auto.
    ++ destruct a.
       destruct (JFVal_dec j (JFVLoc (JFLoc n))).
       +++ subst j.
           simpl.
           simpl in H0.
           destruct H0; try congruence.
           right;auto.
       +++ destruct H0.
           ++++ rewrite <- H0.
                simpl;left;auto.
           ++++ eapply IHGamma in H0;auto.
                simpl;right;auto.
Qed.
       
Hint Resolve in_oplus_eq in_oplus_neq oPlus_neq oplus_decompose_eq.

Fixpoint loc2env_aux (cn:JFClassName) (mdecl:JFMethodDeclaration)
         (vs:list JFVal) (num:nat) (res:JFEnv) {struct vs} :=
  match vs with
  | [] => res
  | (JFVLoc lhd) :: tl =>
    let acidpt := parTypM P (JFClass cn) (name_of_md mdecl) num in
    (* parTypM returns rwr annotation for non-LS methods *)
    match acidpt with
    | None => res
    | Some acid => loc2env_aux cn mdecl tl (num+1) (oPlus res lhd acid)
    end
  | (JFSyn x) :: tl => res
end.

Definition loc2env (cn:JFClassName) (mdecl:JFMethodDeclaration)
           (vs:list JFVal)  :=
  loc2env_aux cn mdecl vs 0 [].

(* 
  (x,Acid) ∈ (oPlus Gamma x Acid')  ∧  Acid ≤: Acid'
*)
Lemma In_oPlus : forall Gamma n D muD,
    names_unique P ->
    subtype_well_founded P ->
    exists D' muD', In (JFVLoc (JFLoc n), (D', muD')) (oPlus Gamma (JFLoc n) (D, muD)) /\
             leqACId P (D',muD') (D,muD).
Proof.
  intros.
  induction Gamma.
  + do 2 eexists.
    simpl.
    repeat split; auto with myhints.
  + simpl.
    destruct a as (x,(Dx,mux)).
    destruct (JFVal_dec x (JFVLoc (JFLoc n))).
    ++
      subst.
      do 2 eexists.
      split.
      +++ simpl; eauto 2.
      +++ split.
          ++++ eapply infClass_subL; eauto 1.
          ++++ eapply infAnn_leq_l; eauto 1.
    ++
      simpl.
      decompose_ex IHGamma.
      decompose_and IHGamma.
      do 2 eexists; eauto 3.
Qed.

Hint Resolve In_oPlus.

(**
  The operation par2env as defined in Section {sec:type-system}. 
  Here, the definition does not use ParTypM, but is equivalent.
*)
Definition par2env :=
match md with
| JFMDecl _ mu _ vs _ _ =>
      (JFSyn JFThis, (JFClass (name_of_cd cdecl), mu))
       :: map
            (fun H0 : JFXId * JFACId =>
             let (x, acid) := H0 in (JFSyn (JFVar x), acid)) vs
| JFMDecl0 _ _ vs _ _ =>
      (JFSyn JFThis, (JFClass (name_of_cd cdecl), JFrwr))
       :: map
            (fun H0 : JFXId * JFCId =>
             let (x, cid) := H0 in (JFSyn (JFVar x), (cid, JFrwr))) vs
end.


Lemma par2env_equiv_parTypM : forall i,
    nth i par2env (JFnull, (JFObject, JFrwr)) =
    (nth i (JFSyn JFThis :: map (fun x => JFSyn (JFVar x)) (params_of_md md)) JFnull,
     parTypM_of_md (JFClass (name_of_cd cdecl)) md i).
Proof.
  destruct i.
  + simpl.
    unfold par2env.
    unfold parTypM_of_md.
    unfold name_of_cd.
    sauto.
  + unfold par2env.
    unfold parTypM_of_md.
    unfold name_of_cd.
    replace (S i - 1) with i by auto with arith.
    revert i.
    destruct md; simpl.
    * induction vs; sauto.
    * induction vs; sauto.
Qed.

Definition subenv (Gamma1 Gamma2: JFEnv) : Prop :=
  forall x Acid2, In (x,Acid2) Gamma2 ->
                 exists Acid1,
                   In (x,Acid1) Gamma1 /\ leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) Acid1 Acid2.

Lemma subenv_cons :
  forall Gamma1 Gamma2 x Acid,
    subenv Gamma1 Gamma2 ->
    subenv ((x,Acid)::Gamma1) ((x,Acid)::Gamma2).
Proof.
  unfold subenv.
  intros until 0.
  intros ? ? ? H0.
  inversion H0 as [H1|?].
  + injection H1; intros; subst.
    eexists.
    split.
    ++ sauto.
    ++ eapply leqIsLS_refl; eauto.
  + simpl In; firstorder.
Qed.

Lemma subenv_cons_sub:
  forall Gamma1 Gamma2 x Acid1 Acid2,
    leqIsLS P (JFClass (name_of_cd cdecl)) (name_of_md md) Acid1 Acid2 ->
    subenv Gamma1 Gamma2 ->
    subenv ((x,Acid1)::Gamma1) ((x,Acid2)::Gamma2).
Proof.
  unfold subenv.
  intros until 0.
  intros ? ? ? ? H0.
  inversion H0 as [H2|?].
  + injection H2; intros; subst.
    eexists.
    sauto.
  + simpl In; firstorder.
Qed.

Lemma subenv_refl:
  forall Gamma,
    subenv Gamma Gamma.
Proof.
  induction Gamma.
  + sauto.
  + destruct a.
    eauto using subenv_cons.
Qed.
         
  
Lemma subenv_oPlus:
  forall Gamma x acid,
    names_unique P ->
    subtype_well_founded P -> 
    subenv (oPlus Gamma x acid) Gamma.
Proof.
  induction Gamma.
  + sauto.
  + intros.
    destruct x; simpl.
    * apply subenv_refl.
    * destruct a.
      destruct (JFVal_dec j (JFVLoc (JFLoc n))).
      - destruct (infACId P acid j0) eqn:Hinf.
        -- eapply infACId_leqIsLS_R in Hinf;eauto.
           eapply subenv_cons_sub;eauto using subenv_refl.
      - auto using subenv_cons.
Qed.       

Hint Resolve subenv_cons subenv_cons_sub subenv_refl subenv_oPlus.


Lemma oPlus_non_null :
  forall Gamma l Acid,
    Forall (fun '(v, _) => isNonNullLoc v) Gamma ->
    Forall (fun '(v, _) => isNonNullLoc v) (oPlus Gamma l Acid).
Proof.
  destruct l.
  * induction Gamma; simpl; trivial.
  * induction Gamma; simpl.
    ** intros ? _.
       repeat constructor.
    ** intros (v1, Acid1) H.
       destruct a as (v2, Acid2).
       ***
         inversion_clear H.
         destruct (JFVal_dec v2 (JFVLoc (JFLoc n))).
         ****
           subst.
           destruct (infACId P (v1, Acid1) Acid2); repeat constructor; assumption.
         ****
           constructor; auto. 
Qed.

Hint Resolve oPlus_non_null.

Lemma oPlus_null : forall Gamma Acid,
    oPlus Gamma null Acid = Gamma.
Proof.
  induction Gamma; sauto.
Qed.

Hint Rewrite oPlus_non_null.

Lemma name_occ_oPlus_eq:
  forall Gamma v l acid,
    v <> JFVLoc l ->
    Env.name_occ (oPlus Gamma l acid) v = Env.name_occ Gamma v.
Proof.
  induction Gamma.
  + intros * Hne. 
    simpl.
    Env.uniq v.
    destruct l.
    ++ trivial.
    ++ unfold Env.NU.name_occ.
       simpl map.
       unfold count_occ.
       destruct VarInEnv.name_dec; intuition.
  + intros * Hne.
    destruct a as (v1,acid1).
    destruct v1 as [l'|x].
    ++ destruct (JFVal_dec (JFVLoc l') (JFVLoc l)) as [e|e].
       +++ injection e;intros;subst.
           destruct l.
           ++++ rewrite oPlus_null;auto.
           ++++ rewrite oplus_decompose_eq;eauto 1.
                congruence.
       +++ rewrite oPlus_neq by auto.
           destruct (JFVal_dec v (JFVLoc l)); Env.uniq v; intuition.
    ++ rewrite oPlus_neq; try congruence.
       destruct (JFVal_dec v (JFSyn x)); Env.uniq v; intuition.
Qed.

Import Env.

Lemma name_occ_oPlus : 
  forall Gamma v l acid n,
    v <> JFVLoc l ->
    name_occ Gamma v = n ->
    name_occ (oPlus Gamma l acid) v = n.
Proof.
  intros.
  now rewrite name_occ_oPlus_eq.
Qed.

Hint Resolve name_occ_oPlus.

Lemma names_unique_env_oPlus:
  forall Gamma l acid,
    Env.names_unique Gamma ->
    Env.names_unique (oPlus Gamma l acid).
Proof.
  induction Gamma.
  + unfold names_unique.
    intros.
    intro v.
    destruct l.
    ++ simpl.
       auto.
    ++ simpl oPlus.
       uniq v.
       apply name_xi_small.
  + intros.
    destruct a as (v1,acid1).
    destruct (JFVal_dec v1 (JFVLoc l)).
    ++ subst.
       destruct (Loc_dec l null).
       +++ subst.
           rewrite oPlus_null;eauto 1.
       +++ rewrite oplus_decompose_eq;eauto 1.
    ++ destruct (Loc_dec l null).
       +++ subst.
           rewrite oPlus_null;eauto 1.
       +++ destruct v1.
           ++++
             rewrite oPlus_neq by eauto 2.
             eapply names_unique_cons; eauto 3.
           ++++
             rewrite oPlus_neq by eauto 2.
             eapply names_unique_cons; eauto 3.
Qed.


Hint Resolve names_unique_env_oPlus.

(* TODO: Hack, żeby odsłonić zasłonięte names_unique... *)
Notation names_unique := JaProgram.names_unique.


Lemma In_in_oPlus:
  forall Gamma n D' muD' D'' muD'',
  names_unique P ->
  Env.names_unique Gamma ->
  subtype_well_founded P ->
  In (JFVLoc (JFLoc n), (D', muD')) Gamma -> 
  exists (D : JFCId) (muD : JFAMod),
    In (JFVLoc (JFLoc n), (D, muD)) (oPlus Gamma (JFLoc n) (D'', muD'')) /\
    leqACId P (D, muD) (D', muD') /\ leqACId P (D, muD) (D'', muD'').
Proof.     
  intros * ? Hun ? HIn.
  induction Gamma.
  + do 2 eexists.
    simpl.
    repeat split; auto with myhints.
  + simpl oPlus.
    destruct a as (x,(Dx,mux)).
    destruct (JFVal_dec x (JFVLoc (JFLoc n))).
    ++
      subst.
      do 2 eexists.
      split.
      +++ simpl; eauto 2.
      +++ assert (In (JFVLoc (JFLoc n), (Dx, mux))
                 ((JFVLoc (JFLoc n), (Dx, mux)) :: Gamma)) as HInx.
          { simpl; auto. }
          eapply Env.name_once_In_unique in HIn; eauto 3.
          (* {simpl; left; reflexivity.} *)
          injection HIn.
          intros; subst.
          do 2 split; eauto 2 using infClass_subL, infClass_subR, infAnn_leq_l, infAnn_leq_r.
    ++
      simpl In in *.
      destruct HIn; try congruence.
      destruct IHGamma as (? & ? & ? & ? & ?); eauto 1; sauto.
Qed.


Lemma In_oPlus_other : forall x Acid l Acid' Gamma,
      x <> JFVLoc l ->
      In (x, Acid) Gamma ->
      In (x, Acid) (oPlus Gamma l Acid').                
Proof.    
  intros * Hneq.
  induction Gamma.
  { intros []. }  
  destruct a as (v,Acid1).
  intros HIn.
  simpl.
  destruct l; trivial.
  destruct JFVal_dec.
  + destruct HIn; try congruence.
    red; auto.
  + destruct HIn as [ -> | H].   
    * red; auto.
    * right; auto.
Qed.      

Hint Resolve In_oPlus_other.

Definition get_mu phi Gamma n : JFAMod :=
  match phi with
  | true =>
    match find Gamma (JFVLoc (JFLoc n)) with
    | None => JFatm
    | Some (_,(DD,mu')) => mu'
    end
  | false => JFatm
  end.


End EnvsInProgram.