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
Require Import JaTypes.
Open Scope list_scope.
Open Scope nat_scope.

From Hammer Require Import Reconstr.


Section RedInvariants.

  Variable P : JFProgram.


Lemma internal_fields_unique :
  Well_formed_program P ->
  JFprogTypes P ->
  forall n,
  forall cdecl C ex flds mthds,
    get_class_height P C = n ->
    cdecl = JFCDecl C ex flds mthds ->
    In cdecl P ->
    exists fields, flds_overline P (JFClass C) = Some fields /\
      Flds.names_unique fields.
Proof.
  intros Hwp Hpt; induction n.
  + intros until 0.
    intros Hch Hcd HIn.
    eapply get_class_height_non_zero in Hch; try contradiction.
    sauto.
  + intros until 0.
    intros Hch Hcd HIn.
    inversion Hpt as [_ Hta].
    rewrite Forall_forall in Hta.
    assert (Ht:=Hta cdecl HIn).
    inversion Ht as [? ? ? ? Hcd' _ Hfr ? | ? ? Hcd' _ ?].
    ++ 
      rewrite Hcd in Hcd'.
      symmetry in Hcd'; injection Hcd'; clear Hcd'; intros; subst.
      generalize HIn; intros HfndC.
      apply in_find_class in HfndC; auto.
      destruct ex as [D |]; swap 1 2. 
      *
        simpl.
        rewrite Hch.
        simpl.
        rewrite HfndC.
        simpl.
        eauto.
      * generalize HfndC; intros HfndD.
        eapply find_class_get_class_height_find_class in HfndD; eauto 2.
        destruct HfndD as (ddecl, HfndD).
        assert (C<>D) as Hneq by (eapply ex_not_circular; eauto 2).
        generalize Hneq; intros Hext.
        eapply find_class_extends in Hext; eauto 2.
        generalize Hext; intro Hdh.
        eapply extends_get_class_height in Hdh; eauto 2.
        rewrite Hch in Hdh.
        injection Hdh; clear Hdh; intro Hdh; symmetry in Hdh.
        destruct ddecl as [D' Dex Dfld Dmthds].
        eapply IHn in Hdh; eauto 2 using find_class_in.
        decompose_ex Hdh.
        destruct Hdh as [HDo Hfu]. 
        eapply flds_overline_decl_extends_decompose in HIn; eauto 2.
        eexists.
        split; eauto 1.
        apply Flds.names_unique_app; eauto 1.
        red in Hfr.
        apply Flds.name_noocc_recip.
        eapply Hfr; swap 1 3; eauto 1; try congruence; eauto 2.
    ++ 
      rewrite Hcd in Hcd'.
      symmetry in Hcd'; injection Hcd'; clear Hcd'; intros; subst.
      apply in_find_class in HIn; auto.
      simpl.
      rewrite Hch.
      simpl.
      rewrite HIn.
      simpl.
      eauto 3.
Qed.      



Lemma exists_fields_unique :
  Well_formed_program P ->
  JFprogTypes P ->
  forall C cdecl ex flds mthds,
    cdecl = JFCDecl C ex flds mthds ->
    In cdecl P ->
    exists fields,
      flds_overline P (JFClass C) = Some fields /\
      Flds.names_unique fields.
Proof.
  intros.
  eapply internal_fields_unique; eauto 1.
Qed.

Lemma fields_unique :
  Well_formed_program P ->
  JFprogTypes P ->
  forall C fields,
    flds_overline P (JFClass C) = Some fields ->
    Flds.names_unique fields.
Proof.
  intros Hwp Htp ? ? HC.
  generalize HC; intro Htmp.
  unfold flds_overline in Htmp.
  assert (exists cdecl, find_class P C = Some cdecl) as HfndC.
  - destruct get_class_height in Htmp.
    + simpl in Htmp.
      destruct find_class as [cdecl|]; try discriminate.
      eauto 2.
    + simpl in Htmp.
      destruct find_class as [cdecl|]; try discriminate.
      eauto 2.
  - destruct HfndC as [ cdecl HfndC ].
    destruct cdecl.
    eapply find_class_in in HfndC.
    edestruct exists_fields_unique as (fields1 & HC1 & ?); eauto 1.
    intuition.
    replace fields with fields1; trivial.
    congruence.
Qed.

Hint Resolve fields_unique.

Lemma subtype_flds_overline_decompose :
  Well_formed_program P ->
  JFprogTypes  P ->
  forall C D,
    subtyping P C D ->
    forall Cfields Dfields,
    flds_overline P C = Some Cfields ->
    flds_overline P D = Some Dfields ->
    exists flds, Cfields = flds ++ Dfields.
Proof.
  intros Hwp Htp ? ? Hsub.
  induction Hsub as [?|?|?|? ? ? ? ? ? ? Hext].
  * intros.
    exists [].
    simpl.
    congruence.
  * intros ? Ofields HC HO.
    destruct C as [Cname|]; [idtac | unfold flds_overline in HC; discriminate].
    edestruct flds_overline_find_class as [cdecl HfndC].
    eapply HC.
    unfold flds_overline in HO.
    unfold JFObject in HO.
    rewrite <- (app_nil_l Ofields) in HO.
    rewrite <- (app_nil_l Cfields) in HC.
    generalize Hwp; intros (_ & Hpo & _).
    generalize Hpo; intro Hfo.
    eapply program_contains_find_class in Hfo.
    destruct Hfo.
    edestruct flds_aux_decompose_object as [flds Heq]; swap 1 3; [apply HfndC | eauto 3 ..].
    * intros ? ? HB ?.
      unfold flds_overline in HB; discriminate.
    * intros ? Efields HC HE.
      subst C D.
      edestruct extends_in_second as (Dex & Dflds & Dmthds & HDIn); eauto 2.
      edestruct exists_fields_unique as (Dfields & HD & HDu); eauto 2.
      edestruct IHHsub as (flds', Heq); eauto 2.
      
      eapply flds_overline_extends_decompose in Hext; eauto 2.
      destruct Hext as (Cflds & HC').
      exists (Cflds ++ flds').
      rewrite <- app_assoc.
      congruence.
Qed.  
  
(** Field exists in subtype and its definition is the same *)
Lemma subtype_fields_same :
  Well_formed_program P ->
  JFprogTypes P ->
  forall C D,
    subtyping P C D ->
    forall Cfields Dfields,
    flds_overline P C = Some Cfields ->
    flds_overline P D = Some Dfields ->
    forall x,
    In x (map Flds.name_of_decl Dfields) ->
    Flds.find Cfields x = Flds.find Dfields x.
Proof.
  intros Hwp Htp ? ? Hsub ? ? HC HD.
  destruct C as [Cname|]; [idtac | unfold flds_overline in HC; discriminate].
  destruct D as [Dname|]; [idtac | unfold flds_overline in HD; discriminate].
  generalize HC; intro HCfu.
  eapply fields_unique in HCfu; eauto 1.
  edestruct subtype_flds_overline_decompose as (flds, Heq); eauto 1.
  subst.
  intros.
  edestruct Flds.in_map_find; eauto 2.
  erewrite Flds.find_app_r_unique; eauto 1.
Qed.
  
      
(* TODO *)
    (* Podtypowanie z Objectem powinno "naturalnie" zachodzić, nie powinno być konstruktora 
       subtyping P E Object, tylko lemat...
       forall P, In C P -> subtyping C Object
       przy założeniach:
       object_not_extends
       all_extend_but_object
       program_contains_object
       well_formed_program (ze jeśli JFDecl (Some D) ... \in P to D też)
     *)
    (* Zresztą chyba dowód lematu 
       flds_aux_decompose_object
       zawiera takie wyprowadzenie...
     *)
    
Record TypedFrame :=
  TFR
  { TFRcdecl : JFClassDeclaration;
    TFRmdecl : JFMethodDeclaration;
    TFRXi : JFExEnv;
    TFRGamma : JFEnv;
    TFRfr : Frame;
    TFRAcid : JFACId
  }.


Definition replace_fr_in_tfr fr tfr : TypedFrame :=
  {| TFRcdecl := TFRcdecl tfr;
     TFRmdecl := TFRmdecl tfr;
     TFRXi := TFRXi tfr;
     TFRGamma := TFRGamma tfr;
     TFRfr := fr;
     TFRAcid := TFRAcid tfr
  |}.

Lemma TFRfr_replace_fr_in_tfr:
  forall fr tfr,
    TFRfr (replace_fr_in_tfr fr tfr) = fr.
Proof.
  intros.
  simpl;auto.
Qed.

(*

Definition replace_fr_in_tfr (fr: Frame) (tfr: TypedFrame) : TypedFrame.
destruct tfr; clear TFRfr0; now constructor.
Defined.
Print replace_fr_in_tfr.

(* more direct definition, more eager to reduce - but breaks some existing proofs  :( *)

  match tfr with
| {| TFRcdecl := TFRcdecl0; TFRmdecl := TFRmdecl0; TFRXi := TFRXi0; TFRGamma := TFRGamma0; TFRAcid
  := TFRAcid0 |} =>
    {|
    TFRcdecl := TFRcdecl0;
    TFRmdecl := TFRmdecl0;
    TFRXi := TFRXi0;
    TFRGamma := TFRGamma0;
    TFRfr := fr;
    TFRAcid := TFRAcid0 |}
end.
*)






Definition update_env_in_fr tfr l0 acid : TypedFrame :=
  {| TFRcdecl := TFRcdecl tfr;
     TFRmdecl := TFRmdecl tfr;
     TFRXi := TFRXi tfr;
     TFRGamma := oPlus P (TFRGamma tfr) l0 acid;
     TFRfr := TFRfr tfr;
     TFRAcid := TFRAcid tfr
  |}.

Lemma update_env_null : forall e acid,
    update_env_in_fr e null acid = e.
Proof.
  intros.
  unfold update_env_in_fr.
  destruct e.
  simpl.
  f_equal.
  destruct TFRGamma0; trivial.
Qed.


  
(** The definition of "derivable extended context expression" from
    the paper. *)
Definition DerivableTFR (tfr : TypedFrame) :=
  match tfr with
    TFR cdecl mdecl Xi Gamma fr Acid =>
    find_class P (name_of_cd cdecl) = Some cdecl /\
    methodLookup P (name_of_cd cdecl) (name_of_md mdecl) = Some mdecl /\
    (match fr with
     | Ctx [[E ]]_ Some _ =>
       exists v, E=JFVal1 v /\ typesCtx P cdecl mdecl Xi Gamma (JFThrow v) Ctx Acid
     | Ctx [[E ]]_ None => typesCtx P cdecl mdecl Xi Gamma E Ctx Acid
     end)
  end.

Definition TypedFrameStack := list TypedFrame.


Definition FSofTFS (tfs:TypedFrameStack) : FrameStack := map TFRfr tfs.


Definition HeapAgreesLocDecl (h:Heap) (ValAcid : JFVal * JFACId) :=
  let (v, acid) := ValAcid in
  let (cid, _) := acid in
  match v with
  | JFnull => False
  | JFVLoc (JFLoc n) =>
    exists (ro : RawObj) (cn : JFClassName),
      Heap.find (*elt:=Obj*) n h = Some (ro, cn) /\ subtyping P (JFClass cn) cid
  | JFSyn _ => False
  end.


Definition HeapAgreesEnv (h:Heap) (Gamma:JFEnv) : Prop :=
  Forall (HeapAgreesLocDecl h) Gamma.




Lemma heap_find_HeapAgreesEnv:
  forall n h o Cn Did mu Gamma,
    names_unique P ->
    subtype_well_founded P ->
    Heap.find (elt:=Obj) n h = Some (o, Cn) ->
    subtyping P (JFClass Cn) Did -> 
    HeapAgreesEnv h Gamma ->
    HeapAgreesEnv h (oPlus P Gamma (JFLoc n) (Did,mu)).
Proof.
  intros until 0.
  intros Nuq Swf Hf HsubCD.
  induction 1 as [ | (x1,(Cid1,mu1)) Gamma Hhal ?].
  + simpl.
    repeat constructor.
    red.
    do 2 eexists.
    split; eauto 1.
  + unfold oPlus; fold oPlus.
    destruct (JFVal_dec x1 (JFVLoc (JFLoc n))); swap 1 2.
    { now constructor. }
    subst x1.
    constructor; try assumption.
    simpl.
    do 2 eexists.
    split; eauto 1.
    inversion Hhal as (x,(cn,[Hf' Hsub])).
    rewrite Hf in Hf'.
    injection Hf'; clear Hf'; intros; subst x cn.
    eapply infClass_inf; swap 1 5; eauto 1.
Qed.

Lemma HeapAgreesEnv_subtyping:
  forall n C mu (Gamma:JFEnv) h obj D,
    In (JFVLoc (JFLoc n), (C, mu)) Gamma ->
    HeapAgreesEnv h Gamma ->
    Heap.find (elt:=Obj) n h = Some (obj, D) ->
    subtyping P (JFClass D) C.
Proof.
  intros * InG HAE Hfnd.
  unfold HeapAgreesEnv in HAE.
  eapply Forall_forall in HAE; try eapply InG.
  simpl in HAE.
  decompose_ex HAE.
  decompose_and HAE as [Fnd Sub].
  congruence.
Qed.

(** Properties that must be satisfied by all [TypedFrame]s 
    in a dynamic typing assertion. *) 

Definition ConsistentTFR (h:Heap) (* W, R *) (tfr : TypedFrame) :=
  Forall (fun '(v, _) => isNonNullLoc v) (TFRGamma tfr)
  /\
  Env.names_unique (TFRGamma tfr)
  /\
  (* NPE loc has some type <: JFNPE and rwr mode *)
  (exists Cnpe, In (NPE_val, (Cnpe, JFrwr)) (TFRGamma tfr) /\ subtyping P Cnpe JFNPE)
  /\
  HeapAgreesEnv h (TFRGamma tfr)
  (* /\ something about W and R B.3.(1)c *)
.

Lemma ConsistentTFR_isNonNullLoc:
  forall h tfr,
    ConsistentTFR h tfr ->
    Forall (fun '(v, _) => isNonNullLoc v) (TFRGamma tfr).
Proof.
  intros.
  unfold ConsistentTFR in H;decompose [and] H;eauto.
Qed.
  
Lemma ConsistentTFR_names_unique:
  forall h tfr,
    ConsistentTFR h tfr ->
    Env.names_unique (TFRGamma tfr).
Proof.
  intros.
  unfold ConsistentTFR in H;decompose [and] H;eauto.
Qed.

Lemma ConsistentTFR_HeapAgreesEnv:
  forall h tfr,
    ConsistentTFR h tfr ->
    HeapAgreesEnv h (TFRGamma tfr).
Proof.
  intros.
  unfold ConsistentTFR in H;decompose [and] H;eauto.
Qed.


Lemma ConsistentTFR_subtyping:
  forall h tfr n oo C C' mu',
    ConsistentTFR h tfr ->
    Heap.find (elt:=Obj) n h = Some (oo, C) ->
    In (JFVLoc (JFLoc n), (C', mu')) (TFRGamma tfr) ->
    subtyping P (JFClass C) C'.
Proof.
  intros.
  unfold ConsistentTFR in H.
  destruct H as (H2 & _ & Hnpe & H3).
  unfold HeapAgreesEnv in H3.
  eapply Forall_forall in H1; try eapply H3.
  simpl in H1.
  decompose_ex H1.
  destruct H1.
  eqf.
  now intros _ [= ->].
Qed.

Inductive ConsistentTFSind (h:Heap) : TypedFrameStack -> Prop :=
| ConsistentTFSind1 : forall tfr, ConsistentTFR h tfr -> ConsistentTFSind h [tfr]
| ConsistentTFSind2 : forall tfri1 tfri tfstail n m vs Ctx robj cn,
    ConsistentTFSind h (tfri :: tfstail) ->
    ConsistentTFR h tfri1 -> 
    (* C i,expr = C[[l.m(ll)]]_∅ , with l ̸= null *)
    TFRfr tfri = Ctx [[JFInvoke (JFVLoc (JFLoc n)) m vs ]]_ None ->
    Forall isLoc vs ->
    (* class(h, l) = C1 and C i+1,class = C1 and *)
    Heap.find n h = Some (robj,cn) ->
    name_of_cd (TFRcdecl tfri1) = cn ->
    (* C i+1,meth = m *) 
    name_of_md (TFRmdecl tfri1) = m ->
    (* and C i+1,exc = thrs(C1 , m) *)    (* we will check that mdecl really comes from cdecl later *)
    TFRXi tfri1 = thrs_of_md (TFRmdecl tfri1) ->
    (* ⟨C i+1,type , C i+1,mod ⟩ = retTypM(C1 , m) *)
    TFRAcid tfri1 = rettyp_of_md (TFRmdecl tfri1) ->

    (* if isLS(C i,meth ) then isLS(C i+1,meth ) *)
    (isLS (TFRmdecl tfri) -> isLS (TFRmdecl tfri1)) -> 
    
    ConsistentTFSind h (tfri1 :: tfri :: tfstail).

Lemma ConsistentTFSind_TFR:
  forall h tfr tl,
  ConsistentTFSind h (tfr :: tl) ->
  ConsistentTFR h tfr.
Proof.
  intros.
  inversion H;auto.
Qed.

Lemma ConsistentTFSind_wfs:
  forall h tfs,
    ConsistentTFSind h tfs ->
    well_formed_framestack (FSofTFS tfs).
Proof.
  induction 1.
  - simpl; trivial.
  - simpl in *.
    rewrite H1.
    trivial.
Qed.
Hint Resolve ConsistentTFSind_wfs.

(*
Lemma ConsistentTFSind_update_env_in_fr:
  forall h e tl v o Cn Did mu,
    ConsistentTFSind h (e :: tl) ->
    Heap.find (elt:=Obj) v h = Some (o, Cn) ->
    subtyping P (JFClass Cn) Did -> 
    ConsistentTFSind h ((update_env_in_fr e  (JFLoc v) (Did,mu)) :: tl).
Proof.
  intros until 0.
  intros IsTFS Hpfnd Hsub.
  destruct tl.
  + apply ConsistentTFSind1.
    inversion IsTFS.
    subst.
    unfold ConsistentTFR in *.
    decompose [and] H0; clear H0.
    repeat split.
    ++ destruct e.
       simpl in *.
       eauto using oPlus_non_null.
    ++ simpl.
       eapply heap_find_HeapAgreesEnv; eauto 1.
  + inversion IsTFS.
    eapply ConsistentTFSind2;eauto 1.
    subst.
    unfold ConsistentTFR in *.
    decompose [and] H3; clear H3.
    repeat split.
    ++ destruct e.
       simpl in *.
       eauto using oPlus_non_null.
    ++ simpl.
       eapply heap_find_HeapAgreesEnv; eauto 1.
Qed.

*)
(** The property that a derivable extended context expression
    support is a dynamic typing assertion.

   Definition {def:dta} in Appendix B.
*)
Inductive ConsistentTFS (h:Heap) : TypedFrameStack -> Prop :=
| ConsistentTFSnone :
    forall tfrn tfs Ctx E,
      ConsistentTFSind h (tfrn::tfs) ->
      TFRfr tfrn = Ctx [[E]]_ None ->
      ConsistentTFS h (tfrn::tfs)
| ConsistentTFSexc :
    forall tfrn tfs Ctx n D robj,
      ConsistentTFSind h (tfrn::tfs) ->
      TFRfr tfrn = Ctx [[JFVal1 (JFVLoc (JFLoc n))]]_ (Some D) ->
      Heap.find n h = Some (robj, D) ->
      ConsistentTFS h (tfrn::tfs).


Lemma ConsistentTFS_wfs:
  forall h tfs,
    ConsistentTFS h tfs ->
    well_formed_framestack (FSofTFS tfs).
Proof.
  destruct 1; eauto 2.
Qed.
Hint Resolve ConsistentTFS_wfs.


Lemma ConsistentTFS_further:
  forall h tfrn1 tfrn2 tfs,
    ConsistentTFS h (tfrn1::tfrn2::tfs) -> ConsistentTFS h (tfrn2::tfs).
Proof.
  induction tfs.
  * intros. 
    inversion H; (
      subst;
       inversion H2;
       subst;
       try inversion H5;
       try inversion H6;
       subst;
       eapply ConsistentTFSnone;eauto 1
    ).
  * intros.
    inversion H.
    ** subst.
       inversion H2.
       subst.
       eapply ConsistentTFSnone;eauto 1.
    ** subst.
       inversion H2.
       subst.
       eapply ConsistentTFSnone;eauto 1.
Qed.

Definition DerivableTFS (h:Heap) (tfs:TypedFrameStack) : Prop :=
  ConsistentTFS h tfs /\ Forall DerivableTFR tfs.

Lemma DerivableTFS_wfs:
  forall h tfs,
    DerivableTFS h tfs ->
    well_formed_framestack (FSofTFS tfs).
Proof.
  destruct 1; eauto 2.
Qed.
Hint Resolve DerivableTFS_wfs.

Lemma DerivableTFS_further:
  forall h e e0 tfs,
    DerivableTFS h (e :: e0 ::tfs) ->
    DerivableTFS h (e0 :: tfs).
Proof.
  intros.
  unfold DerivableTFS in H.
  decompose_and H.
  split.
  + eauto using ConsistentTFS_further.
  + eapply Forall_forall.
    intros.
    eapply Forall_forall in H1.
    apply H1.
    simpl.
    right.
    auto.
Qed.

Lemma ConsistentTFS_DTFR_DerivableTFS:
  forall h tfs,
    ConsistentTFS h tfs ->
    Forall DerivableTFR tfs ->
    DerivableTFS h tfs.
Proof.
  unfold DerivableTFS;eauto 2.
Qed.

Lemma ConsistentTFS_one : forall h tfs,
    ConsistentTFS h tfs -> Forall (ConsistentTFR h) tfs.
Proof.
  destruct 1; induction H; auto.
Qed. 

Lemma DerivableTFS_ConsistentTFR:
  forall h tfr tfs,
    DerivableTFS h (tfr::tfs) -> ConsistentTFR h tfr.
Proof.
  intros.
  unfold DerivableTFS in H.
  destruct H.
  eapply ConsistentTFS_one in H.
  eapply Forall_inv in H.
  assumption.
Qed.

Hint Resolve DerivableTFS_ConsistentTFR ConsistentTFSind_TFR HeapAgreesEnv_subtyping.
Hint Resolve ConsistentTFS_one ConsistentTFS_DTFR_DerivableTFS.







Lemma DerNU_first :
  forall h tfr frs, DerivableTFS h (tfr :: frs) -> Env.names_unique (TFRGamma tfr).
Proof.
  intros * H.
  apply DerivableTFS_ConsistentTFR in H.
  red in H.
  tauto.
Qed.

Hint Resolve DerNU_first.

Lemma DerNU_first' :
  forall h TFRcdecl0 TFRmdecl0 TFRXi0 TFRGamma0 TFRfr0 TFRAcid0 frs, DerivableTFS h
    ({|
     TFRcdecl := TFRcdecl0;
     TFRmdecl := TFRmdecl0;
     TFRXi := TFRXi0;
     TFRGamma := TFRGamma0;
     TFRfr := TFRfr0;
     TFRAcid := TFRAcid0 |} :: frs) -> Env.names_unique TFRGamma0.
Proof.
  intros * H.
  apply DerivableTFS_ConsistentTFR in H.
  red in H.
  tauto.
Qed.

Hint Immediate DerNU_first'.

Lemma DerNU_second' :
  forall h tfr' TFRcdecl0 TFRmdecl0 TFRXi0 TFRGamma0 TFRfr0 TFRAcid0 frs, DerivableTFS h
    (tfr' :: {|
     TFRcdecl := TFRcdecl0;
     TFRmdecl := TFRmdecl0;
     TFRXi := TFRXi0;
     TFRGamma := TFRGamma0;
     TFRfr := TFRfr0;
     TFRAcid := TFRAcid0 |} :: frs) -> Env.names_unique TFRGamma0.
Proof.
  intros * [H _].
  apply ConsistentTFS_further in H.
  apply ConsistentTFS_one in H.
  sauto.
Qed.

Hint Immediate DerNU_second'.

Lemma DerNU_second :
  forall h tfr' tfr fr, DerivableTFS h (tfr' :: tfr :: fr) -> Env.names_unique (TFRGamma tfr).
Proof.
  intros * [H _].
  apply ConsistentTFS_further in H.
  apply ConsistentTFS_one in H.
  sauto.
Qed.

Hint Resolve DerNU_second.

Lemma findAssoc_forDTFS_Invoke:
  forall h fm1 fm2 tfs Ctx n m vs,
    Well_formed_program P ->
    DerivableTFS h (fm1 :: fm2 :: tfs) ->
    TFRfr fm2 = Ctx [[JFInvoke (JFVLoc (JFLoc n)) m vs ]]_ None ->
    exists D mu,
      Env.find (TFRGamma fm2) (JFVLoc (JFLoc n)) = Some (JFVLoc (JFLoc n), (D, mu)).
Proof.
  intros h fm1 fm2 tfs Ctx n m vs Wfp Dtfs FrOfFm2.
  inversion Dtfs as [IsTFS DTFRs].
  inversion DTFRs as [|tfrfst tfrtl DTFRfst DTFRtl tfrfsteq].
  subst.
  inversion DTFRtl as [|tfrsnd tfrtltl DTFRsnd DerDte].
  subst.
  unfold DerivableTFR in DTFRsnd.
  destruct fm2.
  simpl in *.
  rewrite FrOfFm2 in DTFRsnd.
  destruct DTFRsnd as (Fcls & MthdLkp & TpsCtx).
  apply typesCtx_typesCtxExt in TpsCtx; try assumption.
  destruct TpsCtx as [X11 [Acid1 TpsCtx]].
  apply typesCtxExt_types in TpsCtx.
  destruct Acid1 as (C,mu).
  eapply inversion_JFInvoke in TpsCtx; eauto 2.

  destruct TpsCtx as [D0 [dname [mu0 [D' [mu' [mthrs [rettyp info]]]]]]].
  destruct info as [H1 [HtypesVal info]].
  decompose [and] info.
  clear info.
  eapply inversion_JFVal1_nonnull in HtypesVal; eauto 2; try congruence.

  decompose_ex HtypesVal.  
  destruct HtypesVal as [? [HIn ?]].
  eapply Env.In_find_exists in HIn; eauto 2.
  decompose_ex HIn.
  destruct d' as (?, (D, mu1)).
  destruct HIn as [HIn [= ->]].
  eauto 3.
Qed.


Lemma findAssoc_forDTFS_Val1:
  forall (h : Heap) (fm : TypedFrame) (tfs : list TypedFrame) 
         (Ctx : JFContext) (n : nat) (md : JFEvMode),
    Well_formed_program P ->
    DerivableTFS h (fm :: tfs) ->
    TFRfr fm = Ctx [[JFVal1 (JFVLoc (JFLoc n)) ]]_ md ->
    exists (D : JFCId) (mu : JFAMod),
      Env.find (TFRGamma fm) (JFVLoc (JFLoc n)) = Some (JFVLoc (JFLoc n),(D, mu)).
Proof.
  intros h fm tfs Ctx n md Wfp Dtfs FrOfFm2.
  inversion Dtfs as [IsTFS DTFRs].
  inversion DTFRs as [|tfrfst tfrtl DTFRfst DTFRtl tfrfsteq].
  subst.
  unfold DerivableTFR in DTFRfst.
  destruct fm.
  simpl in *.
  rewrite FrOfFm2 in DTFRfst.
  destruct DTFRfst as (Fcls & MthdLkp & TpsCtx).
  destruct md.
  + destruct TpsCtx as [v [ValV TpsCtx]].
    apply typesCtx_typesCtxExt in TpsCtx; try assumption.
    destruct TpsCtx as [X11 [Acid1 TpsCtx]].
    apply typesCtxExt_types in TpsCtx.
    destruct Acid1 as (C,mu).
    eapply inversion_Throw in TpsCtx; eauto 2.

    destruct TpsCtx as [m [C1 [D [mu' [mis [Cis [TpsV [IsLeqIncluded TpsThr]]]]]]]].
    injection ValV;intros.
    subst.
    eapply inversion_JFVal1_nonnull in TpsV; eauto 2; try discriminate.
    destruct TpsV as [C'' [mu'' [LeqIsLS [Inn TpsV]]]].
    eapply Env.In_find in Inn; eauto 1.
    eauto.
  + apply typesCtx_typesCtxExt in TpsCtx; try assumption.
    decompose_ex TpsCtx.
    apply typesCtxExt_types in TpsCtx.
    destruct Acid1.
    eapply inversion_JFVal1_nonnull in TpsCtx; eauto 2; try discriminate.
    destruct TpsCtx as [? [? [? [HIn ?]]]].
    eapply Env.In_find in HIn; eauto 1.
    decompose_ex HIn.
    eauto 3.
Qed.




Lemma getClassName_forDTFS:
  forall h fm2 tfs Ctx n m vs,
    Well_formed_program P ->
    DerivableTFS h (fm2 :: tfs) ->
    TFRfr fm2 = Ctx [[JFInvoke (JFVLoc (JFLoc n)) m vs ]]_ None ->
    exists dname,
    getClassName h n = Some dname.
Proof.
  intros h fm2 tfs Ctx n m vs Wfp Dtfs FrOfFm2.
  inversion Dtfs as [IsTFS DTFRs].
  eapply Forall_inv in DTFRs.
  unfold DerivableTFR in DTFRs.
  destruct fm2.
  simpl in *.
  rewrite FrOfFm2 in DTFRs.
  destruct DTFRs as (Fcls & MthdLkp & TpsCtx).
  eapply typesCtx_typesCtxExt1 in TpsCtx; eauto 2.
  destruct TpsCtx as [Xi1 [Acid1 TpsCtxExt]].
  eapply typesCtxExt_types in TpsCtxExt;eauto 1.
  destruct Acid1.
  eapply inversion_JFInvoke in TpsCtxExt;eauto 2.
  destruct TpsCtxExt as [D [dname [mu [D' [mu' [mthrs [retyp TpsCtxExt]]]]]]].
  destruct TpsCtxExt as [Dname [TpsVal1 TpsCtxExt]].
  eapply inversion_JFVal1_nonnull in TpsVal1;eauto 2;try congruence.
  inversion IsTFS as [tfrn tfs0 Ctx0 E IsTFSindFm12 TFRfrfm1|
                      tfrn tfs0 Ctx0 n0 D0 robj IsTFSindFm12
                           TFRfrfm1 Hpfnd].
  * simpl in *. subst.
    clear TFRfrfm1 E Ctx0.
    inversion IsTFSindFm12 as [|tfri1 tfri tfstail 
                                     n0 m0 vs0 Ctx1 robj cn
                                     IsTFSindfm2 AuxTFSonefm1
                                     TFRfrfm2 FaIsLoc
                                     Hpfnd cneq m0eq TFRXieq
                                     TFRAcideq IsLSimpl].
    ** subst.
       unfold ConsistentTFR in H.
       simpl in H.
       destruct H as (_ & _ & _ & H1).
       unfold HeapAgreesEnv in H1.
       destruct TpsVal1 as [C'' [mu'' [Leq [InTFRGamma0 TpsVal1]]]].
       eapply Forall_forall in InTFRGamma0; try apply H1.
       unfold HeapAgreesLocDecl in InTFRGamma0.
       decompose_ex InTFRGamma0. 
       destruct InTFRGamma0 as [Hpfnd _].
       unfold getClassName.
       rewrite Hpfnd.
       eexists;eauto 1.
    ** subst.
       simpl in *.
       unfold ConsistentTFR in AuxTFSonefm1.
       simpl in AuxTFSonefm1.
       destruct AuxTFSonefm1 as (_ & _ & _ & H0).
       unfold HeapAgreesEnv in H0.
       destruct TpsVal1 as [C'' [mu'' [Leq [InTFRGamma0 TpsVal1]]]].
       eapply Forall_forall in InTFRGamma0; try apply H0.
       unfold HeapAgreesLocDecl in InTFRGamma0.
       destruct InTFRGamma0 as [ro [cn [Hpfnd1 sbt]]].
       unfold getClassName.
       rewrite Hpfnd1.
       eexists;eauto 1.
  * subst.
    inversion IsTFSindFm12 as [|tfri1 tfri tfstail 
                                     n0' m0' vs0' Ctx1 robj' cn
                                     IsTFSindfm2 AuxTFSonefm1
                                     TFRfrfm2 FaIsLoc
                                     Hpfndn0' cneq m0eq TFRXieq
                                     TFRAcideq IsLSimpl].
    ** subst.
       unfold ConsistentTFR in H.
       simpl in H.
       destruct H as (_ & _ & _ & H1).
       unfold HeapAgreesEnv in H1.
       destruct TpsVal1 as [C'' [mu'' [Leq [InTFRGamma0 TpsVal1]]]].
       eapply Forall_forall in InTFRGamma0; try apply H1.
       unfold HeapAgreesLocDecl in InTFRGamma0.
       destruct InTFRGamma0 as [ro [cn [Hpfnd1 sbt]]].
       unfold getClassName.
       rewrite Hpfnd1.
       eexists;eauto 1.
    ** subst.
       simpl in *.
       unfold ConsistentTFR in AuxTFSonefm1.
       simpl in AuxTFSonefm1.
       destruct AuxTFSonefm1 as (_ & _ & _ & H0).
       unfold HeapAgreesEnv in H0.
       destruct TpsVal1 as [C'' [mu'' [Leq [InTFRGamma0 TpsVal1]]]].
       eapply Forall_forall in InTFRGamma0; try apply H0.
       unfold HeapAgreesLocDecl in InTFRGamma0.
       destruct InTFRGamma0 as [ro [cn [Hpfnd1 sbt]]].
       unfold getClassName.
       rewrite Hpfnd1.
       eexists;eauto 1.
Qed.

Lemma methodLookup_forDTFS:
  forall h fm1 fm2 tfs Ctx n m vs dname,
    Well_formed_program P ->
    DerivableTFS h (fm1 :: fm2 :: tfs) ->
    TFRfr fm2 = Ctx [[JFInvoke (JFVLoc (JFLoc n)) m vs ]]_ None ->
    getClassName h n = Some dname ->
    exists md,
      methodLookup P dname m = Some md.
Proof.
  intros h fm1 fm2 tfs Ctx n m vs dname Wfp Dtfs FrOfFm2 GetClNm.
  inversion Dtfs as [IsTFS DTFRs].
  inversion DTFRs as [|tfrn tfrtl Dtfrfm1 DTFRs1].
  subst.
  inversion DTFRs1 as [|tfrn1 tfrtl1 Dtfrfm2 DTFRs2].
  subst.
  unfold DerivableTFR in Dtfrfm2.
  destruct fm2.
  destruct Dtfrfm2 as (Fcls & MthdLkp & TpsCtxInvk).
  simpl in *.
  inversion IsTFS as [fm1' tfs' Ctx0 E IsTFSind TFRfrfm1|
                      tfrn tfs0 Ctx0 n0 D robj IsTFSind TFRfrfm1 HpFnd].
  * (* non-exception *) subst.
    inversion IsTFSind as [|tfri1 tfri tfstail n0 m0 vs0 Ctx1 robj cn
                                 IsTFSindfm2 AuxTFSonefm1 TFRfreq IsLocAll HpFnd
                                 NameCd NameMd TFRXieq TFRAcideq IsLSimpl].
    simpl in *.
    injection TFRfreq;intros;clear TFRfreq.
    subst.
    apply typesCtx_typesCtxExt in TpsCtxInvk; try assumption.
    destruct TpsCtxInvk as [Xi1 [Acid1 TpsCtxInvk]].
    apply typesCtxExt_types in TpsCtxInvk.
    destruct Acid1 as (C,mu).
    eapply inversion_JFInvoke in TpsCtxInvk; eauto 2.
    destruct TpsCtxInvk as [D0 [dname' [mu0 [D' [mu' [mthrs [rettyp info]]]]]]].
    destruct info as [nameq [TpsVal [ParTypM info]]].
    destruct D0;try discriminate nameq.
    injection nameq;intros;clear nameq;subst.
    unfold parTypM in ParTypM.
    destruct (methodLookup P dname' (name_of_md (TFRmdecl fm1))) eqn:mthdLkp;
      try discriminate ParTypM.
    eapply inversion_JFVal1_nonnull in TpsVal;
      try apply Fcls;try trivial;try discriminate;eauto 2.
    destruct TpsVal as [dname'' [mu'' [LeqIsLS [Inn0 TpsVal]]]].
    assert (ConsistentTFR h
                {|
                TFRcdecl := TFRcdecl0;
                TFRmdecl := TFRmdecl0;
                TFRXi := TFRXi0;
                TFRGamma := TFRGamma0;
                TFRfr := Ctx1
                         [[JFInvoke (JFVLoc (JFLoc n0))
                             (name_of_md (TFRmdecl fm1)) vs0 ]]_ None;
                TFRAcid := TFRAcid0 |})
      as AuxTFSone by (inversion IsTFSindfm2;auto).
    inversion AuxTFSone as (NonNull & _ & _ & HpAgreesEnv).
    simpl in *.
    unfold HeapAgreesEnv in HpAgreesEnv.
    assert (forall x : JFVal * JFACId,
               In x TFRGamma0 -> HeapAgreesLocDecl h x)
      as HpAgreesEnv' by
          (apply (Forall_forall (HeapAgreesLocDecl h) TFRGamma0);
           auto).
    apply HpAgreesEnv' in Inn0.
    simpl in Inn0.
    destruct Inn0 as [ro [cn [Hfnd subt]]].
    rewrite HpFnd in Hfnd.
    injection Hfnd;intros;clear Hfnd;subst.
    unfold getClassName in GetClNm.
    rewrite HpFnd in GetClNm.
    injection GetClNm;intros;clear GetClNm;subst.
    assert (subtyping P (JFClass (name_of_cd (TFRcdecl fm1)))
                      (JFClass dname')) as Sbtp.
    { inversion LeqIsLS.
      + injection H1;intros;clear H1.
        injection H2;intros;clear H2.
        subst.
        eapply subtrans;eauto 2.
      + injection H1;intros;clear H1.
        injection H2;intros;clear H2.
        subst.
        eapply subtrans;eauto 2.
    }
    unfold DerivableTFR in Dtfrfm1.
    destruct fm1.
    simpl in *.
    decompose [and] Dtfrfm1.
    eapply lookup_in_supertype_subtype;
      try apply Sbtp; try apply mthdLkp; eauto 2.
  * (* exception *)
    subst.
    inversion IsTFSind as [|tfri1 tfri tfstail n1 m1 vs1 Ctx1 robj1 cn
                                  IsTFSindfm2 AuxTFSonefm1 TFRfreq IsLocAll
                                  HpFnd1
                                  NameCd NameMd TFRXieq TFRAcideq IsLSimpl].
    simpl in *.
    injection TFRfreq;intros;clear TFRfreq.
    subst.
    apply typesCtx_typesCtxExt in TpsCtxInvk; try assumption.
    destruct TpsCtxInvk as [Xi1 [Acid1 TpsCtxInvk]].
    apply typesCtxExt_types in TpsCtxInvk.
    destruct Acid1 as (C,mu).
    eapply inversion_JFInvoke in TpsCtxInvk; eauto 2.
    destruct TpsCtxInvk as [D0 [dname' [mu0 [D' [mu' [mthrs [rettyp info]]]]]]].
    destruct info as [nameq [TpsVal [ParTypM info]]].
    destruct D0;try discriminate nameq.
    injection nameq;intros;clear nameq;subst.
    unfold parTypM in ParTypM.
    destruct (methodLookup P dname' (name_of_md (TFRmdecl fm1))) eqn:mthdLkp;
      try discriminate ParTypM.
    eapply inversion_JFVal1_nonnull in TpsVal;
      try apply Fcls;try trivial;try discriminate;eauto 2.
    destruct TpsVal as [dname'' [mu'' [LeqIsLS [Inn0 TpsVal]]]].
    assert (ConsistentTFR h
                {|
                TFRcdecl := TFRcdecl0;
                TFRmdecl := TFRmdecl0;
                TFRXi := TFRXi0;
                TFRGamma := TFRGamma0;
                TFRfr := Ctx1
                         [[JFInvoke (JFVLoc (JFLoc n0))
                             (name_of_md (TFRmdecl fm1)) vs1 ]]_ None;
                TFRAcid := TFRAcid0 |})
      as AuxTFSone by (inversion IsTFSindfm2;auto).
    inversion AuxTFSone as (NonNull & _ & _ & HpAgreesEnv).
    simpl in *.
    unfold HeapAgreesEnv in HpAgreesEnv.
    assert (forall x : JFVal * JFACId,
               In x TFRGamma0 -> HeapAgreesLocDecl h x)
      as HpAgreesEnv' by
          (apply (Forall_forall (HeapAgreesLocDecl h) TFRGamma0);
           auto).
    apply HpAgreesEnv' in Inn0.
    simpl in Inn0.
    destruct Inn0 as [ro [cn [Hfnd subt]]].
    rewrite HpFnd1 in Hfnd.
    injection Hfnd;intros;clear Hfnd;subst.
    unfold getClassName in GetClNm.
    rewrite HpFnd1 in GetClNm.
    injection GetClNm;intros;clear GetClNm;subst.
    assert (subtyping P (JFClass (name_of_cd (TFRcdecl fm1)))
                      (JFClass dname')) as Sbtp.
    { inversion LeqIsLS.
      + injection H1;intros;clear H1.
        injection H2;intros;clear H2.
        subst.
        eapply subtrans;eauto 2.
      + injection H1;intros;clear H1.
        injection H2;intros;clear H2.
        subst.
        eapply subtrans;eauto 2.
    }
    unfold DerivableTFR in Dtfrfm1.
    destruct fm1.
    simpl in *.
    decompose [and] Dtfrfm1.
    eapply lookup_in_supertype_subtype;
      try apply Sbtp; try apply mthdLkp; eauto 2.
Qed.


Lemma ConsistentTFStoIsTFSe:
  forall tfri tfri' h tfstail Ctx n A robj,
    TFRfr tfri' = Ctx [[JFVal1 (JFVLoc (JFLoc n)) ]]_ Some A ->
    TFRcdecl tfri' = TFRcdecl tfri ->
    TFRmdecl tfri' = TFRmdecl tfri ->
    TFRXi tfri' = TFRXi tfri ->
    TFRGamma tfri' = TFRGamma tfri ->
    TFRAcid tfri' = TFRAcid tfri ->
    Heap.find (elt:=Obj) n h = Some (robj, A) ->
    ConsistentTFSind h (tfri :: tfstail) ->
    ConsistentTFS h (tfri' :: tfstail).
Proof.
  intros tfri tfri' h tfstail Ctx n A robj eqfr eqcdecl eqmdecl
         eqxi eqgamma eqacid hfind IsTFSind.
  inversion IsTFSind as [tfri'' Aux eq1|tfri'' tfri''' tfrtl].
  * eapply ConsistentTFSexc; eauto 1.
    eapply ConsistentTFSind1.
    unfold ConsistentTFR.
    rewrite eqgamma.
    unfold ConsistentTFR in Aux.
    auto.
  * eapply ConsistentTFSexc;try rewrite eqfr; eauto 1.
    eapply ConsistentTFSind2;
      try unfold ConsistentTFR; try rewrite eqgamma;try rewrite eqcdecl;
        try rewrite eqxi; try rewrite eqmdecl; try rewrite eqacid;
          try rewrite eqfr; eauto 2.
Qed.


(* Lemma isDtfs_isNtfs : forall h e fr tfs, ConsistentTFS h (e::tfs) -> ConsistentTFS h (replace_fr_in_tfr fr e::tfs).
*)
Lemma isDtfs_isNtfs : forall h e Ctx E tfs,
    ConsistentTFS h (e::tfs) -> ConsistentTFS h (replace_fr_in_tfr (Ctx [[E]]_None) e::tfs).
Proof.
  unfold replace_fr_in_tfr.
  inversion_clear 1.
  + inversion_clear H0.
    ++
      econstructor; simpl; trivial.
      econstructor.
      destruct H.
      now constructor. 
    ++
      econstructor; simpl; trivial.
      econstructor; eauto 1.
  + inversion_clear H0.
    ++
      econstructor; simpl; trivial.
      econstructor.
      destruct H.
      now constructor. 
    ++
      econstructor; simpl; trivial.
    econstructor; eauto 1.
Qed.

Hint Resolve isDtfs_isNtfs.
  

Lemma isDtfs_isNtfs_ex : forall h e Ctx n robj D tfs,
    ConsistentTFS h (e::tfs) ->
    Heap.find n h = Some (robj,D) ->
    ConsistentTFS h (replace_fr_in_tfr (Ctx [[ JFVal1 (JFVLoc (JFLoc n)) ]]_Some D) e::tfs).
unfold replace_fr_in_tfr.
inversion_clear 1.
+ inversion_clear H0.
  ++
    econstructor 2; simpl; eauto 1.
    econstructor.
    destruct H.
    now constructor. 
  ++
    econstructor 2; simpl; eauto 1.
    econstructor; eauto 1.
+ inversion_clear H0.
  ++
    econstructor 2; simpl; eauto 1.
    econstructor.
    destruct H.
    now constructor. 
  ++
    econstructor 2; simpl; eauto 1.
    econstructor; eauto 1.
Qed.

Hint Resolve isDtfs_isNtfs_ex.



Lemma ConsistentTFR_update_env : forall h e n o Cn Did mu,
    Well_formed_program P ->
    Heap.find (elt:=Obj) n h = Some (o, Cn) ->
    subtyping P (JFClass Cn) Did ->
    ConsistentTFR h e ->  ConsistentTFR h (update_env_in_fr e (JFLoc n) (Did,mu)).  
Proof.
  destruct 4 as (? & ? & Hnpe & ?).
  repeat split; simpl; eauto 4 using heap_find_HeapAgreesEnv, names_unique_env_oPlus, oPlus_non_null.
  destruct e; simpl in *.
  destruct (JFVal_dec NPE_val (JFVLoc (JFLoc n))) as [ Heq | ?].
  + rewrite Heq in *.
    decompose_ex Hnpe.
    destruct Hnpe.
    edestruct In_in_oPlus as (Cnpe' & mu' & HIn_oPlus & Hleq1 & Hleq2); eauto 2.
    eexists.
    split.
    ++ evar (mrwr : JFAMod).
       enough (mrwr = mu') as HeqMod.
       +++ rewrite <- HeqMod in HIn_oPlus.
           unfold mrwr in *.
           apply HIn_oPlus.
       +++
           destruct Hleq1 as [_ Hrwr].
           rewrite rwr_eq; eauto 1.
    ++
      destruct Hleq1.
      eapply subtrans; eauto 2.
  + destruct Hnpe as (Cnpe & HIn & Hsub); eauto 4 using In_oPlus_other.
Qed.
  

Lemma ConsistentTFSind_update_env : forall h e tfs n o Cn Did mu,
    Well_formed_program P ->
    Heap.find (elt:=Obj) n h = Some (o, Cn) ->
    subtyping P (JFClass Cn) Did ->
    ConsistentTFSind h (e :: tfs) ->  ConsistentTFSind h (update_env_in_fr e (JFLoc n) (Did,mu)::tfs).
Proof.
  intros until 3.
  inversion_clear 1.
  + constructor.
    eapply ConsistentTFR_update_env; eauto 1.  
  + econstructor; simpl; eauto 1.
    eapply ConsistentTFR_update_env; eauto 1.
Qed.

Lemma isDtfs_isNtfs_env : forall h e tfs n o Cn Did mu,
    Well_formed_program P ->
    Heap.find (elt:=Obj) n h = Some (o, Cn) ->
    subtyping P (JFClass Cn) Did ->
      ConsistentTFS h (e::tfs) -> ConsistentTFS h (update_env_in_fr e (JFLoc n) (Did,mu)::tfs).
Proof.
  unfold update_env_in_fr.
  intros until 3.
  inversion_clear 1.
  + econstructor; simpl; eauto 1.
    eapply ConsistentTFSind_update_env; eauto 1.
  + econstructor 2; simpl; eauto 1.
    eapply ConsistentTFSind_update_env; eauto 1.
Qed.


Hint Resolve isDtfs_isNtfs_env.


Lemma DerivableTFS_update_env : forall h e tfs n o Cn Did mu,
    Well_formed_program P ->
    Heap.find (elt:=Obj) n h = Some (o, Cn) ->
    subtyping P (JFClass Cn) Did ->
    DerivableTFS h (e::tfs) ->
    names_unique P ->
    subtype_well_founded P ->
    DerivableTFS h (update_env_in_fr e (JFLoc n) (Did,mu) :: tfs).                
Proof.
  destruct 4 as [? Hder].
  constructor; eauto 3.
  inversion_clear Hder as [|? ? Hder' ?].
  econstructor; trivial.
  destruct e  as [? ? ? ? TFRfr0 ?].
  red in Hder' |- *.
  simpl.
  decompose_and Hder' as (? & ? & Hder).
  destruct TFRfr0 as [Ctx E A].
  destruct A.
  + (* case A=Some *)
    decompose_ex Hder.
    intuition.
    eexists.
    ssplit; eauto 1.
    eapply typesCtx_subenv; eauto 2.
    apply subenv_oPlus; eauto 2.
  + (* case A=None *)
    intuition.
    eapply typesCtx_subenv; eauto 1.
    apply subenv_oPlus; eauto 1.
Qed.


Lemma DerivableTFR_replace_fr : forall cdecl mdecl Xi Gamma E1 Ctx1 E2 Ctx2 Acid,
    typesCtx P cdecl mdecl Xi Gamma E2 Ctx2 Acid ->

    DerivableTFR (TFR cdecl mdecl Xi Gamma (Ctx1[[E1]]_ None) Acid) ->
    DerivableTFR (replace_fr_in_tfr ( Ctx2[[E2]]_ None) (TFR cdecl mdecl Xi Gamma (Ctx1[[E1]]_ None) Acid)).
Proof.
  intros until 0.
  simpl.
  intuition.
Qed.  

Lemma DerivableTFS_replace_fr : forall h cdecl mdecl Xi Gamma E1 Ctx1 E2 Ctx2 Acid tfs,
    typesCtx P cdecl mdecl Xi Gamma E2 Ctx2 Acid ->

    DerivableTFS h ((TFR cdecl mdecl Xi Gamma (Ctx1[[E1]]_ None) Acid)::tfs) ->
    DerivableTFS h ((replace_fr_in_tfr ( Ctx2[[E2]]_ None) (TFR cdecl mdecl Xi Gamma (Ctx1[[E1]]_ None) Acid))::tfs).
Proof.
  intros until 0.
  intros Htyp.
  destruct 1 as [Htfs Hder].
  constructor; eauto 2.
  inversion_clear Hder.
  constructor; trivial.
  apply DerivableTFR_replace_fr; trivial.
Qed.        

Lemma DerivableTFR_replace_fr2 : forall e E2 Ctx2,
    typesCtx P (TFRcdecl e) (TFRmdecl e) (TFRXi e) (TFRGamma e) E2 Ctx2 (TFRAcid e) ->
    DerivableTFR e ->
    DerivableTFR (replace_fr_in_tfr ( Ctx2[[E2]]_ None) e).
Proof.
  intros until 0.
  destruct e.
  simpl.
  intuition.
Qed.


End RedInvariants.

Hint Resolve fields_unique.
Hint Resolve DerivableTFS_wfs.
Hint Resolve DerivableTFS_ConsistentTFR.
Hint Resolve DerivableTFS_further.
Hint Resolve ConsistentTFS_one ConsistentTFS_DTFR_DerivableTFS.
Hint Resolve DerNU_first.
Hint Immediate DerNU_first'.
Hint Immediate DerNU_second'.
Hint Resolve DerNU_second.
Hint Resolve isDtfs_isNtfs.
Hint Resolve isDtfs_isNtfs_ex.
Hint Resolve isDtfs_isNtfs_env.
Hint Resolve isDtfs_isNtfs.
Hint Resolve fields_unique.
Hint Resolve ConsistentTFR_isNonNullLoc.
Hint Resolve ConsistentTFR_names_unique.
Hint Resolve ConsistentTFR_HeapAgreesEnv.
Hint Resolve ConsistentTFR_update_env.
