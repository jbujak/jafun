Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.
Require Import JaUtils.
Require Import JaSyntax.
Require Import JaProgram.
Require Import JaSubtype.
Require Import JaProgramWf.
Require Import JaTactics.
Require Import JaUnique.
Open Scope list_scope.
Open Scope nat_scope.    
Require Import Omega.

(*-------------------------- Objects ------------------------------------------*)

Require Import Coq.Structures.Equalities.

Module JFXIdDecidable <: DecidableType.
  Definition t := JFXId.
  Definition eq := @eq t.
  Include EqNotation.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Instance eq_equiv : Equivalence eq.
  Proof.
    split; red; firstorder.
    eapply eq_trans; eassumption.
  Qed.
  Definition eq_dec := string_dec.
End JFXIdDecidable.

Module JFXIdMap := FMapWeakList.Make(JFXIdDecidable).

Definition RawObj := JFXIdMap.t Loc.  (* JFXId => Loc *)
Module RawObj := JFXIdMap. (* to make it possible to use RawObj.find instead JFXIdMap.find *)

(*
Definition find k (m: map_nat_nat) := M.find k m.

Definition update (p: nat * nat) (m: map_nat_nat) :=
  M.add (fst p) (snd p) m.

Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ).
*)


Definition Obj : Type := (RawObj * JFClassName)%type.

(*
Definition get_fields (CC:JFProgram) : JFCId -> list JFXId :=
*)

(**
    The function creates an object of the given class name [cname]
    with the fields from [flds] initialised to <[null].

    This is as defined in Figure {fig:auxiliary-notation} as \emptyclass(cname).
*)
Definition emptyclass (flds : list JFXId) (cname : JFClassName) : Obj :=
  let create_initial_obj_aux :=
      fix F flds o :=
        match flds with
        | [] => o
        | hd :: tl => F tl (JFXIdMap.add hd null o)
        end
  in (create_initial_obj_aux flds (JFXIdMap.empty Loc), cname).


Definition init_obj_aux (o:RawObj) (ll:list (JFXId * Loc)) : RawObj :=
  fold_left (fun o '(x,l) => JFXIdMap.add x l o) ll o. 


Module JFXId.
  Import JFXIdDecidable.
  Definition name:=t.
  Definition name_dec := eq_dec.
End JFXId.
  
Module JFXIds := JFXId <+ NameUniq.


Lemma init_obj_aux_invariant1 :
  forall ll1 o ll2, (forall k l, In (k,l) ll2 -> JFXIdMap.MapsTo k l o) ->
               JFXIds.names_unique fst (ll1++ll2) ->
               (forall k l, In (k,l) (ll1++ll2) -> JFXIdMap.MapsTo k l (init_obj_aux o ll1)).
Proof.
  induction ll1 as [ | a ll1]; trivial.
  (* z In (k,l) ((a :: ll1) ++ ll2) powinno się odczytać, że _albo_ k,l=a _albo_ k,l\in(l1++l2) *)
  simpl.
  intros * H HU * [Heq | HIn].
  + subst a.
    eapply IHll1 with (ll2:=(k,l)::ll2).
    - intros *.
      intros [ [= <- <-] | HIn].
      * apply JFXIdMap.add_1; trivial.
      * apply JFXIdMap.add_2; auto 2.
        eapply JFXIds.names_unique_zero in HU; eauto 1.
        simpl in HU.
        eapply JFXIds.name_noocc_In_decl_neq in HU; swap 1 2; eauto 3 with datatypes.
    - auto.    
    - auto with datatypes.  
  + destruct a.
    eapply IHll1 with (ll2:=(k0,l0)::ll2).
    - clear k l HIn.
      intros k l HIn.
      destruct HIn as [[= -> ->] | HIn].
      * apply JFXIdMap.add_1; trivial.
      * apply JFXIdMap.add_2; auto 2.
        eapply JFXIds.names_unique_zero in HU; eauto 1.
        simpl in HU.
        eapply JFXIds.name_noocc_In_decl_neq in HU; swap 1 2; eauto 3 with datatypes.
    - auto.
    - edestruct in_app_or; eauto 1; auto 4 with datatypes.
Qed.


Lemma init_obj_aux_invariant2:
  forall ll1 o ll2, (forall k l, JFXIdMap.MapsTo k l o -> In (k,l) ll2) ->
               JFXIds.names_unique fst (ll1++ll2) ->
               (forall k l, JFXIdMap.MapsTo k l (init_obj_aux o ll1) -> In (k,l) (ll1++ll2)).
Proof.
  induction ll1 as [ | a ll1]; trivial.
  simpl.
  intros * H HU * Hm.
  eapply IHll1 with (ll2:=a::ll2) in Hm.
  - apply in_app_or in Hm.
    simpl in Hm.
    rewrite -> in_app_iff.
    tauto.
  - intros k0 l0 Hm0.
    destruct a as (k1,l1).
    destruct (JFXIds.name_dec k1 k0) as [e|e].
    + eapply JFXIdMap.add_1 in e as Hm0'.
      apply JFXIdMap.find_1 in Hm0.
      apply JFXIdMap.find_1 in Hm0'.
      rewrite Hm0 in Hm0'.
      injection Hm0'; intro; subst; simpl; auto.
    + simpl; apply JFXIdMap.add_3 in Hm0; auto.
  - auto.
Qed.

Lemma init_obj_aux_invariant:
  forall ll1 o ll2, (forall k l, JFXIdMap.MapsTo k l o <-> In (k,l) ll2) ->
               JFXIds.names_unique fst (ll1++ll2) ->
               (forall k l, JFXIdMap.MapsTo k l (init_obj_aux o ll1) <-> In (k,l) (ll1++ll2)).
Proof.
  intros.
  split.
  - apply init_obj_aux_invariant2; trivial.
    firstorder.
  - apply init_obj_aux_invariant1; trivial.
    firstorder.
Qed.


Definition init_obj (flds : list JFXId) (cname : JFClassName) (vals : list Loc) : option Obj :=
(*
  let init_obj_aux :=
      fix F flds vals (o : RawObj) : option RawObj :=
        match flds, vals with
        | [], [] => Some o
        | fhd :: ftl, vhd :: vtl => F ftl vtl (JFXIdMap.add fhd vhd o)
        | _, _ => None
        end
  in
*)
  match zip flds vals with
  | None => None
  | Some ll => Some (init_obj_aux (JFXIdMap.empty _) ll, cname)
  end.

Lemma init_obj_exists:
  forall flds cname vals, length flds = length vals -> 
                     exists o, init_obj flds cname vals = Some (o, cname).
Proof.
  intros * Hz.
  unfold init_obj.
  apply length_zip in Hz.
  destruct Hz as (ll & Hz).
  eexists.
  rewrite Hz.
  eauto 1.
Qed.  

Lemma init_obj_prop:
  forall flds cname vals ll o,
    JFXIds.names_unique (fun x=>x) flds ->
    zip flds vals = Some ll ->
    init_obj flds cname vals = Some (o, cname) ->
    forall v l, JFXIdMap.find v o = Some l <-> In (v,l) ll.
Proof.
  intros * Hfu Hz.
  unfold init_obj.
  replace (zip _ _) with (Some ll).
  intros [=].
  clear cname.
  replace flds with (map fst ll) in Hfu by eauto 2 using zip_map_fst. 
  rewrite <- JFXIds.move_unique in Hfu by eauto 1.
  evar (e : RawObj).
  pose proof (init_obj_aux_invariant ll e []).
  subst e.
  rewrite app_nil_r in H.
  intros.
  eapply H in Hfu.
  + split.
    ++ intro Hf.
       apply Hfu.
       apply JFXIdMap.find_2.
       subst o.
       eauto 1.
    ++ intro HIn.
       apply Hfu in HIn.
       subst o.
       now apply JFXIdMap.find_1.
  + clear v l.
    intros v l.
    simpl.
    split. 
    ++ apply JFXIdMap.empty_1.
    ++ tauto.
Qed.
  
(*
Lemma init_obj_res:
  forall flds cname vals ll, JFXIds.names_unique (fun x=>x) flds -> zip flds vals = Some ll ->
                        exists o, init_obj flds cname vals = Some (o, cname) /\
                             forall v l, JFXIdMap.find v o = Some l <-> In (v,l) ll.
Proof.
  intros * Hfu Hz.
  eexists.
  split.
  - unfold init_obj.
    replace (zip _ _) with (Some ll).
    eauto 1.
  - clear cname.
    replace flds with (map fst ll) in Hfu by eauto 2 using zip_map. 
    rewrite <- JFXIds.move_unique in Hfu by eauto 1.
    evar (o : RawObj).
    pose proof (init_obj_aux_invariant ll o []).
    subst o.
    rewrite app_nil_r in H.
    intros.
    eapply H in Hfu.
    + split.
      ++ intro Hf.
         apply Hfu.
         apply JFXIdMap.find_2.
         eauto 1.
      ++ intro HIn.
         apply Hfu in HIn.
         now apply JFXIdMap.find_1.
    + clear v l.
      intros v l.
      simpl.
      split. 
      ++ apply JFXIdMap.empty_1.
      ++ tauto.
Qed.
*)


(*-------------------------- Heaps --------------------------------------------*)

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module NatMap := FMapAVL.Make(Nat_as_OT).
Module Heap := NatMap.

Definition Heap : Type :=  NatMap.t Obj. (* Loc => Obj *)

Definition getClassName (h:Heap) (n:nat) :=
  match Heap.find n h with
    | None => None
    | Some (_, cid) => Some cid
  end.

(* --- Initially on a heap --- *)
Definition Object_object := emptyclass [] JFObjectName.
Definition Object_object_loc := 0%nat.
Definition Object_val := JFVLoc (JFLoc Object_object_loc).
Definition NPE_object := emptyclass [] JFNPEName.
Definition NPE_object_loc := 2.
Definition NPE_val := JFVLoc (JFLoc NPE_object_loc).

Definition create_initial_heap :Heap := 
  let h0 := NatMap.add Object_object_loc Object_object (NatMap.empty Obj) in
  let h2 := NatMap.add NPE_object_loc NPE_object h0
  in h2.
  
Definition class (h:Heap) (n : nat) : option JFClassName :=
  match NatMap.find n h with
  | None => None
  | Some (_,c) => Some c
  end.

(* The location [l] is [null] or its type on the heap [h] is a subtype of [D] *)
Definition heap_subtypes CC (h:Heap) l D :=
  match l with
  | null => True
  | JFLoc n => exists ro dn, Heap.find n h = Some(ro, dn) /\
                       subtyping CC (JFClass dn) D
  end.


(** [field_correct_heap CC h robj fd] means that for a given field declaration [fd], 
    a location [l] for the name [fn] of the field [fd] is mentionned in the object [robj]
    and if that location [l] is not [null] then 
      there exists an object [robj'] in the heap 
        such that its class [cn'] is a subtype of the class [fn] of the field 
 *)
Definition field_correct_heap (CC:JFProgram) (h:Heap)
           (robj:RawObj) (fd:JFFieldDeclaration) :=
  match fd with
  | JFFDecl _ fc fn => exists (l:Loc),
      RawObj.find fn robj = Some l /\
      heap_subtypes CC h l fc
  end.
  
  
Definition object_correct_heap CC h robj cn :=
  (* class is declared *)
  (exists cdecl:JFClassDeclaration,
      find_class CC cn = Some cdecl)
  /\
  (* class has fields *)
  exists fields, flds_overline CC (JFClass cn) = Some fields
  /\
  (* all the fields of the object are in the class *)
  (forall (v:JFXId) (l:Loc), JFXIdMap.find v robj = Some l ->
                        exists fdecl, In fdecl fields /\ name_of_fd fdecl = v)
  /\
  (* all fields of the class are in the object and are null or have right type on the heap *)
  Forall (field_correct_heap CC h robj) fields.
  

Definition type_correct_heap CC h : Prop :=
  (* all locations have correct object *)
  (forall (n : nat) (robj:RawObj) (cn:JFClassName),
      Heap.find n h = Some (robj,cn) ->
      object_correct_heap CC h robj cn)
  /\
  (* NPE object is as expected *)
  Heap.find NPE_object_loc h = Some NPE_object.
                        

Lemma type_correct_heap_find_class:
  forall CC h n robj cn,
    type_correct_heap CC h -> 
    Heap.find n h = Some (robj,cn) ->
    exists (cdecl:JFClassDeclaration),
      find_class CC cn = Some cdecl.
Proof.
  intros * Tch H.
  now apply Tch in H as [? _].
Qed.

Hint Resolve type_correct_heap_find_class.


Module FieldNames <: Declaration.
  Definition name := JFXId.
  Definition name_dec := JFXId_dec.

  Definition decl := JFFieldDeclaration.
  Definition name_of_decl : decl -> name := name_of_fd.
End FieldNames.

Module Flds:=FieldNames <+ ListUniq.

Import Flds.Hints.



Lemma type_correct_heap_find_field:
  forall fs P h n oo C x fd,
    type_correct_heap P h ->
    Heap.find (elt:=Obj) n h = Some (oo, C) ->
    flds_overline P (JFClass C) = Some fs ->
    JFXIdMap.find (elt:=Loc) x oo = Some fd ->
    exists fdcs,
      Flds.find fs x = Some fdcs.
Proof.
  intros * [Tch _] H ? Hfnd.
  apply Tch in H as [H (fields & Hflds & Hobj)].
  replace fs with fields by congruence.
  clear dependent fs.
  apply Hobj in Hfnd as (fdecl & HIn & Heq).
  edestruct Flds.In_find_exists; eauto 1.
  intuition.
  eexists.
  eauto 1.
Qed.    

Hint Resolve type_correct_heap_find_field.


Definition alloc (CC:JFProgram) (h:Heap) (cname:JFClassName): Loc * Heap :=
  let domain := NatMap.fold (fun k e res => k :: res) h [] in
  let get_first_free := fix F maxx (prev:nat) (lst:list nat) :=
      match lst with
      | [] => maxx
      | hd :: tl => if (Nat.eqb (hd + 1) prev)
                    then (F maxx hd tl) 
                    else hd + 1
      end in 
   let freeloc := get_first_free 0 0 domain in
   let objflds := flds CC (JFClass cname) in
   let newobject := match objflds with
                    | None => emptyclass [] cname
                    | Some fl => emptyclass fl cname
                    end in
   let newheap := NatMap.add freeloc newobject h
   in (JFLoc freeloc, newheap).
   

Definition newloc (h:Heap) :=
  let keys := map fst (Heap.elements h) in
  match keys with
  | [] => 0
  | h::t => 1 + fold_right max h t
  end.

Lemma newloc_new : forall h l o, Heap.find l h = Some o -> newloc h <> l.
Proof.
  intros * H.
  unfold newloc.
  remember (Heap.elements h) as elts eqn:Heq.
  apply Heap.find_2 in H.
  apply Heap.elements_1 in H.
  rewrite <- Heq in H.
  destruct elts as [ | p].
  { inversion H. }
  simpl.

  enough (l <= fold_right Init.Nat.max (fst p) (map fst elts)) by auto with arith.
  clear Heq.
  destruct p.
  simpl.
  inversion_clear H as [? ? Heqk | ? ? HIn ].
  + simpl.
    compute in Heqk.
    destruct Heqk.
    subst.
    induction elts; simpl; eauto 2 with arith.
  + induction elts as [ | a]; simpl.
    { inversion HIn. }
    destruct a; simpl.
    inversion_clear HIn as [? ? Heqk | ? ? HIn' ].
    - compute in Heqk.
      destruct Heqk.
      subst.
      auto with arith.
    - eauto 3 with arith.
Qed.

Lemma newloc_new_old : forall h l o o1,
    Heap.find l h = Some o1 -> 
    Heap.find l (NatMap.add (newloc h) o h) = Some o1. 
Proof.
  intros * Hf.
  apply Heap.find_1.
  apply Heap.add_2.
  + eauto 2 using newloc_new.
  + now apply Heap.find_2 in Hf.
Qed.
  
Lemma newloc_new_new : forall h o,
    Heap.find (newloc h) (NatMap.add (newloc h) o h) = Some o. 
Proof.
  intros.
  apply Heap.find_1.
  apply Heap.add_1.
  reflexivity.
Qed.


Definition alloc_init (CC:JFProgram) (h:Heap) (cname:JFClassName) (vals: list Loc): option (Loc * Heap) :=
(*  
  (* oszczędna wersja znajdowania nowej lokacji - szuka najmniejszego niezajętego numeru
     - trudna do udowodnienia
     - być może niezgodna z wymaganiem, żeby lokacje miały rosnące numery
  *)
  let domain := NatMap.fold (fun k e res => k :: res) h [] in
  let get_first_free := fix F maxx (prev:nat) (lst:list nat) :=
      match lst with
      | [] => maxx
      | hd :: tl => if (Nat.eqb (hd + 1) prev)
                    then (F maxx hd tl) 
                    else hd + 1
      end in 
   let freeloc := get_first_free 0 0 domain in
 *)
   let freeloc := newloc h in
   let objflds := flds CC (JFClass cname) in
   let newobject := match objflds with
                    | Some fl => init_obj fl cname vals
                    | None => None (* było: init_obj [] cname vals *)
                    end in
   match newobject with
   | Some o => let newheap := NatMap.add freeloc o h
              in Some (JFLoc freeloc, newheap)
   | None => None
   end.



Lemma alloc_init_old_locs : forall CC h cname vals l' h',
    alloc_init CC h cname vals = Some(l',h') ->
    forall l o, Heap.find l h = Some o -> Heap.find l h' = Some o.
Proof.
  intros * H * Hf.
  unfold alloc_init in H.
  destruct flds in H; try discriminate H.
  destruct init_obj in H; try discriminate H.
  simplify_eq H; intros; subst; clear H.
  now apply newloc_new_old.
Qed.


Lemma alloc_init_new_locs : forall CC h cname vals l' h',
    alloc_init CC h cname vals = Some(l',h') ->
    forall l o, Heap.find l h' = Some o -> JFLoc l = l' \/ Heap.find l h = Some o.
Proof.
  intros * H * Hf.
  unfold alloc_init in H.
  destruct flds in H; try discriminate H.
  destruct init_obj in H; try discriminate H.
  simplify_eq H; intros; subst; clear H.
  edestruct Nat.eq_dec as [Heq|Hne].
  + left.
    f_equal.
    exact Heq.
  + right.
    apply Heap.find_1.
    eapply Heap.add_3.
    { eauto 2. }
    eapply Heap.find_2.
    eauto 1.
Qed.    

    
    
Inductive JFContextNode : Set :=
| JFCtxLet (C:JFClassName) (x:JFXId) (Ctx:unit) (E2:JFExpr)
| JFCtxTry (Ctx:unit) (mu:JFAMod) (C:JFClassName) (x:JFXId) (E2:JFExpr).

Definition JFContext : Set := list JFContextNode.

Definition JFEvMode : Set := option JFClassName.

Definition NPE_mode := Some JFNPEName.

Inductive Frame :=
  MkFrame (Ctx:JFContext) (E:JFExpr) (A:JFEvMode).



Definition FrameStack := list Frame.


Notation __ := (tt).  
Notation "Ctx [[ E ]]_ A" := (MkFrame Ctx E A) (at level 60).
Notation "Ctx _[ Ctxa _[[_ E _]]_ A ]_" := (MkFrame (Ctxa :: Ctx) E A) (at level 20).

Fixpoint well_formed_framestack_aux fs :=
  match fs with
  | [] => True
  | Ctx [[ (JFInvoke (JFVLoc (JFLoc n)) _ _) ]]_ None :: fstl => well_formed_framestack_aux fstl
  | _ => False
  end.

Definition well_formed_framestack fs :=
  match fs with
  | [] => False
  | _ :: fstl => well_formed_framestack_aux fstl
  end.

  
(* TODO: ujednolicić prezentację identyfikatorów l, l1... w kolejności występowania *)

Lemma find_field_in_subclass:
  forall P C C' D fldlst rep x n h o,
    subtype_well_founded P ->
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    type_correct_heap P h ->
    flds_overline P C = Some fldlst ->
    In (JFFDecl rep C' x) fldlst ->
    Heap.find (elt:=Obj) n h = Some (o, D) ->
    subtyping P (JFClass D) C ->
    exists l,
      JFXIdMap.find (elt:=Loc) x o = Some l.
Proof.
  intros * ? ? ? ? [Tch _] Hflds HfIn Hfind Hsub.
  apply Tch in Hfind as Hocf.  
  destruct Hocf as ([ddecl Hdecl] & fields & HfldsD & Hobj & Hcf).
  eapply flds_overline_find_class_decompose in Hsub as [fldsn HfldsD2]; eauto 1.
  rewrite -> Forall_forall in Hcf.
  replace fields with (fldsn ++ fldlst) in * by congruence.
  eapply or_intror in HfIn.
  eapply in_or_app in HfIn.
  apply Hcf in HfIn as (l & Heq & _).
  eauto 2.
Qed.  


Definition getInvokeBody CC D0 (n:nat) m vs (h:Heap) Ctx Cc := 
  match D0 with
    | None => None
    | Some D =>
      let mm := methodLookup CC D m in
      match mm with
        | None => None
        | Some mn =>
          let E := body_of_md mn in
          let frmls := map JFVar (params_of_md mn) in
          let Esub := substList frmls vs
                                (substExpr JFThis  (JFLoc n) E) in
          match Esub with
            | None => None
            | Some Es =>
              Some (h, (nil [[ Es ]]_ None) ::
                       (Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None ) :: Cc)
          end
      end
  end.

Lemma getInvokeBody_Some:
  forall P D n m vs h h' Ctx Cc Cc',
    getInvokeBody P D n m vs h Ctx Cc = Some (h', Cc') ->
    exists hd1 hd2, Cc' = hd1 :: hd2 :: Cc /\ h = h'.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct D;try discriminate H.
  destruct (methodLookup P j m); try discriminate H.
  destruct (substList (map JFVar (params_of_md j0)) vs
                      (substExpr JFThis (JFLoc n) (body_of_md j0)));
    try discriminate H.
  injection H;intros.
  rewrite <- H0.
  eexists;eauto.
Qed.


Lemma getInvokeBody_Some_Invoke:
  forall P D n m vs h h' Ctx Cc Cc',
    getInvokeBody P D n m vs h Ctx Cc = Some (h', Cc') ->
    exists hd1, Cc' = hd1 :: (Ctx [[JFInvoke (JFVLoc (JFLoc n)) m vs ]]_ None) :: Cc /\ h = h'.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct D;try discriminate H.
  destruct (methodLookup P j m); try discriminate H.
  destruct (substList (map JFVar (params_of_md j0)) vs
                      (substExpr JFThis (JFLoc n) (body_of_md j0)));
    try discriminate H.
  injection H;intros.
  rewrite <- H0.
  eexists;eauto.
Qed.


Lemma getInvokeBody_Some_ClassName:
  forall P D n m vs h h' Ctx Cc Cc',
    getInvokeBody P D n m vs h Ctx Cc = Some (h', Cc') ->
    exists Dd, D = Some Dd.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct D; try discriminate H.
  eexists;eauto.
Qed.

Lemma getInvokeBody_Some_methodLookup:
  forall P Dd n m vs h h' Ctx Cc Cc',
    getInvokeBody P (Some Dd) n m vs h Ctx Cc = Some (h', Cc') ->
    exists md, methodLookup P Dd m = Some md.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct (methodLookup P Dd m); try discriminate H.
  eexists;eauto.
Qed.


Lemma getInvokeBody_Some_find_class:
  forall P Dd n m vs h h' Ctx Cc Cc',
    getInvokeBody P (Some Dd) n m vs h Ctx Cc = Some (h', Cc') ->
    exists ddecl, find_class P Dd = Some ddecl.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct (methodLookup P Dd m) eqn:MthdLkp; try discriminate H.
  eapply methodLookup_find_class.
  eauto.
Qed.

Lemma getInvokeBody_retTypM:
  forall P cn n m vs h h' Ctx Cc Cc',
    getInvokeBody P (Some cn) n m vs h Ctx Cc = Some (h', Cc') ->
    exists acid, retTypM P (JFClass cn) m = Some acid.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct (methodLookup P cn m) eqn:MthdLkp; try discriminate H.
  simpl in MthdLkp.
  unfold retTypM.
  rewrite MthdLkp.
  eexists;eauto.
Qed.
  
Definition loc_of_val v := match v with JFVLoc l => Some l | _ => None end.

Fixpoint list_map_opt {A B} (f:A -> option B) l :=
  match l with
  | [] => Some []
  | h::t =>
    match f h with
    | None => None
    | Some b =>
      match list_map_opt f t with
      | None => None
      | Some bt => Some (b::bt)
      end
    end
  end.
(*
Definition list_map_opt {A B} (f:A -> option B) l :=
  let F :=
      fix F l acc :=
        match l with
        | [] => Some (List.rev acc) 
        | h::t =>
          match f h with
          | None => None
          | Some b => F t (b::acc)
          end
        end
  in
  F l [].
*)
Definition red  (CC:JFProgram) : Heap * FrameStack -> option (Heap * FrameStack) :=
  fun '(h, st) =>
    match st with
      | [] => None
      | (*newk*)
        Ctx[[JFNew mu C vs]]_ None :: Cc => 
          (*          let (l0, hp) := alloc CC h C *)
          match list_map_opt loc_of_val vs with
          | None => None
          | Some locs => 
            match alloc_init CC h C locs with
            | None => None
            | Some (l0, hp) => Some (hp, Ctx[[JFVal1 (JFVLoc l0)]]_ None :: Cc)
            end
          end
      | (* letin *)
        (Ctx[[ JFLet C x E1 E2 ]]_ None ) :: Cc =>
           Some (h, (Ctx _[ (JFCtxLet C x __ E2 ) _[[_ E1 _]]_ None ]_) :: Cc)
      | (*letgo*)
        (Ctx _[ (JFCtxLet C x _ E) _[[_ (JFVal1 (JFVLoc l)) _]]_ None ]_) :: Cc =>
           Some (h, Ctx[[ substExpr (JFVar x) l E ]]_ None :: Cc)
      | (*ifeq/ifneq*)
        (Ctx[[ JFIf (JFVLoc l1) (JFVLoc l2) E1 E2 ]]_ None ) :: Cc =>
          if Loc_dec l1 l2
          then Some (h, Ctx[[E1]]_ None :: Cc)
          else Some (h, Ctx[[E2]]_ None :: Cc)
      | (* mthdnpe *)
        (Ctx[[ (JFInvoke JFnull _ _) ]]_ None ) :: Cc =>
          Some (h, Ctx[[ JFVal1 NPE_val ]]_ NPE_mode :: Cc)
      | (* mthd *)
        (Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None ) :: Cc =>
        let D0 := getClassName h n in  getInvokeBody CC D0 n m vs h Ctx Cc
      | (* mthdret   *)
        (nil [[JFVal1 (JFVLoc l) ]]_ None) :: (Ctx[[ (JFInvoke _ _ _) ]]_ None ) :: Cc =>
           Some (h, (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ None ) :: Cc)
      | (* assignnpe *)
        (Ctx[[ (JFAssign (JFnull, id) (JFVLoc l)) ]]_ None ) :: Cc =>
           Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
      | (* assignev  *)
        (Ctx[[ (JFAssign (JFVLoc (JFLoc n), x) (JFVLoc l)) ]]_ None ) :: Cc =>
          let o := Heap.find n h
          in match o with
               | None => None
               | Some (ro, cid) =>
                 let modo := (JFXIdMap.add x l ro, cid) in
                 let h1 := Heap.add n modo h
                 in Some (h1, (Ctx[[ JFVal1 (JFVLoc l) ]]_ None ) :: Cc)
             end
      | (* varnpe   *)
        (Ctx[[ (JFVal2 (JFnull, x)) ]]_ None ) :: Cc =>
          Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
      | (* var      *)
        (Ctx[[ (JFVal2 (JFVLoc (JFLoc n), x)) ]]_ None ) :: Cc =>
          let o := Heap.find n h
          in match o with
               | None => None
               | Some (ro, cid) =>
                 let ol1 := JFXIdMap.find x ro
                 in match ol1 with
                      | None => None
                      | Some l1 => Some (h, (Ctx[[ JFVal1 (JFVLoc l1)  ]]_ None ) :: Cc)
                    end
          end
      | (* thrownull *)
        (Ctx[[ (JFThrow JFnull) ]]_ None ) :: Cc =>
          Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
      | (* throw *)
        (Ctx[[ (JFThrow (JFVLoc (JFLoc n))) ]]_ None ) :: Cc =>
          match class h n with
            | None => None
            | Some cname =>
              Some (h, (Ctx[[ JFVal1 (JFVLoc (JFLoc n)) ]]_ (Some cname)) :: Cc)
          end
      | (* ctchin *)
        (Ctx[[ (JFTry E1 mu C x E2) ]]_ None ) :: Cc =>
           Some (h, Ctx _[ (JFCtxTry __ mu C x E2)  _[[_ E1 _]]_ None ]_ :: Cc)

      | (* ctchnrml *)
        (Ctx _[ (JFCtxTry _ mu C x E2)  _[[_ JFVal1 (JFVLoc l) _]]_ None ]_ ) :: Cc =>
           Some (h, (Ctx[[ JFVal1 (JFVLoc l) ]]_ None ) :: Cc)


      | (* letex *)
        (Ctx _[ (JFCtxLet C x _ E) _[[_ (JFVal1 (JFVLoc l)) _]]_ (Some C') ]_) :: Cc =>
           Some (h, (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C') ) :: Cc)
             
      | (* methodex *)
        (nil [[JFVal1 (JFVLoc l) ]]_ (Some C) ) :: (Ctx[[ (JFInvoke _ _ _) ]]_ None ) :: Cc =>
           Some (h, (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ (Some C) ) :: Cc)
                
      | (* ctchexnok/ctchexok *)
        (Ctx _[ (JFCtxTry _ mu C x E2) _[[_ (JFVal1 (JFVLoc l)) _]]_ (Some C') ]_) :: Cc =>
           if subtype_bool CC (JFClass C') (JFClass C) then
             Some (h, Ctx[[ substExpr (JFVar x) l E2 ]]_ None :: Cc) (* ctchexok *)
           else
             Some (h, (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C') ) :: Cc) (* ctchexnok *)
      | _ => None
end.

(*
Unset Printing Matching.
Print red.
*)

(** The same as [red] but cases are more carefully selected, so there
    are less similar cases in proofs over the reduction relation. *)

Definition red2  (CC:JFProgram) 
  : Heap * FrameStack -> option (Heap * FrameStack) :=
  fun '(h, st) =>
    match st with
    | (Ctx [[ E ]]_ Some C') :: Cc =>
        match E with
        | JFVal1 (JFVLoc l) =>
            match Ctx with
            (* methodex *)
            | [] => 
                match Cc with
                | (Ctx0 [[JFInvoke _ _ _ ]]_ None) :: Cc =>
                    Some (h, (Ctx0 [[JFVal1 (JFVLoc l) ]]_ Some C') :: Cc)
                | _ => None
                end
            (* letex *)
            | JFCtxLet C x _ E2 :: Ctx' =>
                Some (h, (Ctx' [[JFVal1 (JFVLoc l) ]]_ Some C') :: Cc)
            (* ctchexnok/ctchexok *)
            | JFCtxTry _ mu C x E2 :: Ctx' =>
                if subtype_class_bool CC C' C
                then (* ctchexok *)
                  Some (h, (Ctx' [[substExpr (JFVar x) l E2 ]]_ None) :: Cc)
                else (* ctchexnok *)
                  Some (h, (Ctx' [[JFVal1 (JFVLoc l) ]]_ Some C') :: Cc)
            end
        | _ => None
        end
    | (Ctx [[E ]]_ None) :: Cc =>
        match E with
        (* newk *)
        | JFNew _ C vs =>
            match list_map_opt loc_of_val vs with
            | Some locs =>
                match alloc_init CC h C locs with
                | Some (l0, hp) => Some (hp, (Ctx [[JFVal1 (JFVLoc l0) ]]_ None) :: Cc)
                | None => None
                end
            | None => None
            end
        (* letin *)
        | JFLet C x E1 E2 => Some (h, Ctx _[ JFCtxLet C x __ E2 _[[_ E1 _]]_ None ]_ :: Cc)
        (* ifeq/ifneq *)
        | JFIf (JFVLoc l1) (JFVLoc l2) E1 E2 =>
          Some (h, (Ctx [[ if Loc_dec l1 l2 then E1 else E2 ]]_ None) :: Cc)
        (* mthdnpe *)
        | JFInvoke JFnull _ _ => Some (h, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: Cc)
        (* mthd *)
        | JFInvoke (JFVLoc (JFLoc n)) m vs => getInvokeBody CC (getClassName h n) n m vs h Ctx Cc
        (* assignnpe *)
        | JFAssign (JFnull, id) (JFVLoc l) => Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
        (* assignev  *)
        | JFAssign (JFVLoc (JFLoc n), x) (JFVLoc l) => 
            let o := Heap.find n h
            in match o with
               | None => None
               | Some (ro, cid) =>
                   let modo := (JFXIdMap.add x l ro, cid) in
                   let h1 := Heap.add n modo h
                   in Some (h1, (Ctx[[ JFVal1 (JFVLoc l) ]]_ None ) :: Cc)
               end
        | JFVal1 (JFVLoc l) => 
            match Ctx with
            (* mthdret *)  
            | [] =>
              match Cc with
              | (Ctx0 [[JFInvoke _ _ _ ]]_ None) :: Cc =>
                  Some (h, (Ctx0 [[JFVal1 (JFVLoc l) ]]_ None) :: Cc)
              | _ => None
              end
            (* letgo *)
            | JFCtxLet _ x _ E :: Ctx => Some (h, (Ctx [[substExpr (JFVar x) l E ]]_ None) :: Cc)
            (* ctchnrml *)
            | JFCtxTry _ _ _ _ _ :: Ctx => Some (h, (Ctx [[JFVal1 (JFVLoc l) ]]_ None) :: Cc)
            end
        (* varnpe   *)
        | JFVal2 (JFnull, _) => Some (h, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: Cc)
        (* var *)
        | JFVal2 (JFVLoc (JFLoc n), x) =>
            match Heap.find (elt:=Obj) n h with
            | Some (ro, _) =>
                match JFXIdMap.find (elt:=Loc) x ro with
                | Some l1 => Some (h, (Ctx [[JFVal1 (JFVLoc l1) ]]_ None) :: Cc)
                | None => None
                end
            | None => None
            end
        | JFThrow JFnull => Some (h, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: Cc)
        | JFThrow (JFVLoc (JFLoc n)) =>
            match class h n with
            | Some cname => Some (h, (Ctx [[JFVal1 (JFVLoc (JFLoc n)) ]]_ Some cname) :: Cc)
            | None => None
            end
        | JFTry E1 mu C x E2 => Some (h, Ctx _[ JFCtxTry __ mu C x E2 _[[_ E1 _]]_ None ]_ :: Cc)
        | _ => None
        end
    | _ => None
    end.

Lemma red_is_red2 : forall CC hfs res, red CC hfs = res ->
                                       red2 CC hfs = res.
  intros until 0.
  intro Red.
  destruct hfs.
  destruct f.
  simpl; trivial.
  destruct f.
  destruct A.
  + (* A = Some j *)
    simpl in Red.
    auto_destr_discr Red; simpl; trivial.
  + (* A = None *)
    simpl.
    simpl in Red.
    repeat destr_discr Red; simpl; trivial.
Qed.


Lemma red_eq_red2 : forall CC hfs, red CC hfs = red2 CC hfs.
  intros.
  symmetry.
  apply red_is_red2.
  reflexivity.
Qed.

Lemma red2_is_red : forall CC hfs res, red2 CC hfs = res ->
                                       red CC hfs = res.
  intros.
  now rewrite red_eq_red2.
Qed.

(* Require Extraction.
Recursive Extraction red.
 *)