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
Require Import JaSubtype.
Require Import Bool.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import FMapFacts.


Module HeapFacts := Facts Heap.
Module StrMapFacts := JaIrisCommon.StrMapFacts.
Module NatMapFacts := JaIrisCommon.NatMapFacts.
Module JFXIdMapFacts := Facts JFXIdMap.


Definition PiMapsTo l1 l2 (pi : HeapPermutation) :=
  match (l1, l2) with
  | (null, null) => True
  | (JFLoc n1, JFLoc n2) => NatMap.MapsTo n1 n2 (fst pi)
  | _ => False
  end.

Definition Bijection (pi : HeapPermutation) :=
  forall n1 n2, NatMap.MapsTo n1 n2 (fst pi) <-> NatMap.MapsTo n2 n1 (snd pi).

Definition PiCoversHeap (pi : HeapPermutation) (h : Heap) :=
  forall n1, Heap.In n1 h -> exists n2, NatMap.MapsTo n1 n2 (fst pi).

Definition LocsPermuted (f : HeapInjection) (h1 h2 : Heap) :=
  forall n1, Heap.In n1 h1 ->
  exists n2, NatMap.MapsTo n1 n2 f /\ Heap.In n2 h2.

Definition ObjsPermuted (pi : HeapPermutation) (h1 h2 : Heap) :=
  forall n1 n2 o1 cn1 o2 cn2,
    NatMap.MapsTo n1 n2 (fst pi) ->
    Heap.MapsTo n1 (o1, cn1) h1 ->
    Heap.MapsTo n2 (o2, cn2) h2 ->
    (cn1 = cn2 /\ forall f,
      (forall v1, JFXIdMap.MapsTo f v1 o1 -> exists v2, JFXIdMap.MapsTo f v2 o2) /\
      (forall v2, JFXIdMap.MapsTo f v2 o2 -> exists v1, JFXIdMap.MapsTo f v1 o1) /\
      (forall v1 v2,
        JFXIdMap.MapsTo f v1 o1 ->
        JFXIdMap.MapsTo f v2 o2 ->
        PiMapsTo v1 v2 pi)).

Definition HeapsPermuted (h1 h2 : Heap) pi :=
  Bijection pi /\
  LocsPermuted (fst pi) h1 h2 /\
  LocsPermuted (snd pi) h2 h1 /\
  ObjsPermuted pi h1 h2.

Definition EnvsPermuted env1 env2 pi :=
  Bijection pi /\
  (forall x, StrMap.In x env1 <-> StrMap.In x env2) /\
  forall x l1 l2,
    StrMap.MapsTo x l1 env1 -> StrMap.MapsTo x l2 env2 ->
    PiMapsTo l1 l2 pi.


Lemma ExtendedEnvsPermuted : forall env1 env2 x l1 l2 pi,
  EnvsPermuted env1 env2 pi ->
  PiMapsTo l1 l2 pi ->
  EnvsPermuted (StrMap.add x l1 env1) (StrMap.add x l2 env2) pi.
Proof.
  intros env1 env2 x l1 l2 pi.
  intros pi_env pi_l.
  split; [ | split].
  + apply pi_env.
  + intros y.
    destruct (Classical_Prop.classic (x = y)).
    ++ split; intros in_env; now apply StrMapFacts.add_in_iff, or_introl.
    ++ split;
       intros in_env;
       apply StrMapFacts.add_in_iff, or_intror;
       apply StrMapFacts.add_in_iff in in_env;
       destruct in_env; try destruct (H H0);
       now apply (proj1 (proj2 pi_env)).
  + intros x' l1' l2'.
    intros x'_l1' x'_l2'.
    destruct (Classical_Prop.classic (x = x')).
    ++ apply StrMapFacts.find_mapsto_iff in x'_l1'.
       rewrite StrMapFacts.add_eq_o in x'_l1'; trivial.
       apply StrMapFacts.find_mapsto_iff in x'_l2'.
       rewrite StrMapFacts.add_eq_o in x'_l2'; trivial.
       injection x'_l1' as l1_eq.
       injection x'_l2' as l2_eq.
       now rewrite <-l1_eq, <-l2_eq.
    ++ apply StrMapFacts.add_neq_mapsto_iff in x'_l1'; trivial.
       apply StrMapFacts.add_neq_mapsto_iff in x'_l2'; trivial.
       now apply (proj2 pi_env) with (x := x').
Qed.

Lemma InvertedHeapPermutation : forall h1 h2 pi_fst pi_snd,
  HeapsPermuted h1 h2 (pi_fst, pi_snd) ->
  HeapsPermuted h2 h1 (pi_snd, pi_fst).
Proof.
  intros h1 h2 pi_fst pi_snd pi_h.
  unfold HeapsPermuted in pi_h |- *.
  simpl in *.
  destruct pi_h as (bijection & locs_fst & locs_snd & pi_h).
  split; [ | split; [ | split]]; trivial.
  + unfold Bijection in *.
    simpl in *.
    intros n1 n2.
    split; apply (bijection n2 n1).
  + unfold ObjsPermuted in *.
    intros n2 n1 o2 cn2 o1 cn1.
    intros n2_n1_snd n2_o2_h2 n1_o1_h1.
    apply bijection in n2_n1_snd as n1_n2_fst.
    destruct (pi_h n1 n2 o1 cn1 o2 cn2 n1_n2_fst n1_o1_h1 n2_o2_h2)
      as (cn_eq & field_mapsto).
    symmetry in cn_eq.
    split; trivial.
    intros f.
    destruct (field_mapsto f) as (o1_fields & o2_fields & field_map).
    clear field_mapsto.
    split; [ | split]; trivial.
    intros v2 v1 f_v2_o2 f_v1_o1.
    simpl in *.
    assert (v1_mapsto_v2 := field_map v1 v2 f_v1_o1 f_v2_o2).
    unfold PiMapsTo in v1_mapsto_v2 |- *.
    simpl in *.
    destruct v2, v1; trivial.
    now apply bijection.
Qed.

Lemma InvertedEnvPermutation : forall env1 env2 pi_fst pi_snd,
  EnvsPermuted env1 env2 (pi_fst, pi_snd) ->
  EnvsPermuted env2 env1 (pi_snd, pi_fst).
Proof.
  intros env1 env2 pi_fst pi_snd.
  intros pi_env.
  unfold EnvsPermuted in *.
  destruct pi_env as (bijection & same_keys & pi_env).
  split; [ | split]; try easy.
  intros x l2 l1.
  intros x_l2_env2 x_l1_env1.
  assert (l1_mapsto_l2 := pi_env x l1 l2 x_l1_env1 x_l2_env2).
  unfold PiMapsTo in l1_mapsto_l2 |- *.
  simpl in *.
  destruct l2, l1; trivial.
  now apply bijection.
Qed.

Lemma InvertPermutation : forall pi, exists pi',
  (forall h1 h2, HeapsPermuted h1 h2 pi <-> HeapsPermuted h2 h1 pi') /\
  (forall env1 env2, EnvsPermuted env1 env2 pi <-> EnvsPermuted env2 env1 pi').
Proof.
  intros (pi_fst, pi_snd).
  exists (pi_snd, pi_fst).
  split.
  + intros h1 h2.
    split; now apply InvertedHeapPermutation.
  + intros env1 env2.
    split; now apply InvertedEnvPermutation.
Qed.

Definition TryPermuteLoc (loc : Loc) (pi : HeapPermutation) :=
  match loc with
  | null => Some null
  | JFLoc n =>
      match (NatMap.find n (fst pi)) with
      | Some n' => Some (JFLoc n')
      | None => None
      end
   end.

Fixpoint TryPermuteObjFlds (flds : list (JFXId * Loc)) (pi : HeapPermutation) :=
  match flds with
  | [] => Some (JFXIdMap.empty Loc)
  | (field_name, loc)::flds =>
    match (TryPermuteLoc loc pi, TryPermuteObjFlds flds pi) with
    | (Some new_loc, Some new_flds) => Some (JFXIdMap.add field_name new_loc new_flds)
    | _ => None
    end
  end.

Definition TryPermuteObj (obj : Obj) (pi : HeapPermutation) :=
  match obj with
  | (o, cn) => match TryPermuteObjFlds (JFXIdMap.elements o) pi with
    | Some new_obj => Some (new_obj, cn)
    | None => None
    end
  end.

Fixpoint TryPermuteHeapElements (objs : list (nat * Obj)) (pi : HeapPermutation) :=
  match objs with
  | [] => Some (Heap.empty Obj)
  | (n, obj)::objs =>
    match (NatMap.find n (fst pi), TryPermuteObj obj pi, TryPermuteHeapElements objs pi) with
    | (Some new_n, Some new_obj, Some new_heap) => Some (Heap.add new_n new_obj new_heap)
    | _ => None
    end
  end.

Definition TryPermuteHeap (h : Heap) (pi : HeapPermutation) :=
  TryPermuteHeapElements (Heap.elements h) pi.

Lemma ObjFldsAux : forall n (pi : HeapPermutation) field_name n' obj',
NatMap.find (elt:=nat) n (fst pi) = Some n' ->
match
  match NatMap.find (elt:=nat) n (fst pi) with
  | Some n'0 => Some (JFLoc n'0)
  | None => None
  end
with
| Some new_loc => Some (JFXIdMap.add field_name new_loc obj')
| None => None
end = Some (JFXIdMap.add field_name (JFLoc n') obj').
Proof.
  intros n pi field_name n' obj' n_n'_pi.
  now rewrite n_n'_pi.
Qed.

Lemma SuccessfulObjFldsPermutation : forall flds pi,
  (forall f n, In (f, (JFLoc n)) flds -> NatMap.In n (fst pi)) ->
  exists obj', TryPermuteObjFlds flds pi = Some obj'.
Proof.
  intros flds pi flds_in_p.
  induction flds.
  now exists (JFXIdMap.empty Loc).
  destruct a as (field_name & loc).
  destruct IHflds as (obj' & flds_perm).
  + intros f n in_flds.
    apply (flds_in_p f n).
    now apply in_cons.
  + destruct loc.
    ++ exists (JFXIdMap.add field_name null obj').
       simpl.
       now rewrite flds_perm.
    ++ destruct (flds_in_p field_name n) as (n' & n'_perm).
       now apply in_eq.
       simpl.
       exists (JFXIdMap.add field_name (JFLoc n') obj').
       apply NatMapFacts.find_mapsto_iff in n'_perm.
       rewrite flds_perm.
       now apply ObjFldsAux.
Qed.

Lemma SuccessfulObjPermutation : forall obj pi,
  (forall f n, JFXIdMap.find f (fst obj) = Some (JFLoc n) -> NatMap.In n (fst pi)) ->
  exists obj', TryPermuteObj obj pi = Some obj'.
Proof.
  intros obj pi fields_in_pi.
  unfold TryPermuteObj.
  destruct obj as (obj & cn).
  destruct (SuccessfulObjFldsPermutation (JFXIdMap.elements obj) pi) as (obj' & obj_perm).
  + intros f n f_n_obj.
    apply fields_in_pi with (f := f).
    apply JFXIdMapFacts.find_mapsto_iff.
    rewrite JFXIdMapFacts.elements_mapsto_iff.
    apply In_InA with (x := (f, JFLoc n)); trivial.
    now exact JFXIdMapEqKeyEltEquivalence.
  + exists (obj', cn).
    now rewrite obj_perm.
Qed.

Lemma HeapPermutationAux : forall n (pi : HeapPermutation) n' obj' (h' : Heap),
  NatMap.find (elt:=nat) n (fst pi) = Some n' ->
  match NatMap.find (elt:=nat) n (fst pi) with
  | Some new_n => Some (Heap.add new_n obj' h')
  | None => None
  end = Some (Heap.add n' obj' h').
Proof.
  intros.
  now rewrite H.
Qed.

Lemma SuccessfulHeapElementsPermutation : forall objs pi,
  (forall n obj f f_n,
      In (n, obj) objs ->
      JFXIdMap.find f (fst obj) = Some (JFLoc f_n) ->
      NatMap.In f_n (fst pi)
  ) ->
  (forall n obj, In (n, obj) objs -> exists n', NatMap.MapsTo n n' (fst pi)) ->
  exists h', TryPermuteHeapElements objs pi = Some h'.
Proof.
  intros objs pi.
  induction objs.
  now exists (Heap.empty Obj).
  intros flds_in_pi a_objs_in_pi.
  destruct IHobjs as (h' & objs_perm); trivial.
  + intros n obj f f_n n_obj_obj f_fn_obj.
    apply (flds_in_pi n obj f); trivial.
    now apply in_cons.
  + intros n obj n_obj_objs.
    apply (a_objs_in_pi n obj); trivial.
    now apply in_cons.
  + destruct a as (n & obj).
    destruct (SuccessfulObjPermutation obj pi) as (obj' & obj_perm).
    ++ intros f f_n f_fn_obj.
       apply (flds_in_pi n obj f); trivial.
       now apply in_eq.
    ++ destruct (a_objs_in_pi n obj) as (n' & n_n'_pi).
       now apply in_eq.
    exists (Heap.add n' obj' h').
    simpl.
    rewrite NatMapFacts.find_mapsto_iff in n_n'_pi.
    rewrite obj_perm, objs_perm.
    now apply HeapPermutationAux.
Qed.

Lemma SuccessfulPermutation : forall h pi,
  HeapConsistent h ->
  PiCoversHeap pi h ->
  exists h', TryPermuteHeap h pi = Some h'.
Proof.
  intros h pi consistent covers.
  unfold TryPermuteHeap.
  destruct (SuccessfulHeapElementsPermutation (Heap.elements h) pi)
    as (h' & h_perm).
  + unfold PiCoversHeap in covers.
    intros n obj f f_n n_obj_h f_fn_obj.
    destruct (consistent n obj f f_n).
    ++ apply HeapFacts.elements_mapsto_iff.
       apply In_InA; trivial.
       exact HeapEqKeyEltEquivalence. 
    ++ now apply JFXIdMapFacts.find_mapsto_iff in f_fn_obj.
    ++ apply covers.
       apply NatMapFacts.elements_in_iff.
       exists x.
       now apply NatMapFacts.elements_mapsto_iff.
  + unfold PiCoversHeap in covers.
    intros n obj n_obj_h.
    destruct (covers n); trivial.
    ++ apply HeapFacts.elements_in_iff.
       exists obj.
       apply In_InA; trivial.
       exact HeapEqKeyEltEquivalence.
    ++ now exists x. 
  + now exists h'.
Qed.

Lemma SuccessfulPermutationIsLocsPermutation : forall h pi n1 obj h',
  TryPermuteHeapElements (Heap.elements h) pi = Some h' ->
  In (n1, obj) (Heap.elements h) ->
  exists n2,
    NatMap.MapsTo n1 n2 (fst pi) /\
    Heap.In (elt:=Obj) n2 h'.
Proof.
  intros h pi n1 obj.
  induction (Heap.elements h); intros h'.
  intros _ in_empty.
  exfalso.
  now apply in_nil in in_empty.
  intros perm n1_in_al.
  destruct (Classical_Prop.classic ((n1, obj) = a)).
  + rewrite <-H in perm.
    simpl in perm.
    destruct (Classical_Prop.classic (exists n2, NatMap.find n1 (fst pi) = Some n2)).
    ++ destruct H0 as (n2 & n1_n2_pi).
       exists n2.
       rewrite n1_n2_pi in perm.
       apply NatMapFacts.find_mapsto_iff in n1_n2_pi.
       split; trivial.
       destruct (TryPermuteObj obj pi), (TryPermuteHeapElements l pi); try discriminate perm.
       injection perm as h'_eq.
       rewrite <- h'_eq.
       apply HeapFacts.add_in_iff.
       now apply or_introl.
    ++ destruct (NatMap.find n1 (fst pi)); try discriminate perm.
       exfalso.
       apply H0.
       now exists n.
  + simpl in perm.
       destruct a.
       destruct (NatMap.find (elt:=nat) k (fst pi)); try discriminate perm.
       destruct (TryPermuteObj o pi); try discriminate perm.
       destruct (TryPermuteHeapElements l pi); try discriminate perm.
       injection perm as h'_eq.
       rewrite <-h'_eq.
       apply in_inv in n1_in_al.
       destruct n1_in_al.
       now symmetry in H0.
       destruct (IHl t) as (n2 & n1_n2_pi & n2_in_t); trivial.
       exists n2.
       split; trivial.
       now apply HeapFacts.add_in_iff, or_intror.
Qed.

Lemma InElementsAdd : forall n n' o p t,
  n <> n' ->
  In (n, o) (Heap.elements (elt:=Obj) (Heap.add n' p t)) ->
  In (n, o) (Heap.elements t).
Proof.
  intros n n' o p t.
  intros neq in_elements.
  apply In_InA with (eqA := Heap.eq_key_elt (elt:=Obj)) in in_elements;
  try apply HeapEqKeyEltEquivalence.
  apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in in_elements.
  apply neq_symmetry in neq.
  rewrite HeapFacts.add_neq_o in in_elements; trivial.
  apply HeapFacts.find_mapsto_iff, HeapFacts.elements_mapsto_iff in in_elements.
    apply InA_alt in in_elements.
    destruct in_elements as ((n1, o1) & y_eq & y_in_h).
    unfold Heap.eq_key_elt, Heap.Raw.Proofs.PX.eqke in y_eq.
    simpl in y_eq.
    now rewrite (proj1 y_eq), (proj2 y_eq).
Qed.

Lemma SuccessfulPermutationIsSndLocsPermutation : forall pi1 pi2 h h' n2 obj,
  Bijection (pi1, pi2) ->
  TryPermuteHeap h (pi1, pi2) = Some h' ->
  In (n2, obj) (Heap.elements h') ->
  exists n1 : nat,
    NatMap.MapsTo n2 n1 (snd (pi1, pi2)) /\
    Heap.In (elt:=Obj) n1 h.
Proof.
  intros pi1 pi2 h.
  unfold TryPermuteHeap.
  assert (in_h : forall a, In a (Heap.elements h) -> Heap.In (fst a) h).
  intros (a1, a2) a_in_h.
  apply HeapFacts.elements_in_iff.
  apply In_InA with (eqA := Heap.eq_key_elt (elt:=Obj)) in a_in_h.
  now exists a2.
  now apply HeapEqKeyEltEquivalence.
  induction (Heap.elements h); intros h' n2 obj bijection pi_h n2_obj_h'.
  + simpl in pi_h.
    injection pi_h as h'_empty.
    rewrite <-h'_empty in n2_obj_h'.
    destruct n2_obj_h'.
  + destruct a as (n & obj_n).
    destruct (Classical_Prop.classic (NatMap.MapsTo n n2 pi1)).
    ++ exists n.
       split.
       +++ now apply bijection.
       +++ apply (in_h (n, obj_n)).
           apply in_eq.
    ++ simpl in pi_h.
       destruct (Classical_Prop.classic (exists n', NatMap.find n pi1 = Some n'))
         as [(n' & n_n'_pi1) | ].
       +++ assert (n_eq := n_n'_pi1).
           apply NatMapFacts.find_mapsto_iff in n_n'_pi1.
           destruct (NatMap.find n pi1); try discriminate pi_h.
           destruct (TryPermuteObj obj_n (pi1, pi2)); try discriminate pi_h.
           destruct (TryPermuteHeapElements l (pi1, pi2)); try discriminate pi_h.
           injection pi_h as h'_eq.
           rewrite <-h'_eq in n2_obj_h'.
           assert (next_in_h : forall a, In a l -> Heap.In (elt:=Obj) (fst a) h).
           intros a a_in_l.
           apply in_cons with (a := (n, obj_n)) in a_in_l.
           apply (in_h a a_in_l).
           apply (IHl next_in_h t n2 obj); trivial.
           apply InElementsAdd with (n' := n0) (p := p); trivial.
           injection n_eq as n_eq.
           intros n2_eq.
           apply H.
           now rewrite n2_eq, n_eq.
       +++ destruct (NatMap.find n pi1); try discriminate pi_h.
           exfalso.
           apply H0.
           now exists n0.
Qed.

Lemma MapsToEq : forall (pi : HeapInjection) n1 n2 n2',
  NatMap.MapsTo n1 n2  pi ->
  NatMap.MapsTo n1 n2' pi ->
  n2 = n2'.
Proof.
  intros pi n1 n2 n2'.
  intros n1_n2_pi n1_n2'_pi.
  apply NatMapFacts.find_mapsto_iff in n1_n2_pi.
  apply NatMapFacts.find_mapsto_iff in n1_n2'_pi.
  rewrite n1_n2'_pi in n1_n2_pi.
  now injection n1_n2_pi.
Qed.

Lemma BijectionIsInjective : forall pi n1 n1' n2,
  Bijection pi ->
  NatMap.MapsTo n1  n2 (fst pi) ->
  NatMap.MapsTo n1' n2 (fst pi) ->
  n1 = n1'.
Proof.
  intros pi n1 n1' n2.
  intros bijection n1_n2_pi n1'_n2_pi.
  apply bijection in n1_n2_pi.
  apply bijection in n1'_n2_pi.
  now apply (MapsToEq (snd pi) n2 n1 n1').
Qed.

Lemma SuccessfulPermutationIsObjPermutation : forall h o1 cn1 n1 objs n2 o2 cn2 h' pi,
  TryPermuteHeapElements ((n1, (o1, cn1)) :: objs) pi = Some h' ->
  NatMap.MapsTo n1 n2 (fst pi) ->
  Heap.MapsTo n1 (o1, cn1) h ->
  Heap.MapsTo n2 (o2, cn2) h' ->
  (cn1 = cn2 /\ forall f,
      (forall v1, JFXIdMap.MapsTo f v1 o1 -> exists v2, JFXIdMap.MapsTo f v2 o2) /\
      (forall v2, JFXIdMap.MapsTo f v2 o2 -> exists v1, JFXIdMap.MapsTo f v1 o1) /\
      (forall v1 v2,
        JFXIdMap.MapsTo f v1 o1 ->
        JFXIdMap.MapsTo f v2 o2 ->
        PiMapsTo v1 v2 pi)).
Proof.
  intros h o1.
  assert (elements_eq : forall f l l',
    In (f, l) (JFXIdMap.elements o1) -> JFXIdMap.MapsTo f l' o1 -> l = l').
    intros f' l l' f'_in_o1 l_l'_o1.
    apply In_InA with (eqA := JFXIdMap.eq_key_elt (elt := Loc)) in f'_in_o1; trivial.
    apply JFXIdMapFacts.elements_mapsto_iff in f'_in_o1.
    apply JFXIdMapFacts.find_mapsto_iff in f'_in_o1.
    apply JFXIdMapFacts.find_mapsto_iff in l_l'_o1.
    rewrite l_l'_o1 in f'_in_o1.
    now injection f'_in_o1.
    now apply JFXIdMapEqKeyEltEquivalence.
  assert (in_o1 : forall a, In a (JFXIdMap.elements o1) -> JFXIdMap.In (fst a) o1).
    intros (a1, a2) a_in_h.
    apply JFXIdMapFacts.elements_in_iff.
    apply In_InA with (eqA := JFXIdMap.eq_key_elt (elt:=Loc)) in a_in_h.
    now exists a2.
    now apply JFXIdMapEqKeyEltEquivalence.
  simpl.
  induction (JFXIdMap.elements o1).
  + intros cn1 n1 objs n2 o2 cn2 h' pi.
    intros pi_h n1_n2_pi n1_o1_h n2_o2_h'.
    simpl in pi_h.
    apply NatMapFacts.find_mapsto_iff in n1_n2_pi.
    rewrite n1_n2_pi in pi_h.
    destruct (TryPermuteHeapElements objs pi); try discriminate pi_h.
    injection pi_h as h'_eq.
    rewrite <-h'_eq in n2_o2_h'.
    apply NatMapFacts.find_mapsto_iff in n2_o2_h'.
    rewrite NatMapFacts.add_eq_o in n2_o2_h'; trivial.
    injection n2_o2_h'.
    intros cn_eq o2_eq.
    split; trivial.
    intros f.
    split; [ | split].
    ++ intros v1 f_v1_o1.
       rewrite <-o2_eq in *.
       exfalso.
       admit.
    ++ intros v2 f_v2_o2.
       rewrite <-o2_eq in f_v2_o2.
       now apply JFXIdMapFacts.empty_mapsto_iff in f_v2_o2.
    ++ intros v1 v2 f_v1_o1 f_v2_o2.
       rewrite <-o2_eq in f_v2_o2.
       now apply JFXIdMapFacts.empty_mapsto_iff in f_v2_o2.
  + intros cn1 n1 objs n2 o2 cn2 h' pi.
    intros pi_h n1_n2_pi n1_o1_h n2_o2_h'.
    simpl in pi_h.
    apply NatMapFacts.find_mapsto_iff in n1_n2_pi.
    rewrite n1_n2_pi in pi_h.
    destruct a as (f' & loc).

    simpl in pi_h.
    assert (new_elements_eq : forall f l0 l',
      In (f, l0) l -> JFXIdMap.MapsTo f l' o1 -> l0 = l').
      intros f0 l1 l' l0_in_l.
      now apply elements_eq, in_cons.
    assert (new_in_o1 : forall a, In a l -> JFXIdMap.In (elt:=Loc) (fst a) o1).
      intros a a_in_l.
      now apply in_o1, in_cons.
    assert (try_permute_loc : exists loc', TryPermuteLoc loc pi = Some loc').
    destruct (TryPermuteLoc loc pi); try discriminate pi_h.
    now exists l0.
    destruct try_permute_loc as (loc' & loc_loc'_pi).
    rewrite loc_loc'_pi in pi_h.
    assert (try_permute_flds : exists new_flds, TryPermuteObjFlds l pi = Some new_flds).
    destruct (TryPermuteObjFlds l pi); try discriminate pi_h.
    now exists t.
    destruct try_permute_flds as (new_flds & new_flds_pi).
    rewrite new_flds_pi in pi_h.
    assert (try_permute_heap : exists new_heap, TryPermuteHeapElements objs pi = Some new_heap).
    destruct (TryPermuteHeapElements objs pi); try discriminate pi_h.
    now exists t.
    destruct try_permute_heap as (new_heap & new_heap_pi).

    assert (IH := IHl new_elements_eq new_in_o1 cn1 n1 objs n2 new_flds cn2
      (Heap.add n2 (new_flds, cn1) new_heap) pi).
    clear IHl.

    rewrite new_heap_pi in pi_h.
    injection pi_h as h'_eq.
    rewrite <-h'_eq in n2_o2_h'.
    apply HeapFacts.find_mapsto_iff in n2_o2_h'.
    rewrite HeapFacts.add_eq_o in n2_o2_h'; trivial.
    rewrite n1_n2_pi, new_flds_pi, new_heap_pi in IH.
    apply NatMapFacts.find_mapsto_iff in n1_n2_pi.
    destruct IH; trivial.
    apply HeapFacts.find_mapsto_iff.
    rewrite HeapFacts.add_eq_o; trivial.
    injection n2_o2_h'.
    intros cn_eq o2_eq.
    now rewrite cn_eq.
    split; trivial.
    intros f.
    destruct (Classical_Prop.classic (f = f')).
    ++ clear H0.
       rewrite <-H1 in *.
       split; [ | split].
       +++ intros v1 f_v1_o1.
           rewrite (elements_eq f loc v1) in *; trivial; try apply in_eq.
           exists loc'.
           injection n2_o2_h' as o2_eq.
           apply JFXIdMapFacts.find_mapsto_iff.
           rewrite <-o2_eq.
           now rewrite JFXIdMapFacts.add_eq_o.
       +++ intros v2 f_v2_o2.
           assert (f_in_o1 := in_o1 (f, loc) (in_eq (f, loc) l)).
           simpl in f_in_o1.
           destruct ((proj1 (JFXIdMapFacts.elements_in_iff o1 f)) f_in_o1) as (v1 & f_v1_o1).
           apply JFXIdMapFacts.elements_mapsto_iff in f_v1_o1.
           now exists v1.
       +++ intros v1 v2 f_v1_o1 f_v2_o2.
           rewrite (elements_eq f loc v1) in *; trivial; try apply in_eq.
           injection n2_o2_h'.
           intros _ o2_eq.
           rewrite <-o2_eq in f_v2_o2.
           apply JFXIdMapFacts.find_mapsto_iff in f_v2_o2.
           rewrite JFXIdMapFacts.add_eq_o in f_v2_o2; trivial.
           injection f_v2_o2 as v2_eq.
           rewrite <-v2_eq in *.
           unfold TryPermuteLoc in loc_loc'_pi.
           destruct v1.
           - injection loc_loc'_pi as loc'_eq.
             now rewrite <-loc'_eq.
           - destruct (Classical_Prop.classic (exists n0, NatMap.find n (fst pi) = Some n0));
             [ | exfalso; apply H0; destruct (NatMap.find n (fst pi)); try discriminate loc_loc'_pi; now exists n0].
             destruct H0 as  (n0 & n_n0_pi).
             rewrite n_n0_pi in loc_loc'_pi.
             injection loc_loc'_pi as loc_eq.
             rewrite <-loc_eq.
             unfold PiMapsTo.
             now apply NatMapFacts.find_mapsto_iff in n_n0_pi.
    ++ injection n2_o2_h'.
       intros _ o2_eq.
       apply neq_symmetry in H1.
       split; [ | split].
       +++ intros v1 f_v1_o1.
           destruct (H0 f) as (IH & _).
           destruct (IH v1 f_v1_o1) as (v2 & f_v2_new_flds).
           exists v2.
           rewrite <-o2_eq.
           apply JFXIdMapFacts.find_mapsto_iff.
           rewrite JFXIdMapFacts.add_neq_o; trivial.
           now apply JFXIdMapFacts.find_mapsto_iff.
       +++ intros v2 f_v2_o2.
           destruct (H0 f) as (_ & IH & _).
           apply IH with (v2 := v2).
           rewrite <-o2_eq in f_v2_o2.
           apply JFXIdMapFacts.find_mapsto_iff in f_v2_o2.
           rewrite JFXIdMapFacts.add_neq_o in f_v2_o2; trivial.
           now apply JFXIdMapFacts.find_mapsto_iff.
       +++ intros v1 v2 f_v1_o1 f_v2_o2.
           apply (H0 f); trivial.
           rewrite <-o2_eq in f_v2_o2.
           apply JFXIdMapFacts.find_mapsto_iff in f_v2_o2.
           rewrite JFXIdMapFacts.add_neq_o in f_v2_o2; trivial.
           now apply JFXIdMapFacts.find_mapsto_iff.
Admitted.

Lemma SuccessfulPermutationIsObjsPermutation : forall h h' pi,
  Bijection pi ->
  TryPermuteHeap h pi = Some h' ->
  ObjsPermuted pi h h'.
Proof.
  intros h.
  unfold TryPermuteHeap.
  assert (in_els_mapsto : forall n obj, In (n, obj) (Heap.elements h) -> Heap.MapsTo n obj h).
  intros n obj n_in_h.
  apply HeapFacts.elements_mapsto_iff.
  apply In_InA with (eqA := Heap.eq_key_elt (elt := Obj)) in n_in_h; trivial.
  apply HeapEqKeyEltEquivalence.
  induction (Heap.elements h).
  + intros h' pi bijection pi_h.
    intros n1 n2 o1 cn1 o2 cn2.
    intros n1_n2_pi n1_o1_h n2_o2_h'.
    exfalso.
    simpl in pi_h.
    injection pi_h as h'_eq.
    rewrite <-h'_eq in n2_o2_h'.
    now apply HeapFacts.empty_mapsto_iff in n2_o2_h'.
  + intros h' pi bijection pi_h.
    intros n1 n2 o1 cn1 o2 cn2.
    intros n1_n2_pi n1_o1_h n2_o2_h'.
    destruct a as (n & obj).
    destruct (Classical_Prop.classic (n = n1)).
    ++ rewrite H in *.
       assert (n1_obj_h := in_els_mapsto n1 obj (in_eq (n1, obj) l)).
       assert (obj_eq : obj = (o1, cn1)).
       apply HeapFacts.find_mapsto_iff in n1_o1_h.
       apply HeapFacts.find_mapsto_iff in n1_obj_h.
       unfold Obj in n1_obj_h.
       rewrite n1_obj_h in n1_o1_h.
       now injection n1_o1_h.
       rewrite obj_eq in pi_h.
       now apply (SuccessfulPermutationIsObjPermutation h o1 cn1 n1 l n2 o2 cn2 h' pi).
    ++ simpl in pi_h.
       assert (exists n', NatMap.find n (fst pi) = Some n').
       destruct (NatMap.find n (fst pi)); try discriminate pi_h.
       now exists n0.
       destruct H0 as (n' & n_pi_n').
       rewrite n_pi_n' in pi_h.
       destruct (TryPermuteObj obj pi); try discriminate pi_h.
       assert (exists h', TryPermuteHeapElements l pi = Some h').
       destruct (TryPermuteHeapElements l pi); try discriminate pi_h.
       now exists t.
       destruct H0 as (rest_h & l_pi_rest_h).
       rewrite l_pi_rest_h in *.
       injection pi_h as h'_eq.
       unfold ObjsPermuted in IHl.
       rewrite <-h'_eq in n2_o2_h'.
       assert (next_in_els : forall n obj, In (n, obj) l -> Heap.MapsTo n obj h).
       intros n0 obj0 n0_in_l.
       now apply in_els_mapsto, in_cons.
       apply (IHl next_in_els rest_h pi bijection l_pi_rest_h n1 n2 o1 cn1 o2 cn2); trivial.
       apply HeapFacts.find_mapsto_iff in n2_o2_h'.
       apply HeapFacts.find_mapsto_iff.
       rewrite HeapFacts.add_neq_o in n2_o2_h'; trivial.
       apply NatMapFacts.find_mapsto_iff in n_pi_n'.
       intros n'_eq_n2.
       rewrite n'_eq_n2 in n_pi_n'.
       apply H.
       now apply (BijectionIsInjective pi n n1 n2).
Qed.

Lemma SuccessfulPermutationIsPermutation : forall h h' pi,
  Bijection pi ->
  TryPermuteHeap h pi = Some h' ->
  HeapsPermuted h h' pi.
Proof.
  intros h h' pi bijection h_pi_h'.
  unfold HeapsPermuted.
  split; [ | split; [ | split]]; trivial.
  + unfold LocsPermuted.
    intros n1 n1_in_h.
    unfold TryPermuteHeap in h_pi_h'.
    apply HeapFacts.elements_in_iff in n1_in_h.
    destruct n1_in_h as (obj1 & n1_obj1_h).
    apply SuccessfulPermutationIsLocsPermutation with (h := h) (obj := obj1); trivial.
    apply InA_alt in n1_obj1_h.
    destruct n1_obj1_h as ((n1', obj1') & y_eq & y_in_h).
    unfold Heap.eq_key_elt, Heap.Raw.Proofs.PX.eqke in y_eq.
    simpl in y_eq.
    now rewrite (proj1 y_eq), (proj2 y_eq).
  + unfold LocsPermuted.
    intros n1 n1_in_h'.
    destruct pi as (pi1 & pi2).
    unfold TryPermuteHeap in h_pi_h'.
    apply HeapFacts.elements_in_iff in n1_in_h'.
    destruct n1_in_h' as (obj1 & n1_obj1_h').
    apply SuccessfulPermutationIsSndLocsPermutation with (h' := h') (obj := obj1); trivial.
    apply InA_alt in n1_obj1_h'.
    destruct n1_obj1_h' as ((n1', obj1') & y_eq & y_in_h).
    unfold Heap.eq_key_elt, Heap.Raw.Proofs.PX.eqke in y_eq.
    simpl in y_eq.
    now rewrite (proj1 y_eq), (proj2 y_eq).
  + now apply SuccessfulPermutationIsObjsPermutation.
Qed.

Lemma ExistsPermutedHeap : forall h pi,
  Bijection pi ->
  PiCoversHeap pi h ->
  exists h', HeapsPermuted h h' pi.
Proof.
  intros h pi bijection covers.
  assert (consistent : HeapConsistent h). admit.
  destruct (SuccessfulPermutation h pi consistent covers) as (h' & try_permute_h_h').
  exists h'.
  now apply SuccessfulPermutationIsPermutation.
Admitted.

Lemma DisjointPermuted : forall h1 h1_perm h2 h2_perm pi,
  JFIHeapsDisjoint h1 h2 ->
  HeapsPermuted h1 h1_perm pi ->
  HeapsPermuted h2 h2_perm pi ->
  JFIHeapsDisjoint h1_perm h2_perm.
Proof.
  intros h1 h1_perm h2 h2_perm pi.
  intros disj pi_h1 pi_h2.
  intros n' (n'_in_h1_perm & n'_in_h2_perm).
  destruct pi_h1 as (bijection & h1_fst & h1_snd & h1_objs).
  destruct pi_h2 as (_ & h2_fst & h2_snd & h2_objs).
  apply h1_snd in n'_in_h1_perm as (n1 & n'_n1_pi & n1_in_h1).
  apply h2_snd in n'_in_h2_perm as (n2 & n'_n2_pi & n2_in_h2).
  apply NatMapFacts.find_mapsto_iff in n'_n1_pi.
  apply NatMapFacts.find_mapsto_iff in n'_n2_pi.
  rewrite n'_n2_pi in n'_n1_pi.
  injection n'_n1_pi as n_eq.
  apply (disj n1).
  split; trivial.
  now rewrite <-n_eq.
Qed.

Lemma PermutedHeapCovered : forall h1 h2 pi,
  HeapsPermuted h1 h2 pi ->
  PiCoversHeap pi h1.
Proof.
  intros h1 h2 pi (_ & locs_permuted & _ & _).
  intros n n_in_h1.
  unfold LocsPermuted in *.
  destruct (locs_permuted n n_in_h1) as (n2 & n1_n2_pi & n2_in_h2).
  now exists n2.
Qed.

Lemma PermutationCoversUnion : forall h1 h2 h pi,
  JFIHeapsUnion h1 h2 h ->
  (PiCoversHeap pi h <-> PiCoversHeap pi h1/\ PiCoversHeap pi h2).
Proof.
  intros h1 h2 h pi.
  intros union_h1_h2.
  split.
  + intro covers_h.
    destruct union_h1_h2 as (h1_subheap & h2_subheap & _).
    split.
    ++ intros n n_in_h1.
       apply HeapFacts.elements_in_iff in n_in_h1 as (o & n_o_h1).
       apply HeapFacts.elements_mapsto_iff in n_o_h1.
       assert (n_o_h := h1_subheap n o n_o_h1).
       apply (covers_h n).
       apply HeapFacts.elements_in_iff.
       exists o.
       now apply HeapFacts.elements_mapsto_iff.
    ++ intros n n_in_h2.
       apply HeapFacts.elements_in_iff in n_in_h2 as (o & n_o_h2).
       apply HeapFacts.elements_mapsto_iff in n_o_h2.
       assert (n_o_h := h2_subheap n o n_o_h2).
       apply (covers_h n).
       apply HeapFacts.elements_in_iff.
       exists o.
       now apply HeapFacts.elements_mapsto_iff.
  + intros (covers_h1 & covers_h2).
    intros n n_in_h.
    destruct union_h1_h2 as (_ & _ & union).
    destruct (union n n_in_h).
    ++ apply (covers_h1 n H).
    ++ apply (covers_h2 n H).
Qed.

Lemma UnionPermuted : forall h1 h1' h2 h2' h h' pi,
  JFIHeapsUnion h1 h2 h ->
  HeapsPermuted h1 h1' pi ->
  HeapsPermuted h2 h2' pi ->
  HeapsPermuted h h' pi ->
  JFIHeapsUnion h1' h2' h'.
Proof.
  intros h1 h1' h2 h2' h h' pi.
  intros union_h1_h2 pi_h1 pi_h2 pi_h.
  split; [ | split].
  + intros n' o' n'_o'_h1'.
    destruct pi_h1 as (bijection & locs_fst_h1 & locs_snd_h1 & _).
    destruct (locs_snd_h1 n') as (n & n'_n_pi & n_in_h1).
    admit.
    destruct union_h1_h2 as (subheap_h1 & subheap_h2 & _).
    apply HeapFacts.elements_in_iff in n_in_h1 as (o & n_o_h1).
    apply HeapFacts.elements_mapsto_iff in n_o_h1.
    assert (n_o_h := subheap_h1 n o n_o_h1).
    apply bijection in n'_n_pi.
    destruct pi_h as (_ & locs_fst_h & locs_snd_h & _).
    unfold LocsPermuted in locs_fst_h.
    destruct (locs_fst_h n) as (n'' & n_n''_pi & n''_in_h2).
    admit.
    apply NatMapFacts.find_mapsto_iff in n'_n_pi.
    apply NatMapFacts.find_mapsto_iff in n_n''_pi.
    rewrite n_n''_pi in n'_n_pi.
    apply NatMapFacts.find_mapsto_iff in n_n''_pi.
    injection n'_n_pi as n'_eq.
    rewrite n'_eq in *.
    (* TODO replace with object equality *)
Admitted.

Lemma DisjointUnionPermuted : forall h1 h1_perm h2 h2_perm h h_perm pi,
  JFIDisjointUnion h1 h2 h ->
  HeapsPermuted h1 h1_perm pi ->
  HeapsPermuted h2 h2_perm pi ->
  HeapsPermuted h h_perm pi ->
  JFIDisjointUnion h1_perm h2_perm h_perm.
Proof.
  intros h1 h1_perm h2 h2_perm h h_perm pi.
  intros (union & disj) pi_h1 pi_h2 pi_h.
  split.
  now apply UnionPermuted with (h1 := h1) (h2 := h2) (h := h) (pi := pi).
  intros n' (n'_in_h1 & n'_in_h2).
  destruct pi_h1 as (_ & _ & locs_h1 & _).
  destruct pi_h2 as (_ & _ & locs_h2 & _).
  destruct (locs_h1 n' n'_in_h1) as (n1 & n1_n'_pi & n_in_h1).
  destruct (locs_h2 n' n'_in_h2) as (n2 & n2_n'_pi & n_in_h2).
  apply NatMapFacts.find_mapsto_iff in n1_n'_pi.
  apply NatMapFacts.find_mapsto_iff in n2_n'_pi.
  rewrite n2_n'_pi in n1_n'_pi.
  injection n1_n'_pi as n_eq.
  rewrite n_eq in n_in_h2.
  now apply (disj n1).
Qed.

Lemma PiMapsToSameType : forall h h_perm pi l type,
  HeapsPermuted h h_perm pi ->
  JFILocOfType l h type ->
  exists l_perm,
    PiMapsTo l l_perm pi /\ JFILocOfType l_perm h_perm type.
Proof.
  intros h h' pi l type pi_h l_of_type.
  destruct pi_h as (_ & locs_h & _ & objs_h).
  destruct l.
  now exists null.
  destruct (Classical_Prop.classic (exists o, Heap.find n h = Some o)) as [(o & n_o_h) | ].
  + destruct (locs_h n) as (n' & n_n'_pi & n'_in_h').
    ++ apply HeapFacts.elements_in_iff.
       exists o.
       now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
    ++ exists (JFLoc n').
       split; try easy.
       unfold ObjsPermuted in objs_h.
       apply HeapFacts.elements_in_iff in n'_in_h' as (o' & n'_o'_h').
       apply HeapFacts.elements_mapsto_iff in n'_o'_h'.
       apply HeapFacts.find_mapsto_iff in n_o_h.
       unfold JFILocOfType.
       apply HeapFacts.find_mapsto_iff in n'_o'_h'.
       rewrite n'_o'_h'.
       apply HeapFacts.find_mapsto_iff in n'_o'_h'.
       destruct o' as (o' & type').
       destruct o as (o & type_o).
       unfold JFILocOfType in l_of_type.
       apply HeapFacts.find_mapsto_iff in n_o_h.
       rewrite n_o_h in l_of_type.
       apply HeapFacts.find_mapsto_iff in n_o_h.
       rewrite <-l_of_type in *.
       now apply (objs_h n n' o type o' type').
  + exfalso; apply H.
    unfold JFILocOfType in l_of_type.
    destruct (Heap.find n h); try destruct l_of_type.
    now exists o.
Qed.

Lemma AddVarToPermutedEnvs : forall x l1 l2 env1 env2 pi,
  EnvsPermuted env1 env2 pi ->
  PiMapsTo l1 l2 pi ->
  EnvsPermuted (StrMap.add x l1 env1) (StrMap.add x l2 env2) pi.
Proof.
  intros x l1 l2 env1 env2 pi.
  intros (bijection & same_keys & var_mapsto) pi_l1.
  unfold EnvsPermuted in *.
  split; [ | split]; trivial.
  + intros y.
    split.
    ++ intros x_in_env.
       apply StrMapFacts.elements_in_iff in x_in_env as (l & x_l_env).
       apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff in x_l_env.
       apply StrMapFacts.elements_in_iff.
       destruct (Classical_Prop.classic (x = y)).
       +++ rewrite StrMapFacts.add_eq_o in x_l_env; trivial.
           exists l2.
           unfold PiMapsTo in pi_l1.
           apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff.
           rewrite StrMapFacts.add_eq_o; trivial.
       +++ rewrite StrMapFacts.add_neq_o in x_l_env; trivial.
           apply StrMapFacts.find_mapsto_iff, StrMapFacts.elements_mapsto_iff in x_l_env.
           assert (y_in_env : StrMap.In y env1).
             apply StrMapFacts.elements_in_iff.
             now exists l.
           apply (same_keys y) in y_in_env.
           apply StrMapFacts.elements_in_iff in y_in_env as (l' & x_l'_env).
           exists l'.
           apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff.
           apply StrMapFacts.elements_mapsto_iff, StrMapFacts.find_mapsto_iff in x_l'_env.
           now rewrite StrMapFacts.add_neq_o.
Admitted.