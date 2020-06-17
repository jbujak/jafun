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

Ltac induction2 l1 l2 length_eq head1 head2 tail1 tail2 :=
  set (_l1 := l1);
  set (_l2 := l2);
  (replace l1 with _l1 in *; try now unfold _l1);
  (replace l2 with _l2 in *; try now unfold _l2);
  (replace _l1 with l1 in length_eq; try now unfold _l1);
  (replace _l2 with l2 in length_eq; try now unfold _l2);
  (replace _l1 with (fst (split (combine l1 l2))) in *; try now rewrite combine_split);
  (replace _l2 with (snd (split (combine l1 l2))) in *; try now rewrite combine_split);
  clear _l1 _l2;
  induction (combine l1 l2) as [ | _a _l];
    [unfold split in *
    | simpl in *; destruct _a as (head1 & head2), (split _l) as (tail1 & tail2)
    ];
  unfold fst, snd in *.


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

Definition HeapLocsPermuted (f : HeapInjection) (h1 h2 : Heap) :=
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
  HeapLocsPermuted (fst pi) h1 h2 /\
  HeapLocsPermuted (snd pi) h2 h1 /\
  ObjsPermuted pi h1 h2.

Definition EnvsPermuted env1 env2 pi :=
  Bijection pi /\
  (forall x, StrMap.In x env1 <-> StrMap.In x env2) /\
  forall x l1 l2,
    StrMap.MapsTo x l1 env1 -> StrMap.MapsTo x l2 env2 ->
    PiMapsTo l1 l2 pi.

Fixpoint LocsPermuted ls ls' pi :=
  match (ls, ls') with
  | ([], []) => True
  | (l::ls, l'::ls') => PiMapsTo l l' pi /\ LocsPermuted ls ls' pi
  | _ => False
  end.

Definition ValPermuted v v' pi :=
  match (v, v') with
  | (JFSyn x, JFSyn y) => x = y
  | (JFVLoc l, JFVLoc l') => PiMapsTo l l' pi
  | _ => False
  end.

Fixpoint ValsPermuted vs vs' pi :=
  match (vs, vs') with
  | ([], []) => True
  | (v::vs, v'::vs') => ValPermuted v v' pi /\ ValsPermuted vs vs' pi
  | _ => False
  end.

Fixpoint ExprsPermuted e e' pi :=
  match (e, e') with
  | (JFNew mu cn vs, JFNew mu' cn' vs') =>
      mu = mu' /\ cn = cn' /\
      ValsPermuted vs vs' pi
  | (JFLet cn x e1 e2, JFLet cn' x' e1' e2') =>
      cn = cn' /\ x = x' /\
      ExprsPermuted e1 e1' pi /\ ExprsPermuted e2 e2' pi
  | (JFIf v1 v2 e1 e2, JFIf v1' v2' e1' e2') =>
      ExprsPermuted e1 e1' pi /\ ExprsPermuted e2 e2' pi /\
      ValPermuted v1 v1' pi /\ ValPermuted v2 v2' pi
  | (JFInvoke v1 m vs, JFInvoke v1' m' vs') =>
      ValPermuted v1 v1' pi /\ ValsPermuted vs vs' pi /\ m = m'
  | (JFAssign (v1, f) v2, JFAssign (v1', f') v2') =>
      f = f' /\ ValPermuted v1 v1' pi /\ ValPermuted v2 v2' pi
  | (JFVal1 v1, JFVal1 v1') =>
      ValPermuted v1 v1' pi
  | (JFVal2 (v1, f), JFVal2 (v1', f')) =>
      f = f' /\ ValPermuted v1 v1' pi
  | (JFThrow v1, JFThrow v1') =>
      ValPermuted v1 v1' pi
  | (JFTry e1 _ _ _ e2, JFTry e1' _ _ _ e2') =>
      ExprsPermuted e1 e1' pi /\ ExprsPermuted e2 e2' pi
  | _ => False
  end.

Definition CtxPermuted ctx ctx' pi :=
  match (ctx, ctx') with
  | (JFCtxLet cn x _ e2, JFCtxLet cn' x' _ e2') => cn = cn' /\ x = x' /\ ExprsPermuted e2 e2' pi
  | (JFCtxTry _ _ cn x e2, JFCtxTry _ _ cn' x' e2') => cn = cn' /\ x = x' /\ ExprsPermuted e2 e2' pi
  | _ => False
  end.

Fixpoint CtxsPermuted ctxs ctxs' pi :=
  match (ctxs, ctxs') with
  | ([], []) => True
  | (ctx::ctxs, ctx'::ctxs') => CtxPermuted ctx ctx' pi /\ CtxsPermuted ctxs ctxs' pi
  | _ => False
  end.

Definition FramesPermuted f f' pi :=
  match (f, f') with
  | (MkFrame ctxs e A, MkFrame ctxs' e' A') =>
      ExprsPermuted e e' pi /\ CtxsPermuted ctxs ctxs' pi /\ A = A'
  end.

Fixpoint StacksPermuted st st' pi :=
  match (st, st') with
  | ([], []) => True
  | (f::st, f'::st') => FramesPermuted f f' pi /\ StacksPermuted st st' pi
  | _ => False
  end.

Definition PermutationSubset (pi pi' : HeapPermutation) :=
  forall l1 l2, PiMapsTo l1 l2 pi -> PiMapsTo l1 l2 pi'.


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
  | [] => Some []
  | (field_name, loc)::flds =>
    match (TryPermuteLoc loc pi, TryPermuteObjFlds flds pi) with
    | (Some new_loc, Some new_flds) => Some ((field_name, new_loc)::new_flds)
    | _ => None
    end
  end.

Definition TryPermuteObj (obj : Obj) (pi : HeapPermutation) :=
  match obj with
  | (o, cn) => match TryPermuteObjFlds (JFXIdMap.elements o) pi with
    | Some new_flds => Some ((fold_left (fun o f => JFXIdMap.add (fst f) (snd f) o) new_flds (JFXIdMap.empty Loc)), cn)
    | None => None
    end
  end.

Fixpoint TryPermuteHeapElements (objs : list (nat * Obj)) (pi : HeapPermutation) :=
  match objs with
  | [] => Some []
  | (n, obj)::objs =>
    match (NatMap.find n (fst pi), TryPermuteObj obj pi, TryPermuteHeapElements objs pi) with
    | (Some new_n, Some new_obj, Some new_els) => Some ((new_n, new_obj)::new_els)
    | _ => None
    end
  end.

Definition TryPermuteHeap (h : Heap) (pi : HeapPermutation) :=
  match (TryPermuteHeapElements (Heap.elements h) pi) with
  | Some new_els => Some (fold_left (fun h o => Heap.add (fst o) (snd o) h) new_els (Heap.empty Obj))
  | None => None
  end.


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


Lemma PiMapsToEqIff : forall l1 l2 l1' l2' pi,
  Bijection pi ->
  PiMapsTo l1 l1' pi ->
  PiMapsTo l2 l2' pi ->
  (l1 = l2 <-> l1' = l2').
Proof.
  intros l1 l2 l1' l2' pi bijection pi_l1 pi_l2.
  split.
  + intros l_eq.
    unfold PiMapsTo in *.
    destruct l1, l2, l1', l2'; try easy.
    injection l_eq as n_eq.
    rewrite <-n_eq in pi_l2.
    assert (n1_eq := MapsToEq (fst pi) n n1 n2 pi_l1 pi_l2).
    now rewrite n1_eq.
  + intros l_eq.
    unfold PiMapsTo in *.
    destruct l1, l2, l1', l2'; try easy.
    apply bijection in pi_l1.
    apply bijection in pi_l2.
    injection l_eq as n1_eq.
    rewrite <-n1_eq in pi_l2.
    assert (n_eq := MapsToEq (snd pi) n1 n n0 pi_l1 pi_l2).
    now rewrite n_eq.
Qed.

Lemma ObjFldsAux : forall n (pi : HeapPermutation) field_name n' (flds' : list (string * Loc)),
NatMap.find (elt:=nat) n (fst pi) = Some n' ->
match
  match NatMap.find (elt:=nat) n (fst pi) with
  | Some n'0 => Some (JFLoc n'0)
  | None => None
  end
with
| Some new_loc => Some ((field_name, new_loc)::flds')
| None => None
end = Some ((field_name, (JFLoc n'))::flds').
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
  now exists [].
  destruct a as (field_name & loc).
  destruct IHflds as (obj' & flds_perm).
  + intros f n in_flds.
    apply (flds_in_p f n).
    now apply in_cons.
  + destruct loc.
    ++ exists ((field_name, null)::obj').
       simpl.
       now rewrite flds_perm.
    ++ destruct (flds_in_p field_name n) as (n' & n'_perm).
       now apply in_eq.
       simpl.
       exists ((field_name, (JFLoc n'))::obj').
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
  + rewrite obj_perm.
    now exists (fold_left (fun o f => JFXIdMap.add (fst f) (snd f) o) obj' (JFXIdMap.empty Loc), cn).
Qed.

Lemma HeapPermutationAux : forall n (pi : HeapPermutation) n' obj' (h' : list (nat * Obj)),
  NatMap.find (elt:=nat) n (fst pi) = Some n' ->
  match NatMap.find (elt:=nat) n (fst pi) with
  | Some new_n => Some ((new_n, obj') :: h')
  | None => None
  end = Some ((n', obj') :: h').
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
  now exists [].
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
    exists ((n', obj')::h').
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
    as (els' & els_perm).
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
  + rewrite els_perm.
    now exists (fold_left (fun h0 o => Heap.add (fst o) (snd o) h0) els'  (Heap.empty Obj)).
Qed.

Lemma PermutationDoesntAddNewHeapElements : forall n1 n2 els new_els pi,
  TryPermuteHeapElements els pi = Some new_els ->
  (~exists o1, In (n1, o1) els) ->
  Bijection pi ->
  NatMap.MapsTo n1 n2 (fst pi) ->
  (~exists o2, In (n2, o2) new_els).
Proof.
  intros n1 n2 els.
  induction els; intros new_els pi pi_els n1_not_in_els bijection pi_n.
  + intros  (o2 & n2_o2_new).
    destruct new_els; try discriminate pi_els.
    now apply in_nil in n2_o2_new.
  + destruct new_els as [ | new_a new_els].
      simpl in pi_els.
      destruct a.
      destruct (NatMap.find n (fst pi)),
               (TryPermuteObj o pi),
               (TryPermuteHeapElements els pi); try discriminate pi_els.
    assert (n2_n1_pi := (proj1 (bijection n1 n2)) pi_n).
    unfold Bijection in bijection.
    destruct a as (n & o), new_a as (new_n & new_o).
    destruct (Classical_Prop.classic (n2 = new_n)).
    ++ rewrite <-H in *.
       simpl in pi_els.
       assert (NatMap.find n (fst pi) = Some n2).
         destruct (NatMap.find n (fst pi)),
                  (TryPermuteObj o pi),
                   (TryPermuteHeapElements els pi); try discriminate pi_els.
         injection pi_els as n_eq _ _.
         now rewrite n_eq.
       apply NatMapFacts.find_mapsto_iff in H0.
       destruct (PiMapsToEqIff (JFLoc n1) (JFLoc n) (JFLoc n2) (JFLoc n2) pi) as (_ & n_eq); try easy.
       injection n_eq; trivial; clear n_eq; intros n_eq.
       exfalso.
       apply n1_not_in_els.
       rewrite n_eq.
       exists o.
       now apply in_eq.
    ++ intros (o2 & n2_o2).
       apply in_inv in n2_o2.
       destruct n2_o2.
         apply H.
         now injection H0.
       unfold not in IHels.
       apply IHels with (new_els := new_els) (pi := pi); try easy.
       +++ simpl in pi_els.
           destruct (NatMap.find n (fst pi)),
                    (TryPermuteObj o pi),
                    (TryPermuteHeapElements els pi); try discriminate pi_els.
           injection pi_els as _ _ l_eq.
           now rewrite l_eq.
       +++ intros (o1 & n1_o1).
           apply n1_not_in_els.
           exists o1.
           now apply in_cons.
       +++ now exists o2.
Qed.

Lemma EqFoldFromEqHeaps : forall els h1 h2 h',
  HeapEq h1 h2 ->
  HeapEq (fold_left (fun h o => Heap.add (fst o) (snd o) h) els h1) h' ->
  HeapEq (fold_left (fun h o => Heap.add (fst o) (snd o) h) els h2) h'.
Proof.
  intros els.
  induction els; intros h1 h2 h' h_eq fold_eq.
  + simpl in *.
    apply HeapEqSym in h_eq.
    now apply HeapEqTrans with (h2 := h1).
  + simpl in *.
    apply IHels with (h1 := (Heap.add (fst a) (snd a) h1)); trivial.
    intros n.
    destruct (Classical_Prop.classic (n = fst a)).
    ++ now rewrite 2!HeapFacts.add_eq_o.
    ++ rewrite 2!HeapFacts.add_neq_o; try easy; try now apply neq_symmetry.
Qed.

Lemma ChangeHeapAddOrder : forall n1 n2 o1 o2 h,
  n1 <> n2 ->
  HeapEq (Heap.add n1 o1 (Heap.add n2 o2 h)) (Heap.add n2 o2 (Heap.add n1 o1 h)).
Proof.
  intros n1 n2 o1 o2 h n_neq.
  intros n.
  destruct (Classical_Prop.classic (n1 = n)) as [n1_eq | n1_neq], (Classical_Prop.classic (n2 = n)) as [n2_eq | n2_neq].
  ++ now rewrite <-n2_eq in n1_eq.
  ++ now rewrite n1_eq, HeapFacts.add_eq_o, HeapFacts.add_neq_o, HeapFacts.add_eq_o.
  ++ now rewrite HeapFacts.add_neq_o, 2!HeapFacts.add_eq_o.
  ++ now rewrite 4!HeapFacts.add_neq_o.
Qed.

Lemma HeapMapsToLastAddedObj : forall els n obj (h h' : Heap),
  (~exists o, In (n, o) els) ->
  HeapEq (fold_left (fun h o  => Heap.add (fst o) (snd o) h) els (Heap.add n obj h)) h' ->
  Heap.MapsTo n obj h'.
Proof.
  intros els.
  induction els; intros n obj h h' n_not_in_els h'_eq.
  + simpl in h'_eq.
    rewrite <-h'_eq.
    now apply HeapFacts.find_mapsto_iff, HeapFacts.add_eq_o.
  + simpl in h'_eq.
    apply IHels with (h := Heap.add (fst a) (snd a) h).
    ++ intros (o & n_in_els).
       apply n_not_in_els.
       exists o.
       now apply in_cons.
    ++ apply EqFoldFromEqHeaps with (h1 := Heap.add (fst a) (snd a) (Heap.add n obj h)); trivial.
       apply ChangeHeapAddOrder.
       destruct a.
       simpl.
       intros k_eq_n.
       apply n_not_in_els.
       exists o.
       rewrite k_eq_n.
       now apply in_eq.
Qed.

Lemma InFoldIff : forall l n (h : Heap),
  Heap.In n (fold_left (fun h o => Heap.add (fst o) (snd o) h) l h) <->
  ((exists o, In (n, o) l) \/ Heap.In n h).
Proof.
  intros l.
  induction l; intros n h.
  + simpl.
    split.
    ++ intros n_h.
       now apply or_intror.
    ++ now destruct 1; try now (destruct H; destruct H).
  + simpl.
    split.
    ++ intros n_h.
       apply IHl in n_h.
       destruct n_h.
       +++ destruct H as (o & n_o_l).
           apply or_introl.
           exists o.
           now apply or_intror.
       +++ apply HeapFacts.elements_in_iff in H.
           destruct H as (o & n_o_h).
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n_o_h.
           destruct (Classical_Prop.classic (fst a = n)).
           - rewrite HeapFacts.add_eq_o in n_o_h; try easy.
             apply or_introl.
             exists o.
             apply or_introl.
             injection n_o_h as o_eq.
             destruct a.
             simpl in *.
             now rewrite o_eq, H.
           - rewrite HeapFacts.add_neq_o in n_o_h; try easy.
             apply or_intror, HeapFacts.elements_in_iff.
             exists o.
             now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
    ++ intros H.
       apply IHl.
       destruct H;  [ destruct H as (o & H); destruct H |].
       +++ apply or_intror.
           rewrite H.
           simpl.
           apply HeapFacts.elements_in_iff.
           exists o.
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
           now rewrite HeapFacts.add_eq_o.
       +++ apply or_introl.
           now exists o.
       +++ apply or_intror.
           apply HeapFacts.elements_in_iff.
           destruct (Classical_Prop.classic (fst a = n)).
           - exists (snd a).
             apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
             now rewrite HeapFacts.add_eq_o.
           - apply HeapFacts.elements_in_iff in H.
             destruct H as (o & n_o_h).
             exists o.
             apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n_o_h.
             apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
             now rewrite HeapFacts.add_neq_o.
Qed.

Lemma FoldStepDoesntRemoveElements : forall l n (h : Heap) n' o',
  Heap.In n (fold_left (fun h o => Heap.add (fst o) (snd o) h) l h) ->
  Heap.In n (fold_left (fun h o => Heap.add (fst o) (snd o) h) l (Heap.add n' o' h)).
Proof.
  intros l.
  induction l; intros n h n' o' in_h.
  + simpl in *.
    apply HeapFacts.elements_in_iff in in_h.
    destruct in_h as (o & n_e_h).
    apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n_e_h.
    apply HeapFacts.elements_in_iff.
    destruct (Classical_Prop.classic (n' = n)).
    ++ exists o'.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
       now rewrite HeapFacts.add_eq_o.
    ++ exists o.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
       now rewrite HeapFacts.add_neq_o.
  + destruct a as (nn & oo).
    simpl in *.
    apply IHl with (n' := n') (o' := o') in in_h.
    apply InFoldIff in in_h.
    apply InFoldIff.
    destruct in_h as [(o & n_o_l) | n_in_h].
    ++ apply or_introl.
       now exists o.
    ++ apply or_intror.
       apply HeapFacts.elements_in_iff in n_in_h as (o & n_o_h).
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n_o_h.
       apply HeapFacts.elements_in_iff.
       destruct (Classical_Prop.classic (n' = n)) as [n'_eq | n'_neq],
                (Classical_Prop.classic (nn = n)) as [nn_eq | nn_neq].
       +++ exists oo.
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
           now rewrite HeapFacts.add_eq_o.
       +++ exists o'.
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
           rewrite HeapFacts.add_neq_o, HeapFacts.add_eq_o; try easy.
       +++ exists oo.
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
           rewrite HeapFacts.add_eq_o; try easy.
       +++ exists o.
           rewrite !HeapFacts.add_neq_o in n_o_h; try easy.
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
           now rewrite !HeapFacts.add_neq_o.
Qed.

Lemma FoldDoesntRemoveElements : forall l n (h : Heap),
  Heap.In n h ->
  Heap.In n (fold_left (fun h o => Heap.add (fst o) (snd o) h) l h).
Proof.
  intros l.
  induction l; intros n h n_h; try easy.
  simpl.
  apply FoldStepDoesntRemoveElements.
  now apply IHl.
Qed.

Lemma RemoveFromFold : forall els n n' o' o2 cn2 (h : Heap),
  n <> n' ->
  Heap.find n (fold_left (fun h o => Heap.add (fst o) (snd o) h)
                els (Heap.add n' o' h)) = Some (o2, cn2) ->
  Heap.find n (fold_left (fun h o => Heap.add (fst o) (snd o) h)
                els h) = Some (o2, cn2).
Proof.
  intros els.
  induction els; intros n n' o' o2 cn2 h n_neq find_n.
  + simpl in *.
    apply neq_symmetry in n_neq.
    now rewrite HeapFacts.add_neq_o in find_n.
  + simpl in *.
    destruct (Classical_Prop.classic (n' = fst a)).
    ++ rewrite <-H in *.
       set (h' := (fold_left
              (fun h o =>
               Heap.add (fst o) (snd o) h) els
              (Heap.add n' (snd a) (Heap.add n' o' h)))).
       assert (heap_eq : HeapEq
         (fold_left
            (fun (h : Heap.t Obj) (o : Heap.key * Obj) =>
             Heap.add (fst o) (snd o) h) els
            (Heap.add n' (snd a) (Heap.add n' o' h))) h').
         fold h'.
         now apply EqImpliesHeapEq.
       apply EqFoldFromEqHeaps with (h2 := (Heap.add n' (snd a) h)) in heap_eq.
       +++ unfold h' in heap_eq.
           unfold HeapEq in heap_eq.
           now rewrite heap_eq.
       +++ intros nn.
           destruct (Classical_Prop.classic (n' = nn)).
           - now rewrite !HeapFacts.add_eq_o.
           - now rewrite !HeapFacts.add_neq_o.
    ++ apply IHels with (n' := n') (o' := o'); try easy.
       set (h' := (fold_left
              (fun h o =>
               Heap.add (fst o) (snd o) h) els
              (Heap.add (fst a) (snd a) (Heap.add n' o' h)))).
       assert (heap_eq : HeapEq
         (fold_left
            (fun (h : Heap.t Obj) (o : Heap.key * Obj) =>
             Heap.add (fst o) (snd o) h) els
            (Heap.add (fst a) (snd a) (Heap.add n' o' h))) h').
         fold h'.
         now apply EqImpliesHeapEq.
       apply EqFoldFromEqHeaps with (h2 := (Heap.add n' o' (Heap.add (fst a) (snd a) h))) in heap_eq.
       +++ unfold h' in heap_eq.
           unfold HeapEq in heap_eq.
           now rewrite heap_eq.
       +++ intros nn.
           destruct (Classical_Prop.classic (fst a = nn)).
           - rewrite HeapFacts.add_eq_o, HeapFacts.add_neq_o, HeapFacts.add_eq_o; try easy.
             intros n'_eq.
             apply H.
             now rewrite H0.
           - rewrite HeapFacts.add_neq_o; try easy.
             destruct (Classical_Prop.classic (n' = nn)).
             now rewrite !HeapFacts.add_eq_o.
             now rewrite !HeapFacts.add_neq_o.
Qed.

Lemma SuccessfulPermutationIsLocsPermutation : forall h pi n1 obj h',
  match TryPermuteHeapElements (Heap.elements h) pi with
  | Some new_els => Some (fold_left (fun h o => Heap.add (fst o) (snd o) h) new_els (Heap.empty Obj))
  | None => None
  end = Some h' ->
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
       apply FoldDoesntRemoveElements.
       apply HeapFacts.elements_in_iff.
       exists p.
       apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
       now rewrite HeapFacts.add_eq_o.
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
    set (rest_h' := (fold_left (fun h o => Heap.add (fst o) (snd o) h) l0 (Heap.empty Obj))).
    destruct (IHl rest_h') as (n2 & n1_n2_pi & n2_in_rest); trivial.
    exists n2.
    split; trivial.
    unfold rest_h' in n2_in_rest.
    now apply FoldStepDoesntRemoveElements.
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
           rewrite n_eq in pi_h.
           destruct (TryPermuteObj obj_n (pi1, pi2)); try discriminate pi_h.
           destruct (TryPermuteHeapElements l (pi1, pi2)); try discriminate pi_h.
           injection pi_h as h'_eq.
           rewrite <-h'_eq in n2_obj_h'.
           assert (next_in_h : forall a, In a l -> Heap.In (elt:=Obj) (fst a) h).
           intros a a_in_l.
           apply in_cons with (a := (n, obj_n)) in a_in_l.
           apply (in_h a a_in_l).
           set (rest_h' := (fold_left (fun h o => Heap.add (fst o) (snd o) h)
                  l0 (Heap.empty Obj))).
           apply (IHl next_in_h rest_h' n2 obj); trivial.
           apply In_InA with (eqA := Heap.eq_key_elt (elt:=Obj)) in n2_obj_h'; [ | apply HeapEqKeyEltEquivalence].
           apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff in n2_obj_h'.
           fold Obj in n2_obj_h'.
           destruct obj.
           apply RemoveFromFold in n2_obj_h'.
           - apply HeapFacts.find_mapsto_iff, HeapFacts.elements_mapsto_iff in n2_obj_h'.
             apply InA_alt in n2_obj_h'.
             destruct n2_obj_h' as (y & y_eq & n2_obj_h').
             destruct y, p0.
             unfold Heap.eq_key_elt, Heap.Raw.Proofs.PX.eqke in y_eq.
             simpl in y_eq.
             now rewrite <-(proj1 y_eq), <-(proj2 y_eq) in n2_obj_h'.
           - intros n2_eq.
             apply H.
             now rewrite <-n2_eq in n_n'_pi1.
       +++ destruct (NatMap.find n pi1); try discriminate pi_h.
           exfalso.
           apply H0.
           now exists n0.
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

Lemma SuccessfulPermutationIsObjPermutation_elements : forall o1 o2 cn1 cn2 pi,
  TryPermuteObj (o1, cn1) pi = Some (o2, cn2) ->
  forall f : JFXIdMap.key,
    (forall v1 : Loc, InA (JFXIdMap.eq_key_elt (elt:=Loc)) (f, v1) (JFXIdMap.elements o1) -> exists v2 : Loc, JFXIdMap.MapsTo f v2 o2) /\
    (forall v2 : Loc, JFXIdMap.MapsTo f v2 o2 -> exists v1 : Loc, InA (JFXIdMap.eq_key_elt (elt:=Loc)) (f, v1) (JFXIdMap.elements o1) ) /\
    (forall v1 v2 : Loc, InA (JFXIdMap.eq_key_elt (elt:=Loc)) (f, v1) (JFXIdMap.elements o1)  -> JFXIdMap.MapsTo f v2 o2 -> PiMapsTo v1 v2 pi).
Proof.
  intros o1.
  unfold TryPermuteObj.
  induction (JFXIdMap.elements o1) as [ | fld flds]; intros o2 cn1 cn2 pi pi_o1 f.
  + simpl in *.
    injection pi_o1 as o2_eq cn_eq.
    split; [ | split].
    ++ intros v1 f_v1.
       inversion f_v1.
    ++ intros v2 f_v2.
       exfalso.
       rewrite <-o2_eq in f_v2.
       now apply JFXIdMapFacts.empty_mapsto_iff in f_v2.
    ++ intros v1 v2 f_v1 f_v2.
       exfalso.
       rewrite <-o2_eq in f_v2.
       now apply JFXIdMapFacts.empty_mapsto_iff in f_v2.
  + simpl in *. clear o1.
    destruct fld as (f1 & l1).
    assert (exists l1', TryPermuteLoc l1 pi = Some l1').
      destruct (TryPermuteLoc l1 pi); try discriminate pi_o1.
      now exists l.
    destruct H as (l1' & pi_l1).
    rewrite pi_l1 in pi_o1.
    assert (exists flds', TryPermuteObjFlds flds pi = Some flds').
      destruct (TryPermuteObjFlds flds pi); try discriminate pi_o1.
      now exists l.
    destruct H as (flds' & pi_flds).
    rewrite pi_flds in pi_o1.
    injection pi_o1 as o_eq cn_eq.
    set (o' := fold_left (fun o f => JFXIdMap.add (fst f) (snd f) o) flds' (JFXIdMap.empty Loc)).
    assert (H := IHflds o' cn1 cn1 pi).
    rewrite pi_flds in H.
    fold o' in H.
    assert (IH := H eq_refl f).
    clear H IHflds.
    destruct IH as (IH1 & IH2 & IH3).
    split; [ | split].
    ++ intros v1 f_v1.
       destruct (Classical_Prop.classic (f1 = f)).
       +++ admit.
       +++ inversion f_v1.
             exfalso.
             apply H.
             now unfold JFXIdMap.eq_key_elt, JFXIdMap.Raw.PX.eqke, fst, snd in H1.
           apply IH1 in H1 as (v2 & f_v2).
           exists v2.
           admit.
    ++ intros v2 f_v2.
       destruct (Classical_Prop.classic (f1 = f)).
       +++ exists l1.
           now apply InA_cons_hd.
       +++ assert (f_v2' : JFXIdMap.MapsTo f v2 o'). admit.
           apply IH2 in f_v2' as (v1 & f_v1).
           exists v1.
           now apply InA_cons_tl.
    ++ intros v1 v2 f_v1 f_v2.
       destruct (Classical_Prop.classic (f1 = f)).
       +++ admit.
       +++ assert (f_v2' : JFXIdMap.MapsTo f v2 o'). admit.
           inversion f_v1.
             exfalso.
             apply H.
             now unfold JFXIdMap.eq_key_elt, JFXIdMap.Raw.PX.eqke, fst, snd in H1.
           now apply IH3.
Admitted.

Lemma SuccessfulPermutationIsObjPermutation : forall o1 o2 cn1 cn2 pi,
  TryPermuteObj (o1, cn1) pi = Some (o2, cn2) ->
  forall f : JFXIdMap.key,
    (forall v1 : Loc, JFXIdMap.MapsTo f v1 o1 -> exists v2 : Loc, JFXIdMap.MapsTo f v2 o2) /\
    (forall v2 : Loc, JFXIdMap.MapsTo f v2 o2 -> exists v1 : Loc, JFXIdMap.MapsTo f v1 o1) /\
    (forall v1 v2 : Loc, JFXIdMap.MapsTo f v1 o1 -> JFXIdMap.MapsTo f v2 o2 -> PiMapsTo v1 v2 pi).
Proof.
  apply SuccessfulPermutationIsObjPermutation_elements.
Qed.

Lemma SuccessfulPermutationIsHeapElementsPermutation : forall o1 cn1 n1 objs objs' n2 o2 cn2 pi,
  TryPermuteHeapElements ((n1, (o1, cn1)) :: objs) pi = Some ((n2, (o2, cn2)) :: objs') ->
  NatMap.MapsTo n1 n2 (fst pi) ->
  (cn1 = cn2 /\ forall f,
      (forall v1, JFXIdMap.MapsTo f v1 o1 -> exists v2, JFXIdMap.MapsTo f v2 o2) /\
      (forall v2, JFXIdMap.MapsTo f v2 o2 -> exists v1, JFXIdMap.MapsTo f v1 o1) /\
      (forall v1 v2,
        JFXIdMap.MapsTo f v1 o1 ->
        JFXIdMap.MapsTo f v2 o2 ->
        PiMapsTo v1 v2 pi)).
Proof.
  intros o1 cn1 n1 objs objs' n2 o2 cn2 pi pi_h pi_n.
  unfold TryPermuteHeapElements in pi_h.
  fold TryPermuteHeapElements in pi_h.
  apply NatMapFacts.find_mapsto_iff in pi_n.
  rewrite pi_n in pi_h.
  split.
  +  simpl in pi_h.
     destruct (TryPermuteObjFlds (JFXIdMap.elements (elt:=Loc) o1) pi),
              (TryPermuteHeapElements objs pi); try discriminate pi_h.
     now injection pi_h.
  + apply SuccessfulPermutationIsObjPermutation with (cn1 := cn1) (cn2 := cn2).
    destruct (TryPermuteObj (o1, cn1) pi), (TryPermuteHeapElements objs pi) in pi_h;
    try discriminate pi_h.
    injection pi_h.
    intros _ p_eq.
    now rewrite p_eq.
Qed.

Lemma HeadOfPermutedElementsIsPermuted : forall n1 n2 o1 o2 cn1 cn2 pi els h',
  Bijection pi ->
  match TryPermuteHeapElements ((n1, (o1, cn1)) :: els) pi with
  | Some new_els =>
      Some (fold_left (fun h o => Heap.add (fst o) (snd o) h) new_els (Heap.empty Obj))
  | None => None
  end = Some h' ->
 (~exists o1', In (n1, o1') els) ->
  NatMap.MapsTo n1 n2 (fst pi) ->
  Heap.MapsTo n2 (o2, cn2) h' ->
  exists els', TryPermuteHeapElements ((n1, (o1, cn1)) :: els) pi = Some ((n2, (o2, cn2)) :: els').
Proof.
  intros n1 n2 o1 o2 cn1 cn2 pi els h'.
  intros bijection pi_elements n1_not_in_els pi_n n2_o2_h'.
  unfold TryPermuteHeapElements in *.
  fold TryPermuteHeapElements in *.
  apply NatMapFacts.find_mapsto_iff in pi_n.
  rewrite pi_n in *.

  destruct (TryPermuteObj (o1, cn1) pi) as [new_obj | ]; try discriminate pi_elements.
  assert (exists els', TryPermuteHeapElements els pi = Some els').
    destruct (TryPermuteHeapElements els pi); try discriminate pi_elements.
    now exists l.
  destruct H as (els' & pi_els).
  rewrite pi_els in *.
  exists els'.
  injection pi_elements as pi_elements.
  apply NatMapFacts.find_mapsto_iff in pi_n.
  apply EqImpliesHeapEq in pi_elements.
  apply HeapMapsToLastAddedObj in pi_elements as n2_new_h';
    [ | now apply PermutationDoesntAddNewHeapElements with (n1 := n1) (els := els) (pi := pi)].
  apply HeapFacts.find_mapsto_iff in n2_new_h'.
  apply HeapFacts.find_mapsto_iff in n2_o2_h'.
  fold RawObj Obj in n2_o2_h'.
  rewrite n2_new_h' in n2_o2_h'.
  injection n2_o2_h' as obj_eq.
  now rewrite obj_eq.
Qed.

Lemma AppNoDupA : forall l1 l2,
  NoDupA (Heap.eq_key (elt:=Obj)) (l1 ++ l2) ->
  NoDupA (Heap.eq_key (elt:=Obj))  l2.
Proof.
  intros l1.
  induction l1; trivial.
  intros l2 no_dup.
  apply IHl1.
  now inversion no_dup.
Qed.

Lemma HeapElementsUnique : forall (h : Heap) els1 els2,
  (Heap.elements h) = els1 ++ els2 ->
  match els2 with
  | [] => True
  | ((n, _) :: els) => ~exists o, In (n, o) els
  end.
Proof.
  intros h els1 els2.
  assert (no_dup := Heap.elements_3w h).
  intros h_eq.
  destruct els2; trivial.
  destruct p as (n & o).
  rewrite h_eq in no_dup.
  apply AppNoDupA in no_dup.
  intros (o' & n_in_els2).
  inversion no_dup.
  apply H1.
  apply InA_eqA with (x := (n, o')); try easy.
  now apply HeapEqKeyEquivalence.
  apply In_InA; trivial.
  now apply HeapEqKeyEquivalence.
Qed.

Lemma HeapElementsUniqueStep : forall (a : (Heap.key * Obj)) l,
  (forall els1 els2,
    a::l = els1 ++ els2 ->
    match els2 with
    | [] => True
    | ((n, _) :: els) => ~exists o, In (n, o) els
    end) ->
  (forall els1 els2,
    l = els1 ++ els2 ->
    match els2 with
    | [] => True
    | ((n, _) :: els) => ~exists o, In (n, o) els
    end).
Proof.
  intros a l elements_unique.
  intros els1 els2 l_eq.
  apply elements_unique with (els1 := a::els1).
  rewrite <-app_comm_cons.
  now rewrite l_eq.
Qed.

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
    now apply HeapEqKeyEltEquivalence.
  assert (els_unique := HeapElementsUnique h).
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
       clear H.
       assert (n1_obj_h := in_els_mapsto n1 obj (in_eq (n1, obj) l)).
       assert (obj_eq : obj = (o1, cn1)).
         apply HeapFacts.find_mapsto_iff in n1_o1_h.
         apply HeapFacts.find_mapsto_iff in n1_obj_h.
         unfold Obj in n1_obj_h.
         rewrite n1_obj_h in n1_o1_h.
         now injection n1_o1_h.
       rewrite obj_eq in pi_h.
       destruct (HeadOfPermutedElementsIsPermuted n1 n2 o1 o2 cn1 cn2 pi l h') as (l' & pi_elements); trivial.
         now apply els_unique with (els1 := []) (els2 := (n1, obj)::l).
       now apply SuccessfulPermutationIsHeapElementsPermutation with (n1 := n1) (n2 := n2) (objs := l) (objs' := l').
    ++ simpl in pi_h.
       assert (exists n', NatMap.find n (fst pi) = Some n').
       destruct (NatMap.find n (fst pi)); try discriminate pi_h.
       now exists n0.
       destruct H0 as (n' & n_pi_n').
       rewrite n_pi_n' in pi_h.
       destruct (TryPermuteObj obj pi); try discriminate pi_h.
       assert (exists h', TryPermuteHeapElements l pi = Some h').
       destruct (TryPermuteHeapElements l pi); try discriminate pi_h.
       now exists l0.
       destruct H0 as (rest_els_h' & pi_rest_els_h').
       rewrite pi_rest_els_h' in *.
       injection pi_h as h'_eq.
       unfold ObjsPermuted in IHl.
       rewrite <-h'_eq in n2_o2_h'.
       assert (next_in_els : forall n obj, In (n, obj) l -> Heap.MapsTo n obj h).
         intros n0 obj0 n0_in_l.
         now apply in_els_mapsto, in_cons.
       assert (next_els_unique := HeapElementsUniqueStep (n, obj) l els_unique).
       set (rest_h' := fold_left (fun h o => Heap.add (fst o) (snd o) h) rest_els_h' (Heap.empty Obj)).
       assert (pi_rest_h' : match TryPermuteHeapElements l pi with 
           | Some new_els => Some   (fold_left (fun h o => Heap.add (fst o) (snd o) h) new_els (Heap.empty Obj))
           | None => None
           end = Some rest_h').
         now rewrite pi_rest_els_h'.
       apply (IHl next_in_els next_els_unique rest_h' pi bijection pi_rest_h' n1 n2 o1 cn1 o2 cn2); trivial.
       apply HeapFacts.find_mapsto_iff in n2_o2_h'.
       apply HeapFacts.find_mapsto_iff.
       unfold rest_h'.
       apply RemoveFromFold with (n' := n') (o' := p); trivial.
       apply NatMapFacts.find_mapsto_iff in n_pi_n'.
       intros n'_eq_n2.
       rewrite <-n'_eq_n2 in n_pi_n'.
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
  + unfold HeapLocsPermuted.
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
  + unfold HeapLocsPermuted.
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

Lemma ExistsPermutedVal : forall v pi,
  exists v', ValPermuted v v' pi.
Proof.
  intros v pi.
  destruct v.
  + destruct l.
    ++ now exists JFnull.
    ++ admit.
  + now exists (JFSyn x).
Admitted.

Lemma ExistsPermutedVals : forall vs pi,
  exists vs', ValsPermuted vs vs' pi.
Proof.
  intros vs pi.
  induction vs.
  + now exists [].
  + destruct IHvs as (vs' & pi_vs).
    destruct (ExistsPermutedVal a pi) as (a' & pi_a).
    now exists (a'::vs').
Qed.

Lemma ExistsPermutedExpr : forall e pi,
  exists e', ExprsPermuted e e' pi.
Proof.
  intros e pi.
  induction e.
  + destruct (ExistsPermutedVals vs pi) as (vs' & pi_vs).
    now exists (JFNew mu cn vs').
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
  unfold HeapLocsPermuted in *.
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
    unfold HeapLocsPermuted in locs_fst_h.
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

Lemma PermutationSubsetTrans : forall pi1 pi2 pi3,
  PermutationSubset pi1 pi2 ->
  PermutationSubset pi2 pi3 ->
  PermutationSubset pi1 pi3.
Proof.
  intros pi1 pi2 pi3 pi1_pi2 pi2_pi3 x l pi1_x_l.
  now apply pi2_pi3, pi1_pi2.
Qed.

Lemma ExistsPermutedResult : forall res A stn_ext pi',
  StacksPermuted [ [] [[JFVal1 (JFVLoc res) ]]_ A] stn_ext pi' ->
  exists res', PiMapsTo res res' pi' /\
       stn_ext = [ [] [[JFVal1 (JFVLoc res') ]]_ A].
Proof.
  intros res A stn_ext pi'.
  intros pi_st.
  unfold StacksPermuted in pi_st.
  destruct stn_ext; try destruct pi_st.
  destruct stn_ext; try destruct H0.
  unfold FramesPermuted in H.
  destruct f.
  destruct H as (pi_val & pi_ctxs & A_eq).
  simpl in pi_ctxs.
  destruct Ctx; try destruct pi_ctxs.
  unfold ExprsPermuted in pi_val.
  destruct E; try destruct pi_val.
  destruct v; try destruct pi_val.
  exists l.
  now rewrite A_eq.
Qed.

Lemma PermutationPreservesClassName : forall h0 h0' h0_perm h0_ext n n_perm C pi,
  PiMapsTo (JFLoc n) (JFLoc n_perm) pi ->
  HeapsPermuted h0 h0_perm pi ->
  JFIDisjointUnion h0_perm h0' h0_ext ->
  getClassName h0 n = Some C ->
  getClassName h0_ext n_perm = Some C.
Proof.
  intros h0 h0' h0_perm h0_ext n n_perm C pi.
  intros pi_n pi_h union class_name.
  unfold getClassName in *.
  assert (exists o, Heap.find n h0 = Some o).
    destruct (Heap.find n h0); try discriminate class_name.
    now exists o.
  destruct H as (o & n_o_h).
  rewrite n_o_h in class_name.
  destruct pi_h as (_ & locs_fst & _ & objs).
  unfold PiMapsTo in pi_n.
  assert (n_in_h : Heap.In n h0).
    apply HeapFacts.elements_in_iff.
    exists o.
    now apply HeapFacts.elements_mapsto_iff, HeapFacts.find_mapsto_iff.
  destruct (locs_fst n n_in_h) as (n_perm' & n_nperm'_pi & n_perm'_in_h_perm).
  rewrite <-(MapsToEq (fst pi) n n_perm n_perm') in *; trivial.
  apply HeapFacts.elements_in_iff in n_perm'_in_h_perm.
  destruct n_perm'_in_h_perm as (o' & n'_o'_h').
  apply HeapFacts.elements_mapsto_iff in n'_o'_h'.

  apply HeapFacts.find_mapsto_iff in n_o_h.
  destruct o as (o & cn), o' as (o' & cn').
  injection class_name as C_eq.
  destruct (objs n n_perm o cn o' cn') as (cn_eq & _); trivial.

  apply HeapFacts.find_mapsto_iff in n_o_h.
  assert (subheap : JFISubheap h0_perm h0_ext). apply union.
  assert (n'_o'_h_ext := subheap n_perm (o', cn') n'_o'_h').
  apply HeapFacts.find_mapsto_iff in n'_o'_h_ext.
  now rewrite n'_o'_h_ext, <-cn_eq, C_eq.
Qed.

Lemma PermutationPreservesSubstExpr : forall e e' pi f l l' e_body e_body',
  ExprsPermuted e_body e_body' pi ->
  ExprsPermuted e e' pi ->
  PiMapsTo l l' pi ->
  substExpr f l e_body = e ->
  substExpr f l' e_body' = e'.
Proof.
Admitted.

Lemma SubstPermutedExpr : forall f l l' e e' pi,
  ExprsPermuted e e' pi ->
  PiMapsTo l l' pi ->
  ExprsPermuted (substExpr f l e) (substExpr f l' e') pi.
Proof.
Admitted.

Lemma PermutationPreservesSubstList : forall fs vs vs',
  (forall f, In f fs -> f <> JFThis) ->
  length fs = length vs ->
  length vs = length vs' -> forall e_body e_body' n n' e pi,
  ValsPermuted vs vs' pi ->
  ExprsPermuted e_body e_body' pi ->
  PiMapsTo (JFLoc n) (JFLoc n') pi ->
  substList fs vs  (substExpr JFThis (JFLoc n) e_body) = Some e ->
  exists e',
  ExprsPermuted e e' pi /\
  substList fs vs' (substExpr JFThis (JFLoc n') e_body') = Some e'.
Proof.
  intros fs vs vs' fs_not_this fs_length_eq vs_length_eq.
  set (_fs := fs).
  replace fs with _fs in fs_not_this; try now unfold _fs.
  set (_vs := vs).
  set (_vs' := vs').
  replace _fs  with (fst (split (combine fs (combine vs vs')))) in *.
  replace _vs  with (fst (split (snd (split (combine fs (combine vs vs')))))).
  replace _vs' with (snd (split (snd (split (combine fs (combine vs vs')))))).
  clear fs_length_eq vs_length_eq _fs _vs _vs'.
  induction (combine fs (combine vs vs')); clear fs vs vs'.
  + intros e_body e_body' n n' e pi.
    intros pi_vs pi_body pi_n subst.
    simpl in *.
         destruct (ExistsPermutedExpr e pi) as (e' & pi_e).
    exists e'.
    split; trivial.
    unfold substList in *.
    injection subst as subst.
    apply PermutationPreservesSubstExpr
      with (e' := e') (e_body' := e_body') (l' := (JFLoc n')) (pi := pi) in subst; trivial.
    now rewrite subst.
  + intros e_body e_body' n n' e pi.
    intros pi_vs pi_body pi_n subst.
    destruct a as (f & (v & v')).
    simpl in *.
    destruct (split l) as (fs & vs_vs').
    unfold fst, snd in *.
    simpl in *.
    unfold fst, snd in *.
    destruct (split vs_vs') as (vs & vs').
    destruct v; try discriminate subst.
    destruct v'; try destruct pi_vs.
    assert (next_f_not_this : (forall f : JFRef, In f fs -> f <> JFThis)).
      intros f0 f0_in_fs. apply (fs_not_this f0). now apply or_intror.
    rewrite SubstExprComm in subst; [ | now apply fs_not_this, or_introl].
    destruct (IHl next_f_not_this (substExpr f l0 e_body) (substExpr f l1 e_body') n n' e pi)
      as (e' & pi_e & subst'); trivial.
    now apply SubstPermutedExpr.
    rewrite SubstExprComm in subst'; [ | now apply neq_symmetry, fs_not_this, or_introl].
    now exists e'.
    now exists e.
  + rewrite combine_split; trivial.
    ++ unfold snd.
       rewrite combine_split; trivial.
    ++ rewrite combine_length.
       rewrite <-vs_length_eq, <-fs_length_eq.
       now rewrite min_r.
  + rewrite combine_split; trivial.
    ++ unfold snd.
       rewrite combine_split; trivial.
    ++ rewrite combine_length.
       rewrite <-vs_length_eq, <-fs_length_eq.
       now rewrite min_r.
  + rewrite combine_split; trivial.
    rewrite combine_length.
    rewrite <-vs_length_eq, <-fs_length_eq.
    now rewrite min_r.
Qed.

Lemma PermutedValsLength: forall vs vs' pi,
  ValsPermuted vs vs' pi ->
  length vs = length vs'.
Proof.
  intros vs.
  induction vs.
 + intros vs' pi pi_vs;
    destruct vs';
    try destruct a;
    try now destruct pi_vs.
  + intros vs' pi pi_vs.
    destruct vs', a;
    try now destruct pi_vs;
    simpl in *;
    now rewrite IHvs with (vs' := vs') (pi := pi).
Qed.

Lemma PermutedCtxsLength : forall ctxs ctxs_perm pi,
  CtxsPermuted ctxs ctxs_perm pi ->
  length ctxs = length ctxs_perm.
Proof.
  intros ctxs.
  induction ctxs;
    intros ctxs_perm pi pi_ctxs;
    destruct ctxs_perm; try now destruct pi_ctxs.
  simpl in *.
  now rewrite IHctxs with (ctxs_perm := ctxs_perm) (pi := pi).
Qed.

Lemma PermutedStacksLength : forall st st_perm pi,
  StacksPermuted st st_perm pi ->
  length st = length st_perm.
Proof.
  intros st.
  induction st;
    intros st_perm pi pi_st;
    destruct st_perm; try now destruct pi_st.
  simpl in *.
  now rewrite (IHst st_perm pi).
Qed.

(* Lemmas about extending permutations *)

Lemma ExtendValsPermutation : forall vs vs_perm pi pi',
  ValsPermuted vs vs_perm pi ->
  PermutationSubset pi pi' ->
  ValsPermuted vs vs_perm pi'.
Proof.
  intros vs vs_perm pi pi' pi_vs pi_subset.
  assert (length_eq : length vs = length vs_perm).
    now apply PermutedValsLength with (pi := pi).
  induction2 vs vs_perm length_eq v v_perm vs' vs'_perm; try easy.
  simpl in *.
  destruct v, v_perm; try now destruct pi_vs; split.
  + split; [now apply pi_subset | now apply IH_l].
  + split; [now apply pi_vs | now apply IH_l].
Qed.

Lemma ExtendExprsPermutation : forall e e_perm pi pi',
  ExprsPermuted e e_perm pi ->
  PermutationSubset pi pi' ->
  ExprsPermuted e e_perm pi'.
Proof.
  intros e.
  induction e;
    intros e_perm pi pi' pi_e pi_subset;
    destruct e_perm;
    try now (
    try destruct v;  try destruct v0;
    try destruct v1; try destruct v2;
    try destruct v3; try destruct vx, j;
    destruct pi_e).
  + simpl in *.
    split; try split; try easy.
    now apply ExtendValsPermutation with (pi := pi).
  + simpl in *.
    split; try split; try split; try easy.
    now apply IHe1 with (pi := pi).
    now apply IHe2 with (pi := pi).
  + simpl in *.
    destruct v0, v1, v2, v3; simpl in pi_e; try now destruct pi_e.
    ++ split; try split; try split; try now apply pi_subset.
       now apply IHe1 with (pi := pi).
       now apply IHe2 with (pi := pi).
    ++ split; try split; try split; try now apply pi_subset.
       now apply IHe1 with (pi := pi).
       now apply IHe2 with (pi := pi).
       now apply pi_e.
    ++ split; try split; try split; try now apply pi_subset.
       now apply IHe1 with (pi := pi).
       now apply IHe2 with (pi := pi).
       now apply pi_e.
    ++ split; try split; try split; try now apply pi_subset.
       now apply IHe1 with (pi := pi).
       now apply IHe2 with (pi := pi).
       now apply pi_e.
       now apply pi_e.
  + simpl in *.
    destruct v, v0; try now destruct pi_e.
    ++ split; try split; try easy.
       now apply pi_subset.
       now apply ExtendValsPermutation with (pi := pi).
    ++ split; try split; try easy.
       now apply ExtendValsPermutation with (pi := pi).
  + simpl in *.
    destruct vx, v, vx0, j1, v0, j; try now destruct pi_e;
    split; try split; try easy; now apply pi_subset.
  + simpl in *.
    destruct v, v0; try now destruct pi_e.
    now apply pi_subset.
  + simpl in *.
    destruct vx, vx0, j, j1; try now destruct pi_e.
    destruct pi_e.
    split; try easy; now apply pi_subset.
  + simpl in *.
    destruct v, v0; try now destruct pi_e.
    now apply pi_subset.
  + simpl in *.
    split.
    now apply IHe1 with (pi := pi).
    now apply IHe2 with (pi := pi).
Qed.

Lemma ExtendCtxPermutation : forall ctx ctx_perm pi pi',
  CtxPermuted ctx ctx_perm pi ->
  PermutationSubset pi pi' ->
  CtxPermuted ctx ctx_perm pi'.
Proof.
  intros ctx ctx_perm pi pi' pi_ctx pi_subset.
  destruct ctx, ctx_perm; try now destruct pi_ctx.
  + unfold CtxPermuted in *.
    destruct pi_ctx.
    split; try split; try easy.
    now apply ExtendExprsPermutation with (pi := pi).
  + unfold CtxPermuted in *.
    destruct pi_ctx.
    split; try split; try easy.
    now apply ExtendExprsPermutation with (pi := pi).
Qed.

Lemma ExtendCtxsPermutation : forall ctxs ctxs_perm pi pi',
  CtxsPermuted ctxs ctxs_perm pi ->
  PermutationSubset pi pi' ->
  CtxsPermuted ctxs ctxs_perm pi'.
Proof.
  intros ctxs ctxs_perm pi pi' pi_ctx pi_subset.
  assert (length_eq : length ctxs = length ctxs_perm).
    now apply PermutedCtxsLength with (pi := pi).

  induction2 ctxs ctxs_perm length_eq ctx ctx_perm ctxs' ctxs'_perm; try easy.
  simpl in *.
  destruct pi_ctx as (pi_ctx & pi_ctxs).
  split.
  now apply ExtendCtxPermutation with (pi := pi).
  now apply IH_l.
Qed.

Lemma ExtendFramePermutation : forall f f_perm pi pi',
  FramesPermuted f f_perm pi ->
  PermutationSubset pi pi' ->
  FramesPermuted f f_perm pi'.
Proof.
  intros f f_perm pi pi' pi_f pi_subset.
  unfold FramesPermuted in *.
  destruct f, f_perm.
  destruct pi_f as (pi_e & pi_ctx & a_eq).
  split; try split; try easy.
  now apply ExtendExprsPermutation with (pi := pi).
  now apply ExtendCtxsPermutation with (pi := pi).
Qed.

Lemma ExtendStacksPermutation : forall st st_perm pi pi',
  StacksPermuted st st_perm pi ->
  PermutationSubset pi pi' ->
  StacksPermuted st st_perm pi'.
Proof.
  intros st st_perm pi pi' pi_st pi_subset.
  assert (length_eq : length st = length st_perm).
    now apply PermutedStacksLength with (pi := pi).

  induction2 st st_perm length_eq f f_perm st' st'_perm; try easy.
  simpl in *.
  destruct pi_st as (pi_f & pi_st).
  split.
  now apply ExtendFramePermutation with (pi := pi).
  now apply IH_l.
Qed.