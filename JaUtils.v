(* Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Coq.Program.Equality. *)

Require Import Lists.List.
Import ListNotations.

From Hammer Require Import Reconstr.

Section JaUtils.

Lemma app_cons_alt : forall A a (l1 l2 l3 : list A),
    l1 ++ l2 = a :: l3 ->
    l1=[] /\ l2 = a :: l3 \/
            exists l4, l1=a::l4 /\ l4++l2=l3.
Proof.
  induction l1; sauto.
Qed.

(*
+ intros.
  auto.
+ simpl.
  intros.
  simplify_eq H; intros.
  eauto.
  right; eexists.
  split; eauto; congruence.
Qed.
*)


Lemma app_cons_last : forall A a (l1 l2 : list A),
    l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  intros.
  now rewrite <- app_assoc.
Qed.


(* auxiliary function on lists: zip two lists of equal length *)
Fixpoint zip {A B} (l1: list A) (l2 : list B) : option (list (A*B)) :=
  match l1, l2 with
  | [], [] => Some []
  | a::l1', b::l2' => match zip l1' l2' with None => None | Some ll => Some ((a,b)::ll) end
  | _, _ => None
  end.

Lemma zip_map_fst : forall {A B} (l1: list A) (l2: list B) ll, zip l1 l2 = Some ll -> map fst ll = l1.
Proof.
  induction l1.
  + intros *; destruct l2; simpl; now intros [= <-].
  + intros *; destruct l2; simpl.
    { congruence. }
    destruct zip eqn:Heq; swap 1 2.
    { congruence. }
    intros [= <-].
    simpl.
    f_equal.
    eauto 2.
Qed.
  
Lemma zip_map1_In : forall A B C l1 (l2: list B) ll (f: A -> C) b c,
  zip (map f l1) l2 = Some ll -> In (c,b) ll -> exists a, In a l1 /\ f a = c.
Proof.
  induction l1.
  + destruct l2; simpl; try congruence.
    intros * [= <-]; simpl; tauto.
  + destruct l2; simpl; try congruence.
    intros *.
    destruct zip eqn:Hz; try congruence.
    intros [= <-] [ [=] | HIn ].
    - eauto 4.
    - edestruct IHl1 as (a0 & HIna & Hfa); eauto 4.
Qed.      

Lemma Forall2_zip : forall A B C D l1 (l2: list B) ll (f: A -> C) (g: A -> D) R a, 
  Forall2 R l2 (map g l1) ->
  zip (map f l1) l2 = Some ll ->
  In a l1 ->
  exists b c, In (c,b) ll /\ c = f a /\ R b (g a).
Proof.
  induction l1; destruct l2; simpl; inversion 1; intuition; destruct zip eqn:Hz; try congruence.
  + generalize dependent ll; intros ? [= <-].
    subst a.
    simpl; do 2 eexists; auto.
  + generalize dependent ll; intros ? [= <-].
    edestruct IHl1 as (? & ? & ? & ? & ?); eauto 1.
    simpl; do 2 eexists; eauto 4.
Qed.

Lemma zip_length : forall A B (l1: list A) (l2: list B) ll, zip l1 l2 = Some ll -> length l1 = length l2. 
Proof.
  induction l1.
  + destruct l2; trivial.
    simpl; congruence.
  + destruct l2; simpl; try congruence.
    intros ll.
    destruct zip eqn: Heq; intros [= <-].
    erewrite IHl1; eauto 1.
Qed.    

Lemma length_zip : forall A B (l1: list A) (l2: list B),
    length l1 = length l2 -> exists ll, zip l1 l2 = Some ll. 
Proof.
  induction l1.
  + destruct l2; intros [=]; simpl; eauto 2.
  + destruct l2; simpl; try congruence.
    intros [=].
    edestruct IHl1 as (ll, Heq); eauto 1.
    eexists.
    rewrite Heq.
    eauto 1.
Qed.    


Lemma Forall2_length : forall A B R (l1: list A) (l2: list B),
    Forall2 R l1 l2 -> length l1 = length l2.
Proof.
  induction 1; trivial.
  simpl; auto.
Qed.

End JaUtils.
