(** * Collection of genaral tactics **)

(** 
   In case one has a hypothesis 
   [H : match e with ... => None end  =  Some ...]
   one wants to do [destruct e; discriminate H]

   [destr_discr H] does exactly this.

   However, doing this (esp. in a loop) can lead to loss of information 
   in case [e] is not a variable.
   Therefore [auto_destr_discr H] does destruct and loop only if [e] is 
   a variable.

   In case [e] is not a variable but one wants do do destruct anyway, 
   one can use [destr_discr H] which does not apply any check.
   
   [destr_discr_raw check H] is an workhorse tactic used by the two 
   and [accept] is an accept-all one argument tactic. 
**)

Ltac destr_discr_raw check H :=
  discriminate H
  ||
  ( match type of H with
      (match ?t with _ => _ end = _) => check t; destruct t
    end;
    try discriminate H ).

Ltac auto_destr_discr H :=
  repeat destr_discr_raw is_var H.

Ltac accept H := idtac.

Ltac destr_discr H :=
  destr_discr_raw accept H.

(** For temporarily blocking some hypotheses *)

Definition HIDE (E:Prop) := E.

Ltac hide H :=
  let E := type of H in
  change (HIDE E) in H.


Definition comment {A:Type} (a:A) := True.

Notation "### X #" := (comment X) (at level 100, no associativity) : type_scope.

Ltac comment name what :=
  assert (comment what) as name by exact I.

Ltac get_last_hypothesis :=
  match goal with H: _ |- _ => constr:(H) end.

Ltac get_first_hypothesis :=
  match reverse goal with H: _ |- _ => constr:(H) end.

Ltac where_am_i :=
  repeat (match reverse goal with
          | [ H1 : comment ?X |- _ ] =>
            let H := get_last_hypothesis in
            move H1 after H; hide H1
          end);
  unfold HIDE in *.

Ltac hide_comments :=
  repeat (match goal with
          | [ H1 : comment ?X |- _ ] =>
            match reverse goal with
              [ H: _ |- _ ] =>  move H1 after H; hide H1
            end
          end);
    unfold HIDE in *.

Require Import String.
Local Open Scope string_scope.

Ltac destr_discr_info H :=
  discriminate H
  ||
  let pp := fresh "prev" in
  ( match type of H with
      (match ?t with _ => _ end = _) =>
      destruct t eqn:pp;
      let T := type of pp in
      let d := fresh "d" in
      comment d T
    end;
    try discriminate H ).


(** 
    [substh id hyp] works similar to [subst id], but only in the hypothesis [hyp]. 
**) 


Ltac substh id hyp :=
  match goal with [ H : id = _ |- _ ] => rewrite H in hyp end.

(** Cool tactic taken from
    # <a href="https://stackoverflow.com/questions/22404394/how-to-automatically-generate-good-names-when-decomposing-existential-hypothes%2322543921">a stackoverflow question</a> #
   which destructs a given hypothesis [H : ∃ (x:A) (y:B) (z:C), P x y z] into
   - [x : A]
   - [y : B]
   - [z : C]
   - [H : P x y z]
*)

Ltac do_destr H x :=
  let x := fresh x in
  let H' := fresh H in
  edestruct H as [x H'];
  try (is_var H'; clear H; rename H' into H).


Ltac destr_one_ex H := 
match type of H with 
| ex (fun x => _) => do_destr H x
| forall _, ex (fun x => _) => do_destr H x
| forall _ _, ex (fun x => _) => do_destr H x
| forall _ _ _, ex (fun x => _) => do_destr H x
end.


Ltac decompose_ex H :=
  repeat destr_one_ex H.



(** [decompose_and H as (? & Y & H)].
   It destructs completely a conjunction [H] giving a name [Y] 
   to the second conjunct and automatic names to the others. 
   The initial conjunction is cleared.
   If [H] is not present at the end of the intropattern, 
   the conjunction is not decomposed completely.
   *)
Tactic Notation "decompose_and" ident(H) :=
  decompose [and] H; clear H.

Tactic Notation "decompose_and" ident(H) "as" simple_intropattern(patt) :=
  destruct H as patt;
  try (progress decompose [and] H; clear H).





(** [ssplit] - safe split - splits _only_ conjunctions in the goal and
   only the main line. Normal [repeat split] may do some unwanted evar
   instantiations and apply constructors in other one-constructor
   inductive types *)
Ltac ssplit :=
  lazymatch goal with
  [ |- (_ /\ _) ] =>
    split; [ssplit | ssplit]
  | _ => idtac
  end.

(** [subtle] solve trivial goals _without_ instantiating evars; 
   recommended for [repeat (ssplit; subtle)] *)
Ltac subtle := try match goal with [ |- ?G ] => has_evar G; fail 2 end || trivial.



Require Import JaSyntax.

(** [destruct_eq] siplifies handling of (decidable) quality tests in goals *) 

Ltac destruct_eq := try match goal with
                          [ |- context [string_dec ?C ?C] ] => destruct (string_dec C C); try contradiction
                        | [ |- context [JFXId_dec ?C ?C] ] => destruct (JFXId_dec C C); try contradiction
                        | [ |- context [JFVal_dec ?C ?C] ] => destruct (JFVal_dec C C); try contradiction
                        | [ |- context [JFClassName_dec ?C ?C] ] => destruct (JFClassName_dec C C); try contradiction
                        | [ H : (?C <> ?D) |- context [string_dec ?C ?D] ] => destruct (string_dec C D); try contradiction
                        | [ H : (?C = ?D) |- context [string_dec ?C ?D] ] => destruct (string_dec C D); try contradiction
                        end.


(** [eqf] finds two equalities with identical lhs, derives new
    equality between the two rhs and simplifies it *) 

Ltac eqf :=
  match goal with
    [ H1 : ?l = ?r, H2 : ?l = ?r' |- _ ] =>
      let H := fresh in
      assert (r=r') as H by congruence;
      simplify_eq H; clear H
  end.
              
  


