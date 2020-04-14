Require Import List.
Import ListNotations.
From Hammer Require Import Reconstr.
Require Import Arith.
Require Import Omega.

Lemma eq_Snm_nm :
  forall n m, S n = S m -> n = m. 
Proof.
  now intros * [=].
Qed.  

Lemma count_occ_app :
  forall A eq_dec l2 (x:A) l1,
    count_occ eq_dec (l1++l2) x = count_occ eq_dec l1 x + count_occ eq_dec l2 x.
Proof.
  induction l1.
  + trivial.
  + simpl.
    destruct eq_dec.
    - now rewrite IHl1.
    - trivial.
Qed.        


Definition HIDE {A:Type} (a:A) := a.

(* Dodatkowe wymaganie: wyjąć identyfikatory z listy unique i dołożyć do nich coś innego wciąż zachowująć gwarancję unique *)


Module Type Name.
  Parameter name : Type.
  Parameter name_dec : forall x y : name, {x=y}+{~x=y}.
End Name.

Module NameUniq(Import Inline X:Name).
  Section Declarations.
  Context {decl:Type}.
  Variable name_of_decl : decl -> name.
  
  (** type of list of declarations *)
  Definition t := list decl.

  Definition name_xi d v :=
    if name_dec (name_of_decl d) v then 1 else 0.
  
  Definition name_occ decls v :=
    count_occ name_dec (map name_of_decl decls) v.

  Definition names_unique decls := forall v, name_occ decls v <= 1.

  Lemma name_occ_nil : forall v, name_occ [] v = 0. 
  Proof.
    trivial.
  Qed.
  Hint Rewrite name_occ_nil : uniq.

  Lemma name_occ_singl : forall d v,
      name_occ [d] v = name_xi d v.
  Proof.
    trivial.
  Qed.
  Hint Rewrite name_occ_singl : uniq.
  
  Lemma name_occ_app : forall decls1 decls2 v,
      name_occ (decls1 ++ decls2) v = name_occ decls1 v + name_occ decls2 v.
  Proof.
    intros.
    unfold name_occ.
    rewrite map_app.
    apply count_occ_app.
  Qed.    
  Hint Rewrite name_occ_app : uniq.

  Lemma name_occ_cons : forall d decls v,
      name_occ (d::decls) v = name_xi d v + name_occ decls v.
  Proof.
    intros *.
    replace (d::decls) with ([d]++decls) by trivial.
    autorewrite with uniq.
    trivial.
  Qed.    
  Hint Rewrite name_occ_cons : uniq.
  
  Lemma name_once_decl : forall d, name_xi d (name_of_decl d) = 1.
  Proof.
    unfold name_xi.
    sauto.
  Qed.
  Hint Rewrite name_once_decl : uniq.

  Lemma name_xi_small : forall v d, name_xi d v <= 1.
  Proof.
    unfold name_xi.
    sauto.
  Qed.
  Hint Resolve name_xi_small.
  
  Lemma name_once : forall v d, name_of_decl d = v <-> name_xi d v = 1.
  Proof.
    unfold name_xi.
    sauto.
  Qed.
  Lemma name_once_sym : forall v d, v = name_of_decl d <-> name_xi d v = 1.
  Proof.
    unfold name_xi.
    sauto.
  Qed.
  (* use with caution - use subst instead *)
  
  Lemma name_occ_In : forall v decls, In v (map name_of_decl decls) <-> name_occ decls v >= 1. 
  Proof.
    intros.
    split.
    - now apply count_occ_In.
    - induction decls; autorewrite with uniq; simpl.
      + omega.
      + unfold name_xi.
        destruct name_dec; auto.
  Qed.
  
  Lemma name_noocc_In : forall v decls, ~ In v (map name_of_decl decls) <-> name_occ decls v = 0. 
  Proof.
    intros.
    split.
    - now apply count_occ_not_In.
    - intros; intro HIn.
      apply -> name_occ_In in HIn.
      omega.
  Qed.

  Lemma name_noocc : forall v d, name_of_decl d <> v <-> name_xi d v = 0.
  Proof.
    unfold name_xi.
    sauto.
  Qed.

  Lemma name_noocc_sym : forall v d, v <> name_of_decl d  <-> name_xi d v = 0.
  Proof.
    unfold name_xi.
    sauto.
  Qed.


  (* next few lemmas are no longer symmetric *)
  Lemma name_occ_In_decl : forall d decls, In d decls -> name_occ decls (name_of_decl d) >= 1.
  Proof.
    intros.
    apply name_occ_In.
    now apply in_map.
  Qed.
    
  Lemma name_noocc_In_decl : forall d decls,
      ~ In d decls -> names_unique (d::decls) -> name_occ decls (name_of_decl d) = 0.
  Proof.
    intros * HnIn HU.
    pose proof (HU (name_of_decl d)) as H.
    autorewrite with uniq in H. 
    omega.
  Qed.

  Lemma name_noocc_In_decl_rev : forall d decls,
      name_occ decls (name_of_decl d) = 0 -> ~ In d decls.
  Proof.
    intros.
    intro HIn.
    apply name_occ_In_decl in HIn.
    omega.
  Qed.

  
  Lemma name_eq_xi : forall d1 d2 v,
      name_of_decl d1 = name_of_decl d2 -> name_xi d1 v = name_xi d2 v.
  Proof.
    unfold name_xi.
    now intros * [= ->].
  Qed.

  Lemma name_eq_xi_rev : forall d1 d2,
      (forall v, name_xi d1 v = name_xi d2 v) -> name_of_decl d1 = name_of_decl d2.
  Proof.
    intros * H.
    specialize (H (name_of_decl d2)).
    autorewrite with uniq in *.
    unfold name_xi in *.
    destruct name_dec; congruence.
  Qed.

  End Declarations.

  Hint Rewrite @name_occ_nil : uniq.
  Hint Rewrite @name_occ_singl : uniq.
  Hint Rewrite @name_occ_app : uniq.
  Hint Rewrite @name_occ_cons : uniq.
  Hint Rewrite @name_once_decl : uniq.
  
  (* autorewrite *)
  Ltac uniq0 :=
    autorewrite with uniq in *.

Goal forall a b c d e, ((((a + b) + c) + 1) + d) + e = 1 -> e = 0.
intros.
rewrite Nat.add_1_r in H.  
simpl in H.  
apply eq_Snm_nm in H.
repeat (apply plus_is_O in H; destruct H).
Abort.


(* tu jeszcze można by jakoś obsłużyć a + 1 + b = 1 i <= 1 *)
(* to by trzeba było jakiś context, albo rewrite a+1 -> S a; simpl na ślepo *)

  Ltac simp_arith :=
    repeat
      (try rewrite ! Nat.add_0_r in *; simpl plus in *;
       match goal with
      | [ H : ?a + ?b = 0 |- _ ] => apply plus_is_O in H; destruct H
      | [ H : S ?b = 1 |- _ ] => simpl in H; apply eq_Snm_nm in H
      | [ |- S ?b = 1 ] => simpl; f_equal
      | [ H : S ?b <= 1 |- _ ] =>
        simpl in H; apply Peano.le_S_n in H; apply Nat.le_0_r in H
      | [ |- S ?b <= 1 ] => simpl; apply Peano.le_n_S; apply Nat.eq_le_incl
      | [ H : ?b + 1 = 1 |- _ ] => rewrite Nat.add_1_r in H; apply eq_Snm_nm in H
      | [ |- ?b + 1 = 1 ] => rewrite Nat.add_1_r; f_equal
      | [ H : ?b + 1 <= 1 |- _ ] =>
        rewrite Nat.add_1_r in H; apply Peano.le_S_n in H; apply Nat.le_0_r in H
      | [ |- ?b + 1 <= 1 ] => rewrite Nat.add_1_r; apply Peano.le_n_S; apply Nat.eq_le_incl
      | [ H : ?b = 0 |- _ ] => rewrite !H in *
      | [ H : 0 = ?b |- _ ] => rewrite <- !H in *
      | [ H : ?b = 1 |- _ ] => rewrite !H in *
      | [ H : 1 = ?b |- _ ] => rewrite <- !H in *
      | _ => idtac
       end). 

  
  
  Ltac case_xi_fun name_of_decl d v :=
    let t := eval red in (name_xi name_of_decl d v) in
    change (name_xi name_of_decl d v) with t in *;
    destruct (name_dec (name_of_decl d) v);
    simp_arith.

  
  (* extract all info about a given v *)
  Ltac uniq_step_d name_of_decl d :=
    match goal with
    | [ H : name_of_decl d = ?v |- _ ] =>  is_var v; subst v
    | [ H : ?v = name_of_decl d |- _ ] =>  is_var v; subst v
    | [ H : names_unique name_of_decl ?decls |- _ ] =>
      pose proof (H (name_of_decl d));
      change (HIDE (names_unique name_of_decl decls)) in H
    | [ H : name_of_decl d = name_of_decl ?d' |- _ ] =>
      try rewrite <- !H in *;
      try rewrite <- !(name_eq_xi name_of_decl) with (1:=H) in *;
      change (name_of_decl d') with (HIDE (name_of_decl (HIDE d'))) in H
    | [ H : name_of_decl ?d' = name_of_decl d |- _ ] =>
      try rewrite ! H in *;
      try rewrite (name_eq_xi name_of_decl) with (1:=H) in *;
      change (name_of_decl d') with (HIDE (name_of_decl (HIDE d'))) in H
    | [ H : ?v = name_of_decl d |- _ ] => is_var v; subst v
    | [ H : name_of_decl d <> ?v |- _ ] => apply name_noocc in H
    | [ H : ?v <> name_of_decl d |- _ ] => apply name_noocc_sym in H
    | [ H : In d ?decls |- _ ] => apply (name_occ_In_decl name_of_decl) in H
    end.

  Ltac uniq_d name_of_decl d :=
    uniq0;
    repeat (uniq_step_d name_of_decl d; uniq0);
    match goal with
    | [ |- name_of_decl d = ?v ] => apply name_once
    | [ |- ?v = name_of_decl d ] => apply name_once_sym
    | [ |- name_of_decl d <> ?v ] => apply name_noocc
    | [ |- ?v <> name_of_decl d ] => apply name_noocc_sym
    (* | [ |- In d ?decls ] =>  nothing *)
    | [ |- ~ In d ?decls ] => apply name_noocc_In_decl_rev
    | [ |- In (name_of_decl d) (map name_of_decl ?decls) ] => apply name_occ_In 
    | [ |- ~ In (name_of_decl d) (map name_of_decl ?decls) ] => apply name_noocc_In
    | _ => idtac
    end; unfold HIDE in *; simp_arith.

  
  Ltac uniq_v name_of_decl v :=
    match goal with
    | [ H : name_of_decl ?d = v |- _ ] => subst v; uniq_d name_of_decl d
    | [ H : v = name_of_decl ?d |- _ ] => subst v; uniq_d name_of_decl d
    | [ |- name_of_decl ?d <> v ] => intro; subst v; uniq_d name_of_decl d
    | [ |- v <> name_of_decl ?d ] => intro; subst v; uniq_d name_of_decl d
    end
    || 
    (uniq0; repeat
      (match goal with
      | [ H : v = ?v' |- _ ] => subst v' 
      | [ H : name_of_decl ?d <> v |- _ ] => apply name_noocc in H
      | [ H : v = name_of_decl ?d |- _ ] => apply name_noocc_sym in H
      | [ H : In v (map name_of_decl ?decls) |- _ ] => apply name_occ_In in H
      | [ H : ~ In v (map name_of_decl ?decls) |- _ ] => apply name_noocc_In in H
      | [ H : names_unique name_of_decl ?decls |- _ ] =>
        pose proof (H v); change (HIDE (names_unique name_of_decl decls)) in H
      | [ |- In v (map name_of_decl ?decls) ] => apply name_occ_In
      | [ |- ~ In v (map name_of_decl ?decls) ] => apply name_noocc_In
      end;
    uniq0)); unfold HIDE in *; simp_arith.

  Ltac uniq_x name_of_decl x :=
    match type of name_of_decl with
    | ?decl -> ?name =>
      let t := type of x in
      ( let e := constr:(eq_refl name : name = t) in uniq_v name_of_decl x )
      ||
      ( let e := constr:(eq_refl decl : decl = t) in uniq_d name_of_decl x )
      ||
      (idtac t)
    | ?t => idtac "Some strange type name_of_decl without an arrow" t; fail 1
    end.
  
(* This lemma is false...  
   One can have d <> d' in decls, such that n_of_d d = n_of_d d'

  Non-Lemma name_occ_In_decl_rev : forall d decls,
      names_unique (decls) -> name_occ decls (name_of_decl d) >= 1 -> In d decls.
*)


  (* | [ H : v <> ?v' ] => ??? *) 
      

  (* coś trzeba zrobić z sytuacjami name_of_decl d1 = name_of_decl d2... ale co??? *)
  (* może dwie równości:
     name_xi d1 (name_of_decl d2) = 1
     name_xi d2 (name_of_decl d1) = 1
   *)
  (* W sumie z jednej z tych równości wynika druga... *)

  (* Troche podobnie mamy z różnością name_of_decl d1 <> name_of_decl d2  też:
     name_xi d1 (name_of_decl d2) = 0
     name_xi d2 (name_of_decl d1) = 0
   *)
  (* I również z jednej z tych równości wynika druga... *)

  (* Jakiś pomysł, żeby na początek skupić się na jednym name, np. v albo (name_of_decl d) *)
  (* I tylko dla niego upraszczać maksymalnie całą wiedzę *)
  (* Korzystając też z names_unique *)

  (* rzeczy dziwne... 
     Powiedzmy, że szukamy (name_of_decl d) i mamy:
     name_occ [d;d1] (name_of_decl d2) = 0
     i tego wynika, że 
     name_occ d2 (name_of_decl d) = 0 
     (do tego można jakoś w miarą łatwo dojść jak będziemy najpierw rozbijać 
     wszystkie consy za pomocą autorewrite)

     Ale jeszcze lepsze:
     name_occ [d;d1] (name_of_decl d2) = 1
     z tego wynika, że
     name_occ [d] (name_of_decl d2) + name_occ [d1] (name_of_decl d2) = 1
     a także, że
     name_occ [d2] (name_of_decl d) + name_occ [d1] (name_of_decl d2) = 1
  *)

  (* ogólnie zawsze 
     name_occ [d1] (name_of_decl d2) = name_occ [d2] (name_of_decl d1) =
  *)

(* Są trzy rodzaje obiektów:

   decls
   d
   v

Może wprowadzić 
  name_xi d v = 1  if  name_of_decl d = v
  name_xi d v = 0  if  name_of_decl d <> v
  name_xi d v <= 1

I w lematach zamieniać [d] na name_xi

Mamy też oczywiście
name_of_decl d1 = name_of_decl d2  ->  forall v, name_xi d1 v = name_xi d2 v
i to potem można specialize'ować dla wszystkiego co się rusza...
 *)
     


(*


  
  (** name occurs exactly once *)
  Definition name_once decls v :=
    count_occ name_dec (map name_of_decl decls) v = 1.

  Definition name_noocc decls v :=
    count_occ name_dec (map name_of_decl decls) v = 0.
  
 *)
  Section Lemmas.

  Context { decl : Type }.

  Variable name_of_decl : decl -> name.

  Ltac uniq := uniq_x name_of_decl.
  Ltac case_xi := case_xi_fun name_of_decl.
  
  Notation name_xi := (name_xi name_of_decl).
  Notation name_occ := (name_occ name_of_decl).
  Notation names_unique := (names_unique name_of_decl).
  
  Lemma name_once_noocc_tail:
    forall decls v d,
      name_of_decl d = v -> 
      name_occ (d :: decls) v = 1 -> name_occ decls v = 0.
  Proof.
    sauto.
  Qed.

  Hint Immediate name_once_noocc_tail.
  
  Lemma name_once_further_neq:
    forall v v' d decls,
      v <> v' ->
      name_of_decl d = v ->
      name_occ (d :: decls) v' = 1 ->
      name_occ decls v' = 1.
  Proof.
    sauto.
  Qed.

  Hint Immediate name_once_further_neq.

  Lemma name_once_further_inv :
    forall v decls d,
      name_occ (d :: decls) v = 1 ->
      (name_of_decl d = v /\ name_occ decls v = 0)
      \/ (name_of_decl d <> v /\ name_occ decls v = 1).
  Proof.
    intros.
    uniq0.
    case_xi d v; auto.
  Qed.
  
      
  Lemma name_once_cons_neq:
    forall v v' d decls,
      v <> v' ->
      name_occ decls v = 1 ->
      name_of_decl d = v' ->
      name_occ (d :: decls) v = 1.
  Proof.
    sauto.
  Qed.

  Lemma name_once_cons_eq:
    forall v decls d,
      name_occ decls v = 0 ->
      name_of_decl d = v -> 
      name_occ (d :: decls) v = 1.
  Proof.
    sauto.
  Qed.

  Hint Resolve name_once_cons_neq name_once_cons_eq.
  
  Lemma name_once_In:
    forall decls v,
      name_occ decls v = 1 -> In v (map name_of_decl decls).
  Proof.
    intros.
    uniq v.
    auto with arith.
  Qed.

  Hint Resolve name_once_In.
  
  Lemma name_once_In_decl:
    forall decls v,
      name_occ decls v = 1 -> exists d, name_of_decl d = v /\ In d decls.
  Proof.
    intros.
    rewrite <- in_map_iff.
    now apply name_once_In.
  Qed.

  Lemma name_noocc_cons :
    forall v decls d,
      name_occ decls v = 0 -> name_of_decl d <> v -> name_occ (d::decls) v = 0.
  Proof.
    intros * H1 H2.
    now uniq v.
  Qed.

  Hint Resolve name_noocc_cons.

  Lemma name_noocc_cons_inv :
    forall v decls d,
      name_occ (d::decls) v = 0 -> name_of_decl d <> v /\ name_occ decls v = 0.
  Proof.
    sauto.
  Qed.

  Lemma name_noocc_head :
    forall v decls d,
      name_occ (d::decls) v = 0 -> name_of_decl d <> v.
  Proof.  
    intros.
    edestruct name_noocc_cons_inv; eauto 2.
  Qed.
  Hint Immediate name_noocc_head.

  Lemma name_noocc_further :
    forall v decls d,
      name_occ (d::decls) v = 0 -> name_occ decls v = 0.
  Proof.  
    intros.
    edestruct name_noocc_cons_inv; eauto 2.
  Qed.
  Hint Immediate name_noocc_further.
  
  Lemma name_noocc_not_In:
    forall decls v,
      name_occ decls v = 0 ->
      ~ In v (map name_of_decl decls).
  Proof.
    intros.
    uniq v.
    trivial.
  Qed.

  Hint Resolve name_noocc_not_In.
  
  

  Lemma not_In_name_noocc:
    forall decls v,
      ~ In v (map name_of_decl decls) ->
      name_occ decls v = 0.
  Proof.
    intros.
    uniq v.
    trivial.
  Qed.

  Hint Resolve not_In_name_noocc.


  Lemma name_noocc_In_neq:
    forall decls v v',
      name_occ decls v = 0 ->
      In v' (map name_of_decl decls) ->
      v <> v'.
  Proof.
    intros.
    intro.
    subst.
    uniq v'.
    omega.
  Qed.

  Hint Resolve name_noocc_In_neq.
  
  Lemma name_noocc_In_decl_neq:
    forall decls d v,
      name_occ decls v = 0 ->
      In d decls ->
      name_of_decl d <> v.
  Proof.
    intros.
    intro.
    uniq v.
    omega.
  Qed.

  Hint Resolve name_noocc_In_decl_neq.

  Lemma name_noocc_decompose_l :
    forall decls1 decls2 v,
      name_occ (decls1 ++ decls2) v = 0 -> name_occ decls1 v = 0. 
  Proof.
    intros.
    uniq0.
    simp_arith.
    trivial.
  Qed.
  
  Lemma name_noocc_decompose_r :
    forall decls1 decls2 v,
      name_occ (decls1 ++ decls2) v = 0 -> name_occ decls2 v = 0. 
  Proof.
    intros.
    uniq0.
    simp_arith.
    trivial.
  Qed.

  Hint Immediate name_noocc_decompose_l name_noocc_decompose_r.
  
  Lemma name_noocc_app:
    forall decls1 decls2 v,
      name_occ decls1 v = 0 ->
      name_occ decls2 v = 0 ->
      name_occ (decls1 ++ decls2) v = 0.
  Proof.
    intros.
    now uniq v.
  Qed.
  Hint Resolve name_noocc_app.
  
  Lemma name_once_In_unique:
    forall v d d' decls,
      name_occ decls v = 1 ->
      In d decls ->
      In d' decls ->
      name_of_decl d = v ->
      name_of_decl d' = v ->
      d = d'.
  Proof.
    induction decls.
    + inversion 2.
    + uniq0; simpl.
      intros Hocc Hd Hd' ? ?.
      case_xi a v; swap 1 2.
      * destruct Hd; try congruence.
        destruct Hd'; try congruence.
        auto.
      * destruct Hd; swap 1 2.  
        { uniq d. omega. }
        destruct Hd'; swap 1 2.        
        { uniq d'; omega. }
        congruence.
  Qed.
  Hint Resolve name_once_In_unique.
(*
(** The property that all values occur in the environment uniquely. *)
  Definition names_unique decls :=
    Forall (name_once decls) (map name_of_decl decls).
*)

  Lemma names_unique_nil:
    names_unique [].
  Proof.
    red.
    intro v.
    uniq v.
    auto.
  Qed.    
  Hint Resolve names_unique_nil.
  
  Lemma names_unique_zero:
    forall decls v d,
      name_of_decl d = v ->
      names_unique (d :: decls) ->
      name_occ decls v = 0.
  Proof.
    intros.
    uniq v.
    trivial.
  Qed.

  Hint Resolve names_unique_zero.

(*
  L e m m a names_unique_cons:
    forall decls d,
      names_unique decls ->
      name_occ decls (name_of_decl d) = 0 -> 
      names_unique (d :: decls).
  Proof.
    intros.
    intro v.
    uniq v.
    case_xi d v; 
    congruence.
  Qed.

  Hint Resolve names_unique_cons.
  *)
  
  Lemma names_unique_cons:
    forall decls v d,
      names_unique decls ->
      name_of_decl d = v ->
      name_occ decls v = 0 -> 
      names_unique (d :: decls).
  Proof.
    intros.
    intro v0.
    uniq d.
    case_xi d v0; uniq v0; trivial.
  Qed.

  Hint Resolve names_unique_cons.
  
  Lemma names_unique_further:
    forall decls d,
      names_unique (d::decls) ->
      names_unique decls.
  Proof.
    intros.
    intro v.
    uniq v.
    case_xi d v; trivial; omega.
  Qed.
  
  Hint Immediate names_unique_further.

  Lemma names_unique_permute :
    forall d decls2a decls2b,
      names_unique (d :: decls2a ++ decls2b) -> 
      names_unique (decls2a ++ d :: decls2b).
  Proof.
    intros.
    intro v.
    uniq v.
    omega.
  Qed.

  Hint Resolve names_unique_permute.

  
  Lemma names_unique_decompose_r:
    forall decls1 decls2,
      names_unique (decls1 ++ decls2) ->
      names_unique decls2.
  Proof.
    intros.
    intro v.
    uniq v.
    omega.
  Qed.

  Lemma names_unique_decompose_l:
    forall decls1 decls2,
      names_unique (decls1 ++ decls2) ->
      names_unique decls1.
  Proof.
    intros.
    intro v.
    uniq v.
    omega.
  Qed.

  Hint Immediate names_unique_decompose_r names_unique_decompose_l.

  Lemma name_noocc_recip :
    forall decls1 decls2,
      Forall (fun d => name_occ decls1 (name_of_decl d) = 0) decls2 ->
      Forall (fun d => name_occ decls2 (name_of_decl d) = 0) decls1.
  Proof.
    intros until 0.
    rewrite! Forall_forall.
    intros H d Hd.
    (* suppose (nd d) occurs in decl2 *)
    edestruct Gt.gt_0_eq as [Hg | ]; eauto.
    apply name_occ_In in Hg.
    (* then there is d' in decl2 with the same name *)
    rewrite in_map_iff in Hg.
    destruct Hg as (d' & Heq & Hd').
    (* so d's name does not occur in decl1 *)
    apply H in Hd'.
    apply name_noocc_In in Hd'.
    (* but that's impossible since d is in decl1 *)
    contradiction Hd'.
    uniq d.
    uniq d'.
    trivial.
  Qed.

  Hint Immediate name_noocc_recip.
  
  Lemma names_unique_app :
    forall decls1 decls2,
      names_unique decls1 ->
      names_unique decls2 ->
      Forall (fun d => name_occ decls1 (name_of_decl d) = 0) decls2 ->
      names_unique (decls1 ++ decls2).
  Proof.
    induction decls1.
    + auto.
    + intros ? ? ? Hf.
      simpl.
      eapply names_unique_cons; eauto 1.
      * apply IHdecls1; eauto 1.
        rewrite Forall_forall in *.
        intros d Hd.
        apply Hf in Hd.
        uniq d.
        trivial.
      * apply name_noocc_recip in Hf.
        rewrite Forall_forall in Hf.
        specialize (Hf a).
        simpl in *.
        intuition.
        uniq a.
        omega.
  Qed.

  Hint Resolve names_unique_app.

        
  Lemma names_unique_In_unique:
    forall decls d d',
      names_unique decls ->
      In d decls ->
      In d' decls ->
      name_of_decl d = name_of_decl d' ->
      d = d'.
  Proof.
    intros.
    eapply name_once_In_unique; cycle 1; eauto 1.
    uniq d'; omega.
  Qed.

  Fixpoint find decls v :=
    match decls with
    | nil => None
    | d :: tl => if name_dec v (name_of_decl d)
                then Some d
                else find tl v
    end.

  Lemma find_In : forall decls v d, find decls v = Some d -> In d decls.
  Proof.
    induction decls; sauto.
  Qed.

  Hint Resolve find_In.

  Lemma find_right : forall decls v d, find decls v = Some d -> name_of_decl d = v.
  Proof.
    induction decls; sauto.
  Qed.

  Hint Resolve find_right.
  
  Lemma In_find_weak : forall v d decls, In d decls -> name_of_decl d = v -> find decls v = None -> False.
  Proof.
    induction decls; sauto.
  Qed.

  Lemma in_map_find:
  forall x decls,
    In x (map name_of_decl decls) -> exists d, find decls x = Some d.
  Proof.
    induction decls; sauto.
  Qed.

  Hint Resolve in_map_find.
  
  Lemma In_find_exists :
    forall decls v d,
      In d decls ->
      name_of_decl d = v ->
      exists d', find decls v = Some d' /\ name_of_decl d' = v.
  Proof.
    induction decls; scrush.
  Qed.

  Hint Resolve In_find_exists.

  Lemma In_find :
    forall decls v d,
      names_unique decls ->
      In d decls ->
      name_of_decl d = v ->
      find decls v = Some d.
  Proof.
    intros until 0; intros Hu HIn Hd.
    generalize Hd; intro Hd'.
    eapply In_find_exists in Hd'; eauto 1.
    destruct Hd' as (d' & Hf' & Hd').
    generalize Hf'; intro Htmp.
    apply find_In in Htmp.
    assert (d=d') as Heq.
    uniq d'.
    { eapply names_unique_In_unique; eauto 2. }
    now rewrite Heq.
  Qed.

  Hint Resolve In_find.

  Lemma find_app_l_some :
    forall decls1 decls2 v d,
      find decls1 v = Some d ->
      find (decls1 ++ decls2) v = Some d.
  Proof.
    induction decls1; sauto.
  Qed.  

  Hint Resolve find_app_l_some.
  
  Lemma find_app_r :
    forall decls1 decls2 v,
      find decls1 v = None ->
      find (decls1 ++ decls2) v = find decls2 v.
  Proof.
    induction decls1; sauto.
  Qed.  

  Hint Rewrite find_app_r.

  Lemma find_app_r_noocc :
    forall decls1 decls2 v,
      name_occ decls1 v = 0 ->
      find (decls1 ++ decls2) v = find decls2 v.
  Proof.
    induction decls1; sauto.
  Qed.  

  Hint Rewrite find_app_r_noocc.

  Lemma find_app_r_unique :
    forall decls1 decls2 v d,
      names_unique (decls1 ++ decls2) ->
      find decls2 v = Some d ->
      find (decls1 ++ decls2) v = Some d.
  Proof.
    intros ? ? ? ? Hu Hf2.
    generalize Hf2. intro HIn.
    apply find_In in HIn.
    generalize Hf2. intro Htmp.
    apply find_right in Htmp.
    apply In_find; sauto.
  Qed.  

  Hint Rewrite find_app_r_unique.
  

  (** [add decls d] overrides corrent definition of [name_of_decl d] in [decls]; 
      adds one if absent *)
  Fixpoint add decls d :=
    match decls with
    | nil => [d]
    | d' :: tl =>
      if name_dec (name_of_decl d) (name_of_decl d') then
        d :: tl
      else
        d' :: add tl d
    end.


  Lemma name_noocc_add :
    forall decls d v,
      name_occ decls v = 0 -> name_of_decl d <> v -> name_occ (add decls d) v = 0.
  Proof.
    induction decls.
    * simpl.
      intros.
      uniq v.
      trivial.
    * intros * ? Hne.
      simpl.
      destruct name_dec.
      + uniq d; trivial.
      + apply IHdecls in Hne; uniq d; trivial.
  Qed.
  Hint Resolve name_noocc_add.


  Lemma name_noocc_add_inv :
    forall v decls d,
      name_occ (add decls d) v = 0 -> name_of_decl d <> v /\ name_occ decls v = 0.
  Proof.
    induction decls.
    - sauto.
    - intros *.
      simpl.
      destruct name_dec.
      + intros H.
        split; uniq d; trivial.
      + intros H.
        split; uniq v; edestruct IHdecls; eauto 1; tauto.
  Qed.

  Lemma name_noocc_add_further :
    forall v decls d,
      name_occ (add decls d) v = 0 -> name_occ decls v = 0.
  Proof.
    intros.
    edestruct name_noocc_add_inv; eauto 1.
  Qed.
  Hint Immediate name_noocc_add_further.

  Lemma name_noocc_add_neq :
    forall v decls d,
      name_occ (add decls d) v = 0 -> name_of_decl d <> v.
  Proof.
    intros.
    edestruct name_noocc_add_inv; eauto 1.
  Qed.
  Hint Resolve name_noocc_add_neq.
  
  Lemma name_once_add :
    forall decls d v,
      name_occ decls v = 1 -> name_occ (add decls d) v = 1.
  Proof.
    induction decls.
    * sauto. 
    * simpl.
      intros * H.
      edestruct name_dec.
      + uniq d.
      + uniq v.
        case_xi a v.
        - rewrite name_noocc_add; trivial; congruence.
        - auto.
  Qed.  
  Hint Resolve name_once_add.
    
  Lemma In_add_In :
    forall decls d v,
      In v (map name_of_decl decls) -> In v (map name_of_decl (add decls d)).
  Proof.
    induction decls.
    * sauto.
    * simpl.
      destruct 1; destruct name_dec; simpl; auto.
      sauto.
  Qed.
  Hint Resolve In_add_In.
  
  Lemma In_add_inv :
    forall v decls d,
      In v (map name_of_decl (add decls d)) -> name_of_decl d = v \/ In v (map name_of_decl decls).
  Proof.
    induction decls.
    * sauto.
    * intros *.
      simpl.
      destruct name_dec; simpl; auto; intuition.
      edestruct IHdecls; eauto 3.
  Qed.

  
  Lemma add_unique :
    forall decls d,
      names_unique decls -> names_unique (add decls d).
  Proof.
    induction decls.
    * unfold names_unique; sauto.
    * simpl.
      intros.
      edestruct name_dec.
      + clear IHdecls.
        red.
        intro v.
        uniq v.
        uniq d.
        trivial.
      + eapply names_unique_cons; eauto 2.
        apply name_noocc_add; trivial.
        eauto 2.
  Qed.  
  Hint Resolve add_unique.


  Lemma name_once_add_further_inv :
    forall v decls d,
      name_occ (add decls d) v = 1 ->
      name_of_decl d = v
      \/ (name_of_decl d <> v /\ name_occ decls v = 1).
  Proof.
    induction decls.
    + sauto.
    + intros *.
      simpl.
      destruct name_dec; eauto.
      - destruct (name_dec (name_of_decl d) v); eauto 4.
      - intros H.
        apply name_once_further_inv in H as [(Hav,H0)|(?,?)].
        * edestruct name_noocc_add_inv; eauto 4.
        * edestruct IHdecls as [?|(?,?)]; eauto 2.
          eauto 6.
  Qed.


  Lemma add_unique_further :
    forall d decls,
      names_unique (add decls d) -> names_unique decls.
  Proof.
    induction decls.
    - auto.
    - simpl.
      edestruct name_dec.
      + clear IHdecls.
        intros.
        intro v.
        uniq v.
        uniq d.
        trivial.
      + intros.
        eapply names_unique_cons; eauto 2.
        eapply names_unique_zero in H; eauto 1.
  Qed.  
  Hint Immediate add_unique_further.
  End Lemmas.
  
  
  (** All hints from the module to be imported without importing the whole module *)
  Module Hints.
    Hint Immediate name_once_noocc_tail.
    Hint Immediate name_once_further_neq.
    Hint Resolve name_once_cons_neq name_once_cons_eq.
    Hint Resolve name_once_In.
    Hint Resolve name_noocc_cons.
    Hint Resolve name_noocc_head.
    Hint Immediate name_noocc_further.
    Hint Resolve name_noocc_not_In.
    Hint Resolve not_In_name_noocc.
    Hint Resolve name_noocc_In_neq.
    Hint Resolve name_noocc_In_decl_neq.
    Hint Resolve names_unique_permute.
    Hint Immediate name_noocc_decompose_l name_noocc_decompose_r.
    Hint Resolve name_noocc_app.
    Hint Resolve name_once_In_unique.
    Hint Resolve names_unique_zero.
    Hint Resolve names_unique_cons.
    Hint Immediate names_unique_further.
    Hint Immediate names_unique_decompose_r names_unique_decompose_l.
    Hint Immediate name_noocc_recip.
    Hint Resolve names_unique_app.
    Hint Resolve find_In.
    Hint Resolve find_right.
    Hint Resolve in_map_find.
    Hint Resolve In_find_exists.
    Hint Resolve In_find.
    Hint Resolve find_app_l_some.
    Hint Rewrite @find_app_r.
    Hint Rewrite @find_app_r_noocc.
    Hint Rewrite @find_app_r_unique.
    Hint Resolve name_noocc_add.
    Hint Immediate name_noocc_add_further.
    Hint Resolve name_noocc_add_neq.
    Hint Resolve name_once_add.
    Hint Resolve In_add_In.
    Hint Resolve add_unique.
    Hint Immediate add_unique_further.
  End Hints.

  Lemma move_unique: forall (decl1 decl2:Type) (f : decl1 -> decl2) name_of_decl1 name_of_decl2 decls1,
      (forall d1, name_of_decl2 (f d1) = name_of_decl1 d1) ->
      names_unique name_of_decl1 decls1 <->
      names_unique name_of_decl2 (map f decls1).
  Proof.
    intros.
    split.
    + intros Hu v.
      unfold name_occ.
      rewrite map_map.
      erewrite map_ext; eauto 1.
    + intros Hum v.
      specialize (Hum v).
      unfold name_occ in Hum.
      rewrite map_map in Hum.
      erewrite map_ext in Hum; eauto 1.
  Qed.
  
End NameUniq.



Module Type Declaration.
  Include Name.
  Parameter decl : Type.
  Parameter name_of_decl : decl -> name.
End Declaration.


Module ListUniq(Import Inline X:Declaration).
  Module NU := X <+ NameUniq.

  Import NU.
  
  Definition t := list decl.
  Definition names_unique := names_unique name_of_decl.
  Definition name_occ := name_occ name_of_decl.
  Definition name_xi := name_xi name_of_decl.
  Definition find := find name_of_decl.
  Definition add := add name_of_decl.
  
  (* this part is generated automatically from the above using...
     cat ThisFile.v | 
     perl -ne 'print if /^ *Section Declarations/ .. /^ *End Lemmas./' | 
     perl -ne 'print if /^ *Lemma/ .. /^ *Proof/' | 
     perl -00 -p -e "s/(Lemma *([^ :]*?) *:.*?Proof)./\1. exact (\2 name_of_decl). Qed.\n/sg" > toimport.v
  
  Beginning of the imported part:
  *)

  Lemma name_occ_nil : forall v, name_occ [] v = 0. 
  Proof. exact (name_occ_nil name_of_decl). Qed.

  Lemma name_occ_singl : forall d v,
      name_occ [d] v = name_xi d v.
  Proof. exact (name_occ_singl name_of_decl). Qed.

  Lemma name_occ_app : forall decls1 decls2 v,
      name_occ (decls1 ++ decls2) v = name_occ decls1 v + name_occ decls2 v.
  Proof. exact (name_occ_app name_of_decl). Qed.

  Lemma name_occ_cons : forall d decls v,
      name_occ (d::decls) v = name_xi d v + name_occ decls v.
  Proof. exact (name_occ_cons name_of_decl). Qed.

  Lemma name_once_decl : forall d, name_xi d (name_of_decl d) = 1.
  Proof. exact (name_once_decl name_of_decl). Qed.

  Lemma name_xi_small : forall v d, name_xi d v <= 1.
  Proof. exact (name_xi_small name_of_decl). Qed.

  Lemma name_once : forall v d, name_of_decl d = v <-> name_xi d v = 1.
  Proof. exact (name_once name_of_decl). Qed.

  Lemma name_once_sym : forall v d, v = name_of_decl d <-> name_xi d v = 1.
  Proof. exact (name_once_sym name_of_decl). Qed.

  Lemma name_occ_In : forall v decls, In v (map name_of_decl decls) <-> name_occ decls v >= 1. 
  Proof. exact (name_occ_In name_of_decl). Qed.

  Lemma name_noocc_In : forall v decls, ~ In v (map name_of_decl decls) <-> name_occ decls v = 0. 
  Proof. exact (name_noocc_In name_of_decl). Qed.

  Lemma name_noocc : forall v d, name_of_decl d <> v <-> name_xi d v = 0.
  Proof. exact (name_noocc name_of_decl). Qed.

  Lemma name_noocc_sym : forall v d, v <> name_of_decl d  <-> name_xi d v = 0.
  Proof. exact (name_noocc_sym name_of_decl). Qed.

  Lemma name_occ_In_decl : forall d decls, In d decls -> name_occ decls (name_of_decl d) >= 1.
  Proof. exact (name_occ_In_decl name_of_decl). Qed.

  Lemma name_noocc_In_decl : forall d decls,
      ~ In d decls -> names_unique (d::decls) -> name_occ decls (name_of_decl d) = 0.
  Proof. exact (name_noocc_In_decl name_of_decl). Qed.

  Lemma name_noocc_In_decl_rev : forall d decls,
      name_occ decls (name_of_decl d) = 0 -> ~ In d decls.
  Proof. exact (name_noocc_In_decl_rev name_of_decl). Qed.

  Lemma name_eq_xi : forall d1 d2 v,
      name_of_decl d1 = name_of_decl d2 -> name_xi d1 v = name_xi d2 v.
  Proof. exact (name_eq_xi name_of_decl). Qed.

  Lemma name_eq_xi_rev : forall d1 d2,
      (forall v, name_xi d1 v = name_xi d2 v) -> name_of_decl d1 = name_of_decl d2.
  Proof. exact (name_eq_xi_rev name_of_decl). Qed.

  Lemma name_once_noocc_tail:
    forall decls v d,
      name_of_decl d = v -> 
      name_occ (d :: decls) v = 1 -> name_occ decls v = 0.
  Proof. exact (name_once_noocc_tail name_of_decl). Qed.

  Lemma name_once_further_neq:
    forall v v' d decls,
      v <> v' ->
      name_of_decl d = v ->
      name_occ (d :: decls) v' = 1 ->
      name_occ decls v' = 1.
  Proof. exact (name_once_further_neq name_of_decl). Qed.

  Lemma name_once_further_inv :
    forall v decls d,
      name_occ (d :: decls) v = 1 ->
      (name_of_decl d = v /\ name_occ decls v = 0)
      \/ (name_of_decl d <> v /\ name_occ decls v = 1).
  Proof. exact (name_once_further_inv name_of_decl). Qed.

  Lemma name_once_cons_neq:
    forall v v' d decls,
      v <> v' ->
      name_occ decls v = 1 ->
      name_of_decl d = v' ->
      name_occ (d :: decls) v = 1.
  Proof. exact (name_once_cons_neq name_of_decl). Qed.

  Lemma name_once_cons_eq:
    forall v decls d,
      name_occ decls v = 0 ->
      name_of_decl d = v -> 
      name_occ (d :: decls) v = 1.
  Proof. exact (name_once_cons_eq name_of_decl). Qed.

  Lemma name_once_In:
    forall decls v,
      name_occ decls v = 1 -> In v (map name_of_decl decls).
  Proof. exact (name_once_In name_of_decl). Qed.

  Lemma name_once_In_decl:
    forall decls v,
      name_occ decls v = 1 -> exists d, name_of_decl d = v /\ In d decls.
  Proof. exact (name_once_In_decl name_of_decl). Qed.

  Lemma name_noocc_cons :
    forall v decls d,
      name_occ decls v = 0 -> name_of_decl d <> v -> name_occ (d::decls) v = 0.
  Proof. exact (name_noocc_cons name_of_decl). Qed.

  Lemma name_noocc_cons_inv :
    forall v decls d,
      name_occ (d::decls) v = 0 -> name_of_decl d <> v /\ name_occ decls v = 0.
  Proof. exact (name_noocc_cons_inv name_of_decl). Qed.

  Lemma name_noocc_head :
    forall v decls d,
      name_occ (d::decls) v = 0 -> name_of_decl d <> v.
  Proof. exact (name_noocc_head name_of_decl). Qed.
  
  Lemma name_noocc_further :
    forall v decls d,
      name_occ (d::decls) v = 0 -> name_occ decls v = 0.
  Proof. exact (name_noocc_further name_of_decl). Qed.
  
  Lemma name_noocc_not_In:
    forall decls v,
      name_occ decls v = 0 ->
      ~ In v (map name_of_decl decls).
  Proof. exact (name_noocc_not_In name_of_decl). Qed.

  Lemma not_In_name_noocc:
    forall decls v,
      ~ In v (map name_of_decl decls) ->
      name_occ decls v = 0.
  Proof. exact (not_In_name_noocc name_of_decl). Qed.

  Lemma name_noocc_In_neq:
    forall decls v v',
      name_occ decls v = 0 ->
      In v' (map name_of_decl decls) ->
      v <> v'.
  Proof. exact (name_noocc_In_neq name_of_decl). Qed.

  Lemma name_noocc_In_decl_neq:
    forall decls d v,
      name_occ decls v = 0 ->
      In d decls ->
      name_of_decl d <> v.
  Proof. exact (name_noocc_In_decl_neq name_of_decl). Qed.

  Lemma name_noocc_decompose_l :
    forall decls1 decls2 v,
      name_occ (decls1 ++ decls2) v = 0 -> name_occ decls1 v = 0. 
  Proof. exact (name_noocc_decompose_l name_of_decl). Qed.

  Lemma name_noocc_decompose_r :
    forall decls1 decls2 v,
      name_occ (decls1 ++ decls2) v = 0 -> name_occ decls2 v = 0. 
  Proof. exact (name_noocc_decompose_r name_of_decl). Qed.

  Lemma name_noocc_app:
    forall decls1 decls2 v,
      name_occ decls1 v = 0 ->
      name_occ decls2 v = 0 ->
      name_occ (decls1 ++ decls2) v = 0.
  Proof. exact (name_noocc_app name_of_decl). Qed.

  Lemma name_once_In_unique:
    forall v d d' decls,
      name_occ decls v = 1 ->
      In d decls ->
      In d' decls ->
      name_of_decl d = v ->
      name_of_decl d' = v ->
      d = d'.
  Proof. exact (name_once_In_unique name_of_decl). Qed.

  Lemma names_unique_nil:
    names_unique [].
  Proof. exact (names_unique_nil name_of_decl). Qed.

  Lemma names_unique_zero:
    forall decls v d,
      name_of_decl d = v ->
      names_unique (d :: decls) ->
      name_occ decls v = 0.
  Proof. exact (names_unique_zero name_of_decl). Qed.

  Lemma names_unique_cons:
    forall decls v d,
      names_unique decls ->
      name_of_decl d = v ->
      name_occ decls v = 0 -> 
      names_unique (d :: decls).
  Proof. exact (names_unique_cons name_of_decl). Qed.

  Lemma names_unique_further:
    forall decls d,
      names_unique (d::decls) ->
      names_unique decls.
  Proof. exact (names_unique_further name_of_decl). Qed.

  Lemma names_unique_permute :
    forall d decls2a decls2b,
      names_unique (d :: decls2a ++ decls2b) -> 
      names_unique (decls2a ++ d :: decls2b).
  Proof. exact (names_unique_permute name_of_decl). Qed.

  Lemma names_unique_decompose_r:
    forall decls1 decls2,
      names_unique (decls1 ++ decls2) ->
      names_unique decls2.
  Proof. exact (names_unique_decompose_r name_of_decl). Qed.

  Lemma names_unique_decompose_l:
    forall decls1 decls2,
      names_unique (decls1 ++ decls2) ->
      names_unique decls1.
  Proof. exact (names_unique_decompose_l name_of_decl). Qed.

  Lemma name_noocc_recip :
    forall decls1 decls2,
      Forall (fun d => name_occ decls1 (name_of_decl d) = 0) decls2 ->
      Forall (fun d => name_occ decls2 (name_of_decl d) = 0) decls1.
  Proof. exact (name_noocc_recip name_of_decl). Qed.

  Lemma names_unique_app :
    forall decls1 decls2,
      names_unique decls1 ->
      names_unique decls2 ->
      Forall (fun d => name_occ decls1 (name_of_decl d) = 0) decls2 ->
      names_unique (decls1 ++ decls2).
  Proof. exact (names_unique_app name_of_decl). Qed.

  Lemma names_unique_In_unique:
    forall decls d d',
      names_unique decls ->
      In d decls ->
      In d' decls ->
      name_of_decl d = name_of_decl d' ->
      d = d'.
  Proof. exact (names_unique_In_unique name_of_decl). Qed.

  Lemma find_In : forall decls v d, find decls v = Some d -> In d decls.
  Proof. exact (find_In name_of_decl). Qed.

  Lemma find_right : forall decls v d, find decls v = Some d -> name_of_decl d = v.
  Proof. exact (find_right name_of_decl). Qed.

  Lemma In_find_weak : forall v d decls, In d decls -> name_of_decl d = v -> find decls v = None -> False.
  Proof. exact (In_find_weak name_of_decl). Qed.

  Lemma in_map_find:
  forall x decls,
    In x (map name_of_decl decls) -> exists d, find decls x = Some d.
  Proof. exact (in_map_find name_of_decl). Qed.

  Lemma In_find_exists :
    forall decls v d,
      In d decls ->
      name_of_decl d = v ->
      exists d', find decls v = Some d' /\ name_of_decl d' = v.
  Proof. exact (In_find_exists name_of_decl). Qed.

  Lemma In_find :
    forall decls v d,
      names_unique decls ->
      In d decls ->
      name_of_decl d = v ->
      find decls v = Some d.
  Proof. exact (In_find name_of_decl). Qed.

  Lemma find_app_l_some :
    forall decls1 decls2 v d,
      find decls1 v = Some d ->
      find (decls1 ++ decls2) v = Some d.
  Proof. exact (find_app_l_some name_of_decl). Qed.

  Lemma find_app_r :
    forall decls1 decls2 v,
      find decls1 v = None ->
      find (decls1 ++ decls2) v = find decls2 v.
  Proof. exact (find_app_r name_of_decl). Qed.

  Lemma find_app_r_noocc :
    forall decls1 decls2 v,
      name_occ decls1 v = 0 ->
      find (decls1 ++ decls2) v = find decls2 v.
  Proof. exact (find_app_r_noocc name_of_decl). Qed.

  Lemma find_app_r_unique :
    forall decls1 decls2 v d,
      names_unique (decls1 ++ decls2) ->
      find decls2 v = Some d ->
      find (decls1 ++ decls2) v = Some d.
  Proof. exact (find_app_r_unique name_of_decl). Qed.

  Lemma name_noocc_add :
    forall decls d v,
      name_occ decls v = 0 -> name_of_decl d <> v -> name_occ (add decls d) v = 0.
  Proof. exact (name_noocc_add name_of_decl). Qed.

  Lemma name_noocc_add_inv :
    forall v decls d,
      name_occ (add decls d) v = 0 -> name_of_decl d <> v /\ name_occ decls v = 0.
  Proof. exact (name_noocc_add_inv name_of_decl). Qed.

  Lemma name_noocc_add_further :
    forall v decls d,
      name_occ (add decls d) v = 0 -> name_occ decls v = 0.
  Proof. exact (name_noocc_add_further name_of_decl). Qed.

  Lemma name_noocc_add_neq :
    forall v decls d,
      name_occ (add decls d) v = 0 -> name_of_decl d <> v.
  Proof. exact (name_noocc_add_neq name_of_decl). Qed.

  Lemma name_once_add :
    forall decls d v,
      name_occ decls v = 1 -> name_occ (add decls d) v = 1.
  Proof. exact (name_once_add name_of_decl). Qed.

  Lemma In_add_In :
    forall decls d v,
      In v (map name_of_decl decls) -> In v (map name_of_decl (add decls d)).
  Proof. exact (In_add_In name_of_decl). Qed.

  Lemma In_add_inv :
    forall v decls d,
      In v (map name_of_decl (add decls d)) -> name_of_decl d = v \/ In v (map name_of_decl decls).
  Proof. exact (In_add_inv name_of_decl). Qed.

  Lemma add_unique :
    forall decls d,
      names_unique decls -> names_unique (add decls d).
  Proof. exact (add_unique name_of_decl). Qed.

  Lemma name_once_add_further_inv :
    forall v decls d,
      name_occ (add decls d) v = 1 ->
      name_of_decl d = v
      \/ (name_of_decl d <> v /\ name_occ decls v = 1).
  Proof. exact (name_once_add_further_inv name_of_decl). Qed.

  Lemma add_unique_further :
    forall d decls,
      names_unique (add decls d) -> names_unique decls.
  Proof. exact (add_unique_further name_of_decl). Qed.


  
  Module Hints.
    Hint Immediate name_once_noocc_tail.
    Hint Immediate name_once_further_neq.
    Hint Resolve name_once_cons_neq name_once_cons_eq.
    Hint Resolve name_once_In.
    Hint Resolve name_noocc_cons.
    Hint Resolve name_noocc_head.
    Hint Immediate name_noocc_further.
    Hint Resolve name_noocc_not_In.
    Hint Resolve not_In_name_noocc.
    Hint Resolve name_noocc_In_neq.
    Hint Resolve name_noocc_In_decl_neq.
    Hint Resolve names_unique_permute.
    Hint Immediate name_noocc_decompose_l name_noocc_decompose_r.
    Hint Resolve name_noocc_app.
    Hint Resolve name_once_In_unique.
    Hint Resolve names_unique_zero.
    Hint Resolve names_unique_cons.
    Hint Immediate names_unique_further.
    Hint Immediate names_unique_decompose_r names_unique_decompose_l.
    Hint Immediate name_noocc_recip.
    Hint Resolve names_unique_app.
    Hint Resolve find_In.
    Hint Resolve find_right.
    Hint Resolve in_map_find.
    Hint Resolve In_find_exists.
    Hint Resolve In_find.
    Hint Resolve find_app_l_some.
    Hint Rewrite @find_app_r.
    Hint Rewrite @find_app_r_noocc.
    Hint Rewrite @find_app_r_unique.
    Hint Resolve name_noocc_add.
    Hint Immediate name_noocc_add_further.
    Hint Resolve name_noocc_add_neq.
    Hint Resolve name_once_add.
    Hint Resolve In_add_In.
    Hint Resolve add_unique.
    Hint Immediate add_unique_further.
  End Hints.

  Ltac uniq x := unfold names_unique, name_occ, name_xi, find, add in *; uniq_x name_of_decl x.
  Ltac case_xi := case_xi_fun name_of_decl.
  
  
End ListUniq.
