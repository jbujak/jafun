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
Require Export JaRedInvariants.
Open Scope list_scope.
Open Scope nat_scope.

From Hammer Require Import Reconstr.

Section JaChurch.

  Variable CC : JFProgram.

  Export Env.
  Transparent DerivableTFS.
  Transparent ConsistentTFR.


Definition typed_red :
  Heap * TypedFrameStack -> option (Heap * TypedFrameStack) :=
  fun '(h, tfs) => 
    match tfs with
      | [] => None
      | hd :: Cc =>
        match TFRfr hd with
        | (* newk *)
          Ctx[[JFNew mu C vs]]_None => 
          match list_map_opt loc_of_val vs with
          | None => None
          | Some locs => 
            match alloc_init CC h C locs with
            | None => None
            | Some (l0, h') =>
              let nhd := update_env_in_fr CC hd l0 (JFClass C,mu) in
              Some (h', (replace_fr_in_tfr (Ctx[[JFVal1 (JFVLoc l0)]]_ None) nhd) :: Cc)
            end
          end
        | (* letin *)
          Ctx[[ JFLet C x E1 E2 ]]_ None =>
          Some (h, (replace_fr_in_tfr
                    (Ctx _[ (JFCtxLet C x __ E2 ) _[[_ E1 _]]_ None ]_) hd) ::
                                                                            Cc)
        | (* letgo *)
          Ctx _[ (JFCtxLet C x _ E) _[[_ (JFVal1 (JFVLoc l)) _]]_ None ]_ =>
          Some (h, (replace_fr_in_tfr
                      (Ctx[[ substExpr (JFVar x) l E ]]_ None) hd) :: Cc)
        | (* ifeq/ifneq *)
          Ctx[[ JFIf (JFVLoc l1) (JFVLoc l2) E1 E2 ]]_ None =>
          if Loc_dec l1 l2
          then Some (h, (replace_fr_in_tfr (Ctx[[E1]]_ None) hd) :: Cc)
          else Some (h, (replace_fr_in_tfr (Ctx[[E2]]_ None) hd) :: Cc)
        | (* mthdnpe *)
          Ctx[[ (JFInvoke JFnull _ _) ]]_ None =>
          Some (h, (replace_fr_in_tfr (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode) hd) ::
                                                                            Cc)
        | (* mthd *)
          Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None =>
          let D0op := getClassName h n in
          match D0op with | None => None | Some D0 =>
          match getInvokeBody CC D0op n m vs h Ctx (FSofTFS Cc) with | None => None 
          | Some (h', []) => None
          | Some (h', bdy :: _) =>
          match find_class CC D0 with | None => None | Some cdecl =>
          match methodLookup CC D0 m with | None => None | Some mdecl =>
          match retTypM CC (JFClass D0) m with | None => None | Some acid =>
          let newTFR := 
            {| TFRcdecl := cdecl;
               TFRmdecl := mdecl;
               TFRXi := thrs_of_md mdecl;
               TFRGamma := loc2env CC D0  mdecl  (JFVLoc (JFLoc n) :: vs);
               TFRfr := bdy;
               TFRAcid := acid
            |} in
            Some (h', newTFR :: tfs)
          end end end end end
        | (* mthdret *)
          nil [[JFVal1 (JFVLoc l) ]]_ None =>
          match Cc with
          | invk :: Cc' =>
            match TFRfr invk with
            | Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None =>
              let dnameopt := getClassName h n in
              match dnameopt with
              | None => None
              | Some dname =>
                let acidopt := retTypM CC (JFClass dname) m in
                match acidopt with
                | None => None
                | Some (C,mu) =>
                  let invkenv := update_env_in_fr CC invk (JFLoc n) (C,mu) in
                  let invkfr := replace_fr_in_tfr
                                  (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ None)
                                  invkenv in
                  Some (h, invkfr :: Cc')
                end
              end
            | _ => None
            end
          | _ => None
          end 
      | (* assignnpe *)
        Ctx[[ (JFAssign (JFnull, id) (JFVLoc l)) ]]_ None =>
        Some (h, (replace_fr_in_tfr (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode) hd) ::
                                                                            Cc)
      | (* assignev *)
        Ctx[[ (JFAssign (JFVLoc (JFLoc n), x) (JFVLoc l)) ]]_ None =>
        let o := Heap.find n h
        in match o with
           | None => None
           | Some (ro, cid) =>
             let modo := (JFXIdMap.add x l ro, cid) in
             let h1 := Heap.add n modo h in
             Some (h1, (replace_fr_in_tfr
                          (Ctx[[ JFVal1 (JFVLoc l) ]]_ None )
                          hd) :: Cc)
           end
      | (* varnpe *)
        Ctx[[ (JFVal2 (JFnull, x)) ]]_ None => 
        Some (h, (replace_fr_in_tfr
                    (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode)
                    hd) :: Cc)
      | (* var *)
        Ctx[[ (JFVal2 (JFVLoc (JFLoc n), x)) ]]_ None =>
        let o := Heap.find n h
        in match o with
           | None => None
           | Some (ro, cname) =>
             let ol1 := JFXIdMap.find x ro in
             match ol1 with
             | None => None
             | Some l1 =>
               match (flds_overline CC (JFClass cname)) with
               | None => None
               | Some flds =>
                 match Flds.find flds x with
                 | None => None
                 | Some (JFFDecl phi D xn) =>
                   let mu := match phi with
                             | true =>
                               match Env.find (TFRGamma hd) (JFVLoc (JFLoc n)) with
                               | None => JFatm
                               | Some (_,(DD,mu')) => mu'
                               end
                             | false => JFatm
                             end in
                   let hdenv := update_env_in_fr CC hd l1 (D,mu) in
                   Some (h, (replace_fr_in_tfr
                               (Ctx[[ JFVal1 (JFVLoc l1) ]]_ None)
                               hdenv) :: Cc)
                 end
               end
             end
           end
      | (* thrownull *)
        Ctx[[ (JFThrow JFnull) ]]_ None =>
        Some (h, (replace_fr_in_tfr
                    (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode) hd) :: Cc)
      | (* throw *)
        Ctx[[ (JFThrow (JFVLoc (JFLoc n))) ]]_ None => 
        match class h n with
        | None => None
        | Some cname =>
          Some (h, (replace_fr_in_tfr
                      (Ctx[[ JFVal1 (JFVLoc (JFLoc n)) ]]_ (Some cname)) hd) :: Cc)
          end
      | (* ctchin *)
        Ctx[[ (JFTry E1 mu C x E2) ]]_ None =>
        Some (h, (replace_fr_in_tfr
                    (Ctx _[ (JFCtxTry __ mu C x E2)  _[[_ E1 _]]_ None ]_) hd) :: Cc)

      | (* ctchnrml *)
        Ctx _[ (JFCtxTry _ mu C x E2)  _[[_ JFVal1 (JFVLoc l) _]]_ None ]_ =>
        Some (h, (replace_fr_in_tfr
                    (Ctx[[ JFVal1 (JFVLoc l) ]]_ None) hd) :: Cc)
      | (* letex *)
        Ctx _[ (JFCtxLet C x _ E) _[[_ (JFVal1 (JFVLoc l)) _]]_ (Some C') ]_ =>
        Some (h, (replace_fr_in_tfr
                    (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C') ) hd) :: Cc)
      | (* methodex *)
        nil [[JFVal1 (JFVLoc l) ]]_ (Some C) =>
        match Cc with
        | [] => None
        | invk :: Cc' =>
          match TFRfr invk with
          | Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None =>
            match l with
            | null =>
              let invkfr := replace_fr_in_tfr
                                (Ctx[[ (JFVal1 JFnull) ]]_ (Some C))
                                invk in
                Some (h, invkfr :: Cc')
            | JFLoc _ =>
              match Env.find (TFRGamma hd) (JFVLoc l) with
              | None => None
              | Some (_,(D,mu)) =>
                let invkenv := update_env_in_fr CC invk l (D,mu) in 
                let invkfr := replace_fr_in_tfr
                                (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ (Some C))
                                invkenv in
                Some (h, invkfr :: Cc')
              end
            end
          | _ => None
          end
        end
      | (* ctchexnok/ctchexok *)
        Ctx _[ (JFCtxTry _ mu C x E2) _[[_ (JFVal1 (JFVLoc l)) _]]_ (Some C') ]_ =>
        if subtype_class_bool CC C' C
        then (* ctchexok *)
          let nhd := update_env_in_fr CC hd l (JFClass C,mu) in
          Some (h, (replace_fr_in_tfr (Ctx[[ substExpr (JFVar x) l E2 ]]_ None) nhd) :: Cc)
        else (* ctchexnok *)
          Some (h, (replace_fr_in_tfr (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C')) hd) :: Cc)
      | _ => None
      end
    end.


Definition typed_red2 :
  Heap * TypedFrameStack -> option (Heap * TypedFrameStack) :=
  fun '(h, tfs) => 
    match tfs with
      | [] => None
      | hd :: Cc =>
        match TFRfr hd with
        | (Ctx [[ E ]]_ Some C') => 
          match E with
          | JFVal1 (JFVLoc l) =>
            match Ctx with
            (* methodex TODO doublecheck *)
            | [] =>  
              match Cc with
              | [] => None
              | invk :: Cc' =>
                match TFRfr invk with
                | Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None =>
                  match l with
                  | null =>
                    let invkfr := replace_fr_in_tfr
                                    (Ctx[[ (JFVal1 JFnull) ]]_ (Some C'))
                                    invk in
                    Some (h, invkfr :: Cc')
                  | JFLoc _ =>
                    match Env.find (TFRGamma hd) (JFVLoc l) with
                    | None => None
                    | Some (_,(D,mu)) =>
                      let invkenv := update_env_in_fr CC invk l (D,mu) in
                      let invkfr := replace_fr_in_tfr
                                      (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ (Some C'))
                                      invkenv in
                      Some (h, invkfr :: Cc')
                    end
                  end
                | _ => None
                end
              end
            (* letex *)
            | JFCtxLet C x _ E2 :: Ctx => 
              Some (h, (replace_fr_in_tfr
                          (Ctx [[ JFVal1 (JFVLoc l) ]]_ (Some C') ) hd) :: Cc)
            (* ctchexnok/ctchexok TODO doublecheck *)
            | JFCtxTry _ mu C x E2 :: Ctx => 
              if subtype_class_bool CC C' C
              then (* ctchexok *)
                let nhd := update_env_in_fr CC hd l (JFClass C,mu) in
                Some (h, (replace_fr_in_tfr (Ctx[[ substExpr (JFVar x) l E2 ]]_ None) nhd) :: Cc)
              else (* ctchexnok *)
                Some (h, (replace_fr_in_tfr (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C')) hd) :: Cc)
            end
          | _ => None
          end
        | (Ctx [[E ]]_ None) =>
          match E with
          (* newk *)
          | JFNew mu C vs =>
            match list_map_opt loc_of_val vs with
            | None => None
            | Some locs => 
              match alloc_init CC h C locs with
              | None => None
              | Some (l0, h') =>
                let nhd := update_env_in_fr CC hd l0 (JFClass C,mu) in
                Some (h', (replace_fr_in_tfr (Ctx[[JFVal1 (JFVLoc l0)]]_ None) nhd) :: Cc)
              end
            end
          (* letin *)
          | JFLet C x E1 E2 =>
            Some (h, (replace_fr_in_tfr
                        (Ctx _[ (JFCtxLet C x __ E2 ) _[[_ E1 _]]_ None ]_) hd) ::
                                                                                Cc)
          (* ifeq/ifneq *)
          | JFIf (JFVLoc l1) (JFVLoc l2) E1 E2 =>
            Some (h, (replace_fr_in_tfr (Ctx[[if Loc_dec l1 l2 then E1 else E2]]_ None) hd) :: Cc)
          (* mthdnpe *)
          | JFInvoke JFnull _ _ =>
            Some (h, (replace_fr_in_tfr (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode) hd) ::
                                                                                Cc)
          (* mthd *)
          | JFInvoke (JFVLoc (JFLoc n)) m vs =>
            let D0op := getClassName h n in
            match D0op with
            | None => None
            | Some D0 =>
              match getInvokeBody CC D0op n m vs h Ctx (FSofTFS Cc) with
              | None => None
              | Some (h', []) => None
              | Some (h', bdy :: _) =>
                let cdecl0 := find_class CC D0 in
                let mdecl0 := methodLookup CC D0 m in
                let acid0 := retTypM CC (JFClass D0) m in
                match cdecl0 with
                | None => None
                | Some cdecl =>
                  match mdecl0 with
                  | None => None
                  | Some mdecl =>
                    match acid0 with
                    | None => None
                    | Some acid =>
                      let newTFR := 
                          {| TFRcdecl := cdecl;
                             TFRmdecl := mdecl;
                             TFRXi := thrs_of_md mdecl;
                             TFRGamma := loc2env CC D0  mdecl (JFVLoc (JFLoc n) :: vs);
                             TFRfr := bdy;
                             TFRAcid := acid
                          |} in
                      Some (h', newTFR :: tfs)
                    end
                  end
                end
              end
            end
          (* assignnpe *)
          | JFAssign (JFnull, id) (JFVLoc l) =>
            Some (h, (replace_fr_in_tfr (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode) hd) ::
                                                                                Cc)
          (* assignev  *)
          | JFAssign (JFVLoc (JFLoc n), x) (JFVLoc l) =>
            let o := Heap.find n h
            in match o with
               | None => None
               | Some (ro, cid) =>
                 let modo := (JFXIdMap.add x l ro, cid) in
                 let h1 := Heap.add n modo h in
                 Some (h1, (replace_fr_in_tfr
                              (Ctx[[ JFVal1 (JFVLoc l) ]]_ None )
                              hd) :: Cc)
               end

          | JFVal1 (JFVLoc l) =>
            match Ctx with
            (* mthdret *)
            | [] =>
              match Cc with
              | invk :: Cc' =>
                match TFRfr invk with
                | Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None =>
                  let dnameopt := getClassName h n in
                  match dnameopt with
                  | None => None
                  | Some dname =>
                    let acidopt := retTypM CC (JFClass dname) m in
                    match acidopt with
                    | None => None
                    | Some (C,mu) =>
                      let invkenv := update_env_in_fr CC invk (JFLoc n) (C,mu) in
                      let invkfr := replace_fr_in_tfr
                                      (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ None)
                                      invkenv in
                      Some (h, invkfr :: Cc')
                    end
                  end
                | _ => None
                end
              | _ => None
              end

            (* letgo *)
            | JFCtxLet C x _ E :: Ctx =>
              Some (h, (replace_fr_in_tfr
                          (Ctx[[ substExpr (JFVar x) l E ]]_ None) hd) :: Cc)

            (* ctchnrml *)
            | JFCtxTry _ mu C x E2 :: Ctx =>
              Some (h, (replace_fr_in_tfr
                          (Ctx[[ JFVal1 (JFVLoc l) ]]_ None) hd) :: Cc)
            end

          (* varnpe   *)
          |  JFVal2 (JFnull, x) => 
             Some (h, (replace_fr_in_tfr
                         (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode)
                         hd) :: Cc)
          (* var *)
          | JFVal2 (JFVLoc (JFLoc n), x) =>
            let o := Heap.find n h
            in match o with
               | None => None
               | Some (ro, cname) =>
                 let ol1 := JFXIdMap.find x ro in
                 match ol1 with
                 | None => None
                 | Some l1 =>
                   match (flds_overline CC (JFClass cname)) with
                   | None => None
                   | Some flds =>
                     match Flds.find flds x with
                     | None => None
                     | Some (JFFDecl phi D xn) =>
                       let mu := get_mu phi (TFRGamma hd) n in
                       let hdenv := update_env_in_fr CC hd l1 (D,mu) in
                       Some (h, (replace_fr_in_tfr
                                   (Ctx[[ JFVal1 (JFVLoc l1) ]]_ None)
                                   hdenv) :: Cc)
                     end
                   end
                 end
               end
          (* thrownull *)
          | JFThrow JFnull =>
            Some (h, (replace_fr_in_tfr
                        (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode) hd) :: Cc)
          (* throw *)
          | JFThrow (JFVLoc (JFLoc n)) => 
            match class h n with
            | Some cname =>
              Some (h, (replace_fr_in_tfr
                          (Ctx[[ JFVal1 (JFVLoc (JFLoc n)) ]]_ (Some cname)) hd) :: Cc)
            | None => None
          end
          (* ctchin *)
          | JFTry E1 mu C x E2 =>
            Some (h, (replace_fr_in_tfr
                        (Ctx _[ (JFCtxTry __ mu C x E2)  _[[_ E1 _]]_ None ]_) hd) :: Cc)

          | _ => None
          end
        end
    end.


Lemma tred1is2 : forall htfs res, typed_red htfs = res ->
                           typed_red2 htfs = res.
destruct htfs as [h d].
intro res.
intro TRed.
destruct d as [|tfr ?]; trivial.
destruct tfr.
destruct TFRfr.
destruct A.
+ simpl in TRed; simpl; repeat destr_discr TRed; simpl; trivial.
+ simpl in TRed; simpl; repeat destr_discr TRed; simpl; trivial.
Qed.

Lemma tred1eq2 : forall htfs, typed_red htfs = typed_red2 htfs.
intros.
symmetry.
now apply tred1is2.
Qed.

Lemma tred2is1 : forall htfs res, typed_red2 htfs = res ->
                             typed_red htfs = res.
intros.
now rewrite tred1eq2.
Qed.

Ltac apply_tred :=
  match goal with
  | [ OnDte : ((replace_fr_in_tfr _ _) :: _) = _
      |- context Ct [FSofTFS ?tfs]  ] => f_equal;
                                       f_equal;
                                       auto;
                                       try unfold replace_fr_in_tfr in OnDte; 
                                       try simpl in OnDte;
                                       try rewrite <- OnDte; 
                                       try simpl;
                                       auto
  end.
(**
   A well defined step in the Church version of the semantics implies a
   well defined step in the untyped version. Moreover, in both cases the
   resulting heaps agree and the type erasure of the resulting typed
   frame stack is the resulting untyped frame stack.

   Version developed non-systematically with natural formulation of
   reduction functions.
 *)

Theorem fs_from_tfs:
  forall h tfs h' tfs' res,
    typed_red (h, tfs) = Some (h',tfs') ->
    red CC (h, FSofTFS tfs) = res -> res = Some (h', FSofTFS tfs').
Proof. (*fs_from_tfs*)
  Load "fs_from_tfs.v".
Qed. (*fs_from_tfs*)

(**
   A well defined step in the Church version of the semantics implies a
   well defined step in the untyped version. Moreover, in both cases the
   resulting heaps agree and the type erasure of the resulting typed
   frame stack is the resulting untyped frame stack.

   Version developed non-systematically for versions of reduction functions
   with no internal redundancy.
 *)

Theorem fs_from_tfs2:
  forall h tfs h' tfs' res,
    typed_red2 (h, tfs) = Some (h',tfs') ->
    red2 CC (h, FSofTFS tfs) = res -> res = Some (h', FSofTFS tfs').
Proof. (*fs_from_tfs2*)
  Load "fs_from_tfs2.v".
Qed. (*fs_from_tfs2*)

(**
   A well defined step in the Church version of the semantics implies a
   well defined step in the untyped version. Moreover, in both cases the
   resulting heaps agree and the type erasure of the resulting typed
   frame stack is the resulting untyped frame stack.

   Version developed non-systematically for natural versions of reduction functions
   but using the version for functions with no internal redundancy.
 *)
Theorem fs_from_tfs':
  forall h tfs h' tfs',
    typed_red (h, tfs) = Some (h',tfs') ->
    red CC (h, FSofTFS tfs) = Some (h', FSofTFS tfs').
Proof.
  intros *.
  rewrite tred1eq2.
  rewrite red_eq_red2.
  eauto 2 using fs_from_tfs2.
Qed.


Ltac tred_congruence :=
  match goal with
      H: Some (?h, ?e) = Some (?h', ?e'), H1 : Some (?hh, ?ee) = ?res |- _ =>
      injection H; intros;
      try (is_var h; subst h);
      try (is_var e; subst e);
      try (is_var h'; subst h');
      try (is_var e'; subst e');
      try (is_var res; subst res);
      simpl;
      trivial
  | H: ?LS = Some (?h', ?e'), H1 : Some (?hh, ?ee) = ?res |- _ =>
    match LS with
    | let (XX,YY) := ?b in ?EE => destruct b eqn:?;
                                  tred_congruence
    end
  | H: ?LS = Some (?h', ?e'), H1 : ?LS1 = ?res |- _ =>
    match LS with
    | let (XX,YY) := ?b in ?EE =>
      match LS1 with
      | Some (?hh, ?ee) => destruct b; tred_congruence
      | let (XX1,YY1) := ?b1 in ?EE1 =>
        destruct b eqn:?;
        try destruct b1 eqn:?;
        tred_congruence
      end
    end
  end.

Ltac eval_match :=
  match goal with
  | H: (match ?E with _ => _ end) = ?res |- _ =>
    simpl in H;
    match goal with
    | H1: (match ?E1 with _ => _ end) = ?res |- _ =>
      constr_eq H H1;
      match goal with
      | H2 : ?E2 = ?E3 |- _ =>
         constr_eq E1 E2; rewrite H2 in H1
      | H2 : ?E2 = ?E3 |- _ =>
        constr_eq E1 E3; rewrite <- H2 in H1
      end
    end
  end.


(**
   A well defined step in the Church version of the semantics implies a
   well defined step in the untyped version. Moreover, in both cases the
   resulting heaps agree and the type erasure of the resulting typed
   frame stack is the resulting untyped frame stack.

   Version developed systematically for versions of reduction functions
   with no internal redundancy, the proof uses automatic destruction
   of matches only on the side of typed reduction.
 *)

Theorem fs_from_tfs3:
  forall h tfs h' tfs' res,
    typed_red2 (h, tfs) = Some (h',tfs') ->
    red2 CC (h, FSofTFS tfs) = res -> res = Some (h', FSofTFS tfs').
Proof. (*fs_from_tfs3*)
  Load "fs_from_tfs3.v".
Qed. (*fs_from_tfs3*)

(* a sequence of tactics used several times in a proof below *)

Local Ltac finish_tfs_for_fs :=
  eexists;
  split;
  [ etransitivity;
     [ symmetry; eassumption
     | f_equal; f_equal; congruence ]
  | simpl; congruence ].

(**
   A well defined step in the untyped version of the semantics 
   on a frame stack that is a type ereasure of a correct typed
   frame stack implies a well defined step in the Church version. 
   Moreover, in both cases the resulting heaps agree and the type
   erasure of the resulting typed frame stack is the resulting
   untyped frame stack.

   Version developed non-systematically with natural formulation of
   reduction functions.
 *)

Theorem tfs_exists:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists*)
  Load "tfs_exists.v".
Qed. (*tfs_exists*)




(**
   A well defined step in the untyped version of the semantics 
   on a frame stack that is a type ereasure of a correct typed
   frame stack implies a well defined step in the Church version. 
   Moreover, in both cases the resulting heaps agree and the type
   erasure of the resulting typed frame stack is the resulting
   untyped frame stack.

   Version developed non-systematically for the formulation of
   reduction functions with no internal duplication.
 *)

Theorem tfs_exists2:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists2*)
  Load "tfs_exists2.v".
Qed. (*tfs_exists2*)




(**
   A well defined step in the untyped version of the semantics 
   on a frame stack that is a type ereasure of a correct typed
   frame stack implies a well defined step in the Church version. 
   Moreover, in both cases the resulting heaps agree and the type
   erasure of the resulting typed frame stack is the resulting
   untyped frame stack.

   Version developed systematically with help of destruction
   tactic that highlights information on the current case.
 *)

Theorem tfs_exists3:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists3*)
  Load "tfs_exists3.v".
Qed. (*tfs_exists3*)



Ltac subst_some_p :=
  match goal with
      H: Some (?h, ?e) = Some ?p |- _ => rewrite <- H
  end.

Ltac red_tred_congr Red TRed Fgt h' fs' p :=
  try (injection Fgt;intros);
  try (injection Red;intros);
  (is_var h'; subst h');
  (is_var fs'; subst fs');
  (is_var p; eexists;
   rewrite <- TRed; split; [reflexivity| simpl;congruence]).


Ltac discriminate_tfrfr Fgt :=
  injection Fgt;intros; subst;
  first [congruence|
         match goal with
           Hr : TFRfr ?e = ?v,
                Hrr : TFRfr ?e = ?v1 |- _ =>
           rewrite Hr in Hrr; discriminate Hrr
         end].


Ltac finish_red :=
  match goal with
    HH: (FSofTFS _) = _ |- _ =>
    simpl in HH;
    match goal with
    | Fgt: ?a :: ?b :: ?c = ?a' :: ?b' :: ?c' |- _ =>
      subst;discriminate_tfrfr Fgt
    | Fgt: ?a :: ?b :: ?c = ?a' :: ?b' |- _ =>
      subst;discriminate_tfrfr Fgt
    | Fgt: (TFRfr ?a) :: (FSofTFS ?b) = ?a' :: ?b' |- _ =>
      subst;discriminate_tfrfr Fgt
    | Red: Some (?h, ?fs) = Some (?h', ?fs'),
           TRed: Some (?hh, ?fss) = Some ?p,
                 Fgt: ?a :: ?b :: ?c = ?a' :: ?b' :: ?c' |- _ =>
      subst;first [(red_tred_congr Red TRed Fgt h' fs' p) |
                   (discriminate_tfrfr Fgt)]
    | Red: Some (?h, ?fs) = Some (?h', ?fs'),
           TRed: Some (?hh, ?fss) = Some ?p,
                 Fgt: ?a :: ?b :: ?c = ?a' :: ?b' |- _ =>
      subst;first [(is_var b'; destruct b' eqn:?); red_tred_congr Red TRed Fgt h' fs' p |
             discriminate_tfrfr Fgt]
    | Red: Some (?h, ?fs) = Some (?h', ?fs'),
           TRed: Some (?hh, ?fss) = Some ?p,
                 Fgt: (TFRfr ?a) :: (FSofTFS ?b) = ?a' :: ?b' |- _ =>
      subst;first [red_tred_congr Red TRed Fgt h' fs' p|
             discriminate_tfrfr Fgt]
    | Red: Some (?h, ?fs) = Some (?h', ?fs'),
           TRed: Some (?hh, ?fss) = Some ?p,
                 Fgt: ?a :: ?b = ?cc |- _ =>
      (is_var cc);
      first [red_tred_congr Red TRed Fgt h' fs' p|
             discriminate_tfrfr Fgt]
    end
  end.


Ltac wffs_contradiction :=
  match goal with
    HH: (FSofTFS _) = _ |- _ =>
    simpl in HH;
    match goal with
    | Fgt: ?a :: ?b :: ?c = ?a' :: ?b' |- _ =>
      subst;simpl in Fgt;injection Fgt;intros;
      match goal with
      | p1 : TFRfr ?e0 = _, p2: TFRfr ?e0 = _ |- _ =>
        rewrite p1 in p2;injection p2;intros;
        match goal with
        | q1 : TFRfr ?ee0 = _, q2: TFRfr ?ee0 = _ |- _ =>
          rewrite q1 in q2;injection q2;intros
        end
      end; subst;
      match goal with
      |  Wffs : well_formed_framestack _ |- _ =>
         simpl in Wffs;  contradiction
      end
    | Fgt: ?a :: ?b :: ?c = ?a' |- _ =>
      (is_var a'); subst a';
      match goal with
      | [p1 : TFRfr ?e0 = _, p2 : TFRfr ?e1 = _   |- _] =>
        ((constr_eq e0 e1; fail 1) ||
                               rewrite p1 in *; rewrite p2 in *)
      end; subst;
         match goal with
         |  Wffs : well_formed_framestack _ |- _ =>
            simpl in Wffs;  contradiction
         end
     end
  end.

(**
   A well defined step in the untyped version of the semantics 
   on a frame stack that is a type ereasure of a correct typed
   frame stack implies a well defined step in the Church version. 
   Moreover, in both cases the resulting heaps agree and the type
   erasure of the resulting typed frame stack is the resulting
   untyped frame stack.

   Version developed systematically with automatic destruction
   of all matches using the destruction  tactic that highlights
   information on the current case.
 *)
Theorem tfs_exists4:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists4*)
  Load "tfs_exists4.v".
Qed. (*tfs_exists4*)


(**
   A well defined step in the untyped version of the semantics 
   on a frame stack that is a type ereasure of a correct typed
   frame stack implies a well defined step in the Church version. 
   Moreover, in both cases the resulting heaps agree and the type
   erasure of the resulting typed frame stack is the resulting
   untyped frame stack.

   Version developed systematically with automatic destruction
   of all matches on a well chosen match expression using the destruction 
   tactic that highlights information on the current case.
 *)
Theorem tfs_exists5:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists5*)
  Load "tfs_exists5.v".
Qed. (*tfs_exists5*)

End JaChurch.
