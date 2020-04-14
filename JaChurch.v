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

Theorem fs_from_tfs_after_tred:
  forall h tfs h' tfs' res,
    typed_red (h, tfs) = Some (h',tfs') ->
    red CC (h, FSofTFS tfs) = res -> res = Some (h', FSofTFS tfs').
Proof. (*fs_from_tfs_after_tred*)
  intros h tfs h' tfs' res TRed Red.
  destruct tfs as [|tfr ?].
  * unfold typed_red in *;
      discriminate TRed.
  * destruct tfr.
    destruct TFRfr.
    destruct Ctx.
        *** destruct E.
           + (* JFNew *)
             destruct A as [A|];simpl in TRed.
             ++
               discriminate TRed.
             ++
               simpl in Red.
               destruct (list_map_opt loc_of_val vs); try discriminate TRed.
               destruct (alloc_init CC h cn l); try discriminate TRed.
               destruct p.
               injection TRed; intros OnDte OnH;clear TRed.
               apply_tred.
               subst h0.
               now symmetry.
           + (* JFLet *)
             destruct A as [A|];simpl in TRed;
           [ try discriminate TRed |
             try (try (injection TRed; intros OnDte OnH;clear TRed);
                  try (simpl in Red; rewrite <- Red);
                  apply_tred)].
           + (* JFIf *)
             destruct A as [A|];simpl in TRed; destruct v1; destruct v2;
               try discriminate TRed.
             try (simpl in Red; rewrite <- Red).
             destruct (Loc_dec l l0);
                  try (injection TRed; intros OnDte OnH;clear TRed);
             apply_tred.
           + (* JFInvoke *)
             destruct A as [A|];simpl in TRed;destruct v; try destruct l;
               try discriminate TRed.
             (* only non exceptional case is left *)
             ++ (* method called on null *)
               injection TRed;intros OnDte OnH;clear TRed.
                try (simpl in Red; rewrite <- Red).
                apply_tred.
             ++ 
               try (simpl in Red; rewrite <- Red).
               unfold getInvokeBody in *.
               destruct (getClassName h n) in *; try discriminate TRed.
               destruct (methodLookup CC j m) in *; try discriminate TRed.
               destruct (substList (map JFVar (params_of_md j0)) vs
                                   (substExpr JFThis (JFLoc n) (body_of_md j0))) in *;
                 try discriminate TRed.
               destruct (find_class CC j) ; try discriminate TRed.
               injection TRed;intros OnDte OnH;clear TRed.
               rewrite <- OnDte.
               unfold FSofTFS; rewrite map_cons; rewrite map_cons;
                 fold (FSofTFS tfs).
               simpl.
               rewrite OnH. 
               auto.
           + (* JFassign *)
             destruct A as [A|];simpl in TRed;destruct vx;destruct j;
               try destruct l; try destruct v; try discriminate TRed.
             ++ try (try (injection TRed; intros OnDte OnH;clear TRed);
                     try (simpl in Red; rewrite <- Red)).
                     apply_tred.
             ++ try (simpl in Red; rewrite <- Red).
                destruct (Heap.find (elt:=Obj) n h);try discriminate TRed.
                destruct o.
                try (injection TRed; intros OnDte OnH;clear TRed).
                apply_tred.
           + (* JFVal1 *)
             destruct A as [A|].
             ++ simpl in TRed;
                  simpl in Red;try destruct tfs; try discriminate TRed;
                    destruct v; try discriminate TRed.
                (* simpl in FgtDte. *)
                destruct t0.
                destruct TFRfr.
                simpl in *.
                destruct E; try discriminate TRed.
                destruct v; try destruct l0; try discriminate TRed.
                destruct A0; try discriminate TRed.
                destruct l; [|
                             destruct (Env.find TFRGamma (JFVLoc (JFLoc n0))); try discriminate TRed;
                             destruct d;
                             destruct j0];
                injection TRed;intros OnH OnDte;
                  rewrite <- Red;
                  apply_tred.
             ++ simpl in TRed;
                  simpl in Red;
                  destruct tfs;
                  destruct v;
                  try discriminate TRed.
                destruct t0.
                simpl in *.
                destruct TFRfr.
                destruct E; try discriminate TRed.
                destruct v; try discriminate TRed.
                destruct l0; try discriminate TRed.
                destruct A; try discriminate TRed.
                destruct (getClassName h n); try discriminate TRed.
                destruct (methodLookup CC j m); try discriminate TRed.
                destruct (rettyp_of_md j0); try discriminate TRed.
                rewrite <- Red.
                injection TRed;intros OnH OnDte.
                apply_tred.
           + (* JFVal2 *)
             destruct A as [A|];simpl in TRed;destruct vx;destruct j;
               try destruct l; try discriminate TRed.
             ++ injection TRed; intros OnDte OnH;clear TRed.
                try (simpl in Red; rewrite <- Red).
                apply_tred.
             ++ simpl in Red.
                destruct (Heap.find (elt:=Obj) n h);inversion TRed.
                destruct o.
                destruct (JFXIdMap.find (elt:=Loc) j0 r);inversion TRed.
                destruct (flds_aux CC j (get_class_height CC j) []);
                  inversion TRed.
                destruct (Flds.find l0 j0);
                  inversion TRed;rewrite <- Red.
                destruct d;                         
                  injection TRed; intros OnDte OnH;clear TRed.
                unfold update_env_in_fr in OnDte.
                simpl in OnDte.
                apply_tred.
           + (* JFThrow *)
             try (simpl in Red; rewrite <- Red).
             destruct A as [A|];simpl in TRed; destruct v;
               try destruct l;
               try discriminate TRed.
             ++ injection TRed; intros OnDte OnH;clear TRed.
                apply_tred.
             ++ destruct (class h n);
                  try discriminate TRed;
                  injection TRed; intros OnDte OnH;clear TRed.
                apply_tred.
           + (* JFTry *)
             destruct A as [A|];simpl in TRed;
             [try discriminate TRed |
             try (try (injection TRed; intros OnDte OnH;clear TRed);
                  try (simpl in Red; rewrite <- Red);
                  apply_tred)].
        *** destruct E.
           + (* JFNew *)
             destruct A as [A|];simpl in TRed;destruct j;destruct Ctx0;
             try discriminate TRed. 
             ++ (* JFCtxLet *)
               try (injection TRed; intros OnDte OnH;clear TRed). 
                  try (simpl in Red; rewrite <- Red).
                  destruct (list_map_opt loc_of_val vs); try discriminate TRed.
                  destruct (alloc_init CC h cn l); try discriminate TRed.
                  destruct p.
                  injection TRed; intros OnDte OnH;clear TRed.
                  apply_tred.
             ++ (* JFCtxTry *)
               try (injection TRed; intros OnDte OnH;clear TRed). 
                try (simpl in Red; rewrite <- Red).
                  destruct (list_map_opt loc_of_val vs); try discriminate TRed.
                  destruct (alloc_init CC h cn l); try discriminate TRed.
                  destruct p.
                  injection TRed; intros OnDte OnH;clear TRed.
                  apply_tred.
           + (* JFLet *)
             destruct A as [A|];simpl in TRed;destruct j;destruct Ctx0;
               try discriminate TRed.
             ++ (* JFCtxLet *)
               try (injection TRed; intros OnDte OnH;clear TRed). 
               try (simpl in Red; rewrite <- Red).
               apply_tred.
             ++ (* JFCtxTry *)
               try (injection TRed; intros OnDte OnH;clear TRed). 
                try (simpl in Red; rewrite <- Red).
                 apply_tred.
           + (* JFIf *)
             try (simpl in Red; rewrite <- Red).
             simpl in TRed.
             destruct j;destruct Ctx0;try inversion TRed;
               destruct v1;try inversion TRed;
                 destruct v2;try inversion TRed;
                   destruct A; try inversion TRed;
                     destruct (Loc_dec l l0);
             try (
               try (injection TRed; intros OnDte OnH;clear TRed);
               apply_tred).
           + (* JFInvoke *)
             destruct A as [A|];simpl in TRed;destruct v; try destruct l;
               try destruct j; try destruct Ctx0;try discriminate TRed.
             (* only non exceptional case is left *)
             ++ (* method called on nonnull JFCtxLet *)
               injection TRed;intros OnDte OnH;clear TRed;
                try (simpl in Red; rewrite <- Red);
                apply_tred.
             ++ (* method called on nonnull JFCtxTry *)
               injection TRed;intros OnDte OnH;clear TRed;
                 try (simpl in Red; rewrite <- Red);
                 apply_tred.
             ++ (* method called on nonnull JFCtxLet *)
               try (simpl in Red; rewrite <- Red).
               unfold getInvokeBody in *.
               destruct (getClassName h n) in *; try discriminate TRed.
               destruct (methodLookup CC j m) in *; try discriminate TRed.
               destruct (substList (map JFVar (params_of_md j0)) vs
                                   (substExpr JFThis (JFLoc n) (body_of_md j0))) in *;
                 try discriminate TRed.
               destruct (find_class CC j) ; try discriminate TRed.
               injection TRed;intros OnDte OnH;clear TRed.
               rewrite <- OnDte.
               unfold FSofTFS; rewrite map_cons; rewrite map_cons;
                 fold (FSofTFS tfs).
               simpl.
               rewrite OnH.
               auto.
             ++ (* method called on nonnull JFCtxLet *)
               try (simpl in Red; rewrite <- Red).
               unfold getInvokeBody in *.
               destruct (getClassName h n) in *; try discriminate TRed.
               destruct (methodLookup CC j m) in *; try discriminate TRed.
               destruct (substList (map JFVar (params_of_md j0)) vs
                                   (substExpr JFThis (JFLoc n) (body_of_md j0))) in *;
                 try discriminate TRed.
               destruct (find_class CC j) ; try discriminate TRed.
               injection TRed;intros OnDte OnH;clear TRed.
               rewrite <- OnDte.
               unfold FSofTFS; rewrite map_cons; rewrite map_cons;
                 fold (FSofTFS tfs).
               simpl.
               rewrite OnH.
               auto.
           + (* JFAssign *)
             try (simpl in Red; rewrite <- Red).
             simpl in TRed.
             destruct j; destruct Ctx0;try inversion TRed;
               destruct vx;try inversion TRed;
                 destruct j;try inversion TRed;
                   destruct l; try inversion TRed;
                     destruct v; try inversion TRed;
                       destruct A; try inversion TRed.
             ++ try (injection TRed; intros OnDte OnH;clear TRed).
                apply_tred.
             ++ destruct (Heap.find (elt:=Obj) n h);
                  try destruct o; try inversion TRed.
                try (injection TRed; intros OnDte OnH;clear TRed).
                apply_tred.
             ++ try (injection TRed; intros OnDte OnH;clear TRed).
                apply_tred.
             ++ destruct (Heap.find (elt:=Obj) n h);
                  try destruct o; try inversion TRed.
                try (injection TRed; intros OnDte OnH;clear TRed).
                apply_tred.
           + (* JFVal1 *)
             try (simpl in Red; rewrite <- Red).
             simpl in TRed.
             destruct j; destruct Ctx0;try inversion TRed;
               destruct v;try inversion TRed;
                 destruct A; try inversion TRed.
             ++ apply_tred. 
             ++ apply_tred.
             ++ destruct (subtype_class_bool CC j C);
                  injection H2;intros OnDte OnH;
                    apply_tred.
             ++ apply_tred. 
           + (* JFVal2 *)
             try (simpl in Red; rewrite <- Red).
             simpl in TRed.
             destruct j;destruct Ctx0;destruct vx;
               destruct j; inversion TRed;
                 destruct l;destruct A; inversion TRed.
             ++ apply_tred.
             ++ destruct (Heap.find (elt:=Obj) n h);inversion TRed;
                  destruct o;
                  destruct (JFXIdMap.find (elt:=Loc) j0 r);inversion TRed.
                destruct (flds_aux CC j (get_class_height CC j) []);
                  try destruct (Flds.find l0 j0);inversion TRed.
                destruct d.
                try (injection H4; intros OnDte OnH;clear H4).
                apply_tred.
             ++ apply_tred.
             ++ destruct (Heap.find (elt:=Obj) n h);inversion TRed;
                  destruct o;
                  destruct (JFXIdMap.find (elt:=Loc) j0 r);inversion TRed.
                destruct (flds_aux CC j (get_class_height CC j) []);
                  try destruct (Flds.find l0 j0);inversion TRed.
                destruct d.
                try (injection H4; intros OnDte OnH;clear H4).
                apply_tred.
           + (* JFThrow *)
             try (simpl in Red; rewrite <- Red).
             simpl in TRed.
             destruct j; destruct Ctx0; destruct v;inversion TRed;
               destruct l; destruct A; inversion TRed;
                 try destruct (class h n); try inversion TRed; try apply_tred.
           + (* JFTry *)
             try (simpl in Red; rewrite <- Red).
             simpl in TRed.
             destruct j; destruct Ctx0; destruct A; inversion TRed.
             apply_tred.
             apply_tred.
Qed. (*fs_from_tfs_after_tred*)

(**
   A well defined step in the Church version of the semantics implies a
   well defined step in the untyped version. Moreover, in both cases the
   resulting heaps agree and the type erasure of the resulting typed
   frame stack is the resulting untyped frame stack.

   Version developed non-systematically for versions of reduction functions
   with no internal redundancy.
 *)

Theorem fs_from_tfs_after_tred2:
  forall h tfs h' tfs' res,
    typed_red2 (h, tfs) = Some (h',tfs') ->
    red2 CC (h, FSofTFS tfs) = res -> res = Some (h', FSofTFS tfs').
Proof. (*fs_from_tfs_after_tred2*)
  intros h tfs h' tfs' res TRed Red.
  destruct tfs as [|tfr ?].
  * discriminate TRed.
  * destruct tfr.
    destruct TFRfr.
    destruct A as [exn|].
        *** destruct E;unfold typed_red in TRed;
              try discriminate TRed.
            (* only JFVal1 is left *)
            simpl in TRed;
              simpl in Red; destruct v; try discriminate TRed.
            destruct Ctx;[ 
              destruct tfs as [|tfr0 ?];try discriminate TRed;
              simpl in Red;
              destruct (JaRedInvariants.TFRfr tfr0) eqn:tfrfre; try discriminate TRed;
              destruct E; try discriminate TRed;
              destruct v; try discriminate TRed;
              destruct l0; try discriminate TRed;
              destruct A; try discriminate TRed;
              try discriminate FgtDte;
              destruct l; [|
                           destruct (Env.find TFRGamma (JFVLoc (JFLoc n0))); try discriminate TRed;
                           destruct d;
                           destruct j0]|
              destruct j;[|destruct (subtype_class_bool CC exn C)]];
            injection TRed;intros OnDte OnH;
                 rewrite <- Red;
                 apply_tred.
        *** simpl in TRed; destruct E.
                + (* JFNew *)
                  simpl in Red.
                  destruct (list_map_opt loc_of_val vs); try discriminate TRed.
                  destruct (alloc_init CC h cn l); try discriminate TRed.
                  destruct p.
                  injection TRed; intros OnDte OnH;clear TRed.
                  apply_tred.
                  subst h0.
                  now symmetry.
                + (* JFLet *)
                  try (injection TRed; intros OnDte OnH;clear TRed);
                    try (simpl in Red; rewrite <- Red);
                    apply_tred.
                + (* JFIf *)
                  destruct v1; destruct v2;
                    try discriminate TRed.
                  try (simpl in Red; rewrite <- Red).
                  destruct (Loc_dec l l0);
                    try (injection TRed; intros OnDte OnH;clear TRed);
                    apply_tred.
                + (* JFInvoke *)
                  destruct v; try destruct l;
                    try discriminate TRed.
                  (* only non exceptional case is left *)
                  ++ (* method called on null *)
                    injection TRed;intros OnDte OnH;clear TRed.
                    try (simpl in Red; rewrite <- Red).
                    apply_tred.
                  ++ 
                    try (simpl in Red; rewrite <- Red).
                    unfold getInvokeBody in *.
                    destruct (getClassName h n) in *; try discriminate TRed.
                    destruct (methodLookup CC j m) in *; try discriminate TRed.
                    destruct (substList (map JFVar (params_of_md j0)) vs
                                        (substExpr JFThis (JFLoc n) (body_of_md j0))) in *;
                      try discriminate TRed.
                    destruct (find_class CC j) ; try discriminate TRed.
                    injection TRed;intros OnDte OnH;clear TRed.
                    rewrite <- OnDte.
                    unfold FSofTFS; rewrite map_cons; rewrite map_cons;
                      fold (FSofTFS tfs).
                    simpl.
                    rewrite OnH. 
                    auto.
                + (* JFassign *)
                  destruct vx;destruct j;
                    try destruct l; try destruct v; try discriminate TRed.
                  ++ try (try (injection TRed; intros OnDte OnH;clear TRed);
                          try (simpl in Red; rewrite <- Red)).
                     apply_tred.
                  ++ try (simpl in Red; rewrite <- Red).
                     destruct (Heap.find (elt:=Obj) n h);try discriminate TRed.
                     destruct o.
                     try (injection TRed; intros OnDte OnH;clear TRed).
                     apply_tred.
                + (* JFVal1 *)
                  destruct v;
                    try discriminate TRed.
                  destruct Ctx; [
                    destruct tfs as [| tfr0 ?];try discriminate TRed;
                    destruct (JaRedInvariants.TFRfr tfr0) eqn:tfrfr0; try discriminate TRed;
                    destruct E; try discriminate TRed;
                    destruct v; try discriminate TRed;
                    destruct l0; try discriminate TRed;
                    destruct A; try discriminate TRed;
                    destruct (getClassName h n); try discriminate TRed;
                    destruct (methodLookup CC j m); try discriminate TRed;
                    destruct (rettyp_of_md j0); try discriminate TRed|
                      destruct j];
                  rewrite <- Red;
                  simpl;
                  try rewrite tfrfr0;
                  injection TRed;intros OnH OnDte;
                    apply_tred.
           + (* JFVal2 *)
             destruct vx;destruct j;
               try destruct l; try discriminate TRed.
             ++ injection TRed; intros OnDte OnH;clear TRed.
                try (simpl in Red; rewrite <- Red).
                apply_tred.
             ++ simpl in Red.
                destruct (Heap.find (elt:=Obj) n h);inversion TRed.
                destruct o.
                destruct (JFXIdMap.find (elt:=Loc) j0 r);inversion TRed.
                destruct (flds_aux CC j (get_class_height CC j) []);
                  inversion TRed.
                destruct (Flds.find l0 j0);
                  inversion TRed;rewrite <- Red.
                destruct d;                         
                  injection TRed; intros OnDte OnH;clear TRed.
                unfold update_env_in_fr in OnDte.
                simpl in OnDte.
                apply_tred.
           + (* JFThrow *)
             try (simpl in Red; rewrite <- Red).
             destruct v;
               try destruct l;
               try discriminate TRed.
             ++ injection TRed; intros OnDte OnH;clear TRed.
                apply_tred.
             ++ destruct (class h n);
                  try discriminate TRed;
                  injection TRed; intros OnDte OnH;clear TRed.
                apply_tred.
           + (* JFTry *)
             injection TRed; intros OnDte OnH;clear TRed;
                  try (simpl in Red; rewrite <- Red);
                  apply_tred.
Qed. (*fs_from_tfs_after_tred2*)

(**
   A well defined step in the Church version of the semantics implies a
   well defined step in the untyped version. Moreover, in both cases the
   resulting heaps agree and the type erasure of the resulting typed
   frame stack is the resulting untyped frame stack.

   Version developed non-systematically for natural versions of reduction functions
   but using the version for functions with no internal redundancy.
 *)
Theorem fs_from_tfs_after_tred':
  forall h tfs h' tfs',
    typed_red (h, tfs) = Some (h',tfs') ->
    red CC (h, FSofTFS tfs) = Some (h', FSofTFS tfs').
Proof.
  intros *.
  rewrite tred1eq2.
  rewrite red_eq_red2.
  eauto 2 using fs_from_tfs_after_tred2.
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

Theorem fs_from_tfs_after_tred3:
  forall h tfs h' tfs' res,
    typed_red2 (h, tfs) = Some (h',tfs') ->
    red2 CC (h, FSofTFS tfs) = res -> res = Some (h', FSofTFS tfs').
Proof. (*fs_from_tfs_after_tred3*)
  intros h tfs h' tfs' res TRed Red.
  unfold typed_red2 in TRed.
  destr_discr_info TRed.
  unfold red2 in Red.
  destr_discr_info Red.
  * subst res.
    simpl in prev0.
    discriminate prev0.
  * simpl in prev0.
    injection prev0;intros;clear prev0.
    subst f f0.
    repeat (destr_discr_info TRed;try discriminate TRed; try tred_congruence);
      try (eval_match;tred_congruence). 
    eapply getInvokeBody_Some_Invoke in prev6.
    decompose_ex prev6.
    decompose_and prev6.
    injection H;intros.
    subst h' hd1 l1.
    rewrite  prev0.
    auto.
Qed. (*fs_from_tfs_after_tred3*)

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

Theorem tfs_exists_for_fs_after_red:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists_for_fs_after_red*)
  intros tfs h h' fs' tfsres WfP Tch Dtfs Red TRed.
  destruct tfsres.
  * (* Some from typed_red *)
    destruct tfs as [|tfr ?].
    ** simpl in Red.
       discriminate Red.
    ** destruct tfr.
       simpl FSofTFS in *.
       destruct TFRfr.
       destruct A.
       *** (* A=Some j *)
         destruct Ctx; destruct E; simpl in Red; auto_destr_discr Red.
         **** destruct tfs as [|tfr ?]; try discriminate Red.
              simpl FSofTFS in *.
              simpl in Red.
              destruct tfr.
              simpl in Red.
              simpl in TRed.
              destruct l.
              + auto_destr_discr TRed.
                finish_tfs_for_fs.
              + auto_destr_discr TRed.
                destr_discr TRed.
                auto_destr_discr TRed.
     (* here starts one case where red really goes to Some...
     [] [[l]]_Some j :: Ctx [[JFInvoke]]_None :: _ *)
              (* exception propagates to method call *)
                finish_tfs_for_fs.
         **** simpl in TRed.
              (* exception propagates through let *)
              finish_tfs_for_fs.
              
         **** simpl in TRed.
              (* exception comes to try *)
              destr_discr TRed.

              *****
                (* exception handled here *)
                finish_tfs_for_fs.
              
              *****
                (* exception passes through (wrong) try *)
                finish_tfs_for_fs.

       ***  (* A=None *)
         Opaque alloc.
         Opaque Heap.find.
         simpl in Red; auto_destr_discr Red; simpl in TRed; try finish_tfs_for_fs.
         (* empty context *)
         **** (* alloc *)
           repeat destr_discr Red.
           finish_tfs_for_fs.
         **** (* if *)
           destr_discr Red; finish_tfs_for_fs.
         **** (* method call *)
           unfold getInvokeBody in *.
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* assign *)
           repeat destr_discr Red; finish_tfs_for_fs.
         **** (* method return *)
           destr_discr TRed.
           destruct t0.
           simpl in *.
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* lookup *)
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* throw *)
           destr_discr Red.
           finish_tfs_for_fs.

         (* non-empty context LetCtx *)
         **** (* alloc *)
           repeat destr_discr Red; repeat destr_discr TRed; finish_tfs_for_fs.
         **** (* if *)
           destr_discr TRed; finish_tfs_for_fs.
         **** (* method call *)
           unfold getInvokeBody in *.
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* assign *)
           repeat destr_discr Red.
           finish_tfs_for_fs.
         **** (* lookup *)
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* throw *)
           destr_discr Red.
           finish_tfs_for_fs.

         (* non-empty context TryCtx *)
         **** (* alloc *)
           repeat destr_discr Red; finish_tfs_for_fs.
         **** (* if *)
           destr_discr Red; finish_tfs_for_fs.
         **** (* method call *)
           unfold getInvokeBody in *.
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.          
         **** (* assign *)
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.          
         **** (* lookup *)
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.          
         **** (* throw *)
           destr_discr Red.
           finish_tfs_for_fs.
         
  * (* None from typed_red *)
    unfold typed_red in TRed.
    destruct tfs as [|tfr ?] .
    ** simpl FSofTFS in *.
       simpl in Red.
       discriminate Red.
    ** destruct tfr.
      destruct TFRfr.
      simpl FSofTFS in *.
      simpl in Red.
      simpl in TRed.
      generalize Dtfs;intros Dtfs0.
      unfold DerivableTFS in Dtfs0.
      generalize Dtfs0;intros.
      destruct Dtfs0 as [IsTFS DerTFR].
      generalize DerTFR;intros.
      apply Forall_inv in DerTFR0.
      unfold DerivableTFR in DerTFR0.
      destruct DerTFR0 as (Fcls & MthdLkp & TpsCtx).
      destruct A.
      *** (* A = Some _ *) destruct TpsCtx.
          destruct H as [Eeq TpsCtx].
          subst E.
          unfold typesCtx in TpsCtx. 
          destruct Ctx.
          **** simpl in TpsCtx.
               destruct x; try discriminate Red; try discriminate TRed.
               destruct tfs as [| tfr ?].
               + simpl in Red;discriminate Red.
               + simpl in Red.
                 destruct (TFRfr tfr) eqn:tfrfre.
                 destruct E;try discriminate Red.
                 destruct A; try discriminate Red.
                 generalize Dtfs; intro Wffs.
                 apply DerivableTFS_wfs in Wffs.
                 simpl in Wffs.
                 rewrite tfrfre in Wffs.
                 destruct v; try contradiction.
                 destruct l0;try contradiction.
                 generalize DerTFR;intros.
                 assert (Forall (DerivableTFR CC) (tfr::tfs)). {
                   clear -DerTFR0.
                   apply  Forall_forall.
                   intros.
                   eapply Forall_forall in DerTFR0; eauto 1.
                   eauto 2 using in_cons.
                 }
                 eapply Forall_inv in H.
                 destruct tfr.
                 simpl in H.
                 simpl in tfrfre.
                 subst TFRfr.
                 simpl in TRed.
                 destruct H as (Fcls1 & MthdLkp1 & TpsCtx1).
                 eapply typesCtx_typesCtxExt1 in TpsCtx1;eauto 2.
                 destruct TpsCtx1 as [Xi1 [Acid1]].
                 eapply typesCtxExt_types in H; eauto 2.
                 destruct Acid1.
                 destruct TFRAcid.
                 eapply inversion_Throw in TpsCtx;eauto 2.
                 destruct TpsCtx as [m' [C [D' [mu' [mname [cname [TpsVal [IsLeqIn TpsCtx]]]]]]]].
                 destruct l.
                 ++ (* l=null *)
                   discriminate TRed.
                 ++ (* l=non_null *)
                   eapply inversion_JFVal1_nonnull in TpsVal;eauto 2;try discriminate.
                   destruct TpsVal as [C'' [mu'' [LeqIsLs [Inn Tpsn0]]]].
                   eapply DerNU_first in Dtfs1.
                   eapply Env.In_find in Inn; eauto 2 using DerNU_first.
                   simpl in Inn.
                   rewrite Inn in TRed.
                   discriminate TRed.
          **** destruct j0.
               + destruct x;try discriminate Red; try discriminate TRed.
               + destruct x;try discriminate Red; try discriminate TRed.
                 destruct (subtype_class_bool CC j C); discriminate TRed.
      *** (* A = None *)
        eapply typesCtx_typesCtxExt1 in TpsCtx;eauto 2.
        destruct TpsCtx as [Xi1 [Acid1]].
        destruct Ctx.
        **** (* empty context *)
           destruct E; try discriminate Red;
           simpl in TRed;
           try discriminate TRed.
         + (* JFNew normal *)
           repeat destr_discr Red.
           finish_tfs_for_fs.
         + (* JFIf normal *) 
           destruct v1;destruct v2; try discriminate Red.
           destruct (Loc_dec l l0); discriminate TRed.
         + (* JFInvoke normal *)
           destruct v; try destruct l;
             try discriminate TRed;try discriminate Red.
           unfold getInvokeBody in *.
           unfold getClassName in *.
           unfold type_correct_heap in Tch.

           case_eq (Heap.find (elt:=Obj) n h);
             [intros o Hf|intros Hf;rewrite Hf in *];
             try discriminate Red.
           destruct o.
           rewrite Hf in *.
           destruct (methodLookup CC j m ); try discriminate Red.
           destruct (substList (map JFVar (params_of_md j0)) vs
                               (substExpr JFThis (JFLoc n) (body_of_md j0)));
             try discriminate Red.
           apply Tch in Hf.
           destruct Hf as [ [? Fcls'] ?].
           rewrite Fcls' in *.
           discriminate TRed.
         + (* JFAssign normal *)
           destruct vx; destruct j;try discriminate Red.
           destruct l;destruct v; try discriminate TRed;
             try discriminate Red.
           destruct (Heap.find (elt:=Obj) n h);try discriminate Red.
           destruct o;discriminate TRed.
         + (* JFVal1 normal *)
           auto_destr_discr Red.
           auto_destr_discr TRed.
           ++ simpl in Red.
              discriminate Red.
           ++ simpl in Red.
              destruct (TFRfr t0) eqn:Ecefreeq.
              auto_destr_discr Red.
              generalize Dtfs; intro Wffs.
              apply DerivableTFS_wfs in Wffs.
              destruct v eqn:veq; try destruct l0; try contradiction.
              +++ simpl in Wffs.
                  rewrite Ecefreeq in Wffs.
                  contradiction.
              +++ edestruct getClassName_forDTFS;
                    try eapply Ecefreeq; eauto 1.
                  simpl.
                  unfold DerivableTFS.
                  { split.
                    eauto 2 using ConsistentTFS_further.
                    eapply Forall_forall.
                    intros.
                    eapply Forall_forall.
                    eapply DerTFR.
                    eauto 2 using in_cons.
                  } 
                  rewrite H0 in *.
                  edestruct methodLookup_forDTFS;
                    try eapply Ecefreeq; eauto 1.
                  rewrite H1 in *.
                  destruct (rettyp_of_md x0).
                  discriminate TRed.
              +++ simpl in Wffs.
                  rewrite Ecefreeq in Wffs.
                  contradiction.
         + (* JFVal2 normal *)
           destruct vx;try destruct j; try destruct l;try discriminate TRed;
             try discriminate Red.
           (* preparations *)
           apply Forall_inv in DerTFR.
           inversion DerTFR as (Fcls1 & MthdLkp1 & TpsCtx1).
           edestruct typesCtx_typesCtxExt in TpsCtx1; eauto 1.
           simpl in *.
           subst.
           apply typesCtxExt_types in H.
           apply Inversion_JFVal2 in H; eauto 2.
           destruct H as [C' [C'' [mu [mu' [fldlst [rep]]]]]].
           destruct H as [Tps [IsLS [Flds [InFlds [IsLS' [NIsLS
                                                            [TpsInd LeqIsLS]]]]]]].

           (* Heap reference is left *)
           destruct (Heap.find (elt:=Obj) n h) eqn:Hpfnd;
             try discriminate Red.
           destruct o as [oo C].
           generalize Hpfnd;intros.
           eapply find_field_in_subclass in Hpfnd0; eauto 2.
           ++ destruct Hpfnd0.
              rewrite H  in *.
              generalize Tch;intros.
              eapply type_correct_heap_find_class in Tch0; eauto 1.
              destruct Tch0.
              eapply find_class_flds_aux in H1; eauto 2.
              destruct H1.
              replace (get_class_height CC C + 0) with (get_class_height CC C) in H1 by auto with zarith.
              erewrite H1 in TRed.
              edestruct type_correct_heap_find_field;eauto 1.
              rewrite H2 in TRed;destruct x3;discriminate TRed.
           ++ eapply inversion_JFVal1_nonnull in Tps;eauto 2;try discriminate.
              destruct Tps as [C0 [mu0 [LeqIsLS0 [Inn Tps]]]].
              replace TFRGamma with (JaRedInvariants.TFRGamma {|
                                          TFRcdecl := TFRcdecl;
                                          TFRmdecl := TFRmdecl;
                                          TFRXi := TFRXi;
                                          TFRGamma := TFRGamma;
                                          TFRfr := [] [[JFVal2 (JFVLoc (JFLoc n), j0) ]]_ None;
                                          TFRAcid := TFRAcid |}) in Inn by (simpl;trivial).
              eapply ConsistentTFR_subtyping in Hpfnd;
                try eapply Inn;eauto 2 using DerivableTFS_ConsistentTFR.
              inversion LeqIsLS0.
              +++ injection H2;injection H3;intros;subst.
                  eapply subtrans;eauto 2.
              +++ injection H2;injection H3;intros;subst.
                  eapply subtrans;eauto 2.
         + (* JFThrow normal *)
           destruct v;try destruct l; try destruct  (class h n);
             try discriminate Red;try discriminate TRed.
         **** (* non-empty context *)
           destruct j.
           + destruct E;try discriminate TRed. 
             ++ destruct (list_map_opt loc_of_val vs); try discriminate Red; try discriminate TRed.
                destruct (alloc_init CC h cn l); try destruct p; try discriminate Red; try discriminate TRed.
             ++ destruct v1; try discriminate Red; try discriminate TRed.
                destruct v2; try discriminate Red.
                destruct (Loc_dec l l0); try discriminate TRed.
             ++ destruct v; try destruct l;
                  try discriminate TRed; try discriminate Red.
                rewrite Red in TRed.
                edestruct getClassName_forDTFS; simpl; eauto 1; simpl; eauto 1.
                rewrite H0 in TRed.
                edestruct getInvokeBody_Some; eauto 1.
                destruct H1 as [hd2 [fs'eq heq]].
                subst.
                unfold getInvokeBody in Red.
                destruct (getClassName h' n) in *; try discriminate Red.
                injection H0;intros.
                subst x0; clear H0.
                destruct (methodLookup CC j m) eqn:MthdLkpj in *;
                  try discriminate Red.
                edestruct methodLookup_find_class; try eapply MthdLkpj.
                rewrite H0 in TRed.
                discriminate TRed.
             ++ destruct vx;destruct j; try discriminate TRed; try discriminate Red.
                destruct l; try discriminate TRed; try discriminate Red.
                destruct v; try discriminate Red; try discriminate TRed.
                destruct v; try discriminate Red; try discriminate TRed.
                destruct (Heap.find (elt:=Obj) n h); try discriminate Red; try discriminate TRed.
                destruct o; try discriminate TRed.
             ++ destruct v; try discriminate Red; try discriminate TRed.
             ++ (* JFVal2 normal *)
               destruct vx;try destruct j; try destruct l;try discriminate TRed;
                 try discriminate Red.
               (* preparations *)
               apply Forall_inv in DerTFR.
               inversion DerTFR as (Fcls1 & MthdLkp1 & TpsCtx1).
               edestruct typesCtx_typesCtxExt in TpsCtx1; eauto 1.
               simpl in *.
               subst.
               apply typesCtxExt_types in H.
               apply Inversion_JFVal2 in H; eauto 2.
               destruct H as [C' [C'' [mu [mu' [fldlst [rep]]]]]].
               destruct H as [Tps [IsLS [Flds [InFlds [IsLS' [NIsLS
                                                            [TpsInd LeqIsLS]]]]]]].
               (* Heap reference is left *)
               destruct (Heap.find (elt:=Obj) n h) eqn:Hpfnd;
                 try discriminate Red.
               destruct o as [oo Ci].
               generalize Hpfnd;intros.
               eapply find_field_in_subclass in Hpfnd0; eauto 3.
               +++
                 destruct Hpfnd0.
                 rewrite H  in *.
                 generalize Tch;intros.
                 eapply type_correct_heap_find_class in Tch0; eauto 1.
                 destruct Tch0.
                 eapply find_class_flds_aux in H1; eauto 2.
                 destruct H1.
                 replace (get_class_height CC Ci + 0) with (get_class_height CC Ci) in H1
                   by auto with zarith.
                 erewrite H1 in TRed.
                 edestruct type_correct_heap_find_field; eauto 1.
                 rewrite H2 in TRed;destruct x4;discriminate TRed.
               +++
                 eapply inversion_JFVal1_nonnull in Tps;try congruence;eauto 2.
                 destruct Tps as [C''' [mu''' [LeqIsLSC'' [Inn Tps]]]].
                 inversion LeqIsLSC''.
                 ++++
                   injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping; eauto 2 using DerivableTFS_ConsistentTFR.
                 ++++  injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping; eauto 2 using DerivableTFS_ConsistentTFR.
             ++ destruct v; try discriminate Red.
                destruct l; try discriminate TRed.
                destruct (class h n);try discriminate Red;try discriminate TRed.
           + destruct E;try discriminate TRed. 
             ++
               destruct (list_map_opt loc_of_val vs);try discriminate TRed; try discriminate Red.
               destruct ( alloc_init CC h cn l);try discriminate TRed; try discriminate Red.
               destruct p;try discriminate TRed; try discriminate Red.
             ++
               destruct v1; try discriminate Red; try discriminate TRed.
               destruct v2; try discriminate Red.
               destruct (Loc_dec l l0); try discriminate TRed.
             ++ (* JFInvoke *)
               destruct v; try destruct l;
                 try discriminate TRed;try discriminate Red.
               edestruct getInvokeBody_Some_ClassName; eauto 1.
               rewrite H0 in TRed.
               rewrite <- H0 in TRed.
               rewrite Red in TRed.
               edestruct getInvokeBody_Some;eauto 1.
               destruct H1 as [x2 [fs'eq heq]].
               subst.
               edestruct getInvokeBody_Some_find_class. {
                 rewrite H0 in Red. eauto 1.
               }
               edestruct getInvokeBody_Some_methodLookup. {
                 rewrite H0 in Red. eauto 1.
               }
               rewrite H2 in TRed.
               rewrite H1 in TRed.
               discriminate TRed.
             ++
               destruct vx;destruct j; try discriminate TRed; try discriminate Red.
               destruct l; try discriminate TRed; try discriminate Red.
               destruct v; try discriminate Red; try discriminate TRed.
               destruct v; try discriminate Red; try discriminate TRed.
               destruct (Heap.find (elt:=Obj) n h); try discriminate Red; try discriminate TRed.
               destruct o; try discriminate TRed.
             ++
               destruct v; try discriminate Red; try discriminate TRed.
             ++ (* JFVal2 *)
               destruct vx;try destruct j; try destruct l;try discriminate TRed;
                 try discriminate Red.
               (* preparations *)
               apply Forall_inv in DerTFR.
               inversion DerTFR as (Fcls1 & MthdLkp1 & TpsCtx1).
               edestruct typesCtx_typesCtxExt in TpsCtx1; eauto 1.
               simpl in *.
               subst.
               apply typesCtxExt_types in H.
               apply Inversion_JFVal2 in H; eauto 2.
               destruct H as [C' [C'' [mu' [mu'' [fldlst [rep]]]]]].
               destruct H as [Tps [IsLS [Flds [InFlds [IsLS' [NIsLS
                                                            [TpsInd LeqIsLS]]]]]]].
               (* Heap reference is left *)
               destruct (Heap.find (elt:=Obj) n h) eqn:Hpfnd;
                 try discriminate Red.
               destruct o as [oo Ci].
               generalize Hpfnd;intros.
               eapply find_field_in_subclass in Hpfnd0; eauto 3.
               +++
                 destruct Hpfnd0.
                 rewrite H  in *.
                 generalize Tch;intros.
                 eapply type_correct_heap_find_class in Tch0; eauto 2.
                 destruct Tch0.
                 eapply find_class_flds_aux in H1;eauto 2.
                 destruct H1.
                 replace (get_class_height CC Ci + 0) with (get_class_height CC Ci) in H1 by auto with zarith.
                 erewrite H1 in TRed.
                 edestruct type_correct_heap_find_field;eauto 1.
                 rewrite H2 in TRed;destruct x4;discriminate TRed.
               +++
                 eapply inversion_JFVal1_nonnull in Tps;try congruence;eauto 2.
                 destruct Tps as [C''' [mu''' [LeqIsLSC'' [Inn Tps]]]].
                 inversion LeqIsLSC''.
                 ++++
                   injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping;eauto 2 using DerivableTFS_ConsistentTFR.
                 ++++
                   injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping;eauto 2 using DerivableTFS_ConsistentTFR.
             ++ destruct v; try discriminate Red; try discriminate TRed.
                destruct l; try discriminate TRed; try discriminate Red.
                destruct (class h n);try discriminate TRed; try discriminate Red.
Qed. (*tfs_exists_for_fs_after_red*)




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

Theorem tfs_exists_for_fs_after_red2:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists_for_fs_after_red2*)
  intros tfs h h' fs' tfsres WfP Tch Dtfs Red TRed.
  destruct tfsres.
  * (* Some from typed_red *)
    destruct tfs as [| tfr ?].
    ** simpl in Red.
       discriminate Red.
    ** destruct tfr.
       destruct TFRfr.
       destruct A.
       *** (* A=Some j *)
         destruct E; destruct Ctx;simpl in Red; auto_destr_discr Red.
         ****
           destruct tfs as [| tfr ?]; try discriminate Red.
           simpl FSofTFS in *.
           simpl in Red.
           destruct tfr.
           simpl in Red.
           simpl in TRed.
           destruct l.
           + auto_destr_discr TRed.
             finish_tfs_for_fs.
           + auto_destr_discr TRed.
             destr_discr TRed.
             auto_destr_discr TRed.
     (* here starts one case where red really goes to Some...
     [] [[l]]_Some j :: Ctx [[JFInvoke]]_None :: _ *)
              (* exception propagates to method call *)
                finish_tfs_for_fs.
         **** simpl in TRed.
              (* exception propagates through let *)
              finish_tfs_for_fs.
              
         **** simpl in TRed.
              (* exception comes to try *)
              destr_discr TRed.

              *****
                (* exception handled here *)
                finish_tfs_for_fs.
              
              *****
                (* exception passes through (wrong) try *)
                finish_tfs_for_fs.

       ***  (* A=None *)
         Opaque Heap.find.
         simpl in Red; auto_destr_discr Red; simpl in TRed; try finish_tfs_for_fs.
         (* empty context *)
         **** (* alloc *)
           repeat destr_discr Red.
           finish_tfs_for_fs.
         **** (* method call *)
           unfold getInvokeBody in *.
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* assign *)
           repeat destr_discr Red; finish_tfs_for_fs.
         **** (* method return *)
           destr_discr TRed.
           destruct t0.
           simpl in *.
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* lookup *)
           repeat destr_discr Red.
           repeat destr_discr TRed.
           finish_tfs_for_fs.
         **** (* throw *)
           destr_discr Red.
           finish_tfs_for_fs.
         
  * (* None from typed_red *)
    unfold typed_red2 in TRed.
    destruct tfs as [| tfr ?].
    **
      simpl in Red.
      discriminate Red.
    **
      destruct tfr.
      destruct TFRfr.
      simpl in Red.
      simpl in TRed.
      generalize Dtfs;intros.
      unfold DerivableTFS in Dtfs0.
      destruct Dtfs0 as [IsTFS DerTFR].
      generalize DerTFR;intros.
      apply Forall_inv in DerTFR0.
      unfold DerivableTFR in DerTFR0.
      destruct DerTFR0 as (Fcls & MthdLkp & TpsCtx).
      destruct A.
      *** (* A = Some _ *)
        destruct TpsCtx.
        destruct H as [Eeq TpsCtx].
        subst E.
        unfold typesCtx in TpsCtx. 
        destruct Ctx.
        ****
          simpl in TpsCtx.
          destruct x; try discriminate Red; try discriminate TRed.
          destruct tfs as [| tfr ?].
           + simpl in Red;discriminate Red.
           + simpl in Red.
             destruct (TFRfr tfr) eqn:tfrfre.
             destruct E;try discriminate Red.
             destruct A; try discriminate Red.
             generalize Dtfs; intro Wffs.
             apply DerivableTFS_wfs in Wffs.
             simpl in Wffs.
             rewrite tfrfre in Wffs.
             destruct v; try contradiction.
             destruct l0;try contradiction.
             generalize DerTFR;intros.
             assert (Forall (DerivableTFR CC) (tfr::tfs)). {
               clear -DerTFR0.
               apply  Forall_forall.
               intros.
               eapply Forall_forall in DerTFR0.
               eauto 1.
               eauto 2 using in_cons.
             }
             eapply Forall_inv in H.
             destruct tfr.
             simpl in H.
             simpl in tfrfre.
             subst TFRfr.
             simpl in TRed.
             destruct H as (Fcls1 & MthdLkp1 & TpsCtx1).
             eapply typesCtx_typesCtxExt1 in TpsCtx1;eauto 2.
             destruct TpsCtx1 as [Xi1 [Acid1]].
             eapply typesCtxExt_types in H; eauto 1.
             destruct Acid1.
             destruct TFRAcid.
             eapply inversion_Throw in TpsCtx; eauto 2.
             destruct TpsCtx as [m' [C [D' [mu' [mname [cname [TpsVal [IsLeqIn TpsCtx]]]]]]]].
             destruct l.
             ++ (* l=null *)
               discriminate TRed.
             ++ (* l=non_null *)
               eapply inversion_JFVal1_nonnull in TpsVal; eauto 2; try discriminate.
               destruct TpsVal as [C'' [mu'' [LeqIsLs [Inn Tpsn0]]]].
               eapply DerNU_first in Dtfs.
               eapply In_find in Inn; eauto 2. 
               simpl in Inn.
               rewrite Inn in TRed.
               discriminate TRed.
        ****
          destruct j0.
          + destruct x;try discriminate Red; try discriminate TRed.
          + destruct x;try discriminate Red; try discriminate TRed.
            destruct (subtype_class_bool CC j C); discriminate TRed.
      *** (* A = None *)
        eapply typesCtx_typesCtxExt1 in TpsCtx;eauto 2.
        destruct TpsCtx as [Xi1 [Acid1]].
        destruct Ctx.
        **** (* empty context *)
           destruct E; try discriminate Red;
           simpl in TRed;
           try discriminate TRed.
         + (* JFNew normal *)
           repeat destr_discr Red.
           finish_tfs_for_fs.
         + (* JFIf normal *) 
           destruct v1;destruct v2; try discriminate Red.
           destruct (Loc_dec l l0); discriminate TRed.
         + (* JFInvoke normal *)
           destruct v; try destruct l;
             try discriminate TRed;try discriminate Red.
           unfold getInvokeBody in *.
           unfold getClassName in *.
           unfold type_correct_heap in Tch.

           case_eq (Heap.find (elt:=Obj) n h);
             [intros o Hf|intros Hf;rewrite Hf in *];
             try discriminate Red.
           destruct o.
           rewrite Hf in *.
           destruct (methodLookup CC j m ); try discriminate Red.
           destruct (substList (map JFVar (params_of_md j0)) vs
                               (substExpr JFThis (JFLoc n) (body_of_md j0)));
             try discriminate Red.
           apply Tch in Hf.
           destruct Hf as [ [? Fcls'] ?].
           rewrite Fcls' in *.
           discriminate TRed.
         + (* JFAssign normal *)
           destruct vx; destruct j;try discriminate Red.
           destruct l;destruct v; try discriminate TRed;
             try discriminate Red.
           destruct (Heap.find (elt:=Obj) n h);try discriminate Red.
           destruct o;discriminate TRed.
         + (* JFVal1 normal *)
           auto_destr_discr Red.
           auto_destr_discr TRed.
           ++ simpl in Red.
              discriminate Red.
           ++ simpl in Red.
              destruct (TFRfr t0) eqn:TFRfreeq.
              auto_destr_discr Red.
              generalize Dtfs; intro Wffs.
              apply DerivableTFS_wfs in Wffs.
              destruct v eqn:veq; try destruct l0; try contradiction.
              +++ simpl in Wffs.
                  rewrite TFRfreeq in Wffs.
                  contradiction.
              +++ edestruct getClassName_forDTFS;
                    try eapply TFRfreeq; eauto 1.
                  { simpl.
                    unfold DerivableTFS.
                    split; eauto 2 using ConsistentTFS_further.
                    eapply Forall_forall.
                    intros.
                    eapply Forall_forall.
                    eapply DerTFR.
                    eauto 2 using in_cons.
                  } 
                  rewrite H0 in *.
                  edestruct methodLookup_forDTFS;
                    try eapply Ecefreeq; eauto 1.
                  rewrite H1 in *.
                  destruct (rettyp_of_md x0).
                  discriminate TRed.
              +++ simpl in Wffs.
                  rewrite TFRfreeq in Wffs.
                  contradiction.
         + (* JFVal2 normal *)
           destruct vx;try destruct j; try destruct l;try discriminate TRed;
             try discriminate Red.
           (* preparations *)
           apply Forall_inv in DerTFR.
           inversion DerTFR as (Fcls1 & MthdLkp1 & TpsCtx1).
           edestruct typesCtx_typesCtxExt in TpsCtx1; eauto 1.
           simpl in *.
           subst.
           apply typesCtxExt_types in H.
           apply Inversion_JFVal2 in H; eauto 2.
           destruct H as [C' [C'' [mu [mu' [fldlst [rep]]]]]].
           destruct H as [Tps [IsLS [Flds [InFlds [IsLS' [NIsLS
                                                            [TpsInd LeqIsLS]]]]]]].

           (* Heap reference is left *)
           destruct (Heap.find (elt:=Obj) n h) eqn:Hpfnd;
             try discriminate Red.
           destruct o as [oo C].
           generalize Hpfnd;intros.
           eapply find_field_in_subclass in Hpfnd0; eauto 3.
           ++
             destruct Hpfnd0.
             rewrite H  in *.
             generalize Tch;intros.
             eapply type_correct_heap_find_class in Tch0; eauto 1.
             destruct Tch0.
             eapply find_class_flds_aux in H1; eauto 2.
             destruct H1.
             replace (get_class_height CC C + 0) with (get_class_height CC C) in H1 by auto with zarith.
             erewrite H1 in TRed.
             edestruct type_correct_heap_find_field; eauto 2.
             rewrite H2 in TRed;destruct x3;discriminate TRed.
           ++ eapply inversion_JFVal1_nonnull in Tps;eauto 2;try discriminate.
              destruct Tps as [C0 [mu0 [LeqIsLS0 [Inn Tps]]]].
              replace TFRGamma with (JaRedInvariants.TFRGamma {|
                                          TFRcdecl := TFRcdecl;
                                          TFRmdecl := TFRmdecl;
                                          TFRXi := TFRXi;
                                          TFRGamma := TFRGamma;
                                          TFRfr := [] [[JFVal2 (JFVLoc (JFLoc n), j0) ]]_ None;
                                          TFRAcid := TFRAcid |}) in Inn by (simpl;trivial).
              eapply ConsistentTFR_subtyping in Hpfnd;
                try eapply Inn; eauto 2  using DerivableTFS_ConsistentTFR.
              inversion LeqIsLS0.
              +++ injection H2;injection H3;intros;subst.
                  eapply subtrans; eauto 2.
              +++ injection H2;injection H3;intros;subst.
                  eapply subtrans; eauto 2.
         + (* JFThrow normal *)
           destruct v;try destruct l; try destruct  (class h n);
             try discriminate Red;try discriminate TRed.
         **** (* non-empty context *)
           destruct j.
           + destruct E;try discriminate TRed. 
             ++ destruct (list_map_opt loc_of_val vs); try discriminate Red; try discriminate TRed.
                destruct (alloc_init CC h cn l); try destruct p; try discriminate Red; try discriminate TRed.
             ++ destruct v1; try discriminate Red; try discriminate TRed.
                destruct v2; try discriminate Red.
                destruct (Loc_dec l l0); try discriminate TRed.
             ++ destruct v; try destruct l;
                  try discriminate TRed; try discriminate Red.
                rewrite Red in TRed.
                edestruct getClassName_forDTFS; simpl; eauto 1;simpl;eauto 1.
                rewrite H0 in TRed.
                edestruct getInvokeBody_Some; eauto 1.
                destruct H1 as [hd2 [fs'eq heq]].
                subst.
                unfold getInvokeBody in Red.
                destruct (getClassName h' n) in *; try discriminate Red.
                injection H0;intros.
                subst x0; clear H0.
                destruct (methodLookup CC j m) eqn:MthdLkpj in *;
                  try discriminate Red.
                edestruct methodLookup_find_class; try eapply MthdLkpj.
                rewrite H0 in TRed.
                discriminate TRed.
             ++ destruct vx;destruct j; try discriminate TRed; try discriminate Red.
                destruct l; try discriminate TRed; try discriminate Red.
                destruct v; try discriminate Red; try discriminate TRed.
                destruct v; try discriminate Red; try discriminate TRed.
                destruct (Heap.find (elt:=Obj) n h); try discriminate Red; try discriminate TRed.
                destruct o; try discriminate TRed.
             ++ destruct v; try discriminate Red; try discriminate TRed.
             ++ (* JFVal2 normal *)
               destruct vx;try destruct j; try destruct l;try discriminate TRed;
                 try discriminate Red.
               (* preparations *)
               apply Forall_inv in DerTFR.
               inversion DerTFR as (Fcls1 & MthdLkp1 & TpsCtx1).
               edestruct typesCtx_typesCtxExt in TpsCtx1; eauto 1.
               simpl in *.
               subst.
               apply typesCtxExt_types in H.
               apply Inversion_JFVal2 in H; eauto 2.
               destruct H as [C' [C'' [mu [mu' [fldlst [rep]]]]]].
               destruct H as [Tps [IsLS [Flds [InFlds [IsLS' [NIsLS
                                                            [TpsInd LeqIsLS]]]]]]].
               (* Heap reference is left *)
               destruct (Heap.find (elt:=Obj) n h) eqn:Hpfnd;
                 try discriminate Red.
               destruct o as [oo Ci].
               generalize Hpfnd;intros.
               eapply find_field_in_subclass in Hpfnd0; eauto 3.
               +++
                 destruct Hpfnd0.
                 rewrite H  in *.
                 generalize Tch;intros.
                 eapply type_correct_heap_find_class in Tch0; eauto 1.
                 destruct Tch0.
                 eapply find_class_flds_aux in H1; eauto 2.
                 destruct H1.
                 replace (get_class_height CC Ci + 0) with (get_class_height CC Ci) in H1 by
                     auto with zarith.
                 erewrite H1 in TRed.
                 edestruct type_correct_heap_find_field; eauto 2.
                 rewrite H2 in TRed; destruct x4; discriminate TRed.
               +++
                 eapply inversion_JFVal1_nonnull in Tps; try congruence; eauto 2.
                 destruct Tps as [C''' [mu''' [LeqIsLSC'' [Inn Tps]]]].
                 inversion LeqIsLSC''.
                 ++++
                   injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping; eauto 2  using DerivableTFS_ConsistentTFR.
                 ++++
                   injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping; eauto 2 using DerivableTFS_ConsistentTFR.
             ++ destruct v; try discriminate Red.
                destruct l; try discriminate TRed.
                destruct (class h n);try discriminate Red;try discriminate TRed.
           + destruct E;try discriminate TRed. 
             ++ destruct (list_map_opt loc_of_val vs);try discriminate TRed; try discriminate Red.
                destruct ( alloc_init CC h cn l);try discriminate TRed; try discriminate Red.
                destruct p;try discriminate TRed; try discriminate Red.
             ++  destruct v1; try discriminate Red; try discriminate TRed.
                 destruct v2; try discriminate Red.
                 destruct (Loc_dec l l0); try discriminate TRed.
             ++ (* JFInvoke *)
               destruct v; try destruct l;
                 try discriminate TRed;try discriminate Red.
               edestruct getInvokeBody_Some_ClassName; eauto 1.
               rewrite H0 in TRed.
               rewrite <- H0 in TRed.
               rewrite Red in TRed.
               edestruct getInvokeBody_Some;eauto 1.
               destruct H1 as [x2 [fs'eq heq]].
               subst.
               edestruct getInvokeBody_Some_find_class. {
                 rewrite H0 in Red. eauto 1.
               }
               edestruct getInvokeBody_Some_methodLookup. {
                 rewrite H0 in Red. eauto 1.
               }
               rewrite H2 in TRed.
               rewrite H1 in TRed.
               discriminate TRed.
             ++ destruct vx;destruct j; try discriminate TRed; try discriminate Red.
                destruct l; try discriminate TRed; try discriminate Red.
                destruct v; try discriminate Red; try discriminate TRed.
                destruct v; try discriminate Red; try discriminate TRed.
                destruct (Heap.find (elt:=Obj) n h); try discriminate Red; try discriminate TRed.
                destruct o; try discriminate TRed.
             ++ destruct v; try discriminate Red; try discriminate TRed.
             ++ (* JFVal2 *)
               destruct vx;try destruct j; try destruct l;try discriminate TRed;
                 try discriminate Red.
               (* preparations *)
               apply Forall_inv in DerTFR.
               inversion DerTFR as (Fcls1 & MthdLkp1 & TpsCtx1).
               edestruct typesCtx_typesCtxExt in TpsCtx1; eauto 1.
               simpl in *.
               subst.
               apply typesCtxExt_types in H.
               apply Inversion_JFVal2 in H; try eauto 2.
               destruct H as [C' [C'' [mu' [mu'' [fldlst [rep]]]]]].
               destruct H as [Tps [IsLS [Flds [InFlds [IsLS' [NIsLS
                                                            [TpsInd LeqIsLS]]]]]]].
               (* Heap reference is left *)
               destruct (Heap.find (elt:=Obj) n h) eqn:Hpfnd;
                 try discriminate Red.
               destruct o as [oo Ci].
               generalize Hpfnd;intros.
               eapply find_field_in_subclass in Hpfnd0; eauto 3.
               +++
                 destruct Hpfnd0.
                 rewrite H  in *.
                 generalize Tch;intros.
                 eapply type_correct_heap_find_class in Tch0; eauto 2.
                 destruct Tch0.
                 eapply find_class_flds_aux in H1; eauto 2.
                 destruct H1.
                 replace (get_class_height CC Ci + 0) with (get_class_height CC Ci) in H1
                   by auto with zarith.
                 erewrite H1 in TRed.
                 edestruct type_correct_heap_find_field; eauto 1.
                 rewrite H2 in TRed;destruct x4;discriminate TRed.
               +++
                 eapply inversion_JFVal1_nonnull in Tps;try congruence;eauto 2.
                 destruct Tps as [C''' [mu''' [LeqIsLSC'' [Inn Tps]]]].
                 inversion LeqIsLSC''.
                 ++++
                   injection H2;intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping; eauto 2  using DerivableTFS_ConsistentTFR.
                 ++++
                   injection H2; intros.
                   injection H3;intros.
                   subst.
                   eapply subtrans;try eapply H4;eauto 2.
                   eapply ConsistentTFR_subtyping; eauto 2  using DerivableTFS_ConsistentTFR.
             ++ destruct v; try discriminate Red; try discriminate TRed.
                destruct l; try discriminate TRed; try discriminate Red.
                destruct (class h n);try discriminate TRed; try discriminate Red.
Qed. (*tfs_exists_for_fs_after_red2*)




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

Theorem tfs_exists_for_fs_after_red3:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists_for_fs_after_red3*)
  intros tfs h h' fs' tfsres WfP Tch Dtfs Red TRed.
  destruct tfsres.
  * unfold red2 in Red.
    unfold typed_red2 in TRed.
    destr_discr_info TRed.
    destr_discr_info Red.
    injection prev0;intros.
    subst f0 f.
    destr_discr_info TRed.
    destr_discr_info TRed.
    ** destr_discr_info TRed.
       destr_discr_info TRed.
       destr_discr_info TRed.
       *** destr_discr_info TRed.
           simpl in Red.
           destr_discr_info TRed.
           destr_discr_info TRed.
           destr_discr_info TRed.
           destr_discr_info TRed; try discriminate TRed.
           destr_discr_info TRed; try discriminate TRed.
           destr_discr_info TRed.
           **** injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** destr_discr_info TRed; try discriminate TRed.
                destruct d13.
                destruct j1.
                injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
       *** destr_discr_info TRed.
           **** injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** unfold subtype_bool in TRed.
                destr_discr_info TRed.
                + injection Red;intros.
                  subst h' fs'.
                  eexists.
                  rewrite <- TRed.
                  eauto.
                + injection Red;intros.
                  subst h' fs'.
                  eexists.
                  rewrite <- TRed.
                  eauto.
    ** destr_discr_info TRed.
       *** destr_discr_info TRed.
           destr_discr_info TRed.
           destruct p0.
           injection Red;intros.
           subst h' fs'.
           eexists.
           rewrite <- TRed.
           eauto.
       *** injection Red;intros.
           subst h' fs'.
           eexists.
           rewrite <- TRed.
           eauto.
       *** destr_discr_info TRed.
           destr_discr_info TRed.
           injection Red;intros.
           subst h' fs'.
           eexists.
           rewrite <- TRed.
           eauto.
       *** destr_discr_info TRed; try discriminate TRed.
           destr_discr_info TRed.
           **** injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** destr_discr_info TRed.
                destr_discr_info TRed.
                destr_discr_info TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                split; eauto 1.
                simpl.
                eapply getInvokeBody_Some_Invoke in prev7.
                decompose_ex prev7.
                decompose_and prev7.
                rewrite prev1.
                injection H;intros.
                subst l1.
                auto.
       *** destr_discr_info TRed.
           destr_discr_info TRed.
           destr_discr_info TRed;try discriminate TRed.
           destr_discr_info TRed.
           **** injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed.
                injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
       *** destr_discr_info TRed; try discriminate TRed.
           destr_discr_info TRed.
           **** destr_discr_info TRed.
                simpl in Red.
                destr_discr_info TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed.
                injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** destr_discr_info TRed.
                + injection Red;intros.
                  subst h' fs'.
                  eexists.
                  rewrite <- TRed.
                  eauto.
                + injection Red;intros.
                  subst h' fs'.
                  eexists.
                  rewrite <- TRed.
                  eauto.
       *** destr_discr_info TRed.
           destr_discr_info TRed.
           destr_discr_info TRed; try discriminate TRed.
           **** injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed; try discriminate TRed.
                destr_discr_info TRed.
                injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
       *** destr_discr_info TRed.
           destr_discr_info TRed.
           **** injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
           **** destr_discr_info TRed.
                injection Red;intros.
                subst h' fs'.
                eexists.
                rewrite <- TRed.
                eauto.
       *** injection Red;intros.
           subst h' fs'.
           eexists.
           rewrite <- TRed.
           eauto.
  * unfold typed_red2 in TRed.
    unfold red2 in Red.
    destr_discr_info Red.
    destr_discr_info TRed.
    ** simpl in prev; congruence.
    ** simpl in prev.
       injection prev;intros.
       subst f f0.
       destr_discr_info Red.
       destr_discr_info Red.
       destr_discr_info Red; try discriminate Red.
       *** destr_discr_info Red; try discriminate Red.
           destr_discr_info Red.
           **** destr_discr_info TRed.
                + simpl in Red.
                  discriminate Red.
                + simpl in Red.
                  generalize Dtfs; intro Wffs.
                  apply DerivableTFS_wfs in Wffs.
                  destr_discr_info Red; try discriminate Red.
                  destr_discr_info Red; try discriminate Red.
                  destr_discr_info TRed; try discriminate TRed.
                  ++ destr_discr_info TRed; try discriminate TRed.
                     destr_discr_info Red; try discriminate Red.
                     +++ simpl in Wffs.
                         rewrite prev7 in Wffs.
                         contradiction.
                     +++ destr_discr_info Red; try discriminate Red.
                         destr_discr_info TRed.
                         destr_discr_info TRed.
                         ++++ destr_discr_info TRed.
                              destr_discr_info TRed.
                         ++++ eapply findAssoc_forDTFS_Val1 in Dtfs;eauto 2.
                              decompose_ex Dtfs.
                              erewrite prev13 in Dtfs.
                              discriminate Dtfs.
                  ++ destr_discr_info Red.
                     simpl in Wffs.
                     rewrite prev7 in Wffs.
                     contradiction.
           **** destr_discr_info TRed.
                unfold subtype_bool in TRed.
                destr_discr_info TRed.
       *** destr_discr_info Red.
           **** destr_discr_info Red; try discriminate Red.
                destr_discr_info Red; try discriminate Red.
                destr_discr_info Red.
                finish_tfs_for_fs.
           **** finish_tfs_for_fs.
           **** destr_discr_info Red; try discriminate Red.
                destr_discr_info Red; try discriminate Red.
                finish_tfs_for_fs.
           **** destr_discr_info Red.
                destr_discr_info Red.
                + finish_tfs_for_fs.
                + destr_discr_info TRed.
                  ++ destr_discr_info TRed.
                     +++ destr_discr_info TRed.
                         destr_discr_info TRed.
                         ++++ eapply getInvokeBody_Some in prev7.
                              decompose_ex prev7.
                              decompose_and prev7.
                              congruence.
                         ++++ destr_discr_info TRed.
                              - destr_discr_info TRed.
                                -- destr_discr_info TRed.
                                   eapply getInvokeBody_retTypM in prev7.
                                   decompose_ex prev7.
                                   congruence.
                                -- eapply getInvokeBody_Some_methodLookup in prev7.
                                   decompose_ex prev7.
                                   congruence.
                              - eapply getInvokeBody_Some_find_class in prev7.
                                decompose_ex prev7.
                                congruence.
                          +++ congruence.
                        ++ eapply getClassName_forDTFS in prev1; eauto.
                           decompose_ex prev1.
                           congruence.
           **** destr_discr_info Red.
                destr_discr_info Red.
                destr_discr_info Red.
                + destr_discr_info Red; try discriminate Red.
                  finish_tfs_for_fs.
                + destr_discr_info Red; try discriminate Red.
                  destr_discr_info Red; try discriminate Red.
                  destr_discr_info Red.
                  finish_tfs_for_fs.
           **** destr_discr_info Red.
                destr_discr_info TRed; try discriminate TRed.
                + destr_discr_info TRed.
                  ++ simpl in Red; discriminate Red.
                  ++ simpl in Red.
                     destr_discr_info Red; try discriminate Red.
                     destr_discr_info Red; try discriminate Red.
                     destr_discr_info Red; try discriminate Red.
                     generalize Dtfs; intro Wffs.
                     apply DerivableTFS_wfs in Wffs.
                     destr_discr_info TRed.
                     +++ destr_discr_info TRed.
                         ++++ unfold well_formed_framestack in Wffs.
                              simpl in Wffs.
                              rewrite prev7 in Wffs.
                              contradiction.
                         ++++ destr_discr_info TRed.
                              - destr_discr_info TRed.
                                destr_discr_info TRed.
                                simpl in prev13.
                                destr_discr_info prev13.
                                eapply methodLookup_forDTFS in prev7;eauto.
                                decompose_ex prev7.
                                congruence.
                              - eapply getClassName_forDTFS in prev7;eauto.
                                decompose_ex prev7.
                                erewrite prev12 in prev7.
                                congruence.
                     +++ simpl in Wffs.
                         rewrite prev7 in Wffs.
                         contradiction.
                + destr_discr_info TRed; try discriminate TRed.
            **** destr_discr_info Red.
                 destr_discr_info Red.
                 destr_discr_info Red.
                 + finish_tfs_for_fs.
                 + destr_discr_info Red; try discriminate Red.
                   destr_discr_info Red.
                   destr_discr_info Red; try discriminate Red.
                   destr_discr_info TRed.
                   ++ destr_discr_info TRed; try discriminate TRed.
                      +++ destr_discr_info TRed; try discriminate TRed.
                      +++ eapply type_correct_heap_find_field in prev10;eauto.
                          decompose_ex prev10.
                          congruence.
                   ++ eapply type_correct_heap_find_class in Tch;eauto.
                      decompose_ex Tch.
                      eapply find_class_flds_aux in Tch; eauto.
                      decompose_ex Tch.
                      simpl in prev10.
                      replace (get_class_height CC j1+0) with (get_class_height CC j1) in Tch by auto with zarith.
                      erewrite prev10 in Tch.
                      congruence.
           **** destr_discr_info TRed; try discriminate TRed.
                 + destr_discr_info TRed; try discriminate TRed.
                   destr_discr_info TRed; try discriminate TRed; try discriminate Red.
                 + discriminate Red.
           **** discriminate TRed.
Qed. (*tfs_exists_for_fs_after_red3*)



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
Theorem tfs_exists_for_fs_after_red4:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists_for_fs_after_red4*)
  intros tfs h h' fs' tfsres WfP Tch Dtfs Red TRed.
  apply DerivableTFS_wfs in Dtfs as Wffs.
  remember (FSofTFS tfs) as fs eqn:Fgt.
  symmetry in Fgt.
  destruct tfsres.
  * unfold red2 in Red.
    unfold typed_red2 in TRed.
    repeat (try destr_discr_info TRed;try discriminate TRed;
            try destr_discr_info Red; try discriminate Red); try finish_red.
     ** simpl in Fgt.
        injection Fgt;intros.
        rewrite prev1 in H0.
        injection H0;intros.
        subst.
        rewrite <- TRed.
        injection Red;intros.
        subst.
        eexists.
        split.
        *** f_equal; f_equal; congruence.
        *** simpl.
            congruence.
     ** simpl in Fgt.
        injection Fgt;intros.
        rewrite prev1 in H0.
        injection H0;intros.
        subst.
        destruct (Loc_dec l0 l2); red_tred_congr Red TRed Fgt h' fs' p.
     ** simpl in Fgt.
        injection Fgt;intros.
        rewrite prev1 in H0.
        injection H0;intros.
        subst.
        rewrite prev11 in Red.
        rewrite prev12 in Red.
        rewrite <- TRed.
        eexists.
        split.
        **** f_equal; f_equal; congruence.
        **** simpl.
             injection Red;intros.
             subst fs'.
             subst h'.
             eapply getInvokeBody_Some_Invoke in prev12.
             decompose_ex prev12.
             decompose_and prev12.
             injection H; intros.
             subst.
             congruence.
     ** simpl in Fgt.
        injection Fgt;intros.
        rewrite prev1 in H0.
        injection H0;intros.
        subst.
        rewrite prev15 in prev16;injection prev16;intros;subst.
        red_tred_congr Red TRed Fgt h' fs' p.
  * unfold red2 in Red.
    unfold typed_red2 in TRed.
    repeat (try destr_discr_info TRed;try discriminate TRed;
            try destr_discr_info Red; try discriminate Red;try discriminate Fgt);
      try finish_red; try wffs_contradiction; try discriminate_tfrfr Fgt.
    ** eapply findAssoc_forDTFS_Val1 in prev1;eauto.
       decompose_ex  prev1.
       congruence.
    ** simpl in Fgt;injection Fgt;intros.
       rewrite prev1 in H0.
       injection H0;intros.
       subst.
       rewrite prev11 in Red.
       generalize Red;intros.
       eapply getInvokeBody_Some in Red0.
       decompose_ex Red0.
       decompose_and Red0.
       subst fs'.
       rewrite prev12 in Red.
       congruence.
    ** eapply getInvokeBody_retTypM in prev12.
       decompose_ex prev12.
       congruence.
    ** eapply getInvokeBody_Some_methodLookup in prev12.
       decompose_ex prev12.
       congruence.
    ** eapply getInvokeBody_Some_find_class in prev12.
       decompose_ex prev12.
       congruence.
    ** eapply getClassName_forDTFS in prev1; eauto.  
       decompose_ex prev1.
       congruence.
    ** eapply methodLookup_forDTFS in prev13;eauto.
       decompose_ex prev13.
       simpl in prev22.
       rewrite prev13 in prev22.
       congruence.
    ** eapply getClassName_forDTFS in prev13;eauto.
       decompose_ex prev13.
       congruence.
    ** eapply type_correct_heap_find_field in Tch;eauto.
       decompose_ex Tch.
       congruence.
    ** simpl in prev19.
       eapply type_correct_heap_find_class in Tch;eauto.
       decompose_ex Tch.
       eapply find_class_flds_aux in Tch; eauto.
       decompose_ex Tch.
       replace (get_class_height CC j3+0) with (get_class_height CC j3) in Tch by auto with zarith.
       erewrite prev19 in Tch.
       congruence.
Qed. (*tfs_exists_for_fs_after_red4*)


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
Theorem tfs_exists_for_fs_after_red5:
  forall tfs h h' fs' tfsres,
    Well_formed_program CC ->
    type_correct_heap CC h ->
    DerivableTFS CC h tfs ->
    red2 CC (h, FSofTFS tfs) = Some (h',fs') ->
    typed_red2 (h, tfs) = tfsres ->
    exists tfs', tfsres = Some (h', tfs') /\ 
      FSofTFS tfs' = fs'.
Proof. (*tfs_exists_for_fs_after_red5*)
  intros tfs h h' fs' tfsres WfP Tch Dtfs Red TRed.
  apply DerivableTFS_wfs in Dtfs as Wffs.
  remember (FSofTFS tfs) as fs eqn:Fgt.
  symmetry in Fgt.
  destruct tfsres.
  * unfold red2 in Red.
    unfold typed_red2 in TRed.
    repeat (try destr_discr_info TRed;try discriminate TRed);
      repeat (eval_match; simpl in Red); try finish_red.
    simpl in Fgt.
    subst fs.
    rewrite prev5 in Red.
    rewrite Red in prev6.
    injection prev6;intros.
    subst h0 fs'.
    rewrite <- TRed.
    eexists.
    split.
    ** f_equal; f_equal; congruence.
    ** simpl.
       eapply getInvokeBody_Some_Invoke in Red.
       decompose_ex Red.
       decompose_and Red.
       injection H;intros.
       congruence.
  * unfold red2 in Red.
    unfold typed_red2 in TRed.
    repeat (try destr_discr_info TRed;try discriminate TRed);
      repeat (eval_match; simpl in Red; try discriminate Red); try finish_red;

    try wffs_contradiction; try discriminate_tfrfr Fgt.


    ** eapply findAssoc_forDTFS_Val1 in prev0;eauto.
       decompose_ex  prev0.
       congruence.
    ** simpl in Fgt; subst fs.
       rewrite prev5 in Red.
       generalize Red;intros.
       eapply getInvokeBody_Some in Red0.
       decompose_ex Red0.
       decompose_and Red0.
       rewrite prev6 in Red.
       congruence.
    ** eapply getInvokeBody_retTypM in prev6.
       decompose_ex prev6.
       congruence.
    ** eapply getInvokeBody_Some_methodLookup in prev6.
       decompose_ex prev6.
       congruence.
    ** eapply getInvokeBody_Some_find_class in prev6.
       decompose_ex prev6.
       congruence.
    ** eapply getClassName_forDTFS in prev0; eauto.  
       decompose_ex prev0.
       congruence.
    ** eapply getClassName_forDTFS in prev0;eauto.
       decompose_ex prev0.
       congruence.
    **  eapply methodLookup_forDTFS in prev6;eauto 3.
       decompose_ex prev6.
       simpl in prev12.
       rewrite prev6 in prev12.
       congruence.
    ** eapply getClassName_forDTFS in prev6;eauto 3.
       decompose_ex prev6.
       congruence.
    ** eapply type_correct_heap_find_field in Tch;eauto.
       decompose_ex Tch.
       congruence.
    ** simpl in prev9.
       eapply type_correct_heap_find_class in Tch;eauto.
       decompose_ex Tch.
       eapply find_class_flds_aux in Tch; eauto.
       decompose_ex Tch.
       replace (get_class_height CC j1+0) with (get_class_height CC j1) in Tch by auto with zarith.
       erewrite prev9 in Tch.
       congruence.    
Qed. (*tfs_exists_for_fs_after_red5*)

End JaChurch.
