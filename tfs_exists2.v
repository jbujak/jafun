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
