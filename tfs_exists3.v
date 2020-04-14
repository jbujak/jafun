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
