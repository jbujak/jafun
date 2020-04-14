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
