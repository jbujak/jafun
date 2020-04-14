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
