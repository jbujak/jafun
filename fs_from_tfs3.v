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
