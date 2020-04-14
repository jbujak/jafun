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
