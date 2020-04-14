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
