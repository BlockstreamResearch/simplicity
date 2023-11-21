Require Import VST.floyd.proofauto.

Lemma nonempty_writable0_glb (shw shr : share) : writable0_share shw -> readable_share shr ->
  nonempty_share (Share.glb shw shr).
Proof.
intros Hshw Hshr.
apply leq_join_sub in Hshw.
apply Share.ord_spec2 in Hshw.
rewrite Share.glb_commute, <- Hshw, Share.distrib1, Share.glb_commute, Share.lub_commute.
apply readable_nonidentity.
apply readable_share_lub.
apply readable_glb.
assumption.
Qed.

Lemma nonempty_writable_glb (shw shr : share) : writable_share shw -> readable_share shr ->
  nonempty_share (Share.glb shw shr).
Proof.
intros Hshw Hshr.
apply nonempty_writable0_glb; try assumption.
apply writable_writable0; assumption.
Qed.

(* From https://stackoverflow.com/a/77309345 *)
Lemma data_at_conflict_glb: forall {cs: compspecs} sh1 sh2 t v v' p,
  sepalg.nonidentity (Share.glb sh1 sh2) ->
  0 < sizeof t ->
  data_at sh1 t v p * data_at sh2 t v' p |-- FF.
Proof.
  intros.
  pose (sh := Share.glb sh1 sh2).
  assert (sepalg.join sh (Share.glb sh1 (Share.comp sh)) sh1). {
    hnf. 
    rewrite (Share.glb_commute sh1), <- Share.glb_assoc, Share.comp2.
     rewrite Share.glb_commute, Share.glb_bot.
     split; auto. 
     rewrite Share.distrib2, Share.comp1.
      rewrite Share.glb_commute, Share.glb_top.
      unfold sh. rewrite Share.lub_commute, Share.lub_absorb. auto.
   }
  assert (sepalg.join sh (Share.glb sh2 (Share.comp sh)) sh2). {
    hnf. rewrite (Share.glb_commute sh2), <- Share.glb_assoc, Share.comp2.
     rewrite Share.glb_commute, Share.glb_bot.
     split; auto. 
     rewrite Share.distrib2, Share.comp1.
      rewrite Share.glb_commute, Share.glb_top.
      unfold sh. rewrite Share.glb_commute.
     rewrite Share.lub_commute, Share.lub_absorb. auto.
   }
   rewrite <- (data_at_share_join _ _ _ _ _ _ H1).
   rewrite <- (data_at_share_join _ _ _ _ _ _ H2).
    sep_apply data_at_conflict; auto.
   entailer!.
Qed.