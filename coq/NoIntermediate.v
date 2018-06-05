
Theorem no_intermediate: ~ exists p : Prop, ~ (p <-> True) /\ ~ (p <-> False).
Proof.
  unfold "~". intros H.
  inversion H.
  inversion H0.
  apply H2. unfold "<->".
  split.
  (* left *)
  intros. apply H1.
  split. (* left *)
         intros. exact I.
         (* right *)
         intros. exact H3.
  (* right *)
  intros.
  inversion H3.
Qed.