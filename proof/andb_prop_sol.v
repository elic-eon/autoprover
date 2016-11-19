Theorem andb_prop : forall n k, andb n k = true -> n = true /\ k = true.
Proof.
  intros.
  induction n.
  induction k.
  split.
  reflexivity.
  reflexivity.
  split.
  reflexivity.
  exact H.
  induction k.
  split.
  exact H.
  reflexivity.
  split.
  exact H.
  exact H.
Qed.
