(* ================================================================== *)
Section Logica_Proposicional.

Variables A B C:Prop.

Lemma ex21 : (A \/ B) \/ C -> A \/ (B\/C).
Proof.
  intros.
  destruct H.
  destruct H.
  left.
  apply H.
  right.
  left.
  apply H.
  right.
  right.
  apply H.
Qed.


Lemma ex22 : (B -> C) -> A \/ B -> A \/ C.
Proof.
  intros.
  destruct H0.
  -left.
  apply H0.
  -right.
  apply H.
  apply H0.
Qed.

Lemma ex23 : (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  intros.
  destruct H.
  destruct H.
  split.
  - apply H.
  - split.
  + apply H1.
  + apply H0.
Qed.

Lemma ex24 : A \/ (B /\ C) -> (A \/ B ) /\ (A \/ C).
Proof.
  intros.
  split.
  destruct H.
  - left.
  apply H.
  - destruct H.
  right.
  apply H.
  - destruct H.
  +left.
  apply H.
  +destruct H.
  right.
  apply H0.
Qed.

Lemma ex25 :(A /\ B) \/ (A /\ C) <-> A /\ (B \/ C).
Proof.
  red.
  split.
  intros.
  - split.
    + destruct H.
      * destruct H. assumption.
      * destruct H. assumption.
    + destruct H. destruct H.
      * left. assumption.
      * destruct H. right. assumption.
  - intro. destruct H. destruct H0.
    + left. split. assumption. assumption.
    + right. split. assumption. assumption.
Qed.

Lemma ex26 :(A \/ B) /\ (A \/ C) <-> A \/ (B /\ C).
Proof.
  red.
  split.
  -intros.
  destruct H.
  destruct H.
  left.
  apply H.
  destruct H0.
  left.
  apply H0.
  right.
  split.
  apply H.
  apply H0.
  -intros.
  destruct H.
  split.
  left.
  apply H.
  left.
  apply H.
  destruct H.
  split.
  right.
  apply H.
  right.
  apply H0.
Qed.

End Logica_Proposicional.

(* ================================================================== *)
Section Logica_de_primeira_ordem.

Variable X :Set.
Variable Y : Set.
Variable Z : Set.
Variable t :X. 
Variables Q P R : X -> Prop.
Variable P1 : Y*Z ->Prop.

Lemma ex31 : (exists x, P(x) /\ Q(x)) ->  (exists x, P(x)) /\ (exists x,Q(x)).
Proof.
  intros.
  destruct H.
  exists .
  - exists x.
  destruct H.
  apply H.
  -exists x.
  destruct H.
  apply H0.
Qed.

Lemma ex32 : (exists x, forall y, P1(x,y)) ->  (forall y,(exists x, P1(x,y))).
Proof.
  intros.
  destruct H.
  exists x.
  apply H.
Qed.

Lemma ex33 : (exists x, P(x)) -> (forall x, (forall y, P(x) -> Q(y))) -> (forall y, Q(y)).
Proof.
  intros.
  destruct H.
  firstorder.
Qed.

Lemma ex34 : (forall x, Q(x) -> R(x)) -> (exists x, P(x) /\ Q(x)) -> ( exists x, P(x) /\ R(x)) .
Proof.
  intros.
  destruct H0.
  exists x.
  split.
  destruct H0.
  - apply H0.
  - destruct H0.
  apply H;assumption.
Qed.

Lemma ex35 :(forall x, P(x) -> Q(x)) -> (exists x, P(x)) -> (exists y, Q(y)) .
Proof.
  intros.
  destruct H0.
  exists x.
  apply H. assumption.
Qed.

Lemma ex36 : (exists x, P(x)) \/ (exists x,Q(x)) <-> (exists x, P(x) \/ Q(x)).
Proof.
  red.
  split.
  intros.
  destruct H.
  - destruct H.
    exists x.
    left.
    apply H.
  - destruct H.
    exists x.
    right.
    apply H.
  -intros.
    elim H.
    intros.
    destruct H.
    destruct H0.
    +left. exists x. apply H0.
    +right. exists x. apply H0.
Qed.

End Logica_de_primeira_ordem.

(* ================================================================== *)
Section Logica_Clássica.

Variables A B C:Prop.
Variable X :Set.
Variables Q P R : X -> Prop.

Axiom pme : forall A:Prop, A \/ ~ A.

Lemma ex41 : ((A -> B)->A)->A.
Admitted.

Lemma ex42 : ~ ~A -> A.
Proof.
  unfold not.
  intros.
  elim (pme A).
  auto.
  intro.
  unfold not in H0.
  elim (H H0).
Qed.

Lemma ex43 : ~ (forall x, P(x)) -> (exists x, ~P(x)).
Proof.
  unfold not.
  intros.
  elim (pme A).
  - intros.
  destruct H.
Qed.


End Logica_Clássica.

