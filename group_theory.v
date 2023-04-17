Section One_a.
Variable P Q R: Prop.
Lemma L0: (P /\ Q -> R) -> (P-> (Q -> R)).
Proof.
intros.
apply H.
split.
assumption.
assumption.
Qed.
End One_a.
Section One_b.
Variable P Q R: Prop.
Hypothesis t: P \/ Q -> R.
Lemma L1: (P -> R) /\ (Q -> R).
split.
intro.
assert (P \/ Q).
left.
assumption.
apply t.
assumption.
intro.
assert (P \/ Q).
right.
assumption.
apply t.
assumption.
Qed.
End One_b.
Section Two_a.
Variable A : Set.
Variable P : A-> A-> Prop.
Lemma L2: (exists x, forall y, P x y) -> forall y, exists x, P x y.
intro.
intro.
elim H.
intro.
intro.
exists x.
apply H0.
Qed.
End Two_a.
Section Two_b.
Variable A: Set.
Variable P: A -> Prop.
Variable Q: A -> Prop.
Hypothesis t: forall x, P x -> Q x.
Lemma L3: (forall x, P x) -> forall x, Q x.
intro.
intro.
assert(P x -> Q x).
apply t.
apply H0.
apply H.
Qed.
End Two_b.
Section Three.
Variable G: Set.
Variable op: G ->  G -> G.
Infix "o" := op (at level 35, right associativity).
Axiom assoc : forall a b c: G, a o (b o c) = (a o b) o c.
Variable e: G.
Axiom unit_l: forall a : G, e o a = a.
Axiom unit_r: forall a : G, a o e = a.
Axiom inv_l: forall a : G, exists b : G, b o a = e.
Axiom inv_r: forall a : G, exists b : G, a o b = e.
Lemma multi_l:
  forall c a b : G, a = b -> c o a = c o b.
intro.
intro.
intro.
intro.
assert (c o b = c o b).
reflexivity.
rewrite H.
assumption.
Qed.
Lemma multi_r:
  forall c a b : G, a = b -> a o c = b o c.
intros.
rewrite H.
reflexivity.
Qed.
(*assert (b o c = b o c).
reflexivity.
rewrite H.
assumption.
Qed.*)
Lemma L4:
  forall a b c: G, ((a o b = a o c) -> b = c).
intro.
intro.
intro.
intro.
assert (b = e o b).
assert (e o b = b).
apply unit_l.
rewrite H0.
reflexivity.
rewrite H0.
assert (exists (a_inv : G), a_inv o a = e).
apply inv_l.
elim H1.
intro.
intro.
assert (e o b = (x o a) o b).
rewrite H2.
reflexivity.
assert ((x o a) o b = x o (a o b)).
assert (x o (a o b) = (x o a) o b).
apply assoc.
rewrite H4.
reflexivity.
assert (x o (a o b) = x o (a o c)).
rewrite H.
reflexivity.
assert (x o (a o c) = (x o a) o c).
apply assoc.
assert ((x o a) o c = e o c).
rewrite H2.
reflexivity.
assert (e o c = c).
apply unit_l.
rewrite H3.
rewrite H4.
rewrite H5.
rewrite H6.
rewrite H7.
rewrite H8.
reflexivity.
Qed.
