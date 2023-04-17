Section Group.
​
Parameter G : Set.
Parameter op : G -> G -> G.
Infix "o" := op (at level 35, right associativity).
Variable e : G.
Variable inv : G -> G.
Notation "a -" := (inv a) (at level 25, left associativity).
​
Axiom assoc : forall a b c : G, a o (b o c) = (a o b) o c.
Axiom unit_l : forall a : G, e o a = a.
Axiom unit_r : forall a : G, a o e = a.
Axiom inv_l : forall a : G, a- o a = e.
Axiom inv_r : forall a : G, a o a- = e.
​
Lemma elim_l:
  forall a b c, c o a = c o b -> a = b.
Proof.
intros.
rewrite <- unit_l.
rewrite <- unit_l with a.
elim (inv_l c).
rewrite <- assoc.
rewrite <- assoc.
rewrite H.
reflexivity.
Qed.
​
Lemma elim_r:
    forall a b c, a o c = b o c -> a = b.
Proof.
intros.
rewrite <- unit_r.
rewrite <- unit_r with a.
elim (inv_r c).
assert ((a o c) o c -= a o c o c -).
repeat rewrite assoc.
reflexivity.
rewrite <- H0.
rewrite H.
repeat rewrite assoc.
reflexivity.
Qed.
​
Lemma comm_aabb:
  (forall a b : G, a o b = b o a) ->
forall a b : G, a o a o b o b = a o b o a o b.
Proof.
intros.
assert(a o (b o a) o b = a o a o b o b).
assert (a o b = b o a).
apply H.
rewrite <-H0.
repeat rewrite assoc.
reflexivity.
rewrite <-H0.
repeat rewrite assoc.
reflexivity.
Qed.
​
Lemma aabb_comm:
  (forall a b : G, a o a o b o b = a o b o a o b) ->
forall a b : G, a o b = b o a.
Proof.
intros.
assert (a o b = e o a o b).
rewrite unit_l.
reflexivity.
assert(e o a o b = a - o a o a o b ).
assert (e = a- o a).
rewrite inv_l.
reflexivity.
rewrite H1.
​
repeat rewrite assoc.
reflexivity.
assert (a- o a o a o b = a- o a o a o b o e).
rewrite unit_r.
reflexivity.
assert (a- o a o a o b o e = a- o a o a o b o b o b-).
rewrite inv_r.
reflexivity.
assert (a- o a o a o b o b o b- = a- o (a o a o b o b) o b-).
repeat rewrite assoc.
reflexivity.
assert (a- o (a o a o b o b) o b- = a- o a o b o a o b o b-).
rewrite H.
repeat rewrite assoc.
reflexivity.
assert (a- o a o b o a o b o b- = (a- o a) o b o a o b o b-).
repeat rewrite assoc.
reflexivity.
assert ((a- o a) o b o a o b o b- = e o b o a o e).
rewrite inv_l.
rewrite inv_r.
reflexivity.
assert(e o b o a o e = b o a).
rewrite unit_r.
rewrite unit_l.
reflexivity.
rewrite H0.
rewrite H1.
rewrite H2.
rewrite H3.
rewrite H4.
rewrite H5.
rewrite H6.
rewrite H7.
rewrite H8.
reflexivity.
Qed.
