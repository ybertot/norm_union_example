Require Import Arith Ascii Program Psatz Wellfounded Lexicographic_Product
  Relation_Operators.

Inductive regex : Set :=
  | Empty   : regex
  | Epsilon : regex
  | Symbol  : ascii -> regex
  | Union   : regex -> regex -> regex
  | Concat  : regex -> regex -> regex
  | Star    : regex -> regex.

Lemma eq_regex_dec : forall u v : regex, {u = v} + {u <> v}.
Proof. decide equality; apply ascii_dec. Defined.

Fixpoint le_regex u v : bool :=
  match u, v with
  | Empty       , _            => true
  | _           , Empty        => false
  | Epsilon     , _            => true
  | _           , Epsilon      => false
  | Symbol a    , Symbol b     => nat_of_ascii a <=? nat_of_ascii b
  | Symbol _    , _            => true
  | _           , Symbol _     => false
  | Star u      , Star v       => le_regex u v
  | Star u      , _            => true
  | _           , Star v       => false
  | Union u1 u2 , Union v1 v2  => if eq_regex_dec u1 v1
                                  then le_regex u2 v2
                                  else le_regex u1 v1
  | Union _ _   , _            => true
  | _           , Union _ _    => false
  | Concat u1 u2, Concat v1 v2 => if eq_regex_dec u1 v1
                                  then le_regex u2 v2
                                  else le_regex u1 v1
  end.

Fixpoint size_regex u :=
  match u with
    Union u v => size_regex u + size_regex v + 1
  | _ => 0
  end.

Definition size_2regex (p : regex * regex) := 
  let (u, v) := p in
  size_regex u + size_regex v + 1.

Inductive abstract_regex_T :=
  aEmpty | aUnion (u v : regex) | aOther (u : regex).

Definition abstract_regex u :=
  match u with
  | Empty => aEmpty
  | Union u v => aUnion u v
  | any => aOther any
  end.

Lemma th1 p : size_regex (snd p) <= size_2regex p.
Proof.
destruct p; unfold size_2regex; simpl; lia.
Qed.

Lemma th2 p u v: 
  abstract_regex (fst p) = aUnion u v ->
  size_regex (Union u v) <= size_2regex p.
Proof.
destruct p as [p1 p2]; destruct p1; try (simpl; discriminate).
simpl; intros h; injection h; intros <- <-; lia.
Qed.

Definition order : regex * regex -> regex * regex -> Prop :=
  fun p1 p2 =>
  lexprod nat (fun _ =>  nat)
   lt (fun _ => lt)
   (existT _ (size_2regex p1) (size_regex (fst p1)))
   (existT _ (size_2regex p2) (size_regex (fst p2))).

Lemma th3 p u v :
  abstract_regex (fst p) = aUnion u v ->
  order (v, snd p) p.
Proof.
destruct p as [p1 p2]; destruct p1; try (simpl; discriminate).
simpl; intros h; injection h; intros <- <-; unfold order.
apply left_lex; simpl; lia.
Qed.

Lemma th4 p u v 
        (eq1 : abstract_regex (fst p) = aUnion u v)
        (h : order (v, snd p) p)
        (g : forall p', order p' p ->
                  {r : regex | size_regex r <= size_2regex p'}) :
  order (u, (proj1_sig (g (v, snd p) h))) p.
Proof.
revert h g.
destruct p as [p1 p2]; destruct p1; try (simpl; discriminate).
simpl; intros h g.
destruct (g (v, p2) h) as [w pw].
simpl in pw |- *.
simpl in eq1; injection eq1; intros -> ->.
unfold order; simpl.
apply le_lt_or_eq in pw; destruct pw as [wlt | weq].
  now apply left_lex; lia.
replace (size_regex u + size_regex w + 1) with
  (size_regex u + size_regex v + 1 + size_regex p2 + 1) by
  ring [weq].
apply right_lex; lia.
Qed.

Lemma th5 p u v 
       (eq1 : abstract_regex (fst p) = aUnion u v)
       (g :  forall p', order p' p -> 
          {r : regex | size_regex r <= size_2regex p'})
       h1 h2 :
  size_regex (proj1_sig (g (u, (proj1_sig (g (v, snd p) h1))) h2)) <=
   size_2regex p.
Proof.
destruct p as [p1 p2]; destruct p1; try (simpl; discriminate).
simpl in h1, h2 |- *.
destruct (g (v, p2) h1) as [w pw]; simpl in h2, pw |- *.
destruct (g (u, w) h2) as [w2 pw2]; simpl in pw2 |- *.
injection eq1; intros -> ->.
lia.
Qed.

Lemma other_case p u : abstract_regex p = aOther u -> p = u.
Proof.
destruct p; try (simpl; discriminate);
simpl; intros h; injection h; auto.
Qed.


Lemma th6 p u :
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aEmpty ->
  size_regex u <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl; intros h; apply other_case in h; rewrite <- h;
 lia.
Qed.
  
Lemma th7 p v w :
  abstract_regex (snd p) = aUnion v w ->
  size_regex (Union v w) <= size_2regex p.
Proof.
destruct p as [p1 p2]; destruct p2; try (simpl; discriminate).
simpl; intros h; injection h; intros -> ->; lia.
Qed.

Lemma th8 p u v w :
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aUnion v w ->
  size_regex (Union u (Union v w)) <= size_2regex p.
Proof.
destruct p as [p1 p2]; destruct p2; try(simpl; discriminate).
simpl; intros h1 h2; injection h2; intros -> ->.
apply other_case in h1; rewrite h1; lia.
Qed.

Lemma th9 p u v w :
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aUnion v w ->
  order (u, w) p.
Proof.
destruct p as [p1 p2]; destruct p2; try (simpl; discriminate).
simpl; intros h1 h2; injection h2; intros -> ->.
apply left_lex; simpl.
apply other_case in h1; rewrite h1; lia.
Qed.

Lemma th10 p u v w :
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aUnion v w ->
  forall g :  (forall p', order p' p -> 
                {r : regex | size_regex r <= size_2regex p'}),
    forall h : (order (u, w) p),
    size_regex (Union v (proj1_sig (g (u, w) h))) <=
      size_2regex p.
Proof.
destruct p as [p1 p2]; destruct p2; try (simpl; discriminate).
simpl; intros h1 h2; injection h2; intros -> -> g h.
destruct (g _ h) as [x px]; simpl in px |- *.
apply other_case in h1; rewrite h1; lia.
Qed.

Lemma th11 p u : 
  abstract_regex (fst p) = aOther u ->
  size_regex u <= size_2regex p.
Proof.
intros h; apply other_case in h; rewrite <- h.
destruct p; unfold size_2regex; simpl; lia.
Qed.

Lemma th12 p u v : 
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aOther v ->
  size_regex (Union u v) <= size_2regex p.
Proof.
intros h; apply other_case in h; rewrite <- h.
intros h2; apply other_case in h2; rewrite <- h2.
destruct p; unfold size_2regex; simpl; lia.
Qed.

Lemma th13 p u v : 
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aOther v ->
  size_regex (Union v u) <= size_2regex p.
Proof.
intros h; apply other_case in h; rewrite <- h.
intros h2; apply other_case in h2; rewrite <- h2.
destruct p; unfold size_2regex; simpl; lia.
Qed.

Definition norm_union_F : forall p : regex * regex,
   forall g : (forall p', order p' p -> 
                {r : regex | size_regex r <= size_2regex p'}), 
    {r : regex | size_regex r <= size_2regex p} :=
 fun p norm_union =>
   match abstract_regex (fst p) as a' 
   return (abstract_regex (fst p) = a' ->
          {r | size_regex r <= size_2regex p}) with
     aEmpty => fun eq1 => exist _ (snd p) (th1 p)
   | aUnion u v => fun eq1 =>
     match abstract_regex (snd p) as b' return
       (abstract_regex (snd p) = b' ->
          {r | size_regex r <= size_2regex p}) with
       aEmpty => fun eq2 => exist _ (Union u v) (th2 _ _ _ eq1)
     | _ =>
         fun eq2 => exist _ (proj1_sig 
             (norm_union (u, 
                 proj1_sig (norm_union (v, snd p) 
                 (th3 _ _ _ eq1)))
                 (th4 _ _ _ eq1 (th3 _ _ _ eq1) norm_union))) 
             (th5 _ _ _ eq1 norm_union (th3 _ _ _ eq1)
                 (th4 _ _ _ eq1 (th3 _ _ _ eq1) norm_union))
     end (refl_equal _)
   | aOther u =>
     fun eq1 =>
     match abstract_regex (snd p) as b'
       return (abstract_regex (snd p) = b' ->
              {r | size_regex r <= size_2regex p}) with
       aEmpty => fun eq2 => exist _ u (th6 _ _ eq1 eq2)
     | aUnion v w =>
       fun eq2 =>
       if eq_regex_dec u v then
          exist _ (Union v w) (th7 _ _ _ eq2)
       else if le_regex u v then
        exist _ (Union u (Union v w)) (th8 _ _ _ _ eq1 eq2)
       else exist _ (Union v (proj1_sig (norm_union (u, w)
               (th9 _ _ _ _ eq1 eq2)))) (th10 _ _ _ _ eq1 eq2 norm_union
                                          (th9 _ _ _ _ eq1 eq2))
     | aOther v =>
       fun eq2 =>
       if eq_regex_dec u v then
         exist _ u (th11 _ _ eq1)
       else if le_regex u v then
         exist _ (Union u v) (th12 _ _ _ eq1 eq2)
       else exist _ (Union v u) (th13 _ _ _ eq1 eq2)
     end (refl_equal _)
   end (refl_equal _).

Lemma well_founded_order : well_founded order.
Proof.
unfold order.
apply (wf_inverse_image (regex*regex) {x : nat & nat}
        (lexprod nat (fun _ => nat) lt (fun _ => lt))
        (fun p => (existT _ (size_2regex p) (size_regex (fst p))))).
apply wf_lexprod; intros; apply Nat.lt_wf_0.
Qed.

Definition norm_union_1 : forall p : regex*regex,
  {x | size_regex x <= size_2regex p} :=
  Fix well_founded_order (fun p => {x | size_regex x <= size_2regex p})
  norm_union_F.

Definition norm_union p := `(norm_union_1 p).
