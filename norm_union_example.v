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

Inductive arT (u : regex) : Type :=
  arE : u = Empty -> arT u
| arU : forall v w, u = Union v w -> arT u
| arO : u <> Empty -> (forall v w, u <> Union v w) -> arT u.

Definition ar u : arT u.
Proof.
destruct u as [ | | s | u v| |]; 
  [apply arE; auto | apply arO| apply arO | apply (arU _ u v); auto |
   apply arO | apply arO ]; discriminate.
Defined.

Lemma th1 p : size_regex (snd p) <= size_2regex p.
Proof.
destruct p; unfold size_2regex; simpl; lia.
Qed.

Lemma th2' p u v (h : fst p = Union u v) :
  size_regex (Union u v) <= size_2regex p.
Proof.
destruct p; rewrite <- h; unfold size_2regex; simpl; lia.
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

Lemma th3' p u v (h : fst p = Union u v) :
   order(v, snd p) p.
Proof.
destruct p; unfold order; apply left_lex; simpl.
simpl in h; rewrite h; simpl; lia.
Qed.

Lemma th3 p u v :
  abstract_regex (fst p) = aUnion u v ->
  order (v, snd p) p.
Proof.
destruct p as [p1 p2]; destruct p1; try (simpl; discriminate).
simpl; intros h; injection h; intros <- <-; unfold order.
apply left_lex; simpl; lia.
Qed.

Lemma th4' p u v (eq1 : fst p = Union u v) (h : order (v, snd p) p)
      r (rs : size_regex r <= size_2regex (v, snd p)) :
      order (u, r) p.
Proof.
destruct p as [p1 p2]; simpl in eq1; rewrite eq1.
simpl in rs |- *.
apply le_lt_or_eq in rs; destruct rs as [rlt | req].
  now apply left_lex; simpl; lia.
unfold order; simpl.
replace (size_regex u + size_regex r + 1) with
  (size_regex u + size_regex v + 1 + size_regex p2 + 1) by
  ring [req].
apply right_lex; lia.
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

Lemma th5' p u v (eq1 : (fst p) = Union u v)
       r1 (r1s : size_regex r1 <= size_2regex (v, snd p))
       r2 (r2s : size_regex r2 <= size_2regex (u, r1)) :
  size_regex r2 <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl in eq1, r1s, r2s |- *.
rewrite eq1; simpl; lia.
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

Lemma th6' p (neq1 : fst p <> Empty) (neq2 : forall u v, fst p <> Union u v) :
   size_regex (fst p) <= size_2regex p.
Proof.
destruct p; simpl; lia.
Qed.

Lemma th6 p u :
  abstract_regex (fst p) = aOther u ->
  abstract_regex (snd p) = aEmpty ->
  size_regex u <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl; intros h; apply other_case in h; rewrite <- h;
 lia.
Qed.
  
Lemma th7' p v w (eq2 : snd p = Union v w) :
   size_regex (Union v w) <= size_2regex p.
Proof. destruct p; rewrite <- eq2; simpl; lia. Qed.

Lemma th7 p v w :
  abstract_regex (snd p) = aUnion v w ->
  size_regex (Union v w) <= size_2regex p.
Proof.
destruct p as [p1 p2]; destruct p2; try (simpl; discriminate).
simpl; intros h; injection h; intros -> ->; lia.
Qed.

Lemma th8' p v w (eq1 : snd p = Union v w) :
  size_regex (Union (fst p) (Union v w)) <= size_2regex p.
Proof.
destruct p; rewrite <- eq1; simpl; lia.
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

Lemma th9' p v w (eq2 : snd p = Union v w) :
  order (fst p, w) p.
Proof.
destruct p as [p1 p2]; simpl in eq2 |- *.
rewrite eq2; apply left_lex; simpl; lia.
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

Lemma th10' p v w (eq2 : snd p = Union v w)
   r (rs : size_regex r <= size_2regex (fst p, w)) :
   size_regex (Union v r) <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl in eq2, rs |- *.
rewrite eq2; simpl; lia.
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

Lemma th11' p : size_regex (fst p) <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl; lia.
Qed.

Lemma th11 p u : 
  abstract_regex (fst p) = aOther u ->
  size_regex u <= size_2regex p.
Proof.
intros h; apply other_case in h; rewrite <- h.
destruct p; unfold size_2regex; simpl; lia.
Qed.

Lemma th12' p : size_regex (Union (fst p) (snd p)) <= size_2regex p.
Proof.
destruct p; simpl; lia.
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

Lemma th13' p : size_regex (Union (snd p) (fst p)) <= size_2regex p.
Proof.
destruct p; simpl; lia.
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
   match ar (fst p) as a' 
   return ({r | size_regex r <= size_2regex p}) with
     arE _ eq1 => exist _ (snd p) (th1 p)
   | arU _ u v eq1 =>
     match ar (snd p) as b' return
       ({r | size_regex r <= size_2regex p}) with
       arE _ eq2 => exist _ (Union u v) (th2' _ _ _ eq1)
     | _ => exist _ (proj1_sig 
             (norm_union (u, 
                 proj1_sig (norm_union (v, snd p) 
                 (th3' _ _ _ eq1)))
                 (th4' _ _ _ eq1 (th3' _ _ _ eq1) 
                   (proj1_sig (norm_union (v, snd p) (th3' _ _ _ eq1)))
                   _))) 
             (th5' _ _ _ eq1 
                 (proj1_sig (norm_union (v, snd p)
                               (th3' _ _ _ eq1)))
                 _
                 (proj1_sig
                     (norm_union 
                          (u, proj1_sig (norm_union (v, snd p)
                                          (th3' _ _ _ eq1)))
                   (th4' _ _ _ eq1 (th3' _ _ _ eq1) 
                   (proj1_sig (norm_union (v, snd p) (th3' _ _ _ eq1)))
                   _))) _)
     end
   | arO _ d1 d2 =>
     match ar (snd p) as b'
       return ({r | size_regex r <= size_2regex p}) with
       arE _ eq2 => exist _ (snd p) (th1 _)
     | arU _ v w eq2 =>
       if eq_regex_dec (fst p) v then
          exist _ (Union v w) (th7' _ _ _ eq2)
       else if le_regex (fst p) v then
        exist _ (Union (fst p) (Union v w)) (th8' _ _ _ eq2)
       else exist _ (Union v (proj1_sig (norm_union (fst p, w)
               (th9' _ _ _ eq2))))
              (th10' _ _ _ eq2 (proj1_sig (norm_union (fst p, w)
               (th9' _ _ _ eq2)))
                )
     | arO _ d1 d2 =>
       if eq_regex_dec (fst p) (snd p) then
         exist _ (fst p) (th11' _)
       else if le_regex (fst p) (snd p) then
         exist _ (Union (fst p) (snd p)) (th12' _)
       else exist _ (Union (snd p) (fst p)) (th13' _)
     end
   end.

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

Definition norm_union u v : regex := proj1_sig (norm_union_1 (u, v)).

Program Fixpoint norm_union1 u v {measure (u, v) (order)} 
: {r | size_regex r <= size_2regex (u, v)} :=
    match abstract_regex u as a' 
   return ({r | size_regex r <= size_2regex (u, v)}) with
     aEmpty => exist _ u _
   | aUnion u1 v1 => 
     match abstract_regex v as b' return
       ({r | size_regex r <= size_2regex (u, v)}) with
       aEmpty => exist _ (Union u1 v1) _
     | _ =>
         exist _ (proj1_sig 
             (norm_union1 u1
                 (proj1_sig (norm_union1 v1 v)))) _
     end
   | aOther u =>
     match abstract_regex v as b'
       return ({r | size_regex r <= size_2regex (u, v)}) with
       aEmpty => exist _ u _
     | aUnion v1 w1 =>
       if eq_regex_dec u v1 then
          exist _ (Union v1 w1) _
       else if le_regex u v1 then
        exist _ (Union u (Union v1 w1)) _
       else exist _ (Union v1 (proj1_sig (norm_union1 u w1))) _
     | aOther v =>
       if eq_regex_dec u v then
         exist _ u _
       else if le_regex u v then
         exist _ (Union u v) _
       else exist _ (Union v u) _
     end
   end.
Proof.
Next Obligation. lia. Qed.
Next Obligation. (* this shows a proof that un feasible. *)

Lemma norm_union_eqn1 p :
  norm_union_1 p =
  norm_union_F p (fun p' (_ : order p' p) => norm_union_1 p').
Proof.
unfold norm_union_1.
apply (Init.Wf.Fix_eq well_founded_order
          (fun p => {r | size_regex r <= size_2regex p})).
intros x f g fg; unfold norm_union_F.
case (abstract_regex (fst x)).
Lemma norm_union_eqn u v :
  norm_union u v = 
  match u, v with
  | Empty    , v         => v
  | u        , Empty     => u
  | Union u v, w         => norm_union u (norm_union v w)
  | u        , Union v w => if eq_regex_dec u v
                            then Union v w
                            else if le_regex u v
                                 then Union u (Union v w)
                                 else Union v (norm_union u w)
  | u        , v         => if eq_regex_dec u v
                            then u
                            else if le_regex u v
                                 then Union u v
                                 else Union v u
  end.