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

Lemma th5' p u v (eq1 : (fst p) = Union u v)
       r1 (r1s : size_regex r1 <= size_2regex (v, snd p))
       r2 (r2s : size_regex r2 <= size_2regex (u, r1)) :
  size_regex r2 <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl in eq1, r1s, r2s |- *.
rewrite eq1; simpl; lia.
Qed.

Lemma th6' p (neq1 : fst p <> Empty) (neq2 : forall u v, fst p <> Union u v) :
   size_regex (fst p) <= size_2regex p.
Proof.
destruct p; simpl; lia.
Qed.

Lemma th7' p v w (eq2 : snd p = Union v w) :
   size_regex (Union v w) <= size_2regex p.
Proof. destruct p; rewrite <- eq2; simpl; lia. Qed.

Lemma th8' p v w (eq1 : snd p = Union v w) :
  size_regex (Union (fst p) (Union v w)) <= size_2regex p.
Proof.
destruct p; rewrite <- eq1; simpl; lia.
Qed.

Lemma th9' p v w (eq2 : snd p = Union v w) :
  order (fst p, w) p.
Proof.
destruct p as [p1 p2]; simpl in eq2 |- *.
rewrite eq2; apply left_lex; simpl; lia.
Qed.

Lemma th10' p v w (eq2 : snd p = Union v w)
   r (rs : size_regex r <= size_2regex (fst p, w)) :
   size_regex (Union v r) <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl in eq2, rs |- *.
rewrite eq2; simpl; lia.
Qed.

Lemma th11' p : size_regex (fst p) <= size_2regex p.
Proof.
destruct p as [p1 p2]; simpl; lia.
Qed.

Lemma th12' p : size_regex (Union (fst p) (snd p)) <= size_2regex p.
Proof.
destruct p; simpl; lia.
Qed.

Lemma th13' p : size_regex (Union (snd p) (fst p)) <= size_2regex p.
Proof.
destruct p; simpl; lia.
Qed.

Definition norm_union_F : forall p : regex * regex,
   forall g : (forall p', order p' p -> 
                {r : regex | size_regex r <= size_2regex p'}), 
    {r : regex | size_regex r <= size_2regex p} :=
 fun p norm_union =>
   match ar (fst p) with
     arE _ eq1 => exist _ (snd p) (th1 p)
   | arU _ u v eq1 =>
     match ar (snd p) with
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
                 (proj2_sig (norm_union (v, snd p)
                               (th3' _ _ _ eq1)))
                 (proj1_sig
                     (norm_union 
                          (u, proj1_sig (norm_union (v, snd p)
                                          (th3' _ _ _ eq1)))
                   (th4' _ _ _ eq1 (th3' _ _ _ eq1) 
                   (proj1_sig (norm_union (v, snd p) (th3' _ _ _ eq1)))
                   (proj2_sig (norm_union (v, snd p) (th3' _ _ _ eq1))))))
                 (proj2_sig
                     (norm_union 
                          (u, proj1_sig (norm_union (v, snd p)
                                          (th3' _ _ _ eq1)))
                   (th4' _ _ _ eq1 (th3' _ _ _ eq1) 
                   (proj1_sig (norm_union (v, snd p) (th3' _ _ _ eq1)))
                   (proj2_sig (norm_union (v, snd p) (th3' _ _ _ eq1)))))))
     end
   | arO _ d1 d2 =>
     match ar (snd p) with
       arE _ eq2 => exist _ (fst p) (th11' _)
     | arU _ v w eq2 =>
       if eq_regex_dec (fst p) v then
          exist _ (Union v w) (th7' _ _ _ eq2)
       else if le_regex (fst p) v then
        exist _ (Union (fst p) (Union v w)) (th8' _ _ _ eq2)
       else exist _ (Union v (proj1_sig (norm_union (fst p, w)
               (th9' _ _ _ eq2))))
              (th10' _ _ _ eq2
                 (proj1_sig (norm_union (fst p, w)
                       (th9' _ _ _ eq2)))
                 (proj2_sig (norm_union (fst p, w)
                       (th9' _ _ _ eq2))))
     | arO _ d1 d2 =>
       if eq_regex_dec (fst p) (snd p) then
         exist _ (fst p) (th11' _)
       else if le_regex (fst p) (snd p) then
         exist _ (Union (fst p) (snd p)) (th12' _)
       else exist _ (Union (snd p) (fst p)) (th13' _)
     end
   end.

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

Lemma norm_union_eqn1 p :
  norm_union_1 p =
  norm_union_F p (fun p' (_ : order p' p) => norm_union_1 p').
Proof.
unfold norm_union_1.
apply (Init.Wf.Fix_eq well_founded_order
          (fun p => {r | size_regex r <= size_2regex p})).
intros x F G fg; unfold norm_union_F.
case (ar (fst x)).
    reflexivity.
  intros u1 v1 eq1; case (ar (snd x)).
      reflexivity.
    intros u2 v2 eq2.
    rewrite (fg (v1, snd x)).
    rewrite (fg (u1, _)); reflexivity.
  intros d1 d2.
  rewrite (fg (v1, _)).
  rewrite (fg (u1, _)); reflexivity.
intros d1 d2; case (ar (snd x)).
    reflexivity.
  intros u2 v2 eq2; case (eq_regex_dec (fst x) u2).
    reflexivity.
  intros fstxnu2; case (le_regex (fst x) u2).
    reflexivity.
  rewrite fg; reflexivity.
reflexivity.
Qed.

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
Proof.
unfold norm_union at 1.
rewrite norm_union_eqn1; unfold norm_union_F.
simpl fst; simpl snd.
destruct u; destruct v; try reflexivity;
 simpl ar; lazy iota beta;
 match goal with |- context [eq_regex_dec ?A ?B] =>
   case (eq_regex_dec A B);[reflexivity | ];
   case (le_regex A B); reflexivity
 end.
Qed.
