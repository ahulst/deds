(* 
 * Classical logic is required for decision-making on 
 * labeling and sub-formulas. Classical logic is not
 * mandatory for the theories formalized in this proof,
 * but help us avoid dragging too much information with
 * us in the K-structures.
 *)
Axiom classic : forall (P : Prop), P \/ ~ P.

(* Assume the event-set E and property-set P as parameters to this theory *)
Parameter E P : Set.

(* Define the characteristic function for uncontrollable events *)
Parameter U : E -> Prop.

(* 
 * Define the K-structure inductively as a four-tuple
 * for state-space X, labeling function (having the
 * X -> P -> Prop signature), transition relation
 * (having the X -> E -> X -> Prop signature) and
 * initial state.
 *)
Inductive K : Type := klts : forall (X : Set),
  (X -> P -> Prop) -> (X -> E -> X -> Prop) -> X -> K.

(* Define the reflexive-transitive closure of a transition relation *)
Inductive trans (X : Set) (step : X -> E -> X -> Prop) : X -> X -> Prop :=
  | trans_refl : forall (x : X), trans X step x x
  | trans_closed : forall (x y x' : X) (e : E), 
    trans X step y x' -> step x e y -> trans X step x x'.

(* Define partial bisimulation *)
Definition pbis (k' k : K) : Prop :=
  match (k', k) with
  | (klts X' L' step' x', klts X L step x) =>
    exists R : X' -> X -> Prop, R x' x /\
    forall (y' : X') (y : X), R y' y ->
      (forall (p : P), L' y' p <-> L y p) /\
      (forall (e : E) (z' : X'), step' y' e z' ->
        exists z : X, step y e z /\ R z' z) /\
      (forall (e : E) (z : X), U e -> step y e z ->
        exists z' : X', step' y' e z' /\ R z' z)
  end.

(* Define the set of B-formulas *)
Inductive B : Set :=
  | true : B
  | false : B
  | prop : P -> B
  | and : B -> B -> B
  | or : B -> B -> B
  | neg : B -> B.

(* Define the set of F-formulas *)
Inductive F : Set :=
  | basic : B -> F
  | conj : F -> F -> F
  | disj : B -> F -> F
  | all : E -> F -> F
  | ex : E -> F -> F
  | box : F -> F
  | diam : B -> F
  | can : E -> F
  | dlf : F.

(* 
 * We need an additional well-formedness test to assure
 * that formulas of type <e>f are restricted in such a
 * way that e is controllable.
 *)
Fixpoint wf (f : F) : Prop :=
  match f with
  | conj f g => wf f /\ wf g
  | disj b f => wf f
  | all e f => wf f
  | ex e f => ~ U e /\ wf f
  | box f => wf f
  | _ => True
  end.

(* Define validity for B-formulas w.r.t a K-structure *)
Fixpoint bval (X : Set) (L : X -> P -> Prop) (x : X) (b : B) : Prop :=
  match b with
  | true => True
  | false => False
  | prop p => L x p
  | and b c => bval X L x b /\ bval X L x c
  | or b c => bval X L x b \/ bval X L x c
  | neg b => ~ bval X L x b
  end.

(* Define validity for F-formulas w.r.t a K-structure *)
Fixpoint fval (k : K) (f : F) : Prop := 
  match (k, f) with
  | (klts X L step x, basic b) => bval X L x b
  | (klts X L step x, conj f g) => fval k f /\ fval k g
  | (klts X L step x, disj b f) => bval X L x b \/ fval k f
  | (klts X L step x, all e f) => forall (x' : X),
    step x e x' -> fval (klts X L step x') f
  | (klts X L step x, ex e f) => exists x' : X,
    step x e x' /\ fval (klts X L step x') f
  | (klts X L step x, box f) => forall (x' : X),
    trans X step x x' -> fval (klts X L step x') f
  | (klts X L step x, diam b) => exists x' : X,
    trans X step x x' /\ bval X L x' b
  | (klts X L step x, can e) => exists x' : X, step x e x'
  | (klts X L step x, dlf) => exists e : E, 
    exists x' : X, step x e x'
  end.

(* Define sub-formulas as an inductive predicate *)
Inductive sub (X : Set) (L : X -> P -> Prop) (x : X) : F -> F -> Prop :=
  | sub_refl : forall (f : F), sub X L x f f
  | sub_conj_left : forall (f g h : F), sub X L x f g -> sub X L x f (conj g h)
  | sub_conj_right : forall (f g h : F), sub X L x f h -> sub X L x f (conj g h)
  | sub_disj : forall (f g : F) (b : B), ~ bval X L x b -> sub X L x f g -> sub X L x f (disj b g)
  | sub_box : forall (f g : F), sub X L x f g -> sub X L x f (box g).

(* Define the unfolded initial transition relation -->0 *)
Inductive zero (X : Set) (L : X -> P -> Prop) 
    (step : X -> E -> X -> Prop) : X * F -> E -> X * F -> Prop :=
  | zero_basic : forall (x x' : X) (e : E) (b : B), 
    step x e x' -> zero X L step (x, basic b) e (x', basic true)
  | zero_conj_incl : forall (x x' : X) (e : E) (f g f' g' : F),
    zero X L step (x, f) e (x', f') -> zero X L step (x, g) e (x', g') ->
    sub X L x' g' f' -> zero X L step (x, conj f g) e (x', f')
  | zero_conj_excl : forall (x x' : X) (e : E) (f g f' g' : F),
    zero X L step (x, f) e (x', f') -> zero X L step (x, g) e (x', g') ->
    ~ sub X L x' g' f' -> zero X L step (x, conj f g) e (x', conj f' g')
  | zero_disj_left : forall (x x' : X) (e : E) (b : B) (f : F),
    bval X L x b -> step x e x' -> zero X L step (x, disj b f) e (x', basic true)
  | zero_disj_right : forall (x x' : X) (e : E) (b : B) (f f' : F),
    ~ bval X L x b -> zero X L step (x, f) e (x', f') ->
    zero X L step (x, disj b f) e (x', f')
  | zero_all_pos : forall (x x' : X) (e : E) (f : F),
    step x e x' -> zero X L step (x, all e f) e (x', f)
  | zero_all_neg : forall (x x' : X) (e e' : E) (f : F), e <> e' ->
    step x e' x' -> zero X L step (x, all e f) e' (x', basic true)
  | zero_ex_pos : forall (x x' : X) (e : E) (f : F),
    step x e x' -> zero X L step (x, ex e f) e (x', f)
  | zero_ex_neg : forall (x x' : X) (e e' : E) (f : F),
    step x e' x' -> zero X L step (x, ex e f) e' (x', basic true)
  | zero_box_incl : forall (x x' : X) (e : E) (f f' : F),
    zero X L step (x, f) e (x', f') -> sub X L x' f' f ->
    zero X L step (x, box f) e (x', box f)
  | zero_box_excl : forall (x x' : X) (e : E) (f f' : F),
    zero X L step (x, f) e (x', f') -> ~ sub X L x' f' f ->
    zero X L step (x, box f) e (x', conj (box f) f')
  | zero_diam : forall (x x' : X) (e : E) (b : B),
    step x e x' -> zero X L step (x, diam b) e (x', basic true)
  | zero_can : forall (x x' : X) (e e' : E), step x e' x' ->
    zero X L step (x, can e) e' (x', basic true)
  | zero_dlf : forall (x x' : X) (e : E), step x e x' ->
    zero X L step (x, dlf) e (x', basic true).

(* 
 * Define the synthesizability predicate by means of an
 * inductive predicate to closely resemble the derivation
 * rules proposed in the paper.
 *)
Inductive syn (X : Set) (L : X -> P -> Prop)
  (step : X * F -> E -> X * F -> Prop) : X * F -> F -> Prop :=
  | syn_basic : forall (x : X) (g : F) (b : B), bval X L x b -> syn X L step (x, g) (basic b)
  | syn_conj : forall (x : X) (g f1 f2 : F), syn X L step (x, g) f1 ->
    syn X L step (x, g) f2 -> syn X L step (x, g) (conj f1 f2)
  | syn_disj_left : forall (x : X) (g f : F) (b : B), bval X L x b -> syn X L step (x, g) (disj b f)
  | syn_disj_right : forall (x : X) (g f : F) (b : B), syn X L step (x, g) f -> 
    syn X L step (x, g) (disj b f)
  | syn_all : forall (x : X) (e : E) (g f : F), syn X L step (x, g) (all e f)
  | syn_ex : forall (x x' : X) (e : E) (g g' f : F), step (x, g) e (x', g') -> 
    sub X L x' f g' -> syn X L step (x', g') f -> syn X L step (x, g) (ex e f)
  | syn_box : forall (x : X) (g f : F), syn X L step (x, g) f -> syn X L step (x, g) (box f)
  | syn_diam : forall (x x' : X) (g g' : F) (b : B), bval X L x' b ->
    trans (X * F) step (x, g) (x', g') -> syn X L step (x, g) (diam b)
  | syn_can : forall (x x' : X) (e : E) (g g' : F),
    step (x, g) e (x', g') -> syn X L step (x, g) (can e)
  | syn_dlf : forall (x x' : X) (e : E) (g g' : F),
    step (x, g) e (x', g') -> syn X L step (x, g) dlf.

(* Restrict a transition relation to only uncontrollable steps *)
Definition unctrl (X : Set) (step : X -> E -> X -> Prop) (x : X) (e : E) (x' : X) : Prop :=
  step x e x' /\ U e.

(* 
 * Give the fixpoint definition for the iterative steps
 * in constructing the transition relation for the synthesis
 * result. The first step, where n = 0, is directly equal
 * to the -->0 relation defined previously. For the
 * n+1 case, we restrict the -->n relation in such a
 * way that only the steps (x, f) -(e)->n (x', f') such
 * that for all (x', f') -(s)->*n (x'', f'') and s taken
 * from U* and syn (x'', f'') f'' are inherited.
 *)
Fixpoint rel (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (xf : X * F) (e : E) (xf' : X * F) : Prop :=
  match n with
  | 0 => zero X L step xf e xf'
  | S n => rel n X L step xf e xf' /\ (U e \/ forall (xf'' : X * F),
    trans (X * F) (unctrl (X * F) (rel n X L step)) xf' xf'' ->
    syn X L (rel n X L step) xf'' (snd xf''))
  end.

(* Define n-th iteration of the synthesis result *)
Definition S (k : K) (f : F) (n : nat) : K :=
  match k with 
  | klts X L step x => klts (X * F) (fun xf => L (fst xf))
      (rel n X L step) (x, f)
  end.

(* Define a predicate to check whether synthesis is finished *)
Definition complete (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (xf : X * F) : Prop :=
  forall (xf' : X * F), trans (X * F) (rel n X L step) xf xf' ->
  syn X L (rel n X L step) xf' (snd xf').

(* If x -->* y and y -->* z then x -->* z *)
Lemma trans_cat : forall (X : Set) (step : X -> E -> X -> Prop) (x y z : X),
  trans X step x y -> trans X step y z -> trans X step x z.
Proof.
  intros X step x y z H H' ; induction H ; auto.
  apply trans_closed with y e ; auto.
Qed.

(* If (x, f) -(e)->0 (x', f') then x -(e)-> x' *)
Lemma zero_impl_step : forall (f f' : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (e : E),
  zero X L step (x, f) e (x', f') -> step x e x'.
Proof.
  intro f ; induction f ; intros f' X L step x x' e' Hzero ;
    solve [ inversion Hzero ; auto ] || auto.
  inversion Hzero ; apply IHf1 in H4 ; auto.
  inversion Hzero ; auto.
  apply IHf in H6 ; auto.
  inversion Hzero ; auto.
  apply IHf in H3 ; auto.
  apply IHf in H3 ; auto.
Qed.

(* If (x, f) -(e)->n (x', f') then (x, f) -(e)->0 (x', f') *)
Lemma rel_impl_zero : forall (n : nat) (f f' : F) (X : Set) 
  (L : X -> P -> Prop) (step : X -> E -> X -> Prop) (x x' : X) (e : E),
  rel n X L step (x, f) e (x', f') -> zero X L step (x, f) e (x', f').
Proof.
  intro n ; induction n ; intros f f' X L step x x' e Hrel.
  simpl in Hrel ; auto.
  simpl in Hrel ; destruct Hrel as [ Hrel _ ].
  apply IHn in Hrel ; auto.
Qed.

(* Synthesizability is inherited over sub-formulas *)
Lemma sub_syn : forall (X : Set) (L : X -> P -> Prop)
  (step : X * F -> E -> X * F -> Prop) (x : X) (f g h : F),
  sub X L x f g -> syn X L step (x, h) g -> syn X L step (x, h) f.
Proof.
  intros X L step x f g h Hsub Hsyn ; induction Hsub ; 
    solve [ auto ] || solve [ inversion Hsyn ; 
    contradiction || auto ] || auto.
Qed.

(* Validity is inherited over sub-formulas *)
Lemma sub_val : forall (f g : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X), sub X L x f g ->
  fval (klts X L step x) g -> fval (klts X L step x) f.
Proof.
  intros f g X L step x Hsub Hval ; induction Hsub ; auto.
  simpl in Hval ; destruct Hval ; auto.
  simpl in Hval ; destruct Hval ; auto.
  simpl in Hval ; destruct Hval ; contradiction || auto.
  apply IHHsub ; apply Hval ; apply trans_refl.
Qed.

(* If f /\ g is a sub-formula of h then both f and g are sub-formulas of h *)
Lemma sub_conj : forall (X : Set) (L : X -> P -> Prop) (x : X) (f g h : F),
  sub X L x (conj f g) h -> sub X L x f h /\ sub X L x g h.
Proof.
  intros X L x f g h Hsub.
  assert (exists i : F, i = conj f g) as H by eauto.
  destruct H as [ i Heq ] ; rewrite <- Heq in *.
  revert Heq ; revert f g ; induction Hsub ; intros p q Heq ;
    rewrite Heq in *.
  split ; [ apply sub_conj_left | apply sub_conj_right ] ; apply sub_refl.
  assert (conj p q = conj p q) as H by auto ; apply IHHsub in H.
  split ; apply sub_conj_left ; tauto.
  assert (conj p q = conj p q) as H by auto ; apply IHHsub in H.
  split ; apply sub_conj_right ; tauto.
  assert (conj p q = conj p q) as H' by auto ; apply IHHsub in H'.
  split ; apply sub_disj ; tauto.
  assert (conj p q = conj p q) as H by auto ; apply IHHsub in H.
  split ; apply sub_box ; tauto.
Qed.

(* If b \/ f is a sub-formula of g and not x |= b then f \in sub (x, g) *)
Lemma sub_disj_not : forall (X : Set) (L : X -> P -> Prop) (x : X) (b : B) (f g : F),
  sub X L x (disj b f) g -> ~ bval X L x b -> sub X L x f g.
Proof.
  intros X L x b f g Hsub Hbval.
  assert (exists h : F, h = disj b f) as H by eauto.
  destruct H as [ h Heq ] ; rewrite <- Heq in *.
  revert Heq ; revert Hbval ; revert b f ; induction Hsub ; 
    intros c f' Hbval Heq ; rewrite Heq in *.
  apply sub_disj ; apply sub_refl || auto ; auto.
  assert (disj c f' = disj c f') as H by auto.
  apply IHHsub in H ; auto.
  apply sub_conj_left ; auto.
  assert (disj c f' = disj c f') as H by auto.
  apply IHHsub in H ; auto.
  apply sub_conj_right ; auto.
  assert (disj c f' = disj c f') as H' by auto.
  apply IHHsub in H' ; auto.
  apply sub_disj ; auto.
  assert (disj c f' = disj c f') as H' by auto.
  apply IHHsub in H' ; auto.
  apply sub_box ; auto.
Qed.

(* If []f \in sub (x, g) then f \in sub (x, g) *)
Lemma sub_box_in : forall (X : Set) (L : X -> P -> Prop) 
  (x : X) (f g : F), sub X L x (box f) g -> sub X L x f g.
Proof.
  intros X L x f g Hsub ; assert (exists h : F, h = box f) as H by eauto.
  destruct H as [ h Heq ] ; rewrite <- Heq in *.
  revert Heq ; revert f ; induction Hsub ;
    intros f' Heq ; rewrite Heq in *.
  apply sub_box ; apply sub_refl.
  apply sub_conj_left ; apply IHHsub ; auto.
  apply sub_conj_right ; apply IHHsub ; auto.
  apply sub_disj ; auto.
  apply sub_box ; auto.
Qed.

(* Prove transitivity of the sub-formula relation *)
Lemma sub_trans : forall (X : Set) (L : X -> P -> Prop) (x : X) (f g h : F),
  sub X L x f g -> sub X L x g h -> sub X L x f h.
Proof.
  intros X L x f g h Hsub Hsub' ; induction Hsub ; auto.
  apply sub_conj in Hsub' ; destruct Hsub' ; auto.
  apply sub_conj in Hsub' ; destruct Hsub' ; auto.
  apply sub_disj_not in Hsub' ; auto.
  apply sub_box_in in Hsub' ; auto.
Qed.

(* If (x, g) -(e)->0 (x', g') and [e]f \in sub (x, g) then f \in sub (x', g') *)
Lemma sub_all : forall (f g g' : F) (X : Set) (L : X -> P -> Prop) 
  (step : X -> E -> X -> Prop) (x y : X) (e : E), sub X L x (all e f) g -> 
  zero X L step (x, g) e (y, g') -> sub X L y f g'.
Proof.
  intros f g g' X L step x y e Hsub Hred.
  assert (exists h : F, h = all e f) as Heq by eauto.
  destruct Heq as [ h Heq ] ; rewrite <- Heq in *.
  revert Heq Hred ; revert e f g' ; induction Hsub ;
    intros e f' g' Heq Hred ; rewrite Heq in *.
  inversion Hred ; apply sub_refl || auto.
  assert (e = e) by auto ; contradiction.
  inversion Hred.
  apply IHHsub with (f := f') in H4 ; auto.
  apply IHHsub with (f := f') in H4 ; auto.
  apply sub_conj_left ; auto.
  inversion Hred.
  apply IHHsub with (f := f') in H6 ; auto.
  apply sub_trans with g'0 ; auto.
  apply IHHsub with (f := f') in H6 ; auto.
  apply sub_conj_right ; auto.
  inversion Hred ; contradiction || auto.
  apply IHHsub with (f := f') in H7 ; auto.
  inversion Hred.
  apply IHHsub with (f := f') in H3 ; auto.
  apply sub_box.
  apply sub_trans with f'0 ; auto.
  apply IHHsub with (f := f') in H3 ; auto.
  apply sub_conj_right ; auto.
Qed.

(* []f as a sub-formula is constant under (x, g) -(e)->0 (y', g') *)
Lemma sub_box_red : forall (X : Set) (L : X -> P -> Prop) 
  (step : X -> E -> X -> Prop) (x y : X) (e : E) (f g g' : F),
  sub X L x (box f) g -> zero X L step (x, g) e (y, g') -> sub X L y (box f) g'.
Proof.
  intros X L step x y e f g g' Hsub Hred ; assert (exists h : F, h = box f) as Heq by eauto.
  destruct Heq as [ h Heq ] ; rewrite <- Heq in *.
  revert Heq Hred ; revert f g' ; induction Hsub ;
    intros f' g' Heq Hred ; rewrite Heq in *.
  inversion Hred ; [ apply sub_refl | ].
  apply sub_conj_left ; apply sub_refl.
  inversion Hred.
  apply IHHsub with (f := f') in H4 ; auto.
  apply IHHsub with (f := f') in H4 ; auto.
  apply sub_conj_left ; auto.
  inversion Hred.
  apply IHHsub with (f := f') in H6 ; auto.
  apply sub_trans with g'0 ; auto.
  apply IHHsub with (f := f') in H6 ; auto.
  apply sub_conj_right ; auto.
  inversion Hred ; contradiction || auto.
  apply IHHsub with (f := f') ; auto.
  inversion Hred.
  apply IHHsub with (f := f') in H3 ; auto.
  apply sub_box ; apply sub_trans with f'0 ; auto.
  apply sub_conj_right ; auto.
  apply IHHsub with (f := f') ; auto.
Qed.

(* If []f is a sub-formula of g and (x, g) -->*n (x', g') then f \in sub (x',g') *)
Lemma sub_trans_box : forall (X : Set) (L : X -> P -> Prop) (step : X -> E -> X -> Prop) 
  (x x' : X) (f g g' : F) (n : nat), sub X L x (box f) g ->
  trans (X * F) (rel n X L step) (x, g) (x', g') -> sub X L x' f g'.
Proof.
  intros X L step x x' f g g' n Hsub Htrans.
  assert (exists xg : X * F, xg = (x, g)) as Heq by eauto.
  assert (exists xg' : X * F, xg' = (x', g')) as Heq' by eauto.
  destruct Heq as [ xg Heq ] ; rewrite <- Heq in *.
  destruct Heq' as [ xg' Heq' ] ; rewrite <- Heq' in *.
  assert (sub X L x' (box f) g') as Hsub'.
  revert Heq Heq' Hsub ; revert x g x' g'.
  induction Htrans ; intros z g z' g' Heq Heq' Hsub.
  rewrite Heq in Heq' ; inversion Heq'.
  replace z with z' in * by auto ; replace g with g' in * by auto ; auto.
  rewrite Heq in * ; destruct y as [ y h ].
  apply rel_impl_zero in H ; apply sub_box_red with (y := y) (f := f) in H ; auto.
  apply IHHtrans with (x'0 := z') (g' := g') in H ; auto.
  apply sub_box_in in Hsub' ; auto.
Qed.

(* Validity of B-formulas only depends on labeling *)
Lemma bval_iff : forall (b : B) (X : Set) (L : X -> P -> Prop) (x : X) (g : F),
  bval X L x b <-> bval (X * F) (fun xf => L (fst xf)) (x, g) b.
Proof.
  intro b ; induction b ; intros X L x g ; split ; intro H ;
    solve [ simpl in * ; tauto ] || idtac.
  simpl in H ; destruct H ; split ; [ apply IHb1 | apply IHb2 ] ; auto.
  simpl in H ; destruct H as [ Hb1 Hb2 ].
  apply IHb1 in Hb1 ; apply IHb2 in Hb2 ; split ; auto.
  simpl in H ; destruct H ; [ left | right ] ; auto.
  apply IHb1 ; auto.
  apply IHb2 ; auto.
  simpl in H ; destruct H as [ Hb1 | Hb2 ].
  apply IHb1 in Hb1 ; left ; auto.
  apply IHb2 in Hb2 ; right ; auto.
  simpl ; intro H' ; simpl in H ; apply H ; apply IHb in H' ; auto.
  simpl in * ; intro H' ; apply H ; apply IHb ; auto.
Qed.

(* 
 * Prove that if synthesizability holds at every
 * reachable state then the synthesis result satisfies
 * the synthesized control objective
 *)
Theorem validity : forall (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (f : F),
  complete n X L step (x, f) -> fval (S (klts X L step x) f n) f.
Proof.
  intros n X L step x f ; assert (sub X L x f f) as H by ( apply sub_refl ).
  revert H ; revert x ; generalize f at 2 3 4 as g.
  induction f ; intros g x Hsub Hcomplete ;
    assert (syn X L (rel n X L step) (x, g) g) as Hsyn by
    ( apply Hcomplete ; apply trans_refl ).
  apply sub_syn with (f := basic b) in Hsyn ; auto.
  inversion Hsyn ; simpl ; apply bval_iff ; auto.
  apply sub_conj in Hsub ; destruct Hsub as [ Hf1 Hf2 ].
  split ; [ apply IHf1 | apply IHf2 ] ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  simpl ; left ; apply bval_iff ; auto.
  apply sub_disj_not in Hsub ; auto.
  right ; apply IHf ; auto.
  simpl ; intros xg' Hstep ; destruct xg' as [ x' g' ].
  assert (zero X L step (x, g) e (x', g')) as Hred.
  apply rel_impl_zero in Hstep ; auto.
  apply sub_all with (f := f) (y := x') in Hred ; auto.
  apply IHf ; auto.
  intros xf' Htrans ; apply Hcomplete.
  apply trans_closed with (x', g') e ; auto.
  assert (syn X L (rel n X L step) (x, g) (ex e f)) as Hex.
  apply sub_syn with g ; auto.
  inversion Hex ; exists (x', g') ; split ; auto.
  apply IHf ; auto.
  intros xg' Htrans ; apply Hcomplete.
  apply trans_closed with (x', g') e ; auto.
  simpl ; intros xg' Htrans ; destruct xg' as [ x' g' ].
  apply IHf ; auto.
  apply sub_trans_box with (f := f) in Htrans ; auto.
  intros xg' Htrans' ; apply Hcomplete.
  apply trans_cat with (x', g') ; auto.
  assert (syn X L (rel n X L step) (x, g) (diam b)) as H.
  apply sub_syn with (g := g) ; auto.
  inversion H ; exists (x', g') ; split ; auto.
  apply bval_iff ; auto.
  assert (syn X L (rel n X L step) (x, g) (can e)) as H.
  apply sub_syn with (g := g) ; auto.
  inversion H ; exists (x', g') ; auto.
  assert (syn X L (rel n X L step) (x, g) dlf) as H.
  apply sub_syn with (g := g) ; auto.
  inversion H ; exists e ; exists (x', g') ; auto.
Qed.

(* If x -(e)-> x' then an f' such that (x, f) -(e)-> (x', f') exists *)
Lemma zero_ex : forall (f : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x y : X) (e : E), step x e y ->
  exists f' : F, zero X L step (x, f) e (y, f').
Proof.
  intro f ; induction f ; intros X L step x y e' Hstep.
  exists (basic true) ; apply zero_basic ; auto.
  destruct (IHf1 X L step x y e') as [ f1' Hred_f1 ] ; auto.
  destruct (IHf2 X L step x y e') as [ f2' Hred_f2 ] ; auto.
  destruct (classic (sub X L y f2' f1')) as [ Hsub | Hnot_sub ].
  exists f1' ; apply zero_conj_incl with f2' ; auto.
  exists (conj f1' f2') ; apply zero_conj_excl ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  exists (basic true) ; apply zero_disj_left ; auto.
  destruct (IHf X L step x y e') as [ f' Hred ] ; auto.
  exists f' ; apply zero_disj_right ; auto.
  destruct (classic (e = e')) as [ Heq | Hnot_eq ].
  rewrite Heq ; exists f ; apply zero_all_pos ; auto.
  exists (basic true) ; apply zero_all_neg ; auto.
  exists (basic true) ; apply zero_ex_neg ; auto.
  destruct (IHf X L step x y e') as [ f' Hred ] ; auto.
  destruct (classic (sub X L y f' f)) as [ Hsub | Hnot_sub ].
  exists (box f) ; apply zero_box_incl with f' ; auto.
  exists (conj (box f) f') ; apply zero_box_excl ; auto.
  exists (basic true) ; apply zero_diam ; auto.
  exists (basic true) ; apply zero_can ; auto.
  exists (basic true) ; apply zero_dlf ; auto.
Qed.

(* If (x, f) -(e)->0 (x', f') then (x, f) -(e)->n (x', f') if e is uncontrollable *)
Lemma unctrl_ex : forall (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (e : E) (f f' : F), U e ->
  zero X L step (x, f) e (x', f') -> rel n X L step (x, f) e (x', f').
Proof.
  intro n ; induction n ; intros X L step x x' e f f' HU Hzero.
  simpl ; unfold rel ; simpl ; auto.
  simpl ; split ; auto.
Qed.

(* 
 * Prove that the synthesis result is related to the original 
 * model via partial bisimulation, which implies controllability
 *)
Theorem controllability : forall (k : K) (f : F) (n : nat),
  pbis (S k f n) k.
Proof.
  intros k f n ; destruct k as [ X L step x ].
  exists (fun yg y => fst yg = y) ; split ; auto.
  intros y' y Heq ; destruct y' as [ y' g ].
  simpl in Heq ; rewrite Heq in * ; clear Heq y'.
  split ; [ simpl ; tauto | split ].
  intros e zg' Hrel ; destruct zg' as [ z g' ].
  apply rel_impl_zero in Hrel ; apply zero_impl_step in Hrel.
  exists z ; split ; simpl ; auto.
  intros e z HU Hstep ; destruct (zero_ex g X L step y z e) as [ g' Hred ] ; auto.
  exists (z, g') ; split ; apply unctrl_ex || auto ; auto.
Qed.

(* 
 * If k = (X,L,-->,x) and k |= f and x -(e)-> x' then there
 * exists f' such that (x, f) -(e)->0 (x', f') and (X,L,-->,x') |= f'
 *) 
Lemma val_next : forall (f : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E ->  X -> Prop) (x x' : X) (e : E), step x e x' ->
  fval (klts X L step x) f -> exists f' : F, zero X L step (x, f) e (x', f') /\ 
  fval (klts X L step x') f'.
Proof.
  intro f ; induction f ; intros X L step x x' e' Hstep Hval.
  exists (basic true) ; split ; apply zero_basic || simpl ; auto.
  simpl in Hval ; destruct Hval as [ Hf1 Hf2 ].
  apply IHf1 with (x' := x') (e := e') in Hf1 ; auto.
  apply IHf2 with (x' := x') (e := e') in Hf2 ; auto.
  destruct Hf1 as [ f1' [ Hred_f1 Hval_f1 ] ].
  destruct Hf2 as [ f2' [ Hred_f2 Hval_f2 ] ].
  destruct (classic (sub X L x' f2' f1')) as [ Hsub | Hnot_sub ].
  exists f1' ; split ; [ apply zero_conj_incl with f2' ; auto | auto ].
  exists (conj f1' f2') ; split.
  apply zero_conj_excl ; auto.
  split ; auto.
  simpl in Hval ; destruct Hval as [ Hbval | Hval ].
  exists (basic true) ; split ; simpl ; auto.
  apply zero_disj_left ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  exists (basic true) ; split ; simpl ; auto.
  apply zero_disj_left ; auto.
  apply IHf with (x' := x') (e := e') in Hval ; auto.
  destruct Hval as [ f' [ Hred Hval ] ].
  exists f' ; split ; auto.
  apply zero_disj_right ; auto.
  destruct (classic (e = e')) as [ Heq | Hnot_eq ].
  rewrite <- Heq in * ; exists f ; split ; auto.
  apply zero_all_pos ; auto.
  exists (basic true) ; split ; simpl ; auto.
  apply zero_all_neg ; auto.
  exists (basic true) ; split ; simpl ; auto.
  apply zero_ex_neg ; auto.
  assert (fval (klts X L step x) f) as Hval_f.
  apply Hval ; apply trans_refl.
  apply IHf with (x' := x') (e := e') in Hval_f ; auto.
  destruct Hval_f as [ f' [ Hred Hval_f' ] ].
  destruct (classic (sub X L x' f' f)) as [ Hsub | Hnot_sub ].
  exists (box f) ; split ; auto.
  apply zero_box_incl with f' ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e' ; auto.
  exists (conj (box f) f') ; split ; auto.
  apply zero_box_excl ; auto.
  split ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e' ; auto.
  exists (basic true) ; split ; simpl ; auto.
  apply zero_diam ; auto.
  exists (basic true) ; split ; simpl ; auto.
  apply zero_can ; auto.
  exists (basic true) ; split ; simpl ; auto.
  apply zero_dlf ; auto.
Qed.

(* Synthesizability in synthesis step n+1 implies the same in step n *)
Lemma syn_less : forall (f g : F) (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X), syn X L (rel (Datatypes.S n) X L step) (x, g) f ->
  syn X L (rel n X L step) (x, g) f.
Proof.
  assert (forall (n : nat) (X : Set) (L : X -> P -> Prop)
    (step : X -> E -> X -> Prop) (x x' : X) (g g' : F),
    trans (X * F) (rel (Datatypes.S n) X L step) (x, g) (x', g') ->
    trans (X * F) (rel n X L step) (x, g) (x', g')) as Htrans.
  intros n X L step x x' g g' Htrans.
  assert (exists xg : X * F, xg = (x, g)) as Heq by eauto.
  assert (exists xg' : X * F, xg' = (x', g')) as Heq' by eauto.
  destruct Heq as [ xg Heq ] ; rewrite <- Heq in *.
  destruct Heq' as [ xg' Heq' ] ; rewrite <- Heq' in *.
  revert Heq Heq' ; revert x g x' g'.
  induction Htrans ; intros z g z' g' Heq Heq' ; apply trans_refl || auto.
  rewrite Heq in * ; destruct y as [ y h ] ; rewrite Heq' in *.
  apply trans_closed with (y, h) e ; auto.
  apply IHHtrans with y h z' g' ; simpl in H ; tauto.
  simpl in H ; tauto.
  intro f ; induction f ; intros g n X L step x Hsyn.
  inversion Hsyn ; apply syn_basic ; auto.
  inversion Hsyn ; apply syn_conj ; auto.
  inversion Hsyn ; [ apply syn_disj_left ; auto | ].
  apply syn_disj_right ; auto.
  apply syn_all.
  inversion Hsyn ; apply syn_ex with x' g' ; auto.
  simpl in * ; tauto.
  inversion Hsyn ; apply syn_box ; auto.
  inversion Hsyn ; apply syn_diam with x' g' ; auto.
  inversion Hsyn ; apply syn_can with x' g'.
  simpl in * ; tauto.
  inversion Hsyn ; apply syn_dlf with x' e g'.
  simpl in * ; tauto.
Qed.

(* 
 * If (x, f) -(e)->0 (x', f') and for all (x', f') -->*n (x'', f'')
 * synthesizability holds, then we can derive (x, f) -(e)->n (x', f')
 *)
Lemma rel_ex : forall (n : nat) (X : Set) (L : X -> P -> Prop) 
  (step : X -> E -> X -> Prop) (x x' : X) (e : E) (f f' : F),
  (forall (x'' : X) (f'' : F), trans (X * F) (unctrl (X * F) (rel n X L step)) (x', f') (x'', f'') ->
    syn X L (rel n X L step) (x'', f'') f'') ->
  zero X L step (x, f) e (x', f') -> rel n X L step (x, f) e (x', f').
Proof.
  assert (forall (X : Set) (L : X -> P -> Prop) (step : X -> E -> X -> Prop)
    (x x' : X) (g g' : F) (n : nat), 
    trans (X * F) (unctrl (X * F) (rel n X L step)) (x, g) (x', g') ->
    trans (X * F) (unctrl (X * F) (rel (Datatypes.S n) X L step)) (x, g) (x', g')) as Htrans.
  intros X L step x x' g g' n Htrans.
  assert (exists xg : X * F, xg = (x, g)) as Heq by eauto.
  assert (exists xg' : X * F, xg' = (x', g')) as Heq' by eauto.
  destruct Heq as [ xg Heq ] ; rewrite <- Heq in *.
  destruct Heq' as [ xg' Heq' ] ; rewrite <- Heq' in *.
  revert Heq Heq' ; revert x g x' g'.
  induction Htrans ; intros z g z' g' Heq Heq' ; apply trans_refl || auto.
  rewrite Heq in * ; destruct y as [ y h ] ; rewrite Heq' in *.
  apply trans_closed with (y, h) e ; auto.
  apply IHHtrans with y h z' g' ; simpl in H ; tauto.
  unfold unctrl in * ; simpl ; tauto.
  intro n ; induction n ; intros X L step x x' e f f' H Hred.
  simpl ; unfold rel ; simpl ; auto.
  simpl ; split ; [ apply IHn ; auto | ].
  intros x'' f'' Htrans' ; apply syn_less ; apply H.
  apply Htrans ; auto.
  right ; intros xf'' Htrans' ; destruct xf'' as [ x'' f'' ].
  simpl ; apply syn_less ; apply H.
  apply Htrans ; auto.
Qed.

(* 
 * If (X,L,-->,x) |= f and (x, f) -(e)-> (x',f') and 
 * event e is uncontrollable, then (X,L,-->,x') |= f'
 *)
Lemma wf_next : forall (f f' : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E ->  X -> Prop) (x x' : X) (e : E), step x e x' ->
  fval (klts X L step x) f -> wf f -> U e -> 
  zero X L step (x, f) e (x', f') -> fval (klts X L step x') f'.
Proof.
  intro f ; induction f ; 
    intros f' X L step x x' e' Hstep Hval Hwf HU Hred ;
    solve [ inversion Hred ; simpl in * ; tauto ] || idtac.
  inversion Hred ; simpl in Hval ; destruct Hval.
  destruct (classic (sub X L x' g' f')) as [ Hsub | Hnot_sub ].
  apply IHf1 with x e' ; simpl in * ; tauto.
  apply IHf1 in H4 ; simpl in * ; tauto || auto.
  apply IHf1 in H4 ; simpl in * ; tauto || auto.
  apply IHf2 in H6 ; simpl in * ; tauto || auto.
  inversion Hred ; simpl ; auto.
  simpl in Hval ; destruct Hval as [ Hbval | Hval ] ;
    contradiction || auto.
  apply IHf with x e' ; simpl in * ; tauto.
  inversion Hred ; [ replace e with e' in * by auto | simpl ; auto ].
  replace f with f' in * by auto ; simpl in * ; auto.
  inversion Hred ; [ replace e with e' in * by auto | simpl ; auto ].
  replace f with f' in * by auto ; simpl in * ; auto.
  destruct Hwf ; contradiction.
  inversion Hred.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e' ; auto.
  split ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e' ; auto.
  apply IHf with x e' ; simpl in * ; auto.
  apply Hval ; apply trans_refl.
Qed.

(* The well-formedness test is stable under (x, f) -(e)->0 (x',f') *)
Lemma wf_zero : forall (f : F) (X : Set) (L : X -> P -> Prop) 
  (step : X -> E -> X -> Prop) (x y : X) (f' : F) (e : E),
  wf f -> zero X L step (x, f) e (y, f') -> wf f'.
Proof.
  intro f ; induction f ; intros X L step x y f' e' Hwf Hred ;
    solve [ inversion Hred ; simpl ; auto ] || auto.
  simpl in Hwf ; destruct Hwf ; inversion Hred.
  apply IHf1 in H6 ; auto.
  apply IHf1 in H6 ; apply IHf2 in H8 ; simpl ; tauto.
  simpl in Hwf ; inversion Hred ; simpl ; auto.
  apply IHf in H6 ; auto.
  inversion Hred ; simpl in Hwf ; simpl ; auto.
  replace f' with f in * ; auto.
  inversion Hred ; simpl in Hwf ; simpl ; auto.
  replace f' with f in * ; tauto.
  inversion Hred ; auto.
  apply IHf in H3 ; simpl ; auto.
Qed.

(* Partial bisimulation implies validity for B-formulas *)
Lemma pbis_bval : forall (b : B) (X X' : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop)
  (step : X -> E -> X -> Prop) (x' : X') (x : X),
  pbis (klts X' L' step' x') (klts X L step x) ->
  (bval X' L' x' b <-> bval X L x b).
Proof.
  intro b ; induction b ; 
    intros X X' L' L step' step x' x Hpbis ; split ; intro H ;
    solve [ simpl in * ; tauto ] || idtac.
  simpl in * ; destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in H ; auto.
  simpl in * ; destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in H ; auto.
  simpl in H ; destruct H as [ Hb1 Hb2 ] ; 
    simpl ; split ; auto.
  apply IHb1 in Hpbis ; tauto.
  apply IHb2 in Hpbis ; tauto.
  simpl in H ; destruct H as [ Hb1 Hb2 ] ; 
    simpl ; split ; auto.
  apply IHb1 in Hpbis ; tauto.
  apply IHb2 in Hpbis ; tauto.
  simpl in H ; destruct H as [ Hb1 | Hb2 ] ; simpl ; auto.
  left ; apply IHb1 in Hpbis ; tauto.
  right ; apply IHb2 in Hpbis ; tauto.
  simpl in H ; destruct H as [ Hb1 | Hb2 ] ; simpl ; auto.
  left ; apply IHb1 in Hpbis ; tauto.
  right ; apply IHb2 in Hpbis ; tauto.
  simpl ; intro H' ; simpl in H ; apply H.
  apply IHb in Hpbis ; tauto.
  simpl ; intro H' ; simpl in H ; apply H.
  apply IHb in Hpbis ; tauto.
Qed.

(* 
 * Since partial bisimulation implies the validity of
 * B-formulas, and since the sub-formula predicate depends
 * upon B-formula validity (for the b \/ g case), partial
 * bisimulation also implies sub-formulas 
 *)
Lemma pbis_sub : forall (X X' : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop)
  (step : X -> E -> X -> Prop) (x' : X') (x : X) (f g : F),
  pbis (klts X' L' step' x') (klts X L step x) ->
  (sub X' L' x' f g <-> sub X L x f g).
Proof.
  intros X X' L' L step' step x' x f g Hpbis ;
    split ; intro Hsub ; induction Hsub ; auto.
  apply sub_refl.
  apply sub_conj_left ; auto.
  apply sub_conj_right ; auto.
  apply sub_disj ; auto.
  intro H' ; apply H ; apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply sub_box ; auto.
  apply sub_refl.
  apply sub_conj_left ; auto.
  apply sub_conj_right ; auto.
  apply sub_disj ; auto.
  intro H' ; apply H ; apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply sub_box ; auto.
Qed.

(* Partial bisimulation implies (x, f) -(e)->0 (x', f') *)
Lemma pbis_zero : forall (f : F) (X X' : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop)
  (step : X -> E -> X -> Prop) (x' y' : X') (x y : X) (f' : F) (e : E),
  pbis (klts X' L' step' x') (klts X L step x) -> step' x' e y' ->
  pbis (klts X' L' step' y') (klts X L step y) -> step x e y ->
  (zero X' L' step' (x', f) e (y', f') <-> zero X L step (x, f) e (y, f')).
Proof.
  intro f ; induction f ; intros X X' L' L step' step x' y' x y f' e' Hpbis Hstep' Hpbis' Hstep.
  split ; intro H ; inversion H ; apply zero_basic ; auto.
  split ; intro H ; inversion H.
  apply zero_conj_incl with g' ; auto.
  apply IHf1 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f') in Hpbis ; tauto.
  apply IHf2 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := g') in Hpbis ; tauto.
  apply pbis_sub with (f := g') (g := f') in Hpbis' ; tauto.
  apply zero_conj_excl ; auto.
  apply IHf1 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f'0) in Hpbis ; tauto.
  apply IHf2 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := g') in Hpbis ; tauto.
  intro H' ; apply H8.
  apply pbis_sub with (f := g') (g := f'0) in Hpbis' ; tauto.
  apply zero_conj_incl with g' ; auto.
  apply IHf1 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f') in Hpbis ; tauto.
  apply IHf2 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := g') in Hpbis ; tauto.
  apply pbis_sub with (f := g') (g := f') in Hpbis' ; tauto.
  apply zero_conj_excl ; auto.
  apply IHf1 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f'0) in Hpbis ; tauto.
  apply IHf2 with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := g') in Hpbis ; tauto.
  intro H' ; apply H8.
  apply pbis_sub with (f := g') (g := f'0) in Hpbis' ; tauto.
  split ; intro H ; inversion H.
  apply zero_disj_left ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply zero_disj_right ; auto.
  intro H' ; apply H4.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply IHf with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f') in Hpbis ; try tauto.
  apply zero_disj_left ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply zero_disj_right ; auto.
  intro H' ; apply H4.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply IHf with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f') in Hpbis ; try tauto.
  split ; intro H ; inversion H.
  apply zero_all_pos ; auto.
  apply zero_all_neg ; auto.
  apply zero_all_pos ; auto.
  apply zero_all_neg ; auto.
  split ; intro H ; inversion H.
  apply zero_ex_pos ; auto.
  apply zero_ex_neg ; auto.
  apply zero_ex_pos ; auto.
  apply zero_ex_neg ; auto.
  split ; intro H ; inversion H.
  apply zero_box_incl with f'0 ; auto.
  apply IHf with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f'0) in Hpbis ; try tauto.
  apply pbis_sub with (f := f'0) (g := f) in Hpbis' ; tauto.
  apply zero_box_excl ; auto.
  apply IHf with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f'0) in Hpbis ; try tauto.
  intro H' ; apply H6.
  apply pbis_sub with (f := f'0) (g := f) in Hpbis' ; tauto.
  apply zero_box_incl with f'0 ; auto.
  apply IHf with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f'0) in Hpbis ; try tauto.
  apply pbis_sub with (f := f'0) (g := f) in Hpbis' ; tauto.
  apply zero_box_excl ; auto.
  apply IHf with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x') (x := x)
    (y' := y') (y := y) (e := e') (f' := f'0) in Hpbis ; try tauto.
  intro H' ; apply H6.
  apply pbis_sub with (f := f'0) (g := f) in Hpbis' ; tauto.
  split ; intro H ; inversion H ; apply zero_diam ; auto.
  split ; intro H ; inversion H ; apply zero_can ; auto.
  split ; intro H ; inversion H ; apply zero_dlf ; auto.
Qed.

(* 
 * If <e>f is a sub-formula of g and if k = (X,L,-->,x)
 * such that k |= g then there exists (x, g) -(e)->0 (x',g')
 * such that (X,L,-->,x') |= g' and f is a sub-formula of g'
 *)
Lemma ex_next : forall (f g : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (e : E), 
  fval (klts X L step x) g -> sub X L x (ex e f) g ->
  exists x' : X, exists g' : F, zero X L step (x, g) e (x', g') /\
  fval (klts X L step x') g' /\ sub X L x' f g'.
Proof.
  intros f g X L step x e Hval Hsub.
  assert (exists h : F, h = ex e f) as Hex by eauto.
  destruct Hex as [ h Heq ] ; rewrite <- Heq in *.
  induction Hsub ; rewrite Heq in *.
  simpl in Hval ; destruct Hval as [ x' [ Hstep Hval' ] ].
  exists x' ; exists f ; repeat split ; apply sub_refl || auto.
  apply zero_ex_pos ; auto.
  simpl in Hval ; destruct Hval as [ Hg Hh ].
  apply IHHsub in Hg ; clear IHHsub ; auto.
  destruct Hg as [ x' [ g' [ Hred_g [ Hval_g Hsub_g ] ] ] ].
  apply val_next with (e := e) (x' := x') in Hh ; auto.
  destruct Hh as [ h' [ Hred_h Hval_h ] ].
  exists x' ; destruct (classic (sub X L x' h' g')) as [ Hsub' | Hnot_sub ].
  exists g' ; repeat split ; auto.
  apply zero_conj_incl with (g' := h') ; auto.
  exists (conj g' h') ; repeat split ; auto.
  apply zero_conj_excl ; auto.
  apply sub_conj_left ; auto.
  apply zero_impl_step in Hred_g ; auto.
  simpl in Hval ; destruct Hval as [ Hg Hh ].
  apply IHHsub in Hh ; clear IHHsub ; auto.
  destruct Hh as [ x' [ h' [ Hred_h [ Hval_h Hsub_h ] ] ] ].
  apply val_next with (e := e) (x' := x') in Hg ; auto.
  destruct Hg as [ g' [ Hred_g Hval_g ] ].
  exists x' ; destruct (classic (sub X L x' h' g')) as [ Hsub' | Hnot_sub ].
  exists g' ; repeat split ; auto.
  apply zero_conj_incl with (g' := h') ; auto.
  apply sub_trans with h' ; auto.
  exists (conj g' h') ; repeat split ; auto.
  apply zero_conj_excl ; auto.
  apply sub_conj_right ; auto.
  apply zero_impl_step in Hred_h ; auto.
  simpl in Hval ; destruct Hval as [ Hval | Hval ] ;
    contradiction || auto.
  apply IHHsub in Hval ; clear IHHsub ; auto.
  destruct Hval as [ x' [ g' [ Hred [ Hval Hsub' ] ] ] ].
  exists x' ; exists g' ; repeat split ; auto.
  apply zero_disj_right ; auto.
  assert (fval (klts X L step x) g) as Hval'.
  apply Hval ; apply trans_refl.
  apply IHHsub in Hval' ; clear IHHsub ; auto.
  destruct Hval' as [ x' [ g' [ Hred [ Hval' Hsub' ] ] ] ].
  destruct (classic (sub X L x' g' g)) as [ His_sub | Hno_sub ].
  exists x' ; exists (box g) ; repeat split ; auto.
  apply zero_box_incl with g' ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e ; auto.
  apply zero_impl_step in Hred ; auto.
  apply sub_box ; apply sub_trans with g' ; auto.
  exists x' ; exists (conj (box g) g') ; repeat split ; auto.
  apply zero_box_excl ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e ; auto.
  apply zero_impl_step in Hred ; auto.
  apply sub_conj_right ; auto.
Qed.

(* 
 * This lemma relates partial bisimulation and validity
 * over a number of uncontrollable steps 
 *)
Lemma trans_unctrl_rel : forall (n : nat) (f f' : F) (X X' : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop) (step : X -> E -> X -> Prop) 
  (x' : X') (x y : X), pbis (klts X' L' step' x') (klts X L step x) -> 
  trans (X * F) (unctrl (X * F) (rel n X L step)) (x, f) (y, f') ->
  fval (klts X' L' step' x') f -> wf f -> exists y' : X',
  pbis (klts X' L' step' y') (klts X L step y) /\
  fval (klts X' L' step' y') f' /\ wf f'.
Proof.
  intros n f f' X X' L' L step' step x' x y Hpbis Htrans Hval Hwf.
  assert (exists xf : X * F, xf = (x, f)) as Hex by eauto.
  assert (exists yf' : X * F, yf' = (y, f')) as Hex' by eauto.
  destruct Hex as [ xf Heq ] ; rewrite <- Heq in *.
  destruct Hex' as [ yf' Heq' ] ; rewrite <- Heq' in *.
  revert Heq Heq' Hpbis Hval Hwf ; revert x f y f' x'.
  induction Htrans ; intros z f z' f' x'' Heq Heq' Hpbis Hval Hwf.
  rewrite Heq in * ; inversion Heq'.
  replace z with z' in * by auto ; replace f with f' in * by auto.
  exists x'' ; repeat split ; auto.
  unfold unctrl in H ; destruct H as [ Hrel HU ].
  rewrite Heq in * ; destruct y as [ w g ].
  assert (step z e w) as Hstep.
  apply rel_impl_zero in Hrel ; apply zero_impl_step in Hrel ; auto.
  assert (zero X L step (z, f) e (w, g)) as Hred.
  apply rel_impl_zero in Hrel ; auto.
  assert (pbis (klts X' L' step' x'') (klts X L step z)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep ; auto.
  destruct Hstep as [ w' [ Hstep' HR ] ].
  apply wf_next with (f' := g) (x' := w') (e := e) in Hval ; auto.
  apply IHHtrans with (x := w) (f := g) (x'0 := w') ; auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step := step) (step' := step') (x' := x'') (y' := w')
    (x := z) (y := w) (f := f) (e := e) (f' := g) in Hpbis' ; try tauto.
  exists R ; split ; auto.
  apply rel_impl_zero in Hrel ; apply zero_impl_step in Hrel ; auto.
Qed.

(*
 * This is the hardest lemma of the entire proof. It
 * details how a partial bisimulant, which satisifies a
 * formula g, implies synthesizability for f, if f is a
 * sub-formula of g. Note how this requires the well-formedness
 * test: it is absolutely required that <e>f formulas are
 * restricted in such a way that e is controllable
 *)
Lemma pbis_impl_syn : forall (n : nat) (f g : F) (X X' : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop) (step : X -> E -> X -> Prop) 
  (x' : X') (x : X), pbis (klts X' L' step' x') (klts X L step x) ->
  wf g -> fval (klts X' L' step' x') g -> sub X L x f g -> syn X L (rel n X L step) (x, g) f.
Proof.
  intro n ; induction n ; intro f ; induction f ;
    intros g X X' L' L step' step x' x Hpbis Hwf Hval Hsub.
  apply syn_basic ; apply sub_val with (f := basic b) in Hval.
  simpl in Hval ; apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply pbis_sub with (f := basic b) (g := g) in Hpbis ; tauto.
  apply sub_conj in Hsub ; destruct Hsub ; apply syn_conj ; auto.
  apply IHf1 with X' L' step' x' ; auto.
  apply IHf2 with X' L' step' x' ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  apply syn_disj_left ; auto.
  apply sub_disj_not in Hsub ; auto.
  apply syn_disj_right.
  apply IHf with X' L' step' x' ; auto.
  apply syn_all.
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  apply ex_next with (e := e) (f := f) in Hval ; auto.
  destruct Hval as [ y' [ g' [ Hred [ Hval Hsub' ] ] ] ].
  destruct Hpbis as [ R [ HinR HrelR ] ].
  assert (step' x' e y') as Hstep'.
  apply zero_impl_step in Hred ; auto.
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_ex with y g' ; simpl ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := x') (x := x)
    (y' := y') (y := y) (f := g) (e := e) (f' := g') in Hpbis' ; try tauto.
  apply zero_impl_step in Hred ; auto.
  exists R ; split ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis''.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis'' ; tauto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis''.
  exists R ; split ; auto.
  apply IHf with (g := g') in Hpbis'' ; simpl in * ; auto.  
  apply wf_zero in Hred ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis'' ; tauto.
  apply pbis_sub with (f := ex e f) (g := g) in Hpbis ; tauto.
  apply syn_box ; apply IHf with X' L' step' x' ; auto.
  apply sub_trans_box with step x g 0 ; apply trans_refl || auto ; auto.
  apply sub_val with (f := diam b) in Hval ; auto.
  simpl in Hval ; destruct Hval as [ y' [ Htrans Hbval ] ].
  clear Hsub ; revert Hpbis Hwf ; revert x g.
  induction Htrans ; intros z g Hpbis Hwf.
  apply syn_diam with z g ; apply trans_refl || auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  destruct Hpbis as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in H ; destruct H as [ z' [ Hstep HR ] ].
  destruct (zero_ex g X L step z z' e) as [ g' Hred ] ; auto.
  apply IHHtrans with (x := z') (g := g') in Hbval ; auto.
  inversion Hbval.
  apply syn_diam with x'0 g'0 ; auto.
  apply trans_closed with (z', g') e ; auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_sub with (f := diam b) (g := g) in Hpbis ; tauto.
  apply sub_val with (f := can e) in Hval ; auto.
  simpl in Hval ; destruct Hval as [ y' Hstep ].
  destruct Hpbis as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in Hstep ; destruct Hstep as [ y [ Hstep HR ] ].
  destruct (zero_ex g X L step x y e) as [ g' Hred ] ; auto.
  apply syn_can with y g' ; auto.
  apply pbis_sub with (f := can e) (g := g) in Hpbis ; tauto.
  apply sub_val with (f := dlf) in Hval ; auto.
  simpl in Hval ; destruct Hval as [ e [ y' Hstep ] ].
  destruct Hpbis as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  apply HinR in Hstep ; destruct Hstep as [ y [ Hstep HR ] ].
  destruct (zero_ex g X L step x y e) as [ g' Hred ] ; auto.
  apply syn_dlf with y e g' ; auto.
  apply pbis_sub with (f := dlf) (g := g) in Hpbis ; tauto.

  (* Inductive case for n *)
  apply syn_basic ; apply sub_val with (f := basic b) in Hval.
  simpl in Hval ; apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply pbis_sub with (f := basic b) (g := g) in Hpbis ; tauto.
  apply sub_conj in Hsub ; destruct Hsub ; apply syn_conj ; auto.
  apply IHf1 with X' L' step' x' ; auto.
  apply IHf2 with X' L' step' x' ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  apply syn_disj_left ; auto.
  apply sub_disj_not in Hsub ; auto.
  apply syn_disj_right.
  apply IHf with X' L' step' x' ; auto.  
  apply syn_all.
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  apply ex_next with (e := e) (f := f) in Hval ; auto.
  destruct Hval as [ y' [ g' [ Hred [ Hval Hsub' ] ] ] ].
  destruct Hpbis as [ R [ HinR HrelR ] ].
  assert (step' x' e y') as Hstep'.
  apply zero_impl_step in Hred ; auto.
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_ex with y g' ; auto.
  simpl ; split ; auto.
  apply rel_ex ; auto.
  intros z g'' Htrans.
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Hpbis'' [ Hval' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := z') ; auto.
  apply sub_refl.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := x') (x := x)
    (y' := y') (y := y) (f := g) (e := e) (f' := g') in Hpbis' ; try tauto.
  apply zero_impl_step in Hred ; auto.
  exists R ; split ; auto.
  right ; intros xf'' Htrans.
  destruct xf'' as [ z g'' ].
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Hpbis'' [ Hval' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := z') ; auto.
  simpl ; apply sub_refl.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis''.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis'' ; tauto.
  apply IHf with (X' := X') (L' := L') (step' := step') (x' := y') ; auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis''.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis'' ; tauto.
  apply pbis_sub with (f := ex e f) (g := g) in Hpbis' ; tauto.
  apply syn_box ; apply IHf with (X' := X') (L' := L')
    (step' := step') (x' := x') ; auto.
  apply sub_trans_box with (step := step) (x' := x)
    (g' := g) (n := n) in Hsub ; apply trans_refl || auto.
  assert (fval (klts X' L' step' x') g) as Hval' by auto.
  apply sub_val with (f := diam b) in Hval' ; auto.
  simpl in Hval' ; destruct Hval' as [ y' [ Htrans Hbval ] ].
  clear Hsub ; revert Hpbis Hwf Hval Hbval ; revert x g.
  induction Htrans ; intros z g Hpbis Hwf Hval Hbval.
  apply syn_diam with z g ; apply trans_refl || auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  assert (pbis (klts X' L' step' x) (klts X L step z)) as Hpbis' by auto.
  destruct Hpbis' as [ R [ HinR HrelR ] ] ; apply HrelR in HinR.
  assert (step' x e y) as Hstep' by auto.
  apply HinR in H ; destruct H as [ w [ Hstep HR ] ].
  apply val_next with (x' := y) (e := e) in Hval ; auto.
  destruct Hval as [ g' [ Hred Hval ] ].
  assert (pbis (klts X' L' step' y) (klts X L step w)) as Hpbis'.
  exists R ; split ; auto.
  apply IHHtrans with (g := g') in Hpbis' ; auto.
  inversion Hpbis'.
  apply syn_diam with x'0 g'0 ; auto.
  apply trans_closed with (w, g') e ; auto.
  simpl ; split ; auto.
  apply rel_ex ; auto.
  intros w' g'' Htrans'.
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y) in Htrans' ; auto.
  destruct Htrans' as [ y' [ Hpbis'' [ Hval' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := y') ; auto.
  apply sub_refl.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := x) (x := z)
    (y' := y) (y := w) (f := g) (e := e) (f' := g') in Hpbis ; try tauto.
  exists R ; split ; auto.
  right ; intros xf'' Htrans' ; destruct xf'' as [ w' g'' ].
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y) in Htrans' ; auto.
  destruct Htrans' as [ y' [ Hpbis'' [ Hval' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := y') ; auto.
  apply sub_refl.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_sub with (f := diam b) (g := g) in Hpbis ; tauto.
  assert (fval (klts X' L' step' x') g) as Hval' by auto.
  apply sub_val with (f := can e) in Hval' ; auto.
  simpl in Hval' ; destruct Hval' as [ y' Hstep ].
  assert (step' x' e y') as Hstep' by auto.
  apply val_next with (f := g) (X := X') (L := L')
    (step := step') (x := x') (e := e) (x' := y') in Hstep ; auto.
  destruct Hstep as [ g' [ Hred Hval' ] ].
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep' ; auto.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_can with (x' := y) (g' := g') ; auto.
  simpl ; split ; auto.
  apply rel_ex ; auto.
  intros z g'' Htrans.
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Hpbis'' [ Hval'' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := z') ; apply sub_refl || auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := x') (x := x)
    (y' := y') (y := y) (f := g) (e := e) (f' := g') in Hpbis' ; try tauto.
  apply zero_impl_step in Hred ; auto.
  exists R ; split ; auto.
  right ; intros xf'' Htrans ; destruct xf'' as [ z g'' ].
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Hpbis'' [ Hval'' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := z') ; apply sub_refl || auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_sub with (f := can e) (g := g) in Hpbis ; tauto.
  assert (fval (klts X' L' step' x') g) as Hval' by auto.
  apply sub_val with (f := dlf) in Hval' ; auto.
  simpl in Hval' ; destruct Hval' as [ e [ y' Hstep ] ].
  assert (step' x' e y') as Hstep' by auto.
  apply val_next with (f := g) (X := X') (L := L')
    (step := step') (x := x') (e := e) (x' := y') in Hstep ; auto.
  destruct Hstep as [ g' [ Hred Hval' ] ].
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep' ; auto.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_dlf with (e := e) (x' := y) (g' := g') ; auto.
  simpl ; split ; auto.
  apply rel_ex ; auto.
  intros z g'' Htrans.
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Hpbis'' [ Hval'' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := z') ; apply sub_refl || auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := x') (x := x)
    (y' := y') (y := y) (f := g) (e := e) (f' := g') in Hpbis' ; try tauto.
  apply zero_impl_step in Hred ; auto.
  exists R ; split ; auto.
  right ; intros xf'' Htrans ; destruct xf'' as [ z g'' ].
  apply trans_unctrl_rel with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Hpbis'' [ Hval'' Hwf' ] ] ].
  apply IHn with (X' := X') (L' := L') (step' := step')
    (x' := z') ; apply sub_refl || auto.
  exists R ; split ; auto.
  apply wf_zero in Hred ; auto.
  apply pbis_sub with (f := dlf) (g := g) in Hpbis ; tauto.
Qed.

(* Prove that the synthesis result is maximal *)
Theorem maximality : forall (k' k : K) (f : F) (n : nat),
  wf f -> pbis k' k -> fval k' f -> pbis k' (S k f n).
Proof.
  intros k' k f n Hwf Hpbis Hval ; destruct k' as [ X' L' step' x' ].
  destruct k as [ X L step x ] ; destruct Hpbis as [ R [ HinR HrelR ] ].
  exists (fun y' yg => R y' (fst yg) /\ wf (snd yg) /\ 
    fval (klts X' L' step' y') (snd yg)) ; split ; auto.
  intros y' yg H ; destruct H as [ HR [ Hwf' Hval' ] ].
  destruct yg as [ y g ] ; simpl in HR ; simpl in Hval' ; simpl.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  apply HrelR in HR ; split ; [ tauto | split ].
  intros e z' Hstep'.
  assert (exists f' : F, zero X' L' step' (y', g) e (z', f') /\ 
    fval (klts X' L' step' z') f') as Hex.
  apply val_next ; auto.
  destruct Hex as [ g' [ Hred Hval'' ] ].
  apply HR in Hstep' ; destruct Hstep' as [ z [ Hstep HR' ] ].
  exists (z, g') ; repeat split ; auto.
  apply rel_ex ; auto.
  intros w g'' Htrans.
  assert (wf g') as Hwf''.
  apply wf_zero in Hred ; auto.
  assert (exists w' : X', trans X' step' z' w' /\ wf g'' /\
    R w' w /\ fval (klts X' L' step' w') g'') as H.
  clear HinR HR Hstep Hred Hval' Hwf Hval.
  assert (exists zg' : X * F, zg' = (z, g')) as Heq by eauto.
  assert (exists wg'' : X * F, wg'' = (w, g'')) as Heq' by eauto.
  destruct Heq as [ zg' Heq ] ; rewrite <- Heq in *.
  destruct Heq' as [ wg'' Heq' ] ; rewrite <- Heq' in *.
  revert Heq Heq' HR' Hval'' Hwf'' ; revert z g' w g'' z'.
  induction Htrans ; intros z g' w g'' z' Heq Heq' HR Hval Hwf.
  rewrite Heq in * ; inversion Heq'.
  replace g' with g'' in * ; auto.
  replace z with w in * ; auto.
  exists z' ; repeat split ; apply trans_refl || auto ; auto.
  rewrite Heq in * ; unfold unctrl in H.
  destruct H as [ Hrel HU ] ; destruct y0 as [ v h ].
  assert (step z e0 v) as Hstep.
  apply rel_impl_zero in Hrel ; apply zero_impl_step in Hrel ; auto.
  assert (zero X L step (z, g') e0 (v, h)) as Hred.
  apply rel_impl_zero in Hrel ; auto.
  assert (pbis (klts X' L' step' z') (klts X L step z)) as Hpbis'.
  exists R ; split ; auto.
  apply HrelR in HR ; apply HR in Hstep ; auto.
  destruct Hstep as [ v' [ Hstep' HR' ] ] ; clear HR.
  assert (fval (klts X' L' step' v') h) as Hval'.
  apply wf_next with g' z' e0 ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := z') (x := z)
    (y' := v') (y := v) (f := g') (e := e0) (f' := h) in Hpbis' ; try tauto.
  exists R ; split ; auto.
  apply zero_impl_step in Hred ; auto.
  apply IHHtrans with (z := v) (w := w) (g'' := g'') 
    in Hval' ; auto.
  destruct Hval' as [ w' [ Htrans' [ Hwf'' [ HR'' Hval' ] ] ] ].
  exists w' ; repeat split ; auto.
  apply trans_closed with v' e0 ; auto.
  apply wf_zero in Hred ; auto.
  destruct H as [ w' [ _ [ Hwf''' [ HR'' Hval''' ] ] ] ].
  apply pbis_impl_syn with (X' := X') (L' := L')
    (step' := step') (x' := w') ; auto.
  exists R ; split ; auto.
  apply sub_refl.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := y') (x := y)
    (y' := z') (y := z) (f := g) (e := e) (f' := g') in Hpbis ; try tauto.
  apply zero_impl_step in Hred ; auto.
  exists R ; split ; auto.
  simpl in * ; apply wf_zero in Hred ; auto.
  intros e z HU Hrel ; destruct z as [ z g' ].
  assert (zero X L step (y, g) e (z, g')) as Hred.
  apply rel_impl_zero in Hrel ; auto.
  apply zero_impl_step in Hred.
  apply HR in Hred ; auto.
  destruct Hred as [ z' [ Hstep' HR' ] ].
  exists z' ; repeat split ; auto.
  apply rel_impl_zero in Hrel.
  apply wf_zero in Hrel ; simpl in * ; auto.
  simpl in * ; apply wf_next with g y' e ; auto.
  apply pbis_zero with (X := X) (X' := X') (L := L) (L' := L')
    (step' := step') (step := step) (x' := y') (x := y)
    (y' := z') (y := z) (f := g) (e := e) (f' := g') in Hpbis ; try tauto.
  apply rel_impl_zero in Hrel ; tauto.
  exists R ; split ; auto.
  apply rel_impl_zero in Hrel ; apply zero_impl_step in Hrel ; auto.
Qed.
