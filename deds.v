Axiom classic : forall (P : Prop), P \/ ~ P.

Parameter E P : Set.
Parameter U : E -> Prop.

Inductive K : Type := klts : forall (X : Set),
  (X -> P -> Prop) -> (X -> E -> X -> Prop) -> X -> K.

Inductive trans (X : Set) (step : X -> E -> X -> Prop) : X -> X -> Prop :=
  | trans_refl : forall (x : X), trans X step x x
  | trans_closed : forall (x y x' : X) (e : E), step x e y ->
    trans X step y x' -> trans X step x x'.

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

Inductive B : Set :=
  | true : B
  | false : B
  | prop : P -> B
  | neg : B -> B
  | and : B -> B -> B
  | or : B -> B -> B.

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

Fixpoint wf (f : F) : Prop :=
  match f with
  | conj f g => wf f /\ wf g
  | disj b f => wf f
  | all e f => wf f
  | ex e f => ~ U e /\ wf f
  | box f => wf f
  | _ => True
  end.

Fixpoint bval (X : Set) (L : X -> P -> Prop) (x : X) (b : B) : Prop :=
  match b with
  | true => True
  | false => False
  | prop p => L x p
  | neg b => ~ bval X L x b
  | and b c => bval X L x b /\ bval X L x c
  | or b c => bval X L x b \/ bval X L x c
  end.

Fixpoint val (k : K) (f : F) : Prop :=
  match (k, f) with
  | (klts X L step x, basic b) => bval X L x b
  | (_, conj f g) => val k f /\ val k g
  | (klts X L step x, disj b f) => bval X L x b \/ val k f
  | (klts X L step x, all e f) => forall (x' : X),
    step x e x' -> val (klts X L step x') f
  | (klts X L step x, ex e f) => exists x' : X,
    step x e x' /\ val (klts X L step x') f
  | (klts X L step x, box f) => forall (x' : X),
    trans X step x x' -> val (klts X L step x') f
  | (klts X L step x, diam b) => exists x' : X,
    trans X step x x' /\ bval X L x' b
  | (klts X L step x, can e) => exists x' : X, step x e x'
  | (klts X L step x, dlf) => exists e : E, exists x' : X, step x e x'
  end.

Inductive red (X : Set) (L : X -> P -> Prop) (x : X) : F -> E -> F -> Prop :=
  | red_basic : forall (b : B) (e : E), red X L x (basic b) e (basic true)
  | red_and : forall (f g f' g' : F) (e : E), red X L x f e f' ->
    red X L x g e g' -> red X L x (conj f g) e (conj f' g')
  | red_or_left : forall (f : F) (b : B) (e : E), 
    bval X L x b -> red X L x (disj b f) e (basic true)
  | red_or_right : forall (f f' : F) (b : B) (e : E),
    ~ bval X L x b -> red X L x f e f' -> red X L x (disj b f) e f'
  | red_all_pos : forall (f : F) (e : E), red X L x (all e f) e f
  | red_all_neg : forall (f : F) (e e' : E), e <> e' -> red X L x (all e f) e' (basic true)
  | red_ex_pos : forall (f : F) (e : E), red X L x (ex e f) e f
  | red_ex_neg : forall (f : F) (e e' : E), red X L x (ex e f) e' (basic true)
  | red_box : forall (f f' : F) (e : E), red X L x f e f' ->
    red X L x (box f) e (conj (box f) f')
  | red_diam : forall (b : B) (e : E), red X L x (diam b) e (basic true)
  | red_can : forall (e e' : E), red X L x (can e) e' (basic true)
  | red_dlf : forall (e : E), red X L x dlf e (basic true).

Inductive sub (X : Set) (L : X -> P -> Prop) (x : X) : F -> F -> Prop :=
  | sub_refl : forall (f : F), sub X L x f f
  | sub_and_left : forall (f g h : F), sub X L x f g -> sub X L x f (conj g h)
  | sub_and_right : forall (f g h : F), sub X L x f h -> sub X L x f (conj g h)
  | sub_or : forall (f g : F) (b : B), ~ bval X L x b -> 
    sub X L x f g -> sub X L x f (disj b g)
  | sub_box : forall (f g : F), sub X L x f g -> sub X L x f (box g).

Inductive syn (X : Set) (L : X -> P -> Prop)
    (step : X * F -> E -> X * F -> Prop) : X * F -> F -> Prop :=
  | syn_basic : forall (x : X) (b : B) (g : F), bval X L x b -> syn X L step (x, g) (basic b)
  | syn_and : forall (x : X) (f1 f2 g : F), syn X L step (x, g) f1 ->
    syn X L step (x, g) f2 -> syn X L step (x, g) (conj f1 f2)
  | syn_or_left : forall (x : X) (b : B) (f g : F),
    bval X L x b -> syn X L step (x, g) (disj b f)
  | syn_or_right : forall (x : X) (b : B) (f g : F),
    syn X L step (x, g) f -> syn X L step (x, g) (disj b f)
  | syn_all : forall (x : X) (f g : F) (e : E), syn X L step (x, g) (all e f)
  | syn_ex : forall (x x' : X) (f g g' : F) (e : E),
    step (x, g) e (x', g') -> sub X L x' f g' ->
    syn X L step (x', g') f -> syn X L step (x, g) (ex e f)
  | syn_box : forall (x : X) (f g : F), syn X L step (x, g) f -> 
    syn X L step (x, g) (box f)
  | syn_diam : forall (x x' : X) (b : B) (g g' : F),
    trans (X * F) step (x, g) (x', g') -> bval X L x' b ->
    syn X L step (x, g) (diam b)
  | syn_can : forall (x x' : X) (g g' : F) (e : E),
    step (x, g) e (x', g') -> syn X L step (x, g) (can e)
  | syn_dlf : forall (x x' : X) (g g' : F) (e : E),
    step (x, g) e (x', g') -> syn X L step (x, g) dlf.

Definition unctrl (X : Set) (step : X -> E -> X -> Prop) (x : X) (e : E) (x' : X) : Prop :=
  step x e x' /\ U e.

Fixpoint rel (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (xf : X * F) (e : E) (xf' : X * F) : Prop :=
  match n with
  | 0 => step (fst xf) e (fst xf') /\ red X L (fst xf) (snd xf) e (snd xf')
  | S n => rel n X L step xf e xf' /\ (U e \/
    forall (xf'' : X * F), trans (X * F) (unctrl (X * F) (rel n X L step)) xf' xf'' -> 
    syn X L (rel n X L step) xf'' (snd xf''))
  end.

Definition S (k : K) (f : F) (n : nat) : K :=
  match k with
  | klts X L step x => 
    klts (X * F) (fun xf => L (fst xf)) (rel n X L step) (x, f)
  end.

Definition complete (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (f : F) : Prop :=
    forall (x' : X) (f' : F), trans (X * F) (rel n X L step) (x, f) (x', f') ->
      syn X L (rel n X L step) (x', f') f'.

Lemma trans_cat : forall (X : Set) (step : X -> E -> X -> Prop) (x y z : X),
  trans X step x y -> trans X step y z -> trans X step x z.
Proof.
  intros X step x y z H H' ; induction H ; auto.
  apply trans_closed with y e ; auto.
Qed.

Lemma complete_impl_syn : forall (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (f : F) (n : nat),
  complete n X L step x f -> syn X L (rel n X L step) (x, f) f.
Proof.
  intros X L step x f n Hcomplete ; unfold complete in *.
  apply Hcomplete ; apply trans_refl.
Qed.

Lemma bval_expand : forall (X : Set) (L : X -> P -> Prop) (x : X) (g : F) (b : B),
  bval X L x b <-> bval (X * F) (fun xf => L (fst xf)) (x, g) b.
Proof.
  intros X L x g b ; induction b ; split ; intro H ;
    solve [ simpl in * ; tauto ] || idtac.
Qed.

Lemma rel_impl_step_red : forall (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (e : E) (f f' : F),
    rel n X L step (x, f) e (x', f') -> step x e x' /\ red X L x f e f'.
Proof.
  intro n ; induction n ; intros X L step x x' e f f' Hrel ;
    simpl in * ; destruct Hrel ; auto.
Qed.

Lemma sub_syn : forall (X : Set) (L : X -> P -> Prop) 
  (step : X -> E -> X -> Prop) (x : X) (f g h : F) (n : nat),
  sub X L x f g -> syn X L (rel n X L step) (x, h) g ->
  syn X L (rel n X L step) (x, h) f.
Proof.
  intros X L step x f g h n Hsub Hsyn ; induction Hsub ; 
    solve [ auto ] || solve [ inversion Hsyn ; auto ] || auto.
  inversion Hsyn ; contradiction || auto.
Qed.

Lemma sub_and : forall (X : Set) (L : X -> P -> Prop) (x : X) (f g h : F),
  sub X L x (conj f g) h -> sub X L x f h /\ sub X L x g h.
Proof.
  intros X L x f g h Hsub ; assert (exists i : F, i = conj f g) as H by eauto.
  destruct H as [ i H ] ; rewrite <- H in *.
  induction Hsub ; rewrite H in *.
  split ; [ apply sub_and_left | apply sub_and_right ] ; apply sub_refl.
  split ; apply sub_and_left ; tauto.
  split ; apply sub_and_right ; tauto.
  split ; apply sub_or ; tauto.
  split ; apply sub_box ; tauto.
Qed.

Lemma sub_not_or : forall (X : Set) (L : X -> P -> Prop) (x : X) (b : B) (f g : F),
  ~ bval X L x b -> sub X L x (disj b f) g -> sub X L x f g.
Proof.
  intros X L x b f g Hbval Hsub ; assert (exists h : F, h = disj b f) as H by eauto.
  destruct H as [ i H ] ; rewrite <- H in *.
  induction Hsub ; rewrite H in *.
  apply sub_or ; apply sub_refl || auto.
  apply sub_and_left ; auto.
  apply sub_and_right ; auto.
  apply sub_or ; auto.
  apply sub_box ; auto.
Qed.

Lemma sub_all : forall (X : Set) (L : X -> P -> Prop) (x x' : X) (e : E) (f g g' : F),
  sub X L x (all e f) g -> red X L x g e g' -> sub X L x' f g'.
Proof.
  intros X L x x' e f g g' Hsub Hred ; assert (exists h : F, h = all e f) as H by eauto.
  destruct H as [ h H ] ; rewrite <- H in *.
  revert Hred ; revert g' ; induction Hsub ; rewrite H in * ; intros g' Hred.
  inversion Hred ; apply sub_refl || auto.
  assert (e = e) by auto ; contradiction.
  inversion Hred ; apply IHHsub in H2 ; apply sub_and_left || auto ; auto.
  inversion Hred ; apply IHHsub in H5 ; apply sub_and_right || auto ; auto.
  inversion Hred ; contradiction || auto.
  inversion Hred ; apply IHHsub in H1 ; auto.
  apply sub_and_right ; auto.
Qed.

Lemma sub_box_impl : forall (X : Set) (L : X -> P -> Prop) (x : X) 
    (f g h : F), h = box f -> sub X L x h g -> sub X L x f g.
Proof.
  intros X L x f g h Heq Hsub ; induction Hsub ; rewrite Heq in *.
  apply sub_box ; apply sub_refl ; auto.
  apply sub_and_left ; auto.
  apply sub_and_right ; auto.
  apply sub_or ; auto.
  apply sub_box ; auto.
Qed.

Lemma sub_box_trans : forall (n : nat) (X : Set)
  (L : X -> P -> Prop) (step : X -> E -> X -> Prop)
  (x x' : X) (f g g' : F), sub X L x (box f) g ->
  trans (X * F) (rel n X L step) (x, g) (x', g') -> sub X L x' f g'.
Proof.
  assert (forall (X : Set) (L : X -> P -> Prop) (x x' : X)
    (f g h : F) (e : E), h = box f -> sub X L x h g -> 
    forall (g' : F), red X L x g e g' -> sub X L x' h g') as Hsub_red.
  intros X L x x' f g h e Heq Hsub ; induction Hsub ;
    rewrite Heq in * ; intros g' Hred.
  inversion Hred ; apply sub_and_left ; apply sub_refl.
  inversion Hred ; apply IHHsub in H1 ; apply sub_and_left || auto ; auto.
  inversion Hred ; apply IHHsub in H4 ; apply sub_and_right || auto ; auto.
  inversion Hred ; contradiction || auto.
  inversion Hred ; apply IHHsub in H0 ; apply sub_and_right || auto ; auto.
  assert (forall (X : Set) (L : X -> P -> Prop) (x : X) (f g h : F),
    h = box f -> sub X L x h g -> sub X L x f g) as Hsub_box.
  intros X L x f g h Heq Hsub ; induction Hsub ; rewrite Heq in *.
  apply sub_box ; apply sub_refl ; auto.
  apply sub_and_left ; auto.
  apply sub_and_right ; auto.
  apply sub_or ; auto.
  apply sub_box ; auto.
  intros n X L step x x' f g g' Hsub Htrans.
  assert (exists xg : X * F, xg = (x, g)) as Hex by eauto.
  assert (exists xg' : X * F, xg' = (x', g')) as Hex' by eauto.
  destruct Hex as [ xg Heq ] ; rewrite <- Heq in *.
  destruct Hex' as [ xg' Heq' ] ; rewrite <- Heq' in *.
  revert Heq Hsub ; revert x g.
  induction Htrans ; intros z g Heq Hsub ; rewrite Heq in *.
  inversion Heq' ; replace x' with z in * by auto.
  replace g' with g in * by auto.
  apply Hsub_box with (f := f) in Hsub ; auto.
  destruct y as [ y h ] ; apply rel_impl_step_red in H.
  destruct H as [ _ Hred ].
  assert ((y, h) = (y, h)) as H by auto.
  apply IHHtrans in H ; auto.
  apply Hsub_red with (x' := y) (f := f) (e := e) 
    (g' := h) in Hsub ; auto.
Qed.

Lemma sub_val : forall (f g : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X), sub X L x f g ->
  val (klts X L step x) g -> val (klts X L step x) f.
Proof.
  intros f g X L step x Hsub Hval ; induction Hsub ; auto.
  simpl in Hval ; destruct Hval ; auto.
  simpl in Hval ; destruct Hval ; auto.
  simpl in Hval ; destruct Hval ; contradiction || auto.
  apply IHHsub ; apply Hval ; apply trans_refl.
Qed.

Theorem validity : forall (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (f : F) (n : nat),
  complete n X L step x f -> val (S (klts X L step x) f n) f.
Proof.
  intros X L step x f n ; assert (sub X L x f f) as Hsub by apply sub_refl.
  revert Hsub ; revert x ; generalize f at 2 3 4 as g.
  induction f ; intros g x Hsub Hcomplete.
  apply complete_impl_syn in Hcomplete.
  apply sub_syn with (f := basic b) in Hcomplete ; auto.
  inversion Hcomplete ; simpl ; apply bval_expand ; auto.
  apply sub_and in Hsub ; destruct Hsub ; split ; auto.
  destruct (classic (bval X L x b)) as [ H | H ].
  simpl ; left ; apply bval_expand ; auto.
  simpl ; right ; apply sub_not_or in Hsub ; apply IHf || auto ; auto.
  simpl ; intros xg' Hstep ; destruct xg' as [ x' g' ] ; apply IHf ; auto.
  apply rel_impl_step_red in Hstep ; destruct Hstep as [ _ Hred ].
  apply sub_all with (x' := x') (g' := g') (f := f) in Hred ; auto.
  intros x'' g'' Htrans ; apply Hcomplete ; apply trans_closed with (x', g') e ; auto.
  assert (complete n X L step x g) as Hcomplete' by auto.
  apply complete_impl_syn in Hcomplete.
  apply sub_syn with (f := ex e f) in Hcomplete ; auto.
  inversion Hcomplete ; exists (x', g') ; split ; solve [ auto ] || apply IHf ; auto.
  intros x'' g'' Htrans ; apply Hcomplete' ; apply trans_closed with (x', g') e ; auto.  
  simpl ; intros x' Htrans ; destruct x' as [ x' g' ].
  apply IHf ; auto.
  apply sub_box_trans with (f := f) in Htrans ; auto.
  intros x'' g'' Htrans' ; apply Hcomplete.
  apply trans_cat with (x', g') ; auto.
  apply complete_impl_syn in Hcomplete.
  apply sub_syn with (f := diam b) in Hcomplete ; auto.
  inversion Hcomplete ; exists (x', g') ; split ; auto.
  apply bval_expand ; auto.
  apply complete_impl_syn in Hcomplete.
  apply sub_syn with (f := can e) in Hcomplete ; auto.
  inversion Hcomplete ; exists (x', g') ; auto.
  apply complete_impl_syn in Hcomplete.
  apply sub_syn with (f := dlf) in Hcomplete ; auto.
  inversion Hcomplete ; exists e ; exists (x', g') ; auto.
Qed.

Lemma red_ex : forall (X : Set) (L : X -> P -> Prop) (x : X) (f : F) (e : E),
  exists f' : F, red X L x f e f'.
Proof.
  intros X L x f e ; induction f.
  exists (basic true) ; apply red_basic.
  destruct IHf1 as [ f1' Hred_f1 ].
  destruct IHf2 as [ f2' Hred_f2 ].
  exists (conj f1' f2') ; apply red_and ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  exists (basic true) ; apply red_or_left ; auto.
  destruct IHf as [ f' Hred ].
  exists f' ; apply red_or_right ; auto.
  destruct (classic (e = e0)) as [ H | H ].
  rewrite <- H in * ; exists f ; apply red_all_pos ; auto.
  exists (basic true) ; apply red_all_neg ; auto.
  exists (basic true) ; apply red_ex_neg ; auto.
  destruct IHf as [ f' Hred ].
  exists (conj (box f) f') ; apply red_box ; auto.
  exists (basic true) ; apply red_diam.
  exists (basic true) ; apply red_can.
  exists (basic true) ; apply red_dlf.
Qed.

Lemma unctrl_ex : forall (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (f f' : F) (e : E),
  step x e x' -> red X L x f e f' -> U e -> rel n X L step (x, f) e (x', f').
Proof.
  intro n ; induction n ; 
    intros X L step x x' f f' e Hstep Hred HU.
  simpl ; split ; auto.
  simpl ; split ; auto.
Qed.

Theorem controllability : forall (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (f : F) (n : nat),
  pbis (S (klts X L step x) f n) (klts X L step x).
Proof.
  intros X L step x f n.
  exists (fun yg y => fst yg = y) ; split ; auto.
  intros yg y' H ; destruct yg as [ y g ] ; simpl in H.
  rewrite <- H in * ; split ; [ simpl ; tauto | split ] ; clear H y'.
  intros e yg' Hrel ; destruct yg' as [ y' g' ].
  apply rel_impl_step_red in Hrel ; destruct Hrel as [ Hstep _ ].
  exists y' ; repeat split ; simpl ; auto.
  intros e y' HU Hstep ; destruct (red_ex X L y g e) as [ g' Hred ].
  exists (y', g') ; repeat split ; auto.
  apply unctrl_ex ; auto.
Qed.


Lemma pbis_bval : forall (b : B) (X' X : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop)
  (step : X -> E -> X -> Prop) (x' : X') (x : X),
  pbis (klts X' L' step' x') (klts X L step x) ->
  (bval X' L' x' b <-> bval X L x b).
Proof.
  intro b ; induction b ; intros X' X L' L step' step x' x Hpbis ; 
    split ; intro H ; solve [ simpl in * ; tauto ] || idtac.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in H ; simpl ; auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in H ; simpl ; auto.
  apply IHb in Hpbis ; intro H' ; apply H ; tauto.
  apply IHb in Hpbis ; intro H' ; apply H ; tauto.
  simpl in H ; destruct H as [ Hb1 Hb2 ] ; split ; auto.
  apply IHb1 in Hpbis ; apply Hpbis ; auto.
  apply IHb2 in Hpbis ; apply Hpbis ; auto.
  simpl in H ; destruct H as [ Hb1 Hb2 ] ; split ; auto.
  apply IHb1 in Hpbis ; apply Hpbis ; auto.
  apply IHb2 in Hpbis ; apply Hpbis ; auto.
  simpl in H ; destruct H as [ Hb1 | Hb2 ] ; auto.
  left ; apply IHb1 in Hpbis ; apply Hpbis ; auto.
  right ; apply IHb2 in Hpbis ; apply Hpbis ; auto.
  simpl in H ; destruct H as [ Hb1 | Hb2 ] ; auto.
  left ; apply IHb1 in Hpbis ; apply Hpbis ; auto.
  right ; apply IHb2 in Hpbis ; apply Hpbis ; auto.
Qed.

Lemma pbis_sub : forall (f g : F) (X' X : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop)
  (step : X -> E -> X -> Prop) (x' : X') (x : X),
  pbis (klts X' L' step' x') (klts X L step x) ->
  (sub X' L' x' f g <-> sub X L x f g).
Proof.
  intros f g X' X L' L step' step x' x Hpbis ; split ;
    intro H ; induction H ; solve [ tauto ] || apply sub_refl || 
    solve [ apply sub_and_left ; auto ] || solve [ apply sub_and_right ; auto ] || 
    solve [ apply sub_box ; auto ] || apply sub_or ; auto.
  intro H' ; apply H ; apply pbis_bval with (b := b) in Hpbis ; tauto.
  intro H' ; apply H ; apply pbis_bval with (b := b) in Hpbis ; tauto.
Qed.

Lemma pbis_red : forall (f f' : F) (e : E) (X' X : Set) (L' : X' -> P -> Prop)
  (L : X -> P -> Prop) (step' : X' -> E -> X' -> Prop)
  (step : X -> E -> X -> Prop) (x' : X') (x : X),
  pbis (klts X' L' step' x') (klts X L step x) ->
  (red X' L' x' f e f' <-> red X L x f e f').
Proof.
  intros f f' e X' X L' L step' step x' x Hpbis ;
    split ; intro H ; induction H ; solve [ apply red_basic ] ||
    solve [ apply red_and ; auto ] || solve [ apply red_all_pos ] ||
    solve [ apply red_all_neg ; auto ] || solve [ apply red_ex_pos ] ||
    solve [ apply red_ex_neg ] || solve [ apply red_box ; auto ] || 
    solve [ apply red_diam ] || solve [ apply red_can ] ||
    solve [ apply red_dlf ] || idtac.
  apply red_or_left ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply red_or_right ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.  
  apply red_or_left ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply red_or_right ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
Qed.

Lemma val_next : forall (f : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (e : E),
  val (klts X L step x) f -> step x e x' -> exists f' : F,
  red X L x f e f' /\ val (klts X L step x') f'.
Proof.
  intro f ; induction f ; intros X L step x x' e' Hval Hstep.
  exists (basic true) ; split ; simpl ; apply red_basic || auto.
  simpl in Hval ; destruct Hval as [ Hf1 Hf2 ].
  apply IHf1 with (step := step) (x' := x') (e := e') in Hf1 ; auto.
  apply IHf2 with (step := step) (x' := x') (e := e') in Hf2 ; auto.
  destruct Hf1 as [ f1' [ Hred_f1 Hval_f1 ] ].
  destruct Hf2 as [ f2' [ Hred_f2 Hval_f2 ] ].
  exists (conj f1' f2') ; split ; simpl ; apply red_and || auto ; auto.
  simpl in Hval ; destruct Hval as [ Hb | Hf ].
  exists (basic true) ; split ; simpl ; apply red_or_left || auto ; auto.
  apply IHf with (step := step) (x' := x') (e := e') in Hf ; auto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  exists (basic true) ; split ; apply red_or_left || auto ; simpl ; auto.
  destruct Hf as [ f' [ Hred Hval ] ].
  exists f' ; split ; apply red_or_right || auto ; auto.
  destruct (classic (e = e')) as [ Heq | Hnot_eq ]. 
  rewrite <- Heq in * ; exists f ; split ; apply red_all_pos || auto.
  exists (basic true) ; split ; simpl ; apply red_all_neg || auto ; auto.
  exists (basic true) ; split ; simpl ; apply red_ex_neg || auto ; auto.
  assert (val (klts X L step x) f) as Hval'.
  apply Hval ; apply trans_refl.
  apply IHf with (step := step) (x' := x') (e := e') in Hval' ; auto.
  destruct Hval' as [ f' [ Hred Hval' ] ].
  exists (conj (box f) f') ; split ; apply red_box || auto ; auto.
  simpl ; split ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e' ; auto.
  exists (basic true) ; split ; apply red_diam || auto ; simpl ; auto.
  exists (basic true) ; split ; apply red_can || auto ; simpl ; auto.
  exists (basic true) ; split ; apply red_dlf || auto ; simpl ; auto.
Qed.

Lemma ex_next : forall (f g : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (e : E),
  sub X L x (ex e f) g -> val (klts X L step x) g ->
  exists x' : X, exists g' : F, step x e x' /\
  red X L x g e g' /\ val (klts X L step x') g' /\
  sub X L x' f g'.
Proof.
  intros f g X L step x e Hsub Hval.
  assert (exists h : F, h = ex e f) as Hex by eauto.
  destruct Hex as [ h Heq ] ; rewrite <- Heq in *.
  induction Hsub ; rewrite Heq in *.
  simpl in Hval ; destruct Hval as [ x' [ Hstep Hval ] ].
  exists x' ; exists f ; repeat split ; 
    apply red_ex_pos || apply sub_refl || auto.
  simpl in Hval ; destruct Hval as [ Hg Hh ].
  apply IHHsub in Hg ; auto.
  destruct Hg as [ x' [ g' [ Hstep [ Hred [ Hval Hsub' ] ] ] ] ].
  apply val_next with (f := h) (X := X) (L := L) (x := x) 
    (e := e) (x' := x') (step := step) in Hh ; auto.
  destruct Hh as [ h' [ Hred' Hval' ] ].
  exists x' ; exists (conj g' h') ; repeat split ; auto.
  apply red_and ; auto.
  apply sub_and_left ; auto.
  simpl in Hval ; destruct Hval as [ Hg Hh ].
  apply IHHsub in Hh ; auto.
  destruct Hh as [ x' [ h' [ Hstep [ Hred [ Hval Hsub' ] ] ] ] ].
  apply val_next with (f := g) (X := X) (L := L) (x := x) 
    (e := e) (x' := x') (step := step) in Hg ; auto.
  destruct Hg as [ g' [ Hred' Hval' ] ].
  exists x' ; exists (conj g' h') ; repeat split ; auto.
  apply red_and ; auto.
  apply sub_and_right ; auto.
  simpl in Hval ; destruct Hval as [ Hbval | Hval ] ;
    contradiction || auto.
  apply IHHsub in Hval ; auto.
  destruct Hval as [ x' [ f' [ Hstep [ Hred [ Hval Hsub' ] ] ] ] ].
  exists x' ; exists f' ; repeat split ; auto.
  apply red_or_right ; auto.
  assert (val (klts X L step x) g) as Hval'.
  apply Hval ; apply trans_refl.
  apply IHHsub in Hval' ; auto.
  destruct Hval' as [ x' [ g' [ Hstep [ Hred [ Hval' Hsub' ] ] ] ] ].
  exists x' ; exists (conj (box g) g') ; repeat split ; auto.
  apply red_box ; auto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e ; auto.
  apply sub_and_right ; auto.
Qed.

Lemma wf_next : forall (f f' : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (e : E), wf f -> U e ->
  val (klts X L step x) f -> step x e x' -> red X L x f e f' ->
  val (klts X L step x') f'.
Proof.
  intros f f' X L step x x' e Hwf HU Hval Hstep Hred ;
    induction Hred ; solve [ simpl ; auto ] || idtac.
  simpl in * ; destruct Hwf ; destruct Hval ; split ; auto.
  simpl in Hval ; destruct Hval ; contradiction || auto.
  simpl in Hwf ; destruct Hwf ; contradiction.
  simpl in * ; split ; try tauto.
  intros x'' Htrans ; apply Hval.
  apply trans_closed with x' e ; auto.
  apply IHHred ; auto.
  apply Hval ; apply trans_refl.
Qed.

Lemma wf_red : forall (f f' : F) (X : Set) (L : X -> P -> Prop)
  (x : X) (e : E), red X L x f e f' -> wf f -> wf f'.
Proof.
  intros f f' X L x e Hred Hwf ; induction Hred ;
    solve [ simpl in * ; tauto ] || idtac.
Qed.

Lemma strong_ind : forall (Q : nat -> Prop), Q 0 ->
  (forall (n : nat), (forall (m : nat), m < n -> Q m) ->
    Q n) -> forall (n : nat), Q n.
Proof.
  intros Q Hzero Hind n ; apply Hind.
  induction n ; intros m Hless ; inversion Hless.
  apply Hind ; auto.
  apply IHn ; auto.
Qed.

Lemma rel_ex : forall (n : nat) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x x' : X) (f f' : F) (e : E),
  step x e x' -> red X L x f e f' -> (forall (n' : nat) (x'' : X) (f'' : F),
  n' < n -> trans (X * F) (unctrl (X * F) (rel n' X L step)) (x', f') (x'', f'') ->
  syn X L (rel n' X L step) (x'', f'') f'') -> rel n X L step (x, f) e (x', f').
Proof.
  intro n ; induction n ; 
    intros X L step x x' f f' e Hstep Hred Hunctrl_syn ;
    simpl ; split ; auto.
  right ; intros xf'' Htrans ; destruct xf'' as [ x'' f'' ].
  apply Hunctrl_syn ; auto.
Qed.

Lemma trans_pres_wf : forall (X : Set) (L : X -> P -> Prop)
  (step : X * F -> E -> X * F -> Prop) (x x' : X) (f f' : F),
  (forall (y y' : X) (g g' : F) (e : E), step (y, g) e (y', g') ->
    red X L y g e g') -> trans (X * F) step (x, f) (x', f') -> wf f -> wf f'.
Proof.
  intros X L step x x' f f' Himpl Htrans Hwf.
  assert (exists xf : X * F, xf = (x, f)) as Hex by eauto.
  assert (exists xf' : X * F, xf' = (x', f')) as Hex' by eauto.
  destruct Hex as [ xf Heq ] ; rewrite <- Heq in *.
  destruct Hex' as [ xf' Heq' ] ; rewrite <- Heq' in *.
  revert Heq Heq' Hwf ; revert x f x' f'.
  induction Htrans ; intros z f z' f' Heq Heq' Hwf.
  rewrite Heq' in * ; inversion Heq ; auto.
  destruct x as [ x g ] ; destruct y as [ y g' ].
  assert ((y, g') = (y, g')) as H' by auto.
  apply IHHtrans with (x'0 := z') (f' := f') in H' ; auto.
  apply Himpl in H ; auto.
  inversion Heq ; replace f with g in * by auto.
  apply wf_red in H ; auto.
Qed.

Lemma trans_rtl_ex : forall (n : nat) (X' X : Set) 
  (L' : X' -> P -> Prop) (L : X -> P -> Prop) 
  (step' : X' -> E -> X' -> Prop)(step : X -> E -> X -> Prop) 
  (x' : X') (x y : X) (f f' : F), val (klts X' L' step' x') f ->  wf f -> 
  trans (X * F) (unctrl (X * F) (rel n X L step)) (x, f) (y, f') ->
  pbis (klts X' L' step' x') (klts X L step x) ->
  exists y' : X', trans X' step' x' y' /\ val (klts X' L' step' y') f' /\ 
  pbis (klts X' L' step' y') (klts X L step y).
Proof.
  intros n X' X L' L step' step x' x y f f' Hval Hwf Htrans Hpbis.
  assert (exists xf : X * F, xf = (x, f)) as Hex by eauto.
  assert (exists yf' : X * F, yf' = (y, f')) as Hex' by eauto.
  destruct Hex as [ xf Heq ] ; rewrite <- Heq in *.
  destruct Hex' as [ yf' Heq' ] ; rewrite <- Heq' in *.
  revert Hval Hpbis Hwf Heq Heq' ; revert x f y f' x'.
  induction Htrans ; intros z f z' f' w Hval Hpbis Hwf Heq Heq'.
  rewrite Heq' in * ; inversion Heq.
  replace z with z' in * by auto.
  replace f' with f in * by auto.
  exists w ; repeat split ; apply trans_refl || auto.
  unfold unctrl in H ; destruct H as [ Hrel HU ].
  rewrite Heq in * ; destruct y as [ y g ].
  apply rel_impl_step_red in Hrel.
  destruct Hrel as [ Hstep Hred ].
  assert (pbis (klts X' L' step' w) (klts X L step z)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep ; auto.
  destruct Hstep as [ w' [ Hstep' HR' ] ].
  assert (val (klts X' L' step' w') g) as Hval'.
  apply wf_next with (f := f) (x := w) (e := e) ; auto.
  apply pbis_red with (f := f) (e := e) (f' := g) in Hpbis' ; tauto.
  apply IHHtrans with (y0 := z') (x := y) (f' := f') in Hval' ; auto.
  destruct Hval' as [ w'' [ Htrans' [ Hval' HR'' ] ] ].
  exists w'' ; repeat split ; auto.
  apply trans_closed with w' e ; auto.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  apply wf_red in Hred ; auto.
Qed.

Lemma pbis_impl_syn : forall (n : nat) (f g : F) (X : Set) (L : X -> P -> Prop)
  (step : X -> E -> X -> Prop) (x : X) (k' : K), sub X L x f g -> wf g ->
  pbis k' (klts X L step x) -> val k' g -> syn X L (rel n X L step) (x, g) f.
Proof.
  intro n ; induction n using strong_ind ; intro f ; induction f ;
    intros g X L step x k' Hsub Hwf Hpbis Hval ;
    solve [ apply syn_all ] || solve [ apply sub_and in Hsub ; 
    destruct Hsub as [ Hf1 Hf2 ] ; apply syn_and ; 
    [ apply IHf1 with k' | apply IHf2 with k' ] ; auto ] || auto.
  destruct k' as [ X' L' step' x' ].
  apply sub_val with (f := basic b) in Hval ; auto.
  simpl in Hval ; apply syn_basic.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply pbis_sub with (f := basic b) (g := g) in Hpbis ; tauto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  apply syn_or_left ; auto.
  apply sub_not_or in Hsub ; auto.
  apply syn_or_right ; apply IHf with k' ; auto.
  destruct k' as [ X' L' step' x' ].
  apply ex_next with (f := f) (e := e) in Hval ; auto.
  destruct Hval as [ y' [ g' [ Hstep' [ Hred [ Hval Hsub' ] ] ] ] ].
  assert (red X L x g e g') as Hred'.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis ; tauto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_ex with y g' ; auto.
  simpl ; split ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis ; tauto.
  apply IHf with (k' := klts X' L' step' y') ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis ; tauto.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  apply pbis_sub with (f := ex e f) (g := g) in Hpbis ; tauto.
  apply sub_box_impl with (f := f) in Hsub ; auto.
  apply syn_box ; apply IHf with k' ; auto.
  destruct k' as [ X' L' step' x' ].
  assert (val (klts X' L' step' x') (diam b)) as Hval'.
  apply sub_val with (f := diam b) in Hval ; auto.
  apply pbis_sub with (f := diam b) (g := g) in Hpbis ; tauto.
  simpl in Hval' ; destruct Hval' as [ y' [ Htrans Hvalb ] ].
  clear Hsub ; revert Hwf Hpbis Hval.
  revert g x ; induction Htrans ; intros g z Hwf Hpbis Hval.
  apply syn_diam with z g ; apply trans_refl || auto ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  assert (step' x e y) as Hstep' by auto.
  assert (pbis (klts X' L' step' x) (klts X L step z)) 
    as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ z' [ Hstep HR ] ].
  assert (step' x e y) as Hstep' by auto.
  apply val_next with (L := L') (step := step') (f := g)
    in Hstep' ; auto.
  destruct Hstep' as [ g' [ Hred Hval' ] ].
  apply IHHtrans with (x := z') in Hval' ; auto.
  inversion Hval' ; apply syn_diam with x'0 g'0 ; auto.
  apply trans_closed with (z', g') e ; auto.
  simpl ; split ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  destruct k' as [ X' L' step' x' ].
  assert (val (klts X' L' step' x') (can e)) as Hval'.
  apply sub_val with (f := can e) in Hval ; auto.
  apply pbis_sub with (f := can e) (g := g) in Hpbis ; tauto.
  simpl in Hval' ; destruct Hval' as [ y' Hstep' ].
  assert (step' x' e y') as H by auto.
  apply val_next with (step := step') (L := L') (f := g) in H ; auto.
  destruct H as [ g' [ Hred Hval' ] ].
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_can with y g' ; simpl ; split ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.
  destruct k' as [ X' L' step' x' ].
  assert (val (klts X' L' step' x') dlf) as Hval'.
  apply sub_val with (f := dlf) in Hval ; auto.
  apply pbis_sub with (f := dlf) (g := g) in Hpbis ; tauto.
  simpl in Hval' ; destruct Hval' as [ e [ y' Hstep' ] ].
  assert (step' x' e y') as H by auto.
  apply val_next with (step := step') (L := L') (f := g) in H ; auto.
  destruct H as [ g' [ Hred Hval' ] ].
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_dlf with y g' e ; simpl ; split ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.

  (* Start inductive case *)
  destruct k' as [ X' L' step' x' ].
  apply sub_val with (f := basic b) in Hval ; auto.
  simpl in Hval ; apply syn_basic.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  apply pbis_sub with (f := basic b) (g := g) in Hpbis ; tauto.
  destruct (classic (bval X L x b)) as [ Hbval | Hnot_bval ].
  apply syn_or_left ; auto.
  apply sub_not_or in Hsub ; auto.
  apply syn_or_right ; apply IHf with k' ; auto.
  destruct k' as [ X' L' step' x' ].
  apply ex_next with (f := f) (e := e) in Hval ; auto.
  destruct Hval as [ y' [ g' [ Hstep' [ Hred [ Hval Hsub' ] ] ] ] ].
  assert (red X L x g e g') as Hred'.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis ; tauto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_ex with y g' ; auto.
  assert (wf g') as Hwf'.
  apply wf_red in Hred ; auto.
  apply rel_ex ; auto.
  intros n' z g'' Hless Htrans_xf.
  assert (wf g'') as Hwf''.
  apply trans_pres_wf with (L := L) in Htrans_xf ; auto.
  intros v v' h h' e' Hunctrl.
  unfold unctrl in Hunctrl.
  destruct Hunctrl as [ Hrel _ ].
  apply rel_impl_step_red in Hrel ; tauto.
  apply trans_rtl_ex with (X' := X') (L' := L') 
    (step' := step') (x' := y') in Htrans_xf ; auto.
  destruct Htrans_xf as [ z' [ Htrans [ Hval' Hpbis ] ] ].
  apply H with (klts X' L' step' z') ; auto.
  apply sub_refl.
  exists R ; split ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis ; tauto.
  apply IHf with (k' := klts X' L' step' y') ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  apply pbis_sub with (f := f) (g := g') in Hpbis ; tauto.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  apply pbis_sub with (f := ex e f) (g := g) in Hpbis ; tauto.
  apply sub_box_impl with (f := f) in Hsub ; auto.
  apply syn_box ; apply IHf with k' ; auto.
  destruct k' as [ X' L' step' x' ].
  assert (val (klts X' L' step' x') (diam b)) as Hval'.
  apply sub_val with (f := diam b) in Hval ; auto.
  apply pbis_sub with (f := diam b) (g := g) in Hpbis ; tauto.
  simpl in Hval' ; destruct Hval' as [ y' [ Htrans Hvalb ] ].
  clear Hsub ; revert Hwf Hpbis Hval.
  revert g x ; induction Htrans ; intros g z Hwf Hpbis Hval.
  apply syn_diam with z g ; apply trans_refl || auto ; auto.
  apply pbis_bval with (b := b) in Hpbis ; tauto.
  assert (step' x e y) as Hstep' by auto.
  assert (pbis (klts X' L' step' x) (klts X L step z)) 
    as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ z' [ Hstep HR ] ].
  assert (step' x e y) as Hstep' by auto.
  apply val_next with (L := L') (step := step') (f := g)
    in Hstep' ; auto.
  destruct Hstep' as [ g' [ Hred Hval' ] ].
  assert (val (klts X' L' step' y) g') as Hval_bak by auto.
  apply IHHtrans with (x := z') in Hval' ; auto.
  inversion Hval' ; apply syn_diam with x'0 g'0 ; auto.
  apply trans_closed with (z', g') e ; auto.
  apply rel_ex ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.
  intros n' x'' g'' Hless Htrans'.
  assert (wf g'') as Hwf''.
  apply trans_pres_wf with (L := L) in Htrans' ; auto.
  intros v v' h h' e' Hunctrl.
  unfold unctrl in Hunctrl.
  destruct Hunctrl as [ Hrel _ ].
  apply rel_impl_step_red in Hrel ; tauto.
  apply wf_red in Hred ; auto.
  apply trans_rtl_ex with (X' := X') (L' := L') (step' := step')
    (x' := y) in Htrans' ; auto.
  destruct Htrans' as [ y' [ Htrans' [ Hval'' Hpbis ] ] ].
  apply H with (klts X' L' step' y') ; auto.
  apply sub_refl.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  destruct k' as [ X' L' step' x' ].
  assert (val (klts X' L' step' x') (can e)) as Hval'.
  apply sub_val with (f := can e) in Hval ; auto.
  apply pbis_sub with (f := can e) (g := g) in Hpbis ; tauto.
  simpl in Hval' ; destruct Hval' as [ y' Hstep' ].
  assert (step' x' e y') as Hstep_bak by auto.
  apply val_next with (step := step') (L := L') (f := g) in Hstep_bak ; auto.
  destruct Hstep_bak as [ g' [ Hred Hval' ] ].
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_can with y g' ; auto.
  apply rel_ex ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.
  intros n' z g'' Hless Htrans.
  assert (wf g'') as Hwf''.
  apply trans_pres_wf with (L := L) in Htrans ; auto.
  intros v v' h h' e' Hunctrl.
  unfold unctrl in Hunctrl.
  destruct Hunctrl as [ Hrel _ ].
  apply rel_impl_step_red in Hrel ; tauto.
  apply wf_red in Hred ; auto.
  apply trans_rtl_ex with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Htrans [ Hval'' Hpbis'' ] ] ].
  apply H with (k' := klts X' L' step' z') ; auto.
  apply sub_refl.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
  destruct k' as [ X' L' step' x' ].
  assert (val (klts X' L' step' x') dlf) as Hval'.
  apply sub_val with (f := dlf) in Hval ; auto.
  apply pbis_sub with (f := dlf) (g := g) in Hpbis ; tauto.
  simpl in Hval' ; destruct Hval' as [ e [ y' Hstep' ] ].
  assert (step' x' e y') as Hstep_bak by auto.
  apply val_next with (step := step') (L := L') (f := g) in Hstep_bak ; auto.
  destruct Hstep_bak as [ g' [ Hred Hval' ] ].
  assert (pbis (klts X' L' step' x') (klts X L step x)) as Hpbis' by auto.
  destruct Hpbis as [ R [ HinR HrelR ] ].
  apply HrelR in HinR ; apply HinR in Hstep'.
  destruct Hstep' as [ y [ Hstep HR ] ].
  apply syn_dlf with y g' e ; simpl ; auto.
  apply rel_ex ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.
  intros n' z g'' Hless Htrans.
  assert (wf g'') as Hwf''.
  apply trans_pres_wf with (L := L) in Htrans ; auto.
  intros v v' h h' e' Hunctrl.
  unfold unctrl in Hunctrl.
  destruct Hunctrl as [ Hrel _ ].
  apply rel_impl_step_red in Hrel ; tauto.
  apply wf_red in Hred ; auto.
  apply trans_rtl_ex with (X' := X') (L' := L')
    (step' := step') (x' := y') in Htrans ; auto.
  destruct Htrans as [ z' [ Htrans [ Hval'' Hpbis'' ] ] ].
  apply H with (k' := klts X' L' step' z') ; auto.
  apply sub_refl.
  apply wf_red in Hred ; auto.
  exists R ; split ; auto.
Qed.  

Theorem maximality : forall (k' k : K) (f : F) (n : nat),
  wf f -> pbis k' k -> val k' f -> pbis k' (S k f n).
Proof.
  intros k' k f n Hwf Hpbis Hval.
  destruct k' as [ X' L' step' x' ].
  destruct k as [ X L step x ].
  destruct Hpbis as [ R [ HinR HrelR ] ].
  exists (fun y' yg => R y' (fst yg) /\ wf (snd yg) /\
    val (klts X' L' step' y') (snd yg)) ; split ; auto.
  intros y' yg H ; destruct H as [ HR [ Hwf' Hval' ] ].
  destruct yg as [ y g ] ; simpl in *.
  assert (R y' y) as HR_bak by auto.
  apply HrelR in HR ; split ; [ tauto | split ].
  intros e z' Hstep' ; assert (step' y' e z') as H by auto.
  apply val_next with (f := g) (X := X') (L := L') (step := step')
    (x := y') (e := e) (x' := z') in H ; auto.
  destruct H as [ g' [ Hred Hval'' ] ].
  assert (step' y' e z') as Hstep_bak by auto.
  apply HR in Hstep' ; destruct Hstep' as [ z [ Hstep HR' ] ].
  exists (z, g') ; repeat split ; auto.
  apply rel_ex ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis ; tauto.
  intros n' x'' g'' Hless Htrans.
  assert (wf g') as Hwf''.
  apply wf_red in Hred ; auto.
  assert (exists z'' : X', trans X' step' z' z'' /\
    val (klts X' L' step' z'') g'' /\ R z'' x'') as H'.
  clear HinR Hstep Hred Hless Hwf Hstep_bak HR_bak HR Hval' Hval Hwf'.
  assert (exists zg : X * F, zg = (z, g')) as Hex by eauto.
  assert (exists xg : X * F, xg = (x'', g'')) as Hex' by eauto.
  destruct Hex as [ yg Heq ] ; rewrite <- Heq in *.
  destruct Hex' as [ zg Heq' ] ; rewrite <- Heq' in *.
  revert Hval'' HR' Hwf'' Heq Heq' ; revert z g' x'' g'' z'.
  induction Htrans ; intros w g' z g'' z' Hval HR Hwf Heq Heq'.
  rewrite Heq' in * ; inversion Heq.
  replace z with w in * by auto.
  replace g'' with g' in * by auto.
  exists z' ; repeat split ; apply trans_refl || auto.
  unfold unctrl in H ; destruct H as [ Hrel HU ].
  rewrite Heq in * ; destruct y0 as [ v h ].
  apply rel_impl_step_red in Hrel.
  destruct Hrel as [ Hstep Hred ].
  assert (R z' w) as HR_bak by auto.
  apply HrelR in HR ; apply HR in Hstep ; auto.
  destruct Hstep as [ v' [ Hstep' HR' ] ].
  assert (val (klts X' L' step' v') h) as Hval'.
  apply wf_next with (f := g') (x := z') (e := e0) ; auto.
  assert (pbis (klts X' L' step' z') (klts X L step w)) as Hpbis.
  exists R ; split ; auto.
  apply pbis_red with (f := g') (e := e0) (f' := h) in Hpbis ; tauto.
  apply IHHtrans with (z' := v') (z := v) (x'' := z) (g'' := g'') in Hval' ; auto.
  destruct Hval' as [ z'' [ Htrans' [ Hval' HR'' ] ] ].
  exists z'' ; repeat split ; auto.
  apply trans_closed with v' e0 ; auto.
  apply wf_red in Hred ; auto.
  destruct H' as [ w' [ Htrans' [ Hval''' HR'' ] ] ].
  apply pbis_impl_syn with (k' := klts X' L' step' w') ; auto.
  apply sub_refl.
  apply trans_pres_wf with (L := L) in Htrans ; auto.
  intros t t' h h' e' Hrel.
  unfold unctrl in Hrel.
  destruct Hrel as [ Hrel _ ].
  apply rel_impl_step_red in Hrel ; tauto.
  exists R ; split ; auto.
  simpl ; apply wf_red in Hred ; auto.
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis.
  exists R ; split ; auto.
  intros e z HU Hrel ; destruct z as [ z g' ].
  apply rel_impl_step_red in Hrel.
  destruct Hrel as [ Hstep Hred ].
  assert (pbis (klts X' L' step' y') (klts X L step y)) as Hpbis'.
  exists R ; split ; auto.
  apply HrelR in HR_bak ; apply HR_bak in Hstep ; auto.
  destruct Hstep as [ z' [ Hstep' HR' ] ].
  exists z' ; repeat split ; auto.
  simpl ; apply wf_red in Hred ; auto.
  simpl ; apply wf_next with (f := g) (x := y') (e := e) ; auto.
  apply pbis_red with (f := g) (e := e) (f' := g') in Hpbis' ; tauto.
Qed.
