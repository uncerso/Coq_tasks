Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical.

Module basic_defs.

Definition implB (b1 b2 : bool) :=
  orb (negb b1) b2.

Lemma implB_is_implb:
  forall a b : bool, implB a b = implb a b.
Proof.
  intros.
  case a.
  auto.
  auto.
Qed.

Definition eqB (b1 b2 : bool) :=
  orb (andb b1 b2) (andb (negb b1) (negb b2)).

Lemma eqB_is_eqb:
  forall a b : bool, eqB a b = eqb a b.
Proof.
  intros.
  case a.
  auto.
  auto.
Qed.

Theorem ExpandNot :
  forall (b : bool), Is_true (negb b) <-> ~ Is_true b.
  intros.
  case b.
  - simpl.
    split.
    intuition.
    apply Peirce.
    intros.
    intuition.
  - simpl.
    intuition.
Qed.

Theorem ExpandOr :
  forall (a b : bool), Is_true (a || b) <-> (Is_true a) \/ Is_true b.
  intros.
  case a.
  case b.
  - simpl.
    intuition.
  - simpl.
    intuition.
  - simpl.
    intuition.
Qed.

Theorem ExpandAnd :
  forall (a b : bool), Is_true (a && b) <-> (Is_true a) /\ Is_true b.
  intros.
  case a.
  case b.
  - simpl.
    intuition.
  - simpl.
    intuition.
  - simpl.
    intuition.
Qed.

Theorem ExpandImpl :
  forall (a b : bool), Is_true (implB a b) <-> ((Is_true a) -> Is_true b).
  intros.
  case a.
  case b.
  - simpl.
    intuition.
  - simpl.
    intuition.
  - simpl.
    intuition.
Qed.

Theorem ExpandEq :
  forall (a b : bool), Is_true ((implB a b) && (implB b a)) <-> ((Is_true a) <-> Is_true b).
  intuition.
  - apply ExpandAnd in H.
    destruct H.
    rewrite -> ExpandImpl in H.
    apply H, H0.
  - apply ExpandAnd in H.
    destruct H.
    rewrite -> ExpandImpl in H1.
    apply H1, H0.
  - apply ExpandAnd.
    rewrite -> ExpandImpl.
    rewrite -> ExpandImpl.
    intuition.
Qed.

Inductive Bool : Type :=
  | T : Bool
  | F : Bool
.

Inductive Formula (Vars : Type) : Type :=
  | const ( c : Bool )
  | var   ( v : Vars )
  | not   ( p : Formula Vars )
  | or    ( lhs rhs : Formula Vars )
  | and   ( lhs rhs : Formula Vars )
.

Fixpoint ApplyInterpretation {Vars : Type} (interpretation : Vars -> bool) (prop : Formula Vars) : bool :=
  match prop with
  | const _ T => true
  | const _ F => false
  | var _ v  => interpretation v
  | not _ p => negb (ApplyInterpretation interpretation p)
  | or _ lhs rhs => orb (ApplyInterpretation interpretation lhs) (ApplyInterpretation interpretation rhs)
  | and _ lhs rhs => andb (ApplyInterpretation interpretation lhs) (ApplyInterpretation interpretation rhs)
 end.

Definition IsModelOf {Vars : Type} (interpretation : Vars -> bool) (prop : Formula Vars) :=
  Is_true (ApplyInterpretation interpretation prop).

Definition IsTautology {Vars : Type} (p: Formula Vars) :=
  forall interpretation : Vars -> bool, IsModelOf interpretation p.


Definition IsInheritsModels {Vars : Type} (from to: Formula Vars) :=
  forall interpretation : Vars -> bool, IsModelOf interpretation from -> IsModelOf interpretation to.

Definition IsEqual {Vars : Type} (p1 p2: Formula Vars) :=
  forall interpretation : Vars -> bool,
      Is_true (andb
      (implB (ApplyInterpretation interpretation p1) (ApplyInterpretation interpretation p2))
      (implB (ApplyInterpretation interpretation p2) (ApplyInterpretation interpretation p1))).

Definition IsEqual2 {Vars : Type} (p1 p2: Formula Vars) :=
  forall interpretation : Vars -> bool,
      Is_true (ApplyInterpretation interpretation p1) <-> Is_true (ApplyInterpretation interpretation p2).

Theorem Equal_is_Equal2:
  forall (Vars : Type) (f g: Formula Vars), (IsEqual f g) <-> (IsEqual2 f g).
Proof.
  intros.
  unfold IsEqual, IsEqual2.
  split.
  - intro; intro.
    rewrite <- ExpandEq.
    intuition.
  - intro; intro.
    rewrite -> ExpandEq.
    revert interpretation.
    apply H.
Qed.

End basic_defs.

Module all_defs.
Import basic_defs.
Export basic_defs.

Definition __Or {Vars : Type} (p1 p2 : Formula Vars) :=
  or Vars p1 p2.

Definition __And {Vars : Type} (p1 p2 : Formula Vars) :=
  and Vars p1 p2.

Definition __Not {Vars : Type} (p : Formula Vars) :=
  not Vars p.

Notation "a | b" := (__Or a b) (at level 50, left associativity).
Notation "a & b " := (__And a b) (at level 40, left associativity).
Notation "! b " := (__Not b) (at level 1, no associativity).

Definition __Implies {Vars : Type} (p1 p2 : Formula Vars) :=
  !p1 | p2.

Definition __Eq {Vars : Type} (p1 p2 : Formula Vars) :=
  (p1 & p2) | (!p1 & !p2).

Notation "a --> b" := (__Implies a b) (at level 90, no associativity).
Notation "a <--> b" := (__Eq a b) (at level 95, no associativity).

Notation "|= F" := (IsTautology F) (at level 100, no associativity).
Notation "F |= G" := (IsInheritsModels F G) (at level 100, no associativity).
Notation "F ~ G" := (IsEqual F G) (at level 100, no associativity).
Notation "F [ g ]" := (ApplyInterpretation F g) (at level 10, no associativity).

End all_defs.

Section task_1.
Import all_defs.

(* Пусть φ и ψ — формулы логики высказываний. Докажите, что |= φ → ψ тогда и только
тогда, когда φ |= ψ, и |= φ ↔ ψ тогда и только тогда, когда φ ∼ ψ.*)

Theorem task1_part1 :
forall (Vars : Type) (f g : Formula Vars), (|= (f --> g)) <-> (f |= g).
Proof.
  intros.
  unfold IsTautology.
  unfold IsInheritsModels.
  unfold "-->".
  unfold IsModelOf.
  simpl.
  split.
  - intros B I.
    apply ExpandImpl.
    unfold implB.
    intuition.
  - intros B I.
    apply ExpandImpl.
    unfold implB.
    intuition.
Qed.

Lemma BestSimpl :
  forall a b : bool,
  (negb a || b) && (negb b || a) = a && b || negb a && negb b.
Proof.
  intros.
  rewrite -> andb_orb_distrib_l.
  rewrite -> andb_orb_distrib_r.
  rewrite -> andb_orb_distrib_r.
  rewrite -> andb_negb_l.
  rewrite -> orb_assoc.
  rewrite -> orb_false_r.
  rewrite -> andb_negb_r.
  rewrite -> orb_false_r.
  rewrite -> orb_comm.
  rewrite -> andb_comm.
  reflexivity.
Qed.

Theorem task1_part2 :
forall (Vars : Type) (f g : Formula Vars), (|= (f <--> g)) <-> (f ~ g).
Proof.
  intros.
  unfold "<-->".
  unfold IsTautology.
  unfold IsEqual.
  unfold IsModelOf.
  unfold implB.
  simpl.
  intuition.
  - rewrite -> BestSimpl.
    apply H.
  - rewrite <- BestSimpl.
    apply H.
Qed.

End task_1.

Section task_2.
Import all_defs.

Ltac unfold_polish :=
  simpl;
  case ApplyInterpretation;
  intuition;
  intuition.


(* ¬¬φ ∼ φ *)
Theorem tast2_part_a:
  forall (Vars : Type) (f : Formula Vars), (!!f) ~ f.
Proof.
  intros.
  unfold IsEqual.
  intros;
  unfold_polish.
Qed.

(*  φ ∨ ¬φ *)
Theorem tast2_part_b:
  forall (Vars : Type) (f : Formula Vars), |= (f | !f).
Proof.
  intros.
  unfold IsTautology.
  intros.
  unfold IsModelOf.
  unfold_polish.
Qed.

Ltac smart_rewrite rule :=
  intros;
  unfold IsEqual;
  intros;
  simpl;
  rewrite -> rule;
  rewrite -> andb_diag;
  rewrite -> implB_is_implb;
  rewrite -> implb_same;
  reflexivity.


(* φ ∧ (ψ ∨ η) ∼ (φ ∧ ψ) ∨ (φ ∧ η) *)
Theorem tast2_part_c:
  forall (Vars : Type) (f p n: Formula Vars), (f & (p | n)) ~ ((f & p) | (f & n)).
Proof.
  smart_rewrite andb_orb_distrib_r.
Qed.

(* φ ∨ (ψ ∧ η) ∼ (φ ∨ ψ) ∧ (φ ∨ η) *)
Theorem tast2_part_d:
  forall (Vars : Type) (f p n: Formula Vars), (f | (p & n)) ~ ((f | p) & (f | n)).
Proof.
  smart_rewrite orb_andb_distrib_r.
Qed.

(* φ ∨ (φ ∧ ψ) ∼ φ *)
Theorem tast2_part_e:
  forall (Vars : Type) (f p: Formula Vars), (f | (f & p)) ~ f.
Proof.
  smart_rewrite absorption_orb.
Qed.

(* φ ∧ (φ ∨ ψ) ∼ φ *)
Theorem tast2_part_f:
  forall (Vars : Type) (f p: Formula Vars), (f & (f | p)) ~ f.
Proof.
  smart_rewrite absorption_andb.
Qed.

(* ¬(φ ∧ ψ) ∼ ¬φ ∨ ¬ψ *)
Theorem tast2_part_g:
  forall (Vars : Type) (f g: Formula Vars), (!(f & g)) ~ (!f | !g).
Proof.
  smart_rewrite negb_andb.
Qed.

(* ¬(φ ∨ ψ) ∼ ¬φ ∧ ¬ψ *)
Theorem tast2_part_h:
  forall (Vars : Type) (f g: Formula Vars), (!(f | g)) ~ (!f & !g).
Proof.
  smart_rewrite negb_orb.
Qed.

End task_2.

Section task_3.
Inductive ThreeVars : Type := pp | qq | rr.

Definition BadInterpretation (v : ThreeVars) : bool :=
  match v with
  | pp => true
  | _ => false
  end.

Import all_defs.

(* (p → q) ↔ (¬q → ¬p) *)
Theorem tast3_part_a:
  forall (Vars : Type) (p q: Formula Vars), |= ((p --> q) <--> (!q --> !p)).
Proof.
  intros.
  unfold IsTautology.
  intros.
  unfold IsModelOf.
  simpl.
  set (P := interpretation[p]).
  set (Q := interpretation[q]).
  case P.
  - case Q.
    intuition.
    intuition.
  - case Q.
    intuition.
    intuition.
Qed.

(* формула не общезначима *)
Theorem tast3_part_b_1:
  exists (Vars : Type) (p q r: Formula Vars) (interpretation : Vars -> bool), ~ (IsModelOf interpretation ((p --> (q --> r)) <--> (!r --> (!q --> !p)))).
Proof.
  constructor 1 with ThreeVars.
  constructor 1 with (var ThreeVars pp).
  constructor 1 with (var ThreeVars qq).
  constructor 1 with (var ThreeVars rr).
  constructor 1 with BadInterpretation.
  intuition.
Qed.

(* формула выполнима *)
Theorem tast3_part_b_2:
  exists (Vars : Type) (p q r: Formula Vars) (interpretation : Vars -> bool), (IsModelOf interpretation ((p --> (q --> r)) <--> (!r --> (!q --> !p)))).
Proof.
  constructor 1 with ThreeVars.
  constructor 1 with (var ThreeVars pp).
  constructor 1 with (var ThreeVars qq).
  constructor 1 with (var ThreeVars rr).
  constructor 1 with (fun _ => false).
  unfold IsModelOf.
  intuition.
Qed.

End task_3.

Section task_4.
Import all_defs.

(* ¬(¬(p ∧ q) → ¬r) *)
(* КНФ, ННФ *)
Theorem tash5_part_1:
  forall (Vars : Type) (p q r: Formula Vars), !(!(p & q) --> !r) ~ (!p | !q) & r.
Proof.
  intros.
  unfold "-->".
  unfold IsEqual.
  intros.
  simpl.
  set (P := ApplyInterpretation interpretation p).
  set (Q := ApplyInterpretation interpretation q).
  set (R := ApplyInterpretation interpretation r).
  case P, Q, R.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
Qed.

(* ДНФ *)
Theorem tash5_part_2:
  forall (Vars : Type) (p q r: Formula Vars), !(!(p & q) --> !r) ~ !p & r | !q & r.
Proof.
  intros.
  unfold "-->".
  unfold IsEqual.
  intros.
  simpl.
  set (P := ApplyInterpretation interpretation p).
  set (Q := ApplyInterpretation interpretation q).
  set (R := ApplyInterpretation interpretation r).
  case P, Q, R.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
  intuition.
Qed.

End task_4.

Section task_5.
Import basic_defs.

Fixpoint IsNNF {Vars : Type} (f : Formula Vars) :=
  match f with
  | or _ a b => (IsNNF a) /\ (IsNNF b)
  | and _ a b => (IsNNF a) /\ (IsNNF b)
  | var _ _ => True
  | not _ (var _ _) => True
  | const _ _ => True
  | _ => False
  end.

Definition NNF_Formula (Vars : Type) := {f : Formula Vars | IsNNF f}.

Fixpoint positive_nesting {Vars : Type} (fromI : Vars -> bool) (toI : Vars -> bool) (f : Formula Vars) :=
  (IsNNF f) ->
  match f with
  | or _ f g => (positive_nesting fromI toI f) /\ (positive_nesting fromI toI g)
  | and _ f g => (positive_nesting fromI toI f) /\ (positive_nesting fromI toI g)
  | var _ v => Is_true (implB (fromI v) (toI v))
  | not _ (var _ _) as V => Is_true (implB (ApplyInterpretation fromI V) (ApplyInterpretation toI V))
  | _ => True
  end.

Import all_defs.

Theorem task5:
  forall (Vars : Type) (I1 I2 : Vars -> bool) (f : Formula Vars),
    (IsNNF f) /\ (positive_nesting I1 I2 f) /\ (IsModelOf I1 f) -> (IsModelOf I2 f).
Proof.
  intros.
  destruct H as [NNF [N M]].
  induction f.
  - auto.
  - revert N.
    unfold IsModelOf in M.
    simpl in M.
    simpl.
    unfold IsModelOf.
    intuition.
    rewrite ExpandImpl in H.
    simpl.
    apply H, M.
  - revert NNF N M IHf.
    case f.
    -- intuition.
    -- intuition.
       revert M N H.
       unfold IsModelOf.
       simpl.
       intuition.
       rewrite ExpandImpl in H0.
       intuition.
    -- intro; simpl; intuition.
    -- intro; simpl; intuition.
    -- intro; simpl; intuition.
  - simpl in NNF.
    destruct NNF as [NNF1 NNF2].
    intuition.
    revert N.
    simpl.
    intuition.
    unfold IsModelOf.
    simpl.
    apply ExpandOr.
    unfold IsModelOf in M.
    simpl in M.
    apply ExpandOr in M.
    destruct M as [M1 | M2].
    intuition.
    intuition.
  - revert N.
    simpl.
    intuition.
    unfold IsModelOf.
    simpl.
    apply ExpandAnd.
    simpl in NNF.
    destruct NNF as [NNF1 NNF2].
    split.
    -- apply IHf1.
       --- auto.
       --- auto.
       --- revert M.
           unfold IsModelOf.
           apply ExpandImpl.
           simpl.
           unfold implB.
           rewrite -> negb_andb.
           rewrite -> orb_comm.
           rewrite -> orb_assoc.
           rewrite -> orb_negb_r.
           intuition.
    -- apply IHf2.
       --- auto.
       --- auto.
       --- revert M.
           unfold IsModelOf.
           apply ExpandImpl.
           simpl.
           unfold implB.
           rewrite -> negb_andb.
           set (F2 := ApplyInterpretation I1 f2).
           rewrite <- orb_assoc.
           rewrite orb_negb_l.
           intuition.
Qed.

End task_5.

Section task_6.
Import basic_defs.

Definition bool_to_Bool (b : bool) :=
  if b then T else F.

Fixpoint n_dim_fun (n : nat):=
  match n with
  | 0 => bool
  | S m => bool -> n_dim_fun m
end.

Inductive array (Vars : Type) : nat -> Type :=
  | nil : array Vars 0
  | cons : forall n : nat, Vars -> array Vars n -> array Vars (S n).

Definition Head {n : nat} {Vars : Type} (v: array Vars (S n)) : Vars :=
  match v in array _ (S m) with
  | nil _ => False_rect unit
  | cons _ _ h _ => h
  end.

Definition Tail {n : nat} {Vars : Type} (v: array Vars (S n)) : array Vars n :=
  match v in array _ (S m) with
  | nil _ => False_rect unit
  | cons _ _ _ t => t
  end.

Fixpoint n_dim_fun_apply {n : nat} {Vars : Type} (interpretation : Vars -> bool) (f : n_dim_fun n) (args : array Vars n): bool :=
  match n, f, args with
  | 0, _, _ => f
  | S m, _, _ => let h := interpretation (Head args) in
                 let t := (Tail args) in
                 n_dim_fun_apply interpretation (f h) t
  end.

Fixpoint make_formula_by_func {n : nat} {Vars : Type} (vars: array Vars n) (f : n_dim_fun n) : (Formula Vars) :=
  match n, f, vars with
  | 0, _, _ => const Vars (bool_to_Bool f)
  | S m, _, _ => let h := var Vars (Head vars) in
                 let t := Tail vars in
                 or Vars
                 (and Vars h (make_formula_by_func t (f true)))
                 (and Vars (not Vars h) (make_formula_by_func t (f false)))
  end.

Import all_defs.

Theorem task6:
  forall (n : nat) (Vars : Type) (vars: array Vars n) (f : n_dim_fun n) , exists (g : Formula Vars), forall (interpretation : Vars -> bool),
  (ApplyInterpretation interpretation g) = (n_dim_fun_apply interpretation f vars).
Proof.
  intros.
  exists (make_formula_by_func vars f).
  intro.
  induction n.
  - simpl; case f; intuition; intuition.
  - simpl.
    set (h := interpretation (Head vars)).
    set (t := Tail vars).
    rewrite <- (IHn t (f h)).
    case h.
    -- simpl; intuition.
    -- simpl; intuition.
Qed.

End task_6.

Section task_7.
Import basic_defs.

Fixpoint IsPositive {Vars : Type} (f : Formula Vars) :=
  match f with 
  | not _ _ => False
  | const _ _ => True
  | var _ _ => True
  | or _ f g => IsPositive f /\ IsPositive g
  | and _ f g => IsPositive f /\ IsPositive g
  end.

Definition nested_inversion {Vars : Type} (from to : Vars -> bool) :=
  forall (v : Vars), Is_true (from v) -> Is_true (to v).

Definition IsMonotonic {Vars : Type} (h : Formula Vars) :=
  forall (F G : Vars -> bool), ((IsModelOf F h) /\ (nested_inversion F G)) -> (IsModelOf G h).

Definition IsLiteral {Vars : Type} (h : Formula Vars) :=
  match h with
  | var _ _ => True
  | not _ (var _ _) => True
  | _ => False
  end.

Fixpoint IsDisj {Vars : Type} (h : Formula Vars) :=
  (IsLiteral h) \/
  match h with
  | or _ a b => (IsLiteral h) /\ (IsDisj b)
  | _ => False
  end.

Fixpoint IsConj {Vars : Type} (h : Formula Vars) :=
  (IsDisj h) \/
  match h with
  | and _ a b => (IsDisj a) /\ (IsConj b)
  | _ => False
  end.

Import all_defs.

Theorem task7_part_a:
  forall (Vars : Type) (F G : Vars -> bool),
      (nested_inversion F G) <->
      forall (h : Formula Vars), (IsPositive h) -> Is_true (F[h]) -> Is_true (G[h]).
Proof.
  intros.
  split.
  - intros H h P A.
    induction h.
    -- intuition.
    -- revert A; apply H.
    -- revert P; simpl; intuition.
    -- destruct P as [P1 P2].
       revert A; simpl. 
       rewrite -> ExpandOr; rewrite -> ExpandOr.
       intuition.
    -- destruct P as [P1 P2].
       revert A; simpl.
       rewrite -> ExpandAnd; rewrite -> ExpandAnd.
       intuition.
  - intros.
    unfold nested_inversion.
    intro.
    set (V := (var Vars v)).
    apply (H V).
    reflexivity.
Qed.

Lemma forall_not:
  forall (Vars : Type) (f : Formula Vars) (G : Vars -> bool),
  (forall interpretation : Vars -> bool, Is_true (negb (interpretation [f]))) -> (Is_true(G [f]) <-> False).
Proof.
  intuition.
  apply -> ExpandNot in H.
  intuition.
  destruct H.
  apply H0.
Qed.

(* Доказательство в одну сторону *)
Theorem task7_part_b:
  forall (Vars : Type) (f : Formula Vars),
    ((|= f) \/ (|= !f) \/ (exists (g : Formula Vars), (IsPositive g) /\ (g ~ f))) -> (IsMonotonic f).
Proof.
  intros.
  intuition.
  - unfold "|= _" in H0.
    unfold IsMonotonic.
    intuition.
  - unfold "|= _" in H.
    unfold IsMonotonic.
    intuition.
    unfold IsModelOf.
    unfold IsModelOf in H.
    simpl in H.
    apply (forall_not Vars f G H).
    apply (forall_not Vars f F0 H) in H1.
    apply H1.
  - unfold IsMonotonic.
    intuition.
    destruct H.
    rewrite -> Equal_is_Equal2 in H.
    destruct H.
    unfold IsEqual2 in H0.
    rewrite <- (H0 G).
    rewrite <- (H0 F0) in H1.
    apply (task7_part_a Vars F0 G).
    -- apply H2.
    -- apply H.
    -- apply H1.
Qed.

Lemma double_monotonic:
  forall (Vars : Type) (f1 f2: Formula Vars), IsMonotonic (and Vars f1 f2) -> ((IsMonotonic f1) /\ (IsMonotonic f2)).
Proof.
  intros.
  unfold IsMonotonic in H.
  unfold IsModelOf in H.
  simpl in H.
  assert (L : (forall F G : Vars -> bool,
    Is_true (F [f1] && F [f2]) /\ nested_inversion F G -> Is_true (G [f1] && G [f2])) -> (forall F G : Vars -> bool,
    (Is_true (F [f1]) /\ Is_true (F [f2])) /\ nested_inversion F G -> (Is_true (G [f1]) /\ Is_true (G [f2])))).
  - intro; intro; intro; rewrite <- ExpandAnd; rewrite <- ExpandAnd; revert F0 G; apply H0. -
   unfold IsMonotonic.
   unfold IsModelOf.
   intuition.
   assert (Is_true (G [f1]) /\ Is_true (G [f2]) -> Is_true (G [f1])).
    -- intuition. --
    apply H1.
    apply (H0 F0 G).
    intuition.
Admitted.

Lemma ApplyIsDisj:
  forall (Vars : Type) (f : Formula Vars), IsDisj f -> IsConj f.
Proof.
   intuition.
   destruct f.
   - simpl. intuition.
   - simpl. intuition.
   - simpl. intuition.
   - simpl. intuition.
   - simpl. intuition.
Qed.


(* Доказательство в обратную сторону. Сразу будем считать, что формула в КНФ *)
Theorem task7_part_b_2:
  forall (Vars : Type) (f : Formula Vars),
    (IsMonotonic f) /\ (IsConj f) -> ((|= f) \/ (|= !f) \/ (exists (g : Formula Vars), (IsPositive g) /\ (g ~ f))).
Proof.
  intuition.
  induction f.
  - unfold "|= _".
    destruct c.
    -- unfold IsModelOf. intuition.
    -- unfold IsModelOf. intuition.
  - right; right.
    exists (var Vars v); simpl.
    rewrite Equal_is_Equal2.
    unfold IsEqual2.
    intuition.
  - unfold IsConj in H1. unfold IsDisj in H1. unfold IsLiteral in H1. intuition. destruct f.
    -- intuition.
    -- unfold IsMonotonic in H0. destruct (H0 (fun _ => false) (fun _ => true)). unfold nested_inversion. intuition.
    -- intuition.
    -- intuition.
    -- intuition.
  - unfold IsConj in H1; intuition.
    simpl in H.
    intuition.
  - unfold IsConj in H1.
    intuition.
    simpl in H.
    intuition.
    right; right.
    apply double_monotonic in H0.
    intuition.
    -- destruct H0.
    --- apply ApplyIsDisj. apply H1.
    --- exists (const Vars T).
        simpl. intuition.
        unfold "|= _" in H4.
        unfold IsModelOf in H4.
        unfold "|= _" in H0.
        unfold IsModelOf in H0.
        rewrite Equal_is_Equal2.
        unfold IsEqual2.
        simpl.
        intuition.
    --- intuition.
    ---- exists (const Vars F). simpl.
        rewrite Equal_is_Equal2.
        unfold IsEqual2.
        simpl.
        unfold "|= _" in H5.
        unfold IsModelOf in H5.
        simpl in H5.
        intuition.
        rewrite ExpandAnd in H0.
        intuition.
        revert H6.
        assert ((Is_true (interpretation [f1]) -> False) <-> Is_true (negb (interpretation [f1]))).
        ----- intuition. rewrite ExpandNot in H0. intuition. -----
        apply H0. intuition.
   ---- unfold "|= _" in H4.
        unfold IsModelOf in H4.
        destruct H5. exists x. intuition. rewrite Equal_is_Equal2. unfold IsEqual2.
        simpl. intuition.
        ----- rewrite ExpandAnd. intuition.
              rewrite Equal_is_Equal2 in H6. unfold IsEqual2 in H6.
              rewrite (H6 interpretation) in H0.
              apply H0.
        ----- rewrite ExpandAnd in H0. intuition.
              rewrite Equal_is_Equal2 in H6. unfold IsEqual2 in H6.
              rewrite <- (H6 interpretation) in H7.
              apply H7.
  -- exists (const Vars F). simpl.
     unfold "|= _" in H5.
     unfold IsModelOf in H5.
     simpl in H5.
     rewrite Equal_is_Equal2. unfold IsEqual2.
     simpl. intuition.
     assert ((Is_true (interpretation [f2]) -> False) <-> Is_true (negb (interpretation [f2]))).
     ----- intuition; rewrite ExpandNot in H6; intuition. -----
     rewrite ExpandAnd in H4.
     intuition.
  -- destruct H0.
  --- apply ApplyIsDisj. apply H1.
  --- destruct H5.
      exists x.
      intuition.
      rewrite Equal_is_Equal2. unfold IsEqual2.
      simpl; intuition.
      ---- unfold "|= _" in H0.
           unfold IsModelOf in H0.
           simpl in H0.
           rewrite Equal_is_Equal2 in H6. unfold IsEqual2 in H6.
           rewrite ExpandAnd.
           intuition.
           apply (H6 interpretation) in H4.
           apply H4.
      ---- rewrite Equal_is_Equal2 in H6. unfold IsEqual2 in H6.
           rewrite ExpandAnd in H4.
           intuition.
           apply <- (H6 interpretation) in H8.
           apply H8.
  --- destruct H0.
      ---- exists (const Vars F).
           unfold "|= _" in H0.
           unfold IsModelOf in H0.
           simpl in H0.
           simpl.
           rewrite Equal_is_Equal2. unfold IsEqual2.
           simpl. intuition.
           rewrite ExpandAnd in H4.
           assert ((Is_true (interpretation [f1]) -> False) <-> Is_true (negb (interpretation [f1]))).
           ----- intuition. rewrite ExpandNot in H4. intuition. -----
           intuition.
      ---- destruct H5, H0.
           exists (x & x0).
           simpl; intuition.
           rewrite Equal_is_Equal2. unfold IsEqual2.
           rewrite Equal_is_Equal2 in H6, H7. unfold IsEqual2 in H6, H7.
           simpl. intro. rewrite ExpandAnd. rewrite ExpandAnd. intuition.
           ----- apply (H7 interpretation). apply H9.
           ----- apply (H6 interpretation). apply H8.
           ----- apply (H6 interpretation). apply H9.
           ----- apply (H7 interpretation). apply H8.
Qed.

End task_7.
