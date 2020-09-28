Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical.

Module task_3_defs.
(* Several task-specific definitions are placed here, because "Notation" breaks "match". *)

Inductive ThreeVars : Type := pp | qq | rr.

Definition BadInterpretation (v : ThreeVars) : bool := 
  match v with
  | pp => true
  | _ => false
  end.
End task_3_defs.

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


Definition IsModelOf {Vars : Type} (interpretation : Vars -> bool) (prop : Formula Vars) := 
  Is_true (ApplyInterpretation interpretation prop).

Definition IsTautology {Vars : Type} (p: Formula Vars) :=
  forall interpretation : Vars -> bool, IsModelOf interpretation p.

Definition IsInheritsModels {Vars : Type} (from to: Formula Vars) :=
  forall interpretation : Vars -> bool, 
    Is_true (implB (ApplyInterpretation interpretation from) (ApplyInterpretation interpretation to)).

Definition IsEqual {Vars : Type} (p1 p2: Formula Vars) :=
  forall interpretation : Vars -> bool, 
      Is_true (andb
      (implB (ApplyInterpretation interpretation p1) (ApplyInterpretation interpretation p2))
      (implB (ApplyInterpretation interpretation p2) (ApplyInterpretation interpretation p1))).

Section task_1.
(* Пусть φ и ψ — формулы логики высказываний. Докажите, что  φ → ψ тогда и только
тогда, когда φ  ψ, и  φ ↔ ψ тогда и только тогда, когда φ ∼ ψ.*)

Theorem task1_part1 : 
forall (Vars : Type) (f g : Formula Vars), IsTautology (f --> g) = IsInheritsModels f g.
Proof.
  trivial.
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
forall (Vars : Type) (f g : Formula Vars), IsTautology (f <--> g) <-> IsEqual f g.
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

(* ¬¬φ ∼ φ *)
Theorem tast2_part_a:
  forall (Vars : Type) (f : Formula Vars), IsEqual (!!f) f.
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  case ApplyInterpretation.
  intuition.
  intuition.
Qed.

(*  φ ∨ ¬φ *)
Theorem tast2_part_b:
  forall (Vars : Type) (f : Formula Vars), IsTautology (f | !f).
Proof.
  intros.
  unfold IsTautology.
  intros.
  unfold IsModelOf.
  simpl.
  case ApplyInterpretation.
  intuition.
  intuition.
Qed.


(* φ ∧ (ψ ∨ η) ∼ (φ ∧ ψ) ∨ (φ ∧ η) *)
Theorem tast2_part_c:
  forall (Vars : Type) (f p n: Formula Vars), IsEqual (f & (p | n)) ((f & p) | (f & n)).
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  rewrite -> andb_orb_distrib_r.
  rewrite -> andb_diag.
  rewrite -> implB_is_implb.
  rewrite -> implb_same.
  reflexivity.
Qed.

(* φ ∨ (ψ ∧ η) ∼ (φ ∨ ψ) ∧ (φ ∨ η) *)
Theorem tast2_part_d:
  forall (Vars : Type) (f p n: Formula Vars), IsEqual (f | (p & n)) ((f | p) & (f | n)).
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  rewrite -> orb_andb_distrib_r.
  rewrite -> andb_diag.
  rewrite -> implB_is_implb.
  rewrite -> implb_same.
  reflexivity.
Qed.

(* φ ∨ (φ ∧ ψ) ∼ φ *)
Theorem tast2_part_e:
  forall (Vars : Type) (f p: Formula Vars), IsEqual (f | (f & p)) f.
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  rewrite -> absorption_orb.
  rewrite -> andb_diag.
  rewrite -> implB_is_implb.
  rewrite -> implb_same.
  reflexivity.
Qed.

(* φ ∧ (φ ∨ ψ) ∼ φ *)
Theorem tast2_part_f:
  forall (Vars : Type) (f p: Formula Vars), IsEqual (f & (f | p)) f.
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  rewrite -> absorption_andb.
  rewrite -> andb_diag.
  rewrite -> implB_is_implb.
  rewrite -> implb_same.
  reflexivity.
Qed.

(* ¬(φ ∧ ψ) ∼ ¬φ ∨ ¬ψ *)
Theorem tast2_part_g:
  forall (Vars : Type) (f g: Formula Vars), IsEqual (!(f & g)) (!f | !g).
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  rewrite -> negb_andb.
  rewrite -> andb_diag.
  rewrite -> implB_is_implb.
  rewrite -> implb_same.
  reflexivity.
Qed.

(* ¬(φ ∨ ψ) ∼ ¬φ ∧ ¬ψ *)
Theorem tast2_part_h:
  forall (Vars : Type) (f g: Formula Vars), IsEqual (!(f | g)) (!f & !g).
Proof.
  intros.
  unfold IsEqual.
  intros.
  simpl.
  rewrite -> negb_orb.
  rewrite -> andb_diag.
  rewrite -> implB_is_implb.
  rewrite -> implb_same.
  reflexivity.
Qed.

End task_2.

Section task_3.
Import task_3_defs.

(* (p → q) ↔ (¬q → ¬p) *)
Theorem tast3_part_a:
  forall (Vars : Type) (p q: Formula Vars), IsTautology ((p --> q) <--> (!q --> !p)).
Proof.
  intros.
  unfold IsTautology.
  intros.
  unfold IsModelOf.
  simpl.
  set (P := ApplyInterpretation interpretation p).
  set (Q := ApplyInterpretation interpretation q).
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

