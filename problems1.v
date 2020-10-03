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

Theorem task5_a2:
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

