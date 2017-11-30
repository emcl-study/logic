Require Import List.
Require Import Bool.

Section Syntax.

(* TODO: Define our language as L(R,F,V) with R containing our predicate symbols including
         their arity. We should use dependent types that take care of verifying the length
         instead of plain lists (matching arity).
         This should be according to Definition 4.1.
*)

Inductive Predicate : Set :=
 | P : Predicate
 | Q : Predicate
 | R : Predicate
 | S : Predicate.

Inductive Var : Set :=
 | X : Var
 | Y : Var
 | Z : Var.

Definition eqv (v1 v2:Var) : bool :=
  match v1, v2 with
    | X, X => true
    | X, Y => false
    | X, Z => false
    | Y, X => false
    | Y, Y => true
    | Y, Z => false
    | Z, X => false
    | Z, Y => false
    | Z, Z => true
  end.

Inductive Constant : Set :=
 | a : Constant
 | b : Constant
 | c : Constant
 | d : Constant.

Inductive Function : Set :=
 | f : Function
 | g : Function
 | h : Function.

(* Definition 4.2 *)
Inductive Term : Set :=
 | VariableTerm : Var -> Term
 | ConstantTerm : Constant -> Term
 | FunctionTerm : Function -> list Term -> Term.

(* The term 'c'. *)
Example HelloConstant := c.

(* The term 'f(c)'. *)
Example HelloFunction := FunctionTerm f (cons (ConstantTerm HelloConstant) nil).

(* Definition 4.3 *)
Record Atom := mkAtom {predicate: Predicate; terms: list Term}.

Example HelloAtom := mkAtom P (cons HelloFunction nil).

(* Definition 4.4 *)
Inductive Formula : Set :=
 | Atomic : Atom -> Formula
 | Negation : Formula -> Formula
 | Conjunction : Formula -> Formula -> Formula
 | Disjunction : Formula -> Formula -> Formula
 | ExistentiallyQuantified : Var -> Formula -> Formula
 | UniversallyQuantified : Var -> Formula -> Formula.

Example HelloFormula := Conjunction (Atomic HelloAtom) (Negation (Atomic HelloAtom)).

(* TODO: Definitions 4.5 - 4.20 are missing. *)

Section Semantics.

(* TODO: This should eventually be the type of the elements in our domain. *)
Definition A := Term.

(* Definition 4.20 *)
(* TODO: Get rid of constantInterpretation. *)
Record Interpretation := mkInterpretation {
 domain: list A;
 constantInterpretation: Constant -> A;
 functionInterpretation: Function -> list A -> A;
 predicateInterpretation: Predicate -> list Term -> bool
}.

(* Definition 4.21 *)
Definition VariableAssignment := Var -> A.

(* TODO: Actually use VariableAssignment instead of (Var -> Term). *)
Definition eval : Interpretation -> VariableAssignment -> Formula -> bool.

Definition herbrandTermInterpretation : Interpretation -> VariableAssignment -> Term -> Term.

Fixpoint herbrandTermInterpretation (i:Interpretation) (z:VariableAssignment) (t:Term) : Term :=
 match t with
  | VariableTerm v => (z v)
  | FunctionTerm n ts => (FunctionTerm n (map (herbrandTermInterpretation i z) ts))
  | ConstantTerm a => ((constantInterpretation i) a)
  | ConstantTerm b => ((constantInterpretation i) b)
  | ConstantTerm c => ((constantInterpretation i) c)
  | ConstantTerm d => ((constantInterpretation i) d)
 end.

Definition instantiate : Var -> A -> VariableAssignment -> VariableAssignment.

Definition instantiate (iv:Var) (it:A) (z:VariableAssignment) : VariableAssignment :=
  (fun v:Var => if (eqv iv v) then it else (z v)).

(* Definition 4.23 *)
Fixpoint eval (i:Interpretation) (z:VariableAssignment) (f:Formula) : bool :=
 match f with
  | Atomic (mkAtom p t) => (predicateInterpretation i) p (map (herbrandTermInterpretation i z) t)
  | Negation nf => (negb (eval i z nf))
  | Conjunction l r => (andb (eval i z l) (eval i z r))
  | Disjunction l r => (orb (eval i z l) (eval i z r))
  | ExistentiallyQuantified v ef => (fold_left
      (fun (y:bool) (x:Term) => if y then true else (eval i (instantiate v x z) ef))
      (domain i)
      false
    )
  | _ => false
 end.

(*
Theorem tautology : forall (F G: Formula) (I: Interpretation) (Z: VariableAssignment), (eval I Z (Disjunction F G)) = true.
Proof.
  intros I Z F G.
  ?
Qed.
*)


