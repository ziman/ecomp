Require Import
  Utf8 List String ListSet.

(* Operators and expressions.  *)
Inductive op : Set :=
  | add : op
  | mul : op.

Inductive expr : Set :=
  | num : nat → expr
  | var : string → expr
  | biop : op → expr → expr → expr.

Notation "x .+ y" := (biop add x y) (at level 50, left associativity).
Notation "x .* y" := (biop mul x y) (at level 40, left associativity).
Notation "[ x ]" := (num x).

Example sample_expr := [3] .* [4] .+ [5] .* ([9] .+ var "x").

(* Variable bindings. *)

Definition binds := list (string * nat).
Notation "x ∪ y" := (set_union string_dec x y) (at level 50, left associativity).
Notation "x ∈ S" := (set_In x S) (at level 30, no associativity).
Notation "M ⊆ N" := (forall x, x ∈ M → x ∈ N) (at level 30, no associativity).
Notation "f ∘ g" := (fun x => f (g x)) (at level 55, left associativity).

Fixpoint freeVars (e : expr) : list string :=
  match e with
  | num _ => nil
  | var v => v :: nil
  | biop _ l r => freeVars l ∪ freeVars r
  end.

Definition boundVars : binds → list string := map (@fst _ _).

Definition covered (bs : binds) (e : expr) := freeVars e ⊆ boundVars bs.

Fixpoint lookup (v : string) (bs : binds) : option nat :=
  match bs with
  | nil => None
  | (p,q) :: bs' => if string_dec p v then Some q else lookup v bs'
  end.

Lemma bound_weaken : forall s n v bs, s ≠ v → v ∈ boundVars ((s,n) :: bs) → v ∈ boundVars bs.
  intros; induction bs.
    simpl in H0; destruct H0; contradiction.
    simpl in H0; destruct H0.
      contradiction. destruct H0.
      simpl; left; assumption.
      simpl; right; assumption.
Qed.

Lemma lookup_pos : forall v bs, v ∈ boundVars bs → exists n, lookup v bs = Some n.
  intros.
  induction bs.
    simpl in H; contradiction.
    destruct a; simpl; destruct (string_dec s v).
      exists n; reflexivity.
      apply IHbs; apply (bound_weaken s n); assumption.
Qed.

Lemma lookup_pos_neg : forall v bs, v ∈ boundVars bs → lookup v bs ≠ None.
  intros; destruct (lookup_pos _ _ H) as [n H0]; rewrite H0; discriminate.
Qed.

Program Definition slookup (v : string) (bs : binds) (pf : v ∈ boundVars bs) : nat :=
  match lookup v bs with
  | None => _
  | Some x => x
  end.
Next Obligation.
  destruct (lookup_pos_neg v bs pf (eq_sym Heq_anonymous)).
Defined.

Lemma expr_subvars_l : forall o l r, freeVars l ⊆ freeVars (biop o l r).
  intros; simpl; apply set_union_intro1; assumption.
Qed.

Lemma expr_subvars_r : forall o l r, freeVars r ⊆ freeVars (biop o l r).
  intros; simpl; apply set_union_intro2; assumption.
Qed.

(* Denotational semantics of ops and expressions. *)
Definition d_op (o : op) : nat → nat → nat :=
  match o with
  | add => plus
  | mul => mult
  end.

Program Fixpoint denotation (e : expr) (bs : binds) (pf : freeVars e ⊆ boundVars bs) {struct e} : nat :=
  match e with
  | num x => x 
  | var v => slookup v bs _
  | biop o l r => d_op o (denotation l bs _) (denotation r bs _)
  end.
Next Obligation.
  simpl in pf; exact (pf v (or_introl _ (eq_refl v))).
Qed.
Next Obligation.
  apply pf; apply (expr_subvars_l o l r x H).
Qed.
Next Obligation.
  apply pf; apply (expr_subvars_r o l r x H).
Qed.

(* Makes coqtop hang at this point:
Eval compute in (denotation sample_expr).
*)

(* Instruction of a stack machine of type [instr s t] transforms
    a stack of size [s] into a stack of size [t]. *)
Inductive instr : nat → nat → Set :=
  | ipush : forall {s}, nat → instr s (S s)
  | iread : forall {s}, string → instr s (S s)
  | ibiop : forall {s}, op → instr (S (S s)) (S s).

(* Code is a snoc-sequence of instructions, indexed by its action on stack. *)
Inductive code : nat → nat → Set :=
  | cnil : forall {s}, code s s
  | csnoc : forall {s t u}, code s t → instr t u → code s u.

(* Concatenation of codes. *)
Fixpoint cappend {s t u : nat} (p : code s t) (q : code t u) : code s u.
  destruct q;
    assumption ||
    exact (csnoc (cappend s s0 t p q) i).
Defined.

(* Compilation of an expression into code. *)
Fixpoint compile (e : expr) {s : nat} : code s (S s) :=
  match e with
  | num x => csnoc cnil (ipush x)
  | var v => csnoc cnil (iread v)
  | biop o l r => csnoc (cappend (compile l) (compile r)) (ibiop o)
  end.

Eval compute in @compile sample_expr 0.

(* A size-indexed stack. *)
Inductive stack (A : Set) : nat → Set :=
  | snil : stack A O
  | spush : forall {n}, A → stack A n → stack A (S n).

Definition pop {A} {s} (st : stack A (S s)) :=
  match st with
  | spush _ x xs => (x,xs)
  end.

(* Operational semantics of a binary operator. *)
Definition exec_op (o : op) {s} (st : stack nat (S (S s))) : stack nat (S s) :=
  let (y,st') := pop st in
  let (x,st'') := pop st' in
  spush _ (d_op o x y) st''.
 
(* Operational semantics of an instruction. *)
Definition exec {s t} (i : instr s t) (bs : binds) : stack nat s → stack nat t.
  destruct i.
    exact (spush _ n).
    exact (spush _ s0).
    exact (exec_op o).
Defined.
Print exec.    

(* Operational semantics of a code sequence. *)
Fixpoint run {s t} (c : code s t) (st : stack nat s) : stack nat t.
  destruct c;
    assumption ||
    exact (exec i (run _ _ c st)).
Defined.
Print run.

(* Some utilities. *)
Definition empty_stack {A} := snil A.
Definition singleton {A : Set} (x : A) := spush A x empty_stack.

Eval compute in run (compile sample_expr) empty_stack.

(* === Proofs === *)

Lemma cappend_cnil : forall {s t} (p : code s t), cappend cnil p = p.
  intros s t; induction p;
    reflexivity ||
    simpl; rewrite IHp; reflexivity.
Qed.

Lemma run_cappend : forall {s t u} (p : code s t) (q : code t u) (st : stack nat s),
  run (cappend p q) st = run q (run p st).
Proof.
  intros s t u p q; revert p; induction q; intros;
    reflexivity ||
    simpl; rewrite (IHq p st); reflexivity.
Qed.

(* A variation of the correctness theorem, operating on any stack. *)
Lemma correctness_strong : forall (e : expr) {s} {st : stack nat s}, run (compile e) st = spush _ (denotation e) st. 
Proof.
  induction e; try reflexivity.
  intros; simpl;
    rewrite (run_cappend (compile e1) (compile e2));
    rewrite (IHe1 _ st);
    rewrite (IHe2 _ (spush nat (denotation e1) st));
  unfold exec_op; reflexivity.
Qed.

(* The main theorem proving the correctness of the compiler and interpreter. *)
Theorem correctness : forall e : expr, run (compile e) empty_stack = singleton (denotation e).
Proof.
  intro e; apply (correctness_strong e).
Qed.






























