Require Import
  Utf8.

(* Code *)

Inductive op : Set :=
  | add : op
  | mul : op.

Inductive expr : Set :=
  | num : nat → expr
  | biop : op → expr → expr → expr.

Notation "x .+ y" := (biop add x y) (at level 50, left associativity).
Notation "x .* y" := (biop mul x y) (at level 40, left associativity).
Notation "[ x ]" := (num x).

Example sample_expr := [3] .* [4] .+ [5] .* [9].

Definition d_op (o : op) : nat → nat → nat :=
  match o with
  | add => plus
  | mul => mult
  end.

Fixpoint denotation (e : expr) : nat :=
  match e with
  | num x => x
  | biop o l r => d_op o (denotation l) (denotation r)
  end.

Eval compute in (denotation sample_expr).

Inductive instr : nat → nat → Set :=
  | ipush : forall {s}, nat → instr s (S s)
  | ibiop : forall {s}, op → instr (S (S s)) (S s).

Inductive code : nat → nat → Set :=
  | cnil : forall {s}, code s s
  | csnoc : forall {s t u}, code s t → instr t u → code s u.

Fixpoint cappend {s t u : nat} (p : code s t) (q : code t u) : code s u.
  destruct q;
    assumption ||
    exact (csnoc (cappend s s0 t p q) i).
Defined.
Print cappend.

Fixpoint compile (e : expr) {s : nat} : code s (S s) :=
  match e with
  | num x => csnoc cnil (ipush x)
  | biop o l r => csnoc (cappend (compile l) (compile r)) (ibiop o)
  end.

Eval compute in @compile sample_expr 0.

Inductive stack (A : Set) : nat → Set :=
  | snil : stack A O
  | spush : forall {n}, A → stack A n → stack A (S n).

Definition pop {A} {s} (st : stack A (S s)) :=
  match st with
  | spush _ x xs => (x,xs)
  end.

Definition exec_op (o : op) {s} (st : stack nat (S (S s))) : stack nat (S s) :=
  let (y,st') := pop st in
  let (x,st'') := pop st' in
  spush _ (d_op o x y) st''.
  
Definition exec {s t} (i : instr s t) : stack nat s → stack nat t.
  destruct i;
    exact (spush _ n) ||
    exact (exec_op o).
Defined.
Print exec.    

Fixpoint run {s t} (c : code s t) (st : stack nat s) : stack nat t.
  destruct c;
    assumption ||
    exact (exec i (run _ _ c st)).
Defined.
Print run.

Definition empty_stack {A} := snil A.
Definition singleton {A : Set} (x : A) := spush A x empty_stack.

Eval compute in run (compile sample_expr) empty_stack.

(* Proofs *)

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

Lemma correctness_strong : forall (e : expr) {s} {st : stack nat s}, run (compile e) st = spush _ (denotation e) st. 
Proof.
  induction e; try reflexivity.
  intros; simpl;
    rewrite (run_cappend (compile e1) (compile e2));
    rewrite (IHe1 _ st);
    rewrite (IHe2 _ (spush nat (denotation e1) st));
  unfold exec_op; reflexivity.
Qed.

Theorem correctness : forall e : expr, run (compile e) empty_stack = singleton (denotation e).
Proof.
  intro e; apply (correctness_strong e).
Qed.






























