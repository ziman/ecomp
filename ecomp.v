Require Import
  Utf8 String List
  FMapWeakList FSetWeakList DecidableType
  JMeq.

(* Maps from strings to nats. *)
Declare Module string_as_DecType : DecidableType
  with Definition t := string
  with Definition eq := @eq string
  with Definition eq_dec := string_dec.

Module StringMap := FMapWeakList.Make string_as_DecType.
Module StringSet := FSetWeakList.Make string_as_DecType.

Definition listSet : list string → StringSet.t := fold_right StringSet.add StringSet.empty.
Definition keys {A} (m : StringMap.t A) : StringSet.t := listSet (map (@fst _ _) (StringMap.elements m)). 

(* Set of variables. *)
Definition vars := StringSet.t.
Definition ø := StringSet.empty.
Notation "x ∩ y" := (StringSet.inter x y) (at level 50, left associativity).
Notation "x ∪ y" := (StringSet.union x y) (at level 40, left associativity).
Notation "x ⊆ y" := (StringSet.Subset x y) (at level 30, no associativity).

(* A variable binding is just a map from strings to nats. *)
Definition binds := StringMap.t nat.

(* Operators and expressions.  *)
Inductive op : Set :=
  | add : op
  | mul : op.

(* An expression is indexed by its free variables. *)
Inductive expr : vars → Type :=
  | num : nat → expr ø
  | var : forall s : string, expr (StringSet.singleton s)
  | biop : forall {s t : vars}, op → expr s → expr t → expr (s ∪ t).

Notation "x .+ y" := (biop add x y) (at level 50, left associativity).
Notation "x .* y" := (biop mul x y) (at level 40, left associativity).
Notation "[ x ]" := (num x).

Example sample_expr := [3] .* [4] .+ [5] .* ([9] .+ var "a" ).

(* Denotational semantics of ops and expressions. *)
Definition d_op (o : op) : nat → nat → nat :=
  match o with
  | add => plus
  | mul => mult
  end.

Lemma keys_in : forall (s : StringSet.t) (m : StringMap.t nat) (v : string),
  StringSet.In v s → StringMap.In v m.
Proof.
  intros. unfold StringMap.In; unfold StringMap.Raw.PX.In.

Program Fixpoint denotation {s} (e : expr s) (bs : binds) (pf : s ⊆ keys bs) : nat :=
  match e with
  | num x => x
  | var v =>
      match StringMap.find v bs with
      | None => _
      | Some x => x
      end
  | biop p q o l r => d_op o (denotation l bs _) (denotation r bs _)
  end.
Next Obligation.
  pose proof (StringSet.singleton_2 (eq_refl v)) as vInS.
  pose proof (pf v vInS) as vInKeys.

Eval compute in (denotation sample_expr).

(* Instruction of a stack machine of type [instr s t] transforms
    a stack of size [s] into a stack of size [t]. *)
Inductive instr : nat → nat → Set :=
  | ipush : forall {s}, nat → instr s (S s)
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
Print cappend.

(* Compilation of an expression into code. *)
Fixpoint compile (e : expr) {s : nat} : code s (S s) :=
  match e with
  | num x => csnoc cnil (ipush x)
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
Definition exec {s t} (i : instr s t) : stack nat s → stack nat t.
  destruct i;
    exact (spush _ n) ||
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






























