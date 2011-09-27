Require Import
  Utf8 List String ListSet ProofIrrelevance.

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

Example sample_binds := ("x"%string, 9) :: ("y"%string, 4) :: nil.

Definition boundVars : binds → list string := map (@fst _ _).

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

(* Free variables of expressions. *)

Fixpoint freeVars_expr (e : expr) : list string :=
  match e with
  | num _ => nil
  | var v => v :: nil
  | biop _ l r => freeVars_expr l ∪ freeVars_expr r
  end.

Lemma expr_subvars_l : forall o l r, freeVars_expr l ⊆ freeVars_expr (biop o l r).
  intros; simpl; apply set_union_intro1; assumption.
Qed.

Lemma expr_subvars_r : forall o l r, freeVars_expr r ⊆ freeVars_expr (biop o l r).
  intros; simpl; apply set_union_intro2; assumption.
Qed.

(* Sample expression versus sample binds. *)

Example sample_pf : freeVars_expr sample_expr ⊆ boundVars sample_binds.
  simpl; intros; destruct H; left. assumption. destruct H.
Qed.

(* Denotational semantics of ops and expressions. *)
Definition d_op (o : op) : nat → nat → nat :=
  match o with
  | add => plus
  | mul => mult
  end.

Lemma elim_In : forall v bs, (forall x : string, v = x ∨ False → x ∈ boundVars bs) → v ∈ boundVars bs.
  intros; exact (H v (or_introl _ (eq_refl v))).
Qed.

Program Fixpoint denotation (e : expr) (bs : binds) (pf : freeVars_expr e ⊆ boundVars bs) {struct e} : nat :=
  match e with
  | num x => x 
  | var v => slookup v bs _
  | biop o l r => d_op o (denotation l bs _) (denotation r bs _)
  end.
Next Obligation.
  simpl in pf; apply elim_In; assumption.
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

Definition freeVars_instr {s t} (i : instr s t) : list string :=
  match i with
  | ipush _ _ => nil
  | iread _ v => v :: nil
  | ibiop _ _ => nil
  end.

(* Code is a snoc-sequence of instructions, indexed by its action on stack. *)
Inductive code : nat → nat → Set :=
  | cnil : forall {s}, code s s
  | csnoc : forall {s t u}, code s t → instr t u → code s u.

Fixpoint freeVars_code {s t} (c : code s t) : list string :=
  match c with
  | cnil _ => nil
  | csnoc _ _ _ c i => set_union string_dec (freeVars_code c) (freeVars_instr i)
  end.

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
Definition exec {s t} (i : instr s t) (bs : binds) (pf : freeVars_instr i ⊆ boundVars bs)
  : stack nat s → stack nat t.
Proof.
  destruct i.
    exact (spush _ n).
    rename s0 into v; simpl in pf; exact (spush _ (slookup v bs (elim_In v bs pf))).
    exact (exec_op o).
Defined.
Print exec.    

(* Operational semantics of a code sequence. *)

Lemma union_subset_l : forall M N O, (M ∪ N) ⊆ O → M ⊆ O.
  intros; apply (H x); apply (set_union_intro1); assumption.
Qed.

Lemma union_subset_r : forall M N O, (M ∪ N) ⊆ O → N ⊆ O.
  intros; apply (H x); apply (set_union_intro2); assumption.
Qed.

Fixpoint run {s t} (c : code s t) (bs : binds) (pf : freeVars_code c ⊆ boundVars bs) {struct c}
  : stack nat s → stack nat t.
Proof.
  intro st.
  destruct c.
    assumption.
    apply (exec i bs).
      simpl in pf; apply (union_subset_r (freeVars_code c) (freeVars_instr i) (boundVars bs)); assumption.
    apply (run _ _ c bs).
      simpl in pf; apply (union_subset_l (freeVars_code c) (freeVars_instr i) (boundVars bs)); assumption.
    assumption.
Defined.

(* Some utilities. *)
Definition empty_stack {A} := snil A.
Definition singleton {A : Set} (x : A) := spush A x empty_stack.

(* === Proofs === *)

Lemma cappend_cnil : forall {s t} (p : code s t), cappend cnil p = p.
  intros s t; induction p;
    reflexivity ||
    simpl; rewrite IHp; reflexivity.
Qed.

Lemma cappend_fvars : forall {v s t u c c'},
  v ∈ freeVars_code (@cappend s t u c c') → v ∈ (freeVars_code c ∪ freeVars_code c').
Proof.
  intros v s t u c c'; induction c'.
    intros; simpl; simpl in H; assumption.
    intros; simpl; simpl in H; pose proof (IHc' c); clear IHc'.
    apply set_union_intro; apply set_union_elim in H; case H.
      intros; pose proof (H0 H1); apply set_union_elim in H2.
        destruct H2.
          left; assumption.
          right; apply set_union_intro1; assumption.
      intros; right; apply set_union_intro2; assumption.
Qed.  

(* The function [compile] does not create free variables. *)
Lemma compile_fvars : forall e v s, v ∈ freeVars_code (@compile e s) → v ∈ freeVars_expr e.
  intro e; induction e; try (intros; simpl in H; assumption).
  intros. simpl; simpl in H.
    pose proof (cappend_fvars H).
    destruct (set_union_elim string_dec _ _ _ H0).
      apply set_union_intro1; exact (IHe1 v s H1).
      apply set_union_intro2; exact (IHe2 v (S s) H1).
Qed.

Lemma cappend_fvars_alt : forall {s t u : nat} {p : code s t} {q : code t u} {bs : binds},
  freeVars_code p ⊆ boundVars bs → freeVars_code q ⊆ boundVars bs
  → freeVars_code (cappend p q) ⊆ boundVars bs.
Proof.
  intros; pose proof (cappend_fvars H1); destruct (set_union_elim string_dec _ _ _ H2);
    exact (H x H3) ||
    exact (H0 x H3).
Qed.

Lemma run_cappend : forall {s t u} (p : code s t) (q : code t u) (st : stack nat s)
  (bs : binds) (pf_p : freeVars_code p ⊆ boundVars bs) (pf_q : freeVars_code q ⊆ boundVars bs)
  , run (cappend p q) bs (cappend_fvars_alt pf_p pf_q) st = run q bs pf_q (run p bs pf_p st).
Proof.
  intros s t u p q; revert p; induction q.
    intros; simpl;
      rewrite (proof_irrelevance (freeVars_code p ⊆ boundVars bs) (cappend_fvars_alt pf_p pf_q) pf_p);
      reflexivity.
    intros; simpl.
      set (pf_r := union_subset_r (freeVars_code (cappend p q)) (freeVars_instr i)
        (boundVars bs) (cappend_fvars_alt pf_p pf_q)).
      set (pf_s := union_subset_l (freeVars_code (cappend p q)) (freeVars_instr i)
        (boundVars bs) (cappend_fvars_alt pf_p pf_q)).
      set (pf_t := union_subset_r (freeVars_code q) (freeVars_instr i) (boundVars bs) pf_q).
      set (pf_u := union_subset_l (freeVars_code q) (freeVars_instr i) (boundVars bs) pf_q).
      pose proof (IHq p st bs pf_p pf_u).
      rewrite <- H.
      rewrite (proof_irrelevance (freeVars_code (cappend p q) ⊆ boundVars bs) (cappend_fvars_alt pf_p pf_u) pf_s).
      rewrite (proof_irrelevance (freeVars_instr i ⊆ boundVars bs) pf_r pf_t).
      reflexivity.
Qed.

Eval compute in run (compile sample_expr) (("x"%string,9)::nil) empty_stack.

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






























