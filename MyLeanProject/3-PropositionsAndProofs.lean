/- 3.1 Propositions as types -/
/-
We could introduce a new type, Prop, to represent
propositions, and introduce constructors to build
new propositions from others.

We could then introduce, for each element p: Prop,
another type Proof p, for the type of proofs of p.

An "axiom" would be a constant of such type.
#check Proof
| Proof (p: Prop): Type

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)

#check and_commut p q
| and_commut p q : Proof (Implies (p ^ q) (q ^ p))

We could represent the rule of modus ponens as

axiom modus_ponens (p q: Prop):
      Proof (Implies p q) -> Proof p -> Proof q

This approach would be reasonable.

Simplifications are possible though

We can avoid writing the term Proof by conflating Proof p with p itself.
Whenever we have p : Prop, we can interpret p as a type, the type of its
proofs. We can then read t : p as the assertion that t is a proof of p
Once we make this identification, implications between propositions p and
q corresponds to having a function that takes any element of p to an
element of q. As a result, we can use the usual function space p -> q

This is the approach followed by the Calculus of Constructions.
This is an instance of the Curry-Howard isomorphism, or the
propositions-as-types paradigm.

The type Prop is syntactic sugar for Sort 0, the bottom of the type
hierarchy. Type u is just Sort u+1

THere are at least two ways of thinking about propositions as types.
To some who take a constructive view of logic and mathematics, this is
a faithful rendering of what it means to be a proposition: a prop p
reps a sort of data type, a specification of the type of data that
constitutes a proof. A proof of p is then simply an object t: p of the
right type

Or view it as a simple coding trick. To each prop p we associate a type
that is empty if p is false and has a single element, say *, if p is
true, we say that p is inhabited.
So constructing an element t : p tells us that p is indeed true.
And a proof p -> q uses "the fact that p is true" to obtain "the fact that
q is true."

If p : Prop is any proposition, the two elements t1 t2: p is definitionally
equal, the same way (fun x => t) and t[s/x] are definitionally equal. This
is called proof irrelevance, and is consistent with the interpretation
in the last paragraph. It means that even though we can treat proofs t : p
as ordinary objects, they carry no information beyond the fact that p is
true.

Lean's task, as a proof assistant, is to help us to construct such a term,
t, and to verify that it is well-formed and has the correct type
-/

/- 3.2 Working with Propositions as Types -/
/-
In this paradigm, theorems involving only -> can be proved using
lambda abstraction and application.
-/

set_option linter.unusedVariables false

variable {p : Prop}
variable {q : Prop}

theorem t1 : p -> q -> p := fun hp : p => fun hq : q => hp
/-
compare with fun x : α => fun y : β => x
The only difference is that p and q are elements of Prop rather than
Type

Note that the theorem command is just a version of the def command
Proving that p -> q -> p is the same as defining an element of the
associated type

Lean tags proofs as irreducible, which tells the elaborator that there
is generally no need to unfold them when processing a file.
Lean can process and check proofs in parallel, since assessing the
correctness of one proof does not require knowing the details of another.
-/

#print t1

/-
the lambda abstractions hp : p and hq : q can be viewed as temporary
assumptions in the proof of t1.

We can also specify the type of the final term hp, with a show statement
-/
theorem t11: p -> q -> p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp

/-
adding such extra information can improve the clarity of a proof and help
detect errors when writing a proof. The show command does nothing more than
annotate the type

As with ordinary definitions, we can move the lambda abstracted variables
to the left of the colon
-/
theorem t12 (hp : p) (hq : q) : p := hp
#print t12

/- we can then use the theorem t1 just as a function application -/
axiom hp : p

theorem t2 : q -> p := t1 hp

/-
declaring an axiom hp : p is the same as that p is true as witnessed by hp
Applying the theorem t1 : p -> q -> p to the fact that hp : p that p is
true yields the theorem t1 hp : q -> p

Because p and q have been declared as variables, Lean will generalize them
for us automatically. When generalized, we can then apply it to different
pairs of propositions, to obtain different instances of the general theorem
-/
theorem t13 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t13 p q
#check t13 r s
#check t13 (r -> s) (s -> r)

variable (h: r -> s)
#check t13 (r -> s) (s -> r) h /- here the variable h of type r -> s can be viewed as the premise r -> s holds -/

variable (pp qq rr ss : Prop)
theorem t21 (h₁ : q -> r) (h₂ : p -> q) : p -> r :=
        fun h₃ : p =>
        show r from h₁ (h₂ h₃)

/-
theorem t21 says
if p -> q and q -> r, then p -> r
-/

/- 3.3 Propositional Logic -/
/- All propositional logic take values in prop -/
#check p -> q -> p ∧ q
#check p -> q <-> False
#check p ∨ q -> q ∨ p

/- 3.3.1 Conjunction -/
example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp: p) (hq :q) => And.intro hp hq

/-
The expression And.left h creates a proof of p from a proof h : p ∧ q.
Similarly, And.right h is a proof of q. They are commonly known as the
left and right and-elimination rules
-/
example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

/- we can now prove p ∧ q -> q ∧ p with the following term -/
example (h : p ∧ q) : q ∧ p :=
        And.intro (And.right h) (And.left h)

/- we can also rewrite the proof as follows -/
example (h: p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

/-
it is common to iterate construction like "And."
As such Lean also allows you to flatten nested constructors that
associate to the right, so these two proofs are equivalent
-/
variable (p q : Prop)
example (h: p ∧ q) : q ∧ p ∧ q :=
        ⟨h.right, ⟨h.left, h.right⟩⟩
example (h: p ∧ q) : q ∧ p ∧ q :=
        ⟨h.right, h.left, h.right⟩

/- 3.3.2 Disjunction -/
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq
example (h : p ∨ q) : q ∨ p := Or.elim h
        (fun hp : p =>
             show q ∨ p from Or.intro_right q hp)
        (fun hq : q =>
             show q ∨ p from Or.intro_left p hq)
/- It can also be written more precisely -/
example (h: p ∨ q) : q ∨ p :=
        Or.elim h (λ hp => Or.inr hp) (fun hq => Or.inl hq)

/- 3.3.3 Negation and Falsity -/
example (hpq : p -> q) (hnq : ¬q) : ¬p :=
        fun hp : p =>
        show False from hnq (hpq hp)

/-
The connetive False has a single elimination rule, False.elim
which expresses the fact that anything follows from a contradiction.
This rule is something called ex falso
-/
example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)

/- Deriving a fact from contradictory hypotheses is represented by absurd -/
example (hp : p) (hnp : ¬p) : q := absurd hp hnp
example (hnp : ¬p) (hq : q) (hqp: q -> p) : r := absurd (hqp hq) hnp

/- 3.3.4 Logical Equivalence -/
theorem and_swap : p ∧ q <-> q ∧ p :=
        Iff.intro
            (fun h : p ∧ q =>
                 show q ∧ p from And.intro (And.right h) (And.left h))
            (fun h : q ∧ p =>
                 show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q

variable (h₁ : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h₁ 

/-
We can use the anonymous constructor notation to construct a proof of
p <-> q from proofs of the forward and backwards directions, and use the
. notation with mp and mpr.
-/

theorem and_swap2 : p ∧ q <-> q ∧ p :=
        ⟨ λ h => ⟨h.right, h.left⟩, λ h => ⟨h.right, h.left⟩ ⟩
example (h: p ∧ q) : q ∧ p := (and_swap p q).mp h

/- 3.4 Introducing Auxiliary Subgoals -/
/-
the have construct introduces an auxiliary subgoal in a proof, this
helps to structure long proofs
-/
example (h : p ∧ q) : q ∧ p :=
        have hp : p := h.left
        have hq : q := h.right
        show q ∧ p from ⟨hq, hp⟩
/-
internally, "have h : p := s; t" produces the term "(λ (h : p) => t) s"
In order words, s is a proof of p, t is a proof of the desired conclusion
assuming h : p

We can also use "suffices to show" construction, to reason backwards
-/
example (h: p ∧ q) : q ∧ p :=
        have hp : p := h.left
        suffices hq : q from And.intro hq hp
        show q from And.right h

/- 3.5 Classical Logic -/
/-
The introduction and elimination rules we have seen so far are all
constructive. Ordinary classical logic adds to this the law of the
excluded middle, p ∨ ¬p. To use this, you have to open the classical
namespace
-/
section
open Classical

#check em p
/-
One consequence of the law of excluded middle is the principle of
double-negation elimination

This allows you to prove any prop p, by assuming not p and deriving False,
because this amounts to proving not not p.
So you can do a proof by contradiction
-/
theorem dne {p : Prop} (h : ¬¬p) : p :=
        Or.elim (em p)
                (λ hp : p => hp)
                (λ hnp : ¬p => absurd hnp h)

theorem _em {p : Prop} (h : p) : p ∨ ¬p :=
        dne (λ h1 : ¬(p ∨ ¬p) =>
             have hnp : ¬p := (λ (hp : p) => h1 (Or.inl hp))
             h1 (Or.inr hnp))

/- One could carry out a proof by cases -/
example (h: ¬¬p) : p :=
        byCases
            (fun h1 : p => h1)
            (fun h1 : ¬p => absurd h1 h)

/- Or by contradiction -/
example (h: ¬¬p) : p :=
        byContradiction
            (λ h1 : ¬p =>
               show False from h h1)

/-
If you are not used to thinking constructively, it may take some time
to get a sense of where classical reasoning is used. From a constructive
standpoint, knowing that p and q are not both true does not necessarily
tell you which one is false
-/
example (h: ¬(p ∧ q)) : ¬p ∨ ¬q :=
        Or.elim (em p)
                (λ hp : p =>
                   Or.inr
                    (show ¬q from
                          fun hq : q => h ⟨hp, hq⟩))
                (λ hp : ¬p => Or.inl hp)

end

/-
The sorry identifier produces a proof of anything, which is useful for
building long proofs incrementally. Start writing from top down, using sorry
to fill in the subproofs. Make sure Lean accepts the term with all the sorry's
Then go back to replace each sorry with an actual proof

Instead of using sorry, you can use _ as a placeholder. This tells Lean
that the argument is implicit, and should be filled in automatically.
If Lean does so and fails with "don't know how to synthesize placeholder,"
Lean reports the subgoal that needs to be filled at that point.
You can then construct a proof by incrementally filling in these
placeholders
-/


/- 3.7 Exercises -/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := ⟨λ h => ⟨h.right, h.left⟩, λ h => ⟨h.right, h.left⟩⟩
example : p ∨ q ↔ q ∨ p := 
        Iff.intro
            (λ h : p ∨ q =>
               Or.elim h
                       (λ hp : p => Or.inr hp)
                       (λ hq : q => Or.inl hq))
            (λ h : q ∨ p =>
               Or.elim h
                       (λ hq : q => Or.inr hq)
                       (λ hp : p => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
        Iff.intro
            (λ (h : (p ∧ q) ∧ r) =>
               have hqr : q ∧ r := ⟨h.left.right, h.right⟩
               have hp : p := h.left.left
               show p ∧ (q ∧ r) from ⟨hp, hqr⟩)
            (λ h : p ∧ (q ∧ r) =>
               have hpq : p ∧ q := ⟨h.left, h.right.left⟩
               have hr : r := h.right.right
               show (p ∧ q) ∧ r from ⟨hpq, hr⟩)
            
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
        Iff.intro
            (λ (h : (p ∨ q) ∨ r) =>
               Or.elim h
                       (λ hpq : p ∨ q => Or.elim hpq
                                                 (λ hp : p => Or.inl hp)
                                                 (λ hq : q => Or.inr (Or.inl hq)))
                       (λ hr : r => Or.inr (Or.inr hr)))
            (λ (h : p ∨ (q ∨ r)) =>
               Or.elim h
                       (λ hp : p => Or.inl (Or.inl hp))
                       (λ hqr : q ∨ r => Or.elim hqr
                                                 (λ hq : q => Or.inl (Or.inr hq))
                                                 (λ hr : r => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
        Iff.intro
            (λ h: p ∧ (q ∨ r) =>
               have hp : p := h.left
               have hqr : q ∨ r := h.right
               Or.elim hqr
                       (λ hq : q => Or.inl ⟨hp, hq⟩)
                       (λ hr : r => Or.inr ⟨hp, hr⟩))
            (λ h: (p ∧ q) ∨ (p ∧ r) =>
               Or.elim h
                       (λ hpq : p ∧ q => ⟨hpq.left, Or.inl hpq.right⟩)
                       (λ hpr : p ∧ r => ⟨hpr.left, Or.inr hpr.right⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := ⟨
        (λ h: p ∨ (q ∧ r) =>
           have hpq : p ∨ q := Or.elim h
                                       (λ hp: p => Or.inl hp)
                                       (λ hqr: q ∧ r => Or.inr hqr.left)
           have hpr : p ∨ r := Or.elim h
                                       (λ hp: p => Or.inl hp)
                                       (λ hqr: q ∧ r => Or.inr hqr.right)
           ⟨hpq, hpr⟩),
        (λ h: (p ∨ q) ∧ (p ∨ r) =>
           have hpq : p ∨ q := h.left
           have hpr : p ∨ r := h.right
           Or.elim hpq
                   (λ hp : p => Or.inl hp)
                   (λ hq : q =>
                      Or.elim hpr
                              (λ hp : p => Or.inl hp)
                              (λ hr : r => Or.inr ⟨hq, hr⟩)))
        ⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := ⟨
        (λ h: p -> (q -> r) => (λ hpq: p ∧ q => h hpq.left hpq.right)),
        (λ h: p ∧ q -> r => λ hp: p => λ hq: q => h ⟨hp, hq⟩)
        ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := ⟨
        (λ h: ((p ∨ q) -> r) => ⟨
           (λ hp: p => h (Or.intro_left q hp)),
           (λ hq: q => h (Or.intro_right p hq))
        ⟩),
        (λ h: (p -> r) ∧ (q -> r) =>
           (λ hpq: p ∨ q =>
              Or.elim hpq
                      (λ hp : p => (And.left h) hp)
                      (λ hq : q => (And.right h) hq)))
⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := ⟨
        (λ h: ¬(p ∨ q) => ⟨
           (λ hp: p => h (Or.intro_left q hp)),
           (λ hq: q => h (Or.intro_right p hq))
        ⟩),
        (λ h: (¬p ∧ ¬q) =>
           λ hpq: (p ∨ q) =>
             Or.elim hpq
                     (λ hp: p => h.left hp)
                     (λ hq: q => h.right hq))
⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
        (λ h: ¬p ∨ ¬q =>
           λ hpq: (p ∧ q) =>
             Or.elim h
                     (λ hp: ¬p => hp hpq.left)
                     (λ hq: ¬q => hq hpq.right))

example : ¬(p ∧ ¬p) :=
        (λ h: (p ∧ ¬p) => h.right h.left)

example : p ∧ ¬q → ¬(p → q) :=
        (λ h: (p ∧ ¬q) =>
           λ hpq: (p -> q) =>
             h.right (hpq h.left))

example : ¬p → (p → q) :=
        (λ h: ¬p => λ hp: p => False.elim (h hp))

example : (¬p ∨ q) → (p → q) :=
        (λ h: (¬p ∨ q) =>
           λ hp: p => Or.elim h
                              (λ hnp: ¬p => False.elim (hnp hp))
                              (λ hq: q => hq))

example : p ∨ False ↔ p := ⟨
        (λ h: p ∨ False =>
           Or.elim h
                   (λ hp: p => hp)
                   (λ f: False => False.elim f)),
        (λ h: p => Or.inl h)
⟩

example : p ∧ False ↔ False := ⟨
        (λ h: p ∧ False => h.right),
        (λ h: False => False.elim h)
⟩

example : (p → q) → (¬q → ¬p) :=
        (λ h: (p -> q) =>
           λ hnq: ¬q =>
             λ hp: p => hnq (h hp))

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
        (λ h: p -> q ∨ r =>
           Or.elim (em p)
                   (λ hp: p =>
                      Or.elim (h hp)
                              (λ hq: q => Or.inl (λ _ : p => hq))
                              (λ hr: r => Or.inr (λ _ : p => hr)))
                   (λ hnp: ¬p => False.elim (hnp hp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
        (λ h: ¬(p ∧ q) =>
           Or.elim (em p)
                   (λ hp: p =>
                      Or.elim (em q)
                              (λ hq: q => False.elim (h ⟨hp, hq⟩))
                              (λ hnq: ¬q => Or.inr hnq))
                   (λ hnp: ¬p => Or.inl hnp))

example : ¬(p → q) → p ∧ ¬q :=
        (λ h: ¬(p -> q) => ⟨
           (Or.elim (em p)
                    (λ hp: p => hp)
                    (λ hnp: ¬p =>
                       have hpq: p -> q := λ hp: p => False.elim (hnp hp)
                       False.elim (h hpq)
                       )),
           (λ hq: q =>
              have hpq: p -> q := λ hp: p => hq
              h hpq)
        ⟩)

example : (p → q) → (¬p ∨ q) :=
        (λ h: p -> q =>
           Or.elim (em p)
                   (λ hp: p => Or.inr (h hp))
                   (λ hnp: ¬p => Or.inl hnp))

example : (¬q → ¬p) → (p → q) :=
        (λ h: (¬q -> ¬p) =>
           Or.elim (em q)
                   (λ hq: q => λ _: p => hq)
                   (λ hnq: ¬q =>
                      (λ hp: p =>
                        False.elim ((h hnq) hp))))

example : p ∨ ¬p :=
        Or.elim (em p)
                (λ hp: p => Or.inl hp)
                (λ hnp: ¬p => Or.inr hnp)

example : (((p → q) → p) → p) :=
        (λ h: ((p -> q) -> p) =>
           Or.elim (em p)
                   (λ hp: p => hp)
                   (λ hnp: ¬p =>
                      have hpq: p -> q := (λ hp: p => False.elim (hnp hp))
                      h hpq))
