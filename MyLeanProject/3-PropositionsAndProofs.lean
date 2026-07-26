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
