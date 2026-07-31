/- 5.1 Entering Tactic Mode -/
/-
Stating a theorem or introducing a have statement creates a goal:
constructing a term with the expected type.
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := sorry
/-
On emacs, use C-h . to show the goal 

we can then write the goal as follows:
p q : prop
hp : p
hq : q
⊢ p ∧ q ∧ p
(vdash)

Ordinarily, you meet such a goal by writing an explicit term. But wherever
a term is expected, Leanallows us to insert instead a by <tactics> block,
where <tactics> is a sequence of commands, seperated by semicolons or
line breaks
-/
theorem test1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
        apply And.intro
        exact hp
        apply And.intro
        exact hq
        exact hp
/-
The apply tactic applies an expression, viewed as denoting a function
with zero or more arguments. It unifies the conclusion with
the expression in the current goal, and creates new goals for the
remaining arguments

The exact command is just a variant of apply which signals that the
expression given should fill the goal exactly. It is also more robust
than apply, since the elaborator takes the expected type, given
by the target of the goal, into account when processing the expression
that is being applied.
-/
#print test1

/-
Tactic commands can take compound expressions, not just single identifiers.
-/
theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
        apply And.intro hp
        exact And.intro hq hp

/-
Tactics that may produce multiple subgoals tag them.
For example, the tactic apply And.intro tagged the first subgoal as left,
and the second as right. In the case of the apply tactic, the tags
are inferred from the parameters' names used in the And.intro declaration.
You can structure your tactics using the notation
case <tag> => <tactics>.
-/
theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
        apply And.intro
        case left => exact hp
        case right =>
             apply And.intro
             case left => exact hq
             case right => exact hp

/-
The case is "focusing" on the selected goal

Lean also provides "bullet notation" . <tactics> 

The fullstop . is basically just a substitute for case <subgoal>
-/
theorem test4 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
        apply And.intro
        . exact hp
        . apply And.intro
          . exact hq
          . exact hp

/- 5.2 Basic Tactics -/
/-
In addition to apply and exact, another useful tactic is intro,
which introduces a hypothesis. What follows is an example of an
identity from propositional logic that we proved in the previous
chapter, now proved using tactics
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro h
          apply Or.elim (And.right h)
          . intro hq
            apply Or.inl
            apply And.intro
            . exact And.left h
            . exact hq
          . intro hr
            apply Or.inr
            apply And.intro
            . exact And.left h
            . exact hr
        . intro h
          apply Or.elim h
          . intro hpq
            apply And.intro
            . exact And.left hpq
            . apply Or.inl
              exact And.right hpq
          . intro hpr
            apply And.intro
            . exact And.left hpr
            . apply Or.inr
              exact And.right hpr

/-
The intro command can more generally be used to introduce a variable
of an type
-/
example (α : Type) : α → α := by
        intro a
        exact a

example (α : Type) : ∀ x : α, x = x := by
        intro x
        exact Eq.refl x

/- Or use it to introduce several variables -/
example : ∀ a b c : Nat, a = b → a = c → c = b := by
        intro a b c h₁ h₂
        exact Eq.trans (Eq.symm h₂) h₁

/-
As the apply tactic is a command for constructing function applications
interactively, the intro tactic is a command for constructing function
abstractions interactively (terms of the form λ x => e) As with
lambda abstraction notation, the intro tactic allows us to use an
implicit match.
-/
example (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
        intro ⟨w, hpw, hqw⟩
        exact ⟨w, hqw, hpw⟩

/- You can also provide multiple alternatives like in the match exp -/
example (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
        intro
        | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
        | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

/-
The intros tactic can be used without any arguments, in which case,
it will choose names and introduce as many variables as it can

The assumption tactic looks through the assumption in context of the
current goal, and if there is one matching the conclusion, it applies it.
-/
variable (x y z w : Nat)

example (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
        apply Eq.trans h₁
        apply Eq.trans h₂
        assumption

/- It will unify metavariables in the conclusion if necessary -/
variable (x y z w : Nat)
example (h₁ : x = y) (h₂: y = z) (h₃ : z = w) : x = w := by
        apply Eq.trans
        assumption /- Solves x = ?b with h₁-/
        apply Eq.trans
        assumption /- solves y = ?h₂.b with h₂ -/
        assumption /- solves z = w with h₃ -/

/-
The following example uses the intros command to introduce the three
variables and two hypotheses automatically
-/
example : ∀ a b c : Nat, a = b → a = c → c = b := by
        intros
        apply Eq.trans
        apply Eq.symm
        assumption
        assumption

/-
Names generated by Lean are inaccessible by default. Which makes the tactic
proofs more robust. However you can use the combinator unhygienic to
disable this restriction
-/
example : ∀ a b c : Nat, a = b → a = c → c = b := by unhygienic
        intros
        apply Eq.trans
        apply Eq.symm
        exact a_2
        exact a_1

/-
You could also use the rename_i tactic to rename the most recent
inaccessible names in your context. the tactic:
rename_i h1 _ h2
renames two of the last three hypotheses in your context
-/
example : ∀ a b c d : Nat, a = b → a = d → a = c → c = b := by
        intros
        rename_i h1 _ h2
        apply Eq.trans
        apply Eq.symm
        exact h2
        exact h1

/-
The rfl tactic solves goals that are reflexive relations applied to
definitionally equal arguments
-/
example (y : Nat) : (λ x : Nat => 0) y = 0 := by
        rfl

/-
The repeat combinator can be used to apply a tactic several times
-/
example : ∀ a b c : Nat, a = b → a = c → c = b := by
        intros
        apply Eq.trans
        apply Eq.symm
        repeat assumption

/-
Another tactic that is sometimes useful is the revert tactic, which is
kind of like an inverse to intro
-/
example (x : Nat) : x = x := by
        revert x
        intro y
        rfl

/-
Revert not only reverts an element of th econtext but also all the
subsequent elements of the context that depend on it
-/
example (x y : Nat) (h : x = y) : y = x := by
        revert x
        intros
        apply Eq.symm
        assumption

/-
You can also revert multiple elements of the context at once
-/
example (x y : Nat) (h : x = y) : y = x := by
        revert x y
        intros
        apply Eq.symm
        assumption

/-
You can replace an arbitrary expr in the goal by a fresh variable 
using the generalize tactic
-/
example : 3 = 3 := by
        generalize 3 = x
        revert x
        intro y
        rfl

/-
not every generalization preserves the validity of the goal.
Here, generalize replaces a goal that could be proved using
rfl with one that is not provable
-/
example : 2 + 3 = 5 := by
        generalize 3 = x
        sorry
        
/-
To preserve the validity of the previous goal, you could record the fact
that 3 has been replaced by x. You just need to provide a label

Here rw uses h to replace x by 3 again
-/
example : 2 + 3 = 5 := by
        generalize h : 3 = x
        rw [← h]

/- 5.3 More Tactics -/
/-
When applied to a goal of the form p ∨ q, you use tactics such as apply
Or.inl and apply Or.inr. Conversely, the cases tactic can be used
to decompose a disjunction
-/
example (p q : Prop) : p ∨ q → q ∨ p := by
        intro h
        cases h with
        | inl hp => apply Or.inr; exact hp
        | inr hq => apply Or.inl; exact hq

/-
The syntax is similar to the one used in match expr, but can be solved in
any order
-/
example (p q : Prop) : p ∨ q → q ∨ p := by
        intro h
        cases h with
        | inr hq => apply Or.inl; exact hq
        | inl hp => apply Or.inr; exact hp

/-
You can also use an unstructured cases without the with and a tactic
for each alternative
-/
example (p q : Prop) : p ∨ q → q ∨ p := by
        intro h
        cases h
        apply Or.inr
        assumption
        apply Or.inl
        assumption

/-
And is particularly useful when you can close several subgoals
using the same tactic
-/
example (p : Prop) : p ∨ p → p := by
        intro h
        cases h
        repeat assumption

/-
You can also use the combinator tac1 <;> tac2 to apply tac2 to each
subgoal produced by tactic tac1
-/
example (p : Prop) : p ∨ p → p := by
        intro h
        cases h <;> assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
        intro h
        cases h
        . apply Or.inr
          assumption
        . apply Or.inl
          assumption


example (p q : Prop) : p ∨ q → q ∨ p := by
        intro h
        cases h
        case inr h =>
             apply Or.inl
             assumption
        case inl h =>
             apply Or.inr
             assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
        intro h
        cases h
        case inr h =>
             apply Or.inl
             assumption
        . apply Or.inr
          assumption

/-
The cases tactic can also be used to decompose a conjunction
-/
example (p q : Prop) : p ∧ q → q ∧ p := by
        intro h
        cases h with
        | intro hp hq => constructor; exact hq; exact hp

/-
The constructor tactic applies the unique constructor for
conjunction, And.intro

Using these, an example from the prev section can be rewritten as
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro h
          cases h with
          | intro hp hqr =>
            cases hqr
            . apply Or.inl; constructor <;> assumption
            . apply Or.inr; constructor <;> assumption
        . intro h
          cases h with
          | inl hpq =>
            cases hpq with
            | intro hp hq =>
              constructor; exact hp; apply Or.inl; exact hq
          | inr hpr =>
            cases hpr with
            | intro hp hr =>
              constructor; exact hp; apply Or.inr; exact hr

/-
These tactics are quite general, as seen in Inductive Types
The cases tactic can be used to decompose any element of an
inductively defined type;
constructor always applies the first applicable constructor of an
inductively defined type.
-/
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
        intro h
        cases h with
        | intro x px => constructor; apply Or.inl; exact px

/-
The constructor tactic leaves the first component of the existential
assertion, the value of x, implicit. It is represented by a metavar
that should be instantiated later on.

In the prev example, the proper value of the metavariable is determined
by the tactic exact px, since px has type p x.

If you want a witness to the existential quantifier explicitly, you
can use the exists tactic instead
-/
example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
        intro h
        cases h with
        | intro x px => exists x; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, p x ∧ q x := by
        intro h
        cases h with
        | intro x hpq =>
          cases hpq with
          | intro hp hq =>
            exists x

/-
These tactics can be used on data just as well as propositions.
For example, you could swap the components of the product and sum types
-/
def swap_pair : α × β → β × α := by
    intro p
    cases p
    constructor <;> assumption

def swap_sum : Sum α β → Sum β α := by
    intro p
    cases p
    . apply Sum.inr; assumption
    . apply Sum.inl; assumption

/-
Note that up to the names we have chosen for the variables, the
definitions are identical to the proofs of the analogous propositions
for conjunction and disjunction.

The cases tactic will also do a case distinction on a natural number

Proof by induction spotted !!
-/
section
open Nat
example (P : Nat → Prop)
        (h₀ : P 0) (h₁ : ∀ n, P (succ n))
        (m : Nat) : P m := by
        cases m with
        | zero => exact h₀
        | succ m' => exact h₁ m'

end

/-
The contradiction tactic searches for a contradiction among the
hypotheses of the current goal
-/
example (p q : Prop) : p ∧ ¬p → q := by
        intro h
        cases h
        contradiction

/-
We can also use match in tactic blocks
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro h
          match h with
          | ⟨_, Or.inl _⟩ =>
            apply Or.inl; constructor <;> assumption
          | ⟨_, Or.inr _⟩ =>
            apply Or.inr; constructor <;> assumption
        . intro h
          match h with
          | Or.inl ⟨hp, hq⟩ =>
            constructor; exact hp; apply Or.inl; exact hq
          | Or.inr ⟨hp, hr⟩ =>
            constructor; exact hp; apply Or.inr; exact hr

/-
You can combine intro with match and write the previous examples as
follows:
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro
        | ⟨hp, Or.inl hq⟩ =>
          apply Or.inl ; constructor <;> assumption
        | ⟨hp, Or.inr hr⟩ =>
          apply Or.inr; constructor <;> assumption
        . intro
        | Or.inl ⟨hp, hq⟩ =>
          constructor; assumption; apply Or.inl; assumption
        | Or.inr ⟨hp, hr⟩ =>
          constructor; assumption; apply Or.inr; assumption

/- 5.4 Structuring Tactic Proofs -/
/-
Long sequences of tactics often obsucre the structure of the argument.
How do we structure a tactic-style proof, making it more readable
and robust.

The nice thing about Lean is the ability to mix term-style and tactic-
style proofs, and pass between the two freely.
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro h
          cases h.right with
          | inl hq => exact Or.inl ⟨h.left, hq⟩
          | inr hr => exact Or.inr ⟨h.left, hr⟩
        . intro h
          cases h with
          | inl hpq => exact ⟨hpq.left, Or.inl hpq.right⟩
          | inr hpr => exact ⟨hpr.left, Or.inr hpr.right⟩

/-
There is a show tactic, which is similar to the show expression in a
proof term. It simply declares the type of the goal that is about to be
solved, while remaining in tactic mode
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        . intro h
          cases h.right with
          | inl hq =>
            show  (p ∧ q) ∨ (p ∧ r)
            exact Or.inl ⟨h.left, hq⟩
          | inr hr =>
            show  (p ∧ q) ∨ (p ∧ r)
            exact Or.inr ⟨h.left, hr⟩
        . intro h
          cases h with
          | inl hpq =>
            show p ∧ (q ∨ r)
            exact ⟨hpq.left, Or.inl hpq.right⟩
          | inr hpr =>
            show p ∧ (q ∨ r)
            exact ⟨hpr.left, Or.inr hpr.right⟩

/-
The show tactic can be used to rewrite a goal to something
definitionally equivalent too
-/
example (n : Nat) : n + 1 = Nat.succ n := by
        show Nat.succ n = Nat.succ n
        rfl

/-
There is also a have tactic, which introduces a new subgoal, just as
when writing proof terms
-/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
        intro ⟨hp, hqr⟩
        show (p ∧ q) ∨ (p ∧ r)
        cases hqr with
        | inl hq =>
          have hpq : p ∧ q := And.intro hp hq
          apply Or.inl
          exact hpq
        | inr hr =>
          have hpr : p ∧ r := And.intro hp hr
          apply Or.inr
          exact hpr

/-
As with the proof terms, you can omit the label in the have tactic,
in which case the default label this is used
-/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
        intro ⟨hp, hqr⟩
        show (p ∧ q) ∨ (p ∧ r)
        cases hqr with
        | inl hq =>
          have : p ∧ q := And.intro hp hq
          apply Or.inl
          exact this
        | inr hr =>
          have : p ∧ r := And.intro hp hr
          apply Or.inr
          exact this

/-
The types in the have tactic can also be omitted, so you can write
have hp := h.left and hqr := h.right.
With this notation, you can omit both the type and the label, and the
fact is introduced with the label this
-/
example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
        intro ⟨hp, hqr⟩
        show (p ∧ q) ∨ (p ∧ r)
        cases hqr with
        | inl hq =>
          have := And.intro hp hq
          apply Or.inl
          exact this
        | inr hr =>
          have := And.intro hp hr
          apply Or.inr
          exact this

/-
Lean also has a let tactic, which is similar to the have tactic, but
is used to introduce local definition sinstead of aux facts.
And is the tactic analogue of a let in a proof term
-/
example : ∃ x, x + 2 = 8 := by
        let a := 3 * 2
        exists a

/-
The difference between let and have is that let introduces a local
definition in the context, so that the definition can be unfolded
in the proof

We have used . to create nested tactic blocks. In a nested block,
Lean focuses on the first goal, and generates an error if it has not
been fully solved at the end of the block. The notation . is whitespace
sensitive and relies on the indentation to detect whether the tactic
block ends.

Alternatively, you can define tactic blocks using curly braces and
semicolons
-/
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
        apply Iff.intro
        { intro h;
          cases h.right;
          { show (p ∧ q) ∨ (p ∧ r);
            exact Or.inl ⟨h.left, ‹q›⟩ }
          { show (p ∧ q) ∨ (p ∧ r);
            exact Or.inr ⟨h.left, ‹r›⟩ } }
        { intro h;
          cases h;
          { show p ∧ (q ∨ r);
            rename_i hpq;
            exact ⟨hpq.left, Or.inl hpq.right⟩ }
          { show p ∧ (q ∨ r);
            rename_i hpr;
            exact ⟨hpr.left, Or.inr hpr.right⟩ } }

/-
every time a tactic leaves more than one subgoal, we seperate the
remaining subgoals by enclosing them in blocks and identing.

Thus if the application of a theorem foo to a single goal produces
four subgoals, one would expect the proof to look like this:

  apply foo
  . <proof of first goal>
  . <proof of second goal>
  . <proof of third goal>
  . <proof of final goal>

or

  apply foo
  case <tag of first goal>  => <proof of first goal>
  case <tag of second goal> => <proof of second goal>
  case <tag of third goal>  => <proof of third goal>
  case <tag of final goal>  => <proof of final goal>

or

  apply foo
  { <proof of first goal>  }
  { <proof of second goal> }
  { <proof of third goal>  }
  { <proof of final goal>  }
-/

/- 5.5 Tactic Combinators -/
/-
Tactic combinators are operations that form new tactics from old ones.
A sequencing combinator is already implicit in the by block:
-/
example (p q : Prop) (hp : p) : p ∨ q := by
        apply Or.inl; assumption

/-
Here apply Or.inl; assumption is functionally equivalent to a single
tactic which first applies apply Or.inl and then applies assumption

In t₁ <;> t₂, the <;> operator provides a parallel version of the
sequencing operation: t₁ is applied to the current goal, and then t₂
is applied to all the resulting subgoals
-/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
        by constructor <;> assumption

/-
This is especially useful when the resulting goals can be finished
off in a uniform way, or make progress on all of them uniformly

first | t₁ | t₂ | ... | tₙ applies each tᵢ until one succeeds, or else
fails

In the following two examples, in the first one, the left branch succeeds,
in the second one, the right branch succeeds
-/
example (p q : Prop) (hp : p) : p ∨ q := by
        first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
        first | apply Or.inl; assumption | apply Or.inr; assumption

/-
In the next three examples, the same compound tactic
succeeds in each case
-/
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
        repeat (first | apply Or.inl; assumption
                      | apply Or.inr
                      | assumption)

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
        repeat (first | apply Or.inl; assumption
                      | apply Or.inr
                      | assumption)

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
        repeat (first | apply Or.inl; assumption
                      | apply Or.inr
                      | assumption)

/-
You have noticed by now that tactics can fail. Indeed it is the
"fail" state that causes the combinators to backtrack and try the
next tactic

The try combinator builds a tactic that always succeeds, though
it could be in a trivial way:

try t executes t and reports success, and is equivalent to
first | t | skip, where skip is a tactic that does nothing (and succeeds
in doing so)

As such repeat (try t) will loop forever

In the next example, the second constructor succeeds on the right
conjunct q ∧ r (disjunct and conjunct assoc right) but fails on the first.
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
        constructor <;> (try constructor) <;> assumption

/-
In a proof, there are often multiple goals outstanding. Parallel
sequencing is one way to arrange it so that a single tactic is applied
to multiple goals, but there are other ways to do this.

For example, all_goals t applies t to all open goals
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
        constructor
        all_goals (try constructor)
        all_goals assumption

/-
In this case, the any_goals tactic provides a more robust solution.
Similar to all_goals, except it succeeds if its argument succeeds on at
least one goal
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
        constructor
        any_goals constructor
        any_goals assumption

/-
We can repeatedly split conjunctions
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
        p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
          repeat (any_goals constructor)
          all_goals assumption

/- We can even compress the full tactic down to one line -/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
        p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
          repeat (any_goals (first | constructor | assumption))

/-
The combinator focus t ensures that t only effects the current goal,
temp hiding the others from the scope. So if t ordinarily only effects
the current goal, focus (all_goals t) has the same effect as t
-/

/- 5.6 Rewriting -/
/-
The rw tactic provides a basic mechanism for applying the substitutions
to goals and hypotheses, providing a convenient and efficient way of
working with equality. The most basic form of the tactic is rw [t], where
t is a term whose type asserts an equality. For example, t can be a
hypothesis h : x = y in the context; it can be a general lemma,
like add_comm : ∀ x y, x + y = y + x, in which the rewrite tactic tries
to find suitable instantiations of x and y; or it can be any compound
term asserting a concrete or general equation.
-/
variable (k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
        rw [h₂] /- replace k with 0 -/
        rw [h₁] /- replace f 0 with 0 -/

/- The tactic automatically closes any goal of the form t = t -/
example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
        rw [h hq]; assumption

/-
You can also have multiple rewrites can be combined using the notation
rw [t₁, t₂, ..., tₙ], which is just shorthand for rw[t₁]; ...; rw[tₙ]. 
-/
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
        rw [h₂, h₁]

/-
By default, rw uses an equation in the forward direction, matching
the left-hand side with an expression, and replacing it with the
right-hand side. By notating ←t can be used to instruct the tactic to
use the equality t in the reverse direction

The term ←h₁ instructs the rewriter to replace b with a.
-/
variable (a b : Nat) (f : Nat → Nat)

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
        rw [←h₁, h₂]

/-
Sometimes the left-hand side of an identity can match more than one
subterm in the pattern, in which case the rw tactic chooses the first
match it finds when traversing the term. If that is not the one you want,
you can use additional args to specify the appropriate subterm
-/
example (a b c : Nat) : a + b + c = a + c + b:= by
        rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

example (a b c : Nat) : a + b + c = a + c + b:= by
        rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

example (a b c : Nat) : a + b + c = a + c + b:= by
        rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

/-
The last example specifies that the rewrite should take place on the
right hand side by specifying the second argument to Nat.add_comm

The rw tactic is not restricted to propositions. In this example,
we use rw [h] at t to rewrite hypothesis t : Tuple α n to t : Tuple
α 0
-/
def Tuple (α : Type) (n : Nat) :=
    { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
        rw [h] at t
        exact t
