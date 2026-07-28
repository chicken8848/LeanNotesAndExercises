/- 4 Quantifiers and Equality -/
/- 4.1 The Universal Quantifier -/
/-
The calculus of constructions identifies dependent arrow
types with forall expressions as such:

If p is any expression, ∀ x: α, p is just alt notation
for (x : α) -> p

Typically the expression p will depend on x : α

In ordinary function spaces, we could interpret α -> β as the
special case of (x : α) -> β in which β does not depend on x.
-/
example (α: Type) (p q : α -> Prop) :
        (∀ x : α, p x ∧ q x) -> ∀ y : α, p y :=
           λ h : ∀ x : α, p x ∧ q x =>
           λ y : α =>
           show p y from (h y).left

/-
As a notational convention, we give the universal quantifier the widest
scope possible, so paretheses are needed to limit the quantifier over x to the
hypothesis in the example above

The canonical way to prove ∀ y : α, p y is to take an arbitrary y, and prove
p y. This is the introduction rule. Now given that h has type
∀ x : α, p x ∧ q x, the expression h y has type p y ∧ q y. This is the
elimination rule. Taking the left conjunct gives the desired conclusion
-/

/-
As another example, here is how we can expressthe fact that a relation, r,
is transitive
-/
variable (α: Type) (r : α -> α -> Prop)
variable (trans_r: ∀ x y z, r x y -> r y z -> r x z)

variable (a b c : α)
variable (hab: r a b) (hbc: r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

/-
In these situations, the arguments a b c can be inferred from hab hbc, and can be thus implicit
-/
variable (trans_r: ∀ { x y z }, r x y → r y z → r x z)
#check trans_r
#check trans_r hab
#check trans_r hbc

/-
A disadvantage of implicit types is that Lean does not have enough information to infer the types of the
arguments in the expressions trans_r and trans_r hab
-/

variable (α : Type) (r : α -> α -> Prop)
variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ { x y }, r x y -> r y x)
variable (trans_r: ∀ { x y z }, r x y -> r y z -> r x z)

/-
It is the typing rule for dependent arrow types, and the universal quantifier in particular, that
distinguishes Prop from other types. Suppose we have α : Sort i and β : Sort j, where β may depend on
variable x : α. Then (x : α) -> β is an element of Sort (imax i j), where imax(i, j) is the maximum of
i and j if j is not 0, and 0 otherwise

If j is not 0, then (x : α) -> β is an element of Sort (max i j). In other words, the type of dependent
functions from α to β "lives" in the universe whoe index is the maximum of i and j. Suppose, however
that β is of Sort 0, that is, an element of Prop. In that case, (x : α) -> β is an element of Sort 0 as well,
no matter which type univers α lives in.

If β is a proposition depending on α, then ∀ x : α, β is again a proposition. This reflects the
interpretation of Prop as the type of propositions rather than data.

This is what makes Prop impredicative
-/

/- 4.2 Equality -/
#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

/- .{u} tells Lean to instantiate the constants at the universe u -/
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example: a = d :=
         Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

/- there is also the projection natiotan -/
example : a = d := (hab.trans hcb.symm).trans hcd

/-
In terms of Calculus of Constructions, terms with a common reduct
are the same. As a result, some nontrivial identities can be proven
by reflexivity
-/
variable (α β: Type)
example (f: α -> β) (a : α) : (λ x => f x) a = f a := Eq.refl _
example (a: α) (b: β) : (a, b).1 = a := Eq.refl _ 
example : 2 + 3 = 5 := Eq.refl _

/- this is so impt that there is an abbrev -/
example (f: α -> β) (a : α) : (λ x => f x) a = f a := rfl
example (a: α) (b: β) : (a, b).1 = a := rfl 
example : 2 + 3 = 5 := rfl

/-
Equality has the property that every assertion respects the equivalence.
We can substitute equal expressions without changing the truth value.

Given h1 : a = b and h2: p a we can construct a proof for p b using Eq.subst h1 h2
-/
#check Eq.subst
example (α : Type) (a b : α) (p : α -> Prop)
        (h1: a = b) (h2 : p a) : p b := Eq.subst h1 h2

example (α : Type) (a b : α) (p : α -> Prop)
        (h1: a = b) (h2 : p a) : p b := h1 ▸ h2

/-
The rule Eq.subst is used to define the following auxiliary rules, which carry out more
explicit substitutions. And are designed to deal with applicative terms (of the form s t),
congrArg can be used to replace the argument, congrFun can be used to replace the term
that is being applied, and congr can be used to replace both at once
-/
variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

/- Lean lib has a large number of common identities, such as -/
variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : 0 + a = a := Nat.zero_add a
example : a * 1 = a := Nat.mul_one a
example : 1 * a = a := Nat.one_mul a
example : a + b = b + a := Nat.add_comm a b
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
example : a * b = b * a := Nat.mul_comm a b
example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c

/- an example of a calc in the natural numbers that use substitution
with assoc and distrib -/

example (x y : Nat) :
        (x + y) * (x + y) =
        x * x + y * x + x * y + y * y :=
        have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
             Nat.mul_add (x + y) x y
        have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
             (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
        h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm

/- 4.3 Calculational Proofs -/
/-
A calculational proof is just a chain of intermediate results that are meant to be composed by
basic principles such as the transitivity of equality.

Note that the calc relations all have the same indentation. Each <proof>_i is a proof for <expr>_{i-1} op_i <expr>_i

We can also use _ in the first relation, which is useful to align the sequence of relation/proof pairs
-/
variable (a b c d e : Nat)
theorem T
        (h1: a = b)
        (h2: b = c + 1)
        (h3: c = d)
        (h4: e = 1 + d):
        a = e :=
    calc
        a = b     := h1
        _ = c + 1 := h2
        _ = d + 1 := congrArg Nat.succ h3
        _ = 1 + d := Nat.add_comm d 1
        _ = e     := Eq.symm h4


/- This style is most effective when it is used in conjunction with the simp and rw tactics -/
variable (a b c d e : Nat)
variable (a b c d e : Nat)
theorem T1
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

/-
The rw tactic uses a given equality to "rewrite" the goal. If doing so reduces the goal to an identity t = t, the tactic
applies reflexivity to prove it

Rewrites can be applied sequentially, so that the proof can be shortened to this
-/
theorem T11
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1 := by rw [h1, h2, h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e := by rw [h4]
 
    
theorem T12
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
      by rw [h1, h2, h3, Nat.add_comm, h4]

/-
The simp tactic, instead, rewrites the goal by applying the given identities repeatedly, in any order,
wherever they are applicable in a term. It also uses other rules that have been previously declared
to the system, and applies commutativity wisely to avoid looping
-/
theorem T13
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
      by simp [h1, h2, h3, Nat.add_comm, h4]

/-
The calc command can be configured for any realtion that supports some form of transitivity, and can even
combine relations
-/
variable (a b c d : Nat)
example (h1 : a = b) (h2 : b <= c) (h3 : c + 1 < d) : a < d :=
        calc
            a = b      := h1
            _ < b + 1  := Nat.lt_succ_self b
            _ <= c + 1 := Nat.succ_le_succ h2
            _ < d      := h3

/-
You can also extend the calc notation using new Trans instances
-/
def divides (x y : Nat) : Prop :=
    ∃ k, k*x = y

def divides_trans (h₁: divides x y) (h₂ : divides y z) : divides x z :=
    let ⟨k₁, d₁⟩ := h₁
    let ⟨k₂, d₂⟩ := h₂
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x: Nat) (k: Nat) : divides x (k*x) := ⟨k, rfl⟩
    
instance: Trans divides divides divides where
          trans := divides_trans

example (h₁: divides x y) (h₂ : y = z) : divides x (2*z) :=
        calc
            divides x y     := h₁
            _ = z           := h₂
            divides _ (2*z) := divides_mul ..

/-
Lean already includes the standard for divisibility \mid "∣"

Not to be confused with the haskell guard "|", (match ... with expr)

We can also use <- to ask lean to rewrite the identity in the opposite direction as such:
by rw [<-Nat.add_assoc]
In such cases, you would start calc with the goal and go backwards

Another example using rw and simp
-/
variable (x y: Nat)
example: (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
         by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, <-Nat.add_assoc]

example: (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
         by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

/- 4.4 The Existential Quantifier -/
/-
Now we get to the existential quantifier, which can be written either
exists x : α, p x or ∃ x: α, p x. Which are both convenient when compared to
Exists (fun x : α => p x)

As expected, the library includes both an introduction rule and an elimination rule

The intro rule is straightforward, to prove ∃ x: α, p x, it suffices to provide a suitable
term t and a proof of p t
-/
example : ∃ x: Nat, x > 0 :=
        have h : 1 > 0 := Nat.zero_lt_succ 0
        Exists.intro 1 h

example (x: Nat) (h: x > 0) : ∃ y, y < x :=
        Exists.intro 0 h

example (x y z: Nat) (hxy: x < y) (hyz: y < z) : ∃w, x < w ∧ w < z :=
        Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

/- We can use the anonymous constructor notation ⟨t, h⟩ for Exists.intro t h -/
example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
    ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    ⟨y, hxy, hyz⟩

/-
We can view Exists.intro as an information hiding operation, since it hides
the witness to the body of the assertion.
Exists.elim, performs the opposite operation. It allows us to prove a prop
q from ∃ x : α, p x, by showing that q follows from p w for an arbitrary value w.

If q does not mention w, then showing that q follows from p w is tantamount to
showing that q follows from the existence of any such x
-/
variable (α : Type) (p q : α → Prop)

example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        Exists.elim h
                    (λ w => 
                    λ hw: p w ∧ q w =>
                    show ∃ x, q x ∧ p x from ⟨w, ⟨hw.right, hw.left⟩⟩)

/-
Notice that an existential propostition is very similar to a sigma type,
as described in the dependent type section.
The difference is that existential propositions are propositions, why sigma
type are types.

Given a predicate p : α -> Prop and a family of types β : α -> Type, for a term
a : α with h: p a and h' : β a, the term Exists.intro a h has the type
(∃ x: α, p x) : Prop, while Sigma.mk a h' has type (Σ x: α, β x). This is another instance
of the Curry-Howard isomorphism

Lean provides a more convenient way to eliminate from an existential quantifier with the
match expression
-/
variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        match h with
        | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
/-
The match statement "destructs" the existential assertion into the components
w and hw, which can then be used in the body of the statement to prove the proposition.
-/

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        match h with
        | ⟨(w: α), (hw: p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

/- You can even use the match statement to decompose the conjunction at the same time -/
example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        match h with
        | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

/- You can also use pattern matching -/
example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
        let ⟨w, hpw, hqw⟩ := h
        ⟨w, hqw, hpw⟩

/- We can also have an implicit match in the λ expr -/
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
        λ ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

/-
These variations are instances of a more general pattern-matching
construct
-/
def IsEven (a : Nat) := ∃ b, a = 2*b

theorem even_plus_even (h1: IsEven a) (h2: IsEven b) : IsEven (a + b) :=
        Exists.elim h1 (λ w1 (hw1 : a = 2 * w1) =>
        Exists.elim h2 (λ w2 (hw2 : b = 2 * w2) =>
                    Exists.intro (w1+w2)
                                 (calc a + b
                                       _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
                                       _ = 2 * (w1 + w2) := by rw [Nat.mul_add])))

theorem even_plus_even2 (h1: IsEven a) (h2: IsEven b) : IsEven (a + b) :=
        match h1, h2 with
        | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
          ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩


section
open Classical
variable (p: α → Prop)

example (h: ¬ ∀ x, ¬ p x) : ∃ x, p x :=
        byContradiction
            (λ h1: ¬ ∃x, p x =>
               have h2: ∀x, ¬ p x :=
                    λ x =>
                    λ h3 : p x =>
                    have h4 : ∃ x, p x := ⟨x, h3⟩
                    show False from h1 h4
                  show False from h h2)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
        (λ h: ∃x : α, r =>
           match h with
           | ⟨x, r⟩ => r)

example (a : α) : r → (∃ x : α, r) :=
        λ hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
        Iff.intro
            (λ ⟨a, ⟨hpa, hr⟩⟩ => ⟨⟨a, hpa⟩, hr⟩)
            (λ ⟨⟨a, hpa⟩, hr⟩ => ⟨a, ⟨hpa, hr⟩⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
        Iff.intro
            (λ ⟨a, (h1: p a ∨ q a)⟩ =>
               Or.elim h1
                       (λ hpa: p a => Or.inl ⟨a, hpa⟩)
                       (λ hqa: q a => Or.inr ⟨a, hqa⟩))
            (λ h: (∃ x, p x) ∨ (∃ x, q x) =>
               Or.elim h
                       (λ ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
                       (λ ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
        Iff.intro
            (λ h1 => λ ⟨x, h2⟩ => h2 (h1 x))
            (λ h1 => λ x =>
               byContradiction
                (λ h2 : ¬ p x => h1 ⟨x, h2⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
        Iff.intro
            (λ ⟨a, h1⟩ => λ h2 => (h2 a) h1)
            (λ h1 => byContradiction
               (λ h2 : ¬(∃ x, p x) =>
                  h1 (λ a => (λ h3 => h2 ⟨a, h3⟩))))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
        Iff.intro
            (λ h1 => λ a => λ h2 => h1 ⟨a, h2⟩)
            (λ h1 => λ ⟨a, h2⟩ => (h1 a) h2)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
        Iff.intro
            (λ h1 => byContradiction
               (λ h2 =>
                  h1 (λ x =>
                     byContradiction
                        (λ h3: ¬ p x =>
                           h2 ⟨x, h3⟩))))
            (λ ⟨a, h1⟩ => λ h2 => h1 (h2 a))

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
        Iff.intro
            (λ h1 => λ ⟨a, h2⟩ => (h1 a) h2)
            (λ h1 => λ a => λ h2 => h1 ⟨a, h2⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
        Iff.intro
            (λ ⟨x, pxr⟩ => λ h1 => (pxr (h1 x)))
            (λ h1 => byContradiction
               (λ h2 =>
                  have h_forall : ∀ x, p x := λ x =>
                       byContradiction
                        (λ hpx : ¬ p x =>
                           h2 ⟨x, λ hp => False.elim (hpx hp)⟩)
                  have hr : r := h1 h_forall
                  h2 ⟨a, λ _ => hr⟩))

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
        Iff.intro
            (λ h1: ∃ x, r -> p x => λ r =>
               match h1 with
               | ⟨x, rpx⟩ => ⟨x, (rpx r)⟩)
            (λ h1: r → ∃ x, p x => byContradiction
               (λ h2: ¬∃ x, r → p x =>
                  have hr: r := byContradiction
                       (λ hnr: ¬r => h2 ⟨a, λ hr': r => False.elim (hnr hr')⟩)
                  match h1 hr with
                  | ⟨x, hpx⟩ => h2 ⟨x, λ _ => hpx⟩))
end 

/- 4.5 More on the Proof Language -/

