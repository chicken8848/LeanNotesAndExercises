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
