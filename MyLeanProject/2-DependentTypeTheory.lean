/- 2.1 Simple Type Theory -/

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

#check m
#check n
#check b1
#check b2
#check b1 && b2
#check b1 || b2
#check true
#eval 5 * 4
#eval b1 && b2

/- make a comment -/

/- 2.2 Types as Objects -/

#check Nat -> Nat
#check Nat × Nat

def α : Type := Nat
def β : Type := Bool
def F : Type -> Type := List
def G : Type -> Type -> Type := Prod

#check Prod α β
#check α × β

#check F α /- returns a type of List[α] -/

/- Lean's foundation has a infinite hierarchy of Types -/
#check Type 0 /- "small and "ordinary" types -/
#check Type 1 /- Even larger universe of types with Type 0 as elements -/
#check Type 2 /- Even larger univers of types with Type 1 as elements -/

/-
Movement along the x-axis refer to a change in universes 
Movement along the y-axis refer to a change in degree 

sort | Prop (sort 0) | Type (sort 1) | Type 1 (sort 2) | Type 2 (sort 3) 
type | true          | Bool          | Nat -> Type     | Type -> Type 1
term | True.intro    | true          | fun n -> Fin n  | fun (_: Type) => Type
-/

/-
Some operations need to be polymorphic over Type universes
Here u is a variable ranging over type levels

List.{u} (α : Type u) : Type u

Means that whenever α has Type u, List α also has Type u, where u is a Type level
-/
#check List

/- Prod does something similar -/
#check Prod


/- You can declare universes using the universe command -/
universe u
def H (α : Type u) : Type u := α × α
#check H

/- Or avoid the universe command entirely -/
def I.{v} (α : Type v) : Type v := α × α

/-
2.3 Function Abstraction and Evaluation

use fun or λ to create a function from an expression
fun and λ mean the same thing
-/

#check fun(x: Nat) => x + 5
#check λ(x: Nat) => x + 6

/- eval a lambda function by passing it the parameters -/
#eval (λ x: Nat => x + 5) 10

/- lambda abstraction -/
/-
Suppose you have a variable x: α and an expression t: β
then λ x => t is of type α → β
-/
#check λ (x: Nat) => λ y: Bool => if not y then x + 1 else x + 2
#check λ (x: Nat) (y: Bool) => if not y then x + 1 else x + 2
#check λ x y => if not y then x + 1 else x + 2 /- type inferred -/

/- common operations in terms of lambda expressions -/

def f(x: Nat) : String := toString x
def g(s: String) : Bool := s.length > 0

#check λ x: Nat => x
#check λ x: Nat => true
#check λ x: Nat => g (f x)

/- you can also pass functions as parameters -/
#check λ (g: String -> Bool) (f: Nat -> String) (x: Nat) => g (f x)

/- or pass types as parameters -/
#check λ (α β γ : Type) (g: β -> γ) (f: α -> β) (x: α) => g (f x)

/-
functions that are the same up to the renaming of
variables are called alpha equivalent
Remember compilers class
-/


/- 2.4 Definitions -/
def double(x: Nat): Nat :=
    x + x

#eval double 3

/- def can be thought of as a named fun or λ -/
def double2: Nat -> Nat :=
    λ x: Nat => x + x

#eval double2 4

/- create functions that take other functions -/
def doTwice (f: Nat -> Nat) (x: Nat) :=
    f (f x)

#eval doTwice double 2

/- create a composition function -/
def compose (α β γ: Type) (g: β -> γ) (f: α -> β) (x: α) :=
    g (f x)

def square (x: Nat): Nat :=
    x * x

#eval compose Nat Nat Nat double square 3

/- 2.5 local definions -/
/- let a := t1; t2 ⇔ replace every occurance of a in t2 by t1 -/
#check let y := 2 + 2; let z := y * y; z + z
#eval let y := 2 + 2; y * y   


/- 2.6 variables and sections -/
def compose2 (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

/- Lean provides variables to make the definitions more compact -/
variable (α β γ : Type)
def compose3 (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

/- You may declare variables of any Type -/
variable (g: β -> γ) (f: α -> β) (h: α -> α)
variable (x: α)

def compose4 := g (f x)
def doTwice2 := h (h x)
def doThrice := h (h (h x))

#print compose4
#print doTwice2
#print doThrice

/-
When declared this way, the variable stays in scope
until the end of the file, however
it may be useful to limit the scope of the variable

Sections limit variables but not definitions
-/

section useful
    variable (α β γ : Type)
    variable (g: β -> γ) (f: α -> β) (h: α -> α)
    variable (x: α)

    def compose5 := g (f x)
    def doTwice3 := h (h x)
    def doThrice2 := h (h (h x))
end useful


/- 2.7 Namespaces -/

namespace Foo
    def a : Nat := 5
    def ff(x: Nat) : Nat := x + 7
    def fa := ff a
    def ffa := ff (ff a)

    #check a
    #check ff
    #check fa
    #check ffa
    #check Foo.fa

end Foo

/- Here #check ff would return an error -/
#check Foo.ff
#check Foo.a
#check Foo.ff
#check Foo.fa
#check Foo.ffa

/- open to bring shorter names into current context -/
open Foo
#check a
#check ff
#check fa
#check ffa

#check List.nil
#check List.cons
#check List.map

/- Namespaces can also be nested -/

/- 2.8 Dependent Type Theory -/
/- The Type of an object can depend on its parameters -/
def cons (α : Type) (x: α) (xs: List α): List α :=
    List.cons x xs

#check cons Nat
#check cons Bool
#check cons

/-
This is an instance of a dependent function type or dependent arrow type
When the value of β depends on the type of α
The expression (a : α) -> β denotes a dependent function type
When β doesn't depend on α, (a : α) -> β is the same as α -> β
-/
/- @ notation and {} will explained later -/
#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

/-
Dependent function types generalize the notion of α -> β
Similarly, dependent cartesian product types (a : α) × β generalize the
notion of cartesian products α × β
Dependent products are also called sigma types, and may also be written as
Σ a: α, β or ⟨a, b⟩ or Sigma.mk a b to create a dependent pair
-/

universe u1 v1

/- β a is written to denote that the type of b is given by β(a) -/ 
def f1 (α : Type u1) (β: α -> Type v1) (a : α) (b : β a) : (a : α) × β a :=
    ⟨a, b⟩

def g1 (α : Type u1) (β: α -> Type v1) (a : α) (b : β a) : Σa: α, β a :=
    Sigma.mk a b

def h1(x: Nat): Nat :=
    (f1 Type (fun α => α) Nat x).2

#eval h1 5

/- 2.9 Implicit arguments -/
/-
when a function takes an argument that can generally be inferred from
context, Lean allows you to specify that these arguments should by
default, be left implicit. This is done by putting these arguments in
curly braces
-/

universe u2
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α): Lst α := List.cons a as
def Lst.nil {α : Type u}: Lst α := List.nil
def Lst.append {α : Type u} (as bs: Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs

/-
We can make the first argument to ident implicit
This makes it look as though ident simply takes an
argument of any type.
-/
universe u3
def ident {α : Type u} (x : α) := x 

#check (ident)
#check ident 1
#check ident "hello"
#check @ident

/-
Variables can also be specified as implicit when they are
declared with the variable command
-/
universe u4

section
    variable {α : Type u4}
    variable (x : α)
    def ident2 := x
end

#check ident2
#check ident2 4
#check ident2 "hello"

/-
Lean has very complex mechanisms for instantiating implicit arguments,
they can be used to infer function types, predicates, and even proofs.
-/

/-
One can specify the type T of an expression e by writing (e: T)
This instructs Lean to use the value T as the type of e when resolving
implicit arguments
-/
#check (List.nil)
#check (id)
#check (List.nil : List Nat)
#check (id: Nat -> Nat)

/-
Numerals are overloaded in Lean, if it cannot be inferred, Lean assumes
that it is a Nat
-/
#check 2
#check (2: Nat)
#check (2: Int)

/-
When we have declared an argument to a function to be implicit,
but now want to provide the argument explicitly. We can use @f
to denote f with all the arguments made explicit
-/
#check @id
#check @id Nat
#check @id Bool
#check @id Nat 1
#check @id Int 1
#check @id Bool true
