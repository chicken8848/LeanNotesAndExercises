import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Group.Equiv.Basic

open Real

/-! 
  Define `PosReal` as the subtype of positive real numbers: { x : ℝ // 0 < x }
-/
def PosReal : Type := { x : ℝ // 0 < x }

namespace PosReal

-- 1. Define Multiplication on PosReal
instance : Mul PosReal where
  mul x y := ⟨x.1 * y.1, mul_pos x.2 y.2⟩

-- 2. Define Inverse on PosReal
instance : Inv PosReal where
  inv x := ⟨x.1⁻¹, inv_pos.mpr x.2⟩

-- 3. Define Identity (1) on PosReal
instance : One PosReal where
  one := ⟨1, Real.zero_lt_one⟩

-- 4. Construct the Group instance for PosReal
instance : Group PosReal where
  mul_assoc x y z := Subtype.ext (mul_assoc x.1 y.1 z.1)
  one_mul x       := Subtype.ext (one_mul x.1)
  mul_one x       := Subtype.ext (mul_one x.1)
  inv_or_div      := Or.inl (fun _ _ => rfl)
  mul_left_inv x  := Subtype.ext (inv_mul_cancel₀ (ne_of_gt x.2))

end PosReal


/-! 
  SUBLEMMA: Proving that exp(x + y) = exp(x) * exp(y) on PosReal.
  This proves that the operation mapping ℝ (additive) to PosReal (multiplicative) 
  preserves the group operations.
-/
theorem exp_preserves_op (x y : ℝ) : 
    (⟨exp (x + y), exp_pos (x + y)⟩ : PosReal) = 
    (⟨exp x, exp_pos x⟩ : PosReal) * (⟨exp y, exp_pos y⟩ : PosReal) := by
  ext
  -- Unfold subtype equality and apply real exponential property
  exact Real.exp_add x y


/-! 
  MAIN THEOREM: Construct the formal group isomorphism ℝ ≃*+ PosReal
-/
def realEquivPosReal : ℝ ≃*+ PosReal where
  -- Forward map: x ↦ exp(x)
  toFun x := ⟨exp x, exp_pos x⟩
  
  -- Inverse map: x ↦ log(x)
  invFun y := log y.1
  
  -- Left Inverse Proof: log(exp(x)) = x
  left_inv x := log_exp x
  
  -- Right Inverse Proof: exp(log(y)) = y
  right_inv y := Subtype.ext (exp_log y.2)
  
  -- Sublemma application: Group homomorphism preservation
  map_add' x y := exp_preserves_op x y
