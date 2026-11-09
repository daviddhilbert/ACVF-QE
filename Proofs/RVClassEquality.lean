import ResidueTransportCore

namespace RVCalc
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}
theorem rv_eq_iff {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    rv v x = rv v y ↔ v (x - y) < v x := by
  have hxpos : 0 < v x := zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 hx)
  rw [rv_of_ne hx, rv_of_ne hy, Option.some.injEq,
    QuotientGroup.mk'_eq_mk' (N := principalUnits v)]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hz' : v ((z : K) - 1) < 1 := hz
    have h1 : x * (z : K) = y := by
      simpa using congrArg Units.val hzy
    have hzx : (z : K) = y / x := by
      rw [eq_div_iff hx, mul_comm]
      exact h1
    have h2 : v (y / x - 1) < 1 := by rw [← hzx]; exact hz'
    calc v (x - y) = v (x * (1 - y / x)) := by
            rw [mul_sub, mul_one, mul_div_cancel₀ y hx]
      _ = v x * v (1 - y / x) := map_mul ..
      _ = v x * v (y / x - 1) := by
            rw [show 1 - y / x = -((y / x) - 1) by ring, Valuation.map_neg v]
      _ < v x * 1 := mul_lt_mul_of_pos_left h2 hxpos
      _ = v x := mul_one _
  · intro h
    refine ⟨(Units.mk0 x hx)⁻¹ * Units.mk0 y hy, ?_, ?_⟩
    · rw [mem_principalUnits]
      have hzK : (((Units.mk0 x hx)⁻¹ * Units.mk0 y hy : Kˣ) : K) = y / x := by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
        ring
      rw [hzK, show y / x - 1 = (y - x) / x by field_simp,
        Valuation.map_div v, show y - x = -(x - y) by ring, Valuation.map_neg v,
        div_lt_one₀ hxpos]
      exact h
    · simp

/-- The nonzero leading-term map has kernel `1 + 𝔪`. -/
theorem rvUnit_kernel (v : Valuation K Γ₀) :
    (QuotientGroup.mk' (principalUnits v) : Kˣ →* RVUnit v).ker = principalUnits v :=
  QuotientGroup.ker_mk' (principalUnits v)

/-- A nonzero field element has leading term `rv 1` exactly when its
difference from one lies in the maximal ideal. -/
theorem rv_eq_rv_one_iff {x : K} (hx : x ≠ 0) :
    rv v x = rv v 1 ↔ v (x - 1) < 1 := by
  rw [eq_comm, rv_eq_iff one_ne_zero hx, ← neg_sub x 1, Valuation.map_neg, map_one]

end RVCalc

#check @RVCalc.rvUnit_kernel
#print axioms RVCalc.rvUnit_kernel
#check @RVCalc.rv_eq_rv_one_iff
#print axioms RVCalc.rv_eq_rv_one_iff
