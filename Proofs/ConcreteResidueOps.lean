/- Ported from special-transformations `Section6/ConcreteResidueOps.lean` at 423c767a84b709487da7e798f70f0639545db1ac (same author, MIT); namespace moved to `ACVFQE.Models`. -/
import ConcreteValued

/-! Addition and negation of ordinary residue classes of valuation-one elements. -/

noncomputable section
open ACVFQE.Models.ConcreteRV

namespace ACVFQE.Models.ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)

theorem reduction_at_value_one (x : K) (hx : v x = 1) :
    residueCode v (IsLocalRing.residue v.valuationSubring ⟨x, hx.le⟩) = RVCalc.rv v x := by
  rw [residueCode_reduction, if_pos hx]

theorem addResidue_rv (x y : K) (hx : v x = 1) (hy : v y = 1) :
    addResidue v (RVCalc.rv v x) (RVCalc.rv v y) =
      if v (x + y) = 1 then RVCalc.rv v (x + y) else none := by
  rw [← reduction_at_value_one v x hx, ← reduction_at_value_one v y hy, addResidue_code, ← map_add]
  exact residueCode_reduction v (⟨x, hx.le⟩ + ⟨y, hy.le⟩)

theorem negResidue_rv (x : K) (hx : v x = 1) :
    negResidue v (RVCalc.rv v x) = RVCalc.rv v (-x) := by
  have hneg : v ((-⟨x, hx.le⟩ : v.valuationSubring) : K) = 1 := by
    change v (-x) = 1
    simpa only [Valuation.map_neg] using hx
  rw [← reduction_at_value_one v x hx, negResidue_code, ← map_neg,
    residueCode_reduction, if_pos hneg]
  rfl

end ACVFQE.Models.ConcreteValued
