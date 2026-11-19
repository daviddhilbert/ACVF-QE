import ConcreteACVF
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Models of ACVF in every characteristic

`Axioms.ACVF` has models of each characteristic pair: `(0,0)`, `(0,p)` and
`(p,p)` for every prime `p`. Each model is the concrete two-sorted structure
`Carrier v` of an algebraically closed field `K` with a nontrivial valuation
`v`. The valuation comes from a valuation subring dominating a local subring
(Chevalley's extension theorem, `IsLocalRing.exists_factor_valuationRing`):

* `(0,0)`: `K` is an algebraic closure of `ℚ((t))`, dominating `ℚ[[t]]`;
* `(0,p)`: `K` is an algebraic closure of `ℚ_p`, dominating `ℤ_p`;
* `(p,p)`: `K` is an algebraic closure of `𝔽_p((t))`, dominating `𝔽_p[[t]]`.

In particular the quantifier-elimination theorem for `Axioms.ACVF` is not
vacuous, in any characteristic. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer

namespace ACVFQE.Models

/-! ## Characteristic sentences and the completions of `ACVF` -/

/-- The valued field has characteristic `p`: `p = 0` in VF. -/
def vfCharP (p : ℕ) : LRV.Sentence := pEq (tVFNumeral p) tVFZero

/-- The residue field has characteristic `p`: `p` lies in the maximal ideal.
This is the negation of `Axioms.residueCharZero p`. -/
def residueCharP (p : ℕ) : LRV.Sentence := pGtOne (tRv (tVFNumeral p))

/-- Mixed characteristic `(0,p)`. -/
def ACVF0p (p : ℕ) : LRV.Theory :=
  Axioms.ACVF ∪ {s | ∃ k, s = Axioms.charZeroVF k} ∪ {residueCharP p}

/-- Equal characteristic `(p,p)`. -/
def ACVFpp (p : ℕ) : LRV.Theory := Axioms.ACVF ∪ {vfCharP p}

/-! ## Realization in the concrete structure -/

namespace ConcreteValued

variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ]
variable (v : Valuation K Γ)
local instance existenceStructure : LRV.Structure (Carrier v) := nativeStructure v

theorem vfCharP_realize (p : ℕ) [CharP K p] : Carrier v ⊨ vfCharP p := by
  change (pEq (tVFNumeral p : Tm 0) tVFZero).Realize
    (@default (Empty → Carrier v) Unique.instInhabited)
    (@default (Fin 0 → Carrier v) Unique.instInhabited)
  rw [pEq, BoundedFormula.realize_bdEqual, HenselianTheory.realize_numeral (fieldInterpretation v),
    realize_tVFZero, vfZero_eq]
  change (Sum.inl ((p : ℕ) : K) : Carrier v) = Sum.inl 0
  rw [CharP.cast_eq_zero]

theorem residueCharP_realize {p : ℕ} (h : v (p : K) < 1) : Carrier v ⊨ residueCharP p := by
  change (HenselianTheory.inMaximalIdeal (tVFNumeral p : Tm 0)).Realize
    (@default (Empty → Carrier v) Unique.instInhabited)
    (@default (Fin 0 → Carrier v) Unique.instInhabited)
  rw [HenselianTheory.realize_inMaximalIdeal (fieldInterpretation v) _ _ _
    (HenselianTheory.realize_numeral (fieldInterpretation v) _ p)]
  exact h

theorem residueCharZero_realize_of {p : ℕ} (h : ¬ v (p : K) < 1) :
    Carrier v ⊨ Axioms.residueCharZero p := by
  change ¬ (HenselianTheory.inMaximalIdeal (tVFNumeral p : Tm 0)).Realize
    (@default (Empty → Carrier v) Unique.instInhabited)
    (@default (Fin 0 → Carrier v) Unique.instInhabited)
  rw [HenselianTheory.realize_inMaximalIdeal (fieldInterpretation v) _ _ _
    (HenselianTheory.realize_numeral (fieldInterpretation v) _ p)]
  exact h

theorem model_ACVF00_of [IsAlgClosed K] [CharZero K] (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1)
    (hres : ∀ p : ℕ, p.Prime → ¬ v (p : K) < 1) : Carrier v ⊨ Axioms.ACVF00 := by
  have h := model_ACVF v hnt
  constructor
  intro σ hσ
  rcases hσ with ((hσ | ⟨k, rfl⟩) | ⟨p, hp, rfl⟩)
  · exact h.realize_of_mem σ hσ
  · exact charZeroVF_realize v k
  · exact residueCharZero_realize_of v (hres p hp)

theorem model_ACVF0p [IsAlgClosed K] [CharZero K] (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1)
    {p : ℕ} (hp : v (p : K) < 1) : Carrier v ⊨ ACVF0p p := by
  have h := model_ACVF v hnt
  constructor
  intro σ hσ
  rcases hσ with ((hσ | ⟨k, rfl⟩) | rfl)
  · exact h.realize_of_mem σ hσ
  · exact charZeroVF_realize v k
  · exact residueCharP_realize v hp

theorem model_ACVFpp [IsAlgClosed K] (hnt : ∃ x : K, x ≠ 0 ∧ v x < 1)
    (p : ℕ) [CharP K p] : Carrier v ⊨ ACVFpp p := by
  have h := model_ACVF v hnt
  constructor
  intro σ hσ
  rcases hσ with (hσ | rfl)
  · exact h.realize_of_mem σ hσ
  · exact vfCharP_realize v p

end ConcreteValued

/-! ## Valuations dominating a local ring -/

/-- A ring map from a local ring into a field `K` factors through a valuation
subring of `K` whose valuation is `< 1` on the image of the maximal ideal and
`= 1` on the image of units (Chevalley). -/
theorem exists_dominating_valuation {R K : Type} [CommRing R] [IsLocalRing R] [Field K]
    (f : R →+* K) :
    ∃ A : ValuationSubring K,
      (∀ r ∈ IsLocalRing.maximalIdeal R, A.valuation (f r) < 1) ∧
      (∀ r : R, IsUnit r → A.valuation (f r) = 1) := by
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨A, fun r hr => ?_, fun r hr => ?_⟩
  · have hnu : f.codRestrict A.toSubring hA r ∈ IsLocalRing.maximalIdeal A := by
      intro hu
      exact hr (hloc.map_nonunit r hu)
    exact (A.valuation_lt_one_iff _).mp hnu
  · exact (A.valuation_eq_one_iff (f.codRestrict A.toSubring hA r)).mp
      (hr.map (f.codRestrict A.toSubring hA))

/-! ## The three characteristic pairs -/

/-- `(0,0)`: an algebraic closure of `ℚ((t))`. -/
theorem exists_model_ACVF00 :
    ∃ (M : Type) (_ : LRV.Structure M), M ⊨ Axioms.ACVF00 := by
  let F := LaurentSeries ℚ
  let K := AlgebraicClosure F
  let f : PowerSeries ℚ →+* K := (algebraMap F K).comp (HahnSeries.ofPowerSeries ℤ ℚ)
  obtain ⟨A, hmax, hunit⟩ := exists_dominating_valuation f
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hX : PowerSeries.X ∈ IsLocalRing.maximalIdeal (PowerSeries ℚ) := by
    intro hu
    have := (PowerSeries.isUnit_iff_constantCoeff (φ := (PowerSeries.X : PowerSeries ℚ))).mp hu
    simp at this
  have hfX : f PowerSeries.X ≠ 0 := by
    intro h0
    have hinj : Function.Injective f :=
      (algebraMap F K).injective.comp (HahnSeries.ofPowerSeries_injective)
    exact PowerSeries.X_ne_zero (hinj (h0.trans (map_zero f).symm))
  refine ⟨ConcreteValued.Carrier A.valuation, ConcreteValued.nativeStructure A.valuation,
    ConcreteValued.model_ACVF00_of A.valuation ⟨f PowerSeries.X, hfX, hmax _ hX⟩ ?_⟩
  intro p hp
  have hu : IsUnit (p : PowerSeries ℚ) := by
    rw [← map_natCast (PowerSeries.C (R := ℚ)) p]
    exact (IsUnit.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp.ne_zero)).map _
  have h1 := hunit _ hu
  rw [map_natCast] at h1
  rw [h1]
  exact lt_irrefl 1

/-- `(0,p)`: an algebraic closure of `ℚ_p`. -/
theorem exists_model_ACVF0p (p : ℕ) [hp : Fact p.Prime] :
    ∃ (M : Type) (_ : LRV.Structure M), M ⊨ ACVF0p p := by
  let K := AlgebraicClosure ℚ_[p]
  let f : ℤ_[p] →+* K := (algebraMap ℚ_[p] K).comp (PadicInt.Coe.ringHom)
  obtain ⟨A, hmax, -⟩ := exists_dominating_valuation f
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hpmax : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    change (p : ℤ_[p]) ∈ nonunits ℤ_[p]
    rw [PadicInt.mem_nonunits, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
  have hval : A.valuation (p : K) < 1 := by
    simpa [f] using hmax _ hpmax
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  exact ⟨ConcreteValued.Carrier A.valuation, ConcreteValued.nativeStructure A.valuation,
    ConcreteValued.model_ACVF0p A.valuation ⟨(p : K), hp0, hval⟩ hval⟩

/-- `(p,p)`: an algebraic closure of `𝔽_p((t))`. -/
theorem exists_model_ACVFpp (p : ℕ) [hp : Fact p.Prime] :
    ∃ (M : Type) (_ : LRV.Structure M), M ⊨ ACVFpp p := by
  let F := LaurentSeries (ZMod p)
  let K := AlgebraicClosure F
  let f : PowerSeries (ZMod p) →+* K := (algebraMap F K).comp (HahnSeries.ofPowerSeries ℤ (ZMod p))
  obtain ⟨A, hmax, -⟩ := exists_dominating_valuation f
  letI : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
  have hX : PowerSeries.X ∈ IsLocalRing.maximalIdeal (PowerSeries (ZMod p)) := by
    intro hu
    have := (PowerSeries.isUnit_iff_constantCoeff (φ := (PowerSeries.X : PowerSeries (ZMod p)))).mp hu
    simp at this
  have hfX : f PowerSeries.X ≠ 0 := by
    intro h0
    have hinj : Function.Injective f :=
      (algebraMap F K).injective.comp (HahnSeries.ofPowerSeries_injective)
    exact PowerSeries.X_ne_zero (hinj (h0.trans (map_zero f).symm))
  exact ⟨ConcreteValued.Carrier A.valuation, ConcreteValued.nativeStructure A.valuation,
    ConcreteValued.model_ACVFpp A.valuation ⟨f PowerSeries.X, hfX, hmax _ hX⟩ p⟩

/-- `Axioms.ACVF` has a model. -/
theorem exists_model_ACVF : ∃ (M : Type) (_ : LRV.Structure M), M ⊨ Axioms.ACVF := by
  obtain ⟨M, _, h⟩ := exists_model_ACVF00
  exact ⟨M, inferInstance, h.mono (fun σ hσ => Or.inl (Or.inl hσ))⟩

end ACVFQE.Models
