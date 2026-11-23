import JohnsonGeometry
import HilbertMathlib.Foundation.Valuation.ValuedFieldAmalgamation

/-!
# Johnson's Chapter 2 proof: valued-field amalgamation

Extracted from the existing QE/Assembly_val.lean (sections 17–19).
The tensor-product statement `Johnson22.star` is proved here and supplies
amalgamation; no amalgamation theorem or QE theorem is assumed.
-/

open FirstOrder FirstOrder.Language FirstOrder.Ring
open scoped FirstOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-! ## 17. Johnson §2.2: amalgamation of valuation rings (`star`) -/

set_option maxHeartbeats 1000000

open IsLocalRing

set_option linter.style.haveILetI false


#print axioms Johnson22.chevalley_subring
#print axioms Johnson22.chevalley_hom
#print axioms Johnson22.chevalley_hom'
#print axioms Johnson22.valuedEmbedding_of_localHom
#print axioms Johnson22.flat_of_torsion_eq_bot
#print axioms Johnson22.torsion_eq_bot_of_injective
#print axioms Johnson22.star
#check Johnson22.amalgamation_of_ring_amalgamation Johnson22.star
#check Johnson22.star

section EndToEnd
universe u

/-- End-to-end check: `star` has the exact shape that `amalgamation_of_ring_amalgamation` consumes,
and the amalgamation property for valued fields follows from it at universe `Type u`. -/
example {F F₁ F₂ : Type u} [Field F] [Field F₁] [Field F₂]
    (O : ValuationSubring F) (O₁ : ValuationSubring F₁) (O₂ : ValuationSubring F₂)
    (i₁ : F →+* F₁) (i₂ : F →+* F₂)
    (h₁ : Johnson22.IsValEmbedding O.valuation O₁.valuation i₁)
    (h₂ : Johnson22.IsValEmbedding O.valuation O₂.valuation i₂) :
    ∃ (N : Type u) (_ : Field N) (O₃ : ValuationSubring N) (j₁ : F₁ →+* N) (j₂ : F₂ →+* N),
      Johnson22.IsValEmbedding O₁.valuation O₃.valuation j₁ ∧
      Johnson22.IsValEmbedding O₂.valuation O₃.valuation j₂ ∧ j₁.comp i₁ = j₂.comp i₂ :=
  Johnson22.amalgamation_of_ring_amalgamation Johnson22.star O O₁ O₂ i₁ i₂ h₁ h₂

end EndToEnd

#print axioms Johnson22.isValEmbedding_of_mem_iff
#print axioms Johnson22.amalgamation_of_ring_amalgamation
#print axioms Johnson22.valExtension_of_fieldExtension

/-! ## 18. `HasAmalgamation valField` -/

namespace ValOneEC

section ValSubring

/-- The order of a valuation is the order of its valuation subring's canonical valuation.  This is
what lets Johnson's §2.2 amalgamation theorem, which is stated for `ValuationSubring`s, be applied
to the valuations `exists_valuation_of_isValPred` produces. -/
theorem le_iff_valuationSubring_valuation_le {K : Type} [Field K] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (x y : K) :
    v x ≤ v y ↔ v.valuationSubring.valuation x ≤ v.valuationSubring.valuation y := by
  rw [ValuationSubring.valuation_le_iff]
  constructor
  · intro h
    by_cases hy : y = 0
    · subst hy
      rw [map_zero] at h
      have hx : x = 0 := v.zero_iff.mp (le_antisymm h zero_le)
      subst hx
      exact ⟨0, by simp⟩
    · refine ⟨⟨x * y⁻¹, ?_⟩, by field_simp⟩
      rw [Valuation.mem_valuationSubring_iff, map_mul, map_inv₀]
      calc v x * (v y)⁻¹ ≤ v y * (v y)⁻¹ := by
            exact mul_le_mul_left h _
        _ = 1 := by rw [mul_inv_cancel₀ (v.ne_zero_iff.mpr hy)]
  · rintro ⟨a, ha⟩
    have hx : v x = v (a : K) * v y := by
      rw [← ha, map_mul]
    rw [hx]
    calc v (a : K) * v y ≤ 1 * v y := by
          exact mul_le_mul_left a.2 _
      _ = v y := one_mul _

/-- An `L_val`-embedding between `valStructure`s is a Johnson valued embedding of `ValuationSubring`s. -/
theorem isValEmbedding_of_valEmb {K : Type} [Field K] {K' : Type} [Field K'] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] {Γ' : Type} [LinearOrderedCommGroupWithZero Γ']
    {v : Valuation K Γ} {w : Valuation K' Γ'}
    (F : @Embedding Language.val K K' (FirstOrder.valStructure v) (FirstOrder.valStructure w)) :
    Johnson22.IsValEmbedding v w (ringHomOfEmbedding v w F) := by
  letI := FirstOrder.valStructure v
  letI := FirstOrder.valStructure w
  refine ⟨fun x y h => F.inj' h, fun x y => ?_⟩
  have h := F.map_rel' ValRel.le ![x, y]
  have h' : (F.toFun ∘ ![x, y]) = ![F.toFun x, F.toFun y] := by
    funext i
    fin_cases i <;> rfl
  rw [h'] at h
  exact h.symm

end ValSubring

end ValOneEC

/-! ## 19. `HasAmalgamation valField` -/

namespace ValOneEC

section Amalgamation

open FirstOrder FirstOrder.Language FirstOrder.Ring

/-- Copy of `JohnsonCriterion.HasAmalgamation` (`QE/ACF_HasQE.lean`) specialised to `L_val`. -/
def HasAmalgamation (T : Language.val.Theory) : Prop :=
  ∀ (A B C : T.ModelType.{0, 0, 0}) (i : A ↪[Language.val] B) (j : A ↪[Language.val] C),
    ∃ (D : T.ModelType.{0, 0, 0}) (i' : B ↪[Language.val] D) (j' : C ↪[Language.val] D),
      i'.comp i = j'.comp j

/-- A Johnson valued embedding of valuations is one of their valuation subrings. -/
theorem isValEmbedding_subring {K : Type} [Field K] {K' : Type} [Field K'] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] {Γ' : Type} [LinearOrderedCommGroupWithZero Γ']
    {v : Valuation K Γ} {w : Valuation K' Γ'} {f : K →+* K'}
    (h : Johnson22.IsValEmbedding v w f) :
    Johnson22.IsValEmbedding v.valuationSubring.valuation w.valuationSubring.valuation f := by
  refine ⟨h.1, fun x y => ?_⟩
  rw [← le_iff_valuationSubring_valuation_le v x y,
    ← le_iff_valuationSubring_valuation_le w (f x) (f y)]
  exact h.2 x y

/-- A model of `valField`, together with a valuation realising its predicate, has its own structure
equal to the `valStructure` of the valuation subring's canonical valuation. -/
theorem valStruct_eq_of_valuationSubring (M : ValPM.valField.ModelType.{0, 0, 0}) [Field M]
    [CompatibleRing M] [valRingHom.IsExpansionOn M] {Γ : Type}
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation M Γ)
    (hv : ∀ x y, (ValPM.predM : M → M → Prop) x y ↔ v x ≤ v y) :
    M.struc = FirstOrder.valStructure v.valuationSubring.valuation :=
  (ValPM.valStruct_ext M).trans
    (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : M → M → Prop))
      (v := v.valuationSubring.valuation) (fun x y =>
        (hv x y).trans (le_iff_valuationSubring_valuation_le v x y)))

/-- **The amalgamation property for `valField`**, from Johnson's §2.2 theorem for valuation
rings.  Each model of `valField` is a Mathlib valued field, its own `L_val`-structure is the
`valStructure` of the valuation subring's canonical valuation, and
`amalgamation_of_ring_amalgamation` then produces the amalgam, which is packaged as a model of
`valField` again through `valStructure_model`. -/
theorem hasAmalgamation_valField : HasAmalgamation ValPM.valField := by
  intro A B C i j
  -- field structures on `A`
  letI : Language.ring.Structure A := ValPM.ringStructOfVal A
  haveI hexpA : valRingHom.IsExpansionOn A := ValPM.ringStructOfVal.expansion A
  have hfieldA : A ⊨ Theory.field := ValPM.model_field_of_valField A A.is_model
  letI : Field A := FirstOrder.Field.fieldOfModelField A
  letI : CompatibleRing A := FirstOrder.Field.compatibleRingOfModelField A
  have hpredA : ValPM.IsValPred (ValPM.predM : A → A → Prop) := ValPM.isValPred_of_model A.is_model
  letI : Language.ring.Structure B := ValPM.ringStructOfVal B
  haveI hexpB : valRingHom.IsExpansionOn B := ValPM.ringStructOfVal.expansion B
  have hfieldB : B ⊨ Theory.field := ValPM.model_field_of_valField B B.is_model
  letI : Field B := FirstOrder.Field.fieldOfModelField B
  letI : CompatibleRing B := FirstOrder.Field.compatibleRingOfModelField B
  have hpredB : ValPM.IsValPred (ValPM.predM : B → B → Prop) := ValPM.isValPred_of_model B.is_model
  letI : Language.ring.Structure C := ValPM.ringStructOfVal C
  haveI hexpC : valRingHom.IsExpansionOn C := ValPM.ringStructOfVal.expansion C
  have hfieldC : C ⊨ Theory.field := ValPM.model_field_of_valField C C.is_model
  letI : Field C := FirstOrder.Field.fieldOfModelField C
  letI : CompatibleRing C := FirstOrder.Field.compatibleRingOfModelField C
  have hpredC : ValPM.IsValPred (ValPM.predM : C → C → Prop) := ValPM.isValPred_of_model C.is_model
  -- valuations
  obtain ⟨ΓA, hΓA, vA, hvA⟩ := ValPM.exists_valuation_of_isValPred hpredA
  letI := hΓA
  obtain ⟨ΓB, hΓB, vB, hvB⟩ := ValPM.exists_valuation_of_isValPred hpredB
  letI := hΓB
  obtain ⟨ΓC, hΓC, vC, hvC⟩ := ValPM.exists_valuation_of_isValPred hpredC
  letI := hΓC
  -- the structures realised by the valuation subrings
  have hAs : A.struc = FirstOrder.valStructure vA.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring A vA hvA
  have hBs : B.struc = FirstOrder.valStructure vB.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring B vB hvB
  have hCs : C.struc = FirstOrder.valStructure vC.valuationSubring.valuation :=
    valStruct_eq_of_valuationSubring C vC hvC
  -- the two embeddings, transported
  let FAB : @Embedding Language.val A B (FirstOrder.valStructure vA) (FirstOrder.valStructure vB) :=
    embeddingCast ((ValPM.valStruct_ext A).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : A → A → Prop)) (v := vA) hvA))
      ((ValPM.valStruct_ext B).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : B → B → Prop)) (v := vB) hvB)) i
  let FAC : @Embedding Language.val A C (FirstOrder.valStructure vA) (FirstOrder.valStructure vC) :=
    embeddingCast ((ValPM.valStruct_ext A).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : A → A → Prop)) (v := vA) hvA))
      ((ValPM.valStruct_ext C).trans
      (ValPM.valStructOf_eq_valStructure (p := (ValPM.predM : C → C → Prop)) (v := vC) hvC)) j
  -- the amalgam
  obtain ⟨N, hN, O₃, j₁, j₂, hj₁, hj₂, hcomm⟩ :=
    Johnson22.amalgamation_of_ring_amalgamation Johnson22.star
      vA.valuationSubring vB.valuationSubring vC.valuationSubring
      (ringHomOfEmbedding vA vB FAB) (ringHomOfEmbedding vA vC FAC)
      (isValEmbedding_subring (isValEmbedding_of_valEmb FAB))
      (isValEmbedding_subring (isValEmbedding_of_valEmb FAC))
  letI : Field N := hN
  letI : Language.val.Structure N := FirstOrder.valStructure O₃.valuation
  haveI : N ⊨ ValPM.valField := ValPM.valStructure_model O₃.valuation
  -- the amalgam as a model of `valField`, with its structure and the two embeddings
  let D : ValPM.valField.ModelType.{0, 0, 0} := Theory.ModelType.of (T := ValPM.valField) N
  have hDs : (D.struc : Language.val.Structure N) = FirstOrder.valStructure O₃.valuation := rfl
  let innerB : @Embedding Language.val B N (FirstOrder.valStructure vB.valuationSubring.valuation)
      (FirstOrder.valStructure O₃.valuation) :=
    embeddingOfIsValEmb vB.valuationSubring.valuation O₃.valuation j₁ hj₁.1 hj₁.2
  let innerC : @Embedding Language.val C N (FirstOrder.valStructure vC.valuationSubring.valuation)
      (FirstOrder.valStructure O₃.valuation) :=
    embeddingOfIsValEmb vC.valuationSubring.valuation O₃.valuation j₂ hj₂.1 hj₂.2
  refine ⟨D, ?_, ?_, ?_⟩
  · exact embeddingCast hBs.symm hDs.symm innerB
  · exact embeddingCast hCs.symm hDs.symm innerC
  · -- the square commutes, because all the casts preserve the underlying function
    refine FirstOrder.Language.Embedding.ext ?_
    intro a
    have h := RingHom.congr_fun hcomm a
    exact h

end Amalgamation

end ValOneEC

#print axioms ValOneEC.hasAmalgamation_valField
#print axioms ValOneEC.isValEmbedding_subring
#print axioms ValOneEC.valStruct_eq_of_valuationSubring
#check @ValOneEC.hasAmalgamation_valField
#check @ValOneEC.oneECIn_of_modelType
#check @ValPM.hasPrimeModels_ACVF_val

