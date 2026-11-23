/-
The theory `ACVF` in the valued-field language and its nontriviality axiom.
The language of valued fields, its axioms and prime models are owned by
hilbert-mathlib (`HilbertMathlib.Foundation.ModelTheory.ValuedFieldLanguage`).
-/
import HilbertMathlib.Foundation.ModelTheory.ValuedFieldLanguage

open FirstOrder FirstOrder.Language
open scoped FirstOrder

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace ValPM

open FirstOrder FirstOrder.Language FirstOrder.Ring

/-! ## 12. The theory `ACVF` in `L_val` -/

/-- The `L_val`-sentence "every monic polynomial of degree `n` has a root", read along
`valRingHom` from the language of rings. -/
noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.val.Sentence :=
  valRingHom.onBoundedFormula (Field.genericMonicPolyHasRoot n)

/-- The valuation is nontrivial: some **nonzero** element lies in the maximal ideal,
`v x < v 1`.

The `x ≠ 0` conjunct is essential and its absence was a real defect: `0` satisfies `v 0 < v 1` in
*every* valued field, so `∃ x, ¬ (v 1 ≤ v x)` alone is a tautology and says nothing about
nontriviality.  The sentence below is the one that has to be used. -/
def axNontrivialF : Language.val.BoundedFormula Empty 1 := ∼((&0) =' 0) ⊓ ∼(leF 1 (&0))

/-- **Nontriviality of the valuation**, as a sentence of `L_val`. -/
def axNontrivial : Language.val.Sentence := axNontrivialF.ex

/-- **The theory of nontrivially valued algebraically closed fields in `L_val`.** -/
noncomputable def ACVF_val : Language.val.Theory :=
  valField ∪ genericMonicPolyHasRoot '' {n : ℕ | 0 < n} ∪ {axNontrivial}

theorem valField_subset_ACVF_val : valField ⊆ ACVF_val := by
  intro φ hφ
  exact Or.inl (Or.inl hφ)


/-- **Hypothesis (i) of Johnson's criterion at `L_val`**: prime models over substructures, for
`ACVF` in the language of valued fields. -/
theorem hasPrimeModels_ACVF_val : HasPrimeModels valField ACVF_val :=
  hasPrimeModels_mono valField_subset_ACVF_val hasPrimeModels_valField

#print axioms ValPM.hasPrimeModels_ACVF_val



/-- The nontriviality sentence asserts a nonzero element in the maximal ideal.
It is phrased with the value of the constant `1` rather than `(1 : M)`, because an
abstract `L_val`-structure carries no `One` instance. -/
theorem axNontrivial_realize {M : Type*} [CommRing M] [Language.val.Structure M]
    [CompatibleRing M] [valRingHom.IsExpansionOn M] :
    (M ⊨ axNontrivial) ↔
      ∃ x : M, x ≠ 0 ∧
        ¬ predM (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) x := by
  have hone : (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) = (1 : M) :=
    valFunMap_one
  have hval : ∀ a : M,
      (∼((&0) =' (0 : Language.val.Term (Empty ⊕ Fin 1)))
          ⊓ ∼(leF (1 : Language.val.Term (Empty ⊕ Fin 1)) (var (Sum.inr 0)))).Realize
          (default : Empty → M) (Fin.snoc (default : Fin 0 → M) a)
        ↔ a ≠ 0 ∧
            ¬ predM (@Structure.funMap Language.val M _ 0 ValFunc.one (fun i => i.elim0)) a := by
    intro a
    rw [show (1 : Language.val.Term (Empty ⊕ Fin 1))
        = (1 : Language.val.Term (Empty ⊕ Fin 1)) from rfl]
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_not,
      BoundedFormula.realize_bdEqual, leF_realize, realize_varTerm', realize_oneTerm',
      realize_zeroTerm', valFunMap_zero, Sum.elim_inr, Fin.snoc_last, hone]
    rfl
  simp only [axNontrivial, axNontrivialF, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_ex]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, (hval a).mp ha⟩, fun ⟨a, ha⟩ => ⟨a, (hval a).mpr ha⟩⟩

#print axioms ValPM.axNontrivial_realize

end ValPM
