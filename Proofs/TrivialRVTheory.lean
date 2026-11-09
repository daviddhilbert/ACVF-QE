import TrivialRVQE

/-! The separate theory of canonical trivially valued RV structures.
The presentation uses the common sentence theory of these structures. -/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SpecialTransformations.TrivialRV

local instance {K : Type} [Field K] : LRV.Structure (K ⊕ K) := interpret

/-- All sentences valid in the canonical trivially valued algebraically
closed fields, with the two sorts and named RV inverse. -/
def theory : LRV.Theory :=
  {σ | ∀ (K : Type) [Field K] [IsAlgClosed K], (K ⊕ K) ⊨ σ}

theorem canonical_model (K : Type) [Field K] [IsAlgClosed K] : (K ⊕ K) ⊨ theory :=
  ⟨fun _ hσ => hσ K⟩

private def sortGuard {I : Type} (s : I → SortTag) (i : I) : LRV.Formula I :=
  sortPredG (s i) (.var (.inl i))

private theorem sortGuard_realize {I M : Type} [LRV.Structure M]
    (s : I → SortTag) (i : I) (w : I → M) :
    (sortGuard s i).Realize w ↔ sortEval (s i) (w i) := by
  cases h : s i <;> rw [sortGuard, h] <;> exact BoundedFormula.realize_rel₁

private def sortedClosure {I : Type} (s : I → SortTag) (f : LRV.Formula I) : LRV.Sentence :=
  let J := f.freeVarFinset
  let g : LRV.Formula J := Formula.iInf (sortGuard (s ∘ Subtype.val))
  ((g.imp (f.restrictFreeVar id)).relabel (Sum.inr : J → Empty ⊕ J)).iAlls J

private theorem sortedClosure_realize {I M : Type} [LRV.Structure M]
    (s : I → SortTag) (f : LRV.Formula I) :
    M ⊨ sortedClosure s f ↔
      ∀ w : f.freeVarFinset → M, (∀ i, sortEval (s i.val) (w i)) →
        Formula.Realize (f.restrictFreeVar id) w := by
  simp only [sortedClosure, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
    Sum.elim_comp_inr, Formula.realize_imp, Formula.realize_iInf, sortGuard_realize,
    Function.comp_apply]

theorem hasQE : HasQE theory := by
  intro α sα n sn φ _
  letI : DecidableEq (α ⊕ Fin n) := Classical.decEq _
  obtain ⟨ψ, hQ, hS, h⟩ := canonical_trivial_rv_qe α sα n sn φ
  let s := Sum.elim sα sn
  let f : LRV.Formula (α ⊕ Fin n) := φ.toFormula.iff ψ.toFormula
  have hf {M : Type} [LRV.Structure M] (z : α ⊕ Fin n → M) :
      f.Realize z ↔ (φ.Realize (z ∘ Sum.inl) (z ∘ Sum.inr) ↔
        ψ.Realize (z ∘ Sum.inl) (z ∘ Sum.inr)) := by
    simp only [f, Formula.realize_iff, BoundedFormula.realize_toFormula]
  have hσ : sortedClosure s f ∈ theory := by
    intro K _ _
    apply (sortedClosure_realize s f).mpr
    intro w hw
    let z (i : α ⊕ Fin n) : K ⊕ K :=
      if hi : i ∈ f.freeVarFinset then w ⟨i, hi⟩ else
        match s i with | .vf => Sum.inl 0 | .rv => Sum.inr 0
    have hz (i) : sortEval (s i) (z i) := by
      by_cases hi : i ∈ f.freeVarFinset
      · simpa only [z, dif_pos hi] using hw ⟨i, hi⟩
      · simp only [z, dif_neg hi]
        cases s i with
        | vf =>
          change True
          trivial
        | rv =>
          change ¬ False
          exact not_false
    have he (i : f.freeVarFinset) : w (id i) = z i.val := by
      simp only [z, i.property, dif_pos, id_eq]
    apply (BoundedFormula.realize_restrictFreeVar (φ := f) (f := id) (v := w)
      (xs := default) z he).mpr
    exact (hf z).mpr (h K (z ∘ Sum.inl) (z ∘ Sum.inr)
      (fun i => hz (.inl i)) (fun i => hz (.inr i)))
  refine ⟨ψ, hQ, hS, ?_⟩
  intro M _ hM v x hv hx
  let z := Sum.elim v x
  have hz (i) : sortEval (s i) (z i) := by
    cases i with
    | inl i => exact hv i
    | inr i => exact hx i
  have hh := (sortedClosure_realize s f).mp (hM.realize_of_mem _ hσ)
    (fun i => z i.val) (fun i => hz i.val)
  exact (hf z).mp ((BoundedFormula.realize_restrictFreeVar (φ := f) (f := id)
    (v := fun i => z i.val) (xs := default) z (fun _ => rfl)).mp hh)

end SpecialTransformations.TrivialRV

#check @SpecialTransformations.TrivialRV.canonical_model
#print axioms SpecialTransformations.TrivialRV.canonical_model
#check @SpecialTransformations.TrivialRV.hasQE
#print axioms SpecialTransformations.TrivialRV.hasQE
