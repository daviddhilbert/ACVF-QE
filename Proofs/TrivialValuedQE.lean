module

public import JohnsonACFMain
public import JohnsonLanguagePrime

@[expose] public section

/-! Quantifier elimination for the trivial branch in the ordinary
valued-field language. Valuation comparisons reduce to zero tests. -/

open FirstOrder FirstOrder.Language FirstOrder.Ring
open scoped FirstOrder
set_option backward.isDefEq.respectTransparency false

namespace ValPM

/-- In the multiplicative order, zero is least and all nonzero values agree. -/
def axTrivial : Language.val.Sentence :=
  let x : Language.val.Term (Empty ⊕ Fin 2) := .var (.inr ⟨0, Nat.zero_lt_two⟩)
  let y : Language.val.Term (Empty ⊕ Fin 2) := .var (.inr ⟨1, Nat.one_lt_two⟩)
  let z : Language.val.Term (Empty ⊕ Fin 2) := .func ValFunc.zero (fun i => i.elim0)
  (BoundedFormula.iff (leF x y) (x.bdEqual z ⊔ (y.bdEqual z).not)).alls

noncomputable def ACVFTrivial_val : Language.val.Theory :=
  valRingHom.onTheory ACFValidation.acf ∪ {axTrivial}

private def eraseSymbol {n : ℕ} : ValFunc n → Language.ring.Functions n
  | .add => addFunc
  | .mul => mulFunc
  | .neg => negFunc
  | .zero => zeroFunc
  | .one => oneFunc

private def eraseTerm {α : Type} : Language.val.Term α → Language.ring.Term α
  | .var i => .var i
  | .func f a => .func (eraseSymbol f) (fun i => eraseTerm (a i))

private def eraseFormula {α : Type} :
    {n : ℕ} → Language.val.BoundedFormula α n → Language.ring.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (eraseTerm t) (eraseTerm u)
  | _, .rel .le a => ((eraseTerm (a 0)).bdEqual 0) ⊔ ((eraseTerm (a 1)).bdEqual 0).not
  | _, .imp φ ψ => .imp (eraseFormula φ) (eraseFormula ψ)
  | _, .all φ => .all (eraseFormula φ)

section

variable {M : Type} [Language.val.Structure M]
local instance : Language.ring.Structure M := valRingHom.reduct M

private theorem eraseTerm_realize {α : Type} (t : Language.val.Term α) (v : α → M) :
    (eraseTerm t).realize v = t.realize v := by
  induction t with
  | var _ => rfl
  | func f a ih =>
    cases f <;> simp only [eraseTerm, eraseSymbol, Term.realize, ih] <;> rfl

private theorem val_zero_realize {α : Type} (v : α → M) :
    (0 : Language.val.Term α).realize v = (0 : Language.ring.Term Empty).realize Empty.elim := by
  change Structure.funMap (L := Language.val) ValFunc.zero _ =
    Structure.funMap (L := Language.val) ValFunc.zero _
  exact congrArg (Structure.funMap (L := Language.val) ValFunc.zero) (Subsingleton.elim _ _)

private theorem ring_zero_realize {α : Type} (v : α → M) :
    (0 : Language.ring.Term α).realize v = (0 : Language.ring.Term Empty).realize Empty.elim := by
  change Structure.funMap (L := Language.ring) zeroFunc _ =
    Structure.funMap (L := Language.ring) zeroFunc _
  exact congrArg (Structure.funMap (L := Language.ring) zeroFunc) (Subsingleton.elim _ _)

private theorem axTrivial_realize (h : M ⊨ axTrivial) (x y : M) :
    predM x y ↔ x = (0 : Language.ring.Term Empty).realize Empty.elim ∨
      y ≠ (0 : Language.ring.Term Empty).realize Empty.elim := by
  have hh := (BoundedFormula.realize_alls.mp h) ![x, y]
  change ((Relations.boundedFormula₂ (L := Language.val) ValRel.le
    (Term.var (.inr 0)) (Term.var (.inr 1))).iff
      ((Term.var (.inr (0 : Fin 2))).bdEqual (0 : Language.val.Term (Empty ⊕ Fin 2)) ⊔
        ((Term.var (.inr (1 : Fin 2))).bdEqual 0).not)).Realize
    (default : Empty → M) ![x, y] at hh
  simpa only [BoundedFormula.realize_iff, BoundedFormula.realize_sup,
    BoundedFormula.realize_not, BoundedFormula.realize_bdEqual, BoundedFormula.realize_rel₂,
    Term.realize_var, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, val_zero_realize] using hh

private theorem eraseFormula_realize (h : M ⊨ axTrivial) {α : Type} {n : ℕ}
    (φ : Language.val.BoundedFormula α n) (v : α → M) (a : Fin n → M) :
    (eraseFormula φ).Realize v a ↔ φ.Realize v a := by
  induction φ with
  | falsum => rfl
  | equal t u => simp [eraseFormula, BoundedFormula.Realize, eraseTerm_realize]
  | rel r ts =>
    cases r
    have hh := axTrivial_realize h ((ts 0).realize (Sum.elim v a)) ((ts 1).realize (Sum.elim v a))
    have hts : ts = ![ts 0, ts 1] := by
      funext i
      fin_cases i <;> rfl
    have hrel : (BoundedFormula.rel ValRel.le ts).Realize v a ↔
        predM ((ts 0).realize (Sum.elim v a)) ((ts 1).realize (Sum.elim v a)) := by
      conv_lhs => rw [hts]
      exact BoundedFormula.realize_rel₂
    simpa only [eraseFormula, BoundedFormula.realize_sup, BoundedFormula.realize_not,
      BoundedFormula.realize_bdEqual, eraseTerm_realize, hrel,
      ring_zero_realize] using hh.symm
  | imp φ ψ ihφ ihψ => simp [eraseFormula, BoundedFormula.realize_imp, ihφ, ihψ]
  | all φ ih => simp [eraseFormula, BoundedFormula.realize_all, ih]

end

private theorem lift_isQF {α : Type} {n : ℕ} {φ : Language.ring.BoundedFormula α n}
    (hφ : φ.IsQF) : (valRingHom.onBoundedFormula φ).IsQF := by
  induction hφ with
  | falsum => exact .falsum
  | of_isAtomic h =>
    cases h with
    | equal _ _ => exact .of_isAtomic (.equal _ _)
    | rel r _ => exact isEmptyElim r
  | imp _ _ h₁ h₂ => exact h₁.imp h₂

theorem hasQEb_ACVF_trivial_val : QECriterion.HasQEb ACVFTrivial_val := by
  intro α n φ
  obtain ⟨ψ, hψ, he⟩ := JohnsonACF.hasQEb α n (eraseFormula φ)
  refine ⟨valRingHom.onBoundedFormula ψ, lift_isQF hψ, ?_⟩
  intro M v a
  have ht : M ⊨ axTrivial := Theory.realize_sentence_of_mem ACVFTrivial_val (Or.inr rfl)
  letI : Language.ring.Structure M := valRingHom.reduct M
  have hA : M ⊨ valRingHom.onTheory ACFValidation.acf :=
    (inferInstance : M ⊨ ACVFTrivial_val).mono Set.subset_union_left
  haveI : M ⊨ ACFValidation.acf := (valRingHom.onTheory_model ACFValidation.acf).mp hA
  have hψ' := Theory.Iff.realize_bd_iff (M := M) he (v := v) (xs := a)
  rw [BoundedFormula.realize_iff, valRingHom.realize_onBoundedFormula]
  exact (eraseFormula_realize ht φ v a).symm.trans hψ'

theorem hasQE_ACVF_trivial_val : QECriterion.HasQE ACVFTrivial_val :=
  QECriterion.HasQE_of_hasQEb hasQEb_ACVF_trivial_val

end ValPM

#check @ValPM.hasQEb_ACVF_trivial_val
#print axioms ValPM.hasQEb_ACVF_trivial_val
