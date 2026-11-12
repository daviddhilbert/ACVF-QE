module

public import Enc
public import JohnsonACFMain
public import TaggedCoordinates

@[expose] public section

/-! The trivially valued RV model has two copies of the same field.
The field interpretation retains a tag and the underlying element.
The inverse symbol is translated through its definable graph. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
open scoped FirstOrder
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV

noncomputable section

namespace SpecialTransformations.TrivialRV

def value {K : Type} : K ⊕ K → K := Sum.elim id id

def fieldFn {K : Type} [Field K] : {n : ℕ} → Fn n → (Fin n → K ⊕ K) → K
  | _, .vfZero, _ => 0
  | _, .vfOne, _ => 1
  | _, .vfAdd, x => value (x 0) + value (x 1)
  | _, .vfNeg, x => -value (x 0)
  | _, .vfMul, x => value (x 0) * value (x 1)
  | _, .rvZero, _ => 0
  | _, .rvOne, _ => 1
  | _, .rvMul, x => value (x 0) * value (x 1)
  | _, .rvInv, x => (value (x 0))⁻¹
  | _, .kAdd, x => value (x 0) + value (x 1)
  | _, .kNeg, x => -value (x 0)
  | _, .rvMap, x => value (x 0)

def inVF {K : Type} : K ⊕ K → Prop
  | .inl _ => True
  | .inr _ => False

@[instance_reducible] def interpret {K : Type} [Field K] : LRV.Structure (K ⊕ K) where
  funMap f x :=
    match Fn.resSort f with
    | .vf => .inl (fieldFn f x)
    | .rv => .inr (fieldFn f x)
  RelMap
    | .memVF, x => inVF (x 0)
    | .memRV, x => ¬ inVF (x 0)
    | .memUnits, x => ¬ inVF (x 0) ∧ value (x 0) ≠ 0
    | .rvLe, x => ¬ inVF (x 0) ∧ ¬ inVF (x 1) ∧
        (value (x 0) ≠ 0 ∨ value (x 1) = 0)

local instance {K : Type} [Field K] : LRV.Structure (K ⊕ K) := interpret

def code {K : Type} [Field K] (p : TaggedCoordinates.Coord → K) : K ⊕ K :=
  if p 0 = 0 then .inl (p 1) else .inr (p 1)

theorem code_onto {K : Type} [Field K] : Function.Surjective (code (K := K)) := by
  rintro (x | x)
  · exact ⟨![0, x], by simp [code]⟩
  · exact ⟨![1, x], by simp [code]⟩

@[simp] theorem code_value {K : Type} [Field K] (p : TaggedCoordinates.Coord → K) :
    value (code p) = p 1 := by
  simp [code, value]; split <;> rfl

@[simp] theorem code_inVF {K : Type} [Field K] (p : TaggedCoordinates.Coord → K) :
    inVF (code p) ↔ p 0 = 0 := by
  by_cases hp : p 0 = 0 <;> simp [code, inVF, hp]

private def isZero {I : Type} (t : Language.ring.Term I) : Language.ring.Formula I := t.equal 0

private def tag {I : Type} (s : SortTag) (t : Language.ring.Term I) : Language.ring.Formula I :=
  match s with
  | .vf => isZero t
  | .rv => (isZero t).not

private def ringOutput {I : Type} : {n : ℕ} → Fn n →
    (Fin n → Language.ring.Term I) → Language.ring.Term I → Language.ring.Formula I
  | _, .vfZero, _, y => isZero y
  | _, .vfOne, _, y => y.equal 1
  | _, .vfAdd, x, y => y.equal (x 0 + x 1)
  | _, .vfNeg, x, y => y.equal (-x 0)
  | _, .vfMul, x, y => y.equal (x 0 * x 1)
  | _, .rvZero, _, y => isZero y
  | _, .rvOne, _, y => y.equal 1
  | _, .rvMul, x, y => y.equal (x 0 * x 1)
  | _, .rvInv, x, y => (isZero (x 0) ⊓ isZero y) ⊔ (x 0 * y).equal 1
  | _, .kAdd, x, y => y.equal (x 0 + x 1)
  | _, .kNeg, x, y => y.equal (-x 0)
  | _, .rvMap, x, y => y.equal (x 0)

private def ringRelation {I : Type} : {n : ℕ} → Rel n →
    (Fin n → TaggedCoordinates.Coord → Language.ring.Term I) → Language.ring.Formula I
  | _, .memVF, x => tag .vf (x 0 0)
  | _, .memRV, x => tag .rv (x 0 0)
  | _, .memUnits, x => tag .rv (x 0 0) ⊓ (isZero (x 0 1)).not
  | _, .rvLe, x => tag .rv (x 0 0) ⊓ tag .rv (x 1 0) ⊓
      ((isZero (x 0 1)).not ⊔ isZero (x 1 1))

private def dictionary : TaggedCoordinates.Syntax LRV Language.ring where
  equality :=
    let l := isZero (.var (.inl 0))
    let r := isZero (.var (.inr 0))
    (l.imp r ⊓ r.imp l) ⊓ (Term.var (.inl 1)).equal (.var (.inr 1))
  functionGraph f :=
    tag (Fn.resSort f) (.var (.inr 0)) ⊓
      ringOutput f (fun i => .var (.inl (i, 1))) (.var (.inr 1))
  relationGraph r := ringRelation r (fun i j => .var (i, j))

variable {K : Type} [Field K] [CompatibleRing K]

private theorem inverse_graph (x y : K) :
    (x = 0 ∧ y = 0) ∨ x * y = 1 ↔ y = x⁻¹ := by
  by_cases h : x = 0
  · simp [h]
  · simp only [h, false_and, false_or]
    exact ⟨fun hxy => eq_inv_of_mul_eq_one_right hxy, fun hy => hy ▸ mul_inv_cancel₀ h⟩

private theorem ringOutput_realize {I : Type} {n : ℕ} (f : Fn n)
    (x : Fin n → Language.ring.Term I) (y : Language.ring.Term I) (v : I → K) :
    (ringOutput f x y).Realize v ↔ y.realize v =
      fieldFn f (fun i => .inr ((x i).realize v)) := by
  cases f <;> simp [ringOutput, isZero, fieldFn, value, inverse_graph]

private theorem fieldFn_code {n : ℕ} (f : Fn n) (x : Fin n → TaggedCoordinates.Coord → K) :
    fieldFn f (fun i => code (x i)) = fieldFn f (fun i => .inr (x i 1)) := by
  have hf (i : Fin n) : value (code (x i)) = value (Sum.inr (x i 1)) := code_value (x i)
  cases f <;> simp only [fieldFn, hf]

private theorem code_ext (x y : TaggedCoordinates.Coord → K) :
    code x = code y ↔ ((x 0 = 0 ↔ y 0 = 0) ∧ x 1 = y 1) := by
  by_cases hx : x 0 = 0 <;> by_cases hy : y 0 = 0 <;> simp [code, hx, hy]

private theorem code_eq_by_tag (x : TaggedCoordinates.Coord → K) (s : SortTag) (y : K) :
    code x = (match s with | .vf => Sum.inl y | .rv => Sum.inr y) ↔
      (match s with | .vf => x 0 = 0 | .rv => x 0 ≠ 0) ∧ x 1 = y := by
  cases s <;> by_cases hx : x 0 = 0 <;> simp [code, hx]

private def dictionaryRealizes : TaggedCoordinates.Realizes dictionary (K ⊕ K) K where
  code := code
  onto := code_onto
  equality := by
    intro v
    rw [code_ext]
    simp [dictionary, isZero, iff_iff_implies_and_implies]
  functionGraph := by
    intro n f v
    change (tag (Fn.resSort f) (.var (.inr 0)) ⊓
      ringOutput f (fun i => .var (.inl (i, 1))) (.var (.inr 1))).Realize v ↔ _
    rw [Formula.realize_inf, ringOutput_realize]
    change _ ↔ code (v ∘ Sum.inr) =
      (match Fn.resSort f with
      | .vf => .inl (fieldFn f (fun i => code (fun j => v (.inl (i,j)))))
      | .rv => .inr (fieldFn f (fun i => code (fun j => v (.inl (i,j))))))
    rw [code_eq_by_tag, fieldFn_code]
    cases Fn.resSort f <;> simp [tag, isZero]
  relationGraph := by
    intro n r v
    cases r with
    | memVF =>
      change _ ↔ inVF (code (fun j => v (0, j)))
      simp [dictionary, ringRelation, tag, isZero]
    | memRV =>
      change _ ↔ ¬inVF (code (fun j => v (0, j)))
      simp [dictionary, ringRelation, tag, isZero]
    | memUnits =>
      change _ ↔ ¬inVF (code (fun j => v (0, j))) ∧ value (code (fun j => v (0, j))) ≠ 0
      simp [dictionary, ringRelation, tag, isZero]
    | rvLe =>
      change _ ↔ ¬inVF (code (fun j => v (0, j))) ∧ ¬inVF (code (fun j => v (1, j))) ∧
        (value (code (fun j => v (0, j))) ≠ 0 ∨ value (code (fun j => v (1, j))) = 0)
      simp [dictionary, ringRelation, tag, isZero, and_assoc]

end SpecialTransformations.TrivialRV

/-! Appended to the field interpretation during development. -/

namespace SpecialTransformations.TrivialRV

local instance {K : Type} [Field K] : LRV.Structure (K ⊕ K) := interpret

private theorem sortEval_iff {K : Type} [Field K] (s : SortTag) (x : K ⊕ K) :
    sortEval s x ↔ (match s with | .vf => inVF x | .rv => ¬inVF x) := by
  cases s <;> rfl

private theorem realize_func {J K : Type} [Field K] {n : ℕ} (f : Fn n)
    (ts : Fin n → LRV.Term J) (w : J → K ⊕ K) :
    (Term.func f ts : LRV.Term J).realize w =
      (match Fn.resSort f with
      | .vf => .inl (fieldFn f (fun i => (ts i).realize w))
      | .rv => .inr (fieldFn f (fun i => (ts i).realize w))) := rfl

private def rvRingSymbol {n : ℕ} : Language.ring.Functions n → Fn n
  | .zero => .rvZero
  | .one => .rvOne
  | .add => .kAdd
  | .neg => .kNeg
  | .mul => .rvMul

private def rvRingTerm {I J : Type} (x : I → LRV.Term J) :
    Language.ring.Term I → LRV.Term J
  | .var i => x i
  | .func f a => .func (rvRingSymbol f) (fun i => rvRingTerm x (a i))

private theorem rvRingTerm_sorted {I α : Type} {n : ℕ} (sα : α → SortTag)
    (sn : Fin n → SortTag) (x : I → LRV.Term (α ⊕ Fin n))
    (hx : ∀ i, TmSort sα sn (x i) = some .rv) (t : Language.ring.Term I) :
    TmSort sα sn (rvRingTerm x t) = some .rv := by
  induction t with
  | var i => exact hx i
  | func f a ih =>
    cases f <;> simp [rvRingTerm, rvRingSymbol, TmSort, Fn.resSort, Fn.argSort, ih]

private theorem rvRingTerm_realize {I J K : Type} [Field K] [CompatibleRing K]
    (x : I → LRV.Term J) (v : I → K) (w : J → K ⊕ K)
    (hx : ∀ i, (x i).realize w = Sum.inr (v i)) (t : Language.ring.Term I) :
    (rvRingTerm x t).realize w = Sum.inr (t.realize v) := by
  induction t with
  | var i => exact hx i
  | func f a ih =>
    cases f <;> simp [rvRingTerm, rvRingSymbol, realize_func, Fn.resSort, fieldFn, value, ih] <;> rfl

private theorem reify_qf {I α : Type} {l n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (x : I ⊕ Fin l → LRV.Term (α ⊕ Fin n))
    (hx : ∀ i, TmSort sα sn (x i) = some .rv)
    (φ : Language.ring.BoundedFormula I l) (hφ : φ.IsQF) :
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧ WellSorted sα sn ψ ∧
      ∀ (K : Type) [Field K] [CompatibleRing K] (v : I → K) (a : Fin l → K)
        (w : α → K ⊕ K) (b : Fin n → K ⊕ K),
        (∀ i, (x i).realize (Sum.elim w b) = Sum.inr (Sum.elim v a i)) →
        (φ.Realize v a ↔ ψ.Realize w b) := by
  induction hφ with
  | falsum => exact ⟨⊥, .falsum, .falsum sn, by intros; rfl⟩
  | of_isAtomic h =>
    cases h with
    | equal t u =>
      refine ⟨.equal (rvRingTerm x t) (rvRingTerm x u), .of_isAtomic (.equal _ _),
        .equal sn (rvRingTerm_sorted sα sn x hx t) (rvRingTerm_sorted sα sn x hx u), ?_⟩
      intro K _ _ v a w b h
      simp [BoundedFormula.Realize, rvRingTerm_realize x (Sum.elim v a) (Sum.elim w b) h]
    | rel r _ => exact isEmptyElim r
  | imp _ _ ih₁ ih₂ =>
    obtain ⟨ψ₁, hq₁, hs₁, h₁⟩ := ih₁
    obtain ⟨ψ₂, hq₂, hs₂, h₂⟩ := ih₂
    refine ⟨ψ₁.imp ψ₂, hq₁.imp hq₂, .imp sn hs₁ hs₂, ?_⟩
    intro K _ _ v a w b h
    exact imp_congr (h₁ K v a w b h) (h₂ K v a w b h)

private def coordinateTerm {α : Type} {n : ℕ} (s : α ⊕ Fin n → SortTag)
    (i : (α ⊕ Fin n) × TaggedCoordinates.Coord) : LRV.Term (α ⊕ Fin n) :=
  if i.2 = 0 then
    match s i.1 with
    | .vf => .func Fn.rvZero Fin.elim0
    | .rv => .func Fn.rvOne Fin.elim0
  else
    match s i.1 with
    | .vf => .func Fn.rvMap (fun _ => .var i.1)
    | .rv => .var i.1

private theorem coordinateTerm_sorted {α : Type} {n : ℕ} (sα : α → SortTag) (sn : Fin n → SortTag)
    (i : (α ⊕ Fin n) × TaggedCoordinates.Coord) :
    TmSort sα sn (coordinateTerm (Sum.elim sα sn) i) = some .rv := by
  have hv : TmSort sα sn (.var i.1) = some (Sum.elim sα sn i.1) := by
    cases i.1 <;> rfl
  unfold coordinateTerm
  split
  · split <;> simp [TmSort, Fn.resSort, Fn.argSort]
  · split
    · rename_i he
      change (if (∀ j : Fin 1, TmSort sα sn (.var i.1) = some (Fn.argSort .rvMap j))
        then some (Fn.resSort .rvMap) else none) = _
      simp [hv, he, Fn.argSort, Fn.resSort]
    · rename_i he
      simpa only [he] using hv

private def coordinateValue {I K : Type} [Field K] (s : I → SortTag) (z : I → K ⊕ K)
    (i : I × TaggedCoordinates.Coord) : K :=
  if i.2 = 0 then
    match s i.1 with
    | .vf => 0
    | .rv => 1
  else value (z i.1)

private theorem coordinateValue_decode {I K : Type} [Field K] (s : I → SortTag)
    (z : I → K ⊕ K) (h : ∀ i, sortEval (s i) (z i)) :
    TaggedCoordinates.decode code (coordinateValue s z) = z := by
  funext i
  have hi := h i
  cases hs : s i <;> cases hz : z i <;>
    simp [TaggedCoordinates.decode, coordinateValue, code, hs, hz, value,
      sortEval_iff, inVF] at hi ⊢

private theorem coordinateTerm_realize {α K : Type} [Field K] {n : ℕ}
    (s : α ⊕ Fin n → SortTag) (z : α ⊕ Fin n → K ⊕ K)
    (h : ∀ i, sortEval (s i) (z i)) (i : (α ⊕ Fin n) × TaggedCoordinates.Coord) :
    (coordinateTerm s i).realize z = Sum.inr (coordinateValue s z i) := by
  have hi := h i.1
  by_cases hb : i.2 = 0 <;> cases hs : s i.1 <;> cases hz : z i.1 <;>
    simp [coordinateTerm, coordinateValue, hb, hs, hz, value,
      realize_func, Fn.resSort, fieldFn, sortEval_iff, inVF] at hi ⊢ <;> rfl

/-- Quantifier elimination for canonical trivially valued algebraically
closed fields in the corrected two-sorted RV language. -/
theorem canonical_trivial_rv_qe (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n) :
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧ WellSorted sα sn ψ ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (v : α → K ⊕ K) (a : Fin n → K ⊕ K),
        (∀ i, sortEval (sα i) (v i)) → (∀ i, sortEval (sn i) (a i)) →
        (φ.Realize v a ↔ ψ.Realize v a) := by
  let I := (α ⊕ Fin n) × TaggedCoordinates.Coord
  let s := Sum.elim sα sn
  let f : Language.ring.Formula I := TaggedCoordinates.bounded dictionary φ
  let x : I ⊕ Fin 0 → LRV.Term (α ⊕ Fin n) := Sum.elim (coordinateTerm s) Fin.elim0
  have hx : ∀ i, TmSort sα sn (x i) = some .rv := by
    rintro (i | i)
    · exact coordinateTerm_sorted sα sn i
    · exact i.elim0
  obtain ⟨g, hq, hfg⟩ := JohnsonACF.hasQEb I 0 f
  obtain ⟨ψ, hp, hws, hgψ⟩ := reify_qf sα sn x hx g hq
  refine ⟨ψ, hp, hws, ?_⟩
  intro K _ _ v a hv ha
  letI : CompatibleRing K := compatibleRingOfRing K
  let z := Sum.elim v a
  have hz : ∀ i, sortEval (s i) (z i) := by
    rintro (i | i)
    · exact hv i
    · exact ha i
  let w := coordinateValue s z
  have h₁ := TaggedCoordinates.bounded_realize dictionary
    (dictionaryRealizes (K := K)) φ w
  change f.Realize w ↔ φ.Realize (TaggedCoordinates.decode code w ∘ Sum.inl)
    (TaggedCoordinates.decode code w ∘ Sum.inr) at h₁
  rw [coordinateValue_decode s z hz] at h₁
  have h₂ : f.Realize w ↔ BoundedFormula.Realize g w default :=
    Theory.Iff.realize_bd_iff (M := K) hfg
  have h₃ := hgψ K w default v a (by
    rintro (i | i)
    · exact coordinateTerm_realize s z hz i
    · exact i.elim0)
  exact h₁.symm.trans (h₂.trans h₃)

end SpecialTransformations.TrivialRV

#check @SpecialTransformations.TrivialRV.canonical_trivial_rv_qe
#print axioms SpecialTransformations.TrivialRV.canonical_trivial_rv_qe
