module
public import Mathlib
@[expose] public section
/-!
# Quantifier elimination for algebraically closed valued fields

Author: Yimu Yin. The definitions below are extracted from the released
ACVF-QE source (478dd4bdd19c1fc1b75750b137f73d1eac5c4dfa), preserving their
names and values. The syntax support through the axioms is retained to preserve
generated auxiliary declarations. Unused later developments are omitted.
This independent statement imports only Mathlib.

The selected claims are pure ACF, ordinary nontrivial ACVF,
and nontrivial ACVF in the corrected two-sorted RV
language. No characteristic is fixed. The RV claim concerns well-sorted
formulas and assignments; RV inversion is named and VF inversion is unnamed.
No saturation or extra mathematical reference hypothesis is imposed.
Only the nontrivial valuation case is claimed for the valued-field results.
-/
open FirstOrder FirstOrder.Language
open FirstOrder FirstOrder.Language
namespace SpecialTransformations
namespace Milestone0
namespace Valued
open Valuation
variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀)
/-- `RV× = Kˣ / (1 + M)`, the multiplicative RV sort. -/ abbrev RVUnit : Type _ := Kˣ ⧸ v.valuationSubring.principalUnitGroup
/-- The `RV` sort: `RV = RV^× ∪ {rv 0}`. `none` is `rv 0`, the absorbing element — the paper's `∞`, which is also the residue field's zero `0`. -/ abbrev RV : Type _ := Option (RVUnit v)
/-- The paper's `RV₀ = RV ∪ {0}`. Since `0 = ∞ = rv 0` is already the element `none` of `RV`, `RV₀` is the same type; the alias is kept for the paper's notation. -/ abbrev RV0 : Type _ := RV v
/-- The quotient map `rv : K → RV`, with `rv 0 = 0` (the paper's `∞`). -/ noncomputable def rv (x : K) : RV v := by
  classical
  exact if h : x = 0 then none else some (QuotientGroup.mk (Units.mk0 x h))
end Valued
/-- The sorts of `L_RV`, as tags on the single carrier. -/ inductive SortTag where
  | vf
  | rv
  deriving DecidableEq, Repr
/-- Function symbols of `L_RV`, tagged by arity. -/ inductive Fn : ℕ → Type where
  /-- `0` of the ring language of the `VF` sort -/ | vfZero : Fn 0
  /-- `1` of the ring language of the `VF` sort -/ | vfOne : Fn 0
  /-- `+` of the ring language of the `VF` sort -/ | vfAdd : Fn 2
  /-- `-` of the ring language of the `VF` sort -/ | vfNeg : Fn 1
  /-- `×` of the ring language of the `VF` sort -/ | vfMul : Fn 2
  /-- `1` of the group language of the `RV` sort -/ | rvOne : Fn 0
  /-- the constant `0` of the `RV` sort: the residue field's zero, which is also `rv(0)` and the absorbing element of `RV`. The paper writes this element both as `0` and as `∞`; it is one element, so the language has one constant. -/ | rvZero : Fn 0
  /-- `×` of the `RV` sort -/ | rvMul : Fn 2
  /-- Multiplicative inverse on `RV`, totalized by `0⁻¹ = 0`. Naming this symbol is the author-approved correction to the inverse-free language specification before Convention 2.5, required for the intended QE result. It ensures that language substructures contain RV inverses. See LANGUAGE-ERRATA.md. -/ | rvInv : Fn 1
  /-- `+ : K² → K` of the `RV` sort -/ | kAdd : Fn 2
  /-- `- : K → K` of the `RV` sort -/ | kNeg : Fn 1
  /-- the projection `rv : VF → RV` -/ | rvMap : Fn 1
/-- Relation symbols of `L_RV`, tagged by arity. The first two are the sort predicates of the encoding (they are not part of the paper's signature); the last two are the paper's unary predicate `Kˣ` and its preorder `≤`. -/ inductive Rel : ℕ → Type where
  /-- encoding: the `VF` sort -/ | memVF : Rel 1
  /-- encoding: the `RV` sort -/ | memRV : Rel 1
  /-- the paper's unary predicate `Kˣ` -/ | memUnits : Rel 1
  /-- the paper's preorder `≤` on `RV` -/ | rvLe : Rel 2
/-- The corrected `L_RV`, with named RV inversion, in the tagged one-sorted encoding. -/ def LRV : Language := ⟨Fn, Rel⟩
namespace LRV
/-- Terms of `L_RV` whose (free) variables are indexed by `Fin n`. -/ abbrev Tm (n : ℕ) : Type := LRV.Term (Empty ⊕ Fin n)
/-- Bounded formulas of `L_RV` with `n` variables in scope and no free parameters. -/ abbrev Bf (n : ℕ) : Type := LRV.BoundedFormula Empty n
variable {n : ℕ}
/-- `0` of the `VF` sort -/ def tVFZero : Tm n := Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def tVFOne : Tm n := Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the `VF` sort -/ def tVFAdd (t u : Tm n) : Tm n := Term.func Fn.vfAdd ![t, u]
/-- `-` of the `VF` sort -/ def tVFNeg (t : Tm n) : Tm n := Term.func Fn.vfNeg ![t]
/-- `×` of the `VF` sort -/ def tVFMul (t u : Tm n) : Tm n := Term.func Fn.vfMul ![t, u]
/-- `1` of the `RV` sort -/ def tRVOne : Tm n := Term.func Fn.rvOne fun i => i.elim0
/-- `0` of the `RV` sort -/ def tRVZero : Tm n := Term.func Fn.rvZero fun i => i.elim0
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the paper's two symbols `0` and `∞` name one element. Kept as a definition so that the axioms can be read in the paper's notation. -/ def tRVInfty : Tm n := tRVZero
/-- `×` of the `RV` sort -/ def tRVMul (t u : Tm n) : Tm n := Term.func Fn.rvMul ![t, u]
/-- Multiplicative inverse on the `RV` sort, with `0⁻¹ = 0`. -/ def tRVInv (t : Tm n) : Tm n := Term.func Fn.rvInv ![t]
/-- `+ : K² → K` of the `RV` sort -/ def tKAdd (t u : Tm n) : Tm n := Term.func Fn.kAdd ![t, u]
/-- `- : K → K` of the `RV` sort -/ def tKNeg (t : Tm n) : Tm n := Term.func Fn.kNeg ![t]
/-- the projection `rv : VF → RV` -/ def tRv (t : Tm n) : Tm n := Term.func Fn.rvMap ![t]
/-- the bound variable of index `i < n` -/ def tv (i : ℕ) (h : i < n) : Tm n := Term.var (Sum.inr ⟨i, h⟩)
/-- the numeral `k · 1` of the `VF` sort -/ def tVFNumeral : ℕ → Tm n
  | 0 => tVFZero
  | k + 1 => tVFAdd (tVFNumeral k) tVFOne
/-- `t ^ k`, in the `VF` sort -/ def tVFPow (t : Tm n) : ℕ → Tm n
  | 0 => tVFOne
  | k + 1 => tVFMul (tVFPow t k) t
/-- `t ^ k`, in the `RV` sort -/ def tRVPow (t : Tm n) : ℕ → Tm n
  | 0 => tRVOne
  | k + 1 => tRVMul (tRVPow t k) t
/-- `t ∈ VF`, the encoding's sort predicate for the `VF` sort -/ def pVF (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV`, the encoding's sort predicate for the `RV` sort -/ def pRVsort (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` -/ def pUnits (t : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` -/ def pLe (t u : Tm n) : Bf n := FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` -/ def pEq (t u : Tm n) : Bf n := t =' u
/-- the paper's `RV = RV-sort ∖ {0}` -/ def pRV (t : Tm n) : Bf n := ∼(pEq t tRVZero)
/-- the paper's `RV-sort ∖ {∞}`. **Caution.** Since `∞ = rv(0) = 0`, this predicate is `RV ∖ {0}` — the multiplicative group `RV^×` — and *not* the residue field `K`: `K = K^× ∪ {0}` is `pInK`, which does contain the absorbing element. The name is kept only because the paper's own notation `RV ∖ {∞}` appears in its statements; `pK` is the same predicate as `pRV`. -/ def pK (t : Tm n) : Bf n := ∼(pEq t tRVInfty)
/-- the paper's `RV₀ = RV ∪ {0}`, i.e. the whole `RV` sort -/ def pRV0 (_t : Tm n) : Bf n := ⊤
/-- the strict order `t > 1` of the `RV` sort -/ def pGtOne (t : Tm n) : Bf n := pLe tRVOne t ⊓ ∼(pLe t tRVOne)
/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort. Not the same as `t ≠ 0`: when `Γ` is nontrivial the elements of `RV ∖ {0}` of value `≠ 1` are not in `K`, and the residue-field operations are junk there. Definition 2.1(d) defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`. The `0` here is `rv(0)`, the absorbing element of `RV`. -/ def pInK (t : Tm n) : Bf n := pUnits t ⊔ pEq t tRVZero
end LRV
namespace LRV
/-- the sort predicate of the sort `s`, as a formula -/ def sortPred (s : SortTag) (t : Tm n) : Bf n :=
  match s with
  | .vf => pVF t
  | .rv => pRVsort t
/-- `⋀ i, x_i ∈ s_i`, for the variables `x_i` of index `i` -/ def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k :=
  (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤
/-- the guarded universal sentence `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/ def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls (sortedHyps ss ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/ def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- `⋀ i < k, x_i ∈ K`: the tuple lies in `K = K^× ∪ {0}` -/ def kHyps {k : ℕ} : Bf k :=
  (List.finRange k).foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤
/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/ def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/ def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓
    pInK (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- the universal closure of a formula in a single variable -/ def allOne (φ : Bf 1) : LRV.Sentence := BoundedFormula.alls φ
/-- The result sort of a function symbol of `L_RV`. -/ def Fn.resSort : {l : ℕ} → Fn l → SortTag
  | _, .vfZero => .vf
  | _, .vfOne => .vf
  | _, .vfAdd => .vf
  | _, .vfNeg => .vf
  | _, .vfMul => .vf
  | _, .rvOne => .rv
  | _, .rvZero => .rv
  | _, .rvMul => .rv
  | _, .rvInv => .rv
  | _, .kAdd => .rv
  | _, .kNeg => .rv
  | _, .rvMap => .rv
/-- The sort of the `i`-th argument of a function symbol of `L_RV`. -/ def Fn.argSort : {l : ℕ} → (f : Fn l) → Fin l → SortTag
  | _, .vfZero => Fin.elim0
  | _, .vfOne => Fin.elim0
  | _, .vfAdd => fun _ => .vf
  | _, .vfNeg => fun _ => .vf
  | _, .vfMul => fun _ => .vf
  | _, .rvOne => Fin.elim0
  | _, .rvZero => Fin.elim0
  | _, .rvMul => fun _ => .rv
  | _, .rvInv => fun _ => .rv
  | _, .kAdd => fun _ => .rv
  | _, .kNeg => fun _ => .rv
  | _, .rvMap => fun _ => .vf
/-- The sort of the `i`-th argument of a relation symbol of `L_RV`. The two encoding predicates `memVF`, `memRV` are dealt with like the paper's own predicates: `memVF` needs its argument in `VF`, and `memRV`, `memUnits`, `rvLe` need their arguments in `RV`. -/ def Rel.argSort : {l : ℕ} → (R : Rel l) → Fin l → SortTag
  | _, .memVF => fun _ => .vf
  | _, .memRV => fun _ => .rv
  | _, .memUnits => fun _ => .rv
  | _, .rvLe => fun _ => .rv
/-- **The sort of a term**, if it has one. `none` is exactly the encoding's ill-sorted terms: `rv` applied to an `RV`-term, a `VF` operation at an `RV`-term, `kAdd` at a `VF`-term, and any term containing one of those. Parameters `a : α` carry the declared sort `sα a`, the bound variable of index `i` carries `sn i`. -/ def TmSort {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag) :
    LRV.Term (α ⊕ Fin n) → Option SortTag
  | Term.var (Sum.inl a) => some (sα a)
  | Term.var (Sum.inr i) => some (sn i)
  | Term.func f ts =>
    if (∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)) then some (Fn.resSort f) else none
/-- `t ∈ VF` with parameters `α` (`pVF` for `Bf n = LRV.BoundedFormula Empty n`). -/ def pVFG {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV` with parameters `α`. -/ def pRVG {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` with parameters `α`. -/ def pUnitsG {α : Type} {n : ℕ} (t : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` with parameters `α`. -/ def pLeG {α : Type} {n : ℕ} (t u : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` with parameters `α`. -/ def pEqG {α : Type} {n : ℕ} (t u : LRV.Term (α ⊕ Fin n)) : LRV.BoundedFormula α n :=
  t =' u
/-- the sort predicate of the sort `s` at a term, with parameters `α` -/ def sortPredG {α : Type} {n : ℕ} (s : SortTag) (t : LRV.Term (α ⊕ Fin n)) :
    LRV.BoundedFormula α n :=
  match s with
  | .vf => pVFG t
  | .rv => pRVG t
theorem sortPred_eq_sortPredG {n : ℕ} (s : SortTag) (t : Tm n) :
    sortPred s t = sortPredG (α := Empty) s t := rfl
theorem pVF_eq_pVFG {n : ℕ} (t : Tm n) : pVF t = pVFG (α := Empty) t := rfl
/-- The guard atom `xᵢ ∈ s`, for an arbitrary parameter type `α`. -/ def guardAtom {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) : LRV.BoundedFormula α n :=
  sortPredG s (Term.var (Sum.inr i))
/-- **`InAntecedent s i η`**: `η` is a formula in which the guard atom `xᵢ ∈ s` occurs as a *top-level conjunct*. `a ⊓ b` is `¬(a → ¬b)` in the encoding, so a formula that starts with `⊓` is an implication whose antecedent is an implication; the two `and` constructors descend through exactly that. Nothing weaker is admitted: the atom under a further negation or as the consequent of an implication does not count, which is the whole point (an atom there is *true* at junk elements, not false). The paper's own antecedents are right-nested `⊓` of sort atoms (`sortedHyps`), which is the shape this family decomposes. -/ inductive InAntecedent {α : Type} {n : ℕ} (s : SortTag) (i : Fin n) :
    LRV.BoundedFormula α n → Prop
  /-- the guard atom itself -/ | atom : InAntecedent s i (guardAtom s i)
  /-- a conjunct of the left half -/ | and_left {a b : LRV.BoundedFormula α n} :
      InAntecedent s i a → InAntecedent s i (a ⊓ b)
  /-- a conjunct of the right half -/ | and_right {a b : LRV.BoundedFormula α n} :
      InAntecedent s i b → InAntecedent s i (a ⊓ b)
/-- **`Occurs i s η`**: the atom "the variable of index `i` lies in the sort `s`" is one of the top-level conjuncts of `η`. Only conjunctions are decomposed (`a ⊓ b` is `¬(a → ¬b)` in the encoding), so an occurrence found by `Occurs` makes `η` *false* whenever the `i`-th element of the tuple is not in the sort `s`, whatever the rest of `η` says. Conjunctions are decomposed in the form the tree's `sortedHyps` and friends are written in, which is the point of the definition. `Occurs` **is** `InAntecedent` — a definition, not a compiled match. A compiled match cannot be unfolded at a constructor-headed argument whose subterms are variables, which is why the two had to be identified rather than bridged (see `Milestone0/DECISION.md`, the guard repair); the inductive form is the one the proofs can use. -/ def Occurs {α : Type} {m : ℕ} (i : Fin m) (s : SortTag) (φ : LRV.BoundedFormula α m) : Prop :=
  InAntecedent s i φ
/-- **The junk-truth condition on the body of a quantifier** (the author's ruling; `DECISION.md`). `GuardTrue s i χ` is the syntactic condition on `χ` that makes it true at elements outside the sort `s`: * `χ = η ⟹ ψ` with the guard among the top-level conjuncts of `η`: the antecedent is false off the sort, so `χ` is true there; * `χ = ∀ y, χ'` with `χ'` junk-true at the *same* variable (cast by `Fin.castSucc`): if the `i`-th element is junk then `χ'` holds at every value of `y`, so `∀ y, χ'` does too. The second clause is what makes the condition survive the iteration in `wellSorted_alls`, where the body of an inner quantifier is another quantifier. Since `WellSorted` has no model parameter the condition has to be syntactic, and this is the strongest shape that (a) excludes `(x ∈ s ⟹ ⊥) ⟹ ψ`, (b) admits `sortedHyps`-shaped antecedents, and (c) is preserved by the fragment's own quantifier. -/ inductive GuardTrue {α : Type} (s : SortTag) :
    {n : ℕ} → (i : Fin n) → LRV.BoundedFormula α n → Prop
  /-- the guard is a top-level conjunct of the antecedent -/ | imp {n : ℕ} {i : Fin n} {η ψ : LRV.BoundedFormula α n}
      (h : InAntecedent s i η) : GuardTrue s i (η ⟹ ψ)
  /-- a universal inherits junk-truth from its body -/ | all {n : ℕ} {i : Fin n} {χ : LRV.BoundedFormula α (n + 1)}
      (h : GuardTrue s (Fin.castSucc i) χ) : GuardTrue s i (.all χ)
/-- The `GuardTrue` obligation at an implication whose antecedent has the guard as a conjunct. -/ theorem GuardTrue.of_inAntecedent {α : Type} {m : ℕ} {i : Fin m} {s : SortTag}
    {η ψ : LRV.BoundedFormula α m} (h : InAntecedent s i η) :
    GuardTrue s i (η ⟹ ψ) :=
  GuardTrue.imp h
/-- Case analysis on a top-level conjunct: either it is the guard atom itself, or the formula is a conjunction with the atom in one of its halves. This is the elimination form of `InAntecedent` (the family is indexed, so a plain `cases` cannot abstract the formula). -/ theorem InAntecedent.shape {α : Type} {m : ℕ} {i : Fin m} {s : SortTag}
    {φ : LRV.BoundedFormula α m} (h : InAntecedent s i φ) :
    φ = guardAtom s i ∨ ∃ a b : LRV.BoundedFormula α m, φ = a ⊓ b := by
  induction h with
  | atom => exact Or.inl rfl
  | and_left _ _ => exact Or.inr ⟨_, _, rfl⟩
  | and_right _ _ => exact Or.inr ⟨_, _, rfl⟩
/-- **`GuardsLast s i χ`**: `χ` has the atom "the variable of index `i` lies in the sort `s`" as a conjunct of an antecedent, at its own level or under further quantifiers. This is the syntactic condition a guarded quantifier `∀ x ∈ s, ...` satisfies: descending under `all` keeps the indices of the earlier variables, so the index only needs to be cast by `Fin.castSucc`. -/ def GuardsLast {α : Type} (s : SortTag) :
    {m : ℕ} → (i : Fin m) → LRV.BoundedFormula α m → Prop
  | _, i, .imp η ψ => Occurs i s η ∨ GuardsLast s i η ∨ GuardsLast s i ψ
  | _, i, .all χ => GuardsLast s (Fin.castSucc i) χ
  | _, _, _ => False
/-- **`WellSorted sα sn φ`**: `φ` is a formula of the paper's two-sorted `L_RV`, with the free parameters `a : α` of sort `sα a` and the free variables of sort `sn`. * atoms: `t = u` only between terms of one sort, `t ∈ VF` only at a `VF`-term, and `t ∈ RV`, `t ∈ Kˣ`, `t ≤ u` only at `RV`-terms (this is `Rel.argSort`); * connectives are componentwise; * a quantifier is admitted only in guarded form: `∀ x, η → ψ` with `x` of sort `s` and `η` containing the conjunct `x ∈ s`. Ill-sorted terms therefore never occur, and the value of a well-sorted formula at a tuple of the declared sorts is a function of the paper's two-sorted structure alone; * **and the body of a quantifier is junk-true**: because `BoundedFormula.all` quantifies over the whole one-sorted carrier, not just the tag `s`, the body must hold at elements outside `s` too. That is the `GuardTrue` field, the author's ruling recorded in `Milestone0/DECISION.md`: the sort predicate of the bound variable is a *top-level conjunct* of the body's antecedent, so the antecedent is false — hence the body true — off the sort. `GuardsLast` alone does not imply it (`(x ∈ s ⟹ ⊥) ⟹ ψ` satisfies `GuardsLast` and is false at junk elements). -/ inductive WellSorted {α : Type} (sα : α → SortTag) :
    {n : ℕ} → (Fin n → SortTag) → LRV.BoundedFormula α n → Prop
  /-- `⊥` -/ | falsum {n : ℕ} (sn : Fin n → SortTag) : WellSorted sα sn .falsum
  /-- `t = u` between terms of one sort -/ | equal {n : ℕ} (sn : Fin n → SortTag) {t u : LRV.Term (α ⊕ Fin n)} {s : SortTag}
      (ht : TmSort sα sn t = some s) (hu : TmSort sα sn u = some s) :
      WellSorted sα sn (.equal t u)
  /-- a relation of `L_RV` applied to terms of its declared sorts -/ | rel {n l : ℕ} (sn : Fin n → SortTag) (R : Rel l) (ts : Fin l → LRV.Term (α ⊕ Fin n))
      (h : ∀ i, TmSort sα sn (ts i) = some (Rel.argSort R i)) :
      WellSorted sα sn (.rel R ts)
  /-- implication -/ | imp {n : ℕ} (sn : Fin n → SortTag) {a b : LRV.BoundedFormula α n} :
      WellSorted sα sn a → WellSorted sα sn b → WellSorted sα sn (.imp a b)
  /-- the guarded universal quantifier `∀ x ∈ s, ψ`, whose body is junk-true (`GuardTrue`) -/ | all {n : ℕ} (sn : Fin n → SortTag) {s : SortTag} {χ : LRV.BoundedFormula α (n + 1)}
      (hχ : WellSorted sα (Fin.snoc sn s) χ) (hg : GuardsLast s (Fin.last n) χ)
      (hj : GuardTrue s (Fin.last n) χ) :
      WellSorted sα sn (.all χ)
section TmSortLemmas
variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)
theorem tmSort_var_inl (a : α) : TmSort sα sn (Term.var (Sum.inl a)) = some (sα a) := rfl
theorem tmSort_var_inr (i : Fin n) : TmSort sα sn (Term.var (Sum.inr i)) = some (sn i) := rfl
/-- the sort of the bound variable `i` -/ theorem tmSort_tv (i : ℕ) (h : i < n) :
    TmSort sα sn (Term.var (Sum.inr (⟨i, h⟩ : Fin n))) = some (sn ⟨i, h⟩) := rfl
/-- the sort of an application of a function symbol -/ theorem tmSort_func_iff {l : ℕ} (f : Fn l) (ts : Fin l → LRV.Term (α ⊕ Fin n)) {s : SortTag} :
    TmSort sα sn (Term.func f ts) = some s ↔
      (∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)) ∧ Fn.resSort f = s := by
  simp only [TmSort]
  split_ifs with h
  · simp [h]
  · simp [h]
theorem tmSort_func {l : ℕ} (f : Fn l) (ts : Fin l → LRV.Term (α ⊕ Fin n))
    (h : ∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)) :
    TmSort sα sn (Term.func f ts) = some (Fn.resSort f) :=
  (tmSort_func_iff sα sn f ts).2 ⟨h, rfl⟩
theorem tmSort_vfZero :
    TmSort sα sn (Term.func Fn.vfZero (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .vf :=
  tmSort_func sα sn Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)
theorem tmSort_vfOne :
    TmSort sα sn (Term.func Fn.vfOne (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .vf :=
  tmSort_func sα sn Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)
theorem tmSort_rvOne :
    TmSort sα sn (Term.func Fn.rvOne (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .rv :=
  tmSort_func sα sn Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)
theorem tmSort_rvZero :
    TmSort sα sn (Term.func Fn.rvZero (fun i => i.elim0) : LRV.Term (α ⊕ Fin n)) = some .rv :=
  tmSort_func sα sn Fn.rvZero (fun i => i.elim0) (fun i => i.elim0)
theorem tmSort_bin_iff (f : Fn 2) {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func f ![t, u]) = some (Fn.resSort f) ↔
      TmSort sα sn t = some (Fn.argSort f 0) ∧ TmSort sα sn u = some (Fn.argSort f 1) := by
  rw [tmSort_func_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
theorem tmSort_un_iff (f : Fn 1) {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func f ![t]) = some (Fn.resSort f) ↔
      TmSort sα sn t = some (Fn.argSort f 0) := by
  rw [tmSort_func_iff, Fin.forall_fin_one]
  simp only [Matrix.cons_val_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
theorem tmSort_vfAdd {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.vfAdd ![t, u]) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfAdd
theorem tmSort_vfMul {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.vfMul ![t, u]) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfMul
theorem tmSort_rvMul {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.rvMul ![t, u]) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.rvMul
theorem tmSort_rvInv {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.rvInv ![t]) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.rvInv
theorem tmSort_kAdd {t u : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.kAdd ![t, u]) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.kAdd
theorem tmSort_vfNeg {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.vfNeg ![t]) = some .vf ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.vfNeg
theorem tmSort_kNeg {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.kNeg ![t]) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.kNeg
theorem tmSort_tRv {t : LRV.Term (α ⊕ Fin n)} :
    TmSort sα sn (Term.func Fn.rvMap ![t]) = some .rv ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.rvMap
/-- **The sort of a term does not change when the context is extended by a new variable.** This is what lets a formula be read under a quantifier that has just been added. -/ theorem tmSort_relabel_castSucc (s : SortTag) (t : LRV.Term (α ⊕ Fin n)) :
    TmSort sα (Fin.snoc sn s) (t.relabel (Sum.map id Fin.castSucc)) = TmSort sα sn t := by
  induction t with
  | var a =>
    rcases a with a | i
    · rfl
    · show TmSort sα (Fin.snoc sn s) (Term.var (Sum.inr (Fin.castSucc i))) = some (sn i)
      simp only [TmSort]
      rw [Fin.snoc_castSucc]
  | @func l f ts ih =>
    simp only [Term.relabel, TmSort]
    by_cases h : ∀ i, TmSort sα sn (ts i) = some (Fn.argSort f i)
    · have h' : ∀ i, TmSort sα (Fin.snoc sn s)
          ((ts i).relabel (Sum.map id Fin.castSucc)) = some (Fn.argSort f i) :=
        fun i => by rw [ih i]; exact h i
      rw [if_pos h', if_pos h]
    · have h' : ¬ ∀ i, TmSort sα (Fin.snoc sn s)
          ((ts i).relabel (Sum.map id Fin.castSucc)) = some (Fn.argSort f i) :=
        fun hc => h (fun i => by rw [← ih i]; exact hc i)
      rw [if_neg h', if_neg h]
end TmSortLemmas
section FormulaLemmas
variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)
/-- the conjunction of two well-sorted formulas is well-sorted -/ theorem wellSorted_inf {a b : LRV.BoundedFormula α n} (ha : WellSorted sα sn a)
    (hb : WellSorted sα sn b) : WellSorted sα sn (a ⊓ b) :=
  WellSorted.imp sn (WellSorted.imp sn ha (WellSorted.imp sn hb (WellSorted.falsum sn)))
    (WellSorted.falsum sn)
theorem wellSorted_top : WellSorted sα sn (⊤ : LRV.BoundedFormula α n) :=
  WellSorted.imp sn (WellSorted.falsum sn) (WellSorted.falsum sn)
/-- `t = u` between terms of one sort -/ theorem wellSorted_pEqG {t u : LRV.Term (α ⊕ Fin n)} {s : SortTag}
    (ht : TmSort sα sn t = some s) (hu : TmSort sα sn u = some s) :
    WellSorted sα sn (pEqG t u) :=
  WellSorted.equal sn ht hu
/-- `t ∈ VF` at a `VF`-term -/ theorem rel_argSort_memVF : Rel.argSort (Rel.memVF) = fun _ => .vf := rfl
theorem rel_argSort_memRV : Rel.argSort (Rel.memRV) = fun _ => .rv := rfl
theorem rel_argSort_memUnits : Rel.argSort (Rel.memUnits) = fun _ => .rv := rfl
theorem rel_argSort_rvLe : Rel.argSort (Rel.rvLe) = fun _ => .rv := rfl
theorem wellSorted_pVFG {t : LRV.Term (α ⊕ Fin n)} (h : TmSort sα sn t = some .vf) :
    WellSorted sα sn (pVFG t) :=
  WellSorted.rel sn Rel.memVF ![t]
    (fun i => by rw [rel_argSort_memVF]; fin_cases i; simpa using h)
/-- `t ∈ RV` at an `RV`-term -/ theorem wellSorted_pRVG {t : LRV.Term (α ⊕ Fin n)} (h : TmSort sα sn t = some .rv) :
    WellSorted sα sn (pRVG t) :=
  WellSorted.rel sn Rel.memRV ![t]
    (fun i => by rw [rel_argSort_memRV]; fin_cases i; simpa using h)
/-- `t ∈ Kˣ` at an `RV`-term -/ theorem wellSorted_pUnitsG {t : LRV.Term (α ⊕ Fin n)} (h : TmSort sα sn t = some .rv) :
    WellSorted sα sn (pUnitsG t) :=
  WellSorted.rel sn Rel.memUnits ![t]
    (fun i => by rw [rel_argSort_memUnits]; fin_cases i; simpa using h)
/-- `t ≤ u` at `RV`-terms -/ theorem wellSorted_pLeG {t u : LRV.Term (α ⊕ Fin n)}
    (ht : TmSort sα sn t = some .rv) (hu : TmSort sα sn u = some .rv) :
    WellSorted sα sn (pLeG t u) :=
  WellSorted.rel sn Rel.rvLe ![t, u] (fun i => by
    rw [rel_argSort_rvLe]
    fin_cases i
    · simpa using ht
    · simpa using hu)
/-- the sort predicate of the sort of a term of that sort -/ theorem wellSorted_sortPredG {s : SortTag} {t : LRV.Term (α ⊕ Fin n)}
    (h : TmSort sα sn t = some s) : WellSorted sα sn (sortPredG s t) := by
  cases s with
  | vf => exact wellSorted_pVFG sα sn h
  | rv => exact wellSorted_pRVG sα sn h
theorem Occurs.of_conj_left {m : ℕ} (i : Fin m) {s : SortTag} {a b : LRV.BoundedFormula α m}
    (h : Occurs i s a) : Occurs i s (a ⊓ b) := InAntecedent.and_left h
theorem Occurs.of_conj_right {m : ℕ} (i : Fin m) {s : SortTag} {a b : LRV.BoundedFormula α m}
    (h : Occurs i s b) : Occurs i s (a ⊓ b) := InAntecedent.and_right h
/-- an occurrence in an antecedent guards the implication -/ theorem GuardsLast.of_occurs {m : ℕ} (i : Fin m) {s : SortTag} {η ψ : LRV.BoundedFormula α m}
    (h : Occurs i s η) : GuardsLast s i (η ⟹ ψ) := Or.inl h
/-- the atom `x_i ∈ s` occurs in `sortPred s (x_i)` -/ theorem occurs_self (α : Type) {m : ℕ} (i : Fin m) (s : SortTag) :
    @Occurs α m i s (sortPredG s (Term.var (Sum.inr i))) :=
  InAntecedent.atom
/-- **The guarded universal quantifier**: `∀ x ∈ s, (η → ψ)` is well-sorted when `ψ` and `η` are well-sorted in the extended context and `η` contains the conjunct `x ∈ s`. -/ theorem wellSorted_all_guarded {m : ℕ} {sn : Fin m → SortTag} {s : SortTag}
    {η ψ : LRV.BoundedFormula α (m + 1)}
    (hη : WellSorted sα (Fin.snoc sn s) η) (hψ : WellSorted sα (Fin.snoc sn s) ψ)
    (hg : Occurs (Fin.last m) s η) :
    WellSorted sα sn (.all (η ⟹ ψ)) :=
  WellSorted.all sn (WellSorted.imp _ hη hψ) (Or.inl hg)
    (GuardTrue.of_inAntecedent hg)
/-- **The guarded existential quantifier** `∃ x ∈ s, ψ`. (The encoding writes it as `¬∀ x, ¬(x ∈ s ∧ ψ)`.) -/ def exSortedG {α : Type} {k : ℕ} (s : SortTag) (ψ : LRV.BoundedFormula α (k + 1)) :
    LRV.BoundedFormula α k :=
  BoundedFormula.ex (sortPredG s (Term.var (Sum.inr (Fin.last k))) ⊓ ψ)
theorem wellSorted_exSortedG {m : ℕ} {sn : Fin m → SortTag} {s : SortTag}
    {ψ : LRV.BoundedFormula α (m + 1)} (h : WellSorted sα (Fin.snoc sn s) ψ) :
    WellSorted sα sn (exSortedG s ψ) := by
  have hpred : WellSorted sα (Fin.snoc sn s)
      (sortPredG s (Term.var (Sum.inr (Fin.last m)))) :=
    wellSorted_sortPredG sα _ (by rw [tmSort_var_inr, Fin.snoc_last])
  refine WellSorted.imp sn (WellSorted.all sn
    (WellSorted.imp _ (wellSorted_inf sα _ hpred h) (WellSorted.falsum _))
    (Or.inl (InAntecedent.and_left (occurs_self α (Fin.last m) s)))
    (GuardTrue.of_inAntecedent (InAntecedent.and_left (α := α) InAntecedent.atom)))
    (WellSorted.falsum sn)
/-- **The `VF`-guarded universal quantifier** `∀ x ∈ VF, ψ` — the quantifier shape of `RVElim.VFQ` (`allVF`) — is well-sorted when `ψ` is. -/ theorem wellSorted_all_pVF {m : ℕ} {sn : Fin m → SortTag} {ψ : Bf (m + 1)} {sα : Empty → SortTag}
    (h : WellSorted sα (Fin.snoc sn .vf) ψ) :
    WellSorted sα sn (BoundedFormula.all (pVF (tv m (Nat.lt_succ_self m)) ⟹ ψ)) :=
  wellSorted_all_guarded sα
    (η := pVF (tv m (Nat.lt_succ_self m)))
    (by
      have h' : TmSort sα (Fin.snoc sn .vf) (tv m (Nat.lt_succ_self m)) = some .vf := by
        show TmSort sα (Fin.snoc sn .vf) (Term.var (Sum.inr (Fin.last m))) = some .vf
        rw [tmSort_var_inr, Fin.snoc_last]
      exact wellSorted_pVFG sα _ h')
    h
    (occurs_self Empty (Fin.last m) .vf)
end FormulaLemmas
section SortedHyps
variable (sα : Empty → SortTag)
theorem wellSorted_foldr_hyps {k : ℕ} (ss : Fin k → SortTag) (l : List (Fin k)) :
    ∀ (acc : Bf k), WellSorted sα ss acc →
      WellSorted sα ss (l.foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc h
    simp only [List.foldr_cons]
    exact wellSorted_inf sα ss (wellSorted_sortPredG sα ss (tmSort_var_inr sα ss i)) (ih acc h)
/-- **`sortedHyps ss` is well-sorted** in the context whose sorts are `ss`. -/ theorem wellSorted_sortedHyps {k : ℕ} (ss : Fin k → SortTag) :
    WellSorted sα ss (sortedHyps ss) :=
  wellSorted_foldr_hyps sα ss (List.finRange k) ⊤ (wellSorted_top sα ss)
end SortedHyps
section OccursHyps
/-- In `sortedHyps ss` the atom `x_i ∈ ss i` occurs as a conjunct. -/ theorem occurs_foldr_hyps {k : ℕ} (ss : Fin k → SortTag) :
    ∀ (l : List (Fin k)) (acc : Bf k) (i : Fin k), i ∈ l →
      Occurs i (ss i) (l.foldr (fun j acc => sortPred (ss j) (tv j.val j.isLt) ⊓ acc) acc)
  | [], _, i, hi => by simp at hi
  | j :: l, acc, i, hi => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact Occurs.of_conj_left i (occurs_self Empty i (ss i))
    · exact InAntecedent.and_right (occurs_foldr_hyps ss l acc i hi')
theorem occurs_sortedHyps {k : ℕ} (ss : Fin k → SortTag) (i : Fin k) :
    Occurs i (ss i) (sortedHyps ss) :=
  occurs_foldr_hyps ss (List.finRange k) ⊤ i (List.mem_finRange i)
end OccursHyps
section Alls
/-- `Fin.snoc` of the restriction to `Fin.castSucc` and the last value is the whole tuple. -/ theorem fin_snoc_castSucc_last {k : ℕ} (ss : Fin (k + 1) → SortTag) :
    Fin.snoc (fun i : Fin k => ss (Fin.castSucc i)) (ss (Fin.last k)) = ss := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro j
    rw [Fin.snoc_castSucc]
/-- **The iterated guarded quantifier.** If `χ` is well-sorted in the context `ss`, and every variable of that context occurs as a guard `x_i ∈ ss i` in a conjunct of an antecedent of `χ`, then `∀ x_0 … ∀ x_{k-1}, χ` is well-sorted. (`BoundedFormula.alls` binds the variables in this order, so the guard for the `d`-th binder is the occurrence at index `d`.) -/ theorem wellSorted_alls {k : ℕ} {sα : Empty → SortTag} {χ : Bf k} {ss : Fin k → SortTag}
    (h : WellSorted sα ss χ) (hg : ∀ d : Fin k, GuardsLast (ss d) d χ)
    (hj : ∀ d : Fin k, GuardTrue (ss d) d χ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (BoundedFormula.alls χ) := by
  induction k with
  | zero =>
    have hss : ss = fun i : Fin 0 => i.elim0 := funext (fun i => i.elim0)
    rwa [hss] at h
  | succ k ih =>
    show WellSorted sα (fun i : Fin 0 => i.elim0) (BoundedFormula.alls (BoundedFormula.all χ))
    refine ih (ss := fun d : Fin k => ss (Fin.castSucc d)) ?_ ?_ ?_
    · refine WellSorted.all _ ?_ (hg (Fin.last k)) (hj (Fin.last k))
      rw [fin_snoc_castSucc_last ss]
      exact h
    · intro d
      exact hg (Fin.castSucc d)
    · intro d
      exact GuardTrue.all (hj (Fin.castSucc d))
/-- **The guarded universal sentence `allSorted ss φ` is well-sorted.** -/ theorem wellSorted_allSorted {k : ℕ} {sα : Empty → SortTag} (ss : Fin k → SortTag) {φ : Bf k}
    (hφ : WellSorted sα ss φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allSorted ss φ) :=
  wellSorted_alls (WellSorted.imp ss (wellSorted_sortedHyps sα ss) hφ)
    (fun d => Or.inl (occurs_sortedHyps ss d))
    (fun d => GuardTrue.of_inAntecedent (occurs_sortedHyps ss d))
/-- `pInK t` is well-sorted at an `RV`-term. -/ theorem wellSorted_pInK {n : ℕ} {sα : Empty → SortTag} {sn : Fin n → SortTag}
    {t : Tm n} (h : TmSort sα sn t = some .rv) : WellSorted sα sn (pInK t) :=
  WellSorted.imp sn (WellSorted.imp sn (wellSorted_pUnitsG sα sn h) (WellSorted.falsum sn))
    (wellSorted_pEqG sα sn h (tmSort_rvZero sα sn))
theorem wellSorted_foldr_kHyps {k : ℕ} (sα : Empty → SortTag) (l : List (Fin k)) :
    ∀ (acc : Bf k), WellSorted sα (fun _ => .rv) acc →
      WellSorted sα (fun _ => .rv)
        (l.foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc h
    simp only [List.foldr_cons]
    exact wellSorted_inf sα _ (wellSorted_pInK (tmSort_var_inr sα (fun _ => .rv) i)) (ih acc h)
theorem wellSorted_kHyps {k : ℕ} (sα : Empty → SortTag) :
    WellSorted sα (fun _ : Fin k => .rv) (kHyps : Bf k) :=
  wellSorted_foldr_kHyps (k := k) sα (List.finRange k) ⊤ (wellSorted_top sα _)
/-- **The guarded universal sentence `allSortedK ss φ` is well-sorted**, in the contexts where it is used (`ss` constantly `RV`; `kHyps` constrains `RV`-variables only). -/ theorem wellSorted_allSortedK {k : ℕ} {sα : Empty → SortTag} {φ : Bf k}
    (hφ : WellSorted sα (fun _ => .rv) φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allSortedK (fun _ => .rv) φ) :=
  wellSorted_alls
    (WellSorted.imp _ (wellSorted_inf sα _ (wellSorted_sortedHyps sα _)
      (wellSorted_kHyps sα)) hφ)
    (fun d => Or.inl (InAntecedent.and_left (occurs_sortedHyps (fun _ => .rv) d)))
    (fun d => GuardTrue.of_inAntecedent
      (InAntecedent.and_left (occurs_sortedHyps (fun _ => .rv) d)))
/-- **The universal closure of a guarded formula in one variable is well-sorted.** -/ theorem wellSorted_allOne {sα : Empty → SortTag} {s : SortTag} {φ : Bf 1}
    (hφ : WellSorted sα (fun _ => s) φ) (hg : GuardsLast s 0 φ)
    (hj : GuardTrue s 0 φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allOne φ) :=
  wellSorted_alls (ss := fun _ => s) hφ (fun d => by
    have : d = 0 := by ext; omega
    rw [this]
    exact hg) (fun d => by
    have : d = 0 := by ext; omega
    rw [this]
    exact hj)
end Alls
section Connectives
variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag)
/-- the negation of a well-sorted formula is well-sorted -/ theorem wellSorted_not {a : LRV.BoundedFormula α n} (h : WellSorted sα sn a) :
    WellSorted sα sn (∼a) :=
  WellSorted.imp sn h (WellSorted.falsum sn)
/-- the disjunction of two well-sorted formulas is well-sorted (`a ⊔ b` is `∼a ⟹ b`) -/ theorem wellSorted_sup {a b : LRV.BoundedFormula α n} (ha : WellSorted sα sn a)
    (hb : WellSorted sα sn b) : WellSorted sα sn (a ⊔ b) :=
  WellSorted.imp sn (wellSorted_not sα sn ha) hb
/-- the biconditional of two well-sorted formulas is well-sorted -/ theorem wellSorted_iff {a b : LRV.BoundedFormula α n} (ha : WellSorted sα sn a)
    (hb : WellSorted sα sn b) : WellSorted sα sn (a ⇔ b) :=
  wellSorted_inf sα sn (WellSorted.imp sn ha hb) (WellSorted.imp sn hb ha)
/-- a double negation -/ theorem wellSorted_not_not {a : LRV.BoundedFormula α n} (h : WellSorted sα sn a) :
    WellSorted sα sn (∼∼a) :=
  wellSorted_not sα sn (wellSorted_not sα sn h)
/-- **`∃ x ∈ s, φ` with an arbitrary guard**: if `η` is well-sorted, `ψ` is well-sorted and the atom `x ∈ s` occurs in a conjunct of `η`, then `∃ x, η ∧ ψ` is well-sorted. (`BoundedFormula.ex ψ` is `¬∀x, ¬ψ` in the encoding.) This generalises m5's `wellSorted_exSortedG`, and is what `exSortedK` needs: its guard is the *conjunction* `x ∈ RV ∧ x ∈ K`, not the single sort predicate. -/ theorem wellSorted_ex_guarded {m : ℕ} {sn : Fin m → SortTag} {s : SortTag}
    {η ψ : LRV.BoundedFormula α (m + 1)}
    (hη : WellSorted sα (Fin.snoc sn s) η) (hψ : WellSorted sα (Fin.snoc sn s) ψ)
    (hg : Occurs (Fin.last m) s η) :
    WellSorted sα sn (BoundedFormula.ex (η ⊓ ψ)) :=
  WellSorted.imp sn (WellSorted.all sn
    (WellSorted.imp _ (wellSorted_inf sα _ hη hψ) (WellSorted.falsum _))
    (Or.inl (InAntecedent.and_left hg))
    (GuardTrue.of_inAntecedent (InAntecedent.and_left (α := α) hg)))
    (WellSorted.falsum sn)
end Connectives
section Variables
variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag)
/-- the bound variable `i` has the sort `sn i` (the constructor form of m5's `tmSort_tv`) -/ @[simp] theorem tmSort_tv' (i : ℕ) (h : i < n) : TmSort sα sn (tv i h) = some (sn ⟨i, h⟩) :=
  tmSort_var_inr sα sn ⟨i, h⟩
/-- the last variable of the context `Fin.snoc ss .rv` is an `RV`-variable -/ @[simp] theorem tmSort_tv_last {k : ℕ} {ss : Fin k → SortTag} :
    TmSort sα (Fin.snoc ss .rv) (tv k (Nat.lt_succ_self k)) = some .rv := by
  rw [tmSort_tv']
  have h : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k := by ext; rfl
  rw [h, Fin.snoc_last]
end Variables
section Existentials
variable (sα : Empty → SortTag)
/-- the encoding's `∃ x ∈ s, φ` (Part 2) is well-sorted at a well-sorted body: it is m5's `exSortedG`, the two are the same formula. -/ theorem wellSorted_exSorted {k : ℕ} {ss : Fin k → SortTag} {s : SortTag} {φ : Bf (k + 1)}
    (h : WellSorted sα (Fin.snoc ss s) φ) : WellSorted sα ss (exSorted s φ) :=
  wellSorted_exSortedG sα h
/-- the encoding's `∃ x ∈ s ∩ K, φ` (Part 2) is well-sorted at a well-sorted body; `pInK` is well-sorted at an `RV`-term, and `exSortedK` is only used at `s = .rv`. -/ theorem wellSorted_exSortedK {k : ℕ} {ss : Fin k → SortTag} {φ : Bf (k + 1)}
    (h : WellSorted sα (Fin.snoc ss .rv) φ) : WellSorted sα ss (exSortedK .rv φ) :=
  wellSorted_ex_guarded sα
    (η := sortPred .rv (tv k (Nat.lt_succ_self k)) ⊓ pInK (tv k (Nat.lt_succ_self k)))
    (wellSorted_inf sα _
      (wellSorted_pRVG sα _ (t := tv k (Nat.lt_succ_self k)) (tmSort_tv_last sα))
      (wellSorted_pInK (t := tv k (Nat.lt_succ_self k)) (tmSort_tv_last sα)))
    h
    (InAntecedent.and_left (occurs_self Empty (Fin.last k) .rv))
/-- `exSortedK` at a context of `RV`-variables: the shape of `acfSchemeK`'s body -/ theorem wellSorted_exSortedK_k {k : ℕ} {φ : Bf (k + 1)}
    (h : WellSorted sα (fun _ : Fin (k + 1) => .rv) φ) :
    WellSorted sα (fun _ : Fin k => .rv) (exSortedK .rv φ) :=
  wellSorted_exSortedK sα (by
    simpa using (fin_snoc_castSucc_last (ss := fun _ : Fin (k + 1) => .rv) ▸ h))
end Existentials
section SortedHypsGeneric
variable (sα : Empty → SortTag)
/-- `kHyps` is well-sorted at **any** context of `RV`-variables, not only at the constant one (m5's `wellSorted_kHyps` is the case `ss ≡ .rv`; the axioms of `Axioms.kField` are written with `![.rv, …]`, which is not definitionally the constant assignment). -/ theorem wellSorted_foldr_kHyps_ss {k : ℕ} {ss : Fin k → SortTag} (hss : ∀ i, ss i = .rv)
    (l : List (Fin k)) :
    ∀ (acc : Bf k), WellSorted sα ss acc →
      WellSorted sα ss (l.foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) acc) := by
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc h
    simp only [List.foldr_cons]
    exact wellSorted_inf sα ss (wellSorted_pInK (by rw [tmSort_tv', hss i])) (ih acc h)
/-- `kHyps` is well-sorted at a context of `RV`-variables -/ theorem wellSorted_kHyps_ss {k : ℕ} {ss : Fin k → SortTag} (hss : ∀ i, ss i = .rv) :
    WellSorted sα ss (kHyps : Bf k) :=
  wellSorted_foldr_kHyps_ss sα hss (List.finRange k) ⊤ (wellSorted_top sα ss)
/-- **`allSortedK ss φ` is well-sorted** for any assignment `ss` of `RV`-variables (m5's `wellSorted_allSortedK` is the case `ss ≡ .rv`). -/ theorem wellSorted_allSortedK_ss {k : ℕ} {ss : Fin k → SortTag} {φ : Bf k}
    (hss : ∀ i, ss i = .rv) (hφ : WellSorted sα ss φ) :
    WellSorted sα (fun i : Fin 0 => i.elim0) (allSortedK ss φ) := by
  refine wellSorted_alls (WellSorted.imp ss ?_ hφ) ?_ ?_
  · exact wellSorted_inf sα ss (wellSorted_sortedHyps sα ss)
      (wellSorted_kHyps_ss sα hss)
  · intro d
    exact Or.inl (InAntecedent.and_left (occurs_sortedHyps ss d))
  · intro d
    exact GuardTrue.of_inAntecedent (InAntecedent.and_left (occurs_sortedHyps ss d))
end SortedHypsGeneric
section TmSortConstructors
attribute [simp] tmSort_var_inr
variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag)
@[simp] theorem tmSort_tVFZero : TmSort sα sn (tVFZero (n := n)) = some .vf :=
  tmSort_func sα sn Fn.vfZero (fun i => i.elim0) (fun i => i.elim0)
@[simp] theorem tmSort_tVFOne : TmSort sα sn (tVFOne (n := n)) = some .vf :=
  tmSort_func sα sn Fn.vfOne (fun i => i.elim0) (fun i => i.elim0)
@[simp] theorem tmSort_tRVZero : TmSort sα sn (tRVZero (n := n)) = some .rv :=
  tmSort_func sα sn Fn.rvZero (fun i => i.elim0) (fun i => i.elim0)
@[simp] theorem tmSort_tRVOne : TmSort sα sn (tRVOne (n := n)) = some .rv :=
  tmSort_func sα sn Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)
@[simp] theorem tmSort_tRVInfty : TmSort sα sn (tRVInfty (n := n)) = some .rv :=
  tmSort_tRVZero sα sn
@[simp] theorem tmSort_tVFAdd {t u : Tm n} :
    TmSort sα sn (tVFAdd t u) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfAdd
@[simp] theorem tmSort_tVFMul {t u : Tm n} :
    TmSort sα sn (tVFMul t u) = some .vf ↔
      TmSort sα sn t = some .vf ∧ TmSort sα sn u = some .vf :=
  tmSort_bin_iff sα sn Fn.vfMul
@[simp] theorem tmSort_tVFNeg {t : Tm n} :
    TmSort sα sn (tVFNeg t) = some .vf ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.vfNeg
@[simp] theorem tmSort_tRVMul {t u : Tm n} :
    TmSort sα sn (tRVMul t u) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.rvMul
@[simp] theorem tmSort_tRVInv {t : Tm n} :
    TmSort sα sn (tRVInv t) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.rvInv
@[simp] theorem tmSort_tKAdd {t u : Tm n} :
    TmSort sα sn (tKAdd t u) = some .rv ↔
      TmSort sα sn t = some .rv ∧ TmSort sα sn u = some .rv :=
  tmSort_bin_iff sα sn Fn.kAdd
@[simp] theorem tmSort_tKNeg {t : Tm n} :
    TmSort sα sn (tKNeg t) = some .rv ↔ TmSort sα sn t = some .rv :=
  tmSort_un_iff sα sn Fn.kNeg
/-- the constructor form of m5's `tmSort_tRv` (the prime avoids the clash with it) -/ @[simp] theorem tmSort_tRv' {t : Tm n} :
    TmSort sα sn (tRv t) = some .rv ↔ TmSort sα sn t = some .vf :=
  tmSort_un_iff sα sn Fn.rvMap
end TmSortConstructors
/-- `pRV t = ∼(t = 0)` is well-sorted at an `RV`-term (m5's `wellSorted_pRV` is the same statement with the symbol `pRV`; it is re-stated here because the audit is at `α = Empty` and uses the `[simp]` facts above). -/ theorem wellSorted_pRV' {n : ℕ} {sα : Empty → SortTag} {sn : Fin n → SortTag} {t : Tm n}
    (h : TmSort sα sn t = some .rv) : WellSorted sα sn (pRV t) :=
  wellSorted_not sα sn (wellSorted_pEqG (s := .rv) sα sn h (tmSort_tRVZero sα sn))
section Powers
variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag)
@[simp] theorem tmSort_tVFPow {t : Tm n} (h : TmSort sα sn t = some .vf) :
    ∀ k : ℕ, TmSort sα sn (tVFPow t k) = some .vf
  | 0 => tmSort_tVFOne sα sn
  | k + 1 => by
    rw [tVFPow, tmSort_tVFMul]
    exact ⟨tmSort_tVFPow h k, h⟩
@[simp] theorem tmSort_tRVPow {t : Tm n} (h : TmSort sα sn t = some .rv) :
    ∀ k : ℕ, TmSort sα sn (tRVPow t k) = some .rv
  | 0 => tmSort_tRVOne sα sn
  | k + 1 => by
    rw [tRVPow, tmSort_tRVMul]
    exact ⟨tmSort_tRVPow h k, h⟩
@[simp] theorem tmSort_tVFNumeral : ∀ k : ℕ, TmSort sα sn (tVFNumeral (n := n) k) = some .vf
  | 0 => tmSort_tVFZero sα sn
  | k + 1 => by
    rw [tVFNumeral, tmSort_tVFAdd]
    exact ⟨tmSort_tVFNumeral k, tmSort_tVFOne sα sn⟩
end Powers
/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k` whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`. The leading term is `x ^ k`, so `acfScheme` quantifies over *all* monic polynomials of degree `k`. (An earlier version started the Horner fold at `x` instead of at `x + a_{k-1}`, which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a monic polynomial of degree `k+1` with zero `x^k` coefficient, so the scheme covered only a proper subclass and did not give algebraic closedness.) For `k = 0` the value is immaterial: `acfScheme` is only used with `1 ≤ k`. -/ def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) :=
  match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (n + 1) =>
    let x : Tm (n + 1 + 1) := tv (n + 1) (Nat.lt_succ_self (n + 1))
    (List.finRange n).reverse.foldl
      (fun acc i => add (mul acc x) (tv i.val (Nat.lt_trans i.isLt (Nat.lt.step (Nat.lt_succ_self n)))))
      (add x (tv n (Nat.lt.step (Nat.lt_succ_self n))))
/-- Sanity check on the Horner form: at `k = 1` it is the monic linear `x + a₀`. -/ theorem hornerPoly_one :
    hornerPoly (k := 1) tKAdd tRVMul = tKAdd (tv 1 Nat.one_lt_two) (tv 0 Nat.zero_lt_two) := rfl
/-- Sanity check on the Horner form: at `k = 2` it is the monic quadratic `x² + a₁x + a₀` (the `x²` coefficient is `1`, not `0`). -/ theorem hornerPoly_two :
    hornerPoly (k := 2) tKAdd tRVMul =
      tKAdd (tRVMul (tKAdd (tv 2 (Nat.lt_succ_self 2)) (tv 1 (Nat.one_lt_succ_succ 1)))
        (tv 2 (Nat.lt_succ_self 2))) (tv 0 (Nat.zero_lt_succ 2)) := rfl
end LRV
namespace Axioms
open LRV
/-- The sentences of a finite list, as a theory. -/ def ofList (l : List LRV.Sentence) : LRV.Theory := {s | s ∈ l}
/-- the carrier is covered by the two sorts -/ def sdCover : LRV.Sentence := allOne (pVF &0 ⊔ pRVsort &0)
/-- the two sorts are disjoint -/ def sdDisjoint : LRV.Sentence := allOne (∼(pVF &0 ⊓ pRVsort &0))
/-- `0` of the ring language lies in the `VF` sort -/ def sdVFZero : LRV.Sentence := pVF tVFZero
/-- `1` of the ring language lies in the `VF` sort -/ def sdVFOne : LRV.Sentence := pVF tVFOne
/-- the `VF` sort is closed under `+` -/ def sdVFAdd : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFAdd &0 &1))
/-- the `VF` sort is closed under `-` -/ def sdVFNeg : LRV.Sentence := allSorted ![.vf] (pVF (tVFNeg &0))
/-- the `VF` sort is closed under `×` -/ def sdVFMul : LRV.Sentence := allSorted ![.vf, .vf] (pVF (tVFMul &0 &1))
/-- `rv` maps the `VF` sort into the `RV` sort -/ def sdRv : LRV.Sentence := allSorted ![.vf] (pRVsort (tRv &0))
/-- `0` of the `RV` sort lies in the `RV` sort -/ def sdRVZero : LRV.Sentence := pRVsort tRVZero
/-- `∞` lies in the `RV` sort -/ def sdRVInfty : LRV.Sentence := pRVsort tRVInfty
/-- `1` of the `RV` sort lies in the `RV` sort -/ def sdRVOne : LRV.Sentence := pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/ def sdRVMul : LRV.Sentence := allSorted ![.rv, .rv] (pRVsort (tRVMul &0 &1))
def sdRVInv : LRV.Sentence := allSorted ![.rv] (pRVsort (tRVInv &0))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort. Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a *proper* subgroup of the multiplicative group `RV ∖ {0}` whenever `Γ` is nontrivial. Identifying `Kˣ` with all of `RV ∖ {0}` puts every `x ≠ 0` in the class of `1`, hence `1 ≤ x ≤ 1`, hence makes the preorder trivial and `Γ` trivial — contradicting the paper's standing hypothesis that `Γ(S)` is nontrivial. -/ def sdUnits : LRV.Sentence := allOne (pUnits &0 ⟹ pRVsort &0)
/-- `K = Kˣ ∪ {0}` is closed under `+` -/ def sdKAdd : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd &0 &1)))
/-- `K` is closed under unary `-` -/ def sdKNeg : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pInK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two elements of `K` is in `K` and not `∞`. Without this the field axioms of `kField` (which are guarded by `pK`) constrain only the products that happen to land in `K`. -/ def sdKMul : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul &0 &1)))
/-- The closure part of the sort discipline: each sort is closed under its own symbols, and the two sorts are related through the symbols that cross them. -/ def sortClosure : LRV.Theory :=
  ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv,
    sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdRVInv, sdUnits, sdKAdd, sdKNeg, sdKMul]
/-- the sort discipline of the encoding, as a theory -/ def sortAxioms : LRV.Theory := sortClosure ∪ ofList [sdCover, sdDisjoint]
/-- the field axioms for the sort `s`, with that sort's `0`, `1`, `+`, `-`, `×` -/ def fieldAxioms (s : SortTag) (zero one : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (neg : {n : ℕ} → Tm n → Tm n) :
    List LRV.Sentence :=
  [
    allSorted ![s, s, s] (pEq (add (add &0 &1) &2) (add &0 (add &1 &2))),
    allSorted ![s, s] (pEq (add &0 &1) (add &1 &0)),
    allSorted ![s] (pEq (add &0 zero) &0),
    allSorted ![s] (pEq (add &0 (neg &0)) zero),
    allSorted ![s, s, s] (pEq (mul (mul &0 &1) &2) (mul &0 (mul &1 &2))),
    allSorted ![s, s] (pEq (mul &0 &1) (mul &1 &0)),
    allSorted ![s] (pEq (mul &0 one) &0),
    allSorted ![s, s, s] (pEq (mul &0 (add &1 &2)) (add (mul &0 &1) (mul &0 &2))),
    ∼(pEq zero one),
    allSorted ![s] (pEq &0 zero ⊔ exSorted s (pEq (mul &0 &1) one)) ]
/-- the algebraic-closedness scheme for the sort `s`: `∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/ def acfScheme (s : SortTag) (zero : {n : ℕ} → Tm n)
    (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (k : ℕ) : LRV.Sentence :=
  allSorted (fun _ : Fin k => s) (exSorted s (pEq (hornerPoly add mul) zero))
/-- Definition 2.2 item 1: `(VF, 0, 1, +, -, ×)` is an algebraically closed field. -/ def vfField : LRV.Theory :=
  ofList (fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg)
/-- algebraic closedness of the `VF` sort -/ def vfAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfScheme .vf tVFZero tVFAdd tVFMul k}
/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field, where `K = K^× ∪ {0}`, the units of `RV` together with the absorbing element `0 = ∞ = rv 0`. Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV` sort. This is not cosmetic: `RV^×` also contains the elements of value `≠ 1`, where the residue operations are junk, so asserting the field axioms at every element of `RV` (equivalently at every `t ≠ ∞`, since `RV ∖ {0}` *is* the group) would force `Γ` trivial. -/ def kField : LRV.Theory :=
  ofList
    [
      allSortedK ![.rv, .rv, .rv] (pEq (tKAdd (tKAdd &0 &1) &2) (tKAdd &0 (tKAdd &1 &2))),
      allSortedK ![.rv, .rv] (pEq (tKAdd &0 &1) (tKAdd &1 &0)),
      allSortedK ![.rv] (pEq (tKAdd &0 tRVZero) &0),
      allSortedK ![.rv] (pEq (tKAdd &0 (tKNeg &0)) tRVZero),
      allSortedK ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2))),
      allSortedK ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0)),
      allSortedK ![.rv] (pEq (tRVMul &0 tRVOne) &0),
      allSortedK ![.rv, .rv, .rv]
        (pEq (tRVMul &0 (tKAdd &1 &2)) (tKAdd (tRVMul &0 &1) (tRVMul &0 &2))),
      ∼(pEq tRVZero tRVOne),
      allSortedK ![.rv] (pEq &0 tRVZero ⊔ exSortedK .rv (pEq (tRVMul &0 &1) tRVOne)) ]
/-- the algebraic-closedness scheme for `K = K^× ∪ {0}`: coefficients and root in `K` -/ def acfSchemeK (k : ℕ) : LRV.Sentence :=
  allSortedK (fun _ : Fin k => .rv)
    (exSortedK .rv (pEq (hornerPoly tKAdd tRVMul) tRVZero))
/-- algebraic closedness of `K = K^× ∪ {0}` -/ def kAlgClosed : LRV.Theory := {s | ∃ k, 1 ≤ k ∧ s = acfSchemeK k}
/-- `1 ∈ Kˣ` -/ def rvOneMem : LRV.Sentence := pUnits tRVOne
/-- `Kˣ` is closed under `×` -/ def rvMulMem : LRV.Sentence := allSorted ![.rv, .rv] (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul &0 &1)))
/-- `×` is associative on `RV` -/ def rvMulAssoc : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul &0 &1) &2) (tRVMul &0 (tRVMul &1 &2)))
/-- `×` is commutative on `RV` -/ def rvMulComm : LRV.Sentence := allSorted ![.rv, .rv] (pEq (tRVMul &0 &1) (tRVMul &1 &0))
/-- `1` is neutral for `×` on `Kˣ` -/ def rvMulOne : LRV.Sentence := allSorted ![.rv] (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every element of `Kˣ` is invertible in `Kˣ` -/ def rvMulInv : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- divisibility of `Kˣ`: for every `k ≥ 1`, `∀ x ∈ Kˣ ∃ y ∈ Kˣ, y^k = x` -/ def rvDivisible (k : ℕ) : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVPow &1 k) &0))
/-- `t × 0 = 0` for `t ∈ K` -/ def rvMulZeroK : LRV.Sentence := allSorted ![.rv] (pInK &0 ⟹ pEq (tRVMul &0 tRVZero) tRVZero)
/-- `t × 0 = 0` for every `t` of the `RV` sort: the absorbing element. (This is the paper's `t × ∞ = ∞`; `∞ = rv 0 = 0`.) -/ def rvMulInfty : LRV.Sentence := allSorted ![.rv] (pEq (tRVMul &0 tRVInfty) tRVInfty)
/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×` augmented by `t × 0 = 0`, i.e. `0 = ∞ = rv 0` absorbing. -/ def rvGroup : LRV.Theory :=
  ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK,
      rvMulInfty] ∪
    {s | ∃ k, 1 ≤ k ∧ s = rvDivisible k}
/-- `≤` is reflexive on `RV` -/ def leRefl : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 &0)
/-- `≤` is transitive on `RV` -/ def leTrans : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe &0 &1 ⟹ (pLe &1 &2 ⟹ pLe &0 &2)))))
/-- `≤` is total on `RV` -/ def leTotal : LRV.Sentence := allSorted ![.rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pLe &0 &1 ⊔ pLe &1 &0)))
/-- `∞` is the top element of `RV` -/ def leTop : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pLe &0 tRVInfty)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/ def leInftyEq : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq &0 tRVInfty))
/-- `Kˣ` is the equivalence class of `1` -/ def leClassOne : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe &0 tRVOne)))
/-- `≤` is compatible with `×` on the left, i.e. the induced order on `RV/Kˣ` is a translation-invariant order -/ def leMulCompat : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pUnits &2 ⟹ (pLe &0 &1 ⟹ pLe (tRVMul &0 &2) (tRVMul &1 &2))))))
/-- Definition 2.2 item 4: `≤` is a preorder on `RV` with `∞` the top element and `Kˣ` the equivalence class of `1`. -/ def preorderRV : LRV.Theory :=
  ofList [leRefl, leTrans, leTotal, leTop, leInftyEq, leClassOne, leMulCompat]
/-- `rv(0) = ∞` -/ def rvZeroEq : LRV.Sentence := pEq (tRv tVFZero) tRVInfty
/-- `rv(x) = ∞` forces `x = 0` -/ def rvEqInfty : LRV.Sentence := allSorted ![.vf] (pEq (tRv &0) tRVInfty ⟹ pEq &0 tVFZero)
/-- `rv` is a group homomorphism on `VF^×` -/ def rvMulHom : LRV.Sentence :=
  allSorted ![.vf, .vf] (pEq (tRv (tVFMul &0 &1)) (tRVMul (tRv &0) (tRv &1)))
/-- **`rv` is surjective**: every element of the `RV` sort other than `rv(0)` is `rv(x)` for some `x ∈ VF`. (Definition 2.2(6): `rv : VF^× → RV^×` is surjective, augmented by `rv(0) = ∞ = 0`. With `RV^× = RV ∖ {0}` this says: `RV = rv(VF^×) ∪ {0}`, so there are no `RV`-elements outside the image of `rv`.) -/ def rvSurj : LRV.Sentence :=
  allSorted ![.rv] (∼(pEq &0 tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))
/-- the ultrametric inequality for `vv = vrv ∘ rv`: `vv(x+y) ≥ min(vv x, vv y)` -/ def rvUltrametric : LRV.Sentence :=
  allSorted ![.vf, .vf] (pLe (tRv &0) (tRv (tVFAdd &0 &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd &0 &1)))
/-- Definition 2.2 item 6: `rv : VF^× → RV^×` is a surjective group homomorphism augmented by `rv(0) = ∞`, and `vv = vrv ∘ rv` is a valuation. (The valuation ring `O = rv⁻¹(RV^{≥1})` and the maximal ideal `M = rv⁻¹(RV^{>1})` are *defined* from `rv`, so — exactly as in the paper — they need no symbols of their own.) -/ def rvAxioms : LRV.Theory :=
  ofList [rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric]
/-- `1` is neutral for `×` on every nonzero `RV`-element. -/ def rvMulOneRV : LRV.Sentence := allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every nonzero `RV`-element is invertible in `RV^×`. -/ def rvMulInvRV : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul &1 &0) tRVOne))
/-- the order on `RV` is invariant under scaling by any `c ≠ rv 0`, in both directions. The guards on the first two variables are dropped because `∞ = rv 0` is absorbing and top, so both sides hold there. -/ def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &2 ⟹ (pLe &0 &1 ⇔ pLe (tRVMul &0 &2) (tRVMul &1 &2)))
/-- `kAdd` is the residue addition at units: `rv (x + y)` if that is a unit, and `0` if `x + y` drops into the maximal ideal. -/ def kAddLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹
      ((pUnits (tRv (tVFAdd &0 &1)) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd &0 &1))) ⊓
        (∼(pUnits (tRv (tVFAdd &0 &1))) ⟹
          pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))
/-- `kNeg` is the residue negation at units. -/ def kNegLink : LRV.Sentence :=
  allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))
/-- two elements of `VF` have the same residue iff their difference has strictly larger value than the second: `rv a = rv b ↔ ¬ (v (a - b) ≤ v b)`. (The first transcription had the two `pLe` arguments transposed, which made the axiom false at `a = b = 1` and the whole theory inconsistent — see `QE-PLAN.md` and `.ultramath/smw163dd5/m5/Audit.lean`.) -/ def rvEqLink : LRV.Sentence :=
  allSorted ![.vf, .vf]
    (∼(pEq &1 tVFZero) ⟹
      (pEq (tRv &0) (tRv &1) ⇔ ∼(pLe (tRv (tVFAdd &0 (tVFNeg &1))) (tRv &1))))
/-- the junk convention for `kAdd` off `K`: the value is `0`. -/ def kJunkZero : LRV.Sentence :=
  allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd &0 &1) tRVZero)
/-- the junk convention for `kNeg` off `K`. -/ def kNegJunkZero : LRV.Sentence := allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)
/-- **Nontriviality**: some nonzero element of `VF` has value strictly below the value of `1`, i.e. lies in the maximal ideal. -/ def axNontrivialRV : LRV.Sentence :=
  exSorted .vf (∼(pEq &0 tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))
/-- The inverse operation fixes the absorbing element `0 = ∞`. -/ def rvInvZero : LRV.Sentence := pEq (tRVInv tRVZero) tRVZero
/-- The named inverse is a multiplicative inverse on the nonzero `RV` group. -/ def rvInvMul : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)
/-- The added axioms, in one theory. -/ def repairRV : LRV.Theory :=
  ofList [rvMulOneRV, rvMulInvRV, leMulCompatFull, kAddLink, kNegLink, rvEqLink, kJunkZero,
    kNegJunkZero, axNontrivialRV, rvInvZero, rvInvMul]
/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/ def ACVFpaper : LRV.Theory :=
  vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms ∪ repairRV ∪ repairRV
/-- **The theory `ACVF` of Definition 2.2**, in the tagged encoding: items 1–6 plus the sort discipline of the encoding. -/ def ACVF : LRV.Theory := sortAxioms ∪ ACVFpaper
/-- characteristic zero of the `VF` sort -/ def charZeroVF (k : ℕ) : LRV.Sentence := ∼(pEq (tVFNumeral (k + 1)) tVFZero)
/-- residue characteristic zero: for each prime `p`, `p · 1` is a unit of the valuation ring, i.e. `¬ (1 < rv(p·1))` -/ def residueCharZero (p : ℕ) : LRV.Sentence := ∼(pGtOne (tRv (tVFNumeral p)))
/-- the paper's content of `ACVF(0,0)`: `ACVF` together with pure characteristic `0` -/ def ACVF00paper : LRV.Theory :=
  ACVFpaper ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}
/-- **The theory `ACVF(0,0)`**: `ACVF` with pure characteristic `0`, i.e. characteristic `0` for the valued field and characteristic `0` for its residue field. -/ def ACVF00 : LRV.Theory := ACVF ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}
end Axioms
open LRV
def sortEval {M : Type*} [LRV.Structure M] : SortTag → M → Prop
  | .vf => fun x => Structure.RelMap (L := LRV) Rel.memVF ![x]
  | .rv => fun x => Structure.RelMap (L := LRV) Rel.memRV ![x]
/-- A theory `T` of `L_RV` **admits quantifier elimination on the well-sorted fragment**: every formula of the paper's two-sorted language — a `WellSorted` formula of the one-sorted encoding — is `T`-equivalent, at tuples respecting the declared sorts, to a quantifier-free formula of the same fragment. This is the paper's Theorem 2.3 ("the theory `ACVF` admits quantifier elimination"), stated for the two-sorted `L_RV` it is about: the encoding's carrier admits ill-sorted terms such as `rv (rv x)`, whose values no axiom fixes, and those are not formulas of the paper's language. -/ def HasQE (T : LRV.Theory) : Prop :=
  ∀ (α : Type) (sα : α → SortTag) (n : ℕ) (sn : Fin n → SortTag)
    (φ : LRV.BoundedFormula α n), WellSorted sα sn φ →
    ∃ ψ : LRV.BoundedFormula α n, ψ.IsQF ∧ WellSorted sα sn ψ ∧
      ∀ (M : Type) [LRV.Structure M], M ⊨ T → ∀ (v : α → M) (x : Fin n → M),
        (∀ a, sortEval (sα a) (v a)) → (∀ i, sortEval (sn i) (x i)) →
        (φ.Realize v x ↔ ψ.Realize v x)
end Milestone0
end SpecialTransformations

set_option backward.isDefEq.respectTransparency false
namespace FirstOrder
inductive ValFunc : ℕ → Type
  | add : ValFunc 2
  | mul : ValFunc 2
  | neg : ValFunc 1
  | zero : ValFunc 0
  | one : ValFunc 0
  deriving DecidableEq
inductive ValRel : ℕ → Type
  | le : ValRel 2
  deriving DecidableEq
namespace Language
/-- **Johnson's language `L_val`**: the language of rings expanded by a binary predicate for the relation `v x ≤ v y`. -/ def val : FirstOrder.Language := ⟨ValFunc, ValRel⟩
end Language
/-- **The `L_val`-structure of a valued field.** -/ @[instance_reducible]
def valStructure {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) : Language.val.Structure K where
  funMap := fun {_} f x =>
    match f with
    | ValFunc.add => x 0 + x 1
    | ValFunc.mul => x 0 * x 1
    | ValFunc.neg => - x 0
    | ValFunc.zero => 0
    | ValFunc.one => 1
  RelMap := fun {_} r x =>
    match r with
    | ValRel.le => v (x 0) ≤ v (x 1)
/-- The language inclusion `L_ring → L_val`. -/ def valRingHom : Language.ring →ᴸ Language.val where
  onFunction := fun {_} f => match f with
    | ringFunc.add => ValFunc.add
    | ringFunc.mul => ValFunc.mul
    | ringFunc.neg => ValFunc.neg
    | ringFunc.zero => ValFunc.zero
    | ringFunc.one => ValFunc.one
  onRelation := fun {_} r => isEmptyElim r
end FirstOrder
namespace ValPM
open FirstOrder FirstOrder.Language FirstOrder.Ring
section Terms
variable {α : Type*}
instance instZeroTerm : Zero (Language.val.Term α) := ⟨Term.func ValFunc.zero fun i => i.elim0⟩
instance instOneTerm : One (Language.val.Term α) := ⟨Term.func ValFunc.one fun i => i.elim0⟩
instance instAddTerm : Add (Language.val.Term α) := ⟨fun a b => Term.func ValFunc.add ![a, b]⟩
instance instMulTerm : Mul (Language.val.Term α) := ⟨fun a b => Term.func ValFunc.mul ![a, b]⟩
instance instNegTerm : Neg (Language.val.Term α) := ⟨fun a => Term.func ValFunc.neg ![a]⟩
end Terms
/-- The atomic formula `v a ≤ v b` of `L_val`. -/ abbrev leF {α : Type*} {n : ℕ} (a b : Language.val.Term (α ⊕ Fin n)) :
    Language.val.BoundedFormula α n :=
  Relations.boundedFormula ValRel.le (l := n) ![a, b]
/-- The valuation predicate of an `L_val`-structure. -/ abbrev predM {M : Type*} [Language.val.Structure M] (x y : M) : Prop :=
  @Structure.RelMap Language.val M _ 2 ValRel.le ![x, y]
/-- The relation `v x ≤ v y` is reflexive. -/ def axReflF : Language.val.BoundedFormula Empty 1 := leF (&0) (&0)
def axRefl : Language.val.Sentence := axReflF.alls
/-- The relation `v x ≤ v y` is transitive. -/ def axTransF : Language.val.BoundedFormula Empty 3 :=
  leF (&0) (&1) ⟹ leF (&1) (&2) ⟹ leF (&0) (&2)
def axTrans : Language.val.Sentence := axTransF.alls
/-- The relation `v x ≤ v y` is total. -/ def axTotalF : Language.val.BoundedFormula Empty 2 := leF (&0) (&1) ⊔ leF (&1) (&0)
def axTotal : Language.val.Sentence := axTotalF.alls
/-- `v 0` is minimal. -/ def axZeroLeF : Language.val.BoundedFormula Empty 1 := leF 0 (&0)
def axZeroLe : Language.val.Sentence := axZeroLeF.alls
/-- `v x ≤ v 0` only for `x = 0`. -/ def axZeroEqF : Language.val.BoundedFormula Empty 1 := leF (&0) 0 ⟹ (&0 =' 0)
def axZeroEq : Language.val.Sentence := axZeroEqF.alls
/-- The ultrametric inequality `v (x + y) ≤ max (v x) (v y)`, as a disjunction. -/ def axUltraF : Language.val.BoundedFormula Empty 2 :=
  leF (&0 + &1) &0 ⊔ leF (&0 + &1) &1
def axUltra : Language.val.Sentence := axUltraF.alls
/-- Multiplication by a nonzero element preserves and reflects the order: `v (x z) ≤ v (y z) ↔ v x ≤ v y`. This is the multiplicative behaviour of `v`, expressed by the predicate alone. -/ def axScaleF : Language.val.BoundedFormula Empty 3 :=
  ∼(&2 =' 0) ⟹ (leF (&0) (&1) ⇔ leF (&0 * &2) (&1 * &2))
def axScale : Language.val.Sentence := axScaleF.alls
/-- The theory of fields, transported to `L_val`. -/ def fieldPart : Language.val.Theory := valRingHom.onBoundedFormula '' Theory.field
/-- The axioms of a valuation, expressed by the predicate `v x ≤ v y` alone. -/ def valAxioms : Language.val.Theory :=
  {axRefl, axTrans, axZeroLe, axZeroEq, axUltra, axScale}
/-- The part of the theory of valued fields which the arguments below actually use. -/ def valFieldCore : Language.val.Theory := fieldPart ∪ valAxioms
/-- **The theory of valued fields** in the language `L_val`: a field, together with a predicate `v x ≤ v y` which behaves like comparison of valuations. -/ def valField : Language.val.Theory := valFieldCore ∪ {axTotal}
/-- The `L_val`-sentence "every monic polynomial of degree `n` has a root", read along `valRingHom` from the language of rings. -/ noncomputable def genericMonicPolyHasRoot (n : ℕ) : Language.val.Sentence :=
  valRingHom.onBoundedFormula (Field.genericMonicPolyHasRoot n)
/-- The valuation is nontrivial: some **nonzero** element lies in the maximal ideal, `v x < v 1`. The `x ≠ 0` conjunct is essential and its absence was a real defect: `0` satisfies `v 0 < v 1` in *every* valued field, so `∃ x, ¬ (v 1 ≤ v x)` alone is a tautology and says nothing about nontriviality. The sentence below is the one that has to be used. -/ def axNontrivialF : Language.val.BoundedFormula Empty 1 :=
  let x : Language.val.Term (Empty ⊕ Fin 1) := Term.var (Sum.inr ⟨0, Nat.zero_lt_succ 0⟩)
  ∼(x =' 0) ⊓ ∼(leF 1 x)
/-- **Nontriviality of the valuation**, as a sentence of `L_val`. -/ def axNontrivial : Language.val.Sentence := axNontrivialF.ex
/-- **The theory of nontrivially valued algebraically closed fields in `L_val`.** -/ noncomputable def ACVF_val : Language.val.Theory :=
  valField ∪ genericMonicPolyHasRoot '' {n : ℕ | 0 < n} ∪ {axNontrivial}
end ValPM

open FirstOrder.Ring
open scoped FirstOrder
namespace ACFValidation
/-- Algebraically closed fields in every characteristic. -/
noncomputable def acf : Theory Language.ring :=
  Theory.field ∪ Field.genericMonicPolyHasRoot '' {n : ℕ | 0 < n}

end ACFValidation
namespace QECriterion
variable {L : Language}
/-- Every bounded formula has a quantifier-free equivalent over all models of T. -/
def HasQEb (T : L.Theory) : Prop :=
  ∀ (α : Type) (n : ℕ) (φ : L.BoundedFormula α n),
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ Theory.Iff T φ ψ
/-- Formula-level quantifier elimination, uniformly across models of T. -/
def HasQE (T : L.Theory) : Prop :=
  ∀ (α : Type) (φ : L.Formula α), ∃ ψ : L.Formula α, ψ.IsQF ∧ Theory.Iff T φ ψ
end QECriterion

/-- Pure ACF has bounded quantifier elimination in every characteristic. -/
theorem PalomarQE.acf : QECriterion.HasQEb (L := Language.ring) ACFValidation.acf := by sorry
/-- Nontrivially valued algebraically closed fields have bounded QE. -/
theorem PalomarQE.nontrivial_acvf : QECriterion.HasQEb (L := Language.val) ValPM.ACVF_val := by sorry
/-- Nontrivial ACVF has well-sorted QE in the corrected RV language. -/
theorem PalomarQE.rv_acvf : SpecialTransformations.Milestone0.HasQE SpecialTransformations.Milestone0.Axioms.ACVF := by sorry
