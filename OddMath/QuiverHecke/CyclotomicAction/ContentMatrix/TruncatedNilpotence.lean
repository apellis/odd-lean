import Mathlib.CategoryTheory.Whiskering
import OddMath.Algebra.FiniteSupermodule
import OddMath.Algebra.FiniteZeroCoordinate
import OddMath.QuiverHecke.CyclotomicAction.ContentModule.ContentModuleQuadratic
import OddMath.SKM.RouquierCoupled

/-!
# Content matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Positive-degree nilpotence in the truncated ELV category

`truncatedContent_positive_pow_zero` derives a common exponent for all positive
integer-degree endomorphisms of every word of a fixed content. It supplies the
quotient-level nilpotence needed for the reservoir post-dot in the coefficient
construction. Integer degree, not super parity, controls the exponent. The
coefficient algebra retains its exterior multiplication.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (N : ℕ)

/-- The bound is derived from the coefficient bound and the cyclotomic append
recurrence. It is uniform in the word, positive degree, and endomorphism. -/
theorem truncatedContent_positive_pow_zero_of_bound (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d → f ^ e = 0 := by
  classical
  choose B hB using fun v : List I =>
    truncatedContent_bounded_of_bound D Sc cutoff sy hc N M hM hbound v v
  let K := ν.permutations.toFinset.sup B
  refine ⟨K + 1, by omega, ?_⟩
  intro v hv d hd f hf
  have hv' : v ∈ ν.permutations.toFinset := by simpa using hv
  have hb : B v ≤ K := Finset.le_sup hv'
  have hp := SetLike.pow_mem_graded (K + 1) hf
  have hdeg : (B v : ℤ) < (K + 1) • d := by
    rw [nsmul_eq_mul]
    have hcast : (B v : ℤ) ≤ K := by exact_mod_cast hb
    have hk : (0 : ℤ) ≤ K := Nat.cast_nonneg K
    push_cast
    nlinarith
  change f ^ (K + 1) ∈ truncatedDegree D Sc cutoff sy hc N v v ((K + 1) • d) at hp
  rw [hB v _ (Or.inr hdeg)] at hp
  exact hp

/-- For finite colours every fixed content has a uniform positive-degree
nilpotence exponent, over any commutative ground ring (including the zero ring). -/
theorem truncatedContent_positive_pow_zero [Finite I] (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedEndDegree D Sc cutoff N sy hc v d → f ^ e = 0 := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_positive_pow_zero_of_bound D Sc cutoff sy hc N M hM hb ν

/-- The positioned affine dot in the coefficient-truncated quotient. -/
def truncatedDot (v : List I) (r : ℕ) : TruncatedEnd D Sc cutoff N v :=
  (truncatedIdeal D Sc cutoff N v v).mkQ
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc v r)

include sy hc in
/-- The last-strand dot of the existing append transformation is nilpotent,
uniformly on the source content. This is componentwise, not a claim of one
exponent on the unbounded category of all words. -/
theorem truncatedAppendDot_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ v : TruncatedCategory D Sc cutoff N, v.word.Perm ν →
      let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
        (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
      f ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedContent_positive_pow_zero D Sc cutoff sy hc N (ν ++ [i])
  refine ⟨e, he, fun v hv => hp _ (hv.append (List.Perm.refl _)) _ ?_ _
    (truncatedAppendDot_degree D Sc cutoff N sy hc i v)⟩
  have := sy.pos i
  omega

/-- Nilpotence of the appended last-strand dot, with one exponent for each source content and
appended colour. This is the only input on the parameters that the content-induction and
reservoir dot nilpotence results use. -/
structure TruncatedAppendDotNilpotent : Prop where
  /-- For each source content `ν` and appended colour `i`, one positive exponent kills the
  appended dot on every word of content `ν`. -/
  out : ∀ (ν : List I) (i : I), ∃ e : ℕ, 0 < e ∧ ∀ v : TruncatedCategory D Sc cutoff N,
    v.word.Perm ν →
      let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
        (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
      f ^ e = 0

include sy hc in
/-- Homogeneous parameters give nilpotence of the appended dot. -/
theorem truncatedAppendDotNilpotent [Finite I] : TruncatedAppendDotNilpotent D Sc cutoff N :=
  ⟨truncatedAppendDot_pow_zero D Sc cutoff sy hc N⟩

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Canonical triple-E transport of the corrected mixed braid

Advances `DeformedActionAssembly.md` §6 with an even all-module comparison
from three successive single-letter E functors to block induction. Intermediate
and final content equalities are explicit. The same recursively constructed
comparison is used at every word, so both three-crossing paths transport
coherently; the checked source maps and both equal-crossing minus signs are
retained. The polynomial has exactly original Sc and three ordered dot powers.
The linear arrows are evaluated genuine supernatural transformations, and the
residual twist on the entire coefficient/diagram kernel is stated explicitly.

This proves path compatibility for these canonical transported source maps.
It does not yet identify them with independently whiskered pair crossings/dots
or prove equality of the two possible recursive associativity comparisons.
No weight assembly, local inversions or nondegeneracy is claimed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentAppend_compTo_eq (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentAppendTo D Sc cutoff N β σ δ hδ ⋙ contentAppendTo D Sc cutoff N δ τ γ hγ =
      contentAppendTo D Sc cutoff N β (σ ++ τ) γ h := by
  subst δ
  exact contentAppend_comp_eq D Sc cutoff N β σ τ γ hγ h

/-- The intermediate content equality is explicit as well. -/
def contentInductionCompTo (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ) (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInductionTo D Sc cutoff N β σ δ hδ ⋙ contentInductionTo D Sc cutoff N δ τ γ hγ ≅
      contentInductionTo D Sc cutoff N β (σ ++ τ) γ h := by
  subst δ
  exact contentInductionComp D Sc cutoff N β σ τ γ hγ h

theorem contentInductionCompTo_mem (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ) (h : β + ((σ ++ τ : List I) : Multiset I) = γ)
    (M : ContentModules D Sc cutoff N β) :
    EvenComparisonAt (k := k) (contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h) M := by
  subst δ
  exact contentInductionComp_mem D Sc cutoff N β σ τ γ hγ h M

/-- Three actual single-letter E functors; only the final content is recast. -/
abbrev contentETripleTo (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :=
  (contentE D Sc cutoff N β i ⋙ contentE D Sc cutoff N (β + ([i] : Multiset I)) j) ⋙
    contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)

def contentETripleComparison (β : Multiset I) (i j l : I) (γ : Multiset I)
    (h : β + ([i,j,l] : Multiset I) = γ) :
    contentETripleTo D Sc cutoff N β i j l γ h ≅ contentInductionTo D Sc cutoff N β [i,j,l] γ h :=
  Functor.isoWhiskerRight (contentEPairComparison D Sc cutoff N β i j)
    (contentInductionTo D Sc cutoff N ((β + ([i] : Multiset I)) + ([j] : Multiset I)) [l] γ
      (by rw [add_assoc, add_assoc]; exact h)) ≪≫
  contentInductionCompTo D Sc cutoff N β [i,j]
    ((β + ([i] : Multiset I)) + ([j] : Multiset I)) (by rw [add_assoc]; rfl)
    [l] γ _ h

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Balanced tensor formulas for content comparison coherence

Pointwise formulas retain the content endpoint casts in the composition
comparisons used by DeformedActionAssembly.md §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELV
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentInductionCompTo_eq (β : Multiset I) (σ : List I) (δ : Multiset I)
    (hδ : β + (σ : Multiset I) = δ) (τ : List I) (γ : Multiset I)
    (hγ : δ + (τ : Multiset I) = γ)
    (h : β + ((σ ++ τ : List I) : Multiset I) = γ) :
    contentInductionCompTo D Sc cutoff N β σ δ hδ τ γ hγ h =
      inductionCompOfEq (contentAppendTo D Sc cutoff N β σ δ hδ)
        (contentAppendTo D Sc cutoff N δ τ γ hγ)
        (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h)
        (contentAppend_compTo_eq D Sc cutoff N β σ δ hδ τ γ hγ h) := by
  subst δ
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Tensor formula for the raising-pair comparison

This retains the content cast needed in DeformedActionAssembly.md §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELV
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentPair_sum (β : Multiset I) (i j : I) :
    β + ([i,j] : Multiset I) = (β + ([i] : Multiset I)) + ([j] : Multiset I) := by
  rw [add_assoc]
  rfl

section Pair
variable (β : Multiset I) (i j : I)

end Pair
end OddMath.QuiverHecke.ELV
end

end

section

/-! # Whiskered single-letter dots and the pair quadratic

The canonical transported positioned dots equal independently constructed
single-letter actions. The inner dot uses induction on the existing
`contentInductionDot`; the outer dot retains the explicit target-content
recast. The original-Sc ordered quadratic is consequently a relation in
these independently whiskered dots, not merely in conjugated block dots.
Triple crossing and associativity coherence are separate obligations.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Evaluation of induction on a homogeneous module map. The statement keeps
the actual induced SVec objects on the left and the raw formula on the right. -/
theorem contentInductionMap_total_of_mem
    {C B : Type u} [Category.{u} C] [Category.{u} B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]
    (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {F G : Superfunctor k C (SVec k)} {p : ZMod 2} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ p) (z : B) :
    ((BalancedInduction.induction J).map f).total z = BalancedInduction.mapComponent J f p z := by
  have hm := Supercategory.map_mem (BalancedInduction.induction J) hf
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 1) (by decide), add_zero]
    rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hm (q := 0) (by decide), zero_add]
    rfl

/-- The component of the actual induction transformation has the raw balanced
formula. This comparison is generic in both content equalities. -/
theorem contentInductionTransform_total {β γ : Multiset I} {σ τ : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    {p : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    ((contentInductionTransform D Sc cutoff N hσ hτ ha).app p M).total z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M z := by
  have h := congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha))) M
  have ht :
      ((BalancedInduction.transformLinear_supernatural
        (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M).toSuperNatTrans).total z =
        BalancedInduction.transformLinear
          (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M z := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [SuperNatTrans.total, IsSupernatural.toSuperNatTrans]
  exact (congrArg (fun f => f.total z) h).trans ht

theorem contentInductionDot_component (β : Multiset I) (i : I)
    (M : ContentModules D Sc cutoff N β) :
    (contentInductionDot D Sc cutoff N β i).app (D.parity i) M =
      BalancedInduction.transformComponent
        (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])) M := by
  exact congrFun (IsSupernatural.toSuperNatTrans_app
    (BalancedInduction.transformComponent_supernatural
      (contentAppendTo_supernatural D Sc cutoff N rfl rfl (firstDot_parity D Sc i [])))) M

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Nilpotence of the content induction dot

The fixed-content positive-integer-degree bound implies nilpotence of the
independently defined induction dot on arbitrary modules. The induction mate
acts by twisted precomposition, not by the target-word module action. Its
iterates carry the sign proved in `transformLinear_pow_tensor`, with the full
coefficient parity retained. This supplies the dot-nilpotence input of
`DeformedActionAssembly.md` §6; construction of the reservoir action is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV
universe u
namespace BalancedInduction
variable {k : Type u} [CommRing k]
variable {C B : Type u} [Category.{u} C] [Category.{u} B]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive B] [Linear k B] [Supercategory k B]
variable {J : C ⥤ B} [J.Additive] [J.Linear k] [IsSuperfunctor k J]

/-- The signed iteration formula transports a common source exponent to all
balanced induction modules. No boundedness of the module is required. -/
theorem transformLinear_pow_zero {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (n : ℕ) (hn : ∀ v, a v ^ n = 0)
    (M : Superfunctor k C (SVec k)) (w : B) :
    transformLinear ha M w ^ n = 0 := by
  apply hom_ext
  intro v h m
  rw [transformLinear_pow_tensor, hn v, Limits.zero_comp]
  simp [tensor]
/-- Total evaluation preserves endomorphism powers, without a transpose sign. -/
theorem end_total_pow (M : Superfunctor k C (SVec k)) (f : End M) (n : ℕ) (v : C) :
    (f ^ n).total v = (show End (M.obj v) from f.total v) ^ n := by
  induction n with
  | zero => exact SuperNatTrans.id_total _ _
  | succ n ih =>
    rw [pow_succ, End.mul_def, Superfunctor.comp_total, ih, pow_succ, End.mul_def]

/-- Total evaluation detects zero because the two parity summands are independent. -/
theorem end_eq_zero_of_total (M : Superfunctor k C (SVec k)) (f : End M)
    (hf : ∀ v, f.total v = 0) : f = 0 := by
  apply Superfunctor.hom_ext_parity
  · intro v
    have h := congrArg (proj (R := k) 0) (hf v)
    simpa only [SuperNatTrans.total, map_add, map_zero,
      proj_of_mem (f.app_mem 0 v), proj_of_mem_ne (f.app_mem 1 v) (by decide : (1 : ZMod 2) ≠ 0),
      add_zero, Superfunctor.zero_app] using h
  · intro v
    have h := congrArg (proj (R := k) 1) (hf v)
    simpa only [SuperNatTrans.total, map_add, map_zero,
      proj_of_mem (f.app_mem 1 v), proj_of_mem_ne (f.app_mem 0 v) (by decide : (0 : ZMod 2) ≠ 1),
      zero_add, Superfunctor.zero_app] using h

/-- Nilpotence of the entire homogeneous module transformation, not just its
value on a selected parity of vectors. -/
theorem transformComponent_pow_zero {p : ZMod 2} {a : ∀ v, End (J.obj v)}
    (ha : IsSupernatural k p a) (n : ℕ) (hn : ∀ v, a v ^ n = 0)
    (M : Superfunctor k C (SVec k)) :
    (show End (induced J M) from transformComponent ha M) ^ n = 0 := by
  apply end_eq_zero_of_total
  intro w
  rw [end_total_pow]
  have ht : (transformComponent ha M).total w = transformLinear ha M w := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [SuperNatTrans.total, transformComponent_app]
  rw [ht]
  exact transformLinear_pow_zero ha n hn M w
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (N : ℕ) (hdot : TruncatedAppendDotNilpotent D Sc cutoff N)

include hdot in
/-- The independently defined content dot is nilpotent as an endomorphism in
the module supercategory, uniformly in the arbitrary input module. -/
theorem contentInductionDot_module_pow_zero [Finite I] (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ M : ContentModules D Sc cutoff N (ν : Multiset I),
      (show End ((contentE D Sc cutoff N (ν : Multiset I) i).obj M) from
        (contentInductionDot D Sc cutoff N (ν : Multiset I) i).app (D.parity i) M) ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := hdot.out ν i
  refine ⟨e, he, fun M => ?_⟩
  rw [contentInductionDot_component]
  apply BalancedInduction.transformComponent_pow_zero
  intro v
  have hv : v.obj.word.Perm ν := Multiset.coe_eq_coe.mp v.content
  simpa only [truncatedAppendDot_app, contentAppendToComponent] using hp v.obj hv

end OddMath.QuiverHecke.ELV
end

end
