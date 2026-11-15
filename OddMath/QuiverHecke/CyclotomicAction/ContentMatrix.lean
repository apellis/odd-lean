import OddMath.Algebra.FiniteSupermodule
import OddMath.QuiverHecke.CyclotomicAction.KernelMatrixEvaluation
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction
import Mathlib.CategoryTheory.Whiskering
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend
import OddMath.QuiverHecke.CyclotomicAction.EvenInputMatrix
import OddMath.Algebra.FiniteZeroCoordinate
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.SKM.RouquierMateSectors
import OddMath.SKM.RouquierCoupled

/-!
# Content matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Prescribed matrix isomorphisms on fixed output content

DeformedMatrixComparison section 4, the old-category naturality step.
The finite count is constant on output content. The independently specified
even unit/cap entries assemble naturally along every old arrow, and their
verified arbitrary-module component inverses give supermodule isomorphisms.
These are restrictions of the old-category matrices; compatibility with
the chosen content E/F comparisons and input-module naturality is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

/-- The prescribed finite unit family as an old supermodule. -/
def unitMatrixSourceModule (i : I) (m : ℕ) :
    Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  FiniteSupermodule.product (unitMatrixFamily D Sc cutoff i M m)

/-- The literal assembled unit matrix is natural along all old arrows. -/
def unitMatrixNatTrans (i : I) (m : ℕ) :
    (unitMatrixSourceModule D Sc cutoff M i m).toFunctor ⟶
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).toFunctor :=
  FiniteSupermodule.columns (unitMatrixEntry D Sc cutoff i M m)
    (unitMatrixEntry_mem D Sc cutoff i M m)

private def unitIsoAtCount (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : ℕ) (hm : contentUnitCount D cutoff i (t.word : Multiset I) = m) :
    unitMatrixSourceSpace D Sc cutoff i M m t ≅ mateTargetSpace D Sc cutoff i M t := by
  subst m
  exact moduleUnitMatrixIso D Sc cutoff M i t hh

private theorem unitIsoAtCount_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (m : ℕ) (hm : contentUnitCount D cutoff i (t.word : Multiset I) = m) :
    (unitIsoAtCount D Sc cutoff M i t hh m hm).hom = unitMatrixComponent D Sc cutoff i M m t := by
  subst m
  exact moduleUnitMatrixIso_hom D Sc cutoff M i t hh

private def capIsoAtCount (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (hm : contentCapCount D cutoff i (t.word : Multiset I) = m) :
    mateSourceSpace D Sc cutoff i M t ≅ capMatrixTargetSpace D Sc cutoff i M m t := by
  subst m
  exact moduleCapMatrixIso D Sc cutoff M i t hh

private theorem capIsoAtCount_hom (i : I) (t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (m : ℕ) (hm : contentCapCount D cutoff i (t.word : Multiset I) = m) :
    (capIsoAtCount D Sc cutoff M i t hh m hm).hom = capMatrixComponent D Sc cutoff i M m t := by
  subst m
  exact moduleCapMatrixIso_hom D Sc cutoff M i t hh

/-- The component inverse at the fixed output-content unit count. -/
def contentUnitMatrixComponentIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    unitMatrixSourceSpace D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj ≅
      mateTargetSpace D Sc cutoff i M t.obj :=
  unitIsoAtCount D Sc cutoff M i t.obj
    (by simpa only [Multiset.coe_eq_coe.mpr t.wordPerm] using hh) _
    (congrArg (contentUnitCount D cutoff i) (Multiset.coe_eq_coe.mpr t.wordPerm))

theorem contentUnitMatrixComponentIso_hom (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).hom =
      unitMatrixComponent D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj :=
  unitIsoAtCount_hom D Sc cutoff M i t.obj _ _ _

/-- The component inverse at the fixed output-content cap count. -/
def contentCapMatrixComponentIso (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (t : OldContentCategory D Sc cutoff ν) :
    mateSourceSpace D Sc cutoff i M t.obj ≅
      capMatrixTargetSpace D Sc cutoff i M (contentCapCount D cutoff i (ν : Multiset I)) t.obj :=
  capIsoAtCount D Sc cutoff M i t.obj
    (by simpa only [Multiset.coe_eq_coe.mpr t.wordPerm] using hh) _
    (congrArg (contentCapCount D cutoff i) (Multiset.coe_eq_coe.mpr t.wordPerm))

theorem contentCapMatrixComponentIso_hom (i : I) (ν : List I)
    (hh : contentCrossingHeight D cutoff i (ν : Multiset I) ≤ 0)
    (t : OldContentCategory D Sc cutoff ν) :
    (contentCapMatrixComponentIso D Sc cutoff M i ν hh t).hom =
      capMatrixComponent D Sc cutoff i M (contentCapCount D cutoff i (ν : Multiset I)) t.obj :=
  capIsoAtCount_hom D Sc cutoff M i t.obj _ _ _

/-- Unit-column inversion natural in every arrow of the output content block. -/
def contentUnitMatrixNatIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (oldContentInclusion D Sc cutoff ν ⋙
      (unitMatrixSourceModule D Sc cutoff M i (contentUnitCount D cutoff i (ν : Multiset I))).toFunctor) ≅
    (oldContentInclusion D Sc cutoff ν ⋙
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).toFunctor) :=
  NatIso.ofComponents (contentUnitMatrixComponentIso D Sc cutoff M i ν hh) (by
    intro t t' f
    simp only [contentUnitMatrixComponentIso_hom]
    exact (unitMatrixNatTrans D Sc cutoff M i _).naturality f)

/-- Even supermodule inversion on fixed output content, for every old input module. -/
def contentUnitMatrixIso (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      (unitMatrixSourceModule D Sc cutoff M i (contentUnitCount D cutoff i (ν : Multiset I))) ≅
    (BalancedInduction.restriction (oldContentInclusion D Sc cutoff ν)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj M)) :=
  moduleIsoOfEvenNatIso _ _ (contentUnitMatrixNatIso D Sc cutoff M i ν hh)
    (fun t => by
      change (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).hom ∈ _
      rw [contentUnitMatrixComponentIso_hom]
      exact unitMatrixComponent_even D Sc cutoff i M _ t.obj)
    (fun t => Supercategory.inv_mem (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t) (by
      rw [contentUnitMatrixComponentIso_hom]
      exact unitMatrixComponent_even D Sc cutoff i M _ t.obj))

/-- The content supermodule isomorphism has exactly the prescribed unit components. -/
theorem contentUnitMatrixIso_hom_total (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I))
    (t : OldContentCategory D Sc cutoff ν) :
    (contentUnitMatrixIso D Sc cutoff M i ν hh).hom.total t =
      unitMatrixComponent D Sc cutoff i M (contentUnitCount D cutoff i (ν : Multiset I)) t.obj := by
  change (contentUnitMatrixComponentIso D Sc cutoff M i ν hh t).hom + 0 = _
  rw [add_zero, contentUnitMatrixComponentIso_hom]

/-- Both directions preserve parity as module morphisms, not only pointwise. -/
theorem contentUnitMatrixIso_even (i : I) (ν : List I)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (ν : Multiset I)) :
    (contentUnitMatrixIso D Sc cutoff M i ν hh).hom ∈ parity (R := k) _ _ 0 ∧
      (contentUnitMatrixIso D Sc cutoff M i ν hh).inv ∈ parity (R := k) _ _ 0 := by
  have h : (contentUnitMatrixIso D Sc cutoff M i ν hh).hom ∈ parity (R := k) _ _ 0 := by
    apply Superfunctor.mem_parity_iff_isHomogeneous.mpr
    intro q hq
    funext t
    change (if q = 0 then _ else 0) = 0
    exact ite_eq_right hq
  exact ⟨h, Supercategory.inv_mem _ h⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

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
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Content induction and independent whiskering

The canonical content composition comparison intertwines the independently
defined inner and outer module transformations of an affine endomorphism.
Both content equality transports are retained. The source comparisons are
proved through tensor coefficients and the truncated quotient, not assumed.
These squares identify the transported positioned dots with whiskered
single-letter dots in the content E-action assembly.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
variable {k : Type u} [CommRing k]
variable {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  [Preadditive E] [Linear k E] [Supercategory k E]
variable (J : C ⥤ D) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
variable (K : D ⥤ E) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
variable (L : C ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

theorem compForward_inner_recast (e : J ⋙ K = L) {p : ZMod 2}
    {a : ∀ v, J.obj v ⟶ J.obj v} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (K.map (a v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    let c := inductionComp J K ≪≫ eqToIso
      (show induction (k := k) (J ⋙ K) = induction L by subst L; rfl)
    (moduleIsoLinearEquiv (c.app M) z).toLinearMap ∘ₗ
        mapComponent K (transformComponent ha M) p z =
      transformLinear hb M z ∘ₗ (moduleIsoLinearEquiv (c.app M) z).toLinearMap := by
  subst L
  have hab' : (fun v => K.map (a v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_inner K ha M z

theorem compForward_outer_recast (e : J ⋙ K = L) {p : ZMod 2}
    {a : ∀ w, K.obj w ⟶ K.obj w} (ha : IsSupernatural k p a)
    {b : ∀ v, L.obj v ⟶ L.obj v} (hb : IsSupernatural k p b)
    (hab : ∀ v, HEq (a (J.obj v)) (b v))
    (M : Superfunctor k C (SVec k)) (z : E) :
    let c := inductionComp J K ≪≫ eqToIso
      (show induction (k := k) (J ⋙ K) = induction L by subst L; rfl)
    (moduleIsoLinearEquiv (c.app M) z).toLinearMap ∘ₗ
        transformLinear ha (induced J M) z =
      transformLinear hb M z ∘ₗ (moduleIsoLinearEquiv (c.app M) z).toLinearMap := by
  subst L
  have hab' : (fun v => a (J.obj v)) = b := funext (fun v => eq_of_heq (hab v))
  subst b
  dsimp only
  simp only [eqToIso_refl, Iso.trans_refl, moduleIsoLinearEquiv,
    Iso.app_hom, SuperNatTrans.total, inductionComp_hom_app_one, add_zero]
  exact compForward_transform_outer J ha M z

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld
open MonoidalCategory
open scoped TensorProduct
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

private theorem whiskerRecast_map_heq {ι : Type*} {A B : ι → Type*}
    (F : ∀ i, A i → B i) {i j : ι} (h : i = j)
    {a : A i} {b : A j} (hab : HEq a b) : HEq (F i a) (F j b) := by
  cases h
  cases hab
  rfl

theorem appendComponent_rightContext_heq (v σ τ : List I)
    (a : End ((pres D Sc).obj (ob D σ))) :
    HEq (truncatedRightContext D Sc cutoff N τ (v ++ σ) (v ++ σ)
      (truncatedAppendComponent D Sc cutoff N a ⟨v⟩))
      (truncatedAppendComponent D Sc cutoff N
        (a ▷ (pres D Sc).obj (ob D τ)) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) a (𝟙 ((pres D Sc).obj (ob D τ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq (((pres D Sc).obj (ob D v) ◁ a) ▷ (pres D Sc).obj (ob D τ))
      ((pres D Sc).obj (ob D v) ◁ (a ▷ (pres D Sc).obj (ob D τ))) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact whiskerRecast_map_heq
    (A := fun w : List I => End ((pres D Sc).obj (ob D w)))
    (B := fun w : List I => TruncatedOld D Sc cutoff N w w)
    (fun w f => (truncatedIdeal D Sc cutoff N w w).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (List.append_assoc v σ τ) hh

theorem appendComponent_leftContext_heq (v σ τ : List I)
    (a : End ((pres D Sc).obj (ob D τ))) :
    HEq (truncatedAppendComponent D Sc cutoff N a ⟨v ++ σ⟩)
      (truncatedAppendComponent D Sc cutoff N
        ((pres D Sc).obj (ob D σ) ◁ a) ⟨v⟩) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D v))) (𝟙 ((pres D Sc).obj (ob D σ))) a
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  have hh : HEq ((pres D Sc).obj (ob D (v ++ σ)) ◁ a)
      ((pres D Sc).obj (ob D v) ◁ ((pres D Sc).obj (ob D σ) ◁ a)) := by
    apply (conj_eqToHom_iff_heq _ _
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))
      (congrArg (fun x => (pres D Sc).obj (ob D x)) (List.append_assoc v σ τ))).1
    rw [comp_eqToHom_iff] at h
    simp only [Category.assoc] at h
    exact h
  exact whiskerRecast_map_heq
    (A := fun w : List I => End ((pres D Sc).obj (ob D w)))
    (B := fun w : List I => TruncatedOld D Sc cutoff N w w)
    (fun w f => (truncatedIdeal D Sc cutoff N w w).mkQ
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f))
    (List.append_assoc v σ τ) hh

/-- Inner module whiskering equals right whiskering of the affine source. -/
theorem contentInductionComp_inner (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.mapComponent (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
        (BalancedInduction.transformComponent
          (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha) M) p z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_inner_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppendTo_supernatural D Sc cutoff N rfl rfl ha)
    (contentAppendTo_supernatural D Sc cutoff N h' h'
      (MonoidalSupercategory.whiskerRight_mem (R := k) ((pres D Sc).obj (ob D τ)) ha))
    (fun v => appendComponent_rightContext_heq D Sc cutoff N v.obj.word σ τ a) M z

/-- Outer module whiskering equals left whiskering of the affine source. -/
theorem contentInductionComp_outer (β : Multiset I) (σ τ : List I)
    (γ : Multiset I) (h : (β + (σ : Multiset I)) + (τ : Multiset I) = γ)
    (h' : β + ((σ ++ τ : List I) : Multiset I) = γ)
    {p : ZMod 2} {a : End ((pres D Sc).obj (ob D τ))}
    (ha : a ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β) (z : ContentCategory D Sc cutoff N γ) :
    (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap ∘ₗ
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h h ha)
        (BalancedInduction.induced (contentAppendTo D Sc cutoff N β σ _ rfl) M) z =
      BalancedInduction.transformLinear
        (contentAppendTo_supernatural D Sc cutoff N h' h'
          (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha)) M z ∘ₗ
      (moduleIsoLinearEquiv ((contentInductionComp D Sc cutoff N β σ τ γ h h').app M) z).toLinearMap := by
  exact BalancedInduction.compForward_outer_recast
    (contentAppendTo D Sc cutoff N β σ _ rfl)
    (contentAppendTo D Sc cutoff N (β + (σ : Multiset I)) τ γ h)
    (contentAppendTo D Sc cutoff N β (σ ++ τ) γ h')
    (contentAppend_comp_eq D Sc cutoff N β σ τ γ h h')
    (contentAppendTo_supernatural D Sc cutoff N h h ha)
    (contentAppendTo_supernatural D Sc cutoff N h' h'
      (MonoidalSupercategory.whiskerLeft_mem (R := k) ((pres D Sc).obj (ob D σ)) ha))
    (fun v => appendComponent_leftContext_heq D Sc cutoff N v.obj.word σ τ a) M z

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Common-content mixed braid and its source correction

`DeformedMixedBraid.md` §2, equations (4)–(5), for the induction operators
needed by `DeformedActionAssembly.md` §6. The two middle equal-colour
crossings carry minus signs. The contravariant transforms use the three
words with common content, not endomorphism substitutes. Their difference
is the signed source correction, with the residual outside-colour twist
on the entire kernel morphism. The ordered dotted polynomial comparison
with the original parameters is a separate obligation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentTripleTransform_tensor {β γ : Multiset I} {σ τ υ ω : List I}
    (hσ : β + (σ : Multiset I) = γ) (hτ : β + (τ : Multiset I) = γ)
    (hυ : β + (υ : Multiset I) = γ) (hω : β + (ω : Multiset I) = γ)
    {p q r : ZMod 2}
    {a : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    {b : (pres D Sc).obj (ob D τ) ⟶ (pres D Sc).obj (ob D υ)}
    {c : (pres D Sc).obj (ob D υ) ⟶ (pres D Sc).obj (ob D ω)}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ r)
    (M : ContentModules D Sc cutoff N β) (w : ContentCategory D Sc cutoff N γ)
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β ω γ hω).obj v ⟶ w) (m : M.obj v) :
    ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hσ hτ ha) M w).comp
      ((BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hτ hυ hb) M w).comp
        (BalancedInduction.transformLinear (contentAppendTo_supernatural D Sc cutoff N hυ hω hc) M w)))
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β ω γ hω) M.toFunctor v h m) =
    sign k (q*r + p*(q+r)) •
      BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ γ hσ) M.toFunctor v
        (contentAppendToComponent D Sc cutoff N hσ hω (a ≫ b ≫ c) v ≫
          twist k (p+(q+r)) h) m := by
  rw [BalancedInduction.transformLinear_comp, LinearMap.comp_smul,
    BalancedInduction.transformLinear_comp, smul_smul, ← sign_add,
    LinearMap.smul_apply, BalancedInduction.transformLinear_tensor]
  congr 2
  change (contentAppendToComponent D Sc cutoff N hσ hτ a v ≫
    contentAppendToComponent D Sc cutoff N hτ hυ b v ≫
    contentAppendToComponent D Sc cutoff N hυ hω c v) ≫ _ = _
  rw [contentAppendToComponent_comp D Sc cutoff N hτ hυ hω b hc,
    contentAppendToComponent_comp D Sc cutoff N hσ hτ hω a (comp_mem hb hc)]

theorem content_triple_iij (β : Multiset I) (i j : I) :
    β + ([i,i,j] : Multiset I) = β + ([i,j,i] : Multiset I) := by
  congr 1
  change i ::ₘ i ::ₘ j ::ₘ (0 : Multiset I) = i ::ₘ j ::ₘ i ::ₘ 0
  rw [Multiset.cons_swap i j]

theorem content_triple_jii (β : Multiset I) (i j : I) :
    β + ([j,i,i] : Multiset I) = β + ([i,j,i] : Multiset I) := by
  congr 1
  change j ::ₘ i ::ₘ i ::ₘ (0 : Multiset I) = i ::ₘ j ::ₘ i ::ₘ 0
  exact Multiset.cons_swap _ _ _

def contentTripleLeft (i j c : I) :
    (pres D Sc).obj (ob D [i,j,c]) ⟶ (pres D Sc).obj (ob D [j,i,c]) :=
  tripleCrossLeft D Sc i j c ⟨[], rfl⟩
def contentTripleRight (i j c : I) :
    (pres D Sc).obj (ob D [i,j,c]) ⟶ (pres D Sc).obj (ob D [i,c,j]) :=
  tripleCrossRight D Sc i j c ⟨[], rfl⟩
theorem contentTripleLeft_parity (i j c : I) :
    contentTripleLeft D Sc i j c ∈ parity (R := k) _ _ (D.parity i * D.parity j) :=
  tripleCrossLeft_parity D Sc i j c ⟨[], rfl⟩
theorem contentTripleRight_parity (i j c : I) :
    contentTripleRight D Sc i j c ∈ parity (R := k) _ _ (D.parity j * D.parity c) :=
  tripleCrossRight_parity D Sc i j c ⟨[], rfl⟩
def contentBraidCorrection (i j : I) : End ((pres D Sc).obj (ob D [i,j,i])) :=
  tripleBraidCorrection D Sc i j ⟨[], rfl⟩
theorem contentTriple_braid (i j : I) (hij : i ≠ j) :
    (contentTripleLeft D Sc i j i ≫ contentTripleRight D Sc j i i ≫ contentTripleLeft D Sc j i i) -
    (contentTripleRight D Sc i j i ≫ contentTripleLeft D Sc i i j ≫ contentTripleRight D Sc i i j) =
      contentBraidCorrection D Sc i j :=
  tripleCross_braid_correction D Sc i j hij ⟨[], rfl⟩

/-- Normalized mixed braid difference on one common content. -/
def contentMixedBraid (β : Multiset I) (i j : I)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :=
  let A := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_iij β i j)
      (contentTripleRight_parity D Sc i j i)) M w
  let B := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j)
      (content_triple_iij β i j) (contentTripleLeft_parity D Sc i i j)) M w
  let C := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_iij β i j) rfl
      (contentTripleRight_parity D Sc i i j)) M w
  let E := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N rfl (content_triple_jii β i j)
      (contentTripleLeft_parity D Sc i j i)) M w
  let F := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j)
      (content_triple_jii β i j) (contentTripleRight_parity D Sc j i i)) M w
  let G := BalancedInduction.transformLinear
    (contentAppendTo_supernatural D Sc cutoff N (content_triple_jii β i j) rfl
      (contentTripleLeft_parity D Sc j i i)) M w
  A.comp ((-B).comp C) - E.comp ((-F).comp G)

/-- The residual twist acts on the entire kernel, not just its affine factor. -/
theorem contentMixedBraid_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    contentMixedBraid D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor v h m) =
    sign k (D.parity i * D.parity j) •
      contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
        (contentBraidCorrection D Sc i j) := by
  let p := D.parity i
  let q := D.parity j
  have hdeg : p*q + (p*p + q*p) = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;>
      rcases parity_eq_zero_or_one q with hq | hq <;> simp [hp,hq]
  have hsign : (p*p)*(q*p) + (p*q)*(p*p + q*p) = p*q := by
    rcases parity_eq_zero_or_one p with hp | hp <;>
      rcases parity_eq_zero_or_one q with hq | hq <;> simp [hp,hq]
  unfold contentMixedBraid
  simp only [LinearMap.neg_comp, LinearMap.comp_neg, LinearMap.sub_apply, LinearMap.neg_apply]
  rw [contentTripleTransform_tensor, contentTripleTransform_tensor]
  simp only [mul_comm q p] at hdeg hsign
  simp only [show D.parity i = p from rfl, show D.parity j = q from rfl]
  simp only [mul_comm q p, hdeg, hsign]
  rw [sub_neg_eq_add, neg_add_eq_sub, ← smul_sub]
  congr 1
  change contentTensorEval D Sc cutoff N M w v (twist k p h) m _ -
    contentTensorEval D Sc cutoff N M w v (twist k p h) m _ = _
  rw [← map_sub, contentTriple_braid D Sc i j hij]
  all_goals first | exact contentTripleLeft_parity D Sc _ _ _ |
    exact contentTripleRight_parity D Sc _ _ _

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Ordered dotted correction for common-content mixed braid

`DeformedMixedBraid.md` §3, equations (6)–(10), and the mixed relation needed
by `DeformedActionAssembly.md` §6. Three arbitrary dot powers retain their
full residual twist. On the support forced by Sc the scalar signs agree
with parameterTwist Sc after reflecting the correction index. No dots are
commuted. The resulting linear-map identity has the original Sc leading
and interior coefficients and the order X₃^(r-1-l) X₂^s X₁^l.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Ordered three-power evaluation, with no even-block assumptions. -/
theorem contentInduction_three_powers {β : Multiset I} {σ : List I}
    {p q t : ZMod 2} {a b c : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ t)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (l s n : ℕ) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((contentInductionEndLinear D Sc cutoff N hc M w ^ n) *
      (contentInductionEndLinear D Sc cutoff N hb M w ^ s) *
      (contentInductionEndLinear D Sc cutoff N ha M w ^ l))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    sign k (p*(l/2 : ℕ) + q*(s/2 : ℕ) + t*(n/2 : ℕ) +
      (s : ZMod 2)*q*((l : ZMod 2)*p) +
      (n : ZMod 2)*t*((s : ZMod 2)*q + (l : ZMod 2)*p)) •
      contentTensorEval D Sc cutoff N M w v
        (twist k ((n : ZMod 2)*t + ((s : ZMod 2)*q + (l : ZMod 2)*p)) h) m
        (a ^ l * b ^ s * c ^ n) := by
  rw [Module.End.mul_apply, Module.End.mul_apply,
    contentInductionEndLinear_pow_tensor, map_smul, contentInductionEndLinear_pow_tensor,
    map_smul, map_smul, contentInductionEndLinear_pow_tensor]
  unfold contentTensorEval
  simp only [contentAppendToLinear_apply]
  simp only [twist_comp,
    twist_of_mem _ ((contentAppendTo_supernatural D Sc cutoff N rfl rfl
      (contentEnd_pow_parity D Sc ha l)).mem v),
    twist_of_mem _ ((contentAppendTo_supernatural D Sc cutoff N rfl rfl
      (contentEnd_pow_parity D Sc hb s)).mem v), map_smul, ← twist_add,
    Linear.smul_comp, Linear.comp_smul, BalancedInduction.tensor,
    ← TensorProduct.smul_tmul', smul_smul, ← sign_add]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  · congr 1
    ring
  congr 2
  change _ = contentAppendToComponent D Sc cutoff N rfl rfl (a^l*b^s*c^n) v ≫ _
  rw [← Category.assoc, contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _
    (contentEnd_pow_parity D Sc hb s), ← Category.assoc,
    contentAppendToComponent_comp D Sc cutoff N rfl rfl rfl _ (contentEnd_pow_parity D Sc ha l)]
  simp only [End.mul_def, Category.assoc]

/-- Arbitrary-exponent sign identity on the prescribed separate parity support. -/
theorem mixed_braid_sign_identity
    (p q : ZMod 2) (r s l a : ℕ)
    (hr : (r : ZMod 2) * p = 0)
    (hs : (s : ZMod 2) * q = 0)
    (hl : l < r) (ha : a = r - 1 - l) :
    p*q + p*(l : ZMod 2) +
      (p*(l/2 : ℕ) + q*(s/2 : ℕ) + p*(a/2 : ℕ) +
        p*q*(s : ZMod 2)*((l : ZMod 2)+(a : ZMod 2)) + p*(l : ZMod 2)*(a : ZMod 2)) =
    p*(a : ZMod 2) + (p*q + p*(r/2 : ℕ) + q*(s/2 : ℕ)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp
  · have hz : (2 : ZMod 2) = 0 := rfl
    have hr0 : (r : ZMod 2) = 0 := by simpa using hr
    have hrmod : r % 2 = 0 := by
      simpa using (ZMod.natCast_eq_natCast_iff' r 0 2).mp hr0
    have hsum : l + a + 1 = r := by omega
    have hh : l / 2 + a / 2 + 1 = r / 2 := by omega
    have hadd := congrArg (Nat.cast : ℕ → ZMod 2) hsum
    push_cast at hadd
    rw [hr0] at hadd
    have hhalf := congrArg (Nat.cast : ℕ → ZMod 2) hh
    push_cast at hhalf
    have hprod : (l : ZMod 2) * (a : ZMod 2) = 0 := by
      rcases parity_eq_zero_or_one (l : ZMod 2) with hl0 | hl1
      · simp [hl0]
      · rw [hl1, one_mul]
        rw [hl1] at hadd
        linear_combination hadd - hz
    have hcross : q*(s : ZMod 2)*((l : ZMod 2)+(a : ZMod 2)) = 0 := by
      rw [mul_comm q (s : ZMod 2), hs, zero_mul]
    simp only [one_mul, hcross, hprod, add_zero]
    linear_combination hadd + hhalf - ((a : ZMod 2) + 1) * hz

theorem mixed_braid_total_parity (p q : ZMod 2) (r s l : ℕ)
    (hr : (r : ZMod 2)*p = 0) (hs : (s : ZMod 2)*q = 0) (hl : l < r) :
    ((r-1-l : ℕ) : ZMod 2)*p + ((s : ZMod 2)*q + (l : ZMod 2)*p) = p := by
  have he : r - 1 - l + l + 1 = r := by omega
  have he' := congrArg (Nat.cast : ℕ → ZMod 2) he
  push_cast at he'
  have hz : (2 : ZMod 2) = 0 := rfl
  linear_combination p * he' + hr + hs - p * hz

/-- Supported intermediate calculation; support is derived from Sc in the polynomial theorem. -/
theorem contentInduction_three_supported {β : Multiset I} {σ : List I}
    {p q : ZMod 2} {a b c : End ((pres D Sc).obj (ob D σ))}
    (ha : a ∈ parity (R := k) _ _ p) (hb : b ∈ parity (R := k) _ _ q)
    (hc : c ∈ parity (R := k) _ _ p)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (r s l : ℕ) (hr : (r : ZMod 2)*p = 0) (hs : (s : ZMod 2)*q = 0) (hl : l < r)
    (d : k) (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β σ _ rfl).obj v ⟶ w) (m : M.obj v) :
    ((sign k (p*(q+(l : ZMod 2))) * d) •
      ((contentInductionEndLinear D Sc cutoff N hc M w ^ (r-1-l)) *
        (contentInductionEndLinear D Sc cutoff N hb M w ^ s) *
        (contentInductionEndLinear D Sc cutoff N ha M w ^ l)))
        (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β σ _ rfl) M.toFunctor v h m) =
    sign k (p*q) • contentTensorEval D Sc cutoff N M w v (twist k p h) m
      ((sign k (p*(q+((r-1-l : ℕ) : ZMod 2))) *
        (sign k (p*q+p*(r/2 : ℕ)+q*(s/2 : ℕ)) * d)) •
        (a^l*b^s*c^(r-1-l))) := by
  rw [LinearMap.smul_apply, contentInduction_three_powers,
    mixed_braid_total_parity p q r s l hr hs hl, map_smul, smul_smul, smul_smul]
  congr 1
  let n := r-1-l
  have hp : p*p = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;> simp [hp]
  have he := mixed_braid_sign_identity p q r s l n hr hs hl rfl
  have hsign : sign k (p*(q+(l : ZMod 2))) *
      sign k (p*(l/2 : ℕ)+q*(s/2 : ℕ)+p*(n/2 : ℕ)+
        (s : ZMod 2)*q*((l : ZMod 2)*p)+(n : ZMod 2)*p*((s : ZMod 2)*q+(l : ZMod 2)*p)) =
      sign k (p*q) * (sign k (p*(q+(n : ZMod 2))) *
        sign k (p*q+p*(r/2 : ℕ)+q*(s/2 : ℕ))) := by
    simp only [← sign_add]
    congr 1
    have hz : (2 : ZMod 2) = 0 := rfl
    linear_combination he + (n : ZMod 2)*(l : ZMod 2)*(hp) - p*q*hz
  calc
    _ = (sign k (p*(q+(l : ZMod 2))) *
      sign k (p*(l/2 : ℕ)+q*(s/2 : ℕ)+p*(n/2 : ℕ)+
        (s : ZMod 2)*q*((l : ZMod 2)*p)+(n : ZMod 2)*p*((s : ZMod 2)*q+(l : ZMod 2)*p))) * d := by ring
    _ = _ := by rw [hsign]; ring

theorem contentTripleDot_one_parity (i j : I) :
    dotE D Sc [i,j,i] 1 ∈ parity (R := k) _ _ (D.parity j) := by
  simpa using positionedDot_parity D Sc [i] [i] j

theorem contentTripleDot_two_parity (i j : I) :
    dotE D Sc [i,j,i] 2 ∈ parity (R := k) _ _ (D.parity i) := by
  simpa using positionedDot_parity D Sc [i,j] [] i

def contentMixedDotSum (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I))) :=
  let A := contentInductionEndLinear D Sc cutoff N (firstDot_parity D Sc i [j,i]) M w
  let B := contentInductionEndLinear D Sc cutoff N (contentTripleDot_one_parity D Sc i j) M w
  let C := contentInductionEndLinear D Sc cutoff N (contentTripleDot_two_parity D Sc i j) M w
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) • (C^(r-1-l)*B^s*A^l)

def contentMixedSourceSum (i j : I) (r s : ℕ) (d : k) : End ((pres D Sc).obj (ob D [i,j,i])) :=
  ∑ l ∈ Finset.range r, (SKM.zsign k (D.parity i*(D.parity j+l))*d) •
    (dotE D Sc [i,j,i] 0 ^ (r-1-l) * dotE D Sc [i,j,i] 1 ^ s * dotE D Sc [i,j,i] 2 ^ l)

theorem contentMixedDotSum_tensor (β : Multiset I) (i j : I) (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2)*D.parity i = 0 ∧ (s : ZMod 2)*D.parity j = 0)
    (M : ContentModules D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D Sc cutoff N β)
    (h : (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl).obj v ⟶ w) (m : M.obj v) :
    contentMixedDotSum D Sc cutoff N β i j r s d M w
      (BalancedInduction.tensor (contentAppendTo D Sc cutoff N β [i,j,i] _ rfl) M.toFunctor v h m) =
    sign k (D.parity i*D.parity j) •
      contentTensorEval D Sc cutoff N M w v (twist k (D.parity i) h) m
        (contentMixedSourceSum D Sc i j r s
          (SKM.zsign k (parameterSignExponent D i j r s)*d)) := by
  by_cases hd0 : d = 0
  · simp [contentMixedDotSum, contentMixedSourceSum, hd0]
  obtain ⟨hr,hs⟩ := hd hd0
  unfold contentMixedDotSum contentMixedSourceSum
  rw [← Finset.sum_range_reflect (fun l =>
    (SKM.zsign k (D.parity i*(D.parity j+l)) *
      (SKM.zsign k (parameterSignExponent D i j r s)*d)) •
      (dotE D Sc [i,j,i] 0 ^ (r-1-l) * dotE D Sc [i,j,i] 1 ^ s * dotE D Sc [i,j,i] 2 ^ l)) r]
  simp only [LinearMap.sum_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have he : r-1-(r-1-l) = l := by omega
  rw [he]
  simpa only [sign_eq_zsign, parameterSignExponent] using
    contentInduction_three_supported D Sc cutoff N (firstDot_parity D Sc i [j,i])
      (contentTripleDot_one_parity D Sc i j) (contentTripleDot_two_parity D Sc i j)
      M w r s l hr hs hl' d v h m

theorem contentBraidCorrection_eq_sums (i j : I) :
    contentBraidCorrection D Sc i j =
      contentMixedSourceSum D Sc i j (D.dn i j) 0 (Sc.t i j : k) +
      ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
        contentMixedSourceSum D Sc i j r s (Sc.s i j r s) := by
  simp only [contentBraidCorrection, tripleBraidCorrection, contentMixedSourceSum,
    tripleWord, List.nil_append, List.length_nil, zero_add, pow_zero, mul_one]
  rfl

/-- The prescribed Sc correction, in ordered powers of the three induction dots. -/
def contentMixedBraidPolynomial (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :=
  contentMixedDotSum D (parameterTwist D Sc) cutoff N β i j (D.dn i j) 0 (Sc.t i j : k) M w +
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      contentMixedDotSum D (parameterTwist D Sc) cutoff N β i j r s (Sc.s i j r s) M w

theorem contentMixedBraidPolynomial_tensor (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I)))
    (v : ContentCategory D (parameterTwist D Sc) cutoff N β)
    (h : (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j,i] _ rfl).obj v ⟶ w)
    (m : M.obj v) :
    contentMixedBraidPolynomial D Sc cutoff N β i j M w
      (BalancedInduction.tensor (contentAppendTo D (parameterTwist D Sc) cutoff N β [i,j,i] _ rfl)
        M.toFunctor v h m) =
    sign k (D.parity i*D.parity j) •
      contentTensorEval D (parameterTwist D Sc) cutoff N M w v (twist k (D.parity i) h) m
        (contentBraidCorrection D (parameterTwist D Sc) i j) := by
  have ht := contentMixedDotSum_tensor D (parameterTwist D Sc) cutoff N β i j
    (D.dn i j) 0 (Sc.t i j : k)
    (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩) M w v h m
  have hs (r s : ℕ) := contentMixedDotSum_tensor D (parameterTwist D Sc) cutoff N β i j
    r s (Sc.s i j r s) (fun hc => elvParameter_support D Sc hc) M w v h m
  unfold contentMixedBraidPolynomial
  rw [contentBraidCorrection_eq_sums]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, smul_add,
    Finset.smul_sum, ht, hs, CyclotomicAction.parameterTwist_t_of_ne D Sc hij,
    CyclotomicAction.parameterTwist_s]

/-- The normalized mixed braid equals the prescribed ordered dotted polynomial. -/
theorem contentMixedBraid_polynomial_linear (β : Multiset I) {i j : I} (hij : i ≠ j)
    (M : ContentModules D (parameterTwist D Sc) cutoff N β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff N (β + ([i,j,i] : Multiset I))) :
    contentMixedBraid D (parameterTwist D Sc) cutoff N β i j M w =
      contentMixedBraidPolynomial D Sc cutoff N β i j M w := by
  apply BalancedInduction.hom_ext
  intro v h m
  rw [contentMixedBraid_tensor D _ cutoff N β hij,
    contentMixedBraidPolynomial_tensor D Sc cutoff N β hij]

end OddMath.QuiverHecke.ELVOld
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
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
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
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Tensor formula for the raising-pair comparison

This retains the content cast needed in DeformedActionAssembly.md §6.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

theorem contentPair_sum (β : Multiset I) (i j : I) :
    β + ([i,j] : Multiset I) = (β + ([i] : Multiset I)) + ([j] : Multiset I) := by
  rw [add_assoc]
  rfl

section Pair
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppendTo D Sc cutoff N δ₁ [j] δ₂ rfl
local notation "A" => contentAppendTo D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
local notation "e" => contentAppend_comp_eq D Sc cutoff N β [i] [j] δ₂ rfl (contentPair_sum β i j)

end Pair
end OddMath.QuiverHecke.ELVOld
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
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
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
namespace OddMath.QuiverHecke.ELVOld
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

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Missing-colour support and the zero predecessor boundary

DeformedMatrixComparison (4) at an output content containing no i has zero
lower E/F term. Full-content extension is zero after restriction by append i,
so the principal shifted source coordinate is zero. Off-diagonal Cartan signs
also give the required nonnegative height, including the genuinely empty
output content. This is separate from an empty predecessor with output[i].
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

/-- A balanced induction coend of zero input values has only the zero vector. -/
theorem obj_subsingleton_of_values_subsingleton
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] (J : C ⥤ A) (M : C ⥤ SVec k)
    (hM : ∀ s, Subsingleton (M.obj s)) (w : A) : Subsingleton (Obj J M w) := by
  have hz : (LinearMap.id : Obj J M w →ₗ[k] Obj J M w) = 0 := by
    apply hom_ext J M
    intro s g b
    change tensor J M s g b = 0
    rw [(hM s).elim b 0, tensor_zero_right]
  exact ⟨fun x y => (LinearMap.congr_fun hz x).trans (LinearMap.congr_fun hz y).symm⟩

end OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

private theorem absentCartanSum_nonpos (i : I) :
    ∀ γ : List I, i ∉ γ → (γ.map (fun j => D.h i (D.α j))).sum ≤ 0 := by
  intro γ
  induction γ with
  | nil => intro _; simp only [List.map_nil, List.sum_nil, le_refl]
  | cons j γ ih =>
    intro hi
    have hij : i ≠ j := fun h => hi (by simp only [h, List.mem_cons, true_or])
    have hγ : i ∉ γ := fun hm => hi (List.mem_cons_of_mem j hm)
    have hj := D.d_nonneg hij
    dsimp only [SKM.Datum.d] at hj
    have hj' : D.h i (D.α j) ≤ 0 := neg_nonneg.mp hj
    simpa only [List.map_cons, List.sum_cons] using add_nonpos hj' (ih hγ)

/-- Missing i forces nonnegative Cartan height, for every cutoff and also γ=[]. -/
theorem contentCrossingHeight_nonneg_of_not_mem (cutoff : I → ℕ) (γ : List I) (i : I)
    (hi : i ∉ γ) : 0 ≤ contentCrossingHeight D cutoff i (γ : Multiset I) := by
  rw [contentCrossingHeight_coe]
  have hs := absentCartanSum_nonpos D i γ hi
  have hc : (0 : ℤ) ≤ cutoff i := Int.natCast_nonneg _
  omega

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
include hi
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "J" => append D Sc cutoff i
local notation "G" => induced Q N

/-- An appended i can never lie in an output block lacking i. -/
theorem oldContentAppend_offContent_of_not_mem (v : OldCategory D Sc cutoff) :
    (((J).obj v).word : Multiset I) ≠ (γ : Multiset I) := by
  intro he
  have hm : i ∈ (((J).obj v).word : Multiset I) := by
    change i ∈ (v.word ++ [i] : List I)
    simp only [List.mem_append, List.mem_singleton, or_true]
  have hmγ : i ∈ (γ : Multiset I) := by
    rw [← he]
    exact hm
  exact hi hmγ

/-- The actual append restriction of the full-content extension is zero on
all old words, not just on the chosen output object. -/
theorem oldContentRestriction_subsingleton_of_not_mem (v : OldCategory D Sc cutoff) :
    Subsingleton (((restriction J).obj G).obj v) :=
  oldContentExtension_supported D Sc cutoff γ N ((J).obj v)
    (oldContentAppend_offContent_of_not_mem D Sc cutoff γ i hi v)

/-- The actual lower E/F coend is zero throughout a missing-colour block. -/
theorem oldContentIndRes_subsingleton_of_not_mem (w : OldCategory D Sc cutoff) :
    Subsingleton ((induced J ((restriction J).obj G)).obj w) :=
  obj_subsingleton_of_values_subsingleton J ((restriction J).obj G).toFunctor
    (oldContentRestriction_subsingleton_of_not_mem D Sc cutoff γ i hi N) w

local instance absentColourGlobalPi : PiSupercategory k
    (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) := supermodulePiSupercategory

/-- The principal canonical source slot of the GIVEN global unit matrix is
zero; it can be dropped without an inverse or compatibility hypothesis. -/
theorem oldContentUnitPrincipal_subsingleton_of_not_mem
    (b : ℕ) (w : OldCategory D Sc cutoff) :
    Subsingleton ((unitMatrixFamily D Sc cutoff i G b none).obj w) := by
  have := oldContentIndRes_subsingleton_of_not_mem D Sc cutoff γ i hi N w
  exact Function.Injective.subsingleton
    (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) (D.parity i)).iso
      (induced J ((restriction J).obj G))) w).injective

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The unit matrix at a missing-colour output

Brundan--Ellis (1.13), and DeformedMatrixComparison (4), at output content
containing no i. The lower E/F summand is zero. Dropping that principal
coordinate from the GIVEN old matrix inverse gives precisely the finite
family of prescribed shifted unit-dot columns, including empty output.
Comparison with the ordinary scalar probe is separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open BalancedInduction OddMath.FiniteSuperspace
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I) (hi : i ∉ γ)
  (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
local notation "G" => induced (oldContentInclusion D Sc cutoff γ) N
local notation "count" => contentUnitCount D cutoff i (γ : Multiset I)

/-- The remaining canonical shifted value coordinates after removing zero E/F. -/
def missingColourUnitSource (w : OldContentCategory D Sc cutoff γ) : SVec k :=
  withoutPrincipal (fun a => (unitMatrixFamily D Sc cutoff i G count a).obj w.obj)

/-- The GIVEN global unit inverse, with only the proved-zero principal
coordinate removed. No matrix compatibility premise is required. -/
def missingColourUnitMatrixIso (w : OldContentCategory D Sc cutoff γ) :
    missingColourUnitSource D Sc cutoff γ i N w ≅ mateTargetSpace D Sc cutoff i G w.obj :=
  (SVec.isoOfLinearEquiv (dropZeroPrincipalEquiv
    (fun a => (unitMatrixFamily D Sc cutoff i G count a).obj w.obj)
    (oldContentUnitPrincipal_subsingleton_of_not_mem D Sc cutoff γ i hi N count w.obj))).symm ≪≫
  contentUnitMatrixComponentIso D Sc cutoff G i γ
    (contentCrossingHeight_nonneg_of_not_mem D cutoff γ i hi) w

/-- The forward field is literally the finite assembly of the GIVEN shifted
unit-dot columns. The zero principal mate column has disappeared. -/
theorem missingColourUnitMatrixIso_hom (w : OldContentCategory D Sc cutoff γ) :
    (missingColourUnitMatrixIso D Sc cutoff γ i hi N w).hom =
      assembleColumns
        (fun r : Fin count => (unitMatrixFamily D Sc cutoff i G count (some r)).obj w.obj)
        (mateTargetSpace D Sc cutoff i G w.obj)
        (fun r => (unitMatrixEntry D Sc cutoff i G count (some r)).total w.obj) := by
  change (SVec.isoOfLinearEquiv (dropZeroPrincipalEquiv _ _)).inv ≫
    (contentUnitMatrixComponentIso D Sc cutoff G i γ _ w).hom = _
  rw [contentUnitMatrixComponentIso_hom]
  exact dropZeroPrincipalEquiv_columns _ _ _ _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
end

end

section

/-! # Invertible component charts for the chosen content matrices

DeformedMatrixComparison (2), (4) transports the prescribed finite matrices
through the selected preceding and following E/F comparisons. These are
linear equivalences obtained from the given module isomorphisms, without
an invertibility hypothesis on any comparison map.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
namespace BalancedInduction
private theorem restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C)
    (z : ((restriction Q).obj M).obj t) :
    ((restriction Q).map f).total t z = f.total (Q.obj t) z := rfl
end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i

/-- The actual preceding E/F chart is a linear equivalence on its full coend. -/
def oldContentEFLinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor t ≃ₗ[k]
      BalancedInduction.Obj J ((BalancedInduction.restriction J).obj
        (BalancedInduction.induced Q₁ N)).toFunctor t.obj :=
  moduleIsoLinearEquiv ((oldContentEFRestrictionNaturalIso D Sc cutoff ν i).app N) t

/-- Its forward map is exactly the selected chart used in the mate comparison. -/
theorem oldContentEFLinearEquiv_hom
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    (oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap =
      oldContentEFRestrictionLinear D Sc cutoff ν i N t := rfl

/-- The actual following F/E chart is a linear equivalence on the full coend. -/
def oldContentFELinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t) ≃ₗ[k]
      BalancedInduction.Obj J (BalancedInduction.induced Q₁ N).toFunctor ((J).obj t.obj) :=
  moduleIsoLinearEquiv ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).app N) t

/-- The value summand uses precisely the fully faithful inclusion unit. -/
def oldContentValueLinearEquiv
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) :
    N.obj t ≃ₗ[k] BalancedInduction.Obj Q₁ N.toFunctor t.obj :=
  moduleIsoLinearEquiv (oldContentExtensionUnitIso D Sc cutoff (i :: ν) N) t

/-- The following-composite equivalence is the very same selected map
appearing on the output side of the prescribed mate tensor square. -/
theorem oldContentFELinearEquiv_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (z : BalancedInduction.Obj J₁ N.toFunctor ((J₁).obj t)) :
    oldContentFELinearEquiv D Sc cutoff ν i N t z =
      oldContentAppendRestrictionLinear D Sc cutoff (i :: ν) i N ((J₁).obj t) z := by
  change ((oldContentFERestrictionNaturalIso D Sc cutoff (i :: ν) i).hom.app N).total t z = _
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact BalancedInduction.restriction_total_apply J₁
    (oldContentAppendRestrictionIso D Sc cutoff (i :: ν) i N).hom t z

/-- The value equivalence inserts the literal identity tensor. -/
theorem oldContentValueLinearEquiv_apply
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (b : N.obj t) :
    oldContentValueLinearEquiv D Sc cutoff ν i N t b =
      BalancedInduction.tensor Q₁ N.toFunctor t (𝟙 t.obj) b := by
  change (BalancedInduction.fullyFaithfulUnitIso Q₁ N).hom.total t b = _
  rw [BalancedInduction.fullyFaithfulUnitIso_hom]
  exact BalancedInduction.unit_total_apply Q₁ N t b

/-- The genuine source and target charts carry the prescribed content mate
to the literal first old matrix entry on every balanced generator. -/
theorem oldContentMatrixCharts_mate_tensor
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (s : OldContentCategory D Sc cutoff ν)
    (t : OldContentCategory D Sc cutoff (i :: ν))
    (g : (J).obj s.obj ⟶ t.obj) (b : N.obj ((J₀).obj s)) :
    (oldContentFELinearEquiv D Sc cutoff ν i N t).toLinearMap
      (BalancedInduction.orderedGridMateLinear J₀ J₁
        (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
        (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b)) =
    (matrixMateComponent D Sc cutoff i (BalancedInduction.induced Q₁ N)).total t.obj
      ((oldContentEFLinearEquiv D Sc cutoff ν i N t).toLinearMap
        (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b)) := by
  rw [oldContentEFLinearEquiv_hom]
  have he := oldContentFELinearEquiv_apply D Sc cutoff ν i N t
    (BalancedInduction.orderedGridMateLinear J₀ J₁
      (oldContentEqualCross_supernatural D Sc cutoff ν i) N t
      (BalancedInduction.tensor J₀ ((BalancedInduction.restriction J₀).obj N).toFunctor s g b))
  have hm := oldContentAppendRestrictionLinear_mate_tensor D Sc cutoff ν i N s t g b
  exact he.trans hm

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Prescribed dotted columns under chosen content charts

DeformedMatrixComparison (4), (5) requires the given ordinary unit/dot
fields through the selected content comparisons. All dot powers are
retained before applying the canonical finite parity coordinates. The
corresponding cap-row comparison remains separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private theorem unitDotLinear_apply_power
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    unitDotLinear J hα M n w b =
      ((transformLinear hα M (J.obj w) : Module.End k (Obj J M.toFunctor (J.obj w))) ^ n)
        (unit J M.toFunctor w b) := rfl
private theorem unitDotLinear_intertwine
    {k C A W : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommMonoid W] [Module k W]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : C)
    (L : Obj J M.toFunctor (J.obj w) →ₗ[k] W) (g : Module.End k W)
    (hd : L ∘ₗ transformLinear hα M (J.obj w) = g ∘ₗ L) (n : ℕ) (b : M.obj w) :
    L (unitDotLinear J hα M n w b) = (g ^ n) (L (unit J M.toFunctor w b)) := by
  exact LinearMap.congr_fun (intertwine_pow _ _ _ hd n) (unit J M.toFunctor w b)

end BalancedInduction

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (ν : List I) (i : I)
local notation "J₀" => oldContentAppend D Sc cutoff ν i
local notation "J₁" => oldContentAppend D Sc cutoff (i :: ν) i
local notation "Q₁" => oldContentInclusion D Sc cutoff (i :: ν)
local notation "J" => append D Sc cutoff i
local notation "d₁" => oldContentAppendDot_supernatural D Sc cutoff (i :: ν) i
local notation "d" => oldAppendDot_supernatural D Sc cutoff i

/-- The old matrix's given unit field is literally the generic ordinary
unit/dot column used by the changing-content grid. -/
theorem moduleUnitColumn_eq_unitDotColumn
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    moduleUnitColumn D Sc cutoff i M n = unitDotColumn J d M n := rfl

/-- The old matrix's given cap field is literally the generic ordinary
dot/counit row; no normalization change is made. -/
theorem moduleCapRow_eq_capDotRow
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (n : ℕ) :
    moduleCapRow D Sc cutoff i M n = capDotRow J d M n := rfl

/-- Every prescribed unit/dot column is transported through the selected
following E/F and value charts, with no rescaling. -/
theorem oldContentFELinearEquiv_unitDot
    (N : Superfunctor k (OldContentCategory D Sc cutoff (i :: ν)) (SVec k))
    (t : OldContentCategory D Sc cutoff (i :: ν)) (n : ℕ) (b : N.obj t) :
    oldContentFELinearEquiv D Sc cutoff ν i N t (unitDotLinear J₁ d₁ N n t b) =
      unitDotLinear J d (induced Q₁ N) n t.obj
        (oldContentValueLinearEquiv D Sc cutoff ν i N t b) := by
  let g := inductionDot D Sc cutoff i (induced Q₁ N) ((J₁).obj t).obj
  have hd := oldContentAppendRestrictionIso_dot D Sc cutoff (i :: ν) i N ((J₁).obj t)
  have hp := BalancedInduction.unitDotLinear_intertwine J₁ d₁ N t _ _ hd n b
  have hu := oldContentAppendRestrictionIso_unit D Sc cutoff (i :: ν) i N t b
  have hv := oldContentValueLinearEquiv_apply D Sc cutoff ν i N t b
  change oldContentValueLinearEquiv D Sc cutoff ν i N t b = unit Q₁ N.toFunctor t b at hv
  have hunit := congrArg (fun x => (g ^ n) x) hu
  have hvalue := congrArg (fun x => (g ^ n) (unit J (induced Q₁ N).toFunctor t.obj x)) hv
  have he := oldContentFELinearEquiv_apply D Sc cutoff ν i N t
    (unitDotLinear J₁ d₁ N n t b)
  have hraw := hp.trans (hunit.trans hvalue.symm)
  have ht := BalancedInduction.unitDotLinear_apply_power J d (induced Q₁ N) n t.obj
    (oldContentValueLinearEquiv D Sc cutoff ν i N t b)
  dsimp only [g, inductionDot] at hraw
  dsimp only [oldContentAppend] at he hraw ht ⊢
  have hr := hraw.trans ht.symm
  have hfinal := he.trans hr
  exact hfinal

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Following E/F and value charts on arbitrary output content

DeformedMatrixComparison (4) at missing-colour and empty outputs needs only
the following E/F chart and value chart. Unlike the two-letter grid, these
charts require no predecessor content or occurrence of the moving colour.
They transport all prescribed unscaled unit/dot columns.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor BalancedInduction
universe u
namespace BalancedInduction
private theorem contentUpper_restriction_total_apply
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (Q : C ⥤ A) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (t : C)
    (z : ((restriction Q).obj M).obj t) :
    ((restriction Q).map f).total t z = f.total (Q.obj t) z := rfl
private theorem unitDotLinear_apply_power_2
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    unitDotLinear J hα M n w b =
      ((transformLinear hα M (J.obj w) : Module.End k (Obj J M.toFunctor (J.obj w))) ^ n)
        (unit J M.toFunctor w b) := rfl
private theorem unitDotLinear_intertwine_2
    {k C A W : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    [AddCommMonoid W] [Module k W]
    (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) (w : C)
    (L : Obj J M.toFunctor (J.obj w) →ₗ[k] W) (g : Module.End k W)
    (hd : L ∘ₗ transformLinear hα M (J.obj w) = g ∘ₗ L) (n : ℕ) (b : M.obj w) :
    L (unitDotLinear J hα M n w b) = (g ^ n) (L (unit J M.toFunctor w b)) := by
  exact LinearMap.congr_fun (intertwine_pow _ _ _ hd n) (unit J M.toFunctor w b)

end BalancedInduction
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (γ : List I) (i : I)
local notation "K" => oldContentAppend D Sc cutoff γ i
local notation "Q" => oldContentInclusion D Sc cutoff γ
local notation "J" => append D Sc cutoff i
local notation "dK" => oldContentAppendDot_supernatural D Sc cutoff γ i
local notation "dJ" => oldAppendDot_supernatural D Sc cutoff i
variable (N : Superfunctor k (OldContentCategory D Sc cutoff γ) (SVec k))
local notation "G" => induced Q N

/-- The selected following F/E equivalence requires no preceding colour. -/
def oldContentFEChart (t : OldContentCategory D Sc cutoff γ) :
    Obj K N.toFunctor ((K).obj t) ≃ₗ[k] Obj J (G).toFunctor ((J).obj t.obj) :=
  moduleIsoLinearEquiv ((oldContentFERestrictionNaturalIso D Sc cutoff γ i).app N) t

/-- The value chart is the fully faithful inclusion unit on arbitrary output. -/
def oldContentValueChart (t : OldContentCategory D Sc cutoff γ) :
    N.obj t ≃ₗ[k] Obj Q N.toFunctor t.obj :=
  moduleIsoLinearEquiv (oldContentExtensionUnitIso D Sc cutoff γ N) t

theorem oldContentFEChart_apply (t : OldContentCategory D Sc cutoff γ)
    (z : Obj K N.toFunctor ((K).obj t)) :
    oldContentFEChart D Sc cutoff γ i N t z =
      oldContentAppendRestrictionLinear D Sc cutoff γ i N ((K).obj t) z := by
  change ((oldContentFERestrictionNaturalIso D Sc cutoff γ i).hom.app N).total t z = _
  rw [oldContentFERestrictionNaturalIso_hom_app]
  exact BalancedInduction.contentUpper_restriction_total_apply K
    (oldContentAppendRestrictionIso D Sc cutoff γ i N).hom t z

theorem oldContentValueChart_apply (t : OldContentCategory D Sc cutoff γ) (b : N.obj t) :
    oldContentValueChart D Sc cutoff γ N t b = tensor Q N.toFunctor t (𝟙 t.obj) b := by
  change (fullyFaithfulUnitIso Q N).hom.total t b = _
  rw [fullyFaithfulUnitIso_hom]
  exact unit_total_apply Q N t b

/-- Every unscaled dotted unit column is preserved, including genuine empty
output and content in which i is absent. -/
theorem oldContentFEChart_unitDot (t : OldContentCategory D Sc cutoff γ) (n : ℕ) (b : N.obj t) :
    oldContentFEChart D Sc cutoff γ i N t (unitDotLinear K dK N n t b) =
      unitDotLinear J dJ G n t.obj (oldContentValueChart D Sc cutoff γ N t b) := by
  let g := inductionDot D Sc cutoff i G ((K).obj t).obj
  have hd := oldContentAppendRestrictionIso_dot D Sc cutoff γ i N ((K).obj t)
  have hp := BalancedInduction.unitDotLinear_intertwine K dK N t _ _ hd n b
  have hu := oldContentAppendRestrictionIso_unit D Sc cutoff γ i N t b
  have hv := oldContentValueChart_apply D Sc cutoff γ N t b
  change oldContentValueChart D Sc cutoff γ N t b = unit Q N.toFunctor t b at hv
  have hunit := congrArg (fun x => (g ^ n) x) hu
  have hvalue := congrArg (fun x => (g ^ n) (unit J (G).toFunctor t.obj x)) hv
  have he := oldContentFEChart_apply D Sc cutoff γ i N t (unitDotLinear K dK N n t b)
  have hraw := hp.trans (hunit.trans hvalue.symm)
  have ht := BalancedInduction.unitDotLinear_apply_power J dJ G n t.obj
    (oldContentValueChart D Sc cutoff γ N t b)
  dsimp only [g, inductionDot] at hraw
  dsimp only [oldContentAppend] at he hraw ht ⊢
  exact he.trans (hraw.trans ht.symm)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The ordered three-dot correction with the original scalar parameters

Brundan--Ellis (1.9), repeated outer colour. Retain the source correction
as an ordered polynomial in three arbitrary endomorphisms, before any
selected module chart or weight evaluation is substituted.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X)

/-- The ordered summand of the three-dot correction. -/
def tripleDotCorrectionSum {R : Type*} [Ring R] [Algebra k R]
    (i j : I) (r s : ℕ) (d : k) (A B C : R) : R :=
  ∑ t ∈ Finset.range r, (SKM.zsign k (D.parity i * (D.parity j + t)) * d) •
    (C ^ (r - 1 - t) * B ^ s * A ^ t)

/-- The original Sc correction, with all three operator orders retained. -/
def tripleDotCorrectionPolynomial {R : Type*} [Ring R] [Algebra k R]
    (Sc : SKM.Scalars D k) (i j : I) (A B C : R) : R :=
  tripleDotCorrectionSum D i j (D.dn i j) 0 (Sc.t i j : k) A B C +
    ∑ r ∈ Finset.range (D.dn i j), ∑ s ∈ Finset.range (D.dn j i),
      tripleDotCorrectionSum D i j r s (Sc.s i j r s) A B C

/-- Algebra maps preserve the ordered summand; no commutativity of the three operators is assumed. -/
theorem tripleDotCorrectionSum_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (φ : R →ₐ[k] S) (i j : I) (r s : ℕ) (d : k) (A B C : R) :
    φ (tripleDotCorrectionSum D i j r s d A B C) =
      tripleDotCorrectionSum D i j r s d (φ A) (φ B) (φ C) := by
  simp only [tripleDotCorrectionSum, map_sum, map_smul, map_mul, map_pow]

/-- Algebra maps retain the ORIGINAL Sc coefficients and all operator orders. -/
theorem tripleDotCorrectionPolynomial_map
    {R S : Type*} [Ring R] [Algebra k R] [Ring S] [Algebra k S]
    (Sc : SKM.Scalars D k) (φ : R →ₐ[k] S) (i j : I) (A B C : R) :
    φ (tripleDotCorrectionPolynomial D Sc i j A B C) =
      tripleDotCorrectionPolynomial D Sc i j (φ A) (φ B) (φ C) := by
  simp only [tripleDotCorrectionPolynomial, map_add, map_sum, tripleDotCorrectionSum_map]

/-- Exact binding to the checked canonical-content correction: the acting
scalars are parameterTwist Sc, while the polynomial coefficients are Sc. -/
theorem contentMixedBraidPolynomial_eq_ordered
    (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ) (β : Multiset I) (i j : I)
    (M : ContentModules D (parameterTwist D Sc) cutoff bound β)
    (w : ContentCategory D (parameterTwist D Sc) cutoff bound (β + ([i,j,i] : Multiset I))) :
    contentMixedBraidPolynomial D Sc cutoff bound β i j M w =
      tripleDotCorrectionPolynomial D Sc i j
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (firstDot_parity D (parameterTwist D Sc) i [j,i]) M w)
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (contentTripleDot_one_parity D (parameterTwist D Sc) i j) M w)
        (contentInductionEndLinear D (parameterTwist D Sc) cutoff bound
          (contentTripleDot_two_parity D (parameterTwist D Sc) i j) M w) := by
  rfl

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The ordered correction as dotted whiskerings

Brundan--Ellis (1.9). The noncommutative three-position polynomial is
exactly the prescribed dotted correction, in every two-supercategory.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c d : B} (F : a ⟶ b) (G : b ⟶ c) (H : c ⟶ d)
  (x : End F) (y : End G) (z : End H)

/-- The exact correction sum of the Rouquier multicolour braid field,
with every dot power in its prescribed position and order. -/
theorem tripleDotCorrectionPolynomial_whiskers :
    tripleDotCorrectionPolynomial (R := End (F ≫ G ≫ H)) D Sc i j
      (x ▷ (G ≫ H)) (F ◁ (y ▷ H)) (F ◁ G ◁ z) =
    ∑ s ∈ Finset.range (D.dn i j),
      (SKM.zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
        (SKM.rouquierPower x s ▷ (G ≫ H) ≫ F ◁ G ◁ SKM.rouquierPower z (D.dn i j - 1 - s)) +
    ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
      (SKM.zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
        (SKM.rouquierPower x s ▷ (G ≫ H) ≫ F ◁ (SKM.rouquierPower y q ▷ H) ≫
          F ◁ G ◁ SKM.rouquierPower z (p - 1 - s)) := by
  have hX (n : ℕ) := SKM.whiskerRight_rouquierPower (k := k) (B := B) x (G ≫ H) n
  have hY (n : ℕ) : (show End (F ≫ G ≫ H) from F ◁ (y ▷ H)) ^ n =
      F ◁ (SKM.rouquierPower y n ▷ H) := by
    rw [SKM.whiskerLeft_rouquierPower (k := k), SKM.rouquierPower_eq_pow, SKM.whiskerRight_rouquierPower (k := k)]
  have hZ (n : ℕ) : (show End (F ≫ G ≫ H) from F ◁ G ◁ z) ^ n =
      F ◁ G ◁ SKM.rouquierPower z n := by
    rw [SKM.whiskerLeft_rouquierPower (k := k), SKM.rouquierPower_eq_pow, SKM.whiskerLeft_rouquierPower (k := k)]
  simp only [tripleDotCorrectionPolynomial, tripleDotCorrectionSum, pow_zero, mul_one]
  simp_rw [hX, hY, hZ]
  simp only [End.mul_def]

end OddMath.QuiverHecke.ELVOld
end

end
