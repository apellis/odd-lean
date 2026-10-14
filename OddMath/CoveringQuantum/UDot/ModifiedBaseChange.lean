/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.CoveringQuantum.UDot.BaseChange
import OddMath.CoveringQuantum.UDot.FormUniqueness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Extension of scalars for the modified covering quantum group and its bilinear forms

For a flat `k`-algebra `k'` with `q ↦ q'`, `π ↦ π'`, the identification
`k' ⊗[k] U̇_{q,π} ≃ U̇_{q',π'}` of `UDot.baseChangeEquiv` restricts to the nonunital modified
algebras of Brundan–Ellis, arXiv:1701.04133v2, §9. A bilinear form on the modified algebra over
`k` then extends to one over `k'`, keeping weight-block orthogonality, `ρ`-adjointness and its
values on positive words. Over fields, the extended form has trivial left radical exactly when the
original form does. This serves the nondegeneracy statement of Brundan–Ellis,
arXiv:1701.04133v2, Theorem 10.1.

## Main definitions

* `UDot.mapModified`: the coefficient change restricted to the modified algebras.
* `UDot.modifiedBaseChange`: `k' ⊗[k] U̇_{q,π} ≃ U̇_{q',π'}` on modified algebras.
* `UDot.baseChangeForm`: the extension of scalars of a bilinear form on the modified algebra.

## Main results

* `UDot.baseChangeForm_mapModified`, `UDot.baseChangeForm_orthogonal`,
  `UDot.baseChangeForm_adjoint`, `UDot.baseChangeForm_positiveWord`.
* `UDot.leftRadical_trivial_of_baseChangeForm`, `UDot.baseChangeForm_leftRadical_trivial`:
  over a field extension, trivial left radical descends and ascends.
-/

noncomputable section

namespace OddMath.CoveringQuantum.UDot

open TensorProduct

/-! ### Extension of scalars of bilinear forms on modules -/

section Module

variable {K L M : Type*} [Field K] [CommRing L] [Algebra K L] [AddCommMonoid M] [Module K M]

/-- Over a field `K`, a bilinear form whose extension of scalars to a nonzero `K`-algebra has
trivial left radical itself has trivial left radical. -/
theorem leftRadical_trivial_of_baseChange [Nontrivial L] (B : LinearMap.BilinForm K M)
    (h : ∀ t : L ⊗[K] M, (∀ s, B.baseChange L t s = 0) → t = 0) :
    ∀ x : M, (∀ y, B x y = 0) → x = 0 := by
  intro x hx
  have h1 : (1 : L) ⊗ₜ[K] x = 0 := by
    refine h _ fun s ↦ ?_
    induction s with
    | tmul c y => simp [hx]
    | add s t hs ht => rw [map_add, hs, ht, add_zero]
  obtain ⟨g, hg⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap K L).injective)
  have hg1 : g 1 = 1 := by
    simpa using LinearMap.congr_fun hg 1
  have h2 := congrArg (fun t ↦ TensorProduct.lid K M (g.rTensor M t)) h1
  simpa [hg1] using h2

/-- Over a field `K`, extension of scalars preserves triviality of the left radical of a bilinear
form. -/
theorem baseChange_leftRadical_trivial (B : LinearMap.BilinForm K M)
    (h : ∀ x : M, (∀ y, B x y = 0) → x = 0) :
    ∀ t : L ⊗[K] M, (∀ s, B.baseChange L t s = 0) → t = 0 := by
  classical
  intro t ht
  let b := Module.Basis.ofVectorSpace K L
  obtain ⟨m, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft b).symm.surjective t
  suffices hm : m = 0 by rw [hm, map_zero]
  ext i
  refine h (m i) fun y ↦ ?_
  have hy := ht (1 ⊗ₜ y)
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum, map_sum,
    LinearMap.sum_apply] at hy
  simp only [LinearMap.BilinForm.baseChange_tmul, mul_one] at hy
  have hz := linearIndependent_iff'.mp b.linearIndependent m.support (fun j ↦ B (m j) y) hy
  by_cases hi : i ∈ m.support
  · exact hz i hi
  · rw [Finsupp.notMem_support_iff.mp hi, map_zero, LinearMap.zero_apply]

end Module

variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] (D : RootDatum I X)

section CommRing

variable {k k' : Type*} [CommRing k] [CommRing k']

/-! ### Linear maps on the modified algebra -/

section Generic

variable (q : kˣ) (π : k)

/-- The inclusion of the modified algebra into the unital envelope. -/
def modifiedInclusion : modified D q π →ₗ[k] CoveringUDot k D q π where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The block projection `x ↦ 1_μ x 1_η` on the modified algebra. -/
def blockProjModified (μ η : X) : modified D q π →ₗ[k] modified D q π where
  toFun x := ⟨blockProj D q π μ η x, block_le_modified D q π μ η (blockProj_mem D q π μ η x)⟩
  map_add' x y := Subtype.ext (map_add (blockProj D q π μ η) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (blockProj D q π μ η) c x.1)

theorem blockProjModified_eq_self {μ η : X} {x : modified D q π}
    (hx : (x : CoveringUDot k D q π) ∈ block D q π μ η) : blockProjModified D q π μ η x = x :=
  Subtype.ext (blockProj_eq_self D q π hx)

end Generic

variable [Algebra k k'] {q : kˣ} {π : k} {q' : k'ˣ} {π' : k'}
variable (hq : algebraMap k k' q = q') (hπ : algebraMap k k' π = π')

/-- The coefficient change restricted to the modified algebras. -/
def mapModified (x : modified D q π) : modified D q' π' :=
  ⟨mapCoeffs (algebraMap k k') D hq hπ x, mapCoeffs_mem_modified hq hπ x.property⟩

@[simp] theorem coe_mapModified (x : modified D q π) :
    (mapModified D hq hπ x : CoveringUDot k' D q' π') = mapCoeffs (algebraMap k k') D hq hπ x :=
  rfl

theorem mapModified_mul (x y : modified D q π) :
    mapModified D hq hπ (x * y) = mapModified D hq hπ x * mapModified D hq hπ y :=
  Subtype.ext (map_mul _ x.1 y.1)

theorem mapModified_add (x y : modified D q π) :
    mapModified D hq hπ (x + y) = mapModified D hq hπ x + mapModified D hq hπ y :=
  Subtype.ext (map_add _ x.1 y.1)

theorem mapModified_smul (c : k) (x : modified D q π) :
    mapModified D hq hπ (c • x) = algebraMap k k' c • mapModified D hq hπ x :=
  Subtype.ext (mapCoeffs_smul hq hπ c x.1)

theorem mapModified_blockProjModified (μ η : X) (x : modified D q π) :
    mapModified D hq hπ (blockProjModified D q π μ η x) =
      blockProjModified D q' π' μ η (mapModified D hq hπ x) :=
  Subtype.ext (by simp [blockProjModified, mapModified])

theorem mapModified_positiveWord (w : List I) (μ : X) :
    mapModified D hq hπ (positiveWord D q π w μ) = positiveWord D q' π' w μ :=
  Subtype.ext (mapCoeffs_halfWord hq hπ true w μ)

theorem mapModified_rhoModified (hπ2 : π ^ 2 = 1) (hπ2' : π' ^ 2 = 1) (x : modified D q π) :
    mapModified D hq hπ (rhoModified D q π hπ2 x) =
      rhoModified D q' π' hπ2' (mapModified D hq hπ x) :=
  Subtype.ext (mapCoeffs_rho hq hπ hπ2 hπ2' x.1)

/-- The base change map on modified algebras, into the unital envelope over `k'`. -/
def modifiedBaseChangeHom : k' ⊗[k] modified D q π →ₗ[k'] CoveringUDot k' D q' π' :=
  (baseChangeEquiv D hq hπ).toLinearMap ∘ₗ (modifiedInclusion D q π).baseChange k'

theorem modifiedBaseChangeHom_tmul (c : k') (x : modified D q π) :
    modifiedBaseChangeHom D hq hπ (c ⊗ₜ x) = c • mapCoeffs (algebraMap k k') D hq hπ x := by
  simp [modifiedBaseChangeHom, modifiedInclusion]

theorem modifiedBaseChangeHom_mem (t : k' ⊗[k] modified D q π) :
    modifiedBaseChangeHom D hq hπ t ∈ modified D q' π' := by
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    rw [modifiedBaseChangeHom_tmul]
    exact SMulMemClass.smul_mem c (mapCoeffs_mem_modified hq hπ x.property)
  | add s t hs ht => rw [map_add]; exact add_mem hs ht

theorem modifiedBaseChangeHom_injective [Module.Flat k k'] :
    Function.Injective (modifiedBaseChangeHom D hq hπ) := by
  refine (baseChangeEquiv D hq hπ).injective.comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

theorem modified_le_range_modifiedBaseChangeHom :
    (modified D q' π').toSubmodule ≤ LinearMap.range (modifiedBaseChangeHom D hq hπ) := by
  rw [← triangularSpan_eq_modified]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, b, ν, μ, rfl⟩
  refine ⟨1 ⊗ₜ ⟨halfWord D q π false a ν * halfWord D q π true b μ,
    (modified D q π).mul_mem
      (block_le_modified D q π _ _ (halfWord_mem_block D q π false a ν))
      (block_le_modified D q π _ _ (halfWord_mem_block D q π true b μ))⟩, ?_⟩
  rw [modifiedBaseChangeHom_tmul, one_smul]
  simp

/-- Extension of scalars of the modified algebra along a flat `k`-algebra `k'`:
`k' ⊗[k] U̇_{q,π} ≃ U̇_{q',π'}` on the nonunital modified algebras. -/
def modifiedBaseChange [Module.Flat k k'] : k' ⊗[k] modified D q π ≃ₗ[k'] modified D q' π' :=
  LinearEquiv.ofBijective
    ((modifiedBaseChangeHom D hq hπ).codRestrict (modified D q' π').toSubmodule
      (modifiedBaseChangeHom_mem D hq hπ))
    ⟨fun s t h ↦ modifiedBaseChangeHom_injective D hq hπ (congrArg Subtype.val h), fun y ↦ by
      obtain ⟨t, ht⟩ := modified_le_range_modifiedBaseChangeHom D hq hπ y.property
      exact ⟨t, Subtype.ext ht⟩⟩

theorem coe_modifiedBaseChange [Module.Flat k k'] (t : k' ⊗[k] modified D q π) :
    (modifiedBaseChange D hq hπ t : CoveringUDot k' D q' π') = modifiedBaseChangeHom D hq hπ t :=
  rfl

@[simp] theorem modifiedBaseChange_tmul [Module.Flat k k'] (c : k') (x : modified D q π) :
    modifiedBaseChange D hq hπ (c ⊗ₜ x) = c • mapModified D hq hπ x :=
  Subtype.ext (modifiedBaseChangeHom_tmul D hq hπ c x)


/-! ### Extension of scalars of bilinear forms on the modified algebra -/

/-- A bilinear identity `B (P x) (Q y) = B (P₂ x) (Q₂ y)` persists after extension of scalars. -/
theorem baseChange_apply_baseChange_eq {M : Type*} [AddCommMonoid M] [Module k M]
    (B : LinearMap.BilinForm k M) (P Q P₂ Q₂ : M →ₗ[k] M)
    (h : ∀ x y, B (P x) (Q y) = B (P₂ x) (Q₂ y)) (t s : k' ⊗[k] M) :
    B.baseChange k' (P.baseChange k' t) (Q.baseChange k' s) =
      B.baseChange k' (P₂.baseChange k' t) (Q₂.baseChange k' s) := by
  induction t with
  | tmul c x =>
    induction s with
    | tmul d y => simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]
    | add s s' hs hs' => simp only [map_add, hs, hs']
  | add t t' ht ht' => simp only [map_add, LinearMap.add_apply, ht, ht']

variable [Module.Flat k k']

theorem modifiedBaseChange_symm_mapModified (x : modified D q π) :
    (modifiedBaseChange D hq hπ).symm (mapModified D hq hπ x) = 1 ⊗ₜ x := by
  rw [LinearEquiv.symm_apply_eq, modifiedBaseChange_tmul, one_smul]

/-- A `k'`-linear endomorphism of the modified algebra over `k'` which extends a `k`-linear
endomorphism over `k` corresponds to its extension of scalars. -/
theorem modifiedBaseChange_symm_apply_map (P : modified D q π →ₗ[k] modified D q π)
    (P' : modified D q' π' →ₗ[k'] modified D q' π')
    (hP : ∀ x, P' (mapModified D hq hπ x) = mapModified D hq hπ (P x)) (y : modified D q' π') :
    (modifiedBaseChange D hq hπ).symm (P' y) =
      P.baseChange k' ((modifiedBaseChange D hq hπ).symm y) := by
  obtain ⟨t, rfl⟩ := (modifiedBaseChange D hq hπ).surjective y
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
  induction t with
  | tmul c x =>
    rw [modifiedBaseChange_tmul, map_smul, hP, LinearMap.baseChange_tmul, modifiedBaseChange_tmul]
  | add s t hs ht => simp only [map_add, hs, ht]

variable (B : LinearMap.BilinForm k (modified D q π))

/-- The extension of scalars of a bilinear form on the modified algebra, transported along
`modifiedBaseChange`. -/
def baseChangeForm : LinearMap.BilinForm k' (modified D q' π') :=
  LinearMap.BilinForm.congr (modifiedBaseChange D hq hπ) (B.baseChange k')

theorem baseChangeForm_apply (x y : modified D q' π') :
    baseChangeForm D hq hπ B x y = B.baseChange k' ((modifiedBaseChange D hq hπ).symm x)
      ((modifiedBaseChange D hq hπ).symm y) :=
  LinearMap.BilinForm.congr_apply _ _ _ _

@[simp] theorem baseChangeForm_mapModified (x y : modified D q π) :
    baseChangeForm D hq hπ B (mapModified D hq hπ x) (mapModified D hq hπ y) =
      algebraMap k k' (B x y) := by
  rw [baseChangeForm_apply, modifiedBaseChange_symm_mapModified,
    modifiedBaseChange_symm_mapModified, LinearMap.BilinForm.baseChange_tmul, mul_one,
    Algebra.smul_def, mul_one]

/-- Weight-block orthogonality at both endpoints survives extension of scalars. -/
theorem baseChangeForm_orthogonal
    (hB : ∀ μ ν μ' ν' (x y : modified D q π),
      (x : CoveringUDot k D q π) ∈ block D q π μ ν →
      (y : CoveringUDot k D q π) ∈ block D q π μ' ν' → μ ≠ μ' ∨ ν ≠ ν' → B x y = 0)
    (μ ν μ' ν' : X) (x y : modified D q' π')
    (hx : (x : CoveringUDot k' D q' π') ∈ block D q' π' μ ν)
    (hy : (y : CoveringUDot k' D q' π') ∈ block D q' π' μ' ν') (hne : μ ≠ μ' ∨ ν ≠ ν') :
    baseChangeForm D hq hπ B x y = 0 := by
  rw [baseChangeForm_apply, ← blockProjModified_eq_self D q' π' hx,
    ← blockProjModified_eq_self D q' π' hy,
    modifiedBaseChange_symm_apply_map D hq hπ (blockProjModified D q π μ ν) _
      (fun z ↦ (mapModified_blockProjModified D hq hπ μ ν z).symm),
    modifiedBaseChange_symm_apply_map D hq hπ (blockProjModified D q π μ' ν') _
      (fun z ↦ (mapModified_blockProjModified D hq hπ μ' ν' z).symm),
    baseChange_apply_baseChange_eq B _ _ 0 0 (fun a b ↦ by
      rw [LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
      exact hB μ ν μ' ν' _ _ (blockProj_mem D q π μ ν a) (blockProj_mem D q π μ' ν' b) hne)]
  simp

/-- Left `ρ`-adjointness survives extension of scalars. -/
theorem baseChangeForm_adjoint (hπ2 : π ^ 2 = 1) (hπ2' : π' ^ 2 = 1)
    (hB : ∀ u x y, B (u * x) y = B x (rhoModified D q π hπ2 u * y))
    (u x y : modified D q' π') :
    baseChangeForm D hq hπ B (u * x) y =
      baseChangeForm D hq hπ B x (rhoModified D q' π' hπ2' u * y) := by
  obtain ⟨t, rfl⟩ := (modifiedBaseChange D hq hπ).surjective u
  induction t with
  | tmul c u =>
    rw [modifiedBaseChange_tmul, map_smul, smul_mul_assoc, smul_mul_assoc, LinearMap.map_smul₂,
      map_smul]
    congr 1
    have h1 := modifiedBaseChange_symm_apply_map D hq hπ (LinearMap.mulLeft k u)
      (LinearMap.mulLeft k' (mapModified D hq hπ u)) (fun z ↦ by simp [mapModified_mul]) x
    have h2 := modifiedBaseChange_symm_apply_map D hq hπ
      (LinearMap.mulLeft k (rhoModified D q π hπ2 u))
      (LinearMap.mulLeft k' (mapModified D hq hπ (rhoModified D q π hπ2 u)))
      (fun z ↦ by simp [mapModified_mul]) y
    rw [LinearMap.mulLeft_apply] at h1 h2
    rw [baseChangeForm_apply, baseChangeForm_apply, h1,
      ← mapModified_rhoModified D hq hπ hπ2 hπ2', h2]
    have := baseChange_apply_baseChange_eq B (LinearMap.mulLeft k u) LinearMap.id LinearMap.id
      (LinearMap.mulLeft k (rhoModified D q π hπ2 u)) (fun a b ↦ hB u a b)
      ((modifiedBaseChange D hq hπ).symm x) ((modifiedBaseChange D hq hπ).symm y)
    simpa only [LinearMap.baseChange_id, LinearMap.id_apply] using this
  | add s t hs ht =>
    rw [map_add, add_mul, map_add, LinearMap.add_apply, hs, ht, map_add, add_mul, map_add]

/-- Values on positive words are the images of the values over `k`. -/
theorem baseChangeForm_positiveWord (g : List I → List I → X → X → k)
    (hg : ∀ a b μ ν, B (positiveWord D q π a μ) (positiveWord D q π b ν) = g a b μ ν)
    (a b : List I) (μ ν : X) :
    baseChangeForm D hq hπ B (positiveWord D q' π' a μ) (positiveWord D q' π' b ν) =
      algebraMap k k' (g a b μ ν) := by
  rw [← mapModified_positiveWord D hq hπ, ← mapModified_positiveWord D hq hπ,
    baseChangeForm_mapModified, hg]

end CommRing

/-! ### Nondegeneracy over a field extension -/

section Field

variable {k k' : Type*} [Field k] [Field k'] [Algebra k k'] {q : kˣ} {π : k} {q' : k'ˣ} {π' : k'}
variable (hq : algebraMap k k' q = q') (hπ : algebraMap k k' π = π')
variable (B : LinearMap.BilinForm k (modified D q π))

/-- Descent of nondegeneracy: if the extension of scalars of `B` to a field extension has trivial
left radical, so does `B`. -/
theorem leftRadical_trivial_of_baseChangeForm
    (h : ∀ x, (∀ y, baseChangeForm D hq hπ B x y = 0) → x = 0) :
    ∀ x, (∀ y, B x y = 0) → x = 0 := by
  refine leftRadical_trivial_of_baseChange (L := k') B fun t ht ↦ ?_
  have he : modifiedBaseChange D hq hπ t = 0 := h _ fun y ↦ by
    rw [baseChangeForm_apply, LinearEquiv.symm_apply_apply]
    exact ht _
  simpa using he

/-- Ascent of nondegeneracy: if `B` has trivial left radical, so does its extension of scalars
to a field extension. -/
theorem baseChangeForm_leftRadical_trivial (h : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∀ x, (∀ y, baseChangeForm D hq hπ B x y = 0) → x = 0 := by
  intro x hx
  have he := baseChange_leftRadical_trivial (L := k') B h ((modifiedBaseChange D hq hπ).symm x)
    fun s ↦ by
      have := hx (modifiedBaseChange D hq hπ s)
      rwa [baseChangeForm_apply, LinearEquiv.symm_apply_apply] at this
  simpa using he

end Field

end OddMath.CoveringQuantum.UDot
