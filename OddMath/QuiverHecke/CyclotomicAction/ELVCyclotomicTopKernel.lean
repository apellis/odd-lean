/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicTopQuotient
import OddMath.QuiverHecke.CyclotomicAction.ELVIdealSum

/-! # Kernel of the canonical short-column quotient

The kernel is computed from the first-factor cyclotomic ideal on the prescribed
balanced tensor. No crossing-image source or injectivity assertion is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- First-factor cyclotomic relations in the affine balanced source. -/
def firstIdeal (i : I) (v t : List I) : Submodule k (ShortTarget D Sc cutoff i v t) :=
  Submodule.span k {z | ∃ s, ∃ c : hom D Sc cutoff (s ++ [i]) t,
    c ∈ ideal D Sc cutoff (s ++ [i]) t ∧ ∃ b : Old D Sc cutoff v (s ++ [i]),
      shortTensor D Sc cutoff i v s t c b = z}

/-- Each indicated ideal tensor is killed by the canonical quotient. -/
theorem firstIdeal_le_ker_q (i : I) (v t : List I) :
    firstIdeal D Sc cutoff i v t ≤ LinearMap.ker (q D Sc cutoff i v t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, c, hc, b, rfl⟩
  change q D Sc cutoff i v t _ = 0
  have hz : (ideal D Sc cutoff (s ++ [i]) t).mkQ c = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hc
  rw [q_shortTensor, hz]
  change BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ (0 ⊗ₜ[k] b) = 0
  rw [zero_tmul, map_zero]

/-- The affine tensor pairing followed by the specified ideal quotient. -/
def quotientPair (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [i]) →ₗ[k]
        ShortTarget D Sc cutoff i v t ⧸ firstIdeal D Sc cutoff i v t :=
  LinearMap.compr₂
    ((TensorProduct.mk k _ _).compr₂
      (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
        (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩))
    (firstIdeal D Sc cutoff i v t).mkQ

/-- Descent in the first factor alone. -/
def inversePair (i : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [i]) →ₗ[k]
        ShortTarget D Sc cutoff i v t ⧸ firstIdeal D Sc cutoff i v t :=
  (ideal D Sc cutoff (s ++ [i]) t).liftQ (quotientPair D Sc cutoff i v s t) (by
    intro c hc
    apply LinearMap.ext
    intro b
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span ⟨s, c, hc, b, rfl⟩)

@[simp] theorem inversePair_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    inversePair D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b =
      (firstIdeal D Sc cutoff i v t).mkQ (shortTensor D Sc cutoff i v s t c b) := rfl

theorem shortTensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

theorem inversePair_balance (i : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i) i v).obj s) :
    inversePair D Sc cutoff i v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      inversePair D Sc cutoff i v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i) i v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  exact congrArg (firstIdeal D Sc cutoff i v t.word).mkQ
    (shortTensor_balance D Sc cutoff i v s.word s'.word t.word r c b)

/-- The reverse map is defined on the lower-cyclotomic balanced tensor itself. -/
def inverse (i : I) (v t : List I) : Source D Sc cutoff i v t →ₗ[k]
    ShortTarget D Sc cutoff i v t ⧸ firstIdeal D Sc cutoff i v t :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (inversePair D Sc cutoff i v s.word t))
    (fun s s' r c b => inversePair_balance D Sc cutoff i v s s' ⟨t⟩ r c b)

@[simp] theorem inverse_tensor_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    inverse D Sc cutoff i v t (tensor D Sc cutoff i v s t
      ((ideal D Sc cutoff _ _).mkQ c) b) =
      (firstIdeal D Sc cutoff i v t).mkQ (shortTensor D Sc cutoff i v s t c b) := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ _ b

theorem inverse_q (i : I) (v t : List I) :
    inverse D Sc cutoff i v t ∘ₗ q D Sc cutoff i v t =
      (firstIdeal D Sc cutoff i v t).mkQ := by
  apply BalancedInduction.hom_ext
  intro s c b
  change inverse D Sc cutoff i v t
    (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b)) = _
  rw [q_shortTensor, inverse_tensor_mk]
  rfl

/-- Exact kernel equality for the canonical quotient, without a flatness assumption. -/
theorem ker_q (i : I) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) = firstIdeal D Sc cutoff i v t := by
  apply le_antisymm
  · intro z hz
    have h := congrArg (fun f => f z) (inverse_q D Sc cutoff i v t)
    change inverse D Sc cutoff i v t (q D Sc cutoff i v t z) =
      (firstIdeal D Sc cutoff i v t).mkQ z at h
    rw [LinearMap.mem_ker.mp hz, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h.symm
  · exact firstIdeal_le_ker_q D Sc cutoff i v t

/-- The first tensor coordinate as a linear map, for ideal-sum descent. -/
def shortLeft (i : I) (v s t : List I) (b : Old D Sc cutoff v (s ++ [i])) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k] ShortTarget D Sc cutoff i v t :=
  BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ ∘ₗ
      (TensorProduct.mk k _ _).flip b

/-- Lower old relations already vanish by the prescribed balance. -/
theorem shortTensor_appendRelations (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (hc : c ∈ appendRelations D Sc cutoff i s t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t c b = 0 := by
  have h : appendRelations D Sc cutoff i s t ≤ LinearMap.ker (shortLeft D Sc cutoff i v s t b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s', r, hr, c, rfl⟩
    change shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b = 0
    rw [shortTensor_balance]
    have hz : (coefficient D Sc cutoff (D.parity i) i v).map
        ((ideal D Sc cutoff s s').mkQ r) b = 0 := by
      obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
      change (ideal D Sc cutoff _ _).mkQ
        (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i) r)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (comp_ideal D Sc cutoff b
          (ideal_rightContext D Sc cutoff [i] (twist_ideal D Sc cutoff _ hr)))
    rw [hz]
    change BalancedInduction.inclusion (affineAppend D Sc cutoff i)
      (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s'⟩
        (c ⊗ₜ[k] 0) = 0
    rw [tmul_zero, map_zero]
  exact h hc

/-- The literal lower moving-word generators, before constructing their balanced domain. -/
def movingImage (i : I) (v t : List I) : Submodule k (ShortTarget D Sc cutoff i v t) :=
  Submodule.span k {z | ∃ s, ∃ h : hom D Sc cutoff (i :: s) t,
    ∃ b : Old D Sc cutoff v (s ++ [i]),
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b = z}

/-- The proved full-ELV ideal sum reduces the kernel to the actual lower moving word. -/
theorem firstIdeal_eq_movingImage (i : I) (v t : List I) :
    firstIdeal D Sc cutoff i v t = movingImage D Sc cutoff i v t := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, c, hc, b, rfl⟩
    rw [ideal_eq_appendRelations_sup_range] at hc
    obtain ⟨a, ha, w, ⟨h, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hc
    change shortLeft D Sc cutoff i v s t b (a + (appendW D Sc cutoff i s ≫ h)) ∈ _
    rw [map_add]
    have hz := shortTensor_appendRelations D Sc cutoff i v s t a ha b
    change shortLeft D Sc cutoff i v s t b a = 0 at hz
    rw [hz, zero_add]
    exact Submodule.subset_span ⟨s, h, b, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, h, b, rfl⟩
    exact Submodule.subset_span ⟨s, appendW D Sc cutoff i s ≫ h,
      ideal_comp D Sc cutoff (appendW_mem_ideal D Sc cutoff i s) h, b, rfl⟩

/-- Concrete kernel equality: the generators are `h W₋ ⊗ πᵖ b` in algebra order. -/
theorem ker_q_eq_movingImage (i : I) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i v t) = movingImage D Sc cutoff i v t := by
  rw [ker_q, firstIdeal_eq_movingImage]

/-- The quotient by the literal moving-word relations is the prescribed source. -/
def quotientEquiv (i : I) (v t : List I) :
    (ShortTarget D Sc cutoff i v t ⧸ movingImage D Sc cutoff i v t) ≃ₗ[k]
      Source D Sc cutoff i v t :=
  (Submodule.quotEquivOfEq _ _ (ker_q_eq_movingImage D Sc cutoff i v t).symm).trans
    ((q D Sc cutoff i v t).quotKerEquivOfSurjective (q_surjective D Sc cutoff i v t))

@[simp] theorem quotientEquiv_mk (i : I) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    quotientEquiv D Sc cutoff i v t (Submodule.Quotient.mk z) = q D Sc cutoff i v t z := rfl

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
