/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingTensor

/-! # Kernel of the two-colour short-column quotient

The kernel is computed from the first-factor cyclotomic ideal on the prescribed
balanced tensor. No crossing-image source or injectivity assertion is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor.Distinct

/-- First-factor cyclotomic relations in the affine balanced source. -/
def firstIdeal (i j : I) (v t : List I) : Submodule k (ShortTarget D Sc cutoff i j v t) :=
  Submodule.span k {z | ∃ s, ∃ c : hom D Sc cutoff (s ++ [i]) t,
    c ∈ ideal D Sc cutoff (s ++ [i]) t ∧ ∃ b : Old D Sc cutoff v (s ++ [j]),
      shortTensor D Sc cutoff i j v s t c b = z}

/-- Each indicated ideal tensor is killed by the canonical quotient. -/
theorem firstIdeal_le_ker_q (i j : I) (v t : List I) :
    firstIdeal D Sc cutoff i j v t ≤ LinearMap.ker (q D Sc cutoff i j v t) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨s, c, hc, b, rfl⟩
  change q D Sc cutoff i j v t _ = 0
  have hz : (ideal D Sc cutoff (s ++ [i]) t).mkQ c = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hc
  rw [q_shortTensor, hz]
  change BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩ (0 ⊗ₜ[k] b) = 0
  rw [zero_tmul, map_zero]

/-- The affine tensor pairing followed by the specified ideal quotient. -/
def quotientPair (i j : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [j]) →ₗ[k]
        ShortTarget D Sc cutoff i j v t ⧸ firstIdeal D Sc cutoff i j v t :=
  LinearMap.compr₂
    ((TensorProduct.mk k _ _).compr₂
      (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
        (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩))
    (firstIdeal D Sc cutoff i j v t).mkQ

/-- Descent in the first factor alone. -/
def inversePair (i j : I) (v s t : List I) :
    Old D Sc cutoff (s ++ [i]) t →ₗ[k]
      Old D Sc cutoff v (s ++ [j]) →ₗ[k]
        ShortTarget D Sc cutoff i j v t ⧸ firstIdeal D Sc cutoff i j v t :=
  (ideal D Sc cutoff (s ++ [i]) t).liftQ (quotientPair D Sc cutoff i j v s t) (by
    intro c hc
    apply LinearMap.ext
    intro b
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span ⟨s, c, hc, b, rfl⟩)

@[simp] theorem inversePair_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    inversePair D Sc cutoff i j v s t ((ideal D Sc cutoff _ _).mkQ c) b =
      (firstIdeal D Sc cutoff i j v t).mkQ (shortTensor D Sc cutoff i j v s t c b) := rfl

theorem shortTensor_balance (i j : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    shortTensor D Sc cutoff i j v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i j v s' t c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

theorem inversePair_balance (i j : I) (v : List I) (s s' t : OldCategory D Sc cutoff)
    (r : s ⟶ s') (c : (append D Sc cutoff i).obj s' ⟶ t)
    (b : (coefficient D Sc cutoff (D.parity i * D.parity j) j v).obj s) :
    inversePair D Sc cutoff i j v s.word t.word ((append D Sc cutoff i).map r ≫ c) b =
      inversePair D Sc cutoff i j v s'.word t.word c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map r b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word s'.word).mkQ_surjective r
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s'.word ++ [i]) t.word).mkQ_surjective c
  exact congrArg (firstIdeal D Sc cutoff i j v t.word).mkQ
    (shortTensor_balance D Sc cutoff i j v s.word s'.word t.word r c b)

/-- The reverse map is defined on the lower-cyclotomic balanced tensor itself. -/
def inverse (i j : I) (v t : List I) : Source D Sc cutoff i j v t →ₗ[k]
    ShortTarget D Sc cutoff i j v t ⧸ firstIdeal D Sc cutoff i j v t :=
  BalancedInduction.lift (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩
    (fun s => TensorProduct.lift (inversePair D Sc cutoff i j v s.word t))
    (fun s s' r c b => inversePair_balance D Sc cutoff i j v s s' ⟨t⟩ r c b)

@[simp] theorem inverse_tensor_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    inverse D Sc cutoff i j v t (tensor D Sc cutoff i j v s t
      ((ideal D Sc cutoff _ _).mkQ c) b) =
      (firstIdeal D Sc cutoff i j v t).mkQ (shortTensor D Sc cutoff i j v s t c b) := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ _ _ ⟨s⟩ _ b

theorem inverse_q (i j : I) (v t : List I) :
    inverse D Sc cutoff i j v t ∘ₗ q D Sc cutoff i j v t =
      (firstIdeal D Sc cutoff i j v t).mkQ := by
  apply BalancedInduction.hom_ext
  intro s c b
  change inverse D Sc cutoff i j v t
    (q D Sc cutoff i j v t (shortTensor D Sc cutoff i j v s.word t c b)) = _
  rw [q_shortTensor, inverse_tensor_mk]
  rfl

/-- Exact kernel equality for the canonical quotient, without a flatness assumption. -/
theorem ker_q (i j : I) (v t : List I) :
    LinearMap.ker (q D Sc cutoff i j v t) = firstIdeal D Sc cutoff i j v t := by
  apply le_antisymm
  · intro z hz
    have h := congrArg (fun f => f z) (inverse_q D Sc cutoff i j v t)
    change inverse D Sc cutoff i j v t (q D Sc cutoff i j v t z) =
      (firstIdeal D Sc cutoff i j v t).mkQ z at h
    rw [LinearMap.mem_ker.mp hz, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h.symm
  · exact firstIdeal_le_ker_q D Sc cutoff i j v t

end CyclotomicCrossingTensor.Distinct
end OddMath.QuiverHecke.ELVOld
