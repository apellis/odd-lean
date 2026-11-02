/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCoefficientModule

/-! # Canonical parity transport for the two-colour balanced source

The map J in `DeformedActionAssembly.md` §4 twists the entire first tensor
factor. The coefficient's right action remains ordinary, including its
exterior directions. These are underlying linear equivalences; no claim
about representing a supernatural map by ordinary precomposition is made.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

abbrev SourceWithParity (p : ZMod 2) (i j : I) (v t : List I) :=
  BalancedInduction.Obj (append D Sc cutoff i) (coefficient D Sc cutoff p j v)
    (⟨t⟩ : OldCategory D Sc cutoff)

def parityTensor (p : ZMod 2) (i j : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    SourceWithParity D Sc cutoff p i j v t :=
  BalancedInduction.tensor (append D Sc cutoff i) (coefficient D Sc cutoff p j v) ⟨s⟩ c b

private theorem parityTensor_balance (p q : ZMod 2) (i j : I) (v s s' t : List I)
    (r : Old D Sc cutoff s s') (c : Old D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    parityTensor D Sc cutoff q i j v s t
      (oldTwist D Sc cutoff (p + q) (s ++ [i]) t
        ((append D Sc cutoff i).map (X := ⟨s⟩) (Y := ⟨s'⟩) r ≫ c)) b =
      parityTensor D Sc cutoff q i j v s' t
        (oldTwist D Sc cutoff (p + q) (s' ++ [i]) t c)
        ((coefficient D Sc cutoff p j v).map (X := ⟨s⟩) (Y := ⟨s'⟩) r b) := by
  have hb := BalancedInduction.balance (append D Sc cutoff i) (coefficient D Sc cutoff q j v)
    (v := (⟨s⟩ : OldCategory D Sc cutoff)) (v' := ⟨s'⟩)
    (twist k (p + q) r) (twist k (p + q) c) b
  rw [Supercategory.map_twist, ← twist_comp] at hb
  rw [oldCategory_twist, oldCategory_twist] at hb
  change parityTensor D Sc cutoff q i j v s t _ b =
    parityTensor D Sc cutoff q i j v s' t _
      ((coefficient D Sc cutoff q j v).map (twist k (p + q) r) b) at hb
  trans parityTensor D Sc cutoff q i j v s' t
    (oldTwist D Sc cutoff (p + q) (s' ++ [i]) t c)
      ((coefficient D Sc cutoff q j v).map (X := ⟨s⟩) (Y := ⟨s'⟩) (twist k (p + q) r) b)
  · exact hb
  congr 1
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s s').mkQ_surjective r
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [j])).mkQ_surjective b
  rw [oldCategory_twist]
  change (ideal D Sc cutoff v (s' ++ [j])).mkQ
      (b ≫ rightContext D Sc cutoff [j] _ _ (twist k q (twist k (p + q) r))) =
    (ideal D Sc cutoff v (s' ++ [j])).mkQ
      (b ≫ rightContext D Sc cutoff [j] _ _ (twist k p r))
  rw [← twist_add, show q + (p + q) = p by rw [add_left_comm, zmod2_add_self, add_zero]]

/-- Change the coefficient shift by twisting the whole first tensor factor. -/
def parityTransport (p q : ZMod 2) (i j : I) (v t : List I) :
    SourceWithParity D Sc cutoff p i j v t →ₗ[k] SourceWithParity D Sc cutoff q i j v t :=
  BalancedInduction.lift (append D Sc cutoff i) (coefficient D Sc cutoff p j v) ⟨t⟩
    (fun s => BalancedInduction.inclusion (append D Sc cutoff i)
      (coefficient D Sc cutoff q j v) ⟨t⟩ s ∘ₗ
        TensorProduct.map (oldTwist D Sc cutoff (p + q) (s.word ++ [i]) t) LinearMap.id)
    (fun s s' r c b => parityTensor_balance D Sc cutoff p q i j v s.word s'.word t r c b)

@[simp] theorem parityTransport_tensor (p q : ZMod 2) (i j : I) (v s t : List I)
    (c : Old D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    parityTransport D Sc cutoff p q i j v t (parityTensor D Sc cutoff p i j v s t c b) =
      parityTensor D Sc cutoff q i j v s t (oldTwist D Sc cutoff (p + q) (s ++ [i]) t c) b := by
  exact BalancedInduction.lift_tensor (append D Sc cutoff i) (coefficient D Sc cutoff p j v)
    ⟨t⟩ _ _ ⟨s⟩ c b

/-- The canonical transport and its prescribed reverse are inverse. -/
theorem parityTransport_involutive (p q : ZMod 2) (i j : I) (v t : List I) :
    parityTransport D Sc cutoff q p i j v t ∘ₗ parityTransport D Sc cutoff p q i j v t =
      LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  change parityTransport D Sc cutoff q p i j v t
    (parityTransport D Sc cutoff p q i j v t (parityTensor D Sc cutoff p i j v s.word t c b)) = _
  rw [parityTransport_tensor, parityTransport_tensor, add_comm q p, oldTwist_twice]
  rfl

def sourceParityEquiv (i j : I) (v t : List I) :
    SourceWithParity D Sc cutoff 0 i j v t ≃ₗ[k] Source D Sc cutoff i j v t :=
  LinearEquiv.ofLinearMap
    (parityTransport D Sc cutoff 0 (D.parity i * D.parity j) i j v t)
    (parityTransport D Sc cutoff (D.parity i * D.parity j) 0 i j v t)
    (parityTransport_involutive D Sc cutoff (D.parity i * D.parity j) 0 i j v t)
    (parityTransport_involutive D Sc cutoff 0 (D.parity i * D.parity j) i j v t)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
