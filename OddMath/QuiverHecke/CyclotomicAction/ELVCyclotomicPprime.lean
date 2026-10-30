/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicTopKernel
import OddMath.QuiverHecke.CyclotomicAction.ELVQDescent

/-! # The balanced short moving-word map

The domain is `Rf ⊗_(S,j_L) Π^epsilon(eB)`. The lower balance is
proved using the full ELV moving-word error, including exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- The resolution shift on the coefficient word of content beta. -/
def epsilon (i : I) (v : List I) : ZMod 2 :=
  D.parity i * wordSumParity D v + (cutoff i : ZMod 2) * D.parity i

/-- Left inclusion on the full affine coefficient category. -/
def affinePrepend (i : I) : AffineWord D Sc cutoff ⥤ AffineWord D Sc cutoff where
  obj s := ⟨i :: s.word⟩
  map {s t} := insert D Sc cutoff i s.word t.word
  map_id _ := insert_id D Sc cutoff i _
  map_comp f g := insert_comp D Sc cutoff i f g

/-- The prescribed epsilon-shifted balanced domain, before applying the moving word. -/
abbrev PprimeDomain (i : I) (v t : List I) :=
  BalancedInduction.Obj (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v)
    (⟨t⟩ : AffineWord D Sc cutoff)

def pprimeTensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    PprimeDomain D Sc cutoff i v t :=
  BalancedInduction.tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨s⟩ h b

/-- On a supported coefficient corner, epsilon is the moving parity plus p. -/
theorem epsilon_eq_appendQ_add (i : I) (v s : List I)
    (hv : wordSumParity D (s ++ [i]) = wordSumParity D v) :
    epsilon D cutoff i v = appendQ D cutoff i s + D.parity i := by
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  unfold epsilon appendQ
  rw [← hv]
  simp only [wordSumParity, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  rw [mul_add, hp]
  ring

/-- Multiplication by W on one tensor summand. -/
def pprimeSummand (i : I) (v s t : List I) :
    hom D Sc cutoff (i :: s) t ⊗[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      ShortTarget D Sc cutoff i v t :=
  BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ ∘ₗ
    TensorProduct.map (Linear.leftComp k _ (appendW D Sc cutoff i s)) LinearMap.id

@[simp] theorem pprimeSummand_tmul (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeSummand D Sc cutoff i v s t (h ⊗ₜ[k] b) =
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b := rfl

/-- The full lower balance, not only scalar or homogeneous-generator balance. -/
theorem pprimeSummand_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    pprimeSummand D Sc cutoff i v s t ((insert D Sc cutoff i s s' r ≫ h) ⊗ₜ[k] b) =
      pprimeSummand D Sc cutoff i v s' t (h ⊗ₜ[k]
        (coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  by_cases hv : wordSumParity D (s ++ [i]) = wordSumParity D v
  · have he := appendRelations_comp D Sc cutoff i
      (appendError_mem_appendRelations D Sc cutoff i (twist k (appendQ D cutoff i s) r)) h
    have hz := shortTensor_appendRelations D Sc cutoff i v s t _ he
      ((ideal D Sc cutoff v (s ++ [i])).mkQ b)
    change shortLeft D Sc cutoff i v s t _ _ = 0 at hz
    rw [appendError_apply, twist_twist, Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
    change shortTensor D Sc cutoff i v s t _ _ = shortTensor D Sc cutoff i v s t _ _ at hz
    rw [Category.assoc, Category.assoc] at hz
    rw [pprimeSummand_tmul, pprimeSummand_tmul, ← hz, shortTensor_balance]
    congr 1
    change (ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _
        (twist k (D.parity i) (twist k (appendQ D cutoff i s) r))) =
      (ideal D Sc cutoff _ _).mkQ
        (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (epsilon D cutoff i v) r))
    rw [epsilon_eq_appendQ_add D cutoff i v s hv, add_comm (appendQ D cutoff i s), twist_add]
  · rw [hom_zero_of_wordParity_ne D Sc cutoff hv b, map_zero, map_zero,
      tmul_zero, tmul_zero, map_zero, map_zero]

/-- The descended moving-word map on the independently prescribed domain. -/
def pprime (i : I) (v t : List I) : PprimeDomain D Sc cutoff i v t →ₗ[k]
    ShortTarget D Sc cutoff i v t :=
  BalancedInduction.lift (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩
    (fun s => pprimeSummand D Sc cutoff i v s.word t)
    (fun s s' r h b => pprimeSummand_balance D Sc cutoff i v s.word s'.word t r h b)

@[simp] theorem pprime_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h b) =
      shortTensor D Sc cutoff i v s t (appendW D Sc cutoff i s ≫ h) b := by
  exact BalancedInduction.lift_tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩ _ _ ⟨s⟩ h b

/-- The range is exactly the literal moving-word span. -/
theorem range_pprime (i : I) (v t : List I) :
    LinearMap.range (pprime D Sc cutoff i v t) = movingImage D Sc cutoff i v t := by
  classical
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (BalancedInduction.relations (affinePrepend D Sc cutoff i)
      (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩).mkQ_surjective z
    induction z using DirectSum.induction_on with
    | zero => simpa only [map_zero] using (movingImage D Sc cutoff i v t).zero_mem
    | add x y hx hy => simpa only [map_add] using (movingImage D Sc cutoff i v t).add_mem hx hy
    | of s z =>
      induction z using TensorProduct.inductionOn with
      | add x y hx hy => simpa only [map_add] using (movingImage D Sc cutoff i v t).add_mem hx hy
      | tmul h b =>
        change pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b) ∈ _
        rw [pprime_tensor]
        exact Submodule.subset_span ⟨s.word, h, b, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, h, b, rfl⟩
    exact ⟨pprimeTensor D Sc cutoff i v s t h b, pprime_tensor D Sc cutoff i v s t h b⟩

/-- Right exactness for the named moving-word map and canonical quotient. -/
theorem range_pprime_eq_ker_q (i : I) (v t : List I) :
    LinearMap.range (pprime D Sc cutoff i v t) = LinearMap.ker (q D Sc cutoff i v t) := by
  rw [range_pprime, ker_q_eq_movingImage]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
