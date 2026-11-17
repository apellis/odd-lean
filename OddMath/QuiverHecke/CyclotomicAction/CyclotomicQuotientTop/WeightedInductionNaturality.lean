import StringDiagrams.Super.BoxProduct
import Mathlib.CategoryTheory.Whiskering
import Mathlib.LinearAlgebra.Isomorphisms
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop.CyclotomicCrossingTensor
import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials.PCentral

/-!
# Cyclotomic quotient top

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Naturality of weighted quotient induction
The old/truncated action comparison in SwappedVacuumCoordinates §6 must
intertwine all module maps, including both homogeneous parities.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]

def inductionFunctorIsoOfEq (J K : C ⥤ D)
    [J.Additive] [J.Linear k] [IsSuperfunctor k J]
    [K.Additive] [K.Linear k] [IsSuperfunctor k K] (h : J = K) :
    induction (k := k) J ≅ induction (k := k) K := by
  subst K
  exact Iso.refl _

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
local notation "Q" => oldTruncateFunctor D Sc cutoff N

@[simp] theorem weightedRestrictionModuleIso_inv_app
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) (p : ZMod 2)
    (v : OldCategory D Sc cutoff) :
    (weightedRestrictionModuleIso D Sc cutoff N M hM).inv.app p v =
      if p = 0 then LinearMap.id else 0 := rfl

@[simp] theorem quotientInductionCounitIso_hom
    (M : Superfunctor k (TruncatedCategory D Sc cutoff N) (SVec k)) :
    (quotientInductionCounitIso D Sc cutoff N M).hom =
      (BalancedInduction.adjunctionCounit Q).app M := by
  apply Superfunctor.hom_ext
  intro p v
  rfl

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Kernel of the canonical short-column quotient

The kernel is computed from the first-factor cyclotomic ideal on the prescribed
balanced tensor. No crossing-image source or injectivity assertion is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end

end

section

/-! # The balanced short moving-word map

The domain is `Rf ⊗_(S,j_L) Π^epsilon(eB)`. The lower balance is
proved using the full ELV moving-word error, including exterior coefficients.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end

end
