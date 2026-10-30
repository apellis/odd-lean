/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicPprime
import OddMath.QuiverHecke.CyclotomicAction.ELVChronologicalShort
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVCokernel

/-! # Short columns into the old-only resolution

The balanced columns land in the original prepend and append quotients.
Their square uses the literal moving-word map, before the final cyclotomic quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- The short source column in signed old-only coordinates. -/
def alphaPair (i : I) (v s t : List I) :
    hom D Sc cutoff (i :: s) t →ₗ[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      Target D Sc cutoff i v (t ++ [i]) where
  toFun h := pair D Sc cutoff (epsilon D cutoff i v) i (rightContext D Sc cutoff [i] _ _ h)
  map_add' h h' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [pair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a h := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [pair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem alphaPair_mk (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : hom D Sc cutoff v (s ++ [i])) :
    alphaPair D Sc cutoff i v s t h ((ideal D Sc cutoff _ _).mkQ b) =
      projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i _ _ (twist k (epsilon D cutoff i v) b) ≫
          rightContext D Sc cutoff [i] _ _ h) := rfl

theorem alphaPair_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (h : hom D Sc cutoff (i :: s') t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    alphaPair D Sc cutoff i v s t (insert D Sc cutoff i s s' r ≫ h) b =
      alphaPair D Sc cutoff i v s' t h
        ((coefficient D Sc cutoff (epsilon D cutoff i v) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change projection D Sc cutoff i v (t ++ [i]) _ =
    projection D Sc cutoff i v (t ++ [i]) _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply]
  rw [rightContext_comp, rightContext_insert, twist_comp, ← rightContext_twist,
    twist_twist, insert_comp, Category.assoc]

/-- The prescribed short source column into the original Mackey source. -/
def alpha (i : I) (v t : List I) : PprimeDomain D Sc cutoff i v t →ₗ[k]
    Target D Sc cutoff i v (t ++ [i]) :=
  BalancedInduction.lift (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩
    (fun s => TensorProduct.lift (alphaPair D Sc cutoff i v s.word t))
    (fun s s' r h b => alphaPair_balance D Sc cutoff i v s.word s'.word t r h b)

@[simp] theorem alpha_tensor (i : I) (v s t : List I)
    (h : hom D Sc cutoff (i :: s) t) (b : Old D Sc cutoff v (s ++ [i])) :
    alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s t h b) =
      alphaPair D Sc cutoff i v s t h b := by
  exact BalancedInduction.lift_tensor (affinePrepend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (epsilon D cutoff i v) i v) ⟨t⟩ _ _ ⟨s⟩ h b

/-- The crossing column before imposing the enlarged cyclotomic ideal. -/
def shortCrossPair (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t →ₗ[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      AppendTarget D Sc cutoff i v (t ++ [i]) where
  toFun c := appendPair D Sc cutoff 0 i
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫ rightContext D Sc cutoff [i] _ _ c)
  map_add' c c' := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [appendPair_mk, map_add, Preadditive.comp_add, LinearMap.add_apply]
  map_smul' a c := by
    apply LinearMap.ext
    intro b
    obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
    simp only [appendPair_mk, map_smul, Linear.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem shortCrossPair_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    shortCrossPair D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ b) =
      appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ b ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ c) := by
  change appendProjection D Sc cutoff i v (t ++ [i]) _ = _
  simp only [LinearMap.comp_apply, Linear.rightComp_apply, twist_zero]

theorem shortCrossPair_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortCrossPair D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortCrossPair D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s ++ [i])).mkQ_surjective b
  change shortCrossPair D Sc cutoff i v s t _ ((ideal D Sc cutoff _ _).mkQ b) =
    shortCrossPair D Sc cutoff i v s' t _ ((ideal D Sc cutoff _ _).mkQ
      (b ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i) r)))
  rw [shortCrossPair_mk, shortCrossPair_mk]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have h := crossLast_comp_rightContext D Sc cutoff i i r
  rw [hp] at h
  simp only [rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)), h]
  simp only [Category.assoc]

/-- The balanced short crossing column into the old-only append target. -/
def shortCross (i : I) (v t : List I) : ShortTarget D Sc cutoff i v t →ₗ[k]
    AppendTarget D Sc cutoff i v (t ++ [i]) :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => TensorProduct.lift (shortCrossPair D Sc cutoff i v s.word t))
    (fun s s' r c b => shortCrossPair_balance D Sc cutoff i v s.word s'.word t r c b)

@[simp] theorem shortCross_tensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c b) =
      shortCrossPair D Sc cutoff i v s t c b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The short-column square with the original moving-word map. -/
theorem shortColumn_square (i : I) (v t : List I) :
    pMap D Sc cutoff i v (t ++ [i]) ∘ₗ alpha D Sc cutoff i v t =
      shortCross D Sc cutoff i v t ∘ₗ pprime D Sc cutoff i v t := by
  apply BalancedInduction.hom_ext
  intro s h b
  change pMap D Sc cutoff i v (t ++ [i])
    (alpha D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b)) =
    shortCross D Sc cutoff i v t
      (pprime D Sc cutoff i v t (pprimeTensor D Sc cutoff i v s.word t h b))
  rw [alpha_tensor, pprime_tensor, shortCross_tensor]
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  rw [alphaPair_mk, shortCrossPair_mk, pMap_chronologicalShort_generator]
  change appendProjection D Sc cutoff i v (t ++ [i])
    (rightContext D Sc cutoff [i] _ _
      (twist k (appendQ D cutoff i v) (twist k (appendQ D cutoff i v) b)) ≫ _) = _
  rw [twist_twist]

/-- The right square lands in the independently prescribed cyclotomic source. -/
theorem shortColumn_quotient_square (i : I) (v t : List I) :
    canonicalAppendTarget D Sc cutoff i v (t ++ [i]) ∘ₗ shortCross D Sc cutoff i v t =
      toCyclotomic D Sc cutoff i v t ∘ₗ q D Sc cutoff i v t := by
  apply BalancedInduction.hom_ext
  intro s c b
  change canonicalAppendTarget D Sc cutoff i v (t ++ [i])
    (shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b)) =
    toCyclotomic D Sc cutoff i v t
      (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c b))
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
  rw [shortCross_tensor, shortCrossPair_mk, canonicalAppendTarget_projection,
    toCyclotomic_q_shortTensor]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
