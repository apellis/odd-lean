import OddMath.QuiverHecke.CyclotomicAction.ELVContentTripleTensor
/-! # Suffix-first content induction on tensors

The second composition tree for DeformedActionAssembly.md §6, retaining its endpoint casts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
universe u
namespace OddMath.QuiverHecke.ELVOld
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
/-- Equality morphisms in the two append trees compose coherently. -/
theorem composition_cast_arrow
    {C B E F : Type u} [Category C] [Category B] [Category E] [Category F]
    (J : C ⥤ B) (K : B ⥤ E) (L : E ⥤ F)
    (A : C ⥤ E) (B' : B ⥤ F) (H : C ⥤ F)
    (eA : J ⋙ K = A) (eB : K ⋙ L = B')
    (eH : A ⋙ L = H) (eH' : J ⋙ B' = H)
    (v : C) (w : B) (z : E) (t : F)
    (a : J.obj v ⟶ w) (b : K.obj w ⟶ z) (g : L.obj z ⟶ t) :
    eqToHom (congrArg (fun T => T.obj v) eH).symm ≫
      L.map (eqToHom (congrArg (fun T => T.obj v) eA).symm ≫ K.map a ≫ b) ≫ g =
    eqToHom (congrArg (fun T => T.obj v) eH').symm ≫ B'.map a ≫
      eqToHom (congrArg (fun T => T.obj w) eB).symm ≫ L.map b ≫ g := by
  subst A
  subst B'
  subst H
  simp only [eqToHom_refl, Category.id_comp, Functor.map_comp, Functor.comp_map,
    Category.assoc]

section Pair
variable (β : Multiset I) (i j : I)
local notation "δ₁" => (β + ([i] : Multiset I))
local notation "δ₂" => ((β + ([i] : Multiset I)) + ([j] : Multiset I))
local notation "J" => contentAppend D Sc cutoff N β [i]
local notation "K" => contentAppend D Sc cutoff N δ₁ [j]

local notation "e" => contentAppend_comp_eq D Sc cutoff N β [i] [j] δ₂ rfl (contentPair_sum β i j)

theorem contentInductionComp_cast_arrow
    (τ : List I) (γ : Multiset I) (hγ : δ₂ + (τ : Multiset I) = γ)
    (hs : δ₁ + (([j] ++ τ : List I) : Multiset I) = γ)
    (h : β + (([i,j] ++ τ : List I) : Multiset I) = γ)
    (v : ContentCategory D Sc cutoff N β)
    (w : ContentCategory D Sc cutoff N δ₁) (z : ContentCategory D Sc cutoff N δ₂)
    (t : ContentCategory D Sc cutoff N γ)
    (g : (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).obj z ⟶ t)
    (b : (K).obj w ⟶ z) (a : (J).obj v ⟶ w) :
    eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_compTo_eq D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j)
          τ γ hγ h)).symm ≫
        (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).map
          (eqToHom (congrArg (fun F => F.obj v) e).symm ≫ (K).map a ≫ b) ≫ g =
    eqToHom (congrArg (fun F => F.obj v)
        (contentAppend_comp_eq D Sc cutoff N β [i] ([j] ++ τ) γ hs h)).symm ≫
        (contentAppendTo D Sc cutoff N δ₁ ([j] ++ τ) γ hs).map a ≫
        eqToHom (congrArg (fun F => F.obj w)
          (contentAppend_comp_eq D Sc cutoff N δ₁ [j] τ γ hγ hs)).symm ≫
        (contentAppendTo D Sc cutoff N δ₂ τ γ hγ).map b ≫ g := by
  apply composition_cast_arrow
  · exact e
  · exact contentAppend_comp_eq D Sc cutoff N δ₁ [j] τ γ hγ hs
  · exact contentAppend_compTo_eq D Sc cutoff N β [i,j] δ₂ (contentPair_sum β i j) τ γ hγ h
  · exact contentAppend_comp_eq D Sc cutoff N β [i] ([j] ++ τ) γ hs h
end Pair
end OddMath.QuiverHecke.ELVOld
