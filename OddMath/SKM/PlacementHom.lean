/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Placement

/-!
# Placement of homogeneous morphisms with changing boundaries

`plcL_interchange_hom` proves super interchange for two homogeneous morphisms,
neither of which need be an endomorphism. `plcL_nested` combines successive
placements. Explicit region and word transports retain the dependent boundary
data needed for bending cups and caps in the pitchfork relations.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

/-- Transport a morphism along an equality of its right-hand region. -/
def regionCast {μ ν : X} (h : μ = ν) {s t : List (Letter I)}
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t) := h ▸ f

@[simp] theorem regionCast_cl {μ ν : X} (h : μ = ν) (s t : List (Letter I))
    (L : List (LayerData I)) :
    regionCast (D := D) (Sc := Sc) h (cl D Sc μ s t L) = cl D Sc ν s t L := by
  subst ν; rfl

@[simp] theorem regionCast_add {μ ν : X} (h : μ = ν) {s t : List (Letter I)}
    (f g : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    regionCast h (f + g) = regionCast h f + regionCast h g := by
  subst ν; rfl

@[simp] theorem regionCast_smul {μ ν : X} (h : μ = ν) {s t : List (Letter I)}
    (a : k) (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    regionCast h (a • f) = a • regionCast h f := by
  subst ν; rfl

@[simp] theorem regionCast_zero {μ ν : X} (h : μ = ν) (s t : List (Letter I)) :
    regionCast (D := D) (Sc := Sc) h (0 : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) = 0 := by
  subst ν; rfl

def wordCast (μ : X) {s t s' t' : List (Letter I)} (hs : s = s') (ht : t = t') :
    ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) →ₗ[k]
      ((pres D Sc).obj (ob D μ s') ⟶ (pres D Sc).obj (ob D μ t')) := by
  subst s'; subst t'; exact LinearMap.id

@[simp] theorem wordCast_cl (μ : X) {s t s' t' : List (Letter I)}
    (hs : s = s') (ht : t = t') (M : List (LayerData I)) :
    wordCast μ hs ht (cl D Sc μ s t M) = cl D Sc μ s' t' M := by
  subst s'; subst t'; rfl

def plcRight (μ : X) (s a b : List (Letter I)) :
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) →ₗ[k]
      ((pres D Sc).obj (ob D μ (s ++ a)) ⟶ (pres D Sc).obj (ob D μ (s ++ b))) :=
  (wordCast μ (List.append_nil (s ++ a)) (List.append_nil (s ++ b))).comp
    (plcL D Sc μ s [] a b)

theorem plcRight_cl (μ : X) (s a b : List (Letter I)) (M : List (LayerData I)) :
    plcRight μ s a b (cl D Sc μ a b M) =
      cl D Sc μ (s ++ a) (s ++ b) (M.map (whL s [])) := by
  dsimp only [plcRight, LinearMap.comp_apply]
  erw [plcL_cl D Sc μ s [] a b M, wordCast_cl]

/-- Interchange of two homogeneous morphisms, allowing both to change their boundary words. -/
theorem plcL_interchange_hom (μ : X) {s t a b : List (Letter I)}
    (hw : wt D μ a = wt D μ b) {p q : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ a) s) ⟶ (pres D Sc).obj (ob D (wt D μ a) t)}
    {g : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (hf : f ∈ homPar D Sc (wt D μ a) s t p) (hg : g ∈ homPar D Sc μ a b q) :
    plcL D Sc μ [] a s t f ≫ plcRight μ t a b g =
      zsign k (p * q) •
        (plcRight μ s a b g ≫ plcL D Sc μ [] b s t (regionCast hw f)) := by
  refine homPar_induction₂ (P := fun f g =>
    plcL D Sc μ [] a s t f ≫ plcRight μ t a b g =
      zsign k (p * q) •
        (plcRight μ s a b g ≫ plcL D Sc μ [] b s t (regionCast hw f)))
    (fun L M hL hp hM hq => ?_)
    (fun g => by rw [map_zero, regionCast_zero, map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero])
    (fun f => by rw [map_zero, map_zero, Limits.comp_zero, Limits.zero_comp, smul_zero])
    (fun f₁ f₂ g h₁ h₂ => by
      simp only [map_add, regionCast_add, Preadditive.add_comp, Preadditive.comp_add, smul_add, h₁, h₂])
    (fun f g₁ g₂ h₁ h₂ => by
      simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, smul_add, h₁, h₂])
    (fun r f g h => by
      simp only [map_smul, regionCast_smul, Linear.smul_comp, Linear.comp_smul, h, smul_comm r])
    (fun r f g h => by
      simp only [map_smul, Linear.smul_comp, Linear.comp_smul, h, smul_comm r]) hf hg
  simp only [plcL_cl, plcRight_cl, regionCast_cl]
  have hLa : SChain (s ++ a) (L.map (whL [] a)) (t ++ a) := by simpa using hL.whisk [] a
  have hLb : SChain (s ++ b) (L.map (whL [] b)) (t ++ b) := by simpa using hL.whisk [] b
  have hMs : SChain (s ++ a) (M.map (whL s [])) (s ++ b) := by simpa using hM.whisk s []
  have hMt : SChain (t ++ a) (M.map (whL t [])) (t ++ b) := by simpa using hM.whisk t []
  simp only [List.nil_append]
  rw [cl_comp hLa hMt, cl_comp hMs hLb]
  have E := cl_interchange (D := D) (Sc := Sc) (μ := μ) (S := s ++ a) (T := t ++ b) [] [] hL hM
  simpa only [List.nil_append, List.append_nil, hp, hq] using E

@[simp] theorem regionCast_family {μ ν : X} (h : μ = ν) {s t : List (Letter I)}
    (f : ∀ ν, (pres D Sc).obj (ob D ν s) ⟶ (pres D Sc).obj (ob D ν t)) :
    regionCast h (f μ) = f ν := by
  subst ν; rfl

theorem plcL_mem (μ : X) (u v : List (Letter I)) {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ homPar D Sc (wt D μ v) s t p) :
    plcL D Sc μ u v s t f ∈ homPar D Sc μ (u ++ s ++ v) (u ++ t ++ v) p := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, hp, rfl⟩ := hf
    rw [plcL_cl]
    exact cl_mem_homPar (hL.whisk u v) (by simpa only [parsum_map_whL] using hp)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem plcL_nested (μ : X) (u v u' v' : List (Letter I))
    {s t : List (Letter I)} {p : ZMod 2}
    {f : (pres D Sc).obj (ob D (wt D (wt D μ v) v') s) ⟶
      (pres D Sc).obj (ob D (wt D (wt D μ v) v') t)}
    (hf : f ∈ homPar D Sc (wt D (wt D μ v) v') s t p) :
    wordCast μ (by simp only [List.append_assoc]) (by simp only [List.append_assoc])
      (plcL D Sc μ u v (u' ++ s ++ v') (u' ++ t ++ v')
        (plcL D Sc (wt D μ v) u' v' s t f)) =
      plcL D Sc μ (u ++ u') (v' ++ v) s t
        (regionCast (wt_append D μ v' v).symm f) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, hp, rfl⟩ := hf
    simp only [plcL_cl, wordCast_cl, regionCast_cl]
    congr 1
    simp only [List.map_map]
    apply List.map_congr_left
    intro x _
    rcases x with ⟨a, g, b⟩
    simp only [Function.comp_apply, whL, List.append_assoc]
  | zero => simp only [map_zero, regionCast_zero]
  | add x y _ _ hx hy => simp only [map_add, regionCast_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, regionCast_smul, hx]

end OddMath.SKM
