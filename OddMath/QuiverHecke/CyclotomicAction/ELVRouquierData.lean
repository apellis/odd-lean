/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossingSquare
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import OddMath.Algebra.FiniteSupermoduleFunctor

/-! # Rouquier generator data on the full-coefficient weight categories

Brundan--Ellis Definition 1.5 and DeformedActionAssembly §6: assemble the
prescribed weight induction, dot and crossing in the actual PiSCat target.
The same-colour square is a native two-morphism equation. No local inverse
or complete factor-family assertion is supplied.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u

section Total
variable {k : Type u} [CommRing k]
    {C B : Type*} [Category* C] [Category* B]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive B] [Linear k B] [Supercategory k B]

/-- Total components detect a supernatural map into any supercategory. -/
theorem supernatural_hom_ext_total {F G : Superfunctor k C B} {f g : F ⟶ G}
    (h : ∀ t, f.total t = g.total t) : f = g := by
  apply Superfunctor.hom_ext
  intro p t
  have hp (s : F ⟶ G) : proj k p (s.total t) = s.app p t := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact proj_eq_of_add rfl (s.app_mem 0 t) (s.app_mem 1 t)
    · exact proj_eq_of_add (add_comm _ _) (s.app_mem 1 t)
        (by simpa using s.app_mem 0 t)
  rw [← hp f, ← hp g, h t]

theorem supernatural_zero_total {F G : Superfunctor k C B} (t : C) :
    (0 : F ⟶ G).total t = 0 := by
  simp only [SuperNatTrans.total, Superfunctor.zero_app, zero_add]

theorem supernatural_total_of_mem {F G : Superfunctor k C B}
    {p : ZMod 2} {f : F ⟶ G} (hf : f ∈ parity (R := k) _ _ p) (t : C) :
    f.total t = f.app p t := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

theorem supernatural_square_zero_of_total {F : Superfunctor k C B} (f : F ⟶ F)
    (h : ∀ t, f.total t ≫ f.total t = 0) : f ≫ f = 0 := by
  apply supernatural_hom_ext_total
  intro t
  rw [Superfunctor.comp_total, supernatural_zero_total]
  exact h t
end Total

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- The given action crossing, as a two-morphism, has square zero on every
weight category. The proof includes every absent predecessor component. -/
theorem elvActionCross_square (i : I) (Λ : X) {x₀ x₁ x₂ : X}
    (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) :
    elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ ≫
      elvActionCross D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂ = 0 := by
  apply supernatural_square_zero_of_total
  intro M
  simp only [supernatural_total_of_mem
    (elvActionCross_mem D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂) M]
  funext ε
  change elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M ε ≫
    elvWeightCrossComponent D Sc cutoff bound i i Λ h₁ h₂ h₁ h₂
      (D.parity i * D.parity i) M ε = 0
  apply FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, supernatural_zero_total]
  exact elvWeightCrossComponent_square_total D Sc cutoff bound i Λ h₁ h₂ M ε w

/-- The prescribed upward generators on the original weight spaces.
This is generator data, not a complete relation-preserving factor action. -/
def elvRouquierData (Λ : X) :
    SKM.RouquierData (k := k) (B := PiSCat.{u, u, u + 1} k) D where
  obj x := elvWeightSpace D Sc cutoff bound Λ x
  E i _ _ h := elvE D Sc cutoff bound i Λ h
  dot i _ _ h := elvActionDot D Sc cutoff bound i Λ h
  dot_mem i _ _ h := elvActionDot_mem D Sc cutoff bound i Λ h
  cross i j _ _ _ _ h₁ h₂ h₃ h₄ := elvActionCross D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄
  cross_mem i j _ _ _ _ h₁ h₂ h₃ h₄ := elvActionCross_mem D Sc cutoff bound i j Λ h₁ h₂ h₃ h₄

theorem elvRouquierData_square (i : I) (Λ : X) {x₀ x₁ x₂ : X}
    (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂) :
    (elvRouquierData D Sc cutoff bound Λ).cross i i h₁ h₂ h₁ h₂ ≫
      (elvRouquierData D Sc cutoff bound Λ).cross i i h₁ h₂ h₁ h₂ = 0 :=
  elvActionCross_square D Sc cutoff bound i Λ h₁ h₂

end OddMath.QuiverHecke.ELVOld
