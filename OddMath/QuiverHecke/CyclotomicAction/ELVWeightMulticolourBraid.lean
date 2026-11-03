import OddMath.QuiverHecke.CyclotomicAction.ELVWeightBraidPathsComparison

/-! # The prescribed multicolour braid of the weight action

Brundan--Ellis (1.9) outside the repeated-outer correction case. The six
selected chart squares prove the equality for all input modules and all
output blocks, including absent predecessor sectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem total_three {k : Type u} [CommRing k]
    {A B : PiSCat.{u, u, u + 1} k} {F₀ F₁ F₂ F₃ : A ⟶ B}
    (f : F₀ ⟶ F₁) (g : F₁ ⟶ F₂) (h : F₂ ⟶ F₃) (M : A) :
    (f ≫ g ≫ h).total M = f.total M ≫ g.total M ≫ h.total M := by
  rw [Superfunctor.comp_total, Superfunctor.comp_total]

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i j l : I) (Λ : X) {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)
local notation "a₀" => elvWeightSuffixCross D Sc cutoff bound i j l Λ hal hlj hd₁ hli hd₂
local notation "a₁" => elvWeightPrefixCross D Sc cutoff bound j i l Λ hal hli hai hil hd₂
local notation "a₂" => elvWeightSuffixCross D Sc cutoff bound j l i Λ hai hil hd₂ hij hd₃
local notation "b₀" => elvWeightPrefixCross D Sc cutoff bound i j l Λ hal hlj haj hjl hd₁
local notation "b₁" => elvWeightSuffixCross D Sc cutoff bound i l j Λ haj hjl hd₁ hji hd₃
local notation "b₂" => elvWeightPrefixCross D Sc cutoff bound l i j Λ haj hji hai hij hd₃

/-- The given six multicolour crossing natural transformations satisfy
the uncorrected braid on all input modules and every output block. -/
theorem elvActionCross_multicolour_braid (hb : ¬ (i = l ∧ i ≠ j)) :
    a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂ := by
  apply supernatural_hom_ext_total
  intro M
  funext ε
  have hL := congrFun (total_three a₀ a₁ a₂ M) ε
  have hR := congrFun (total_three b₀ b₁ b₂ M) ε
  by_cases hs : ∃ β, elvBlockSucc₃ D i j l Λ hal hlj hd₁ β = ε
  · obtain ⟨β, rfl⟩ := hs
    have h := elvWeightBraid_paths D Sc cutoff bound i j l Λ
      hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ β hb M
    exact hL.trans (h.trans hR.symm)
  · have hz := elvEFunctor_comp₃_isZero D Sc cutoff bound i j l Λ hal hlj hd₁ ε hs M
    exact hL.trans ((hz.eq_of_src _ _).trans hR.symm)

end OddMath.QuiverHecke.ELVOld
