/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Operations


/-!
# Nilpotent perturbations of isomorphisms

In a `k`-linear category, an isomorphism `a` stays an isomorphism after adding a morphism
divisible by a nilpotent ideal `J` of `k`: `a + b = (1 + b a⁻¹) a`, and `b a⁻¹` is nilpotent
because composition multiplies ideal levels (`comp_mem_pow_smul`).

This is the perturbation step needed when the parameters of Brundan–Wang–Webster
(arXiv:2505.22929v2, §2.2) are used in place of those of Brundan–Ellis: the pure terms
`cᵢⱼ(r, 0) u^r` of `Qᵢⱼ(u, 0)` have positive coefficient degree, so over a truncated Rees
base they lie in a nilpotent ideal, and the mixed mates built from `tᵢⱼ u^{dᵢⱼ}` remain
invertible.

* `comp_mem_pow_smul`: `J^m Hom ∘ J^n Hom ⊆ J^{m+n} Hom`.
* `isNilpotent_of_mem_smul`: an endomorphism in `J • End X` with `J^N = 0` is nilpotent.
* `isIso_add_of_mem_smul`: the perturbation statement.
-/

open CategoryTheory

namespace OddMath.Algebra

universe v u w

variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- Composition multiplies the ideal levels of morphisms divisible by an ideal. -/
theorem comp_mem_pow_smul (J : Ideal k) {X Y Z : C} {m n : ℕ}
    {f : X ⟶ Y} (hf : f ∈ (J ^ m) • (⊤ : Submodule k (X ⟶ Y)))
    {g : Y ⟶ Z} (hg : g ∈ (J ^ n) • (⊤ : Submodule k (Y ⟶ Z))) :
    f ≫ g ∈ (J ^ (m + n)) • (⊤ : Submodule k (X ⟶ Z)) := by
  refine Submodule.smul_induction_on hf ?_ ?_
  · intro a ha f _
    refine Submodule.smul_induction_on hg ?_ ?_
    · intro b hb g _
      rw [Linear.smul_comp, Linear.comp_smul, smul_smul, pow_add]
      exact Submodule.smul_mem_smul (Ideal.mul_mem_mul ha hb) Submodule.mem_top
    · intro g g' hg hg'
      rw [Preadditive.comp_add]
      exact Submodule.add_mem _ hg hg'
  · intro f f' hf hf'
    rw [Preadditive.add_comp]
    exact Submodule.add_mem _ hf hf'

/-- An endomorphism divisible by a nilpotent ideal is nilpotent. -/
theorem isNilpotent_of_mem_smul (J : Ideal k) {N : ℕ} (hJ : J ^ N = ⊥) {X : C}
    {e : End X} (he : e ∈ J • (⊤ : Submodule k (X ⟶ X))) : IsNilpotent e := by
  have key : ∀ n : ℕ, (e ^ n : End X) ∈ (J ^ n) • (⊤ : Submodule k (X ⟶ X)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show e ^ (n + 1) = (e ^ n) ≫ e by rw [pow_succ', End.mul_def]]
      exact comp_mem_pow_smul J (m := n) (n := 1) (f := e ^ n) (g := e) ih (by rwa [pow_one])
  refine ⟨N, ?_⟩
  have h := key N
  rw [hJ, Submodule.bot_smul] at h
  exact (Submodule.mem_bot k).mp h

/-- **Nilpotent perturbation.** An isomorphism perturbed by a morphism divisible by a
nilpotent ideal of the base ring is still an isomorphism. -/
theorem isIso_add_of_mem_smul (J : Ideal k) {N : ℕ} (hJ : J ^ N = ⊥) {X Y : C}
    (a : X ⟶ Y) [IsIso a] {b : X ⟶ Y} (hb : b ∈ J • (⊤ : Submodule k (X ⟶ Y))) :
    IsIso (a + b) := by
  have he : b ≫ inv a ∈ J • (⊤ : Submodule k (X ⟶ X)) := by
    have h := comp_mem_pow_smul J (m := 1) (n := 0) (f := b) (g := inv a)
      (by rwa [pow_one]) (by simp)
    rwa [pow_one] at h
  obtain ⟨u, hu⟩ := (isNilpotent_of_mem_smul J hJ (e := (b ≫ inv a : End X)) he).isUnit_one_add
  have hiso : IsIso (𝟙 X + b ≫ inv a) :=
    have hu' : (u.val : X ⟶ X) = 𝟙 X + b ≫ inv a := hu
    ⟨⟨u.inv, by rw [← hu']; exact u.inv_val, by rw [← hu']; exact u.val_inv⟩⟩
  have e : a + b = (𝟙 X + b ≫ inv a) ≫ a := by
    rw [Preadditive.add_comp, Category.id_comp, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
  rw [e]
  infer_instance

end OddMath.Algebra
