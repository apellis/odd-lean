/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.Functor
import OddMath.SKM.Grading

/-!
# The 2-functor `𝔘(𝔤) → U` preserves degrees

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, the grading after
(1.31), and A. D. Lauda, M. Khovanov, *A categorification of quantum sl(n)* III,
arXiv:0807.3250, Definition 3.1 ii).

With the symmetrizer `dᵢ = (i·i)/2` (`symmetrizer`), the image under `evenFunctor` of each
generator of Definition 1.5 is homogeneous, for KL III's grading, of the degree of the generator
in the table after (1.31) (`imgS_mem_homDeg`). Hence `evenFunctor` maps the degree-`d` part of a
Hom-space of `𝔘(𝔤)` into the degree-`d` part of the corresponding Hom-space of `U`
(`evenFunctor_map_mem_homDeg`).
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open CategoryTheory Categorification.KL3

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : Categorification.QuantumGroup.CartanDatum I) (hc : Compatible D C)
  (k : Type w) [CommRing k] (Sc : Scalars D k) (hD : IsEven D) (hS : IsKLScalars D k Sc)

/-- Shorthand for the KL III weight datum of `D`. -/
local notation "RD" => weightDatum D C hc

/-- **The images of the generators are homogeneous** of the degrees of the table after
(1.31), for the symmetrizer `dᵢ = (i·i)/2`. -/
theorem imgS_mem_homDeg (ν : X) (g : Shape I) :
    imgS D C hc k ν g ∈ (Diagram.pres RD k).homDeg (Diagram.deg RD) (Diagram.ob RD ν g.dom)
      (Diagram.ob RD ν g.cod) (gdeg D (symmetrizer D C hc) (g, ν)) := by
  cases g with
  | dot i =>
    refine Diagram.dg_mem_homDeg ?_
    simp [Diagram.sdeg, gdeg, ← Categorification.QuantumGroup.UDot.two_mul_di]
  | cross i j =>
    refine Diagram.dg_mem_homDeg ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Diagram.sdeg,
      gdeg, symmetrizer_d, d_eq hc, mul_neg, Categorification.QuantumGroup.UDot.di_mul_A]
  | cup i =>
    refine Diagram.dg_mem_homDeg ?_
    simp [Diagram.sdeg, gdeg, Categorification.QuantumGroup.UDot.sgn, Diagram.wt]
  | cap i =>
    refine Diagram.dg_mem_homDeg ?_
    simp [Diagram.sdeg, gdeg, Categorification.QuantumGroup.UDot.sgn, Diagram.wt, sub_eq_add_neg]
  | lcross i j =>
    exact Diagram.crossrL_mem j i ν
  | dcup i n =>
    simp only [imgS]
    split_ifs with hn
    · refine Submodule.sum_mem _ fun g hg => ?_
      have hg' := Finset.mem_range.1 hg
      have h1 : Diagram.ccwU RD k ν i (-Diagram.ip RD i ν - 1 + g) ∈
          (Diagram.pres RD k).homDeg (Diagram.deg RD) _ _ _ := Diagram.ccwU_mem ν i _
      have hlt : n + g < (Diagram.ip RD i ν).toNat := by omega
      have h2 : Diagram.betaEF RD k i ν (n + g) ∈
          (Diagram.pres RD k).homDeg (Diagram.deg RD) _ _ _ := Diagram.betaEF_mem i ν (n + g) hlt
      have h := StringDiagrams.Presentation.comp_mem_homDeg h1 h2
      have e : 2 * Categorification.QuantumGroup.UDot.di C i *
          (-Diagram.ip RD i ν - 1 + g + 1 + Diagram.ip RD i ν) +
          Categorification.QuantumGroup.UDot.di C i *
            (Diagram.ip RD i ν - 1 - 2 * ((n + g : ℕ) : ℤ)) =
          gdeg D (symmetrizer D C hc) (Shape.dcup i n, ν) := by
        simp only [gdeg, symmetrizer_d]
        push_cast
        have : Diagram.ip RD i ν = D.h i ν := rfl
        rw [this]
        ring
      rw [e] at h
      exact h
    · exact Submodule.zero_mem _
  | dcap i n =>
    simp only [imgS]
    split_ifs with hn
    · have h : Diagram.alphaFE RD k i ν ((-Diagram.ip RD i ν).toNat - 1 - n) ∈
          (Diagram.pres RD k).homDeg (Diagram.deg RD) _ _ _ := Diagram.alphaFE_mem i ν _
      have e : Categorification.QuantumGroup.UDot.di C i *
          (2 * (((-Diagram.ip RD i ν).toNat - 1 - n : ℕ) : ℤ) + 1 + Diagram.ip RD i ν) =
          gdeg D (symmetrizer D C hc) (Shape.dcap i n, ν) := by
        simp only [gdeg, symmetrizer_d]
        have : Diagram.ip RD i ν = D.h i ν := rfl
        have hc' : (((-Diagram.ip RD i ν).toNat - 1 - n : ℕ) : ℤ) = -D.h i ν - 1 - n := by
          rw [this] at hn ⊢; omega
        rw [hc', this]
        ring
      rw [e] at h
      exact h
    · exact Submodule.zero_mem _

theorem img_mem_homDeg (g : Shape I × X) :
    img D C hc k g ∈ (Diagram.pres RD k).homDeg (Diagram.deg RD)
      (StringDiagrams.LocalMap.genDom (κ D C hc) g) (StringDiagrams.LocalMap.genCod (κ D C hc) g)
      (gdeg D (symmetrizer D C hc) g) := by
  have h := StringDiagrams.Presentation.comp_mem_homDeg
    (StringDiagrams.Presentation.eqToHom_mem_homDeg (P := Diagram.pres RD k) (Diagram.deg RD)
      (congrArg (Diagram.pres RD k).obj (genDom_eq D C hc g.2 g.1)))
    (StringDiagrams.Presentation.comp_mem_homDeg (imgS_mem_homDeg D C hc k g.2 g.1)
      (StringDiagrams.Presentation.eqToHom_mem_homDeg (P := Diagram.pres RD k) (Diagram.deg RD)
        (congrArg (Diagram.pres RD k).obj (genCod_eq D C hc g.2 g.1)).symm))
  rw [zero_add, add_zero] at h
  exact h

theorem locMap_preservesDeg :
    (locMap D C hc k).PreservesDeg (gdeg D (symmetrizer D C hc)) (Diagram.deg RD) :=
  StringDiagrams.LocalMap.ofGen_preservesDeg _ _ (img_mem_homDeg D C hc k)

/-- **`evenFunctor` preserves degrees**: it maps the degree-`d` part of a Hom-space of `𝔘(𝔤)`
(grading after (1.31), `dᵢ = (i·i)/2`) into the degree-`d` part of KL III's `U`. -/
theorem evenFunctor_map_mem_homDeg {a b : StringDiagrams.Obj (sig D)}
    {x : (pres D Sc).obj a ⟶ (pres D Sc).obj b} {d : ℤ}
    (hx : x ∈ (pres D Sc).homDeg (gdeg D (symmetrizer D C hc)) a b d) :
    (evenFunctor D C hc k Sc hD hS).map x ∈ (Diagram.pres RD k).homDeg (Diagram.deg RD)
      ((κ D C hc).obj a) ((κ D C hc).obj b) d := by
  unfold evenFunctor StringDiagrams.LocalMap.liftGen
  exact StringDiagrams.LocalMap.lift_mem_homDeg (φ := fun _ : Unit => locMap D C hc k) _ _ _ _ ()
    (locMap_preservesDeg D C hc k) hx

end OddMath.SKM.EvenBridge
