/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.LayerDegree
import OddMath.SKM.EvenBridge.GradedCount
import OddMath.SKM.EvenBridge.Full
import OddMath.SKM.EvenBridge.Degree
import OddMath.SKM.Nondegeneracy
import Categorification.Diagrams.KL3.Nondegeneracy
import Categorification.Diagrams.KL3.FinDimHomUp

/-!
# The Nondegeneracy Conjecture for purely even data

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture after Theorem 8.1: the decorated reduced matchings of Theorem 8.1 form
a basis of `HOM(E_a 1_μ, E_b 1_μ)` as a free module over the bubble algebra `SYM`.

For purely even data (`IsEven D`) with Khovanov–Lauda scalars (`IsKLScalars`), over every
commutative ring, and with finitely many colours, this file proves the conjecture
(`nondegeneracyConjecture_of_isEven`). The proof compares with Khovanov–Lauda's 2-category
(A. D. Lauda, M. Khovanov, *A categorification of quantum sl(n)*, arXiv:0807.3250v1, the
"KL III" paper), whose nondegeneracy (Theorem 1.2 with its nondegeneracy hypothesis, proved in
`Categorification.KL3.Diagram.calculusNondeg`) gives, by KL III §6.4, a homogeneous basis of
every Hom space over every commutative ring (`Categorification.KL3.Diagram.integralNondegBasis`):

* the 2-functor `evenFunctor` is full (`evenFunctor_surjective`) and preserves degrees
  (`evenFunctor_map_mem_homDeg`), so the composite of the expansion map with it is surjective
  and sends each decorated matching with a bubble monomial into one graded piece;
* by `spanDeg_monoIdxEquiv`, these are indexed by KL III's set `B_{𝐢,𝐣,λ}` with its degree;
* by KL III Proposition 3.12 each degree contains finitely many indices;
* in each degree the comparison with the KL basis is a surjective endomorphism of a finitely
  generated free module, hence injective by Orzech's theorem
  (`injective_of_surjective_of_basis`).

## Hypotheses

The statement carries, beyond the conjecture's own setting: purely even data, Khovanov–Lauda
scalars (`s = 0`, `t` as in KL III), a compatible symmetrizable Cartan datum and finitely many
colours. The ground ring is an arbitrary commutative ring. The general (super) conjecture is not
addressed.
-/

noncomputable section

namespace OddMath.SKM.EvenBridge

open CategoryTheory StringDiagrams Presentation Categorification.KL3 Categorification.QuantumGroup
  Module

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : CartanDatum I) (hc : Compatible D C)
  {k : Type w} [CommRing k] (Sc : Scalars D k) (hD : IsEven D) (hS : IsKLScalars D k Sc)

local notation "WD" => weightDatum D C hc

/-- `mapOb` preserves degrees. -/
theorem mapOb_mem_homD {μ : X} {s t : List (Letter I)}
    {x : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)} {d : ℤ}
    (hx : x ∈ (pres D Sc).homDeg (gdeg D (symmetrizer D C hc)) (ob D μ s) (ob D μ t) d) :
    mapOb D C hc k Sc hD hS μ s t x ∈ Diagram.HomD WD k μ s t d := by
  have h := comp_mem_homDeg (eqToHom_mem_homDeg (P := Diagram.pres WD k) (Diagram.deg WD)
      (congrArg (Diagram.pres WD k).obj (κ_obj_ob D C hc μ s)).symm)
    (comp_mem_homDeg (evenFunctor_map_mem_homDeg D C hc k Sc hD hS hx)
      (eqToHom_mem_homDeg (P := Diagram.pres WD k) (Diagram.deg WD)
        (congrArg (Diagram.pres WD k).obj (κ_obj_ob D C hc μ t))))
  rw [zero_add, add_zero] at h
  exact h

variable {D Sc}

include C hc hD hS

/-- **Injectivity of the expansion map for even data**: the decorated reduced matchings of a
`MatchingBasisChoice` are linearly independent over `SYM`, over every commutative ring. -/
theorem expansion_injective [Finite I] (cs : CScalars Sc) (μ : X) {a b : List (Letter I)}
    (F : MatchingBasisChoice a b) : Function.Injective (F.expansion cs μ) := by
  classical
  let B : Basis (MonoIdx F) k (F.Labels →₀ SYM D k) :=
    Finsupp.basis fun _ => symMonomialBasis hD
  let f := mapOb D C hc k Sc hD hS μ a b ∘ₗ F.expansion cs μ ∘ₗ B.repr.symm.toLinearMap
  let deg : MonoIdx F → ℤ := fun j => Diagram.spanDeg C ((WD).ellOf μ) (monoIdxEquiv F j)
  let KB : Basis (MonoIdx F) k _ :=
    (Diagram.integralNondegBasis k (Diagram.calculusNondeg WD ℚ) μ a b).reindex
      (monoIdxEquiv F).symm
  have hKB : ∀ j, KB j ∈ Diagram.HomD WD k μ a b (deg j) := by
    intro j
    simp only [KB, Basis.reindex_apply, Equiv.symm_symm, Diagram.integralNondegBasis_apply]
    exact Diagram.IntegralSpanning.twoB_mem μ a b _
  have hfin : ∀ d, Finite {j // deg j = d} := by
    intro d
    have := (Diagram.prop_3_12 WD (s := a) (t := b) μ d).1
    exact Finite.of_equiv _ ((monoIdxEquiv F).subtypeEquiv fun _ => Iff.rfl).symm
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := evenFunctor_surjective D C hc k Sc hD hS μ a b y
    obtain ⟨z, rfl⟩ := F.expansion_surjective cs μ g
    exact ⟨B.repr z, by simp [f, mapOb, hg]⟩
  have hdeg : ∀ j, f (Finsupp.single j 1) ∈ Diagram.HomD WD k μ a b (deg j) := by
    rintro ⟨t, m⟩
    have hB : B.repr.symm (Finsupp.single ⟨t, m⟩ 1) = Finsupp.single t (symMonomial hD m) := by
      rw [Basis.repr_symm_single_one, Finsupp.coe_basis]
      exact congrArg _ (symMonomialBasis_apply hD m)
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, hB,
      MatchingBasisChoice.expansion_single]
    refine mapOb_mem_homD D C hc Sc hD hS ?_
    rw [show deg ⟨t, m⟩ = bubbleDegree (symmetrizer D C hc) m +
        tableDegree D (symmetrizer D C hc) μ (F.layers t) by
      rw [show deg ⟨t, m⟩ = _ from spanDeg_monoIdxEquiv D C hc μ F ⟨t, m⟩, add_comm]]
    exact comp_mem_homDeg
      (bubAt_mem_gdeg _ a (betaSYM_symMonomial_mem_gdeg (symmetrizer D C hc) cs hD μ m))
      (xev_mem_gdeg _ cs μ a b (F.layers t))
  have hinj := injective_of_surjective_of_basis f hf (Diagram.HomD WD k μ a b)
    (Diagram.isInternal_homDeg (RD := WD) (k := k) _ _).submodule_iSupIndep deg hdeg KB hKB hfin
  intro x y hxy
  have := hinj (a₁ := B.repr x) (a₂ := B.repr y) (by simp [f, hxy])
  exact B.repr.injective this

/-- **The Nondegeneracy Conjecture of Brundan–Ellis (arXiv:1701.04133v2, §8) for purely even
data**, with Khovanov–Lauda scalars, a compatible Cartan datum and finitely many colours, over
every commutative ring: for all words `a`, `b`, every weight `μ` and every
`MatchingBasisChoice`, the decorated reduced matchings of Theorem 8.1 are a basis of `HOM(E_a 1_μ, E_b 1_μ)` over `SYM`. -/
theorem nondegeneracyConjecture_of_isEven [Finite I] (cs : CScalars Sc) :
    NondegeneracyConjecture cs :=
  (nondegeneracyConjecture_iff_injective cs).2 fun _ _ _ μ F =>
    expansion_injective C hc hD hS cs μ F

end OddMath.SKM.EvenBridge
