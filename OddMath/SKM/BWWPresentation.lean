/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Presentation
import OddMath.SKM.BWWBoxSum

/-!
# The Kac–Moody 2-supercategory with Brundan–Wang–Webster parameters

J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2, §2.2: the polynomials
`Qᵢⱼ(u, v) = Σ_{p ≤ dᵢⱼ, q ≤ dⱼᵢ} cᵢⱼ(p, q) u^p v^q`, in the presentation of
J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5
(`OddMath.SKM.pres`).

For parameters `Sc' : BWWScalars D k` only two relations change: the quadratic relation
(1.7) for `dᵢⱼ ≠ 0` (`quadSum`) and the correction term of the braid relation (1.9) for
`i ≠ j` (`braidSum`). Each is one sum over the box `[0, dᵢⱼ] × [0, dⱼᵢ]`; the leading term
`tᵢⱼ u^{dᵢⱼ}` of the braid correction is the corner `(dᵢⱼ, 0)`. All other relations are those
of `pres D Sc'.toScalars`.

* `presBWW D Sc'`: the presentation, on the relation labels of `pres`; its relations are
  parity-homogeneous (`isParityHomogeneous_presBWW`).
* `presBWW_toBWW`: `presBWW D Sc.toBWW = pres D Sc` for Brundan–Ellis parameters `Sc`.
* `presBWW_eq_pres_of_noPure`: without pure monomials, `presBWW D Sc' = pres D Sc'.toScalars`.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams LinDiagram
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
variable {k : Type w} [CommRing k]

theorem dg_congr (μ : X) {t t' : List (Letter I)} {ls ls' : List (LayerData I)}
    (h : SChain t ls t') (h' : SChain t ls' t') (e : ls = ls') :
    dg (k := k) D μ ls h = dg D μ ls' h' := by
  subst e; rfl

/-- The quadratic term `Qᵢⱼ(v, u)` on `Eᵢ Eⱼ 1_ν`: `Σ_{p ≤ dᵢⱼ, q ≤ dⱼᵢ} cᵢⱼ(p, q) v^q u^p`. -/
def quadSum (c : I → I → ℕ → ℕ → k) (i j : I) (ν : X) :
    LinDiagram k (ob D ν [up i, up j]) (ob D ν [up i, up j]) :=
  ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1),
    c i j p q • dg D ν (dotsL [up i] j [] q ++ dotsL [] i [up j] p)
      ((sChain_dotsL [up i] j [] q).append (sChain_dotsL [] i [up j] p))

/-- The correction term of the braid relation for `i ≠ j`:
`Σ_{p,q} cᵢⱼ(p, q) Σ_{s<p} ζ(|i|(|j| + s)) u₁^s v^q u₃^{p-1-s}`. -/
def braidSum (c : I → I → ℕ → ℕ → k) (i j : I) (ν : X) :
    LinDiagram k (ob D ν [up i, up j, up i]) (ob D ν [up i, up j, up i]) :=
  ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1), ∑ s ∈ Finset.range p,
    (zsign k (D.parity i * (D.parity j + s)) * c i j p q) •
      dg D ν (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
          dotsL [] i [up j, up i] (p - 1 - s))
        (((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [up i] j [up i] q)).append
          (sChain_dotsL [] i [up j, up i] _))

variable (Sc' : BWWScalars D k)

/-- The relations of `presBWW`, each written as `lhs - rhs`. The relations other than
`quadNe` and `braidEq` do not involve the pure monomials and are those of `pres`. -/
def relationBWW : (r : Rel D) → LinDiagram k (ob D r.ν r.dom) (ob D r.ν r.cod)
  | .quadNe i j ν _ _ => dg D ν (crossL [] i j [] ++ crossL [] j i [])
      (by simp [crossL, Shape.dom, Shape.cod]) - quadSum D Sc'.c i j ν
  | .braidEq i j ν _ =>
      dg D ν (crossL [] i j [up i] ++ crossL [up j] i i [] ++ crossL [] j i [up i])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      dg D ν (crossL [up i] j i [] ++ crossL [] i i [up j] ++ crossL [up i] i j [])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      braidSum D Sc'.c i j ν
  | r => relation D Sc'.toScalars r

/-- The presentation of the Kac–Moody 2-supercategory with Brundan–Wang–Webster
parameters. -/
def presBWW : Presentation.{w, max u v} (sig D) k where
  Rel := Rel D
  dom r := ob D r.ν r.dom
  cod r := ob D r.ν r.cod
  rel := relationBWW D Sc'

/-- All relations of `presBWW` are parity-homogeneous, by (1.2) and the parity condition on
`c`. -/
theorem isParityHomogeneous_presBWW : (presBWW D Sc').IsParityHomogeneous := by
  intro r
  cases r with
  | quadNe i j ν _ _ =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_)⟩
    · rw [parity_sum_append]; simp only [parity_crossL]
      generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
    · by_cases hs : Sc'.c i j p q = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · obtain ⟨hp, hq⟩ := Sc'.toScalars.parity_of_ne_zero (i := i) (j := j) hs
        refine Submodule.smul_mem _ _ (dg_mem D ?_)
        rw [parity_sum_append, parity_dotsL, parity_dotsL, hp, hq, add_zero]
  | braidEq i j ν _ =>
    refine ⟨D.parity i, Submodule.sub_mem _ (Submodule.sub_mem _
      (dg_mem D ?_) (dg_mem D ?_))
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q _ =>
        Submodule.sum_mem _ fun s hs => ?_)⟩
    · simp only [parity_sum_append, parity_crossL]
      generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
    · simp only [parity_sum_append, parity_crossL]
      generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
    · by_cases hz : Sc'.c i j p q = 0
      · rw [hz, mul_zero, zero_smul]; exact Submodule.zero_mem _
      · obtain ⟨hp', hq'⟩ := Sc'.toScalars.parity_of_ne_zero (i := i) (j := j) hz
        refine Submodule.smul_mem _ _ (dg_mem D ?_)
        rw [Finset.mem_range] at hs
        have hc : ((p - 1 - s : ℕ) : ZMod 2) + s + 1 = p := by
          rw [← Nat.cast_add, ← Nat.cast_add_one, show p - 1 - s + s + 1 = p by omega]
        rw [parity_sum_append, parity_sum_append, parity_dotsL, parity_dotsL, parity_dotsL, hq',
          add_zero]
        rw [← hc] at hp'
        generalize D.parity i = a at hp' ⊢
        generalize ((p - 1 - s : ℕ) : ZMod 2) = x at hp' ⊢
        generalize (s : ZMod 2) = y at hp' ⊢
        revert a x y; decide
  | _ => exact isParityHomogeneous D Sc'.toScalars _

variable {D}

theorem quadSum_toBWW (Sc : Scalars D k) {i j : I} (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    quadSum D Sc.toBWW.c i j ν =
      (Sc.t i j : k) • dg D ν (dotsL [] i [up j] (D.dn i j)) (sChain_dotsL [] i [up j] _) +
      (Sc.t j i : k) • dg D ν (dotsL [up i] j [] (D.dn j i)) (sChain_dotsL [up i] j [] _) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • dg D ν (dotsL [up i] j [] q ++ dotsL [] i [up j] p)
          ((sChain_dotsL [up i] j [] q).append (sChain_dotsL [] i [up j] p)) := by
  rw [quadSum, sum_box_toBWW Sc hij hd]
  congr 2
  all_goals try congr 1
  all_goals exact dg_congr D ν _ _ (by simp [dotsL])

theorem braidSum_toBWW (Sc : Scalars D k) {i j : I} (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    braidSum D Sc.toBWW.c i j ν =
      ∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          dg D ν (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] (D.dn i j - 1 - s))
            ((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [] i [up j, up i] _)) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          dg D ν (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
              dotsL [] i [up j, up i] (p - 1 - s))
            (((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [up i] j [up i] q)).append
              (sChain_dotsL [] i [up j, up i] _)) := by
  have hc : ∀ (c : k) (p q : ℕ), ∑ s ∈ Finset.range p,
      (zsign k (D.parity i * (D.parity j + s)) * c) •
        dg (k := k) D ν (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
            dotsL [] i [up j, up i] (p - 1 - s))
          (((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [up i] j [up i] q)).append
            (sChain_dotsL [] i [up j, up i] _)) =
      c • ∑ s ∈ Finset.range p, zsign k (D.parity i * (D.parity j + s)) •
        dg D ν (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
            dotsL [] i [up j, up i] (p - 1 - s))
          (((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [up i] j [up i] q)).append
            (sChain_dotsL [] i [up j, up i] _)) := by
    intro c p q
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm, mul_smul]
  simp only [braidSum, hc]
  rw [sum_box_toBWW Sc hij hd]
  simp only [Finset.range_zero, Finset.sum_empty, smul_zero, add_zero]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_comm (zsign k _), mul_smul]
  congr 2
  exact dg_congr D ν _ _ (by simp [dotsL])

/-- Over Brundan–Ellis parameters the two presentations have the same relations. -/
theorem relationBWW_toBWW (Sc : Scalars D k) (r : Rel D) :
    relationBWW D Sc.toBWW r = relation D Sc r := by
  cases r with
  | quadNe i j ν hij hd =>
    simp only [relationBWW, relation, quadSum_toBWW Sc ν hij hd]
    abel
  | braidEq i j ν hij =>
    by_cases hd : D.d i j = 0
    · have h0 : D.dn i j = 0 := by simp [Datum.dn, hd]
      have h0' : D.dn j i = 0 := by simp [Datum.dn, (D.d_eq_zero_iff i j).mp hd]
      simp [relationBWW, relation, braidSum, h0, h0']
    simp only [relationBWW, relation, braidSum_toBWW Sc ν hij hd]
    abel
  | _ => rfl

/-- **The comparison of presentations.** -/
theorem presBWW_toBWW (Sc : Scalars D k) : presBWW D Sc.toBWW = pres D Sc := by
  unfold presBWW pres
  congr 1
  funext r
  exact relationBWW_toBWW Sc r

/-- Without pure monomials, the presentation with Brundan–Wang–Webster parameters is the
Brundan–Ellis presentation of the underlying parameters. -/
theorem presBWW_eq_pres_of_noPure {P : BWWScalars D k} (hn : P.NoPure) :
    presBWW D P = pres D P.toScalars :=
  calc presBWW D P = presBWW D P.toScalars.toBWW := by rw [hn.toScalars_toBWW]
    _ = pres D P.toScalars := presBWW_toBWW _

end OddMath.SKM
