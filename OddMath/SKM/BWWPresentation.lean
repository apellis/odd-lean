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
* `presBWW_eq_pres`: `presBWW D Sc' = pres D Sc'.toScalars`.
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

variable {D}

end OddMath.SKM
