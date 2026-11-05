/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Basic

/-!
# The Kac–Moody 2-supercategory `𝔘(𝔤)` (Brundan–Ellis, Definition 1.5)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5
(TeX label `def1`), relations (1.7)–(1.14); the inverse entries are named as in Definition 2.2,
(2.6)–(2.9). The TeX pictures are the authoritative reading of the relations.

`pres D S k` is the presentation of `𝔘(𝔤)` on the signature `sig D`
(`OddMath.SKM.Basic`), and `U D S k := (pres D S k).Bicat` is the strict 2-supercategory
(`twoSupercategory`; Brundan–Ellis, *Monoidal supercategories*, Definitions 2.1–2.2). Its objects
are weights, its 1-morphisms words in the `Eᵢ`, `Fᵢ`, and its 2-morphisms linear combinations of
diagrams modulo the relations below and the super interchange law.

## Conventions

Diagrams are lists of layers, read from bottom to top, so no reordering signs arise in the
statement of a relation. Two dots "at the same horizontal level" in the paper denote the
horizontal composite `yx = (yH) ∘ (Gx)` of the paper's (1.1)–(1.3): the dot on the **right** is
applied first (it is the lower layer). All relations are written as `lhs - rhs = 0`; `ν` is the
weight of the rightmost region, and `⟨hᵢ, ν⟩` is `D.h i ν`.

## The relations (all `i, j, k ∈ I`, `ν ∈ X`)

* (1.7) quiver Hecke quadratic relation on `Eᵢ Eⱼ 1_ν`: `τ ≫ τ = 0` (`i = j`), `= tᵢⱼ`
  (`dᵢⱼ = 0`), `= tᵢⱼ x^{dᵢⱼ} ⊗ 1 + tⱼᵢ 1 ⊗ x^{dⱼᵢ} + ∑ sᵢⱼ^{pq} x^p ⊗ x^q` otherwise
  (`quadEq`, `quadZero`, `quadNe`).
* (1.8) dot slides: `(x ⊗ 1) ≫ τ - (-1)^{|i||j|} τ ≫ (1 ⊗ x) = δᵢⱼ` and
  `τ ≫ (x ⊗ 1) - (-1)^{|i||j|} (1 ⊗ x) ≫ τ = δᵢⱼ` (`slideL`, `slideLEq`, `slideR`, `slideREq`).
* (1.9) braid relation on `Eᵢ Eⱼ Eₖ 1_ν`, with the correction terms for `i = k ≠ j`
  (`braid`, `braidEq`).
* (1.10) right adjunction: the two zigzag relations for `η`, `ε` (`zigE`, `zigF`).
* (1.11) `σ : Eⱼ Fᵢ 1_ν → Fᵢ Eⱼ 1_ν` (`sigmaL`) is `η` on the left, then `τ`, then `ε` on the right.
* (1.12) for `i ≠ j`, the leftward crossing is a two-sided inverse of `σ` (`invNe₁`, `invNe₂`;
  (2.7)).
* (1.13) for `⟨hᵢ, ν⟩ ≥ 0`: `(-lcross, ♦-cup₀, …, ♦-cup_{h-1})` is a two-sided inverse of
  `(σ, ε ∘ (xⁿ ⊗ 1))_{0 ≤ n < h} : Eᵢ Fᵢ 1_ν → Fᵢ Eᵢ 1_ν ⊕ 1_ν^{⊕ h}` ((2.8);
  `invP₁`–`invP₅`, the five matrix identities).
* (1.14) for `⟨hᵢ, ν⟩ ≤ 0`: `(-lcross, ♦-cap₀, …, ♦-cap_{-h-1})` is a two-sided inverse of
  `(σ, (1 ⊗ xⁿ) ∘ η)_{0 ≤ n < -h} : Eᵢ Fᵢ 1_ν ⊕ 1_ν^{⊕ -h} → Fᵢ Eᵢ 1_ν` ((2.9);
  `invM₁`–`invM₅`).
* The `♦`-cups with label `n ≥ ⟨hᵢ, ν⟩` and the `♦`-caps with label `n ≥ -⟨hᵢ, ν⟩` vanish
  (`dcupZero`, `dcapZero`): these generators are not part of the paper's presentation.

At `⟨hᵢ, ν⟩ = 0` both (1.13) and (1.14) apply and say the same thing (`lcross = -σ⁻¹`).
Requiring the maps of (1.12)–(1.14) to be invertible is equivalent to adjoining generators for
the entries of their inverses with these relations, since two-sided inverses are unique; this is
how the paper reads the inversion relations ("there are some as yet unnamed generating
2-morphisms in `𝔘(𝔤)` which are the matrix entries of two-sided inverses").

All relations are homogeneous for the parity (`isParityHomogeneous`), using (1.4) and (1.6).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams LinDiagram

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-! ## Notation for letters -/

/-- The letter `Eᵢ`. -/
abbrev up (i : I) : Letter I := (true, i)

/-- The letter `Fᵢ`. -/
abbrev dn (i : I) : Letter I := (false, i)

/-! ## Layer lists of the named 2-morphisms -/

/-- `n` dots on the strand `Eᵢ` between `u` and `v`. -/
def dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) : List (LayerData I) :=
  List.replicate n (u, Shape.dot i, v)

theorem sChain_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    SChain (u ++ [up i] ++ v) (dotsL u i v n) (u ++ [up i] ++ v) :=
  SChain.replicate n u i v

/-- `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` (1.11): the cup `η` on the left, the crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`,
the cap `ε` on the right. -/
def sigmaL (i j : I) : List (LayerData I) :=
  [([], Shape.cup i, [up j, dn i]), ([dn i], Shape.cross i j, [dn i]),
    ([dn i, up j], Shape.cap i, [])]

theorem sChain_sigmaL (i j : I) : SChain [up j, dn i] (sigmaL i j) [dn i, up j] := by
  simp [sigmaL, Shape.dom, Shape.cod]

/-- The leftward crossing `Fᵢ Eⱼ → Eⱼ Fᵢ` as a layer list. -/
def lcrossL (i j : I) : List (LayerData I) := [([], Shape.lcross i j, [])]

theorem sChain_lcrossL (i j : I) : SChain [dn i, up j] (lcrossL i j) [up j, dn i] := by
  simp [lcrossL, Shape.dom, Shape.cod]

/-- `ε ∘ (xⁿ ⊗ 1) : Eᵢ Fᵢ → 1`, the components of (1.13). -/
def epsL (i : I) (n : ℕ) : List (LayerData I) :=
  dotsL [] i [dn i] n ++ [([], Shape.cap i, [])]

theorem sChain_epsL (i : I) (n : ℕ) : SChain [up i, dn i] (epsL i n) [] :=
  (sChain_dotsL [] i [dn i] n).append (by simp [Shape.dom, Shape.cod])

/-- `(1 ⊗ xⁿ) ∘ η : 1 → Fᵢ Eᵢ`, the components of (1.14). -/
def etaL (i : I) (n : ℕ) : List (LayerData I) :=
  [([], Shape.cup i, [])] ++ dotsL [dn i] i [] n

theorem sChain_etaL (i : I) (n : ℕ) : SChain [] (etaL i n) [dn i, up i] :=
  SChain.append (t' := [dn i] ++ [up i] ++ []) (by simp [Shape.dom, Shape.cod])
    (sChain_dotsL [dn i] i [] n)

/-- The `♦`-cup with label `n`. -/
def dcupL (i : I) (n : ℕ) : List (LayerData I) := [([], Shape.dcup i n, [])]

theorem sChain_dcupL (i : I) (n : ℕ) : SChain [] (dcupL i n) [up i, dn i] := by
  simp [dcupL, Shape.dom, Shape.cod]

/-- The `♦`-cap with label `n`. -/
def dcapL (i : I) (n : ℕ) : List (LayerData I) := [([], Shape.dcap i n, [])]

theorem sChain_dcapL (i : I) (n : ℕ) : SChain [dn i, up i] (dcapL i n) [] := by
  simp [dcapL, Shape.dom, Shape.cod]

/-- A single crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` between `u` and `v`. -/
def crossL (u : List (Letter I)) (i j : I) (v : List (Letter I)) : List (LayerData I) :=
  [(u, Shape.cross i j, v)]

/-! ## The relations -/

/-- The sign `(-1)^p` for `p ∈ ℤ/2`. -/
def zsign (k : Type*) [CommRing k] (p : ZMod 2) : k := if p = 1 then -1 else 1

/-- The relations of Definition 1.5 (see the module docstring). `ν` is the rightmost region. -/
inductive Rel (D : Datum I X)
  | quadEq (i : I) (ν : X)
  | quadZero (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j = 0)
  | quadNe (i j : I) (ν : X) (hij : i ≠ j) (hd : D.d i j ≠ 0)
  | slideL (i j : I) (ν : X) (hij : i ≠ j)
  | slideLEq (i : I) (ν : X)
  | slideR (i j : I) (ν : X) (hij : i ≠ j)
  | slideREq (i : I) (ν : X)
  | braid (i j k : I) (ν : X) (h : ¬(i = k ∧ i ≠ j))
  | braidEq (i j : I) (ν : X) (hij : i ≠ j)
  | zigE (i : I) (ν : X)
  | zigF (i : I) (ν : X)
  | invNe₁ (i j : I) (ν : X) (hij : i ≠ j)
  | invNe₂ (i j : I) (ν : X) (hij : i ≠ j)
  | invP₁ (i : I) (ν : X) (hh : 0 ≤ D.h i ν)
  | invP₂ (i : I) (ν : X) (hh : 0 ≤ D.h i ν)
  | invP₃ (i : I) (ν : X) (m : ℕ) (hm : (m : ℤ) < D.h i ν)
  | invP₄ (i : I) (ν : X) (n : ℕ) (hn : (n : ℤ) < D.h i ν)
  | invP₅ (i : I) (ν : X) (m n : ℕ) (hm : (m : ℤ) < D.h i ν) (hn : (n : ℤ) < D.h i ν)
  | invM₁ (i : I) (ν : X) (hh : D.h i ν ≤ 0)
  | invM₂ (i : I) (ν : X) (hh : D.h i ν ≤ 0)
  | invM₃ (i : I) (ν : X) (m : ℕ) (hm : (m : ℤ) < -D.h i ν)
  | invM₄ (i : I) (ν : X) (n : ℕ) (hn : (n : ℤ) < -D.h i ν)
  | invM₅ (i : I) (ν : X) (m n : ℕ) (hm : (m : ℤ) < -D.h i ν) (hn : (n : ℤ) < -D.h i ν)
  | dcupZero (i : I) (ν : X) (n : ℕ) (hn : D.h i ν ≤ n)
  | dcapZero (i : I) (ν : X) (n : ℕ) (hn : -D.h i ν ≤ n)

namespace Rel

variable {D}

/-- The rightmost region of a relation. -/
@[simp]
def ν : Rel D → X
  | quadEq _ ν | quadZero _ _ ν _ _ | quadNe _ _ ν _ _ | slideL _ _ ν _ | slideLEq _ ν
  | slideR _ _ ν _ | slideREq _ ν | braid _ _ _ ν _ | braidEq _ _ ν _ | zigE _ ν | zigF _ ν
  | invNe₁ _ _ ν _ | invNe₂ _ _ ν _ | invP₁ _ ν _ | invP₂ _ ν _ | invP₃ _ ν _ _ | invP₄ _ ν _ _
  | invP₅ _ ν _ _ _ _ | invM₁ _ ν _ | invM₂ _ ν _ | invM₃ _ ν _ _ | invM₄ _ ν _ _
  | invM₅ _ ν _ _ _ _ | dcupZero _ ν _ _ | dcapZero _ ν _ _ => ν

/-- The bottom boundary word of a relation. -/
@[simp]
def dom : Rel D → List (Letter I)
  | quadEq i _ => [up i, up i]
  | quadZero i j _ _ _ | quadNe i j _ _ _ | slideL i j _ _ | slideR i j _ _ => [up i, up j]
  | slideLEq i _ | slideREq i _ => [up i, up i]
  | braid i j k _ _ => [up i, up j, up k]
  | braidEq i j _ _ => [up i, up j, up i]
  | zigE i _ => [up i]
  | zigF i _ => [dn i]
  | invNe₁ i j _ _ => [up j, dn i]
  | invNe₂ i j _ _ => [dn i, up j]
  | invP₁ i _ _ | invM₂ i _ _ | invM₄ i _ _ _ => [up i, dn i]
  | invP₂ i _ _ | invP₃ i _ _ _ | invM₁ i _ _ => [dn i, up i]
  | invP₄ _ _ _ _ | invP₅ _ _ _ _ _ _ | invM₃ _ _ _ _ | invM₅ _ _ _ _ _ _ | dcupZero _ _ _ _ => []
  | dcapZero i _ _ _ => [dn i, up i]

/-- The top boundary word of a relation. -/
@[simp]
def cod : Rel D → List (Letter I)
  | quadEq i _ => [up i, up i]
  | quadZero i j _ _ _ | quadNe i j _ _ _ => [up i, up j]
  | slideL i j _ _ | slideR i j _ _ => [up j, up i]
  | slideLEq i _ | slideREq i _ => [up i, up i]
  | braid i j k _ _ => [up k, up j, up i]
  | braidEq i j _ _ => [up i, up j, up i]
  | zigE i _ => [up i]
  | zigF i _ => [dn i]
  | invNe₁ i j _ _ => [up j, dn i]
  | invNe₂ i j _ _ => [dn i, up j]
  | invP₁ i _ _ | invM₂ i _ _ | invM₃ i _ _ _ | dcupZero i _ _ _ => [up i, dn i]
  | invP₂ i _ _ | invP₄ i _ _ _ | invM₁ i _ _ => [dn i, up i]
  | invP₃ _ _ _ _ | invP₅ _ _ _ _ _ _ | invM₄ _ _ _ _ | invM₅ _ _ _ _ _ _ | dcapZero _ _ _ _ => []

end Rel

variable {k : Type w} [CommRing k] (Sc : Scalars D k)

/-- Shorthand: the class of the normal-form diagram with layers `ls` as a linear combination. -/
abbrev dg (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I)) (h : SChain t ls t') :
    LinDiagram k (ob D μ t) (ob D μ t') :=
  of (mkD D μ ls h)

/-- The identity of `ob D μ t` as a linear combination. -/
abbrev idg (μ : X) (t : List (Letter I)) : LinDiagram k (ob D μ t) (ob D μ t) := of (𝟙 _)

/-- The relations of Definition 1.5, each written as `lhs - rhs`. -/
def relation : (r : Rel D) → LinDiagram k (ob D r.ν r.dom) (ob D r.ν r.cod)
  | .quadEq i ν => dg D ν (crossL [] i i [] ++ crossL [] i i [])
      (by simp [crossL, Shape.dom, Shape.cod])
  | .quadZero i j ν _ _ => dg D ν (crossL [] i j [] ++ crossL [] j i [])
      (by simp [crossL, Shape.dom, Shape.cod]) - (Sc.t i j : k) • idg D ν _
  | .quadNe i j ν _ _ => dg D ν (crossL [] i j [] ++ crossL [] j i [])
      (by simp [crossL, Shape.dom, Shape.cod]) -
      (Sc.t i j : k) • dg D ν (dotsL [] i [up j] (D.dn i j)) (sChain_dotsL [] i [up j] _) -
      (Sc.t j i : k) • dg D ν (dotsL [up i] j [] (D.dn j i)) (sChain_dotsL [up i] j [] _) -
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • dg D ν (dotsL [up i] j [] q ++ dotsL [] i [up j] p)
          ((sChain_dotsL [up i] j [] q).append (sChain_dotsL [] i [up j] p))
  | .slideL i j ν _ => dg D ν (dotsL [] i [up j] 1 ++ crossL [] i j [])
        ((sChain_dotsL [] i [up j] 1).append (by simp [crossL, Shape.dom, Shape.cod])) -
      zsign k (D.parity i * D.parity j) • dg D ν (crossL [] i j [] ++ dotsL [up j] i [] 1)
        (SChain.append (t' := [up j] ++ [up i] ++ []) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [up j] i [] 1))
  | .slideLEq i ν => dg D ν (dotsL [] i [up i] 1 ++ crossL [] i i [])
        ((sChain_dotsL [] i [up i] 1).append (by simp [crossL, Shape.dom, Shape.cod])) -
      zsign k (D.parity i * D.parity i) • dg D ν (crossL [] i i [] ++ dotsL [up i] i [] 1)
        (SChain.append (t' := [up i] ++ [up i] ++ []) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [up i] i [] 1)) - idg D ν _
  | .slideR i j ν _ => dg D ν (crossL [] i j [] ++ dotsL [] j [up i] 1)
        (SChain.append (t' := [] ++ [up j] ++ [up i]) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [] j [up i] 1)) -
      zsign k (D.parity i * D.parity j) • dg D ν (dotsL [up i] j [] 1 ++ crossL [] i j [])
        ((sChain_dotsL [up i] j [] 1).append (by simp [crossL, Shape.dom, Shape.cod]))
  | .slideREq i ν => dg D ν (crossL [] i i [] ++ dotsL [] i [up i] 1)
        (SChain.append (t' := [] ++ [up i] ++ [up i]) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [] i [up i] 1)) -
      zsign k (D.parity i * D.parity i) • dg D ν (dotsL [up i] i [] 1 ++ crossL [] i i [])
        ((sChain_dotsL [up i] i [] 1).append (by simp [crossL, Shape.dom, Shape.cod])) -
      idg D ν _
  | .braid i j k' ν _ =>
      dg D ν (crossL [] i j [up k'] ++ crossL [up j] i k' [] ++ crossL [] j k' [up i])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      dg D ν (crossL [up i] j k' [] ++ crossL [] i k' [up j] ++ crossL [up k'] i j [])
        (by simp [crossL, Shape.dom, Shape.cod])
  | .braidEq i j ν _ =>
      dg D ν (crossL [] i j [up i] ++ crossL [up j] i i [] ++ crossL [] j i [up i])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      dg D ν (crossL [up i] j i [] ++ crossL [] i i [up j] ++ crossL [up i] i j [])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      ∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          dg D ν (dotsL [up i, up j] i [] s ++ dotsL [] i [up j, up i] (D.dn i j - 1 - s))
            ((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [] i [up j, up i] _)) -
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          dg D ν (dotsL [up i, up j] i [] s ++ dotsL [up i] j [up i] q ++
              dotsL [] i [up j, up i] (p - 1 - s))
            (((sChain_dotsL [up i, up j] i [] s).append (sChain_dotsL [up i] j [up i] q)).append
              (sChain_dotsL [] i [up j, up i] _))
  | .zigE i ν => dg D ν [([up i], Shape.cup i, []), ([], Shape.cap i, [up i])]
      (by simp [Shape.dom, Shape.cod]) - idg D ν _
  | .zigF i ν => dg D ν [([], Shape.cup i, [dn i]), ([dn i], Shape.cap i, [])]
      (by simp [Shape.dom, Shape.cod]) - idg D ν _
  | .invNe₁ i j ν _ => dg D ν (sigmaL i j ++ lcrossL i j)
      ((sChain_sigmaL i j).append (sChain_lcrossL i j)) - idg D ν _
  | .invNe₂ i j ν _ => dg D ν (lcrossL i j ++ sigmaL i j)
      ((sChain_lcrossL i j).append (sChain_sigmaL i j)) - idg D ν _
  | .invP₁ i ν _ => -dg D ν (sigmaL i i ++ lcrossL i i)
        ((sChain_sigmaL i i).append (sChain_lcrossL i i)) +
      ∑ n ∈ Finset.range (D.h i ν).toNat,
        dg D ν (epsL i n ++ dcupL i n) ((sChain_epsL i n).append (sChain_dcupL i n)) -
      idg D ν _
  | .invP₂ i ν _ => dg D ν (lcrossL i i ++ sigmaL i i)
      ((sChain_lcrossL i i).append (sChain_sigmaL i i)) + idg D ν _
  | .invP₃ i ν m _ => dg D ν (lcrossL i i ++ epsL i m)
      ((sChain_lcrossL i i).append (sChain_epsL i m))
  | .invP₄ i ν n _ => dg D ν (dcupL i n ++ sigmaL i i)
      ((sChain_dcupL i n).append (sChain_sigmaL i i))
  | .invP₅ i ν m n _ _ => dg D ν (dcupL i n ++ epsL i m)
      ((sChain_dcupL i n).append (sChain_epsL i m)) - if m = n then idg D ν _ else 0
  | .invM₁ i ν _ => -dg D ν (lcrossL i i ++ sigmaL i i)
        ((sChain_lcrossL i i).append (sChain_sigmaL i i)) +
      ∑ n ∈ Finset.range (-D.h i ν).toNat,
        dg D ν (dcapL i n ++ etaL i n) ((sChain_dcapL i n).append (sChain_etaL i n)) -
      idg D ν _
  | .invM₂ i ν _ => dg D ν (sigmaL i i ++ lcrossL i i)
      ((sChain_sigmaL i i).append (sChain_lcrossL i i)) + idg D ν _
  | .invM₃ i ν m _ => dg D ν (etaL i m ++ lcrossL i i)
      ((sChain_etaL i m).append (sChain_lcrossL i i))
  | .invM₄ i ν n _ => dg D ν (sigmaL i i ++ dcapL i n)
      ((sChain_sigmaL i i).append (sChain_dcapL i n))
  | .invM₅ i ν m n _ _ => dg D ν (etaL i m ++ dcapL i n)
      ((sChain_etaL i m).append (sChain_dcapL i n)) - if m = n then idg D ν _ else 0
  | .dcupZero i ν n _ => dg D ν (dcupL i n) (sChain_dcupL i n)
  | .dcapZero i ν n _ => dg D ν (dcapL i n) (sChain_dcapL i n)

/-- The presentation of the Kac–Moody 2-supercategory `𝔘(𝔤)` (Definition 1.5). -/
def pres : Presentation.{w, max u v} (sig D) k where
  Rel := Rel D
  dom r := ob D r.ν r.dom
  cod r := ob D r.ν r.cod
  rel := relation D Sc

/-! ## Parity homogeneity -/

theorem zmod2_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  fin_cases a
  · rfl
  · exact absurd rfl h

theorem parity_mul_dn (i j : I) : D.parity i * (D.dn i j : ZMod 2) = 0 := by
  by_cases hi : D.parity i = 1
  · obtain ⟨m, hm⟩ := D.even_d_of_odd hi j
    have : (D.dn i j : ZMod 2) = 0 := by
      unfold Datum.dn
      rw [hm]
      rcases le_or_gt 0 m with h | h
      · rw [show m + m = ((m.toNat + m.toNat : ℕ) : ℤ) by omega, Int.toNat_natCast]
        push_cast
        rw [← two_mul]; exact mul_eq_zero_of_left (by decide) _
      · rw [show (m + m).toNat = 0 by omega]; rfl
    rw [this, mul_zero]
  · rw [zmod2_eq_zero_of_ne_one hi, zero_mul]

variable {D} in
theorem Scalars.parity_of_ne_zero {i j : I} {p q : ℕ} (hs : Sc.s i j p q ≠ 0) :
    (p : ZMod 2) * D.parity i = 0 ∧ (q : ZMod 2) * D.parity j = 0 :=
  ⟨zmod2_eq_zero_of_ne_one fun h => hs (Sc.s_eq_zero i j p q h),
    zmod2_eq_zero_of_ne_one fun h => hs (by rw [Sc.s_symm]; exact Sc.s_eq_zero j i q p h)⟩

/-- A normal-form diagram whose generators have parities summing to `d` has parity `d`. -/
theorem dg_mem {μ : X} {t t' : List (Letter I)} {ls : List (LayerData I)} {h : SChain t ls t'}
    {d : ZMod 2} (hd : (ls.map fun x => x.2.1.parity D).sum = d) :
    dg (k := k) D μ ls h ∈
      LinDiagram.homDeg k (Presentation.parityDeg (sig D)) (ob D μ t) (ob D μ t') d :=
  of_mem_homDeg' (by rw [degree_parity_mkD]; exact hd)

theorem idg_mem (μ : X) (t : List (Letter I)) :
    idg (k := k) D μ t ∈
      LinDiagram.homDeg k (Presentation.parityDeg (sig D)) (ob D μ t) (ob D μ t) 0 :=
  of_mem_homDeg' (Diagram.degree_id _ _)

/-- The parities of the layer lists used in the relations. -/
theorem parity_sum_append (ls ms : List (LayerData I)) :
    ((ls ++ ms).map fun x => x.2.1.parity D).sum =
      (ls.map fun x => x.2.1.parity D).sum + (ms.map fun x => x.2.1.parity D).sum := by
  simp

@[simp] theorem parity_dotsL (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    ((dotsL u i v n).map fun x => x.2.1.parity D).sum = (n : ZMod 2) * D.parity i := by
  simp [dotsL, Shape.parity, List.sum_replicate, nsmul_eq_mul]

@[simp] theorem parity_crossL (u : List (Letter I)) (i j : I) (v : List (Letter I)) :
    ((crossL u i j v).map fun x => x.2.1.parity D).sum = D.parity i * D.parity j := by
  simp [crossL, Shape.parity]

@[simp] theorem parity_sigmaL (i j : I) :
    ((sigmaL i j).map fun x => x.2.1.parity D).sum = D.parity i * D.parity j := by
  simp [sigmaL, Shape.parity]

@[simp] theorem parity_lcrossL (i j : I) :
    ((lcrossL i j).map fun x => x.2.1.parity D).sum = D.parity i * D.parity j := by
  simp [lcrossL, Shape.parity]

@[simp] theorem parity_epsL (i : I) (n : ℕ) :
    ((epsL i n).map fun x => x.2.1.parity D).sum = (n : ZMod 2) * D.parity i := by
  rw [epsL, parity_sum_append, parity_dotsL]; simp [Shape.parity]

@[simp] theorem parity_etaL (i : I) (n : ℕ) :
    ((etaL i n).map fun x => x.2.1.parity D).sum = (n : ZMod 2) * D.parity i := by
  rw [etaL, parity_sum_append, parity_dotsL]; simp [Shape.parity]

@[simp] theorem parity_dcupL (i : I) (n : ℕ) :
    ((dcupL i n).map fun x => x.2.1.parity D).sum = D.parity i * n := by
  simp [dcupL, Shape.parity]

@[simp] theorem parity_dcapL (i : I) (n : ℕ) :
    ((dcapL i n).map fun x => x.2.1.parity D).sum = D.parity i * n := by
  simp [dcapL, Shape.parity]

/-- All relations of Definition 1.5 are homogeneous for the parity, by (1.4) and (1.6). -/
theorem isParityHomogeneous : (pres D Sc).IsParityHomogeneous := by
  intro r
  cases r with
  | quadEq i ν =>
    refine ⟨0, dg_mem D ?_⟩
    rw [parity_sum_append]; simp only [parity_crossL]
    generalize D.parity i = a; revert a; decide
  | quadZero i j ν _ _ =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem D ?_) (Submodule.smul_mem _ _ (idg_mem D _ _))⟩
    rw [parity_sum_append]; simp only [parity_crossL]
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | quadNe i j ν _ _ =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))) (Submodule.smul_mem _ _ (dg_mem D ?_)))
      (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_)⟩
    · rw [parity_sum_append]; simp only [parity_crossL]
      generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
    · rw [parity_dotsL, mul_comm]; exact parity_mul_dn D i j
    · rw [parity_dotsL, mul_comm]; exact parity_mul_dn D j i
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · obtain ⟨hp, hq⟩ := Sc.parity_of_ne_zero hs
        refine Submodule.smul_mem _ _ (dg_mem D ?_)
        rw [parity_sum_append, parity_dotsL, parity_dotsL, hp, hq, add_zero]
  | slideL i j ν _ =>
    refine ⟨D.parity i + D.parity i * D.parity j, Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | slideLEq i ν =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))) (idg_mem D _ _)⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; revert a; decide
  | slideR i j ν _ =>
    refine ⟨D.parity j + D.parity i * D.parity j, Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | slideREq i ν =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))) (idg_mem D _ _)⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; revert a; decide
  | braid i j k' ν _ =>
    refine ⟨D.parity i * D.parity j + D.parity i * D.parity k' + D.parity j * D.parity k',
      Submodule.sub_mem _ (dg_mem D ?_) (dg_mem D ?_)⟩
    all_goals simp only [parity_sum_append, parity_crossL]
    all_goals generalize D.parity i = a; generalize D.parity j = b; generalize D.parity k' = c
    all_goals revert a b c; decide
  | braidEq i j ν _ =>
    refine ⟨D.parity i, Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
      (dg_mem D ?_) (dg_mem D ?_)) (Submodule.sum_mem _ fun s hs => ?_))
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q _ =>
        Submodule.sum_mem _ fun s hs => ?_)⟩
    · simp only [parity_sum_append, parity_crossL]
      generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
    · simp only [parity_sum_append, parity_crossL]
      generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
    · refine Submodule.smul_mem _ _ (dg_mem D ?_)
      rw [Finset.mem_range] at hs
      have hd := parity_mul_dn D i j
      have hc : ((D.dn i j - 1 - s : ℕ) : ZMod 2) + s + 1 = D.dn i j := by
        rw [← Nat.cast_add, ← Nat.cast_add_one, show D.dn i j - 1 - s + s + 1 = D.dn i j by omega]
      rw [parity_sum_append, parity_dotsL, parity_dotsL]
      rw [← hc] at hd
      generalize D.parity i = a at hd ⊢
      generalize ((D.dn i j - 1 - s : ℕ) : ZMod 2) = x at hd ⊢
      generalize (s : ZMod 2) = y at hd ⊢
      revert a x y; decide
    · by_cases hz : Sc.s i j p q = 0
      · rw [hz, mul_zero, zero_smul]; exact Submodule.zero_mem _
      · obtain ⟨hp', hq'⟩ := Sc.parity_of_ne_zero hz
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
  | zigE i ν =>
    exact ⟨0, Submodule.sub_mem _ (dg_mem D (by simp [Shape.parity])) (idg_mem D _ _)⟩
  | zigF i ν =>
    exact ⟨0, Submodule.sub_mem _ (dg_mem D (by simp [Shape.parity])) (idg_mem D _ _)⟩
  | invNe₁ i j ν _ =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem D ?_) (idg_mem D _ _)⟩
    rw [parity_sum_append, parity_sigmaL, parity_lcrossL]
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | invNe₂ i j ν _ =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem D ?_) (idg_mem D _ _)⟩
    rw [parity_sum_append, parity_sigmaL, parity_lcrossL]
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | invP₁ i ν _ =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (dg_mem D ?_))
      (Submodule.sum_mem _ fun n _ => dg_mem D ?_)) (idg_mem D _ _)⟩
    · rw [parity_sum_append, parity_sigmaL, parity_lcrossL]
      generalize D.parity i = a; revert a; decide
    · rw [parity_sum_append, parity_epsL, parity_dcupL]
      generalize D.parity i = a; generalize (n : ZMod 2) = b; revert a b; decide
  | invP₂ i ν _ =>
    refine ⟨0, Submodule.add_mem _ (dg_mem D ?_) (idg_mem D _ _)⟩
    rw [parity_sum_append, parity_sigmaL, parity_lcrossL]
    generalize D.parity i = a; revert a; decide
  | invP₃ i ν m _ => exact ⟨_, dg_mem D rfl⟩
  | invP₄ i ν n _ => exact ⟨_, dg_mem D rfl⟩
  | invP₅ i ν m n _ _ =>
    refine ⟨D.parity i * n + (m : ZMod 2) * D.parity i, Submodule.sub_mem _ (dg_mem D ?_) ?_⟩
    · rw [parity_sum_append, parity_epsL, parity_dcupL]
    · split_ifs with hmn
      · subst hmn
        have : D.parity i * m + (m : ZMod 2) * D.parity i = 0 := by
          generalize D.parity i = a; generalize (m : ZMod 2) = b; revert a b; decide
        rw [this]; exact idg_mem D _ _
      · exact Submodule.zero_mem _
  | invM₁ i ν _ =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _ (dg_mem D ?_))
      (Submodule.sum_mem _ fun n _ => dg_mem D ?_)) (idg_mem D _ _)⟩
    · rw [parity_sum_append, parity_sigmaL, parity_lcrossL]
      generalize D.parity i = a; revert a; decide
    · rw [parity_sum_append, parity_etaL, parity_dcapL]
      generalize D.parity i = a; generalize (n : ZMod 2) = b; revert a b; decide
  | invM₂ i ν _ =>
    refine ⟨0, Submodule.add_mem _ (dg_mem D ?_) (idg_mem D _ _)⟩
    rw [parity_sum_append, parity_sigmaL, parity_lcrossL]
    generalize D.parity i = a; revert a; decide
  | invM₃ i ν m _ => exact ⟨_, dg_mem D rfl⟩
  | invM₄ i ν n _ => exact ⟨_, dg_mem D rfl⟩
  | invM₅ i ν m n _ _ =>
    refine ⟨(m : ZMod 2) * D.parity i + D.parity i * n, Submodule.sub_mem _ (dg_mem D ?_) ?_⟩
    · rw [parity_sum_append, parity_etaL, parity_dcapL]
    · split_ifs with hmn
      · subst hmn
        have : (m : ZMod 2) * D.parity i + D.parity i * m = 0 := by
          generalize D.parity i = a; generalize (m : ZMod 2) = b; revert a b; decide
        rw [this]; exact idg_mem D _ _
      · exact Submodule.zero_mem _
  | dcupZero i ν n _ => exact ⟨_, dg_mem D rfl⟩
  | dcapZero i ν n _ => exact ⟨_, dg_mem D rfl⟩

/-- **The Kac–Moody 2-supercategory `𝔘(𝔤)`** (Brundan–Ellis, Definition 1.5): the presented
bicategory of `pres D Sc`, a strict 2-supercategory (`twoSupercategory`). -/
abbrev U : Type _ := (pres D Sc).Bicat

/-- The hom categories of `𝔘(𝔤)` are supercategories: the parity of a diagram is the number of
its odd generators modulo `2`. -/
abbrev homSupercategory (l m : U D Sc) : Supercategory k (l ⟶ m) :=
  Presentation.Bicat.supercategory (isParityHomogeneous D Sc) l m

/-- `𝔘(𝔤)` is a 2-supercategory (Brundan–Ellis, Definition 1.5 with Definition 1.3; strict by
`Presentation.Bicat.instStrict`). -/
theorem twoSupercategory :
    letI := homSupercategory D Sc
    TwoSupercategory k (U D Sc) :=
  Presentation.twoSupercategory (isParityHomogeneous D Sc)

end OddMath.SKM
