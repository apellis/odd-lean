/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LieLean.RepresentationTheory.Crystal.Basic
import StringDiagrams.Super.Presented

/-!
# Super Kac–Moody data and the signature of `𝔘(𝔤)`

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, the data fixed
before Definition 1.5 and the generators of Definition 1.5 (TeX label `def1`), together with the
"as yet unnamed" generating 2-morphisms of Definition 1.5 that are the matrix entries of the
inverses of (1.12)–(1.14); Definition 2.2 names them (2.6).

## The data

* `Datum I X`: an index set `I` with a parity `I → ℤ/2`, a weight lattice `X` (any additive
  commutative group) with simple roots `αᵢ ∈ X` and simple coroots `⟨hᵢ, -⟩ : X → ℤ`
  (lie-lean's `CartanDatum I X`), such that `aᵢⱼ = ⟨hᵢ, αⱼ⟩` is a generalized Cartan matrix and
  `dᵢⱼ := -aᵢⱼ` is even whenever `i` is odd (assumption (1.4)).
  The paper takes a complex vector space `𝔥` with linearly independent `αᵢ ∈ 𝔥*`, `hᵢ ∈ 𝔥` and
  the weight lattice `P = {λ ∈ 𝔥* | ⟨hᵢ, λ⟩ ∈ ℤ}`; that is a special case (`X = P`). Nothing in
  Definition 1.5 uses linear independence.
* `Scalars D k`: the units `tᵢⱼ` with (1.5) and the scalars `sᵢⱼ^{pq}` with (1.6), over a
  commutative ring `k`, with `2` invertible if some `i` is odd. The paper allows a
  supercommutative ground ring `k = k₀ ⊕ k₁`; we work with `k` concentrated in even parity, the
  case of main interest in the paper (all scalars lie in `k₀` anyway).

## The signature

Regions are weights `λ ∈ X`. A strand colour is a signed letter `(ε, i)` (`(true, i)` for
`Eᵢ`, oriented up; `(false, i)` for `Fᵢ`, oriented down) together with the weight of the region
to its **right**. Words are read from left to right (as in the paper's pictures): the word
`[(true, j), (false, i)]` with rightmost region `λ` is the 1-morphism `Eⱼ Fᵢ 1_λ`. Diagrams are
read from bottom to top, and `f ≫ g` is `f` below `g`.

A generator is a shape (`Shape`) together with the weight of its rightmost region:

| shape         | 2-morphism (rightmost region `λ`)            | parity     | paper                     |
|---------------|-----------------------------------------------|------------|---------------------------|
| `dot i`       | `x : Eᵢ 1_λ → Eᵢ 1_λ`                         | `\|i\|`     | (1.7), upward dot          |
| `cross i j`   | `τ : Eᵢ Eⱼ 1_λ → Eⱼ Eᵢ 1_λ`                   | `\|i\|\|j\|` | (1.7), upward crossing     |
| `cup i`       | `η : 1_λ → Fᵢ Eᵢ 1_λ`                         | `0`        | (1.7), rightward cup       |
| `cap i`       | `ε : Eᵢ Fᵢ 1_λ → 1_λ`                         | `0`        | (1.7), rightward cap       |
| `lcross i j`  | leftward crossing `Fᵢ Eⱼ 1_λ → Eⱼ Fᵢ 1_λ`     | `\|i\|\|j\|` | (2.6)                      |
| `dcup i n`    | `♦`-cup with label `n`: `1_λ → Eᵢ Fᵢ 1_λ`     | `\|i\|n`    | (2.6)                      |
| `dcap i n`    | `♦`-cap with label `n`: `Fᵢ Eᵢ 1_λ → 1_λ`     | `\|i\|n`    | (2.6)                      |

The last three are the matrix entries of the two-sided inverses of (1.12)–(1.14) (with the sign
of (2.8), (2.9) on the leftward crossing when `i = j`); the relations making them inverses are in
`OddMath.SKM.Presentation`. The `♦`-cups (resp. caps) are only meaningful for
`0 ≤ n < ⟨hᵢ, λ⟩` (resp. `0 ≤ n < -⟨hᵢ, λ⟩`); the generators with other labels are set to zero
by relations.

## Normal forms

All regions of a diagram are determined by the signed letters of its boundary words and by the
weight `μ` of its rightmost region. `ob μ t` is the object of the signed sequence `t` with
rightmost region `μ`; `lay μ u g v` is the layer with a generator of shape `g` between the
strands `u` and `v`; `mkD μ ls h` is the diagram with layers `ls`.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams

universe u v

/-! ## The data -/

/-- Super Kac–Moody data (Brundan–Ellis, §1, before Definition 1.5): a Cartan datum in
lie-lean's sense (weights `X`, simple roots `αᵢ`, simple coroots `⟨hᵢ, -⟩`) whose Cartan matrix
`aᵢⱼ = ⟨hᵢ, αⱼ⟩` is a generalized Cartan matrix, and a parity on `I` such that `dᵢⱼ = -aᵢⱼ` is
even when `i` is odd (1.4). -/
structure Datum (I : Type u) (X : Type v) [AddCommGroup X] where
  /-- Simple roots and coroots. -/
  cd : CartanDatum I X
  /-- `aᵢⱼ = ⟨hᵢ, αⱼ⟩` is a generalized Cartan matrix. -/
  isGCM : cd.cartanMatrix.IsGeneralizedCartan
  /-- The parity `i ↦ |i|`. -/
  parity : I → ZMod 2
  /-- Assumption (1.4): `|i| = 1 → dᵢⱼ` is even. -/
  even_of_odd : ∀ i j, parity i = 1 → Even (cd.coroot i (cd.root j))

namespace Datum

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- The simple root `αᵢ`. -/
abbrev α (i : I) : X := D.cd.root i

/-- `⟨hᵢ, λ⟩`. -/
abbrev h (i : I) (μ : X) : ℤ := D.cd.coroot i μ

/-- `dᵢⱼ = -⟨hᵢ, αⱼ⟩`, so that `(-dᵢⱼ)` is the Cartan matrix. -/
def d (i j : I) : ℤ := -D.h i (D.α j)

theorem d_self (i : I) : D.d i i = -2 := by
  simp [d, D.cd.coroot_root_self]

theorem d_nonneg {i j : I} (hij : i ≠ j) : 0 ≤ D.d i j := by
  have := D.isGCM.offDiag_nonpos i j hij
  simp only [CartanDatum.cartanMatrix_apply] at this
  simp only [d, h, α]; omega

theorem d_eq_zero_iff (i j : I) : D.d i j = 0 ↔ D.d j i = 0 := by
  have := D.isGCM.zero_comm i j
  simp only [CartanDatum.cartanMatrix_apply] at this
  simp only [d, h, α, neg_eq_zero]; exact this

theorem even_d_of_odd {i : I} (hi : D.parity i = 1) (j : I) : Even (D.d i j) := by
  simpa [d] using (D.even_of_odd i j hi).neg

/-- The number of dots `dᵢⱼ` as a natural number (equal to `dᵢⱼ` for `i ≠ j`). -/
def dn (i j : I) : ℕ := (D.d i j).toNat

theorem dn_cast {i j : I} (hij : i ≠ j) : (D.dn i j : ℤ) = D.d i j :=
  Int.toNat_of_nonneg (D.d_nonneg hij)

end Datum

/-- The scalars of Brundan–Ellis §1: units `tᵢⱼ ∈ k^×` with `tᵢᵢ = 1` and `tᵢⱼ = tⱼᵢ` when
`dᵢⱼ = 0` (1.5), and scalars `sᵢⱼ^{pq} ∈ k` (used for `0 < p < dᵢⱼ`, `0 < q < dⱼᵢ`) with
`sᵢⱼ^{pq} = sⱼᵢ^{qp}` and `sᵢⱼ^{pq} = 0` if `p|i|` is odd (1.6). If some `i` is odd, `2` is
invertible in `k`. -/
structure Scalars {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
    (k : Type*) [CommRing k] where
  /-- The units `tᵢⱼ`. -/
  t : I → I → kˣ
  t_self : ∀ i, t i i = 1
  t_symm_of_d_eq_zero : ∀ i j, D.d i j = 0 → t i j = t j i
  /-- The scalars `sᵢⱼ^{pq}`. -/
  s : I → I → ℕ → ℕ → k
  s_symm : ∀ i j p q, s i j p q = s j i q p
  s_eq_zero : ∀ (i j : I) (p q : ℕ), (p : ZMod 2) * D.parity i = 1 → s i j p q = 0
  /-- `2` is invertible if some element of `I` is odd. -/
  two_isUnit : (∃ i, D.parity i = 1) → IsUnit (2 : k)

/-! ## Signed letters and weights -/

/-- A signed letter: `(true, i)` stands for `Eᵢ` and `(false, i)` for `Fᵢ`. -/
abbrev Letter (I : Type u) : Type u := Bool × I

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- The weight `±αᵢ` of the signed letter `(±, i)`. -/
def sh (l : Letter I) : X := if l.1 then D.α l.2 else -D.α l.2

/-- The weight `μ + wt(t)` of the region to the left of the signed sequence `t`, whose
rightmost region is `μ`. -/
def wt (μ : X) : List (Letter I) → X
  | [] => μ
  | l :: t => sh D l + wt μ t

@[simp] theorem wt_nil (μ : X) : wt D μ [] = μ := rfl

@[simp] theorem wt_cons (μ : X) (l : Letter I) (t : List (Letter I)) :
    wt D μ (l :: t) = sh D l + wt D μ t := rfl

theorem wt_append (μ : X) (a b : List (Letter I)) : wt D μ (a ++ b) = wt D (wt D μ b) a := by
  induction a with
  | nil => rfl
  | cons l a ih => simp [ih]

/-- A strand colour: a signed letter and the weight of the region to its right. -/
@[ext]
structure Col (I : Type u) (X : Type v) where
  /-- The signed letter. -/
  l : Letter I
  /-- The weight of the region to the right of the strand. -/
  r : X

/-- The colours of the signed sequence `t` with rightmost region `μ`. -/
def wd (μ : X) : List (Letter I) → List (Col I X)
  | [] => []
  | l :: t => ⟨l, wt D μ t⟩ :: wd μ t

@[simp] theorem wd_nil (μ : X) : wd D μ [] = [] := rfl

@[simp] theorem wd_cons (μ : X) (l : Letter I) (t : List (Letter I)) :
    wd D μ (l :: t) = ⟨l, wt D μ t⟩ :: wd D μ t := rfl

theorem wd_append (μ : X) (a b : List (Letter I)) :
    wd D μ (a ++ b) = wd D (wt D μ b) a ++ wd D μ b := by
  induction a with
  | nil => rfl
  | cons l a ih => simp [ih, wt_append]

/-! ## Shapes of generators -/

/-- The shape of a generator (see the table in the module docstring). -/
inductive Shape (I : Type u)
  /-- The upward dot `x` on `Eᵢ`. -/
  | dot (i : I)
  /-- The upward crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ`. -/
  | cross (i j : I)
  /-- The rightward cup `η : 1 → Fᵢ Eᵢ`. -/
  | cup (i : I)
  /-- The rightward cap `ε : Eᵢ Fᵢ → 1`. -/
  | cap (i : I)
  /-- The leftward crossing `Fᵢ Eⱼ → Eⱼ Fᵢ` (2.6). -/
  | lcross (i j : I)
  /-- The `♦`-cup with label `n`, `1 → Eᵢ Fᵢ` (2.6). -/
  | dcup (i : I) (n : ℕ)
  /-- The `♦`-cap with label `n`, `Fᵢ Eᵢ → 1` (2.6). -/
  | dcap (i : I) (n : ℕ)

namespace Shape

/-- Bottom boundary of a shape. -/
def dom : Shape I → List (Letter I)
  | dot i => [(true, i)]
  | cross i j => [(true, i), (true, j)]
  | cup _ => []
  | cap i => [(true, i), (false, i)]
  | lcross i j => [(false, i), (true, j)]
  | dcup _ _ => []
  | dcap i _ => [(false, i), (true, i)]

/-- Top boundary of a shape. -/
def cod : Shape I → List (Letter I)
  | dot i => [(true, i)]
  | cross i j => [(true, j), (true, i)]
  | cup i => [(false, i), (true, i)]
  | cap _ => []
  | lcross i j => [(true, j), (false, i)]
  | dcup i _ => [(true, i), (false, i)]
  | dcap _ _ => []

/-- The parity of a generator of the given shape. -/
def parity : Shape I → ZMod 2
  | dot i => D.parity i
  | cross i j => D.parity i * D.parity j
  | cup _ => 0
  | cap _ => 0
  | lcross i j => D.parity i * D.parity j
  | dcup i n => D.parity i * n
  | dcap i n => D.parity i * n

theorem wt_dom_eq_wt_cod (ν : X) (g : Shape I) : wt D ν g.dom = wt D ν g.cod := by
  cases g <;> simp [dom, cod, sh] <;> abel

end Shape

/-! ## The signature -/

/-- The signature of `𝔘(𝔤)`: regions `X`, colours `Col I X`, generators a shape with the weight
of the rightmost region, with the parities of Definition 1.5 and (2.6). -/
def sig : Signature.{v, max u v, max u v} where
  Region := X
  Colour := Col I X
  colourSrc c := sh D c.l + c.r
  colourTgt c := c.r
  Gen := Shape I × X
  dom g := wd D g.2 g.1.dom
  cod g := wd D g.2 g.1.cod
  left g := wt D g.2 g.1.dom
  right g := g.2
  odd g := decide (g.1.parity D = 1)

@[simp] theorem sig_colourSrc (c : Col I X) : (sig D).colourSrc c = sh D c.l + c.r := rfl
@[simp] theorem sig_colourTgt (c : Col I X) : (sig D).colourTgt c = c.r := rfl

theorem parityDeg_sig (g : (sig D).Gen) : Presentation.parityDeg (sig D) g = g.1.parity D := by
  show (if decide (g.1.parity D = 1) = true then (1 : ZMod 2) else 0) = g.1.parity D
  generalize g.1.parity D = p
  fin_cases p <;> rfl

/-! ## Well-formed words -/

theorem ok_wd (μ : X) (t : List (Letter I)) : (sig D).ok (wt D μ t : X) (wd D μ t) := by
  induction t with
  | nil => trivial
  | cons l t ih => exact ⟨rfl, ih⟩

theorem endR_wd (μ : X) (t : List (Letter I)) : (sig D).endR (wt D μ t : X) (wd D μ t) = μ := by
  induction t with
  | nil => rfl
  | cons l t ih => exact ih

/-- The object given by the signed sequence `t` with rightmost region `μ`: the 1-morphism
`E_t 1_μ`. -/
def ob (μ : X) (t : List (Letter I)) : Obj (sig D) := ⟨(wt D μ t : X), wd D μ t⟩

/-! ## Layers in normal form -/

/-- The layer `u ⊗ g ⊗ v` with rightmost region `μ`. -/
def lay (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) : Layer (sig D) :=
  ⟨(wt D μ (u ++ g.dom ++ v) : X), wd D (wt D μ (g.dom ++ v)) u, (g, wt D μ v), wd D μ v⟩

theorem lay_valid (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (lay D μ u g v).Valid := by
  have hw := Shape.wt_dom_eq_wt_cod D (wt D μ v) g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (sig D).ok (wt D μ (u ++ g.dom ++ v) : X) (wd D (wt D μ (g.dom ++ v)) u)
    rw [List.append_assoc, wt_append]; exact ok_wd D _ u
  · show (sig D).endR (wt D μ (u ++ g.dom ++ v) : X) (wd D (wt D μ (g.dom ++ v)) u) =
      wt D (wt D μ v) g.dom
    rw [List.append_assoc, wt_append, endR_wd, wt_append]
  · exact ok_wd D _ _
  · exact endR_wd D _ _
  · show (sig D).ok (wt D (wt D μ v) g.dom : X) (wd D (wt D μ v) g.cod)
    rw [hw]; exact ok_wd D _ _
  · show (sig D).endR (wt D (wt D μ v) g.dom : X) (wd D (wt D μ v) g.cod) = wt D μ v
    rw [hw, endR_wd]
  · exact ok_wd D _ _

theorem lay_dom (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (lay D μ u g v).dom = ob D μ (u ++ g.dom ++ v) := by
  refine Obj.ext rfl ?_
  simp only [Layer.dom_word, lay, ob]
  change (wd D (wt D μ (g.dom ++ v)) u ++ wd D (wt D μ v) g.dom) ++ wd D μ v =
    wd D μ ((u ++ g.dom) ++ v)
  rw [List.append_assoc, List.append_assoc, wd_append D μ u, wd_append D μ g.dom]

theorem lay_cod (μ : X) (u : List (Letter I)) (g : Shape I) (v : List (Letter I)) :
    (lay D μ u g v).cod = ob D μ (u ++ g.cod ++ v) := by
  refine Obj.ext ?_ ?_
  · show wt D μ (u ++ g.dom ++ v) = wt D μ (u ++ g.cod ++ v)
    simp only [List.append_assoc, wt_append, Shape.wt_dom_eq_wt_cod]
  simp only [Layer.cod_word, lay, ob]
  change (wd D (wt D μ (g.dom ++ v)) u ++ wd D (wt D μ v) g.cod) ++ wd D μ v =
    wd D μ ((u ++ g.cod) ++ v)
  rw [List.append_assoc, List.append_assoc, wd_append D μ u, wd_append D μ g.cod,
    wt_append, wt_append, Shape.wt_dom_eq_wt_cod]

/-! ## Diagrams in normal form -/

/-- A layer in normal form: strands `u` to the left, a generator of shape `g`, strands `v` to
the right. -/
abbrev LayerData (I : Type u) : Type u := List (Letter I) × Shape I × List (Letter I)

/-- The layers `ls` form a diagram from the signed sequence `t` (bottom) to `t'` (top). -/
def SChain : List (Letter I) → List (LayerData I) → List (Letter I) → Prop
  | t, [], t' => t = t'
  | t, x :: ls, t' => t = x.1 ++ x.2.1.dom ++ x.2.2 ∧ SChain (x.1 ++ x.2.1.cod ++ x.2.2) ls t'

@[simp] theorem sChain_nil (t t' : List (Letter I)) : SChain t [] t' ↔ t = t' := Iff.rfl

@[simp] theorem sChain_cons (t t' : List (Letter I)) (x : LayerData I) (ls : List (LayerData I)) :
    SChain t (x :: ls) t' ↔ t = x.1 ++ x.2.1.dom ++ x.2.2 ∧ SChain (x.1 ++ x.2.1.cod ++ x.2.2) ls t' :=
  Iff.rfl

theorem SChain.append {t t' t'' : List (Letter I)} {ls ms : List (LayerData I)}
    (h₁ : SChain t ls t') (h₂ : SChain t' ms t'') : SChain t (ls ++ ms) t'' := by
  induction ls generalizing t with
  | nil => cases h₁; exact h₂
  | cons x ls ih => exact ⟨h₁.1, ih h₁.2⟩

theorem SChain.replicate (n : ℕ) (u : List (Letter I)) (i : I) (v : List (Letter I)) :
    SChain (u ++ [(true, i)] ++ v) (List.replicate n (u, Shape.dot i, v))
      (u ++ [(true, i)] ++ v) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ⟨rfl, ih⟩

/-- The layers of a normal-form diagram. -/
def layList (μ : X) (ls : List (LayerData I)) : List (Layer (sig D)) :=
  ls.map fun x => lay D μ x.1 x.2.1 x.2.2

theorem SChain.chain (μ : X) {t t' : List (Letter I)} {ls : List (LayerData I)}
    (h : SChain t ls t') : Chain (ob D μ t) (layList D μ ls) (ob D μ t') := by
  induction ls generalizing t with
  | nil => cases h; rfl
  | cons x ls ih =>
    obtain ⟨rfl, h⟩ := h
    exact ⟨lay_valid D μ _ _ _, lay_dom D μ _ _ _, by rw [lay_cod D]; exact ih h⟩

/-- The diagram with rightmost region `μ` given by the layers `ls`, from `E_t 1_μ` to
`E_{t'} 1_μ`. -/
def mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I)) (h : SChain t ls t') :
    ob D μ t ⟶ ob D μ t' :=
  Diagram.mk (layList D μ ls) (h.chain D μ)

@[simp] theorem layers_mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain t ls t') : Diagram.layers (mkD D μ ls h) = layList D μ ls := rfl

theorem mkD_comp (μ : X) {t t' t'' : List (Letter I)} (ls ms : List (LayerData I))
    (h₁ : SChain t ls t') (h₂ : SChain t' ms t'') :
    mkD D μ ls h₁ ≫ mkD D μ ms h₂ = mkD D μ (ls ++ ms) (h₁.append h₂) := by
  ext; simp [layList]

/-- The parity of a normal-form diagram: the sum of the parities of its generators. -/
theorem degree_parity_mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain t ls t') :
    Diagram.degree (Presentation.parityDeg (sig D)) (mkD D μ ls h) =
      (ls.map fun x => x.2.1.parity D).sum := by
  simp only [Diagram.degree, layers_mkD, layList, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  exact parityDeg_sig D _

end OddMath.SKM
