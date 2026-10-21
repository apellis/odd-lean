/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Basic

/-!
# The quiver Hecke supercategory

Brundan–Ellis, arXiv:1701.04133v2, §11, definition preceding (11.1),
with the normalization of Definition 1.5, (1.7)–(1.9). This presentation
contains only upward dots and crossings; its quotient is independent of
`SKM.U`. The Koszul far-commutation relations are supplied by the ambient
presentation machinery, not additional defining relations.

The parameters are BE2's `t` and `s`. In particular the zero-edge quadratic
relation is `τ² = tᵢⱼ`, not the sum of two constant terms. KKT §3.1
packages these coefficients into `Qᵢⱼ`; Hill–Wang uses a specialized
polynomial. This module does not replace BE2's parameters by that specialization.
BE2 also reverses strand positions relative to the left-to-right list convention
used here. The changed parity shift mentioned in BE2 after Lemma 11.1 concerns
Hill–Wang's `(q,π)`-integer convention, not a change to the local relations.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LinDiagram
open SKM (zsign parity_mul_dn)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)

/-- `n` dots on the strand `Eᵢ` between `u` and `v`. -/
def dotsL (u : List I) (i : I) (v : List I) (n : ℕ) : List (LayerData I) :=
  List.replicate n (u, Shape.dot i, v)

theorem sChain_dotsL (u : List I) (i : I) (v : List I) (n : ℕ) :
    SChain (u ++ [i] ++ v) (dotsL u i v n) (u ++ [i] ++ v) :=
  SChain.replicate n u i v

/-- A single crossing `τ : Eᵢ Eⱼ → Eⱼ Eᵢ` between `u` and `v`. -/
def crossL (u : List I) (i j : I) (v : List I) : List (LayerData I) :=
  [(u, Shape.cross i j, v)]

/-- The upward relations (1.7)–(1.9), without a weight label. -/
inductive Rel (D : SKM.Datum I X)
  | quadEq (i : I) 
  | quadZero (i j : I)  (hij : i ≠ j) (hd : D.d i j = 0)
  | quadNe (i j : I)  (hij : i ≠ j) (hd : D.d i j ≠ 0)
  | slideL (i j : I)  (hij : i ≠ j)
  | slideLEq (i : I) 
  | slideR (i j : I)  (hij : i ≠ j)
  | slideREq (i : I) 
  | braid (i j k : I)  (h : ¬(i = k ∧ i ≠ j))
  | braidEq (i j : I)  (hij : i ≠ j)

namespace Rel
variable {D}
@[simp]
def dom : Rel D → List I
  | quadEq i => [i, i]
  | quadZero i j _ _ | quadNe i j _ _ | slideL i j _ | slideR i j _ => [i, j]
  | slideLEq i | slideREq i => [i, i]
  | braid i j k _ => [i, j, k]
  | braidEq i j _ => [i, j, i]

@[simp]
def cod : Rel D → List I
  | quadEq i => [i, i]
  | quadZero i j _ _ | quadNe i j _ _ => [i, j]
  | slideL i j _ | slideR i j _ => [j, i]
  | slideLEq i | slideREq i => [i, i]
  | braid i j k _ => [k, j, i]
  | braidEq i j _ => [i, j, i]

end Rel
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Shorthand: the class of the normal-form diagram with layers `ls` as a linear combination. -/
abbrev dg  {t t' : List I} (ls : List (LayerData I)) (h : SChain t ls t') :
    LinDiagram k (ob D t) (ob D t') :=
  of (mkD D ls h)

/-- The identity of `ob D t` as a linear combination. -/
abbrev idg  (t : List I) : LinDiagram k (ob D t) (ob D t) := of (𝟙 _)

/-- The relations of Definition 1.5, each written as `lhs - rhs`. -/
def relation : (r : Rel D) → LinDiagram k (ob D r.dom) (ob D r.cod)
  | .quadEq i => dg D (crossL [] i i [] ++ crossL [] i i [])
      (by simp [crossL, Shape.dom, Shape.cod])
  | .quadZero i j _ _ => dg D (crossL [] i j [] ++ crossL [] j i [])
      (by simp [crossL, Shape.dom, Shape.cod]) - (Sc.t i j : k) • idg D _
  | .quadNe i j _ _ => dg D (crossL [] i j [] ++ crossL [] j i [])
      (by simp [crossL, Shape.dom, Shape.cod]) -
      (Sc.t i j : k) • dg D (dotsL [] i [j] (D.dn i j)) (sChain_dotsL [] i [j] _) -
      (Sc.t j i : k) • dg D (dotsL [i] j [] (D.dn j i)) (sChain_dotsL [i] j [] _) -
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
        Sc.s i j p q • dg D (dotsL [i] j [] q ++ dotsL [] i [j] p)
          ((sChain_dotsL [i] j [] q).append (sChain_dotsL [] i [j] p))
  | .slideL i j _ => dg D (dotsL [] i [j] 1 ++ crossL [] i j [])
        ((sChain_dotsL [] i [j] 1).append (by simp [crossL, Shape.dom, Shape.cod])) -
      zsign k (D.parity i * D.parity j) • dg D (crossL [] i j [] ++ dotsL [j] i [] 1)
        (SChain.append (t' := [j] ++ [i] ++ []) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [j] i [] 1))
  | .slideLEq i => dg D (dotsL [] i [i] 1 ++ crossL [] i i [])
        ((sChain_dotsL [] i [i] 1).append (by simp [crossL, Shape.dom, Shape.cod])) -
      zsign k (D.parity i * D.parity i) • dg D (crossL [] i i [] ++ dotsL [i] i [] 1)
        (SChain.append (t' := [i] ++ [i] ++ []) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [i] i [] 1)) - idg D _
  | .slideR i j _ => dg D (crossL [] i j [] ++ dotsL [] j [i] 1)
        (SChain.append (t' := [] ++ [j] ++ [i]) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [] j [i] 1)) -
      zsign k (D.parity i * D.parity j) • dg D (dotsL [i] j [] 1 ++ crossL [] i j [])
        ((sChain_dotsL [i] j [] 1).append (by simp [crossL, Shape.dom, Shape.cod]))
  | .slideREq i => dg D (crossL [] i i [] ++ dotsL [] i [i] 1)
        (SChain.append (t' := [] ++ [i] ++ [i]) (by simp [crossL, Shape.dom, Shape.cod])
          (sChain_dotsL [] i [i] 1)) -
      zsign k (D.parity i * D.parity i) • dg D (dotsL [i] i [] 1 ++ crossL [] i i [])
        ((sChain_dotsL [i] i [] 1).append (by simp [crossL, Shape.dom, Shape.cod])) -
      idg D _
  | .braid i j k' _ =>
      dg D (crossL [] i j [k'] ++ crossL [j] i k' [] ++ crossL [] j k' [i])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      dg D (crossL [i] j k' [] ++ crossL [] i k' [j] ++ crossL [k'] i j [])
        (by simp [crossL, Shape.dom, Shape.cod])
  | .braidEq i j _ =>
      dg D (crossL [] i j [i] ++ crossL [j] i i [] ++ crossL [] j i [i])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      dg D (crossL [i] j i [] ++ crossL [] i i [j] ++ crossL [i] i j [])
        (by simp [crossL, Shape.dom, Shape.cod]) -
      ∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          dg D (dotsL [i, j] i [] s ++ dotsL [] i [j, i] (D.dn i j - 1 - s))
            ((sChain_dotsL [i, j] i [] s).append (sChain_dotsL [] i [j, i] _)) -
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          dg D (dotsL [i, j] i [] s ++ dotsL [i] j [i] q ++
              dotsL [] i [j, i] (p - 1 - s))
            (((sChain_dotsL [i, j] i [] s).append (sChain_dotsL [i] j [i] q)).append
              (sChain_dotsL [] i [j, i] _))

/-- The independent presentation of the quiver Hecke supercategory. -/
def pres : Presentation (sig D) k where
  Rel := Rel D
  dom r := ob D r.dom
  cod r := ob D r.cod
  rel := relation D Sc

/-- A normal-form diagram whose generators have parities summing to `d` has parity `d`. -/
theorem dg_mem {t t' : List I} {ls : List (LayerData I)} {h : SChain t ls t'}
    {d : ZMod 2} (hd : (ls.map fun x => x.2.1.parity D).sum = d) :
    dg (k := k) D ls h ∈
      LinDiagram.homDeg k (Presentation.parityDeg (sig D)) (ob D t) (ob D t') d :=
  of_mem_homDeg' (by rw [degree_parity_mkD]; exact hd)

theorem idg_mem (t : List I) :
    idg (k := k) D t ∈
      LinDiagram.homDeg k (Presentation.parityDeg (sig D)) (ob D t) (ob D t) 0 :=
  of_mem_homDeg' (Diagram.degree_id _ _)

/-- The parities of the layer lists used in the relations. -/
theorem parity_sum_append (ls ms : List (LayerData I)) :
    ((ls ++ ms).map fun x => x.2.1.parity D).sum =
      (ls.map fun x => x.2.1.parity D).sum + (ms.map fun x => x.2.1.parity D).sum := by
  simp

@[simp] theorem parity_dotsL (u : List I) (i : I) (v : List I) (n : ℕ) :
    ((dotsL u i v n).map fun x => x.2.1.parity D).sum = (n : ZMod 2) * D.parity i := by
  simp [dotsL, Shape.parity, List.sum_replicate, nsmul_eq_mul]

@[simp] theorem parity_crossL (u : List I) (i j : I) (v : List I) :
    ((crossL u i j v).map fun x => x.2.1.parity D).sum = D.parity i * D.parity j := by
  simp [crossL, Shape.parity]

/-- All relations (1.7)–(1.9) are parity-homogeneous, by (1.4) and (1.6). -/
theorem isParityHomogeneous : (pres D Sc).IsParityHomogeneous := by
  intro r
  cases r with
  | quadEq i =>
    refine ⟨0, dg_mem D ?_⟩
    rw [parity_sum_append]; simp only [parity_crossL]
    generalize D.parity i = a; revert a; decide
  | quadZero i j _ _ =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem D ?_) (Submodule.smul_mem _ _ (idg_mem D _))⟩
    rw [parity_sum_append]; simp only [parity_crossL]
    generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | quadNe i j _ _ =>
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
  | slideL i j _ =>
    refine ⟨D.parity i + D.parity i * D.parity j, Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | slideLEq i =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))) (idg_mem D _)⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; revert a; decide
  | slideR i j _ =>
    refine ⟨D.parity j + D.parity i * D.parity j, Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; generalize D.parity j = b; revert a b; decide
  | slideREq i =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem D ?_)
      (Submodule.smul_mem _ _ (dg_mem D ?_))) (idg_mem D _)⟩
    all_goals rw [parity_sum_append]; simp only [parity_crossL, parity_dotsL, Nat.cast_one,
      one_mul]
    all_goals generalize D.parity i = a; revert a; decide
  | braid i j k' _ =>
    refine ⟨D.parity i * D.parity j + D.parity i * D.parity k' + D.parity j * D.parity k',
      Submodule.sub_mem _ (dg_mem D ?_) (dg_mem D ?_)⟩
    all_goals simp only [parity_sum_append, parity_crossL]
    all_goals generalize D.parity i = a; generalize D.parity j = b; generalize D.parity k' = c
    all_goals revert a b c; decide
  | braidEq i j _ =>
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

/-- The monoidal supercategory `H` of BE2 §11. -/
abbrev H := (pres D Sc).Presented

instance supercategory : Supercategory k (H D Sc) :=
  (pres D Sc).supercategory (isParityHomogeneous D Sc)

instance monoidalSupercategory : MonoidalSupercategory k (H D Sc) :=
  (pres D Sc).monoidalSupercategory (isParityHomogeneous D Sc)

/-- The same-colour corner, before any assertion of its nilHecke comparison. -/
abbrev Corner (i : I) (n : ℕ) := CategoryTheory.End ((pres D Sc).obj (ob D (List.replicate n i)))

end OddMath.QuiverHecke
