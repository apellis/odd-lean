/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Presentation
import StringDiagrams.Super.PresentedGraded

/-!
# The grading on the quiver Hecke supercategory

BE2, arXiv:1701.04133v2, §11 and the degree table after (1.31).
Dots have degree `2dᵢ`, crossings have degree `dᵢdᵢⱼ`; parity is independent
of this integer grading. No bar-consistency hypothesis is used.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LinDiagram
open SKM (dn_cast')
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (sy : SKM.Symmetrizer D)

/-- The generator degrees in BE2's normalization. -/
def gdeg : (sig D).Gen → ℤ
  | .dot i => 2 * sy.d i
  | .cross i j => sy.d i * D.d i j

/-- The degree of a normal-form diagram: the sum of the degrees of its generators, each in the
region `wt v` to its right. -/
theorem degree_gdeg_mkD {t t' : List I} (ls : List (LayerData I))
    (h : SChain t ls t') :
    Diagram.degree (gdeg D sy) (mkD D ls h) =
      (ls.map fun x => gdeg D sy x.2.1).sum := by
  simp only [Diagram.degree, layers_mkD, layList, List.map_map]
  rfl

/-- The degree of a layer list (for the homogeneity proofs). -/
abbrev gsum (ls : List (LayerData I)) : ℤ :=
  (ls.map fun x => gdeg D sy x.2.1).sum

theorem gsum_append (ls ms : List (LayerData I)) :
    gsum D sy (ls ++ ms) = gsum D sy ls + gsum D sy ms := by
  simp [gsum]

@[simp] theorem gsum_dotsL (u : List I) (i : I) (v : List I) (n : ℕ) :
    gsum D sy (dotsL u i v n) = n * (2 * sy.d i) := by
  simp [gsum, dotsL, gdeg, List.sum_replicate]

@[simp] theorem gsum_crossL (u : List I) (i j : I) (v : List I) :
    gsum D sy (crossL u i j v) = sy.d i * D.d i j := by
  simp [gsum, crossL, gdeg]

/-- A normal-form diagram of degree `d` lies in the degree-`d` part. -/
theorem dg_mem_gdeg {t t' : List I} {ls : List (LayerData I)}
    {h : SChain t ls t'} {d : ℤ} (hd : gsum D sy ls = d) :
    dg (k := k) D ls h ∈ LinDiagram.homDeg k (gdeg D sy) (ob D t) (ob D t') d :=
  of_mem_homDeg' (by rw [degree_gdeg_mkD]; exact hd)

theorem idg_mem_gdeg (t : List I) :
    idg (k := k) D t ∈ LinDiagram.homDeg k (gdeg D sy) (ob D t) (ob D t) 0 :=
  of_mem_homDeg' (Diagram.degree_id _ _)

/-- **The grading of `𝔘(𝔤)`** (Brundan–Ellis, §1, "Gradings"): under the homogeneity condition
(1.31), every relation of Definition 1.5 is homogeneous for the degrees `gdeg`. -/
theorem isHomogeneous_gdeg (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous) :
    (pres D Sc).IsHomogeneous (gdeg D sy) := by
  intro r
  cases r with
  | quadEq i =>
    exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | quadZero i j _ hd =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (idg_mem_gdeg D sy _))⟩
    rw [gsum_append, gsum_crossL, gsum_crossL, hd, (D.d_eq_zero_iff i j).mp hd]; ring
  | quadNe i j hij hd =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j), Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)))
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)))
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq => ?_)⟩
    · rw [gsum_append, gsum_crossL, gsum_crossL]; linarith
    · rw [gsum_dotsL, dn_cast' hij]; ring
    · rw [gsum_dotsL, dn_cast' (Ne.symm hij)]; linarith
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)
        rw [Finset.mem_Ioo] at hp hq
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp.2
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq.2
        have h31 := hc i j p q hp.1 hp' hq.1 hq' hs
        have hdji : D.d j i ≠ 0 := fun h0 => hd ((D.d_eq_zero_iff i j).mpr h0)
        rw [gsum_append, gsum_dotsL, gsum_dotsL]
        have key : D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j) = 0 := by
          have e1 : D.d j i * (sy.d j * q) = q * (sy.d i * D.d i j) := by rw [hji]; ring
          calc D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j)
              = sy.d i * (p * D.d j i - D.d i j * D.d j i) + D.d j i * (sy.d j * q) := by ring
            _ = sy.d i * (p * D.d j i - D.d i j * D.d j i) + q * (sy.d i * D.d i j) := by rw [e1]
            _ = sy.d i * (p * D.d j i + q * D.d i j - D.d i j * D.d j i) := by ring
            _ = 0 := by rw [h31]; ring
        have := (mul_eq_zero.mp key).resolve_left hdji
        linarith
  | slideL i j _ =>
    refine ⟨2 * sy.d i + sy.d i * D.d i j, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideLEq i =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))) (idg_mem_gdeg D sy _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | slideR i j _ =>
    refine ⟨2 * sy.d j + sy.d i * D.d i j, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideREq i =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))) (idg_mem_gdeg D sy _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | braid i j k' _ =>
    refine ⟨sy.d i * D.d i j + sy.d i * D.d i k' + sy.d j * D.d j k',
      Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (dg_mem_gdeg D sy ?_)⟩
    all_goals (simp only [gsum_append, gsum_crossL]; try ring)
  | braidEq i j hij =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j) - 2 * sy.d i, Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (dg_mem_gdeg D sy ?_))
      (Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)))
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq =>
        Submodule.sum_mem _ fun s hs => ?_)⟩
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · rw [Finset.mem_range] at hs
      rw [gsum_append, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        dn_cast' hij]
      push_cast; ring
    · by_cases hz : Sc.s i j p q = 0
      · rw [hz, mul_zero, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)
        rw [Finset.mem_Ioo] at hp hq
        rw [Finset.mem_range] at hs
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp.2
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq.2
        have h31 := hc i j p q hp.1 hp' hq.1 hq' hz
        have hd : D.d i j ≠ 0 := by omega
        have hdji : D.d j i ≠ 0 := fun h0 => hd ((D.d_eq_zero_iff i j).mpr h0)
        have key : D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j) = 0 := by
          have e1 : D.d j i * (sy.d j * q) = q * (sy.d i * D.d i j) := by rw [hji]; ring
          calc D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j)
              = sy.d i * (p * D.d j i - D.d i j * D.d j i) + D.d j i * (sy.d j * q) := by ring
            _ = sy.d i * (p * D.d j i - D.d i j * D.d j i) + q * (sy.d i * D.d i j) := by rw [e1]
            _ = sy.d i * (p * D.d j i + q * D.d i j - D.d i j * D.d j i) := by ring
            _ = 0 := by rw [h31]; ring
        have := (mul_eq_zero.mp key).resolve_left hdji
        rw [gsum_append, gsum_append, gsum_dotsL, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega),
          Nat.cast_sub (by omega)]
        push_cast; linarith

/-- Integer-homogeneous morphisms of `H`. -/
abbrev homDegree (Sc : SKM.Scalars D k) (a b : List I) (d : ℤ) :=
  (pres D Sc).homDeg (gdeg D sy) (ob D a) (ob D b) d

/-- The integer grading is an internal direct sum, not only a filtration. -/
theorem isInternal_homDegree (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous) (a b : List I) :
    DirectSum.IsInternal (homDegree D sy Sc a b) :=
  Presentation.isInternal_homDeg (isHomogeneous_gdeg D sy Sc hc) (ob D a) (ob D b)

end OddMath.QuiverHecke
