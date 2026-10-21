/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.TableIsotopy
import OddMath.SKM.ChevalleyGrading

/-!
# Integer degrees of bubble coefficients and decorated diagrams

For Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
§§11–12, the coefficient generators in (1.21) have strictly positive degrees.
The degree formulas below include the negatively dotted bubbles of Definition 2.3
at arbitrary weights. Placement in the rightmost region preserves degree, and
extended diagram evaluation has the numerical degree computed by `tableDegree`.

Membership in the image submodules `Presentation.homDeg` needs no homogeneity
hypothesis on the relations. Under `Scalars.Homogeneous`, `isHomogeneous_gdeg`
identifies these submodules as the integer grading of the presented category.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (sy : Symmetrizer D)

/-- The degree of a normal-form class, in a specified degree. -/
theorem cl_mem_gdeg_of_eq {μ : X} {s t : List (Letter I)} {L : List (LayerData I)}
    {d : ℤ} (hd : gsum D sy μ L = d) :
    cl D Sc μ s t L ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ s) (ob D μ t) d :=
  hd ▸ cl_mem_gdeg sy μ s t L

variable (cs : CScalars Sc)

/-- The left cup has the degree prescribed by the generator table. -/
theorem etaP_mem_gdeg (i : I) (μ : X) :
    etaP cs i μ ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * (1 - D.h i μ)) := by
  unfold etaP
  split_ifs with h
  · apply Submodule.smul_mem
    apply cl_mem_gdeg_of_eq
    rw [gsum_dcupL, Int.toNat_of_nonneg (show 0 ≤ D.h i μ - 1 by omega)]
    ring
  · apply Submodule.smul_mem
    apply cl_mem_gdeg_of_eq
    rw [gsum_append, gsum_etaL, gsum_lcrossL,
      Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega)]
    ring

/-- The left cap has the degree prescribed by the generator table. -/
theorem epsP_mem_gdeg (i : I) (μ : X) :
    epsP cs i μ ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (sy.d i * (1 + D.h i μ)) := by
  unfold epsP
  split_ifs with h
  · apply Submodule.smul_mem
    apply cl_mem_gdeg_of_eq
    rw [gsum_dcapL, Int.toNat_of_nonneg (show 0 ≤ -D.h i μ - 1 by omega)]
    ring
  · apply Submodule.smul_mem
    apply cl_mem_gdeg_of_eq
    rw [gsum_append, gsum_lcrossL, gsum_epsL,
      Int.toNat_of_nonneg (show 0 ≤ D.h i μ by omega)]
    ring

/-- Degree of a left bubble, including every fake-bubble branch. -/
theorem bubL_mem_gdeg (i : I) (μ : X) (n : ℤ) :
    bubL cs i μ n ∈ (pres D Sc).homDeg (gdeg D sy) _ _
      (2 * sy.d i * (n - D.h i μ + 1)) := by
  unfold bubL
  split_ifs with hn hh he
  · have hd : sy.d i * (1 - D.h i μ) + gsum D sy μ (epsL i n.toNat) =
        2 * sy.d i * (n - D.h i μ + 1) := by
      rw [gsum_epsL, Int.toNat_of_nonneg hn]
      ring
    exact hd ▸ comp_mem_homDeg (etaP_mem_gdeg sy cs i μ)
      (cl_mem_gdeg (Sc := Sc) sy μ [up i, dn i] [] (epsL i n.toNat))
  · apply Submodule.smul_mem
    apply cl_mem_gdeg_of_eq
    rw [gsum_append, gsum_etaL, gsum_dcapL,
      Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega),
      Int.toNat_of_nonneg (show 0 ≤ -n - 1 by omega)]
    ring
  · rw [he, show 2 * sy.d i * (D.h i μ - 1 - D.h i μ + 1) = 0 by ring]
    exact Submodule.smul_mem _ _ (id_mem_homDeg _ _ _)
  · exact Submodule.zero_mem _

/-- Degree of a right bubble, including every fake-bubble branch. -/
theorem bubR_mem_gdeg (i : I) (μ : X) (n : ℤ) :
    bubR cs i μ n ∈ (pres D Sc).homDeg (gdeg D sy) _ _
      (2 * sy.d i * (n + D.h i μ + 1)) := by
  unfold bubR
  split_ifs with hn hh he
  · have hd : gsum D sy μ (etaL i n.toNat) + sy.d i * (1 + D.h i μ) =
        2 * sy.d i * (n + D.h i μ + 1) := by
      rw [gsum_etaL, Int.toNat_of_nonneg hn]
      ring
    exact hd ▸ comp_mem_homDeg
      (cl_mem_gdeg (Sc := Sc) sy μ [] [dn i, up i] (etaL i n.toNat))
      (epsP_mem_gdeg sy cs i μ)
  · apply Submodule.smul_mem
    apply cl_mem_gdeg_of_eq
    rw [gsum_append, gsum_dcupL, gsum_epsL,
      Int.toNat_of_nonneg (show 0 ≤ -n - 1 by omega),
      Int.toNat_of_nonneg (show 0 ≤ D.h i μ by omega)]
    ring
  · rw [he, show 2 * sy.d i * (-D.h i μ - 1 + D.h i μ + 1) = 0 by ring]
    exact Submodule.smul_mem _ _ (id_mem_homDeg _ _ _)
  · exact Submodule.zero_mem _

/-- The shifted bubble notation removes dependence on the ambient weight. -/
theorem bubLs_mem_gdeg (i : I) (μ : X) (n : ℤ) :
    bubLs cs i μ n ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i * n) := by
  simpa only [bubLs, show n + D.h i μ - 1 - D.h i μ + 1 = n by ring] using
    bubL_mem_gdeg sy cs i μ (n + D.h i μ - 1)

/-- The shifted right bubble has the same weight-independent degree. -/
theorem bubRs_mem_gdeg (i : I) (μ : X) (n : ℤ) :
    bubRs cs i μ n ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i * n) := by
  simpa only [bubRs, show n - D.h i μ - 1 + D.h i μ + 1 = n by ring] using
    bubR_mem_gdeg sy cs i μ (n - D.h i μ - 1)

/-- The odd bubble has degree `2dᵢ` at every weight. -/
theorem oddBubble_mem_gdeg (i : I) (μ : X) :
    oddBubble cs i μ ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i) := by
  unfold oddBubble
  split_ifs
  · apply Submodule.smul_mem
    simpa only [sub_self, zero_add, mul_one] using bubL_mem_gdeg sy cs i μ (D.h i μ)
  · apply Submodule.smul_mem
    simpa only [neg_add_cancel, zero_add, mul_one] using bubR_mem_gdeg sy cs i μ (-D.h i μ)

variable (D) in
/-- Integer degree of a polynomial or exterior coefficient generator. -/
def symGenDegree : SYMGen D → ℤ
  | .inl (i, n) => if D.parity i = 0 then 2 * sy.d i * ((n : ℤ) + 1)
      else 4 * sy.d i * ((n : ℤ) + 1)
  | .inr i => 2 * sy.d i

/-- All coefficient generators have strictly positive integer degree. -/
theorem symGenDegree_pos (g : SYMGen D) : 0 < symGenDegree D sy g := by
  rcases g with ⟨i, n⟩ | i
  · have hp := sy.pos i
    dsimp [symGenDegree]
    split_ifs <;> positivity
  · exact mul_pos (by decide) (sy.pos i)

variable (D) in
/-- The positive natural weight used for finite generator words. -/
def symGenNatDegree (g : SYMGen D) : ℕ := (symGenDegree D sy g).toNat

@[simp] theorem symGenNatDegree_cast (g : SYMGen D) :
    (symGenNatDegree D sy g : ℤ) = symGenDegree D sy g :=
  Int.toNat_of_nonneg (symGenDegree_pos sy g).le

theorem symGenNatDegree_pos (g : SYMGen D) : 0 < symGenNatDegree D sy g := by
  have h := symGenDegree_pos sy g
  rw [← symGenNatDegree_cast sy g] at h
  exact_mod_cast h

/-- Every generator image is homogeneous in the presented Hom space. -/
theorem betaSYMGen_mem_gdeg (μ : X) (g : SYMGen D) :
    betaSYMGen cs μ g ∈ (pres D Sc).homDeg (gdeg D sy)
      (ob D μ []) (ob D μ []) (symGenDegree D sy g) := by
  rcases g with ⟨i, n⟩ | i
  · dsimp only [betaSYMGen, symGenDegree]
    split_ifs
    · exact Submodule.smul_mem _ _ (bubLs_mem_gdeg sy cs i μ _)
    · convert Submodule.smul_mem _ (↑(cs.c μ i)⁻¹ : k)
        (bubLs_mem_gdeg sy cs i μ (2 * ((n : ℤ) + 1))) using 1 <;> try rfl
      congr 1
      ring
  · exact oddBubble_mem_gdeg sy cs i μ

/-- Placement preserves integer degree, including its boundary transports. -/
theorem plcL_mem_gdeg {μ : X} {u v s t : List (Letter I)} {d : ℤ}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) _ _ d) :
    plcL D Sc μ u v s t f ∈ (pres D Sc).homDeg (gdeg D sy)
      (ob D μ (u ++ s ++ v)) (ob D μ (u ++ t ++ v)) d := by
  unfold plcL
  split_ifs with h
  · dsimp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
    simpa only [zero_add, add_zero] using comp_mem_homDeg
      (eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
        (congrArg (pres D Sc).obj (ob_whisker D μ u v s s rfl).symm))
      (comp_mem_homDeg (whisk_mem_homDeg hf _ _)
        (eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
          (congrArg (pres D Sc).obj (ob_whisker D μ u v s t h))))
  · exact Submodule.zero_mem _

/-- Word transports do not change integer degree. -/
theorem wordCast_mem_gdeg {μ : X} {s t s' t' : List (Letter I)}
    (hs : s = s') (ht : t = t') {d : ℤ}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) _ _ d) :
    wordCast μ hs ht f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ s') (ob D μ t') d := by
  subst s' t'
  exact hf

/-- Rightmost bubble placement preserves the integer degree. -/
theorem bubAt_mem_gdeg {μ : X} (v : List (Letter I)) {d : ℤ}
    {f : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}
    (hf : f ∈ (pres D Sc).homDeg (gdeg D sy) _ _ d) :
    bubAt D Sc μ v f ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ v) (ob D μ v) d :=
  wordCast_mem_gdeg sy _ _ (plcL_mem_gdeg sy hf)

/-- A single extended layer has its numerical table degree. -/
theorem xlay_mem_gdeg (μ : X) (x : XLayer I) :
    xlay cs μ x ∈ (pres D Sc).homDeg (gdeg D sy)
      (ob D μ (x.1 ++ x.2.1.dom ++ x.2.2))
      (ob D μ (x.1 ++ x.2.1.cod ++ x.2.2)) (tableDegree D sy μ [x]) := by
  rcases x with ⟨a, g, b⟩
  cases g <;>
    simp only [xlay, XShape.dom, XShape.cod, tableDegree, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  · rename_i g
    simpa only [gsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
      (cl_mem_gdeg (Sc := Sc) sy μ (a ++ g.dom ++ b) (a ++ g.cod ++ b) [(a, g, b)])
  · exact plcL_mem_gdeg sy (μ := μ) (u := a) (v := b) (etaP_mem_gdeg sy cs _ (wt D μ b))
  · exact plcL_mem_gdeg sy (μ := μ) (u := a) (v := b) (epsP_mem_gdeg sy cs _ (wt D μ b))

/-- Evaluation of any extended diagram has the degree of its table sum.
This also covers invalid chains, whose evaluation is zero. -/
theorem xev_mem_gdeg (μ : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    xev cs μ s t L ∈ (pres D Sc).homDeg (gdeg D sy)
      (ob D μ s) (ob D μ t) (tableDegree D sy μ L) := by
  induction L generalizing s with
  | nil => exact cl_mem_gdeg sy μ s t []
  | cons x L ih =>
    simpa only [xev_cons, tableDegree, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, gsum, zero_add] using
      comp_mem_homDeg (cl_mem_gdeg (Sc := Sc) sy μ s _ [])
        (comp_mem_homDeg (xlay_mem_gdeg sy cs μ x) (ih _))

end OddMath.SKM
