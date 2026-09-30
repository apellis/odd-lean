import OddMath.Diagrams.OddNilHecke.DifferentialComparison

/-!
# The dg odd nilHecke algebra `(ONH_n, d)` as a dg ring

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§2.2 ((2.3)–(2.5)), §3.2 (Proposition 3.3, Corollary 3.9) and Proposition 3.16(2).

Ellis–Qi equip the odd nilHecke algebra `ONH_n` with the differential `d(x_i) = x_i²`,
`d(∂_i) = 1`. The grading is the `q`-grading (`deg x_i = 2`, `deg ∂_i = -2`) together with the
parity (all generators odd); `d` has bidegree `(2, 1̄)`. As in
`OddMath.Frontier.EQDGStructures`, the `DG` library's cohomological `ℤ`-grading is **half the
`q`-degree**: `x_i` has degree `1` and `∂_i` degree `-1`, `d` has degree `+1`, and the parity of a
homogeneous element is its degree mod `2` (`grading_le_parity`), so that the Koszul sign
`(-1)^{deg}` of the `DG` library is the Ellis–Qi parity sign.

## Contents

This file: `zDeg`, the `ℤ`-degree of the generators of the diagrammatic odd nilHecke category
(`dot ↦ 1`, `crossing ↦ -1`); the presentation is homogeneous (`isHomogeneous_zDeg`), the
diagrammatic differential has degree `+1` (`deriv_mem_homDeg_zDeg`), and the parity of a
morphism of degree `k` is `k mod 2` (`homDeg_zDeg_le_parityDeg`).

Companion files:

* `EQOnhDGRing`: the grading `grading n k` of `Presented n` (rank `n + 2`), an internal direct
  sum decomposition, parity `k mod 2` (`grading_le_parity`); `ONH n`, a type synonym of
  `NilHeckeAction.Presented n` with the differential `dONH n`, a dg ring (`DG.DGRing`) and a dg
  `ℤ`-algebra (`ONH.dgAlgebra_int`);
* `EQOnhDGCompare`: `grading n k` is the `q`-degree-`2k` part `NilHeckeGrading.degreePiece n (2k)`;
* `EQOnhDGPoly`: the inclusion of dots `ONH.polyHom n : OPol (n + 2) →ᵈᵍ+* ONH n`;
* `EQOnhDGAcyclic`: **Proposition 3.16(2)**, `H(ONH_{n+2}) = 0`, every dg `ONH_{n+2}`-module is
  acyclic and `D(ONH_{n+2})` is zero;
* `EQOnhDGZn`, `EQOnhDGEnd`, `EQOnhDGEndIso`: **Corollary 3.9**, `Z_{n+2}` is a dg
  `(ONH_{n+2}, OΛ_{n+2})`-bimodule, and `ONH_{n+2}ᵒᵖ ≅ END_{OΛᵒᵖ}(Z_{n+2})` as dg algebras.

## Ranks

`Presented n` has rank `n + 2`, so only `ONH_N` with `N ≥ 2` is covered. For `N = 1`,
`ONH_1 = OPol_1` with `d(x) = x²` is the dg ring `OddMath.Frontier.EQSkewDifferential.OPol 1`
of `EQDGStructures`, and `ONH_0 = ℤ` (concentrated in degree `0`, `d = 0`). Proposition 3.16(2)
concerns `N ≥ 2`: for `N ≤ 1` the degree `-1` part vanishes, so the cocycle `1` is not a
coboundary.
-/

noncomputable section

namespace OddMath.Frontier.EQOnhDG

open CategoryTheory StringDiagrams
open OddMath.Diagrams.OddNilHecke
open OddMath.Frontier NilHeckeAction

/-! ## The `ℤ`-degree on diagrams -/

/-- The `ℤ`-degree (half the Ellis–Qi `q`-degree) of the generators: a dot has degree `1`, a
crossing degree `-1`. -/
def zDeg : sig.Gen → ℤ
  | .dot => 1
  | .cross => -1

theorem degree_dlay_zDeg {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) :
    Diagram.degree zDeg (dlay h) = zDeg g := by
  rw [Diagram.degree, layers_dlay]
  simp [lay]

theorem cast_zDeg (g : sig.Gen) : ((zDeg g : ℤ) : ZMod 2) = parityDeg g := by
  cases g
  · simp [zDeg, parityDeg]
  · simp only [zDeg, parityDeg, Int.cast_neg, Int.cast_one]; decide

/-- The parity degree of a diagram is its `ℤ`-degree mod `2`. -/
theorem degree_zDeg_cast {a b : Obj sig} (f : a ⟶ b) :
    ((Diagram.degree zDeg f : ℤ) : ZMod 2) = Diagram.degree parityDeg f := by
  simp only [Diagram.degree]
  generalize Diagram.layers f = ls
  induction ls with
  | nil => simp
  | cons L ls ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, Int.cast_add, ih, cast_zDeg]

/-- The odd nilHecke presentation is homogeneous for the `ℤ`-degree. -/
theorem isHomogeneous_zDeg : (pres ℤ).IsHomogeneous zDeg := by
  intro r
  classical
  cases r with
  | square => exact ⟨_, LinDiagram.of_mem_homDeg _⟩
  | braid =>
    refine ⟨-3, Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' ?_) (LinDiagram.of_mem_homDeg' ?_)⟩ <;>
      simp only [Diagram.degree_comp, degree_dlay_zDeg, zDeg] <;> norm_num
  | mixedRight =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (LinDiagram.of_mem_homDeg' ?_)) (LinDiagram.of_mem_homDeg' ?_)⟩ <;>
      rfl
  | mixedLeft =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (LinDiagram.of_mem_homDeg' ?_)
      (LinDiagram.of_mem_homDeg' ?_)) (LinDiagram.of_mem_homDeg' ?_)⟩ <;>
      rfl

/-! ## The differential has degree `+1` -/

section Deriv

variable (a b c : ℤ)

theorem ansatzδ_mem_homDeg_zDeg (g : sig.Gen) :
    (ansatz ℤ a b c).δ g ∈
      LinDiagram.homDeg ℤ zDeg (sig.genDom g) (sig.genCod g) (zDeg g + 1) := by
  cases g with
  | dot =>
    exact LinDiagram.of_mem_homDeg' (by rw [Diagram.degree_comp]; rfl)
  | cross =>
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ ?_)) (Submodule.smul_mem _ _ ?_)
    · exact LinDiagram.of_mem_homDeg' rfl
    · exact LinDiagram.of_mem_homDeg' (by simp [degree_dlay_zDeg, zDeg])
    · exact LinDiagram.of_mem_homDeg' (by simp [degree_dlay_zDeg, zDeg])

theorem derivList_mem_homDeg_zDeg (ls : List (Layer sig)) {X Y : Obj sig} (h : Chain X ls Y) :
    (ansatz ℤ a b c).derivList X ls Y h ∈
      LinDiagram.homDeg ℤ zDeg X Y ((ls.map fun L => zDeg L.gen).sum + 1) := by
  induction ls generalizing X with
  | nil =>
    rw [LocalDerivation.derivList]
    exact Submodule.zero_mem _
  | cons L ls ih =>
    rw [LocalDerivation.derivList]
    apply LinDiagram.cast_mem_homDeg
    have hδ : (ansatz ℤ a b c).layerDeriv L h.1 ∈
        LinDiagram.homDeg ℤ zDeg _ _ (zDeg L.gen + 1) :=
      LinDiagram.whisker_mem_homDeg (ansatzδ_mem_homDeg_zDeg a b c L.gen) _ _ _
    have hmk : LinDiagram.of (Diagram.mk ls h.2.2) ∈
        LinDiagram.homDeg ℤ zDeg _ _ ((ls.map fun L => zDeg L.gen).sum) :=
      LinDiagram.of_mem_homDeg' (Diagram.degree_mk _ _ _)
    have hlay : LinDiagram.of (Diagram.ofLayer L h.1) ∈
        LinDiagram.homDeg ℤ zDeg _ _ (zDeg L.gen) :=
      LinDiagram.of_mem_homDeg' (by rw [Diagram.degree_ofLayer])
    rw [List.map_cons, List.sum_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
    · have := LinDiagram.comp_mem_homDeg hδ hmk
      rwa [add_right_comm] at this
    · have := LinDiagram.comp_mem_homDeg hlay (ih h.2.2)
      rwa [← add_assoc] at this

/-- The derivative of a diagram has degree one more. -/
theorem derivDiag_mem_homDeg_zDeg {a' b' : Obj sig} (f : a' ⟶ b') :
    (ansatz ℤ a b c).derivDiag f ∈
      LinDiagram.homDeg ℤ zDeg a' b' (Diagram.degree zDeg f + 1) :=
  derivList_mem_homDeg_zDeg a b c _ _

end Deriv

/-- **The differential has degree `+1`** for the `ℤ`-grading (half the `q`-degree): it maps
morphisms of degree `k` to morphisms of degree `k + 1`. -/
theorem deriv_mem_homDeg_zDeg {X Y : Obj sig} {f : (pres ℤ).obj X ⟶ (pres ℤ).obj Y} {k : ℤ}
    (hf : f ∈ (pres ℤ).homDeg zDeg X Y k) :
    deriv ℤ f ∈ (pres ℤ).homDeg zDeg X Y (k + 1) := by
  obtain ⟨F, hF, rfl⟩ := Presentation.mem_homDeg_iff.mp hf
  rw [deriv, Presentation.deriv_lin]
  refine Presentation.lin_mem_homDeg ?_
  clear hf
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hF
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, rfl⟩ := hy
    rw [LocalDerivation.derivFree_single, one_smul]
    exact (show Diagram.degree zDeg g = k from hg) ▸ derivDiag_mem_homDeg_zDeg 1 0 0 g
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy

/-- A morphism of `ℤ`-degree `k` has parity `k mod 2`. -/
theorem homDeg_zDeg_le_parityDeg (X Y : Obj sig) (k : ℤ) :
    (pres ℤ).homDeg zDeg X Y k ≤ (pres ℤ).homDeg parityDeg X Y (k : ZMod 2) := by
  intro f hf
  obtain ⟨F, hF, rfl⟩ := Presentation.mem_homDeg_iff.mp hf
  refine Presentation.lin_mem_homDeg (LinDiagram.mem_homDeg_iff.mpr fun g hg => ?_)
  rw [← degree_zDeg_cast, LinDiagram.mem_homDeg_iff.mp hF g hg]

end OddMath.Frontier.EQOnhDG

end
