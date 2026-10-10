/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ChevalleyInv
import OddMath.SKM.LeftAdj2

/-!
# The left adjunction on `Fᵢ` (Brundan–Ellis, Proposition 6.2, second relation)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 6.2, the
second relation of (6.6), which the paper deduces from the first one by the Chevalley involution
(Proposition 3.5).

* `Om μ s t f`: the image under `ω` of a 2-morphism `f : E_s 1_μ ⟶ E_t 1_μ`, as a 2-morphism
  `E_{flip t} 1_{-μ} ⟶ E_{flip s} 1_{-μ}` (the two `eqToHom`s of `omega_obj` removed);
  `Om_cl`, `Om_add`, `Om_smul`, `Om_id`.
* `eq_6_6_b`: on `Fᵢ 1_λ`, `η'` (at `λ`) on the right followed by `ε'` (at `λ - αᵢ`) on the left is
  the identity: the image under `ω` of the first relation (`eq_6_6_a`) at `-λ`, computed case by case
  on normal-form diagrams.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Supercategory Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k}

variable (D Sc) in
/-- The image under `ω` of a 2-morphism between normal-form objects. -/
def Om (μ : X) (s t : List (Letter I))
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    (pres D Sc).obj (ob D (-μ) (flipW t)) ⟶ (pres D Sc).obj (ob D (-μ) (flipW s)) :=
  eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ t)).symm ≫ SOp.unsop ((omega Sc).map f) ≫
    eqToHom (congrArg (pres D Sc).obj (chevMap_obj D μ s))

theorem Om_cl (μ : X) {s t : List (Letter I)} {L : List (LayerData I)} (h : SChain s L t) :
    Om D Sc μ s t (cl D Sc μ s t L) = omegaC D k L • cl D Sc (-μ) (flipW t) (flipW s) (omegaL L) := by
  rw [Om, omega_cl μ h]
  simp

theorem Om_add (μ : X) (s t : List (Letter I))
    (f g : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    Om D Sc μ s t (f + g) = Om D Sc μ s t f + Om D Sc μ s t g := by
  simp [Om, Functor.map_add]

theorem Om_smul (μ : X) (s t : List (Letter I)) (a : k)
    (f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)) :
    Om D Sc μ s t (a • f) = a • Om D Sc μ s t f := by
  simp [Om, Functor.map_smul]

theorem Om_id (μ : X) (s : List (Letter I)) :
    Om D Sc μ s s (𝟙 _) = 𝟙 _ := by
  rw [← cl_nil μ s, Om_cl μ (SChain.nil' s), omegaC_nil, one_smul]
  exact cl_nil (-μ) (flipW s)


/-! ## The second relation of (6.6) -/

variable (cs : CScalars Sc)

/-- `η'` (at `λ`) to the right of `Fᵢ 1_λ`. -/
def retaF (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i]) ⟶ (pres D Sc).obj (ob D μ [dn i, up i, dn i]) :=
  plcL D Sc μ [dn i] [] [] [up i, dn i] (etaP cs i (wt D μ []))

/-- `ε'` (at `λ - αᵢ`) on the two left strands of `Fᵢ Eᵢ Fᵢ 1_λ`. -/
def lepsF (i : I) (μ : X) :
    (pres D Sc).obj (ob D μ [dn i, up i, dn i]) ⟶ (pres D Sc).obj (ob D μ [dn i]) :=
  plcL D Sc μ [] [dn i] [dn i, up i] [] (epsP cs i (wt D μ [dn i]))

theorem c_neg_wt_dn (i : I) (μ : X) : cs.c (wt D (-μ) [dn i]) i = cs.c (-μ) i := by
  have := cs.shift (wt D (-μ) [dn i]) i i
  rw [Sc.t_self, one_mul] at this
  rw [← this]
  congr 1
  simp [wt, sh]

theorem h_wt_dn (i : I) (μ : X) : D.h i (wt D μ [dn i]) = D.h i μ - 2 := by
  simp [wt, sh, Datum.h, Datum.α, map_add, map_neg, D.cd.coroot_root_self]; ring

/-- The second relation of (6.6) at `-μ`, for `⟨hᵢ,μ⟩ = -1`. -/
theorem eq_6_6_b_m1 (i : I) (μ : X) (hh : D.h i μ = -1) :
    retaF cs i (-μ) ≫ lepsF cs i (-μ) = 𝟙 _ := by
  have hν : D.h i (wt D μ [up i]) = 1 := by rw [h_wt_up]; omega
  -- the first relation at `μ`, in normal form
  have E := eq_6_6_a cs i μ
  have e1 : leta cs i μ = (cs.c μ i : k) •
      cl D Sc μ [up i] [up i, dn i, up i] [([], Shape.dcup i 0, [up i])] := by
    rw [leta, etaP_of_pos cs (by omega), map_smul, plcL_cl, c_wt_up, hν]
    rfl
  have e2 : reps cs i μ = (↑(cs.c μ i)⁻¹ : k) •
      cl D Sc μ [up i, dn i, up i] [up i] [([up i], Shape.dcap i 0, [])] := by
    rw [reps, epsP_of_neg cs (show D.h i (wt D μ []) < 0 by simp only [wt_nil]; omega), map_smul,
      plcL_cl, show (-D.h i (wt D μ []) - 1).toNat = 0 by simp only [wt_nil]; omega]
    rfl
  rw [e1, e2, Linear.smul_comp, Linear.comp_smul, smul_smul, Units.mul_inv, one_smul,
    cl_comp (by simp [Shape.dom, Shape.cod]) (by simp [Shape.dom, Shape.cod]),
    ipar, hh, show ((-1 : ℤ) : ZMod 2) + 1 = 0 by push_cast; rfl, mul_zero, zsign_zero,
    one_smul, ← cl_nil μ [up i]] at E
  have E' := congrArg (Om D Sc μ [up i] [up i]) E
  rw [Om_cl μ (by simp [Shape.dom, Shape.cod]), Om_cl μ (SChain.nil' _)] at E'
  simp only [omegaL, omegaC_cons, omegaC_nil, chevL, chevC, dcupL, dcapL, List.map_cons,
    List.map_nil, whL, flipW_cons, flipW_nil, flipL_up, flipL_dn, List.nil_append, List.append_nil,
    List.singleton_append, Shape.parity, parsum_cons, parsum_nil, Nat.cast_zero, mul_zero,
    zero_mul, zsign_zero, mul_one, one_smul, cl_nil] at E'
  have h' : D.h i (wt D (-μ) []) = 1 := by simp only [wt_nil, coroot_neg]; omega
  have h'' : D.h i (wt D (-μ) [dn i]) = -1 := by rw [h_wt_dn]; simp only [coroot_neg]; omega
  rw [retaF, lepsF, etaP_of_pos cs (by omega), epsP_of_neg cs (by omega), map_smul, map_smul,
    plcL_cl, plcL_cl, Linear.smul_comp, Linear.comp_smul, smul_smul, c_neg_wt_dn,
    show cs.c (wt D (-μ) []) i = cs.c (-μ) i from rfl, Units.mul_inv, one_smul, h',
    show (-(-1 : ℤ) - 1).toNat = 0 by rfl, show ((1 : ℤ) - 1).toNat = 0 by rfl]
  sorry

end OddMath.SKM
