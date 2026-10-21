/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Alpha
import OddMath.SKM.ChevalleyGrading

/-!
# The downward map of BE2 (11.8)

The source is the super-opposite, not the ordinary opposite. Apply the upward
map at `-μ`, then the existing Chevalley involution, which negates the weight
and reverses the vertical direction with the super sign.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The contravariant downward functor; the rightmost weight is `μ`. -/
abbrev alphaContravariant (μ : X) : H D Sc ⥤ SOp k (SKM.pres D Sc).Presented :=
  alpha D Sc (-μ) ⋙ SKM.omega Sc

theorem alphaContravariant_mem (μ : X) {a b : H D Sc} {p : ZMod 2} {f : a ⟶ b}
    (hf : f ∈ Supercategory.parity (R := k) a b p) :
    (alphaContravariant D Sc μ).map f ∈ Supercategory.parity (R := k)
      ((alphaContravariant D Sc μ).obj a) ((alphaContravariant D Sc μ).obj b) p :=
  SKM.omega_mem (alpha_mem_parity D Sc (-μ) hf)

/-- The downward functor of (11.8), with its super-opposite source. -/
def alphaPrime (μ : X) : SOp k (H D Sc) ⥤ (SKM.pres D Sc).Presented :=
  SOp.mapFunctor (alphaContravariant D Sc μ) (alphaContravariant_mem D Sc μ) ⋙ SOp.unsopUnsop

@[simp] theorem alphaPrime_map (μ : X) {a b : SOp k (H D Sc)} (f : a ⟶ b) :
    (alphaPrime D Sc μ).map f =
      SOp.unsop ((SKM.omega Sc).map ((alpha D Sc (-μ)).map (SOp.unsop f))) := rfl

instance alphaPrime_additive (μ : X) : (alphaPrime D Sc μ).Additive where
  map_add := by intros; simp only [alphaPrime_map, SOp.unsop_add, Functor.map_add]
instance alphaPrime_linear (μ : X) : (alphaPrime D Sc μ).Linear k where
  map_smul := by intros; simp only [alphaPrime_map, SOp.unsop_smul, Functor.map_smul]

/-- The rightmost weight is `μ`, and all boundary strands point down. -/
@[simp] theorem alphaPrime_obj (μ : X) (s : List I) :
    (alphaPrime D Sc μ).obj (SOp.mk ((pres D Sc).obj (ob D s))) =
      (SKM.pres D Sc).obj (SKM.ob D μ (SKM.flipW (upWord s))) := by
  change ((SKM.omega Sc).obj ((alpha D Sc (-μ)).obj ((pres D Sc).obj (ob D s)))).unop = _
  rw [alpha_obj, SKM.omega_obj, neg_neg]

/-- The downward map preserves parity, including the super-opposite composition law. -/
theorem alphaPrime_mem_parity (μ : X) {a b : SOp k (H D Sc)} {p : ZMod 2} {f : a ⟶ b}
    (hf : f ∈ Supercategory.parity (R := k) a b p) :
    (alphaPrime D Sc μ).map f ∈ Supercategory.parity (R := k)
      ((alphaPrime D Sc μ).obj a) ((alphaPrime D Sc μ).obj b) p := by
  exact SOp.mem_parity_iff.mp (alphaContravariant_mem D Sc μ (SOp.mem_parity_iff.mp hf))

/-- Integer degrees are unchanged by the downward map. -/
theorem alphaPrime_mem_degree (sy : SKM.Symmetrizer D) (μ : X)
    {a b : Obj (sig D)} {d : ℤ}
    {f : (SOp.mk ((pres D Sc).obj a) : SOp k (H D Sc)) ⟶ SOp.mk ((pres D Sc).obj b)}
    (hf : SOp.unsop f ∈ (pres D Sc).homDeg (gdeg D sy) b a d) :
    (alphaPrime D Sc μ).map f ∈ (SKM.pres D Sc).homDeg (SKM.gdeg D sy)
      ((SKM.chevMap D).obj ((label D (-μ)).obj a))
      ((SKM.chevMap D).obj ((label D (-μ)).obj b)) d :=
  SKM.omega_mem_gdeg sy (alpha_mem_degree D Sc sy (-μ) hf)

end OddMath.QuiverHecke
