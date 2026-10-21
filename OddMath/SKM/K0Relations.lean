/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.HomComponents
import OddMath.SKM.RelationsNF
import StringDiagrams.Super.K0Ring

/-!
# Weight and mixed relations in the SKM Grothendieck group

Brundan–Ellis, arXiv:1701.04133v2, Lemma 11.6 and the existence step of
Theorem 11.7. We use the existing additive idempotent completion `SKM.UDot`.
Presented words run from the left region to the right region; therefore the
paper's algebra multiplication is the opposite of `StringDiagrams.K₀Ring`.
The parity shift in the distinct-colour relation is essential for odd colours.
-/

noncomputable section
namespace OddMath.SKM.K0Relations

open CategoryTheory StringDiagrams Presentation
open CategoryTheory.Idempotents CategoryTheory.Limits
open Supercategory GradedSupercategory

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] (Sc : Scalars D k) (sy : Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- A weight of the existing completed SKM 2-category. -/
abbrev weight (μ : X) : UDot D Sc sy hc := GSKAR.mkObj k (UGr D Sc sy hc) ⟨μ⟩

/-- The split Grothendieck ring, with the multiplication order of BE2. -/
abbrev Grothendieck := (K₀Ring (UDot D Sc sy hc))ᵐᵒᵖ

/-- A word with its two region labels made explicit. -/
def word (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ) :
    (show UGr D Sc sy hc from ⟨μ⟩) ⟶ (show UGr D Sc sy hc from ⟨ν⟩) :=
  ⟨ob D ν s, hs, ok_wd D ν s, ob_endR D ν s⟩

/-- A shifted word in the even degree-zero envelope. -/
abbrev shifted (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) := shiftedUnderlying n a (word Sc sy hc μ ν s hs)

/-- Inclusion into the additive idempotent completion of a hom category. -/
abbrev inclusion (μ ν : X) :=
  Mat_.embedding ((show UUnderline D Sc sy hc from ⟨⟨⟨⟨⟨μ⟩⟩⟩⟩⟩) ⟶
    (show UUnderline D Sc sy hc from ⟨⟨⟨⟨⟨ν⟩⟩⟩⟩⟩)) ⋙ toKaroubi _

/-- The shifted word as a 1-morphism of `UDot`. -/
abbrev completed (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) : weight Sc sy hc μ ⟶ weight Sc sy hc ν :=
  (inclusion Sc sy hc μ ν).obj (shifted Sc sy hc μ ν s hs n a)

/-- Its class, in the BE2 multiplication convention. -/
def cls (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) : Grothendieck Sc sy hc :=
  MulOpposite.op (K₀Ring.mk (completed Sc sy hc μ ν s hs n a))

/-- The weight idempotent. -/
def one (μ : X) : Grothendieck Sc sy hc :=
  MulOpposite.op (K₀Ring.one (weight Sc sy hc μ))

open Classical in
/-- Orthogonality and idempotence of weight classes, used in Theorem 11.7. -/
theorem one_mul_one (μ ν : X) :
    one Sc sy hc μ * one Sc sy hc ν = if μ = ν then one Sc sy hc μ else 0 := by
  classical
  by_cases h : μ = ν
  · subst ν
    simp only [ite_eq_left rfl, one, ← MulOpposite.op_mul, K₀Ring.one_mul_one_self]
  · rw [ite_eq_right h]
    change MulOpposite.op (K₀Ring.one (weight Sc sy hc ν) *
      K₀Ring.one (weight Sc sy hc μ)) = MulOpposite.op 0
    congr 1
    apply K₀Ring.one_mul_one_of_ne
    intro e
    exact h (by cases e; rfl)

/-- Left weight support, in the source's multiplication order. -/
theorem one_mul_cls (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    one Sc sy hc μ * cls Sc sy hc μ ν s hs n a = cls Sc sy hc μ ν s hs n a := by
  change MulOpposite.op (_ * _) = MulOpposite.op _
  congr 1
  exact K₀Ring.of_mul_one _

/-- Right weight support, in the source's multiplication order. -/
theorem cls_mul_one (μ ν : X) (s : List (Letter I)) (hs : wt D ν s = μ)
    (n : ℤ) (a : ZMod 2) :
    cls Sc sy hc μ ν s hs n a * one Sc sy hc ν = cls Sc sy hc μ ν s hs n a := by
  change MulOpposite.op (_ * _) = MulOpposite.op _
  congr 1
  exact K₀Ring.one_mul_of _

/-- Lift a homogeneous normal-form morphism to the shifted underlying category. -/
def lift {μ ν : X} {s t : List (Letter I)}
    {hs : wt D ν s = μ} {ht : wt D ν t = μ} {m n : ℤ} {a b : ZMod 2}
    (L : List (LayerData I)) (hL : SChain s L t)
    (hd : gsum D sy ν L = m - n)
    (hp : (L.map fun x => x.2.1.parity D).sum = a + b) :
    shifted Sc sy hc μ ν s hs m a ⟶ shifted Sc sy hc μ ν t ht n b :=
  ⟨⟨cl D Sc ν s t L, by
    change cl D Sc ν s t L ∈ (pres D Sc).homDeg (gdeg D sy) _ _ (0 + (m - n))
    rw [zero_add, cl_of hL]
    exact diag_mem_homDeg' ((degree_gdeg_mkD D sy ν L hL).trans hd)⟩, by
    change cl D Sc ν s t L ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ (0 + (a + b))
    rw [zero_add, cl_of hL]
    exact diag_mem_homDeg' ((degree_parity_mkD D ν L hL).trans hp)⟩

/-- The degree-zero, even crossing isomorphism after the required parity shift.
This is inversion relation (1.12) in the actual underlying envelope. -/
def mixedIso (i j : I) (ν μ : X)
    (hs : wt D ν [up i, dn j] = μ) (ht : wt D ν [dn j, up i] = μ) (hij : i ≠ j) :
    shifted Sc sy hc μ ν [up i, dn j] hs 0 0 ≅
      shifted Sc sy hc μ ν [dn j, up i] ht 0 (D.parity i * D.parity j) where
  hom := lift Sc sy hc (sigmaL j i) (sChain_sigmaL j i)
    (by simp) (by simp [mul_comm])
  inv := lift Sc sy hc (lcrossL j i) (sChain_lcrossL j i)
    (by simp) (by simp [mul_comm])
  hom_inv_id := by
    apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 𝟙 _
    rw [cl_comp (sChain_sigmaL j i) (sChain_lcrossL j i), cl_invNe₁ Sc j i ν hij.symm, cl_nil]
  inv_hom_id := by
    apply Subtype.ext; apply Subtype.ext
    change cl D Sc ν _ _ _ ≫ cl D Sc ν _ _ _ = 𝟙 _
    rw [cl_comp (sChain_lcrossL j i) (sChain_sigmaL j i), cl_invNe₂ Sc j i ν hij.symm, cl_nil]

/-- Lemma 11.6, the distinct-colour mixed relation. No parity factor is discarded. -/
theorem mixed_ne (i j : I) (ν μ : X)
    (hs : wt D ν [up i, dn j] = μ) (ht : wt D ν [dn j, up i] = μ) (hij : i ≠ j) :
    cls Sc sy hc μ ν [up i, dn j] hs 0 0 =
      cls Sc sy hc μ ν [dn j, up i] ht 0 (D.parity i * D.parity j) := by
  apply congrArg MulOpposite.op
  exact K₀Ring.mk_eq_mk_of_iso
    ((inclusion Sc sy hc μ ν).mapIso (mixedIso Sc sy hc i j ν μ hs ht hij))

end OddMath.SKM.K0Relations
