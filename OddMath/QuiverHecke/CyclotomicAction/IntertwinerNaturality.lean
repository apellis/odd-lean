/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerChain
import StringDiagrams.Super.Parity

/-!
# Moving-strand balance on arbitrary morphisms

Kang–Kashiwara–Oh, arXiv:1206.5933v2, (8.13), the balance input to
Proposition 8.4. `hom_comp_moveHom` extends the positioned-word identity to
all morphisms of the presented quiver Hecke supercategory. The parity
involution is applied to the entire morphism, so no homogeneity hypothesis
is imposed. This is an input to the balanced map Q and subsequently the
QP identity of Theorem 8.5, not a construction of Q itself.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory
open Categorification.TypeA
open SKM (zsign)

variable {I X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- The parity of the layers of a fitting positioned generator. -/
theorem parity_ld_of_fits (t : List I) (g : PG) (hg : g.pos + g.width ≤ t.length) :
    ((g.ld t).map fun x => x.2.1.parity D).sum = g.par D t := by
  obtain ⟨l, s, r, rfl, hgs, -, -⟩ := exists_split g 0 t (Nat.zero_le _) (by simpa using hg)
  simp only [zero_add] at hgs
  subst hgs
  rw [par_ofShape]
  cases s <;> simp [PG.ld, PG.ofShape, Shape.dom, Shape.parity]

/-- The recursive word parity agrees with the diagram's parity. -/
theorem parity_pl_of_fits (t : List I) (gs : List PG) (hf : Fits t.length gs) :
    ((pl t gs).map fun x => x.2.1.parity D).sum = chainParity D t gs := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    rw [pl_cons, List.map_append, List.sum_append, parity_ld_of_fits D t g (hf g (by simp)),
      chainParity_cons, ih]
    intro g' hg'
    simpa using hf g' (by simp [hg'])

/-- Positioned words are homogeneous for their recursive parity. -/
theorem cl_mem_chainParity {t t' : List I} (gs : List PG)
    (h : SChain t (pl t gs) t') (hf : Fits t.length gs) :
    cl D Sc t t' gs h ∈ Supercategory.parity (R := k) _ _ (chainParity D t gs) := by
  have hd := (pres D Sc).diag_isHomogeneous (isParityHomogeneous D Sc) (mkD D (pl t gs) h)
  have he : Diagram.degree (Presentation.parityDeg (sig D)) (mkD D (pl t gs) h) =
      chainParity D t gs := by
    rw [Diagram.degree, layers_mkD]
    have hp : ∀ g : Shape I, Presentation.parityDeg (sig D) g = g.parity D := by
      intro g
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (g.parity D) with h | h <;>
        simp [Presentation.parityDeg, sig, h]
    simpa only [layList, List.map_map, Function.comp_def, lay, hp] using
      parity_pl_of_fits D t gs hf
  rw [he] at hd
  exact hd

/-- KKO (8.13) on arbitrary, possibly inhomogeneous, Hom entries. The twist
is `f₀ + (-1)^(p(i)p(t)) f₁`. -/
theorem hom_comp_moveHom (i : I) {t t' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    ((pres D Sc).obj (ob D [i]) ◁ f) ≫ moveHom D Sc i [] t' =
      moveHom D Sc i [] t ≫
        (Supercategory.twist k (D.parity i * wordSumParity D t) f ▷
          (pres D Sc).obj (ob D [i])) := by
  have hf : f ∈ Submodule.span k {f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t') |
      ∃ l : List ℕ, l.Pairwise (· ≤ ·) ∧ (∀ x ∈ l, x < t.length) ∧
        ∃ w : Equiv.Perm (Fin t.length),
          ∃ h, cl D Sc t t' (l.map PG.dot ++ cw (canWord t.length w)) h = f} := by
    rw [span_normalForms]; trivial
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, -, hl, w, h, rfl⟩ := hf
    have hfit := fits_append (fits_dots hl) (fits_cw (validWord_canWord t.length w))
    rw [Supercategory.twist_of_mem _ (cl_mem_chainParity D Sc _ h hfit),
      (MonoidalSupercategory.smul_whiskerRight (R := k)), Linear.comp_smul,
      cl_whiskerLeft, cl_whiskerRight D Sc _ h [i] hfit]
    have hs : ∀ p : ZMod 2, Supercategory.sign k p = zsign k p := by
      intro p
      rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) p with rfl | rfl <;>
        simp [Supercategory.sign, zsign]
    simpa only [List.singleton_append, List.length_singleton, hs, mul_comm] using
      (cl_comp_moveHom D Sc i _ h hfit).1
  | zero => simp [MonoidalSupercategory.whiskerLeft_zero (R := k),
      MonoidalSupercategory.zero_whiskerRight (R := k)]
  | add f g _ _ hf hg =>
    simp only [map_add, (MonoidalSupercategory.whiskerLeft_add (R := k)),
      (MonoidalSupercategory.add_whiskerRight (R := k)), Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | smul r f _ hf =>
    simp only [map_smul, (MonoidalSupercategory.whiskerLeft_smul (R := k)),
      (MonoidalSupercategory.smul_whiskerRight (R := k)), Linear.smul_comp,
      Linear.comp_smul, hf]

end OddMath.QuiverHecke
