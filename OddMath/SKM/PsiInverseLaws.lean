import OddMath.SKM.PsiInverseFunctor

/-!
# Comparison laws for the two ψ composites

This module proves the comparison-data part of the inverse assertion for ψ in
Brundan–Ellis, *Super Kac–Moody 2-categories*. Both composites of `psiExtension`
and `psiInverseFunctor` have identity composition and unit comparisons, after
the established equalities on 1-morphisms. In particular both are strict, and
preserve arbitrary left and right contexts up to those endpoint equalities.

The calculation retains all integer and parity shifts. The forward composition
comparison is the equality morphism multiplied by `sign (a * (b + P(g)))`;
the inverse-direction comparison is multiplied by `sign (b * (a + P(f)))`.
The endpoint correction in `psiInverseFunctor` makes these factors cancel in
both composite orders.

These results supply the comparison and context-preservation inputs for the
literal inverse-functor laws. They do not assert a roundtrip on arbitrary
quotient 2-morphisms, or equality of either composite with the identity functor.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct TwoSupercategory QPiSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

variable (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)

/-- The forward/inverse composite unit comparison is exactly its endpoint equality iso. -/
theorem psiForwardInverse_mapId (a : Uqπ D Sc sy hc) :
    ((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).mapId a =
      eqToIso (psiInverseFunctor_map_forward t ht cs (𝟙 a)).symm := by
  apply Iso.ext
  simp only [TwoSuperfunctor.comp_mapId, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom]
  rw [psiInverseFunctor_mapId_hom, psiExtension_mapId_eq, psiExtension_mapId_eq]
  change 𝟙 _ ≫ (psiInverseFunctor t ht cs).map₂ (𝟙 _) = _
  rw [TwoSuperfunctor.map₂_id, Category.id_comp]
  rfl

section Shifts
variable {a b : UGr D Sc sy hc}
local instance : QPiSupercategory k
    (psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :=
  QPiTwoSupercategory.homQPiLeft _ _

private theorem qpi_hom_mem (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (psiQPiIso m p f).hom ∈ parity (R := k) _ _ p := by
  simpa only [psiQPiIso, psiPiIso, psiQIso, Iso.trans_hom, add_zero] using
    comp_mem (Envelope.ζPow_hom_mem (R := k) p (qPow k m f)) (σPow_hom_mem (R := k) m f)

private theorem qpi_hom (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQPiIso m p f).hom) =
      eqToHom (congrArg (pres D Sc).obj
        ((psiPiIso_obj p (qPow k m f)).trans (psiQPow_obj m f)).symm) := by
  unfold psiQPiIso
  erw [Iso.trans_hom, SOp.comp_of_mem (SOp.mem_parity_iff.mp
      (Envelope.ζPow_hom_mem (R := k) p (qPow k m f)))
    (SOp.mem_parity_iff.mp (σPow_hom_mem (R := k) m f))]
  change sign k (p * 0) •
    (QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).hom) ≫
      QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso p (qPow k m f)).hom)) = _
  rw [mul_zero, sign_zero, one_smul, psiQIso_hom_eq, psiPiIso_hom_eq]
  exact eqToHom_trans (C := (pres D Sc).Presented)
    (congrArg (pres D Sc).obj (psiQPow_obj m f).symm)
    (congrArg (pres D Sc).obj (psiPiIso_obj p (qPow k m f)).symm)

private theorem qpi_inv_mem (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (psiQPiIso m p f).inv ∈ parity (R := k) _ _ p := by
  simpa only [psiQPiIso, psiPiIso, psiQIso, Iso.trans_inv, zero_add] using
    comp_mem (σPow_inv_mem (R := k) m f) (Envelope.ζPow_inv_mem (R := k) p (qPow k m f))

private theorem qpi_inv (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQPiIso m p f).inv) =
      sign k p • eqToHom (congrArg (pres D Sc).obj
        ((psiPiIso_obj p (qPow k m f)).trans (psiQPow_obj m f))) := by
  unfold psiQPiIso
  erw [Iso.trans_inv, SOp.comp_of_mem (SOp.mem_parity_iff.mp
      (σPow_inv_mem (R := k) m f))
    (SOp.mem_parity_iff.mp (Envelope.ζPow_inv_mem (R := k) p (qPow k m f)))]
  change sign k (0 * p) •
    (QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso p (qPow k m f)).inv) ≫
      QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).inv)) = _
  rw [zero_mul, sign_zero, one_smul, psiPiIso_inv_eq, psiQIso_inv_eq]
  erw [Linear.smul_comp]
  exact congrArg (sign k p • ·) (eqToHom_trans (C := (pres D Sc).Presented)
    (congrArg (pres D Sc).obj (psiPiIso_obj p (qPow k m f)))
    (congrArg (pres D Sc).obj (psiQPow_obj m f)))

private theorem qpi_word (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (Envelope.piPow (B := psiObj a ⟶ psiObj b) k p
      (qPow (C := psiObj a ⟶ psiObj b) k m f))).obj.obj = (SOp.unop f).obj.obj :=
  Presentation.Bicat.Hom.ext ((psiPiIso_obj p (qPow k m f)).trans (psiQPow_obj m f))

private theorem qpi_hom_bicat (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQPiIso m p f).hom) = eqToHom (qpi_word m p f).symm := by
  rw [qpi_hom]
  rfl

private theorem qpi_inv_bicat (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQPiIso m p f).inv) = sign k p • eqToHom (qpi_word m p f) := by
  rw [qpi_inv]
  rfl

private theorem qpi_hom_even (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQPiIso m p f).hom) ∈ parity (R := k) _ _ 0 := by
  rw [qpi_hom]
  exact eqToHom_mem (R := k) (C := a ⟶ b)
    (Presentation.Bicat.Hom.ext
      ((psiPiIso_obj p (qPow k m f)).trans (psiQPow_obj m f))).symm

end Shifts

private theorem underlying_comp {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f g h : a ⟶ b} {x : f ⟶ g} {y : g ⟶ h} {p q : ZMod 2}
    (hx : x ∈ parity (R := k) _ _ p) (hy : y ∈ parity (R := k) _ _ q) :
    QPiTwoEnvelope.toHom (SOp.unsop (x ≫ y)) = sign k (p * q) •
      (QPiTwoEnvelope.toHom (SOp.unsop y) ≫ QPiTwoEnvelope.toHom (SOp.unsop x)) := by
  rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp hx) (SOp.mem_parity_iff.mp hy)]
  rfl

private theorem underlying_right {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} {x : f ⟶ g} {p : ZMod 2}
    (hx : x ∈ parity (R := k) _ _ p) (h : b ⟶ c) :
    QPiTwoEnvelope.toHom (SOp.unsop (x ▷ h)) =
      sign k ((SOp.unop h).par * p) •
        (QPiTwoEnvelope.toHom (SOp.unsop x) ▷ (SOp.unop h).obj.obj) := by
  change QEnvelope.toHom (Envelope.toHom
    (twist k (SOp.unop h).par (SOp.unsop x)) ▷ (SOp.unop h).obj) = _
  rw [twist_of_mem _ (show SOp.unsop x ∈ parity (R := k) _ _ p from hx)]
  change (sign k ((SOp.unop h).par * p) • QPiTwoEnvelope.toHom (SOp.unsop x)) ▷
    (SOp.unop h).obj.obj = _
  exact smul_whiskerRight (R := k) _ _ _

private theorem underlying_left_even {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) {g h : b ⟶ c} {x : g ⟶ h}
    (hx : QPiTwoEnvelope.toHom (SOp.unsop x) ∈ parity (R := k) _ _ 0) :
    QPiTwoEnvelope.toHom (SOp.unsop (f ◁ x)) =
      (SOp.unop f).obj.obj ◁ QPiTwoEnvelope.toHom (SOp.unsop x) := by
  change QEnvelope.toHom ((SOp.unop f).obj ◁
    twist k (SOp.unop f).par (Envelope.toHom (SOp.unsop x))) = _
  rw [twist_of_mem _ (show Envelope.toHom (SOp.unsop x) ∈ parity (R := k) _ _ 0 from hx)]
  rw [mul_zero, sign_zero, one_smul]
  rfl

private theorem underlying_eq {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (e : f = g) :
    QPiTwoEnvelope.toHom (SOp.unsop (eqToHom e)) =
      eqToHom (congrArg (fun z => (SOp.unop z).obj.obj) e.symm) := by
  cases e
  rfl

local instance : ∀ a b : TwoSOp k (Uqπ D Sc sy hc), QPiSupercategory k (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

private theorem qpi_right {a b c : UGr D Sc sy hc}
    (m : ℤ) (p : ZMod 2) (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b)
    (g : psiObj b ⟶ psiObj c) :
    QPiTwoEnvelope.toHom (SOp.unsop ((psiQPiIso m p f).hom ▷ g)) =
      sign k ((SOp.unop g).par * p) • eqToHom
        (congrArg (· ≫ (SOp.unop g).obj.obj) (qpi_word m p f).symm) := by
  rw [underlying_right (qpi_hom_mem m p f), qpi_hom_bicat]
  rw [eqToHom_whiskerRight k]

private theorem qpi_left {a b c : UGr D Sc sy hc}
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b)
    (m : ℤ) (p : ZMod 2) (g : psiObj b ⟶ psiObj c) :
    QPiTwoEnvelope.toHom (SOp.unsop (f ◁ (psiQPiIso m p g).hom)) =
      eqToHom (congrArg ((SOp.unop f).obj.obj ≫ ·) (qpi_word m p g).symm) := by
  rw [underlying_left_even f (qpi_hom_even m p g), qpi_hom_bicat]
  rw [whiskerLeft_eqToHom k]

private theorem underlying_four {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f₀ f₁ f₂ f₃ f₄ : a ⟶ b}
    {x : f₀ ⟶ f₁} {y : f₁ ⟶ f₂} {z : f₂ ⟶ f₃} {v : f₃ ⟶ f₄}
    {p q r : ZMod 2} (hx : x ∈ parity (R := k) _ _ p)
    (hy : y ∈ parity (R := k) _ _ q) (hz : z ∈ parity (R := k) _ _ 0)
    (hv : v ∈ parity (R := k) _ _ r) :
    QPiTwoEnvelope.toHom (SOp.unsop (x ≫ y ≫ z ≫ v)) =
      sign k (p * (q + r) + q * r) •
        (QPiTwoEnvelope.toHom (SOp.unsop v) ≫ QPiTwoEnvelope.toHom (SOp.unsop z) ≫
          QPiTwoEnvelope.toHom (SOp.unsop y) ≫ QPiTwoEnvelope.toHom (SOp.unsop x)) := by
  rw [underlying_comp hx (comp_mem hy (comp_mem hz hv)),
    underlying_comp hy (comp_mem hz hv), underlying_comp hz hv]
  simp only [zero_add, zero_mul, sign_zero, one_smul,
    Linear.smul_comp, smul_smul, ← sign_add, Category.assoc]

private theorem qpi_par {a b : UGr D Sc sy hc} (g : a ⟶ b) (n : ℤ) (q : ZMod 2) :
    (SOp.unop (Envelope.piPow (B := psiObj a ⟶ psiObj b) k q
      (qPow (C := psiObj a ⟶ psiObj b) k n (psiMap g)))).par = q + psiParity g := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa only [Envelope.piPow_zero, zero_add, psiMap] using psiQPow_par n (psiMap g)
  · change (SOp.unop (qPow (C := psiObj a ⟶ psiObj b) k n (psiMap g))).par + 1 = _
    rw [psiQPow_par]
    exact add_comm _ _

private theorem qpi_comparison {a b c : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (m n : ℤ) (p q : ZMod 2) :
    QPiTwoEnvelope.toHom (SOp.unsop
      ((psiQPiIso m p (psiMap f)).hom ▷ Envelope.piPow k q (qPow k n (psiMap g)) ≫
        psiMap f ◁ (psiQPiIso n q (psiMap g)).hom ≫
        eqToHom (psiMap_comp f g).symm ≫
        (psiQPiIso (m + n) (p + q) (psiMap (f ≫ g))).inv)) =
      sign k (p * (q + (p + q)) + q * (p + q) + (p + q) + (q + psiParity g) * p) •
        eqToHom ((qpi_word (m + n) (p + q) (psiMap (f ≫ g))).trans
          (congrArg₂ (fun x y => x ≫ y) (qpi_word m p (psiMap f)).symm
            (qpi_word n q (psiMap g)).symm)) := by
  rw [underlying_four
    (whiskerRight_mem _ (qpi_hom_mem m p (psiMap f)))
    (whiskerLeft_mem _ (qpi_hom_mem n q (psiMap g)))
    (eqToHom_mem (psiMap_comp f g).symm)
    (qpi_inv_mem (m + n) (p + q) (psiMap (f ≫ g)))]
  rw [qpi_right m p (psiMap f), qpi_left (psiMap f) n q (psiMap g),
    qpi_inv_bicat, underlying_eq, qpi_par]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, ← sign_add,
    eqToHom_trans]
  congr 2
  abel

private theorem qpi_comparison_signed {a b c : UGr D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) (m n : ℤ) (p q : ZMod 2) :
    sign k (p * q) • QPiTwoEnvelope.toHom (SOp.unsop
      ((psiQPiIso m p (psiMap f)).hom ▷ Envelope.piPow k q (qPow k n (psiMap g)) ≫
        psiMap f ◁ (psiQPiIso n q (psiMap g)).hom ≫
        eqToHom (psiMap_comp f g).symm ≫
        (psiQPiIso (m + n) (p + q) (psiMap (f ≫ g))).inv)) =
      sign k (p * (q + psiParity g)) •
        eqToHom ((qpi_word (m + n) (p + q) (psiMap (f ≫ g))).trans
          (congrArg₂ (fun x y => x ≫ y) (qpi_word m p (psiMap f)).symm
            (qpi_word n q (psiMap g)).symm)) := by
  rw [qpi_comparison, smul_smul, ← sign_add]
  have he (p q r : ZMod 2) : p * q +
      (p * (q + (p + q)) + q * (p + q) + (p + q) + (q + r) * p) = p * (q + r) := by
    revert p q r
    decide
  rw [he]

/-- The extended ψ preserves composition of 1-morphisms as an equality of shifted words. -/
theorem psiExtension_map_comp_eq {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    (psiExtension t ht cs).map (f ≫ g) =
      (psiExtension t ht cs).map f ≫ (psiExtension t ht cs).map g := by
  apply SOp.ext
  rw [psiExtension_map_eq_psiShift]
  change psiShift (f ≫ g) =
    SOp.unop ((psiExtension t ht cs).map f) ≫ SOp.unop ((psiExtension t ht cs).map g)
  rw [psiExtension_map_eq_psiShift, psiExtension_map_eq_psiShift, psiShift_comp]

/-- The complete forward composition comparison is a signed equality morphism. -/
theorem psiExtension_mapComp_scalar {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((psiExtension t ht cs).mapComp f g).hom =
      sign k (f.par * (g.par + psiParity g.obj.obj)) •
        eqToHom (psiExtension_map_comp_eq t ht cs f g).symm := by
  apply SOp.hom_ext
  change QPiTwoEnvelope.toHom (SOp.unsop ((psiExtension t ht cs).mapComp f g).hom) = _
  rw [psiExtension_mapComp_hom_eq]
  change sign k (f.par * g.par) • QPiTwoEnvelope.toHom (SOp.unsop
    ((psiQPiIso f.obj.shift f.par (psiMap f.obj.obj)).hom ▷ (psiExtension t ht cs).map g ≫
      psiMap f.obj.obj ◁ (psiQPiIso g.obj.shift g.par (psiMap g.obj.obj)).hom ≫
      eqToHom (psiMap_comp f.obj.obj g.obj.obj).symm ≫
      (psiQPiIso (f.obj.shift + g.obj.shift) (f.par + g.par)
        (psiMap (f.obj.obj ≫ g.obj.obj))).inv)) = _
  erw [qpi_comparison_signed f.obj.obj g.obj.obj f.obj.shift g.obj.shift f.par g.par]
  change _ = sign k (f.par * (g.par + psiParity g.obj.obj)) •
    QPiTwoEnvelope.toHom (SOp.unsop (eqToHom (psiExtension_map_comp_eq t ht cs f g).symm))
  rw [underlying_eq]

private theorem signed_inv {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {a b : C} (e : a ≅ b) (h : a = b) (p : ZMod 2)
    (he : e.hom = sign k p • eqToHom h) : e.inv = sign k p • eqToHom h.symm := by
  apply (cancel_epi e.hom).mp
  rw [Iso.hom_inv_id, he, Linear.smul_comp, Linear.comp_smul,
    smul_smul, sign_mul_self, one_smul, eqToHom_trans]
  rfl

/-- The inverse of the forward comparison has the same scalar and reversed endpoint equality. -/
theorem psiExtension_mapComp_inv_scalar {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((psiExtension t ht cs).mapComp f g).inv =
      sign k (f.par * (g.par + psiParity g.obj.obj)) •
        eqToHom (psiExtension_map_comp_eq t ht cs f g) :=
  signed_inv _ _ _ (psiExtension_mapComp_scalar t ht cs f g)

/-- The inverse-direction ψ preserves composition of shifted 1-morphisms. -/
theorem psiInverseFunctor_map_comp_eq {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    (psiInverseFunctor t ht cs).map (f ≫ g) =
      (psiInverseFunctor t ht cs).map f ≫ (psiInverseFunctor t ht cs).map g := by
  rw [psiInverseFunctor_map, psiInverseFunctor_map, psiInverseFunctor_map]
  exact psiShift_comp _ _

private theorem unsop_eq {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (h : f = g) :
    SOp.unsop (eqToHom h) = eqToHom (congrArg SOp.unop h.symm) := by
  cases h
  rfl

private theorem inverse_sign_comparison {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (h : f = g) (x y p q : ZMod 2) :
    sign k (x * q + y * p) • SOp.unsop (sign k (x * (y + q)) • eqToHom h) =
      sign k (y * (x + p)) • eqToHom (congrArg SOp.unop h.symm) := by
  rw [SOp.unsop_smul, unsop_eq, smul_smul, ← sign_add]
  have he (a b p q : ZMod 2) : a * q + b * p + a * (b + q) = b * (a + p) := by
    revert a b p q
    decide
  rw [he]

/-- The complete inverse-direction composition comparison, including the endpoint correction. -/
theorem psiInverseFunctor_mapComp_scalar {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiInverseFunctor t ht cs).mapComp f g).hom =
      sign k ((SOp.unop g).par * ((SOp.unop f).par + psiParity (SOp.unop f).obj.obj)) •
        eqToHom (psiInverseFunctor_map_comp_eq t ht cs f g).symm := by
  rw [psiInverseFunctor_mapComp_hom]
  change sign k (psiInverseSign (SOp.unop f) + psiInverseSign (SOp.unop g) +
      psiInverseSign (SOp.unop f ≫ SOp.unop g)) • _ = _
  rw [psiInverseSign_comp, psiExtension_mapComp_inv_scalar]
  exact inverse_sign_comparison _ _ _ _ _

/-- The inverse-direction comparison inverse has the same scalar and reversed endpoint equality. -/
theorem psiInverseFunctor_mapComp_inv_scalar {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiInverseFunctor t ht cs).mapComp f g).inv =
      sign k ((SOp.unop g).par * ((SOp.unop f).par + psiParity (SOp.unop f).obj.obj)) •
        eqToHom (psiInverseFunctor_map_comp_eq t ht cs f g) :=
  signed_inv _ _ _ (psiInverseFunctor_mapComp_scalar t ht cs f g)

private theorem map₂_eq {B C : Type*} [BicategoryStruct B] [BicategoryStruct C]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [∀ a b : C, Supercategory k (a ⟶ b)]
    (F : TwoSuperfunctor k B C) {a b : B} {f g : a ⟶ b} (e : f = g) :
    F.map₂ (eqToHom e) = eqToHom (congrArg F.map e) := by
  cases e
  exact F.map₂_id _

private theorem same_signed_map_comp {B C : Type*} [BicategoryStruct B] [BicategoryStruct C]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [∀ a b : C, Supercategory k (a ⟶ b)]
    (F : TwoSuperfunctor k B C) {a b : B} {f g : a ⟶ b}
    {h : F.obj a ⟶ F.obj b} (e : h = F.map f) (d : f = g) (p : ZMod 2) :
    (sign k p • eqToHom e) ≫ F.map₂ (sign k p • eqToHom d) =
      eqToHom (e.trans (congrArg F.map d)) := by
  rw [F.map₂_smul, map₂_eq, Linear.smul_comp, Linear.comp_smul,
    smul_smul, sign_mul_self, one_smul, eqToHom_trans]

private theorem forward_comparison_sign {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    (SOp.unop ((psiExtension t ht cs).map g)).par *
      ((SOp.unop ((psiExtension t ht cs).map f)).par +
        psiParity (SOp.unop ((psiExtension t ht cs).map f)).obj.obj) =
      f.par * (g.par + psiParity g.obj.obj) := by
  rw [psiExtension_map_eq_psiShift, psiExtension_map_eq_psiShift]
  change (g.par + psiParity g.obj.obj) *
    ((f.par + psiParity f.obj.obj) + psiParity f.obj.obj) = _
  simp only [add_assoc, zmod2_add_self, add_zero, mul_comm]

/-- The entire forward/inverse composition comparison is its endpoint equality iso. -/
theorem psiForwardInverse_mapComp {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).mapComp f g =
      eqToIso ((congrArg₂ (fun x y => x ≫ y)
        (psiInverseFunctor_map_forward t ht cs f) (psiInverseFunctor_map_forward t ht cs g)).trans
        (psiInverseFunctor_map_forward t ht cs (f ≫ g)).symm) := by
  apply Iso.ext
  change ((psiInverseFunctor t ht cs).mapComp ((psiExtension t ht cs).map f)
    ((psiExtension t ht cs).map g)).hom ≫
      (psiInverseFunctor t ht cs).map₂ ((psiExtension t ht cs).mapComp f g).hom = _
  rw [psiInverseFunctor_mapComp_scalar, psiExtension_mapComp_scalar,
    forward_comparison_sign]
  exact same_signed_map_comp _ _ _ _

private theorem inverse_comparison_sign {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiInverseFunctor t ht cs).map f).par *
      (((psiInverseFunctor t ht cs).map g).par +
        psiParity ((psiInverseFunctor t ht cs).map g).obj.obj) =
      (SOp.unop g).par * ((SOp.unop f).par + psiParity (SOp.unop f).obj.obj) := by
  rw [psiInverseFunctor_map, psiInverseFunctor_map]
  change ((SOp.unop f).par + psiParity (SOp.unop f).obj.obj) *
    (((SOp.unop g).par + psiParity (SOp.unop g).obj.obj) + psiParity (SOp.unop g).obj.obj) = _
  simp only [add_assoc, zmod2_add_self, add_zero, mul_comm]

/-- The entire inverse/forward composition comparison is its endpoint equality iso. -/
theorem psiInverseForward_mapComp {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).mapComp f g =
      eqToIso ((congrArg₂ (fun x y => x ≫ y)
        (psiInverseFunctor_map_reverse t ht cs f) (psiInverseFunctor_map_reverse t ht cs g)).trans
        (psiInverseFunctor_map_reverse t ht cs (f ≫ g)).symm) := by
  apply Iso.ext
  change ((psiExtension t ht cs).mapComp ((psiInverseFunctor t ht cs).map f)
    ((psiInverseFunctor t ht cs).map g)).hom ≫
      (psiExtension t ht cs).map₂ ((psiInverseFunctor t ht cs).mapComp f g).hom = _
  rw [psiExtension_mapComp_scalar, psiInverseFunctor_mapComp_scalar,
    inverse_comparison_sign]
  exact same_signed_map_comp _ _ _ _

/-- The inverse/forward composite unit comparison is exactly its endpoint equality iso. -/
theorem psiInverseForward_mapId (a : TwoSOp k (Uqπ D Sc sy hc)) :
    ((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).mapId a =
      eqToIso (psiInverseFunctor_map_reverse t ht cs (𝟙 a)).symm := by
  apply Iso.ext
  simp only [TwoSuperfunctor.comp_mapId, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom]
  rw [psiInverseFunctor_mapId_hom, psiExtension_mapId_eq, psiExtension_mapId_eq]
  change 𝟙 _ ≫ (psiExtension t ht cs).map₂ (𝟙 _) = _
  rw [TwoSuperfunctor.map₂_id, Category.id_comp]
  rfl

/-- The forward/inverse composite has identity comparison data at every Q/Π label.
This does not assert that its map on arbitrary 2-morphisms is the identity. -/
theorem psiForwardInverse_isStrict :
    ((psiExtension (sy := sy) (hc := hc) t ht cs).comp (psiInverseFunctor t ht cs)).IsStrict where
  map_comp f g := (psiInverseFunctor_map_forward t ht cs (f ≫ g)).trans
    (congrArg₂ (fun x y => x ≫ y) (psiInverseFunctor_map_forward t ht cs f)
      (psiInverseFunctor_map_forward t ht cs g)).symm
  map_id a := psiInverseFunctor_map_forward t ht cs (𝟙 a)
  mapComp_eq f g := psiForwardInverse_mapComp t ht cs f g
  mapId_eq a := psiForwardInverse_mapId t ht cs a

/-- The inverse/forward composite has identity comparison data at every Q/Π label.
The arbitrary 2-morphism roundtrip is a separate assertion. -/
theorem psiInverseForward_isStrict :
    ((psiInverseFunctor (sy := sy) (hc := hc) t ht cs).comp (psiExtension t ht cs)).IsStrict where
  map_comp f g := (psiInverseFunctor_map_reverse t ht cs (f ≫ g)).trans
    (congrArg₂ (fun x y => x ≫ y) (psiInverseFunctor_map_reverse t ht cs f)
      (psiInverseFunctor_map_reverse t ht cs g)).symm
  map_id a := psiInverseFunctor_map_reverse t ht cs (𝟙 a)
  mapComp_eq f g := psiInverseForward_mapComp t ht cs f g
  mapId_eq a := psiInverseForward_mapId t ht cs a

section Whiskering
variable {B C : Type*} [BicategoryStruct B] [BicategoryStruct C]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [∀ a b : C, Supercategory k (a ⟶ b)]

private theorem strict_left (F : TwoSuperfunctor k B C) (hF : F.IsStrict)
    {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    HEq (F.map₂ (f ◁ x)) (F.map f ◁ F.map₂ x) := by
  apply (conj_eqToHom_iff_heq _ _ (hF.map_comp f g) (hF.map_comp f h)).1
  have H := congrArg (eqToHom (hF.map_comp f g) ≫ ·) (F.mapComp_naturality_right f x)
  rw [hF.mapComp_eq, hF.mapComp_eq] at H
  simpa only [eqToIso.hom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Category.assoc] using H.symm

private theorem strict_right (F : TwoSuperfunctor k B C) (hF : F.IsStrict)
    {a b c : B} {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    HEq (F.map₂ (x ▷ h)) (F.map₂ x ▷ F.map h) := by
  apply (conj_eqToHom_iff_heq _ _ (hF.map_comp f h) (hF.map_comp g h)).1
  have H := congrArg (eqToHom (hF.map_comp f h) ≫ ·) (F.mapComp_naturality_left x h)
  rw [hF.mapComp_eq, hF.mapComp_eq] at H
  simpa only [eqToIso.hom, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, Category.assoc] using H.symm
end Whiskering

/-- Left contexts are preserved by the composite on arbitrary, not necessarily homogeneous, maps. -/
theorem psiForwardInverse_whiskerLeft {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    HEq (((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).map₂ (f ◁ x))
      (((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).map f ◁
        ((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).map₂ x) :=
  strict_left _ (psiForwardInverse_isStrict t ht cs) f x

/-- Right contexts are preserved by the forward/inverse composite without a parity hypothesis. -/
theorem psiForwardInverse_whiskerRight {a b c : Uqπ D Sc sy hc}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    HEq (((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).map₂ (x ▷ h))
      (((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).map₂ x ▷
        ((psiExtension t ht cs).comp (psiInverseFunctor t ht cs)).map h) :=
  strict_right _ (psiForwardInverse_isStrict t ht cs) x h

/-- Left contexts are preserved by the inverse/forward composite without a parity hypothesis. -/
theorem psiInverseForward_whiskerLeft {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    HEq (((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).map₂ (f ◁ x))
      (((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).map f ◁
        ((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).map₂ x) :=
  strict_left _ (psiInverseForward_isStrict t ht cs) f x

/-- Right contexts are preserved by the inverse/forward composite without a parity hypothesis. -/
theorem psiInverseForward_whiskerRight {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    HEq (((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).map₂ (x ▷ h))
      (((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).map₂ x ▷
        ((psiInverseFunctor t ht cs).comp (psiExtension t ht cs)).map h) :=
  strict_right _ (psiInverseForward_isStrict t ht cs) x h

end OddMath.SKM
