import OddMath.SKM.PsiExtension
import OddMath.SKM.PsiInverseParameters

/-!
# The inverse-direction shifted ψ functor

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4 asserts an isomorphism of graded 2-supercategories. We construct
its inverse-direction candidate as a graded `TwoSuperfunctor`, using the proved
shifted ψ at `-t` and `psiInverseCScalars t ht cs`. No inverse or preservation
hypotheses are assumed.

Write `P(w) = psiParity w` and `h(Q^m Π^a w) = a * (1 + P(w))`. The 2-map is
`sign(h(f) + h(g))` times the unwrapped opposite-root ψ map. Both composition
comparison maps acquire `sign(h(f) + h(g) + h(f ≫ g))`; the identity comparison
is unchanged. The exponent is invariant under `psiShift`, vanishes on Π-label
zero, and its coboundary is `a * P(v) + b * P(w)`. We prove the parity identity
identifying this correction with the double-extension residual relative to the
unshifted-word conjugation. This does not assert uniqueness or necessity of a
normalization over every coefficient ring.

The opposite adapter is private and specialized to `Uqπ`, reusing the existing
hom-category `SOp.mapFunctor` and `SOp.unsopUnsop`. The functor's naturality,
associativity, unit coherence, parity and integer grading are all proved.
The source's shifted extension is not required to be strict.

Both assignments on 1-morphisms compose to the identity. Still required for
the complete Proposition 9.4 inverse identities are the two composite 2-map
identities on arbitrary quotient/envelope morphisms and the composite
composition and identity comparisons. Neither generator roundtrips nor the
scalar residual identity alone proves these functor equalities.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private abbrev reverseHom (F : TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc)))
    (a b : Uqπ D Sc sy hc) :=
  SOp.mapFunctor (F.mapFunctor a b) F.map₂_mem ⋙ SOp.unsopUnsop

private def reverseIso {a b : Uqπ D Sc sy hc} {f g : SOp k (a ⟶ b)}
    (e : f ≅ g) (he : e.hom ∈ parity (R := k) _ _ 0) : (SOp.unop f) ≅ (SOp.unop g) :=
  SOp.unsopUnsop.mapIso (SOp.evenIso e he)

private theorem unsop_comp_left {a b : Uqπ D Sc sy hc}
    {f g h : SOp k (a ⟶ b)} (x : f ⟶ g) (y : g ⟶ h)
    (hx : x ∈ parity (R := k) _ _ 0) :
    SOp.unsop (x ≫ y) = SOp.unsop y ≫ SOp.unsop x :=
  SOp.compC_even_left (show SOp.unsop x ∈ parity (R := k) _ _ 0 from hx) _

private theorem unsop_comp_right {a b : Uqπ D Sc sy hc}
    {f g h : SOp k (a ⟶ b)} (x : f ⟶ g) (y : g ⟶ h)
    (hy : y ∈ parity (R := k) _ _ 0) :
    SOp.unsop (x ≫ y) = SOp.unsop y ≫ SOp.unsop x :=
  SOp.compC_even_right _ (show SOp.unsop y ∈ parity (R := k) _ _ 0 from hy)

private def reversePsi (F : TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc))) :
    TwoSuperfunctor k (TwoSOp k (Uqπ D Sc sy hc)) (Uqπ D Sc sy hc) where
  obj a := (F.obj a.unop).unop
  map {a b} f := SOp.unop (F.map (SOp.unop f))
  map₂ {a b f g} x := SOp.unsop (F.map₂ (SOp.unsop x))
  map₂_id f := (reverseHom F _ _).map_id f
  map₂_comp x y := (reverseHom F _ _).map_comp x y
  map₂_add {a b f g} x y := by
    change SOp.unsop (F.map₂ (SOp.unsop (x + y))) = _
    rw [SOp.unsop_add, F.map₂_add, SOp.unsop_add]
  map₂_smul {a b f g} r x := by
    change SOp.unsop (F.map₂ (SOp.unsop (r • x))) = _
    rw [SOp.unsop_smul, F.map₂_smul, SOp.unsop_smul]
  map₂_mem hx := F.map₂_mem hx
  mapComp f g := reverseIso (F.mapComp (SOp.unop f) (SOp.unop g)) (F.mapComp_hom_mem _ _)
  mapId a := reverseIso (F.mapId a.unop) (F.mapId_hom_mem _)
  mapComp_hom_mem f g := inv_mem (F.mapComp (SOp.unop f) (SOp.unop g)) (F.mapComp_hom_mem _ _)
  mapId_hom_mem a := inv_mem (F.mapId a.unop) (F.mapId_hom_mem _)
  mapComp_naturality_left {a b c f f'} x g := by
    have e : F.map₂ (SOp.unsop x ▷ (SOp.unop g)) ≫ (F.mapComp (SOp.unop f) (SOp.unop g)).inv =
        (F.mapComp (SOp.unop f') (SOp.unop g)).inv ≫ F.map₂ (SOp.unsop x) ▷ F.map (SOp.unop g) := by
      rw [Iso.comp_inv_eq, Category.assoc, F.mapComp_naturality_left, Iso.inv_hom_id_assoc]
    have h := congrArg SOp.unsop e
    rw [unsop_comp_right _ _ (inv_mem _ (F.mapComp_hom_mem _ _)),
      unsop_comp_left _ _ (inv_mem _ (F.mapComp_hom_mem _ _))] at h
    exact h.symm
  mapComp_naturality_right {a b c} f {g g'} x := by
    have e : F.map₂ ((SOp.unop f) ◁ SOp.unsop x) ≫ (F.mapComp (SOp.unop f) (SOp.unop g)).inv =
        (F.mapComp (SOp.unop f) (SOp.unop g')).inv ≫ F.map (SOp.unop f) ◁ F.map₂ (SOp.unsop x) := by
      rw [Iso.comp_inv_eq, Category.assoc, F.mapComp_naturality_right, Iso.inv_hom_id_assoc]
    have h := congrArg SOp.unsop e
    rw [unsop_comp_right _ _ (inv_mem _ (F.mapComp_hom_mem _ _)),
      unsop_comp_left _ _ (inv_mem _ (F.mapComp_hom_mem _ _))] at h
    exact h.symm
  map₂_associator f g h := by
    have e : whiskerLeftIso (R := k) (F.map (SOp.unop f)) (F.mapComp (SOp.unop g) (SOp.unop h)) ≪≫
        F.mapComp (SOp.unop f) ((SOp.unop g) ≫ (SOp.unop h)) ≪≫
          F.map₂Iso (associator (SOp.unop f) (SOp.unop g) (SOp.unop h)).symm =
      (associator (F.map (SOp.unop f)) (F.map (SOp.unop g)) (F.map (SOp.unop h))).symm ≪≫
        whiskerRightIso (R := k) (F.mapComp (SOp.unop f) (SOp.unop g)) (F.map (SOp.unop h)) ≪≫
          F.mapComp ((SOp.unop f) ≫ (SOp.unop g)) (SOp.unop h) :=
      Iso.ext (by simpa using F.map₂_associator (SOp.unop f) (SOp.unop g) (SOp.unop h))
    have hh := congrArg (fun e => SOp.unsop e.inv) e
    simp only [Iso.trans_inv, Iso.symm_inv, TwoSuperfunctor.map₂Iso_inv,
      whiskerLeftIso_inv, whiskerRightIso_inv, Category.assoc] at hh
    rw [unsop_comp_left _ _ (F.map₂_mem (associator_hom_mem _ _ _)),
      unsop_comp_left _ _ (inv_mem _ (F.mapComp_hom_mem _ _)),
      unsop_comp_left _ _ (inv_mem _ (F.mapComp_hom_mem _ _)),
      unsop_comp_left _ _ (whiskerRight_mem _ (inv_mem _ (F.mapComp_hom_mem _ _)))] at hh
    simp only [Category.assoc] at hh
    exact hh
  map₂_leftUnitor f := by
    have e : whiskerRightIso (R := k) (F.mapId _) (F.map (SOp.unop f)) ≪≫
        F.mapComp (𝟙 _) (SOp.unop f) ≪≫ F.map₂Iso (leftUnitor (SOp.unop f)) =
        leftUnitor (F.map (SOp.unop f)) := Iso.ext (F.map₂_leftUnitor (SOp.unop f))
    have h := congrArg (fun e => SOp.unsop e.inv) e
    simp only [Iso.trans_inv, TwoSuperfunctor.map₂Iso_inv, whiskerRightIso_inv, Category.assoc] at h
    rw [unsop_comp_left _ _ (F.map₂_mem (inv_mem _ (leftUnitor_hom_mem _))),
      unsop_comp_left _ _ (inv_mem _ (F.mapComp_hom_mem _ _))] at h
    simp only [Category.assoc] at h
    exact h
  map₂_rightUnitor f := by
    have e : whiskerLeftIso (R := k) (F.map (SOp.unop f)) (F.mapId _) ≪≫
        F.mapComp (SOp.unop f) (𝟙 _) ≪≫ F.map₂Iso (rightUnitor (SOp.unop f)) =
        rightUnitor (F.map (SOp.unop f)) := Iso.ext (F.map₂_rightUnitor (SOp.unop f))
    have h := congrArg (fun e => SOp.unsop e.inv) e
    simp only [Iso.trans_inv, TwoSuperfunctor.map₂Iso_inv, whiskerLeftIso_inv, Category.assoc] at h
    rw [unsop_comp_left _ _ (F.map₂_mem (inv_mem _ (rightUnitor_hom_mem _))),
      unsop_comp_left _ _ (inv_mem _ (F.mapComp_hom_mem _ _))] at h
    simp only [Category.assoc] at h
    exact h

/-- Endpoint exponent of the inverse-direction shift correction. -/
def psiInverseSign {a b : Uqπ D Sc sy hc} (f : a ⟶ b) : ZMod 2 :=
  f.par * (1 + psiParity f.obj.obj)

@[simp] theorem psiInverseSign_id (a : Uqπ D Sc sy hc) : psiInverseSign (𝟙 a) = 0 := rfl

private def signIso {a b : TwoSOp k (Uqπ D Sc sy hc)} (f : a ⟶ b) (p : ZMod 2) : f ≅ f where
  hom := sign k p • 𝟙 f
  inv := sign k p • 𝟙 f
  hom_inv_id := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul, Category.id_comp]
  inv_hom_id := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul, Category.id_comp]

private abbrev ep {a b : TwoSOp k (Uqπ D Sc sy hc)} (f : a ⟶ b) : ZMod 2 :=
  psiInverseSign (SOp.unop f)

private theorem sign_cancel (p q r : ZMod 2) :
    sign k (p + q) * sign k (q + r) = sign k (p + r) := by
  rw [← sign_add]
  congr 1
  have h : q + q = 0 := by
    rcases parity_eq_zero_or_one q with rfl | rfl <;> rfl
  linear_combination h

private def psiShiftCorrection :
    TwoSuperfunctor k (TwoSOp k (Uqπ D Sc sy hc)) (TwoSOp k (Uqπ D Sc sy hc)) where
  obj a := a
  map f := f
  map₂ {a b f g} x := sign k (ep f + ep g) • x
  map₂_id f := by rw [sign_add, sign_mul_self, one_smul]
  map₂_comp {a b f g h} x y := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_cancel]
  map₂_add x y := smul_add _ _ _
  map₂_smul r x := smul_comm _ _ _
  map₂_mem hx := Submodule.smul_mem _ _ hx
  mapComp f g := signIso (f ≫ g) (ep f + ep g + ep (f ≫ g))
  mapId a := Iso.refl _
  mapComp_hom_mem f g := Submodule.smul_mem _ _ (id_mem _)
  mapId_hom_mem a := id_mem _
  mapComp_naturality_left {a b c f f'} x g := by
    dsimp only [signIso]
    rw [smul_whiskerRight (R := k), Linear.smul_comp, Linear.comp_smul,
      Linear.smul_comp, Linear.comp_smul, Category.comp_id, Category.id_comp,
      smul_smul, smul_smul, ← sign_add, ← sign_add]
    congr 2
    ring_nf
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
  mapComp_naturality_right {a b c} f {g g'} x := by
    dsimp only [signIso]
    rw [whiskerLeft_smul (R := k), Linear.smul_comp, Linear.comp_smul,
      Linear.smul_comp, Linear.comp_smul, Category.comp_id, Category.id_comp,
      smul_smul, smul_smul, ← sign_add, ← sign_add]
    congr 2
    ring_nf
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
  map₂_associator f g h := by
    dsimp only [signIso]
    simp only [whiskerLeft_smul (R := k), smul_whiskerRight (R := k),
      whiskerLeft_id (R := k), id_whiskerRight (R := k),
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id, smul_smul,
      ← sign_add]
    congr 2
    ring_nf
    simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, zero_add, add_zero]
  map₂_leftUnitor {a b} f := by
    dsimp only [signIso, Iso.refl_hom]
    simp only [id_whiskerRight (R := k), Category.id_comp, Linear.smul_comp, Linear.comp_smul,
      smul_smul, ← sign_add]
    have he : ep (𝟙 a) = (0 : ZMod 2) := rfl
    rw [he, zero_add]
    have hs : ep (𝟙 a ≫ f) + ep f + (ep f + ep (𝟙 a ≫ f)) = 0 := by
      ring_nf
      simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
    rw [hs, sign_zero, one_smul]
  map₂_rightUnitor {a b} f := by
    dsimp only [signIso, Iso.refl_hom]
    simp only [whiskerLeft_id (R := k), Category.id_comp, Linear.smul_comp, Linear.comp_smul,
      smul_smul, ← sign_add]
    have he : ep (𝟙 b) = (0 : ZMod 2) := rfl
    rw [he, add_zero]
    have hs : ep (f ≫ 𝟙 b) + ep f + (ep f + ep (f ≫ 𝟙 b)) = 0 := by
      ring_nf
      simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero]
    rw [hs, sign_zero, one_smul]

open GradedSupercategory

/-- The inverse-direction ψ, at the opposite root and the rescaled auxiliary units.
The endpoint correction is included in its 2-map and composition comparisons.
The two complete composite identities are separate obligations. -/
def psiInverseFunctor (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) :
    TwoSuperfunctor k (TwoSOp k (Uqπ D Sc sy hc)) (Uqπ D Sc sy hc) :=
  psiShiftCorrection.comp
    (reversePsi (psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)))

variable (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)

@[simp] theorem psiInverseFunctor_obj (a : TwoSOp k (Uqπ D Sc sy hc)) :
    (psiInverseFunctor t ht cs).obj a = a.unop := rfl

/-- The inverse-direction assignment negates Q, adds the word parity to Π, and fixes the word. -/
theorem psiInverseFunctor_map {a b : TwoSOp k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    (psiInverseFunctor t ht cs).map f = psiShift (SOp.unop f) :=
  psiExtension_map_eq_psiShift _ _ _ _

/-- Explicit endpoint correction of the opposite-root shifted 2-map. -/
theorem psiInverseFunctor_map₂ {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (x : f ⟶ g) :
    (psiInverseFunctor t ht cs).map₂ x =
      sign k (psiInverseSign (SOp.unop f) + psiInverseSign (SOp.unop g)) •
        SOp.unsop ((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).map₂
          (SOp.unsop x)) := by
  change SOp.unsop ((psiExtension _ _ _).map₂ (SOp.unsop (_ • x))) = _
  rw [SOp.unsop_smul, TwoSuperfunctor.map₂_smul, SOp.unsop_smul]

/-- The composition comparison has exactly the endpoint coboundary scalar. -/
theorem psiInverseFunctor_mapComp_hom {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiInverseFunctor t ht cs).mapComp f g).hom =
      sign k (psiInverseSign (SOp.unop f) + psiInverseSign (SOp.unop g) +
        psiInverseSign (SOp.unop (f ≫ g))) •
      SOp.unsop (((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).mapComp
        (SOp.unop f) (SOp.unop g)).inv) := by
  change ((reversePsi (psiExtension _ _ _)).mapComp f g).hom ≫
    (reversePsi (psiExtension _ _ _)).map₂ (sign k _ • 𝟙 (f ≫ g)) = _
  rw [TwoSuperfunctor.map₂_smul, TwoSuperfunctor.map₂_id, Linear.comp_smul, Category.comp_id]
  rfl

/-- The reverse comparison has the same involutive scalar. -/
theorem psiInverseFunctor_mapComp_inv {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiInverseFunctor t ht cs).mapComp f g).inv =
      sign k (psiInverseSign (SOp.unop f) + psiInverseSign (SOp.unop g) +
        psiInverseSign (SOp.unop (f ≫ g))) •
      SOp.unsop (((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).mapComp
        (SOp.unop f) (SOp.unop g)).hom) := by
  change (reversePsi (psiExtension _ _ _)).map₂ (sign k _ • 𝟙 (f ≫ g)) ≫
    ((reversePsi (psiExtension _ _ _)).mapComp f g).inv = _
  rw [TwoSuperfunctor.map₂_smul, TwoSuperfunctor.map₂_id, Linear.smul_comp, Category.id_comp]
  rfl

/-- The identity comparison is unchanged by the endpoint correction. -/
theorem psiInverseFunctor_mapId_hom (a : TwoSOp k (Uqπ D Sc sy hc)) :
    ((psiInverseFunctor t ht cs).mapId a).hom =
      SOp.unsop (((psiExtension (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)).mapId a.unop).inv) := by
  change ((reversePsi (psiExtension _ _ _)).mapId a).hom ≫
    (reversePsi (psiExtension _ _ _)).map₂ (𝟙 (𝟙 a)) = _
  rw [TwoSuperfunctor.map₂_id, Category.comp_id]
  rfl

/-- Degree preservation includes both comparison families. -/
theorem psiInverseFunctor_isGraded :
    (psiInverseFunctor (sy := sy) (hc := hc) t ht cs).IsGraded where
  map₂_mem_degree hx := by
    rw [psiInverseFunctor_map₂]
    exact Submodule.smul_mem _ _ ((psiExtension_isGraded _ _ _).map₂_mem_degree hx)
  mapComp_hom_mem_degree f g := by
    rw [psiInverseFunctor_mapComp_hom]
    exact Submodule.smul_mem _ _ (inv_mem_degree _
      ((psiExtension_isGraded _ _ _).mapComp_hom_mem_degree (SOp.unop f) (SOp.unop g)))
  mapId_hom_mem_degree a := by
    rw [psiInverseFunctor_mapId_hom]
    exact inv_mem_degree _ ((psiExtension_isGraded (-t) (psi_neg_sq ht)
      (psiInverseCScalars t ht cs)).mapId_hom_mem_degree a.unop)

/-- The correction is invariant under the ψ assignment of shifted words. -/
theorem psiInverseSign_psiShift {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    psiInverseSign (psiShift f) = psiInverseSign f := by
  change (f.par + psiParity f.obj.obj) * (1 + psiParity f.obj.obj) = _
  rcases parity_eq_zero_or_one (psiParity f.obj.obj) with hp | hp <;>
    simp [psiInverseSign, hp, show (1 : ZMod 2) + 1 = 0 from rfl]

/-- Explicit mixed-parity coboundary: no Q exponent occurs. -/
theorem psiInverseSign_comp {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    psiInverseSign f + psiInverseSign g + psiInverseSign (f ≫ g) =
      f.par * psiParity g.obj.obj + g.par * psiParity f.obj.obj := by
  change f.par * (1 + psiParity f.obj.obj) + g.par * (1 + psiParity g.obj.obj) +
    (f.par + g.par) * (1 + psiParity (f.obj.obj ≫ g.obj.obj)) = _
  rw [psiParity_comp]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, mul_zero, add_zero, zero_add]

/-- The residual of the two extension exponents, relative to the unshifted-word
roundtrip conjugation, is exactly the endpoint correction. This is a parity
identity, not an assertion of a roundtrip on arbitrary 2-morphisms. -/
theorem psiInverseSign_extension_residual (a b p q r : ZMod 2) :
    (a * r + (a + r) * b + b) +
      ((b + q) * (r + p + q) + ((b + q) + (r + p + q)) * (a + p) + (a + p)) +
      (q * (r + p + q) + (q + (r + p + q)) * p + p) =
      a * (1 + p) + b * (1 + q) := by
  ring_nf
  simp only [show (2 : ZMod 2) = 0 from rfl, show (6 : ZMod 2) = 0 from rfl,
    mul_zero, add_zero]

/-- No endpoint correction is introduced on a word with Π label zero. -/
theorem psiInverseSign_of_par_zero {a b : Uqπ D Sc sy hc} (f : a ⟶ b) (hf : f.par = 0) :
    psiInverseSign f = 0 := by simp only [psiInverseSign, hf, zero_mul]

/-- On the parity shift of the identity the correction exponent is one. -/
@[simp] theorem psiInverseSign_pi (a : Uqπ D Sc sy hc) :
    psiInverseSign (PiTwoSupercategory.pi (R := k) a) = 1 := rfl

/-- The forward then inverse assignment is literally the identity on 1-morphisms. -/
theorem psiInverseFunctor_map_forward {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (psiInverseFunctor t ht cs).map ((psiExtension t ht cs).map f) = f := by
  rw [psiInverseFunctor_map, psiExtension_map_eq_psiShift, psiShift_involutive]

/-- The inverse then forward assignment is literally the identity on 1-morphisms. -/
theorem psiInverseFunctor_map_reverse {a b : TwoSOp k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    (psiExtension t ht cs).map ((psiInverseFunctor t ht cs).map f) = f := by
  apply SOp.ext
  rw [psiExtension_map_eq_psiShift, psiInverseFunctor_map, psiShift_involutive]

/-- The concrete quotient-and-shifts formula for the corrected inverse 2-map. -/
theorem psiInverseFunctor_map₂_eq {a b : TwoSOp k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (x : f ⟶ g) :
    (psiInverseFunctor t ht cs).map₂ x =
      sign k (psiInverseSign (SOp.unop f) + psiInverseSign (SOp.unop g)) •
        SOp.unsop (psiQPiConjugate (SOp.unop g).obj.shift (SOp.unop f).obj.shift
          (SOp.unop g).par (SOp.unop f).par
          (psiMap₂ (-t) (psi_neg_sq ht) (psiInverseCScalars t ht cs)
            (SOp.unop g).obj.obj (SOp.unop f).obj.obj
            (QPiTwoEnvelope.toHom (SOp.unsop x)))) := by
  rw [psiInverseFunctor_map₂, psiExtension_map₂_eq]

end OddMath.SKM
