import OddMath.SKM.PsiInverse

/-!
# Integer shifts and the combined ψ extension comparison

This is the next inverse-calculation slice for Brundan–Ellis Proposition 9.4,
using the actual `(Q,Π)` structure of the super-opposite envelope and the
canonical extension of Lemma 9.1. `psiQConjugate_eq` computes every integer
power, with literal word transports and no scalar. `psiQPiConjugate_eq` and
its cup/cap consumers combine this with the previously proved Π calculation.
`psiExtension_map₂_heq` identifies the result with the canonical extension;
`psiExtension_mapComp_hom_combined` computes its full composition comparison,
including the leading parity sign and both structure-isomorphism layers.

The coefficient hypotheses remain those of the existing graded presentation;
there is no field, flatness, or comparison-identity assumption. The arbitrary
input functor `F` below is an interface, not a constructed ψ functor. This file
does not evaluate ψ on the original derived left cups/caps, prove the literal
two-sided inverse, or normalize the inverse composition comparison. Those are
separate obligations, not consequences of the scalar calculations alone.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct QPiSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

variable {a b : UGr D Sc sy hc}
local instance : QPiSupercategory k
    (psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :=
  QPiTwoSupercategory.homQPiLeft _ _

private theorem psiSigma_hom_eq
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (QPiSupercategory.σ (R := k) f).hom) =
      eqToHom (congrArg (pres D Sc).obj (Obj.tensor_nil _ _).symm) := by
  change QPiTwoEnvelope.toHom (SOp.unsop
    (f ◁ (QPiTwoSupercategory.σ (R := k) (psiObj b)).hom ≫ (rightUnitor f).hom)) = _
  rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (TwoSupercategory.whiskerLeft_mem f
    (QPiTwoSupercategory.σ_hom_mem _))) (SOp.mem_parity_iff.mp
      (TwoSupercategory.rightUnitor_hom_mem f))]
  simp only [mul_zero, sign_zero, one_smul, TwoSOp.unsop_rightUnitor_hom,
    TwoSOp.unsop_whiskerLeft]
  change QEnvelope.toHom ((rightUnitor (SOp.unop f).obj).inv ≫
    (SOp.unop f).obj ◁ twist k (SOp.unop f).par (𝟙 _)) = _
  rw [twist_id]
  change (rightUnitor (SOp.unop f).obj.obj).inv ≫
    (SOp.unop f).obj.obj ◁ 𝟙 _ = _
  erw [TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  rfl

private theorem psiSigmaBar_hom_eq
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (QPiSupercategory.σbar (R := k) f).hom) =
      eqToHom (congrArg (pres D Sc).obj (Obj.tensor_nil _ _).symm) := by
  change QPiTwoEnvelope.toHom (SOp.unsop
    (f ◁ (QPiTwoSupercategory.σbar (R := k) (psiObj b)).hom ≫ (rightUnitor f).hom)) = _
  rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (TwoSupercategory.whiskerLeft_mem f
    (QPiTwoSupercategory.σbar_hom_mem _))) (SOp.mem_parity_iff.mp
      (TwoSupercategory.rightUnitor_hom_mem f))]
  simp only [mul_zero, sign_zero, one_smul, TwoSOp.unsop_rightUnitor_hom,
    TwoSOp.unsop_whiskerLeft]
  change QEnvelope.toHom ((rightUnitor (SOp.unop f).obj).inv ≫
    (SOp.unop f).obj ◁ twist k (SOp.unop f).par (𝟙 _)) = _
  rw [twist_id]
  change (rightUnitor (SOp.unop f).obj.obj).inv ≫
    (SOp.unop f).obj.obj ◁ 𝟙 _ = _
  erw [TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
  rfl

private theorem psiQNat_obj (n : ℕ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (qPowNat (C := psiObj a ⟶ psiObj b) k n f)).obj.obj.obj =
      (SOp.unop f).obj.obj.obj := by
  induction n with
  | zero => rfl
  | succ n ih => exact (Obj.tensor_nil _ _).trans ih

private theorem psiQInvNat_obj (n : ℕ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (qinvPowNat (C := psiObj a ⟶ psiObj b) k n f)).obj.obj.obj =
      (SOp.unop f).obj.obj.obj := by
  induction n with
  | zero => rfl
  | succ n ih => exact (Obj.tensor_nil _ _).trans ih

/-- Integer-shifting in the super-opposite preserves the word. -/
theorem psiQPow_obj (m : ℤ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (qPow (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) k m f)).obj.obj.obj = (SOp.unop f).obj.obj.obj := by
  cases m with
  | ofNat n => exact psiQNat_obj n f
  | negSucc n => exact psiQInvNat_obj (n + 1) f

/-- The integer structure isomorphism used by the extension. -/
def psiQIso (m : ℤ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) := σPow k m f

/-- No scalar occurs in the integer structure map. -/
theorem psiQIso_hom_eq (m : ℤ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).hom) =
      eqToHom (congrArg (pres D Sc).obj (psiQPow_obj m f).symm) := by
  cases m with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      change QPiTwoEnvelope.toHom (SOp.unsop
        ((QPiSupercategory.σ (R := k) (qPowNat (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) k n f)).hom ≫ (σPowNat k n f).hom)) = _
      rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (σ_hom_mem (R := k) (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) _))
        (SOp.mem_parity_iff.mp (σPowNat_hom_mem (R := k) (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) _ _))]
      change sign k (0 * 0) •
        (QPiTwoEnvelope.toHom (SOp.unsop (σPowNat k n f).hom) ≫
          QPiTwoEnvelope.toHom (SOp.unsop (QPiSupercategory.σ (R := k) (C := psiObj a ⟶ psiObj b) _).hom)) = _
      rw [show sign k (0 * 0) = 1 from sign_zero k, one_smul]
      change QPiTwoEnvelope.toHom (SOp.unsop (psiQIso (Int.ofNat n) f).hom) ≫ _ = _
      rw [ih, psiSigma_hom_eq]
      exact eqToHom_trans
        (congrArg (pres D Sc).obj (psiQPow_obj (Int.ofNat n) f).symm)
        (congrArg (pres D Sc).obj (Obj.tensor_nil _ _).symm)
  | negSucc n =>
    suffices h : ∀ n, QPiTwoEnvelope.toHom (SOp.unsop (σbarPowNat k n f).hom) =
        eqToHom (congrArg (pres D Sc).obj (psiQInvNat_obj n f).symm) by
      exact h (n + 1)
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change QPiTwoEnvelope.toHom (SOp.unsop
        ((QPiSupercategory.σbar (R := k) (qinvPowNat (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) k n f)).hom ≫
          (σbarPowNat k n f).hom)) = _
      rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (σbar_hom_mem (R := k) (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) _))
        (SOp.mem_parity_iff.mp (σbarPowNat_hom_mem (R := k) (C := psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) _ _))]
      change sign k (0 * 0) •
        (QPiTwoEnvelope.toHom (SOp.unsop (σbarPowNat k n f).hom) ≫
          QPiTwoEnvelope.toHom (SOp.unsop (QPiSupercategory.σbar (R := k) (C := psiObj a ⟶ psiObj b) _).hom)) = _
      rw [show sign k (0 * 0) = 1 from sign_zero k, one_smul, ih, psiSigmaBar_hom_eq]
      exact eqToHom_trans
        (congrArg (pres D Sc).obj (psiQInvNat_obj n f).symm)
        (congrArg (pres D Sc).obj (Obj.tensor_nil _ _).symm)

/-- The inverse integer structure map is also the boundary transport. -/
theorem psiQIso_inv_eq (m : ℤ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).inv) =
      eqToHom (congrArg (pres D Sc).obj (psiQPow_obj m f)) := by
  have hh := congrArg (fun x => QPiTwoEnvelope.toHom (SOp.unsop x))
    (psiQIso m f).hom_inv_id
  erw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (σPow_hom_mem (R := k) m f))
    (SOp.mem_parity_iff.mp (σPow_inv_mem (R := k) m f))] at hh
  change sign k (0 * 0) •
    (QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).inv) ≫
      QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).hom)) = 𝟙 _ at hh
  rw [show sign k (0 * 0) = 1 from sign_zero k, one_smul, psiQIso_hom_eq] at hh
  apply (cancel_mono (eqToHom (congrArg (pres D Sc).obj (psiQPow_obj m f).symm))).mp
  exact hh.trans (eqToHom_trans
    (congrArg (pres D Sc).obj (psiQPow_obj m f))
    (congrArg (pres D Sc).obj (psiQPow_obj m f).symm)).symm

/-- Integer-shift conjugation in the hom category of the ψ target. -/
def psiQConjugate (m n : ℤ)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b} (x : f ⟶ g) :=
  (psiQIso m f).hom ≫ x ≫ (psiQIso n g).inv

/-- Integer conjugation adds no sign, for every homogeneous parity. -/
theorem psiQConjugate_eq (m n : ℤ) (r : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ parity (R := k) _ _ r) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQConjugate m n x)) =
      eqToHom (congrArg (pres D Sc).obj (psiQPow_obj n g)) ≫
        QPiTwoEnvelope.toHom (SOp.unsop x) ≫
        eqToHom (congrArg (pres D Sc).obj (psiQPow_obj m f).symm) := by
  have hm := σPow_hom_mem (R := k) m f
  have hn := σPow_inv_mem (R := k) n g
  unfold psiQConjugate
  rw [← Category.assoc]
  erw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (comp_mem hm hx))
    (SOp.mem_parity_iff.mp hn), SOp.comp_of_mem (SOp.mem_parity_iff.mp hm)
    (SOp.mem_parity_iff.mp hx)]
  change sign k ((0 + r) * 0) •
    (QPiTwoEnvelope.toHom (SOp.unsop (psiQIso n g).inv) ≫
      (sign k (0 * r) • (QPiTwoEnvelope.toHom (SOp.unsop x) ≫
        QPiTwoEnvelope.toHom (SOp.unsop (psiQIso m f).hom)))) = _
  rw [mul_zero, zero_mul, sign_zero, one_smul, one_smul,
    psiQIso_inv_eq, psiQIso_hom_eq]
  rfl

/-- Integer conjugation preserves parity. -/
theorem psiQConjugate_mem_parity (m n : ℤ) {r : ZMod 2}
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ parity (R := k) _ _ r) :
    psiQConjugate m n x ∈ parity (R := k) _ _ r := by
  simpa only [psiQConjugate, psiQIso, zero_add, add_zero] using
    comp_mem (σPow_hom_mem (R := k) m f) (comp_mem hx (σPow_inv_mem (R := k) n g))

/-- Integer conjugation changes degree by the target shift minus the source shift. -/
theorem psiQConjugate_mem_degree (m n : ℤ) {d : ℤ}
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ GradedSupercategory.degree (R := k) _ _ d) :
    psiQConjugate m n x ∈ GradedSupercategory.degree (R := k) _ _ (d + n - m) := by
  have h := GradedSupercategory.comp_mem_degree (σPow_hom_mem_degree (R := k) m f)
    (GradedSupercategory.comp_mem_degree hx (σPow_inv_mem_degree (R := k) n g))
  rw [show -m + (d + n) = d + n - m by omega] at h
  exact h

/-- The combined conjugation used by Lemma 9.1 on the ψ target. -/
def psiQPiConjugate (m n : ℤ) (p q : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b} (x : f ⟶ g) :=
  psiPiConjugate p q (psiQConjugate m n x)

/-- Combined integer/parity conjugation, retaining every boundary transport. -/
theorem psiQPiConjugate_eq (m n : ℤ) (p q r : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ parity (R := k) _ _ r) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiQPiConjugate m n p q x)) =
      sign k (p * r + (p + r) * q + q) •
        (eqToHom (congrArg (pres D Sc).obj (psiPiIso_obj q (qPow k n g))) ≫
          (eqToHom (congrArg (pres D Sc).obj (psiQPow_obj n g)) ≫
            QPiTwoEnvelope.toHom (SOp.unsop x) ≫
            eqToHom (congrArg (pres D Sc).obj (psiQPow_obj m f).symm)) ≫
          eqToHom (congrArg (pres D Sc).obj (psiPiIso_obj p (qPow k m f)).symm)) := by
  rw [psiQPiConjugate, psiPiConjugate_eq p q r (psiQConjugate_mem_parity m n hx),
    psiQConjugate_eq m n r hx]

private theorem transport_heq {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B A' B' : C} (hA : A' = A) (hB : B = B') (x : A ⟶ B) (c : k) :
    HEq (c • (eqToHom hA ≫ x ≫ eqToHom hB)) (c • x) := by
  subst hA
  subst hB
  simp

/-- Combined conjugation with word boundaries expressed heterogeneously. -/
theorem psiQPiConjugate_heq (m n : ℤ) (p q r : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ parity (R := k) _ _ r) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop (psiQPiConjugate m n p q x)))
      (sign k (p * r + (p + r) * q + q) • QPiTwoEnvelope.toHom (SOp.unsop x)) := by
  exact (heq_of_eq (psiQPiConjugate_eq m n p q r hx)).trans
    ((transport_heq _ _ _ _).trans (transport_heq _ _ _ _))

/-- The combined shifts on the cup assignment retain only the printed parity sign. -/
theorem psiCup_qpiConjugate (cs : CScalars Sc) (μ : X) (i : I)
    (m n : ℤ) (p q : ZMod 2) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiQPiConjugate m n p q (psiCup (sy := sy) (hc := hc) cs μ i))))
      (sign k (p * q + q) • epsP cs i μ) := by
  have h := psiQPiConjugate_heq m n p q 0 (psiCup_mem_parity (sy := sy) (hc := hc) cs μ i)
  change HEq _ (sign k (p * 0 + (p + 0) * q + q) • epsP cs i μ) at h
  simpa only [mul_zero, add_zero, zero_add] using h

/-- The cap assignment retains its additional `ipar` coefficient after both shifts. -/
theorem psiCap_qpiConjugate (cs : CScalars Sc) (μ : X) (i : I)
    (m n : ℤ) (p q : ZMod 2) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiQPiConjugate m n p q (psiCap (sy := sy) (hc := hc) cs μ i))))
      (sign k (p * q + q + ipar D i μ) • etaP cs i μ) := by
  have h := psiQPiConjugate_heq m n p q 0 (psiCap_mem_parity (sy := sy) (hc := hc) cs μ i)
  change HEq _ (sign k (p * 0 + (p + 0) * q + q) •
    (sign k (ipar D i μ) • etaP cs i μ)) at h
  simpa only [mul_zero, add_zero, zero_add, smul_smul, ← sign_add] using h

/-- The integer shift in the super-opposite subtracts the exponent. -/
theorem psiQPow_shift (m : ℤ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (qPow (C := psiObj a ⟶ psiObj b) k m f)).obj.shift =
      (SOp.unop f).obj.shift - m := by
  cases m with
  | ofNat n =>
    induction n with
    | zero => exact (sub_zero _).symm
    | succ n ih =>
      change (SOp.unop (qPowNat (C := psiObj a ⟶ psiObj b) k n f)).obj.shift + -1 =
        (SOp.unop f).obj.shift - ((n + 1 : ℕ) : ℤ)
      change (SOp.unop (qPowNat (C := psiObj a ⟶ psiObj b) k n f)).obj.shift =
        (SOp.unop f).obj.shift - (n : ℤ) at ih
      push_cast
      omega
  | negSucc n =>
    have h : ∀ n, (SOp.unop (qinvPowNat (C := psiObj a ⟶ psiObj b) k n f)).obj.shift =
        (SOp.unop f).obj.shift + n := by
      intro n
      induction n with
      | zero => exact (add_zero _).symm
      | succ n ih =>
        change (SOp.unop (qinvPowNat (C := psiObj a ⟶ psiObj b) k n f)).obj.shift + 1 = _
        push_cast
        omega
    change (SOp.unop (qinvPowNat (C := psiObj a ⟶ psiObj b) k (n + 1) f)).obj.shift = _
    rw [h]
    omega

/-- Integer shifts do not alter the parity label. -/
theorem psiQPow_par (m : ℤ)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (qPow (C := psiObj a ⟶ psiObj b) k m f)).par = (SOp.unop f).par := by
  cases m with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih => exact (add_zero _).trans ih
  | negSucc n =>
    suffices h : ∀ n, (SOp.unop (qinvPowNat (C := psiObj a ⟶ psiObj b) k n f)).par =
        (SOp.unop f).par from h (n + 1)
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (add_zero _).trans ih

/-- Integer and parity conjugations preserve the prescribed total degree. -/
theorem psiQPiConjugate_mem_degree (m n : ℤ) (p q : ZMod 2) {d : ℤ}
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ GradedSupercategory.degree (R := k) _ _ d) :
    psiQPiConjugate m n p q x ∈ GradedSupercategory.degree (R := k) _ _ (d + n - m) := by
  have h := GradedSupercategory.comp_mem_degree
    (Envelope.ζPow_hom_mem_degree (R := k) p (qPow k m f))
    (GradedSupercategory.comp_mem_degree (psiQConjugate_mem_degree m n hx)
      (Envelope.ζPow_inv_mem_degree (R := k) q (qPow k n g)))
  simpa only [psiQPiConjugate, psiPiConjugate, psiPiIso, zero_add, add_zero] using h

/-- The structure isomorphism for the full `(Q,Π)` shift. -/
def psiQPiIso (m : ℤ) (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :=
  psiPiIso p (qPow k m f) ≪≫ psiQIso m f

private theorem psiComparison_fuse {a b c : TwoSOp k (Uqπ D Sc sy hc)}
    {f₀ f₁ f₂ : a ⟶ b} {g₀ g₁ g₂ : b ⟶ c} {h₀ h₁ h₂ : a ⟶ c}
    (e : f₂ ≅ f₁) (s : f₁ ≅ f₀) (e' : g₂ ≅ g₁) (s' : g₁ ≅ g₀)
    (t : h₂ ≅ h₁) (u : h₁ ≅ h₀) (x : f₀ ≫ g₀ ⟶ h₀)
    (hs : s.hom ∈ parity (R := k) _ _ 0) :
    e.hom ▷ g₂ ≫ f₁ ◁ e'.hom ≫
        (s.hom ▷ g₁ ≫ f₀ ◁ s'.hom ≫ x ≫ u.inv) ≫ t.inv =
      (e ≪≫ s).hom ▷ g₂ ≫ f₀ ◁ (e' ≪≫ s').hom ≫ x ≫ (t ≪≫ u).inv := by
  simp only [Iso.trans_hom, Iso.trans_inv, TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [reassoc_of% (TwoEnvelope.interchange_even_left k hs e'.hom)]

section Extension
local instance : ∀ a b : TwoSOp k (Uqπ D Sc sy hc), QPiSupercategory k (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b
variable (F : TwoSuperfunctor k (UGr D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc)))

/-- The actual 1-map endpoint of the canonical extension. This equality isolates
its nested universal-property implementation for later comparison transports. -/
theorem psiExtension_map {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (extendEnvelopeSOp F).map f =
      Envelope.piPow k f.par (qPow k f.obj.shift (F.map f.obj.obj)) := rfl

/-- The combined conjugation is the 2-morphism map of the canonical extension,
not an assumed formula for a prospective ψ functor. -/
theorem psiExtension_map₂ {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    (extendEnvelopeSOp F).map₂ x =
      psiQPiConjugate f.obj.shift g.obj.shift f.par g.par
        (F.map₂ (QPiTwoEnvelope.toHom x)) := rfl

/-- The canonical extension on homogeneous maps, including both shifts and the sign. -/
theorem psiExtension_map₂_heq {a b : Uqπ D Sc sy hc} {f g : a ⟶ b}
    {x : f ⟶ g} {r : ZMod 2}
    (hx : QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ r) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop ((extendEnvelopeSOp F).map₂ x)))
      (sign k (f.par * r + (f.par + r) * g.par + g.par) •
        QPiTwoEnvelope.toHom (SOp.unsop (F.map₂ (QPiTwoEnvelope.toHom x)))) := by
  rw [psiExtension_map₂]
  exact psiQPiConjugate_heq _ _ _ _ _ (F.map₂_mem hx)

/-- The complete composition comparison of the canonical extension, expressed
in its integer and parity structure maps. The leading `sign(pq)` is retained. -/
theorem psiExtension_mapComp_hom {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((extendEnvelopeSOp F).mapComp f g).hom = sign k (f.par * g.par) •
      ((psiPiIso f.par _).hom ▷ (extendEnvelopeSOp F).map g ≫
        (QTwoEnvelope.extend F).map f.obj ◁ (psiPiIso g.par _).hom ≫
        ((psiQIso f.obj.shift (F.map f.obj.obj)).hom ▷ (QTwoEnvelope.extend F).map g.obj ≫
          F.map f.obj.obj ◁ (psiQIso g.obj.shift (F.map g.obj.obj)).hom ≫
          (F.mapComp f.obj.obj g.obj.obj).hom ≫
          (psiQIso (f.obj.shift + g.obj.shift) (F.map (f.obj.obj ≫ g.obj.obj))).inv) ≫
        (psiPiIso (f.par + g.par) _).inv) := by
  exact QPiTwoEnvelope.extendComp_hom F f g

/-- Fusing the integer and parity comparisons gives the complete extension
comparison. The even integer map crosses the parity map without an extra sign. -/
theorem psiExtension_mapComp_hom_combined {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((extendEnvelopeSOp F).mapComp f g).hom = sign k (f.par * g.par) •
      ((psiQPiIso f.obj.shift f.par (F.map f.obj.obj)).hom ▷ (extendEnvelopeSOp F).map g ≫
        F.map f.obj.obj ◁ (psiQPiIso g.obj.shift g.par (F.map g.obj.obj)).hom ≫
        (F.mapComp f.obj.obj g.obj.obj).hom ≫
        (psiQPiIso (f.obj.shift + g.obj.shift) (f.par + g.par)
          (F.map (f.obj.obj ≫ g.obj.obj))).inv) := by
  exact (psiExtension_mapComp_hom F f g).trans
    (congrArg (fun z => sign k (f.par * g.par) • z)
      (psiComparison_fuse _ _ _ _ _ _ _
        (σPow_hom_mem (R := k) f.obj.shift (F.map f.obj.obj))))

end Extension
end OddMath.SKM
