import OddMath.SKM.PsiTwo
import OddMath.SKM.PsiInverseQ

/-!
# The shifted ψ functor

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4: extend the strict graded functor ψ by Lemma 9.1 to the
`(Q,Π)` envelope. We identify its objects, words, 2-morphism maps and both
composition comparisons. The restriction is an equality of 2-superfunctors,
including their comparisons. The source explicitly distinguishes the strict
unshifted ψ from its non-strict canonical extension. Accordingly, strictness
is asserted here only for the restriction; the extension retains its shift
comparisons. A literal
inverse functor and its two composite equalities are separate obligations;
invertibility of a composition comparison does not supply that inverse.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct QPiSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The extension of ψ to all integer and parity shifts. -/
def psiExtension (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc) :
    TwoSuperfunctor k (Uqπ D Sc sy hc) (TwoSOp k (Uqπ D Sc sy hc)) :=
  extendEnvelopeSOp (psiTwo t ht cs)

variable (t : k) (ht : t ^ 2 = -1) (cs : CScalars Sc)

/-- The shifted ψ preserves the integer grading. -/
theorem psiExtension_isGraded : (psiExtension (sy := sy) (hc := hc) t ht cs).IsGraded :=
  extendEnvelopeSOp_isGraded _ (psiTwo_isGraded t ht cs)

/-- Restriction recovers ψ with all of its comparison data. -/
theorem twoJ_comp_psiExtension :
    (QPiTwoEnvelope.twoJ k (UGr D Sc sy hc)).comp (psiExtension t ht cs) =
      psiTwo t ht cs :=
  twoJ_comp_extendEnvelopeSOp _

/-- The unshifted restriction, rather than the canonical extension, is strict. -/
theorem psiExtension_restriction_isStrict :
    ((QPiTwoEnvelope.twoJ k (UGr D Sc sy hc)).comp (psiExtension t ht cs)).IsStrict := by
  rw [twoJ_comp_psiExtension]
  exact psiTwo_isStrict t ht cs

/-- ψ fixes the weight object. -/
@[simp] theorem psiExtension_obj (a : Uqπ D Sc sy hc) :
    (psiExtension t ht cs).obj a = ⟨a⟩ := rfl

local instance : ∀ a b : TwoSOp k (Uqπ D Sc sy hc), QPiSupercategory k (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b

local instance {a b : UGr D Sc sy hc} : QPiSupercategory k
    (psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :=
  QPiTwoSupercategory.homQPiLeft _ _

/-- The 1-map is the explicit signed shift assignment on the same word. -/
theorem psiExtension_map_eq_psiShift {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    SOp.unop ((psiExtension t ht cs).map f) = psiShift f := by
  change SOp.unop (Envelope.piPow (B := psiObj a.as.as ⟶ psiObj b.as.as) k f.par
    (qPow (C := psiObj a.as.as ⟶ psiObj b.as.as) k f.obj.shift
      (psiMap f.obj.obj))) = psiShift f
  have hw := (psiPiIso_obj f.par (qPow k f.obj.shift (psiMap f.obj.obj))).trans
    (psiQPow_obj f.obj.shift (psiMap f.obj.obj))
  have hs := psiQPow_shift f.obj.shift (psiMap f.obj.obj)
  have hp := psiQPow_par f.obj.shift (psiMap f.obj.obj)
  rcases parity_eq_zero_or_one f.par with h | h
  · simp only [h, Envelope.piPow_zero]
    apply Envelope.ext
    · simpa only [psiShift, h, zero_add, psiMap] using hp
    · apply QEnvelope.ext
      · simpa only [psiShift, psiMap, zero_sub] using hs
      · apply Presentation.Bicat.Hom.ext
        exact psiQPow_obj f.obj.shift (psiMap f.obj.obj)
  · simp only [h, Envelope.piPow_one]
    apply Envelope.ext
    · change (SOp.unop (qPow (C := psiObj a.as.as ⟶ psiObj b.as.as) k f.obj.shift (psiMap f.obj.obj))).par + 1 =
        f.par + psiParity f.obj.obj
      rw [hp, h]
      exact add_comm _ _
    · apply QEnvelope.ext
      · change (SOp.unop (qPow (C := psiObj a.as.as ⟶ psiObj b.as.as) k f.obj.shift (psiMap f.obj.obj))).obj.shift + 0 =
          -f.obj.shift
        simpa only [psiMap, zero_sub, add_zero] using hs
      · apply Presentation.Bicat.Hom.ext
        simpa only [h, Envelope.piPow_one, psiShift, psiMap] using hw

/-- The integer exponent is negated for every shifted word. -/
@[simp] theorem psiExtension_map_shift {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (SOp.unop ((psiExtension t ht cs).map f)).obj.shift = -f.obj.shift := by
  rw [psiExtension_map_eq_psiShift]
  rfl

/-- The parity label acquires the downward-word parity. -/
@[simp] theorem psiExtension_map_par {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (SOp.unop ((psiExtension t ht cs).map f)).par = f.par + psiParity f.obj.obj := by
  rw [psiExtension_map_eq_psiShift]
  rfl

/-- The word, including its typed endpoints, is unchanged. -/
@[simp] theorem psiExtension_map_word {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (SOp.unop ((psiExtension t ht cs).map f)).obj.obj = f.obj.obj := by
  rw [psiExtension_map_eq_psiShift]
  rfl

/-- The identity comparison is inherited from the strict unshifted ψ. -/
theorem psiExtension_mapId_eq (a : Uqπ D Sc sy hc) :
    (psiExtension t ht cs).mapId a = eqToIso (psiMap_id a.as.as).symm := rfl

/-- The 2-map is conjugation of the proved quotient map by both shift structures. -/
theorem psiExtension_map₂_eq {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (x : f ⟶ g) :
    (psiExtension t ht cs).map₂ x =
      psiQPiConjugate f.obj.shift g.obj.shift f.par g.par
        (psiMap₂ t ht cs f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom x)) := rfl

/-- The homogeneous formula retains all four word-boundary transports. -/
theorem psiExtension_map₂_toHom {a b : Uqπ D Sc sy hc} {f g : a ⟶ b}
    {x : f ⟶ g} {r : ZMod 2}
    (hx : QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ r) :
    QPiTwoEnvelope.toHom (SOp.unsop ((psiExtension t ht cs).map₂ x)) =
      sign k (f.par * r + (f.par + r) * g.par + g.par) •
        (eqToHom (congrArg (pres D Sc).obj
            (psiPiIso_obj g.par (qPow k g.obj.shift (psiMap g.obj.obj)))) ≫
          (eqToHom (congrArg (pres D Sc).obj (psiQPow_obj g.obj.shift (psiMap g.obj.obj))) ≫
            QPiTwoEnvelope.toHom (SOp.unsop
              (psiMap₂ t ht cs f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom x))) ≫
            eqToHom (congrArg (pres D Sc).obj
              (psiQPow_obj f.obj.shift (psiMap f.obj.obj)).symm)) ≫
          eqToHom (congrArg (pres D Sc).obj
            (psiPiIso_obj f.par (qPow k f.obj.shift (psiMap f.obj.obj))).symm)) :=
  psiQPiConjugate_eq _ _ _ _ _ (psiMap₂_mem_parity t ht cs hx)

/-- The same homogeneous formula with the endpoint transports expressed by HEq. -/
theorem psiExtension_map₂_toHom_heq {a b : Uqπ D Sc sy hc} {f g : a ⟶ b}
    {x : f ⟶ g} {r : ZMod 2}
    (hx : QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ r) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop ((psiExtension t ht cs).map₂ x)))
      (sign k (f.par * r + (f.par + r) * g.par + g.par) •
        QPiTwoEnvelope.toHom (SOp.unsop
          (psiMap₂ t ht cs f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom x)))) :=
  psiExtension_map₂_heq (psiTwo t ht cs) hx

/-- Forward composition comparison, with ψ's equality comparison made explicit. -/
theorem psiExtension_mapComp_hom_eq {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiExtension t ht cs).mapComp f g).hom = sign k (f.par * g.par) •
      ((psiQPiIso f.obj.shift f.par (psiMap f.obj.obj)).hom ▷ (psiExtension t ht cs).map g ≫
        psiMap f.obj.obj ◁ (psiQPiIso g.obj.shift g.par (psiMap g.obj.obj)).hom ≫
        eqToHom (psiMap_comp f.obj.obj g.obj.obj).symm ≫
        (psiQPiIso (f.obj.shift + g.obj.shift) (f.par + g.par)
          (psiMap (f.obj.obj ≫ g.obj.obj))).inv) :=
  psiExtension_mapComp_hom_combined (psiTwo t ht cs) f g

/-- Inverse of the composition comparison; this is not an inverse functor. -/
theorem psiExtension_mapComp_inv_eq {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) :
    ((psiExtension t ht cs).mapComp f g).inv = sign k (f.par * g.par) •
      ((psiQPiIso (f.obj.shift + g.obj.shift) (f.par + g.par)
          (psiMap (f.obj.obj ≫ g.obj.obj))).hom ≫
        eqToHom (psiMap_comp f.obj.obj g.obj.obj) ≫
        psiMap f.obj.obj ◁ (psiQPiIso g.obj.shift g.par (psiMap g.obj.obj)).inv ≫
        (psiQPiIso f.obj.shift f.par (psiMap f.obj.obj)).inv ▷
          (psiExtension t ht cs).map g) :=
  psiExtension_mapComp_inv_combined (psiTwo t ht cs) f g

end OddMath.SKM
