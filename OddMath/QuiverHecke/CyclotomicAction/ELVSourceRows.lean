/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentModule
import OddMath.QuiverHecke.CentreFinite

/-! # Common-source rows for the prepend endpoint

The reconstruction maps below use representable old rows, rather than separate
scalar coordinates at each old source. Their naturality includes arbitrary
word-to-word old arrows and retains the total parity twist in `pair`.
The intended application is the source endpoint of the deformed square resolution.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory Opposite MonoidalCategory
open scoped Classical TensorProduct DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Absorbing the prescribed twist into `pair` leaves ordinary old composition
on coefficients, even for off-diagonal arrows and inhomogeneous coefficients. -/
theorem sourcePull_pair (p : ZMod 2) (i : I) {u v t w : List I}
    (c : Old D Sc cutoff u v) (h : hom D Sc cutoff (i :: t) w)
    (b : Old D Sc cutoff v t) :
    sourcePull D Sc cutoff p i u v w c (pair D Sc cutoff p i h b) =
      pair D Sc cutoff p i h (oldComp D Sc cutoff u v t c b) := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff u v).mkQ_surjective c
  obtain ⟨b, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  simp only [pair_mk, sourcePull_mk, oldComp_mk, twist_comp, insert_comp,
    Category.assoc]

/-- The representable old presheaf at an arbitrary target word. -/
def oldRowPresheaf (t : List I) : (OldCategory D Sc cutoff)ᵒᵖ ⥤ ModuleCat k where
  obj v := ModuleCat.of k (Old D Sc cutoff v.unop.word t)
  map f := ModuleCat.ofHom (oldComp D Sc cutoff _ _ t f.unop)
  map_id v := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact Category.id_comp (X := (⟨v.unop.word⟩ : OldCategory D Sc cutoff))
      (Y := ⟨t⟩) b
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact Category.assoc (Z := (⟨t⟩ : OldCategory D Sc cutoff)) g.unop f.unop b

instance oldRowPresheaf_additive (t : List I) :
    (oldRowPresheaf D Sc cutoff t).Additive where
  map_add := by
    intro a b f g
    apply ModuleCat.hom_ext
    exact (oldComp D Sc cutoff _ _ t).map_add f.unop g.unop

/-- All old columns of a single representable old row. No corner is assumed nonzero. -/
abbrev OldContentRow (ν t : List I) :=
  OddMath.FiniteHomMatrix.RightModule (contentObject D Sc cutoff ν)
    (oldRowPresheaf D Sc cutoff t)

/-- A fixed positioned tail is a natural transformation from its representable row. -/
def sourcePairNat (p : ZMod 2) (i : I) {t w : List I}
    (h : hom D Sc cutoff (i :: t) w) :
    oldRowPresheaf D Sc cutoff t ⟶ sourcePresheaf D Sc cutoff p i w where
  app v := ModuleCat.ofHom (pair D Sc cutoff p i h)
  naturality a b f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact (sourcePull_pair D Sc cutoff p i f.unop h z).symm

/-- Right-old-ring-linear reconstruction along a common positioned tail. -/
def sourcePairRow (p : ZMod 2) (i : I) (ν : List I) {t w : List I}
    (h : hom D Sc cutoff (i :: t) w) :
    OldContentRow D Sc cutoff ν t →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceRow D Sc cutoff p i ν w :=
  OddMath.FiniteHomMatrix.RightModule.map (contentObject D Sc cutoff ν)
    (sourcePairNat D Sc cutoff p i h)

@[simp] theorem sourcePairRow_apply (p : ZMod 2) (i : I) (ν : List I)
    {t w : List I} (h : hom D Sc cutoff (i :: t) w)
    (b : OldContentRow D Sc cutoff ν t) (v : ContentWords ν) :
    sourcePairRow D Sc cutoff p i ν h b v = pair D Sc cutoff p i h (b v) := rfl

/-- The finite part of the common tail index: an old target and an input shuffle. -/
abbrev SourceTailIndex (ν : List I) := Σ t : ContentWords ν, PrependShuffle t.val.length

instance sourceTailIndexFintype (ν : List I) : Fintype (SourceTailIndex ν) := inferInstance

/-- The ambient word is determined by the old target and shuffle, not the old source. -/
def sourceTailWord (i : I) {ν : List I} (q : SourceTailIndex ν) : ContentWords (i :: ν) :=
  ⟨tgt (i :: q.1.val)
      (cw (Categorification.TypeA.canWord (q.1.val.length + 1) q.2.val⁻¹)),
    (tgt_perm _ _).trans (q.1.property.cons i)⟩

private theorem source_canWord_one (n : ℕ) : Categorification.TypeA.canWord n 1 = [] := by
  apply List.length_eq_zero_iff.mp
  rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]

/-- A common tail represented with the identity old normal form. -/
def sourceTailPBW (i : I) {ν : List I} (q : SourceTailIndex ν) (m : ℕ) :
    PrependIdx i q.1.val (sourceTailWord i q).val :=
  ⟨(m, [], 1, q.2), by simp, by simp, by
    simp [prependCrossingWord, source_canWord_one, cw, sourceTailWord,
      Categorification.TypeA.shiftWord]⟩

@[simp] theorem sourceTailPBW_oldTarget (i : I) {ν : List I}
    (q : SourceTailIndex ν) (m : ℕ) : (sourceTailPBW i q m).oldTarget = q.1.val := by
  simp [sourceTailPBW, PrependIdx.oldTarget, source_canWord_one, cw]

/-- The common tail, with its old target independent of the coefficient's source. -/
def sourceTail (i : I) {ν : List I} (q : SourceTailIndex ν) (m : ℕ) :
    hom D Sc cutoff (i :: q.1.val) (sourceTailWord i q).val :=
  sourceTailPBW_oldTarget i q m ▸
    ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
      prependTail D Sc (sourceTailPBW i q m))

/-- Embed one representable old row along a common tail into all ambient rows. -/
def sourceTailRow (p : ZMod 2) (i : I) (ν : List I) (q : SourceTailIndex ν) (m : ℕ) :
    OldContentRow D Sc cutoff ν q.1.val →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceContent D Sc cutoff p i ν :=
  (LinearMap.single (R := (ContentRing D Sc cutoff ν)ᵐᵒᵖ)
    (φ := fun w : ContentWords (i :: ν) => SourceRow D Sc cutoff p i ν w.val)
    (sourceTailWord i q)).comp
      (sourcePairRow D Sc cutoff p i ν (sourceTail D Sc cutoff i q m))

/-- Finitely supported common tails, each carrying an entire old idempotent row. -/
abbrev SourceRows (ν : List I) :=
  ⨁ q : SourceTailIndex ν × ℕ, OldContentRow D Sc cutoff ν q.1.1.val

/-- Actual common-source reconstruction; the scalar ring is the full old content ring. -/
def sourceRowsReconstruct (p : ZMod 2) (i : I) (ν : List I) :
    SourceRows D Sc cutoff ν →ₗ[(ContentRing D Sc cutoff ν)ᵐᵒᵖ]
      SourceContent D Sc cutoff p i ν :=
  DirectSum.toModule _ _ _ fun q => sourceTailRow D Sc cutoff p i ν q.1 q.2

@[simp] theorem sourceRowsReconstruct_lof (p : ZMod 2) (i : I) (ν : List I)
    (q : SourceTailIndex ν × ℕ) (b : OldContentRow D Sc cutoff ν q.1.1.val) :
    sourceRowsReconstruct D Sc cutoff p i ν (DirectSum.lof (ContentRing D Sc cutoff ν)ᵐᵒᵖ _ _ q b) =
      sourceTailRow D Sc cutoff p i ν q.1 q.2 b :=
  DirectSum.toModule_lof _ _ _

end OddMath.QuiverHecke.ELVOld
