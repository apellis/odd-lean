/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.TwoNatTransZigzag
import OddMath.SKM.ChevalleyQPiTwo
import StringDiagrams.Super.PiSOpInverseRoundtrip
import OddMath.SKM.ChevalleyQCounit

/-!
# The inverse and counit of `ω̃`

`chevalleyQPiReverseTwo : 𝔘_{q,π}(𝔤)^{sop} → 𝔘_{q,π}(𝔤)`, the inverse `PiSOp.inverseTwoFunctor` of the parity bridge followed by the Π-envelope of `G_q`, and the counit `chevalleyQPiGlobalCounit : G̃ ⋙ ω̃ ⟹ 1`. The counit is the Π-envelope of the counit of `ω_q`, conjugated by the parity bridge and transported along endpoint equalities. It is strong and graded.

Part of the adjoint biequivalence reading of [BE2] J. Brundan, A. P. Ellis,
*Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition 9.3.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
open TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local notation "A" => QTwoEnvelope k (UGr D Sc sy hc)
local notation "T" => TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc))
local notation "F" => chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "G" => chevalleyQReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "E" => chevalleyQGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "P" => PiSOp.twoFunctor (R := k) (B := A)
local notation "P⁻" => PiSOp.inverseTwoFunctor (R := k) (B := A)
local notation "Fπ" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- First the parity bridge reverse, then the lifted chosen Q reverse. -/
def chevalleyQPiReverseTwo : TwoSuperfunctor k (T) (QPiTwoEnvelope k (UGr D Sc sy hc)) :=
  (P⁻).comp (TwoEnvelope.mapPi (G))
local notation "Gπ" => chevalleyQPiReverseTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- Grading includes arbitrary arrow degrees and both comparison types. -/
theorem chevalleyQPiReverseTwo_isGraded : (Gπ).IsGraded :=
  PiSOp.inverseTwoFunctor_isGraded.comp
    (TwoEnvelope.mapPi_isGraded chevalleyQReverseTwo_isGraded)

/-- Exact weight action. -/
theorem chevalleyQPiReverseTwo_obj (a : T) :
    (Gπ).obj a = ⟨⟨negWeight a.unop.as.as⟩⟩ := rfl

/-- The parity tag is retained and the chosen Q reverse acts on the shifted word. -/
theorem chevalleyQPiReverseTwo_map {a b : T} (f : a ⟶ b) :
    (Gπ).map f = Envelope.mk (SOp.unop f).par
      ((G).map (SOp.mk (SOp.unop f).obj)) := rfl

/-- All arrows use the ordered endpoint correction, followed by the reverse Q map. -/
theorem chevalleyQPiReverseTwo_map₂ {a b : T} {f g : a ⟶ b} (η : f ⟶ g) :
    (Gπ).map₂ η = Envelope.ofHom ((G).map₂
      (SOp.mk' (PiSOp.correction (R := k) (SOp.unop f).par (SOp.unop g).par
        (Envelope.toHom (SOp.unsop η))))) := rfl

/-- Both comparison factors are retained. -/
theorem chevalleyQPiReverseTwo_mapComp {a b c : T} (f : a ⟶ b) (g : b ⟶ c) :
    (Gπ).mapComp f g =
      (TwoEnvelope.mapPi (G)).mapComp ((P⁻).map f) ((P⁻).map g) ≪≫
        (TwoEnvelope.mapPi (G)).map₂Iso ((P⁻).mapComp f g) := rfl

/-- The conjugate uses the Q counit, not a new chosen equivalence. -/
def qPiCounitConjugate :=
  TwoNatTrans.postcompose (P) (TwoNatTrans.precompose (P⁻) (TwoEnvelope.mapPiNatTrans (E)))

/-- Complete source endpoint equality, including the signed comparison maps. -/
theorem qPiCounit_source :
    ((P⁻).comp (TwoEnvelope.mapPi ((G).comp (F)))).comp (P) = (Gπ).comp (Fπ) := by
  simp only [chevalleyQPiReverseTwo, chevalleyQPiTwo,
    TwoEnvelope.mapPi_comp, TwoSuperfunctor.comp_assoc]

/-- Complete target endpoint equality uses the global parity inverse. -/
theorem qPiCounit_target :
    ((P⁻).comp (TwoEnvelope.mapPi (TwoSuperfunctor.id k (TwoSOp k (A))))).comp (P) =
      TwoSuperfunctor.id k (T) := by
  rw [TwoEnvelope.mapPi_id, TwoSuperfunctor.comp_id, PiSOp.inverseTwoFunctor_comp_twoFunctor]

/-- Transport the two endpoints within the target. -/
def qPiRebase {S S' U U' : TwoSuperfunctor k (T) (T)}
    (p : S = S') (q : U = U') (θ : TwoNatTrans S U) : TwoNatTrans S' U' := by
  cases p
  cases q
  exact θ

theorem qPiRebase_X {S S' U U' : TwoSuperfunctor k (T) (T)}
    (p : S = S') (q : U = U') (θ : TwoNatTrans S U) (a : T) :
    HEq ((qPiRebase p q θ).X a) (θ.X a) := by
  cases p
  cases q
  rfl

theorem qPiRebase_x {S S' U U' : TwoSuperfunctor k (T) (T)}
    (p : S = S') (q : U = U') (θ : TwoNatTrans S U) {a b : T} (f : a ⟶ b) :
    HEq ((qPiRebase p q θ).x f) (θ.x f) := by
  cases p
  cases q
  rfl

theorem qPiRebase_isStrong {S S' U U' : TwoSuperfunctor k (T) (T)}
    (p : S = S') (q : U = U') (θ : TwoNatTrans S U) (hθ : θ.IsStrong) :
    (qPiRebase p q θ).IsStrong := by
  cases p
  cases q
  exact hθ

theorem qPiRebase_isGraded {S S' U U' : TwoSuperfunctor k (T) (T)}
    (p : S = S') (q : U = U') (θ : TwoNatTrans S U) (hθ : θ.IsGraded) :
    (qPiRebase p q θ).IsGraded := by
  cases p
  cases q
  exact hθ

/-- The strong graded global counit on the target. -/
def chevalleyQPiGlobalCounit : TwoNatTrans ((Gπ).comp (Fπ)) (TwoSuperfunctor.id k (T)) :=
  qPiRebase
    (qPiCounit_source (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiCounit_target (D := D) (Sc := Sc) (sy := sy) (hc := hc))
    (qPiCounitConjugate (D := D) (Sc := Sc) (sy := sy) (hc := hc))

local notation "Eπ" => chevalleyQPiGlobalCounit (D := D) (Sc := Sc) (sy := sy) (hc := hc)

/-- All naturality cells of the counit are invertible. -/
theorem chevalleyQPiGlobalCounit_isStrong : (Eπ).IsStrong := by
  apply qPiRebase_isStrong
  apply TwoNatTrans.postcompose_isStrong (P)
  apply TwoNatTrans.precompose_isStrong (P⁻)
  exact TwoEnvelope.mapPiNatTrans_isStrong (θ := E) chevalleyQGlobalCounit_isStrong

/-- All naturality cells of the counit have integer degree zero. -/
theorem chevalleyQPiGlobalCounit_isGraded : (Eπ).IsGraded := by
  apply qPiRebase_isGraded
  apply TwoNatTrans.postcompose_isGraded (P) PiSOp.twoFunctor_isGraded
  apply TwoNatTrans.precompose_isGraded (P⁻)
  exact TwoEnvelope.mapPiNatTrans_isGraded (θ := E) chevalleyQGlobalCounit_isGraded

/-- The untransported conjugate has exactly the parity-zero object component. -/
theorem qPiCounitConjugate_X (a : T) :
    (qPiCounitConjugate (D := D) (Sc := Sc) (sy := sy) (hc := hc)).X a =
      (P).map (TwoEnvelope.Jm ((E).X ((P⁻).obj a).as)) := rfl

/-- Invertible naturality cells of the transported counit. -/
def chevalleyQPiGlobalCounitCell {a b : T} (f : a ⟶ b) :
    ((Gπ).comp (Fπ)).map f ≫ (Eπ).X b ≅
      (Eπ).X a ≫ (TwoSuperfunctor.id k (T)).map f :=
  @asIso _ _ _ _ ((Eπ).x f) (chevalleyQPiGlobalCounit_isStrong f)

end OddMath.SKM
