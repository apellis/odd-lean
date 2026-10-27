/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChangeBaseChange
import OddMath.SKM.BubbleAlgebra

/-!
# Scalar change of the Brundan–Ellis coefficient and bubble families

Brundan–Ellis, *Super Kac–Moody 2-categories*, (1.21)–(1.22) and
Definition 2.3. The all-colour polynomial/exterior coefficient algebra and
its normalized even and odd bubbles specialize over arbitrary commutative
ring maps. The datum and weight group are unchanged.
-/

noncomputable section
namespace OddMath.SKM.ScalarChange
open CategoryTheory StringDiagrams Presentation
universe u v w w'
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {R : Type w} {S : Type w'} [CommRing R] [CommRing S]
  (f : R →+* S)

/-- Specialization of the full polynomial/exterior coefficient algebra.
In particular, odd generators are retained, not projected away. -/
def symMap : SYM D R →+* SYM D S := by
  letI : Algebra R (SYM D S) := Algebra.compHom _ f
  let gen : SYMGen D → SYM D S := SYM.ι D S
  have rel {x y : FreeAlgebra R (SYMGen D)} (h : SYMRel D R x y) :
      FreeAlgebra.lift R gen x = FreeAlgebra.lift R gen y := by
    cases h with
    | polynomial a b =>
        simpa only [map_mul, FreeAlgebra.lift_ι_apply, gen, SYM.e] using
          (SYM.e_commute D S a.1 b.1 a.2 b.2).eq
    | mixed a i =>
        simpa only [map_mul, FreeAlgebra.lift_ι_apply, gen, SYM.e, SYM.delta] using
          (SYM.e_delta_commute D S a.1 a.2 i).eq
    | exterior i j =>
        simpa only [map_mul, map_neg, FreeAlgebra.lift_ι_apply, gen, SYM.delta] using
          SYM.delta_anticommute D S i j
    | square i =>
        simpa only [map_pow, map_zero, FreeAlgebra.lift_ι_apply, gen, SYM.delta] using
          SYM.delta_sq D S i
  exact (RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R gen, fun _ _ h => rel h⟩).toRingHom

@[simp] theorem symMap_ι (g : SYMGen D) :
    symMap (D := D) f (SYM.ι D R g) = SYM.ι D S g := by
  simp [symMap, SYM.ι, SYM.mk]

@[simp] theorem symMap_e (i : I) (n : ℕ) :
    symMap (D := D) f (SYM.e D R i n) = SYM.e D S i n :=
  symMap_ι f (.inl (i, n))

@[simp] theorem symMap_delta (i : {i : I // D.parity i = 1}) :
    symMap (D := D) f (SYM.delta D R i) = SYM.delta D S i :=
  symMap_ι f (.inr i)

/-- Every dotted or fake left bubble specializes with its prescribed normalization. -/
theorem homMap_bubL {Sc : Scalars D R} (cs : CScalars Sc)
    (i : I) (μ : X) (n : ℤ) :
    homMap f D Sc _ _ (bubL cs i μ n) =
      bubL (cScalars D f cs) i μ n := by
  unfold bubL
  split_ifs <;> simp [cScalars, zsign]
  split_ifs
  all_goals simp

/-- Every dotted or fake right bubble specializes with its inverse unit. -/
theorem homMap_bubR {Sc : Scalars D R} (cs : CScalars Sc)
    (i : I) (μ : X) (n : ℤ) :
    homMap f D Sc _ _ (bubR cs i μ n) =
      bubR (cScalars D f cs) i μ n := by
  unfold bubR
  split_ifs <;> simp [cScalars, zsign]
  split_ifs
  all_goals simp

@[simp] theorem homMap_bubLs {Sc : Scalars D R} (cs : CScalars Sc)
    (i : I) (μ : X) (n : ℤ) :
    homMap f D Sc _ _ (bubLs cs i μ n) =
      bubLs (cScalars D f cs) i μ n :=
  homMap_bubL f cs i μ _

@[simp] theorem homMap_oddBubble {Sc : Scalars D R} (cs : CScalars Sc)
    (i : I) (μ : X) :
    homMap f D Sc _ _ (oddBubble cs i μ) =
      oddBubble (cScalars D f cs) i μ := by
  unfold oddBubble
  split_ifs <;> simp [homMap_bubL, homMap_bubR, cScalars]

/-- The two generator families, including the odd bubble, commute with specialization. -/
theorem homMap_betaSYMGen {Sc : Scalars D R} (cs : CScalars Sc)
    (μ : X) (g : SYMGen D) :
    homMap f D Sc _ _ (betaSYMGen cs μ g) =
      betaSYMGen (cScalars D f cs) μ g := by
  cases g with
  | inl a =>
      rcases a with ⟨i, n⟩
      simp only [betaSYMGen]
      split_ifs <;> simp [betaGen, betaDGen, homMap_bubLs]
  | inr i => exact homMap_oddBubble f cs i μ

/-- Coefficient change is multiplicative on closed diagrams, with the
`End` multiplication convention (`x * y = y ≫ x`). -/
def endMap {Sc : Scalars D R} (μ : X) :
    End ((pres D Sc).obj (ob D μ [])) →+*
      End ((pres D (scalars D f Sc)).obj (ob D μ [])) where
  toFun x := homMap f D Sc _ _ x
  map_one' := homMap_id f D Sc _
  map_mul' x y := by
    change homMap f D Sc _ _ (y ≫ x) =
      homMap f D Sc _ _ y ≫ homMap f D Sc _ _ x
    exact homMap_comp f D Sc y x
  map_zero' := (homMap f D Sc _ _).map_zero
  map_add' := (homMap f D Sc _ _).map_add

/-- The coefficient embedding follows the specified ground-ring map. -/
theorem symMap_algebraMap (r : R) :
    symMap (D := D) f (algebraMap R (SYM D R) r) =
      algebraMap S (SYM D S) (f r) := by
  let : Algebra R (SYM D S) := Algebra.compHom _ f
  rw [← (SYM.mk D R).commutes r]
  simp [symMap, SYM.mk]
  exact Algebra.compHom_algebraMap_apply (SYM D S) f r

/-- The full all-colour bubble evaluation commutes with specialization,
including products of exterior generators and arbitrary finite expressions. -/
theorem homMap_betaSYM {Sc : Scalars D R} (cs : CScalars Sc)
    (μ : X) (p : SYM D R) :
    homMap f D Sc _ _ (betaSYM cs μ p) =
      betaSYM (cScalars D f cs) μ (symMap (D := D) f p) := by
  obtain ⟨q, rfl⟩ := RingQuot.mkAlgHom_surjective R (SYMRel D R) p
  induction q using FreeAlgebra.induction with
  | grade0 r =>
      simp only [AlgHom.commutes, symMap_algebraMap, AlgHom.commutes]
      simp [Algebra.algebraMap_eq_smul_one]
  | grade1 g =>
      change homMap f D Sc _ _ (betaSYM cs μ (SYM.ι D R g)) =
        betaSYM (cScalars D f cs) μ (symMap (D := D) f (SYM.ι D R g))
      rw [symMap_ι, betaSYM_ι, betaSYM_ι, homMap_betaSYMGen]
  | mul p q hp hq =>
      simp only [map_mul]
      exact (endMap f μ).map_mul _ _ ▸ congrArg₂ (· * ·) hp hq
  | add p q hp hq =>
      simp only [map_add]
      exact congrArg₂ (· + ·) hp hq

/-- The tensor comparison sends every source bubble coefficient to the
specialized bubble coefficient, without a flatness or basis assumption. -/
theorem homBaseChange_betaSYM {Sc : Scalars D R} (cs : CScalars Sc)
    (μ : X) (s : S) (p : SYM D R) :
    letI := f.toAlgebra
    homBaseChange f D Sc (ob D μ []) (ob D μ []) (s ⊗ₜ[R] betaSYM cs μ p) =
      s • betaSYM (cScalars D f cs) μ (symMap (D := D) f p) := by
  let := f.toAlgebra
  rw [homBaseChange_tmul, homMap_betaSYM]

end OddMath.SKM.ScalarChange
