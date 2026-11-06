import OddMath.QuiverHecke.SwappedAssembly.Supernatural.RestrictedLeftward
import OddMath.QuiverHecke.SwappedAssembly.SupportedAugmentedInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedInterchange

/-! # Supernaturality and interchange on the supported Hom inputs

The retained-input attachment in `SwappedActionAssembly.md` §3 and
(A7): the conditional raw leftward entries are homogeneous and natural
on the full supported input categories, by inverse uniqueness there.
The resulting native layer representation satisfies super interchange.
The unequal-colour permutation input remains explicit at this step.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ProbeReservoir
universe u
local instance supportedNaturalityHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "Q" => retainedInput D Sc m cutoff bound ΛP ΛR hP hR

/-- The full inclusion of exactly the retained raw Hom inputs. -/
abbrev retainedInclusion (s : Sector I) : (Q s).FullSubcategory ⥤ (P).H s :=
  (Q s).ι

instance retainedInclusion_additive (s : Sector I) :
    (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s).Additive :=
  inferInstanceAs (((Q s).ι).Additive)

instance retainedInclusion_linear (s : Sector I) :
    (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s).Linear k :=
  inferInstanceAs (((Q s).ι).Linear k)

instance retainedInclusion_super (s : Sector I) :
    IsSuperfunctor k (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s) where
  map_mem hf := hf

variable [Finite I] (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound)
  (hwin : ReservoirWindowIdeal D Sc m cutoff bound ΛP ΛR hP hR)
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hdot
local notation "L" => pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR hdot

include hwin in
/-- The chosen equal-colour crossing is supernatural on every retained input. -/
theorem pointwiseLeftward_lcrossSame_supernatural (i : I) (ν : X) {t s : Sector I}
    (q : SPath (wd D ν [dn i,up i]) t s) (p : SPath (wd D ν [up i,dn i]) t s) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s ⋙ (P).pathFunctor q)
      (G := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s ⋙ (P).pathFunctor p)
      (fun Z => (L).lcrossSame i ν q p Z.obj) := by
  by_cases hw : (P).wt s = ν
  · have hC := elvProbeCrossCoeffOf_isSupernatural D Sc m cutoff bound ΛP ΛR hP hR
        hdot
    by_cases hh : 0 ≤ D.h i ν
    · exact (leftward_supernatural_of_posInverseAt_comp c L hC i ν t s
        (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s)
        (fun Z => pointwiseLeftward_posInverseAt D Sc m cutoff bound ΛP ΛR hP hR
          hdot hwin i ν t s Z hw hh)).1 q p
    · exact (leftward_supernatural_of_negInverseAt_comp c L hC i ν t s
        (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s)
        (fun Z => pointwiseLeftward_negInverseAt D Sc m cutoff bound ΛP ΛR hP hR
          hdot hwin i ν t s Z hw (not_le.mp hh))).1 q p
  · have he (Z : (Q s).FullSubcategory) : (L).lcrossSame i ν q p Z.obj = 0 :=
      (pointwiseLeftwardData_vanishesOffWeight D Sc m cutoff bound ΛP ΛR hP hR
        hdot).1
        i ν q p Z.obj hw
    simp only [he]
    exact isSupernatural_zero _

include hwin in
/-- The chosen diamond cups have the required homogeneous naturality on retained inputs. -/
theorem pointwiseLeftward_dcup_supernatural (i : I) (n : ℕ) (ν : X)
    (hn : (n : ℤ) < D.h i ν) {t s : Sector I}
    (r : SPath (wd D ν []) t s) (p : SPath (wd D ν [up i,dn i]) t s) :
    IsSupernatural k (D.parity i * (n : ZMod 2))
      (F := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s ⋙ (P).pathFunctor r)
      (G := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s ⋙ (P).pathFunctor p)
      (fun Z => (L).dcup i n ν r p Z.obj) := by
  by_cases hw : (P).wt s = ν
  · have hh : 0 ≤ D.h i ν := by omega
    have hC := elvProbeCrossCoeffOf_isSupernatural D Sc m cutoff bound ΛP ΛR hP hR
        hdot
    exact IsSupernatural.of_parity_eq
      ((leftward_supernatural_of_posInverseAt_comp c L hC i ν t s
        (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s)
        (fun Z => pointwiseLeftward_posInverseAt D Sc m cutoff bound ΛP ΛR hP hR
          hdot hwin i ν t s Z hw hh)).2 ⟨n,Int.lt_toNat.mpr hn⟩ r p) (mul_comm _ _)
  · have he (Z : (Q s).FullSubcategory) : (L).dcup i n ν r p Z.obj = 0 :=
      (pointwiseLeftwardData_vanishesOffWeight D Sc m cutoff bound ΛP ΛR hP hR
        hdot).2.1
        i n ν r p Z.obj hw
    simp only [he]
    exact isSupernatural_zero _

include hwin in
/-- The chosen diamond caps have the required homogeneous naturality on retained inputs. -/
theorem pointwiseLeftward_dcap_supernatural (i : I) (n : ℕ) (ν : X)
    (hn : (n : ℤ) < -D.h i ν) {t s : Sector I}
    (q : SPath (wd D ν [dn i,up i]) t s) (r : SPath (wd D ν []) t s) :
    IsSupernatural k (D.parity i * (n : ZMod 2))
      (F := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s ⋙ (P).pathFunctor q)
      (G := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s ⋙ (P).pathFunctor r)
      (fun Z => (L).dcap i n ν q r Z.obj) := by
  by_cases hw : (P).wt s = ν
  · have hh : D.h i ν < 0 := by omega
    have hC := elvProbeCrossCoeffOf_isSupernatural D Sc m cutoff bound ΛP ΛR hP hR
        hdot
    exact IsSupernatural.of_parity_eq
      ((leftward_supernatural_of_negInverseAt_comp c L hC i ν t s
        (retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s)
        (fun Z => pointwiseLeftward_negInverseAt D Sc m cutoff bound ΛP ΛR hP hR
          hdot hwin i ν t s Z hw hh)).2 ⟨n,Int.lt_toNat.mpr hn⟩ q r) (mul_comm _ _)
  · have he (Z : (Q s).FullSubcategory) : (L).dcap i n ν q r Z.obj = 0 :=
      (pointwiseLeftwardData_vanishesOffWeight D Sc m cutoff bound ΛP ΛR hP hR
        hdot).2.2
        i n ν q r Z.obj hw
    simp only [he]
    exact isSupernatural_zero _

include hwin in
/-- All chosen swapped generators are supernatural after the retained full inclusions. -/
theorem pointwiseLeftward_generatorsSupernaturalOn
    (hσ : ∀ i j : I, i ≠ j → ∀ ν : X, (P).SigmaPermutation c i j ν) :
    GeneratorsSupernaturalOn Q ((P).swappedGens c L) := by
  rintro ⟨g,ν⟩ t s p p'
  have hC := elvProbeCrossCoeffOf_isSupernatural D Sc m cutoff bound ΛP ΛR hP hR
    hdot
  let J := retainedInclusion D Sc m cutoff bound ΛP ΛR hP hR s
  cases g with
  | dot i => exact ((P).dotImage_supernatural i ν p p').whiskerLeft J
  | cross i j => exact ((P).crossImage_supernatural c hC i j ν p p').whiskerLeft J
  | cup i => exact ((P).cupImage_supernatural i ν p p').whiskerLeft J
  | cap i => exact ((P).capImage_supernatural i ν p p').whiskerLeft J
  | lcross i j =>
    by_cases hij : i = j
    · subst j
      have he (Z : (Q s).FullSubcategory) :
          ((P).swappedGens c L).image (.lcross i i,ν) p p' Z.obj =
            (L).lcrossSame i ν p p' Z.obj := (P).swappedGens_lcross_self c L i ν p p' Z.obj
      simp only [he]
      exact pointwiseLeftward_lcrossSame_supernatural D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i ν p p'
    · have he (Z : (Q s).FullSubcategory) :
          ((P).swappedGens c L).image (.lcross i j,ν) p p' Z.obj =
            (P).lcrossNeImage c i j ν p p' Z.obj := (P).swappedGens_lcross_of_ne c L hij ν p p' Z.obj
      simp only [he]
      exact (lcrossNeImage_supernatural c hC i j ν (hσ i j hij ν) p p').whiskerLeft J
  | dcup i n =>
    by_cases hn : D.h i ν ≤ n
    · have he (Z : (Q s).FullSubcategory) :
          ((P).swappedGens c L).image (.dcup i n,ν) p p' Z.obj = 0 := by
        simp [Generators.image,swappedGens,hn]
      simp only [he]
      exact isSupernatural_zero _
    · have he (Z : (Q s).FullSubcategory) :
          ((P).swappedGens c L).image (.dcup i n,ν) p p' Z.obj =
            (L).dcup i n ν p p' Z.obj := (P).swappedGens_dcup_of_lt c L i n ν (not_le.mp hn) p p' Z.obj
      simp only [he]
      exact pointwiseLeftward_dcup_supernatural D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i n ν
        (not_le.mp hn) p p'
  | dcap i n =>
    by_cases hn : -D.h i ν ≤ n
    · have he (Z : (Q s).FullSubcategory) :
          ((P).swappedGens c L).image (.dcap i n,ν) p p' Z.obj = 0 := by
        simp [Generators.image,swappedGens,hn]
      simp only [he]
      exact isSupernatural_zero _
    · have he (Z : (Q s).FullSubcategory) :
          ((P).swappedGens c L).image (.dcap i n,ν) p p' Z.obj =
            (L).dcap i n ν p p' Z.obj := (P).swappedGens_dcap_of_lt c L i n ν (not_le.mp hn) p p' Z.obj
      simp only [he]
      exact pointwiseLeftward_dcap_supernatural D Sc m cutoff bound ΛP ΛR hP hR hdot hwin i n ν
        (not_le.mp hn) p p'

include hwin in
/-- The original native layer representation satisfies interchange on the
chosen supported inputs, with only the unequal-colour permutation input explicit. -/
theorem pointwiseLeftward_interchangeLaw
    (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (hσ : ∀ i j : I, i ≠ j → ∀ ν : X, (P).SigmaPermutation c i j ν) :
    InterchangeLaw ((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
      ((P).swappedGens c L)) :=
  ProbeReservoir.interchangeLaw_on Q (retainedInput_path D Sc m cutoff bound ΛP ΛR hP hR)
    (fun s => (Gs s).obj) (fun s => (Ys s).obj) (fun s => (Ys s).property)
    (pointwiseLeftward_generatorsSupernaturalOn D Sc m cutoff bound ΛP ΛR hP hR hdot hwin hσ)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
