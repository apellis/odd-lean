import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorDotObservation
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorCrossObservation
import OddMath.QuiverHecke.SwappedAssembly.VacuumPathSplit

/-! # Layer squares of the quotient observation on arbitrary presented objects

SwappedVacuumCoordinates §§5–7. The dot and crossing layer observations
(`tensorMatrixQuotientObservation_dot`, `_sameCross`, `_cross`) are stated on the
literal source and target objects of an SKM layer, with the vacuum path assembled
from its pieces. Here they are restated for arbitrary objects equal to the layer
boundary, arbitrary upward vacuum paths, and target words named by arbitrary outer
contexts `ℓ`, `r`: the vacuum path splits through the layer
(`SPath.split_three`), its generator part is a reservoir step, and the observed
classes are read through the target-word quotient transports.

This is the form consumed by a vacuum corner evaluation, where the objects are the
word objects `ob μ (upWord t)` of a presented layer of `H`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorLayerSquaresHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C

/-- The target-word quotient transports compose to the identity. -/
theorem tensorTargetWordQuotientEquiv_cancel {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : Datum I X) (Sc : Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ) (s : List I)
    {t r : List I} (h : t = r) (h' : r = t) (z) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s h'
      (tensorTargetWordQuotientEquiv D Sc cutoff L s h z) = z := by
  subst h
  rfl

/-- Two distinct upward reservoir steps commute. -/
theorem SPath.cross_steps {I : Type u} [DecidableEq I] {i j : I} (hij : i ≠ j) {c : I →₀ ℕ}
    (hv₁ : StepValid (true,i) false (0,c))
    (hv₂ : StepValid (true,j) false (nextSector (true,i) false (0,c))) :
    StepValid (true,j) false (0,c) ∧
      StepValid (true,i) false (nextSector (true,j) false (0,c)) ∧
      nextSector (true,j) false (nextSector (true,i) false (0,c)) =
        nextSector (true,i) false (nextSector (true,j) false (0,c)) := by
  simp only [StepValid, nextSector] at hv₁ hv₂ ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finsupp.single_apply, hij] using hv₂
  · simpa [Finsupp.single_apply, Ne.symm hij] using hv₁
  · rw [tsub_right_comm]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "Tw" => parameterTwist D Sc
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s
local notation "colApp" =>
  @HAppend.hAppend (List (Col I X)) (List (Col I X)) (List (Col I X)) instHAppendOfAppend
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "Q" => interpretation D Sc m cutoff N ΛP ΛR hP hR
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)
local notation "E0" => (ΛP - contentWeight D (0 : I →₀ ℕ)) + (-ΛR + contentWeight D (0 : I →₀ ℕ))

/-- **Dot layer square on arbitrary boundary objects.** -/
theorem tensorMatrixQuotientObservation_dot_of_eq
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData)
    (ν : X) (u v : List (Letter I)) (i : I) {ℓ r : List I}
    (hℓ : List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.left (SKM.lay D ν u (SKM.Shape.dot i) v)))) = ℓ)
    (hr : List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.right (SKM.lay D ν u (SKM.Shape.dot i) v)))) = r)
    {A B : Obj (SKM.sig D)} (hA : (SKM.lay D ν u (SKM.Shape.dot i) v).dom = A)
    (hB : (SKM.lay D ν u (SKM.Shape.dot i) v).cod = B)
    (hEA : E0 = A.endR) (hEB : E0 = B.endR)
    (pA : SPath A.word (0,cS) (0,0)) (hupA : ∀ c ∈ A.word, c.l.1 = true)
    (pB : SPath B.word (0,cS) (0,0)) (hupB : ∀ c ∈ B.word, c.l.1 = true)
    (hwA : A.word.map (fun a : Col I X => a.l.2) = ℓ ++ [i] ++ r)
    (hwB : B.word.map (fun a : Col I X => a.l.2) = ℓ ++ [i] ++ r)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) A)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (ℓ ++ [i] ++ r))
    (hy : tensorTargetWordQuotientEquiv D Sc cutoff L s hwA
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEA pA hupA x) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (ℓ ++ [i] ++ r)).mkQ y) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s hwB
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEB pB hupB
          (((Q ((P).swappedGens a leftward)).res B)
            ((Q ((P).swappedGens a leftward)).op (SKM.lay D ν u (SKM.Shape.dot i) v)
              ((Q ((P).swappedGens a leftward)).ext A x)))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (ℓ ++ [i] ++ r)).mkQ
        (y ≫ sourceCoefficientHom D Sc 1
          (ContextualOldGenerators.layerDiagram D Sc ℓ (.dot i) r)) := by
  subst hA hB hℓ hr
  obtain ⟨c, c', ⟨pL⟩, ⟨pm⟩, ⟨pR⟩⟩ := SPath.split_three
    (l := (SKM.lay D ν u (SKM.Shape.dot i) v).left)
    (m := [Col.mk (up i) (SKM.wt D ν v)])
    (r := (SKM.lay D ν u (SKM.Shape.dot i) v).right) pA hupA
  obtain ⟨hv, rfl⟩ := SPath.single_up (i := i) rfl pm
  have hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).left, a.l.1 = true :=
    fun a ha => hupA a (List.mem_append_left _ (List.mem_append_left _ ha))
  have hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.dot i) v).right, a.l.1 = true :=
    fun a ha => hupA a (List.mem_append_right _ ha)
  obtain rfl := (SPath.subsingleton_of_upward_probe_zero hupA rfl).elim pA
    (SPath.append (SPath.append pL
      (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _))) pR)
  obtain rfl := (SPath.subsingleton_of_upward_probe_zero hupB rfl).elim pB
    (SPath.append (SPath.append pL
      (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false (0,c) hv (SPath.nil _))) pR)
  have hy' := (congrArg (tensorTargetWordQuotientEquiv D Sc cutoff L s
      (tensorDotLayer_domWord D ν u v i)) hy).symm.trans
    (tensorTargetWordQuotientEquiv_cancel D Sc cutoff L s hwA
      (tensorDotLayer_domWord D ν u v i) _)
  have key := tensorMatrixQuotientObservation_dot D Sc m cutoff ΛP ΛR L hP hR s
    ν u v i hv pL hl pR hr a leftward hEB hupA x y hy'.symm
  exact (congrArg (tensorTargetWordQuotientEquiv D Sc cutoff L s hwB) key).trans
    (tensorTargetWordQuotientEquiv_cancel D Sc cutoff L s
      (tensorDotLayer_codWord D ν u v i) hwB _)

/-- **Equal-colour crossing layer square on arbitrary boundary objects.** -/
theorem tensorMatrixQuotientObservation_sameCross_of_eq
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData)
    (ν : X) (u v : List (Letter I)) (i : I) {ℓ r : List I}
    (hℓ : List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.left (SKM.lay D ν u (SKM.Shape.cross i i) v)))) = ℓ)
    (hr : List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.right (SKM.lay D ν u (SKM.Shape.cross i i) v)))) = r)
    {A B : Obj (SKM.sig D)} (hA : (SKM.lay D ν u (SKM.Shape.cross i i) v).dom = A)
    (hB : (SKM.lay D ν u (SKM.Shape.cross i i) v).cod = B)
    (hEA : E0 = A.endR) (hEB : E0 = B.endR)
    (pA : SPath A.word (0,cS) (0,0)) (hupA : ∀ c ∈ A.word, c.l.1 = true)
    (pB : SPath B.word (0,cS) (0,0)) (hupB : ∀ c ∈ B.word, c.l.1 = true)
    (hwA : A.word.map (fun a : Col I X => a.l.2) = ℓ ++ [i, i] ++ r)
    (hwB : B.word.map (fun a : Col I X => a.l.2) = ℓ ++ [i, i] ++ r)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) A)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (ℓ ++ [i, i] ++ r))
    (hy : tensorTargetWordQuotientEquiv D Sc cutoff L s hwA
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEA pA hupA x) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (ℓ ++ [i, i] ++ r)).mkQ y) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s hwB
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEB pB hupB
          (((Q ((P).swappedGens a leftward)).res B)
            ((Q ((P).swappedGens a leftward)).op (SKM.lay D ν u (SKM.Shape.cross i i) v)
              ((Q ((P).swappedGens a leftward)).ext A x)))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (ℓ ++ [i, i] ++ r)).mkQ
        (y ≫ sourceCoefficientHom D Sc 1
          (ContextualOldGenerators.layerDiagram D Sc ℓ (.cross i i) r)) := by
  subst hA hB hℓ hr
  obtain ⟨c, c', ⟨pL⟩, ⟨pm⟩, ⟨pR⟩⟩ := SPath.split_three
    (l := (SKM.lay D ν u (SKM.Shape.cross i i) v).left)
    (m := [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i]), Col.mk (up i) (SKM.wt D ν v)])
    (r := (SKM.lay D ν u (SKM.Shape.cross i i) v).right) pA hupA
  obtain ⟨hv, hw, rfl⟩ := SPath.two_up (i := i) (j := i) rfl rfl pm
  have hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i i) v).left, a.l.1 = true :=
    fun a ha => hupA a (List.mem_append_left _ (List.mem_append_left _ ha))
  have hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i i) v).right, a.l.1 = true :=
    fun a ha => hupA a (List.mem_append_right _ ha)
  obtain rfl := (SPath.subsingleton_of_upward_probe_zero hupA rfl).elim pA
    (SPath.append (SPath.append pL
      (SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i])) false (0,c) hv
        (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _)))) pR)
  obtain rfl := (SPath.subsingleton_of_upward_probe_zero hupB rfl).elim pB
    (SPath.append (SPath.append pL
      (SPath.cons (Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up i])) false (0,c) hv
        (SPath.cons (Col.mk (up i) (SKM.wt D ν v)) false _ hw (SPath.nil _)))) pR)
  have hy' := (congrArg (tensorTargetWordQuotientEquiv D Sc cutoff L s
      (tensorSameCrossLayer_domWord D ν u v i)) hy).symm.trans
    (tensorTargetWordQuotientEquiv_cancel D Sc cutoff L s hwA
      (tensorSameCrossLayer_domWord D ν u v i) _)
  have key := tensorMatrixQuotientObservation_sameCross D Sc m cutoff ΛP ΛR L hP hR s
    ν u v i hv hw pL hl pR hr a leftward hEB hupA x y hy'.symm
  exact (congrArg (tensorTargetWordQuotientEquiv D Sc cutoff L s hwB) key).trans
    (tensorTargetWordQuotientEquiv_cancel D Sc cutoff L s
      (tensorSameCrossLayer_codWord D ν u v i) hwB _)

/-- **Distinct-colour crossing layer square on arbitrary boundary objects.** -/
theorem tensorMatrixQuotientObservation_cross_of_eq [DecidableEq I]
    (a : (P).CrossCoeff) (leftward : (P).LeftwardData)
    (ν : X) (u v : List (Letter I)) (i j : I) (hij : i ≠ j) {ℓ r : List I}
    (hℓ : List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.left (SKM.lay D ν u (SKM.Shape.cross i j) v)))) = ℓ)
    (hr : List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.right (SKM.lay D ν u (SKM.Shape.cross i j) v)))) = r)
    {A B : Obj (SKM.sig D)} (hA : (SKM.lay D ν u (SKM.Shape.cross i j) v).dom = A)
    (hB : (SKM.lay D ν u (SKM.Shape.cross i j) v).cod = B)
    (hEA : E0 = A.endR) (hEB : E0 = B.endR)
    (pA : SPath A.word (0,cS) (0,0)) (hupA : ∀ c ∈ A.word, c.l.1 = true)
    (pB : SPath B.word (0,cS) (0,0)) (hupB : ∀ c ∈ B.word, c.l.1 = true)
    (hwA : A.word.map (fun a : Col I X => a.l.2) = ℓ ++ [i, j] ++ r)
    (hwB : B.word.map (fun a : Col I X => a.l.2) = ℓ ++ [j, i] ++ r)
    (x : matrixModule D Sc m cutoff N ΛP ΛR
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L) A)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc (ℓ ++ [i, j] ++ r))
    (hy : tensorTargetWordQuotientEquiv D Sc cutoff L s hwA
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEA pA hupA x) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (ℓ ++ [i, j] ++ r)).mkQ y) :
    tensorTargetWordQuotientEquiv D Sc cutoff L s hwB
        (tensorMatrixQuotientObservation D Sc m cutoff ΛP ΛR L hP hR s hEB pB hupB
          (((Q ((P).swappedGens a leftward)).res B)
            ((Q ((P).swappedGens a leftward)).op (SKM.lay D ν u (SKM.Shape.cross i j) v)
              ((Q ((P).swappedGens a leftward)).ext A x)))) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s (ℓ ++ [j, i] ++ r)).mkQ
        (y ≫ sourceCoefficientHom D Sc 1
          (ContextualOldGenerators.layerDiagram D Sc ℓ (.cross i j) r)) := by
  subst hA hB hℓ hr
  obtain ⟨c, c', ⟨pL⟩, ⟨pm⟩, ⟨pR⟩⟩ := SPath.split_three
    (l := (SKM.lay D ν u (SKM.Shape.cross i j) v).left)
    (m := [Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]), Col.mk (up j) (SKM.wt D ν v)])
    (r := (SKM.lay D ν u (SKM.Shape.cross i j) v).right) pA hupA
  obtain ⟨hv₁, hv₂, rfl⟩ := SPath.two_up (i := i) (j := j) rfl rfl pm
  obtain ⟨hw₁, hw₂, hs⟩ := SPath.cross_steps hij hv₁ hv₂
  have hc : c - Finsupp.single i 1 - Finsupp.single j 1 =
      c - Finsupp.single j 1 - Finsupp.single i 1 := tsub_right_comm
  rw [hc] at pR
  have hl : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i j) v).left, a.l.1 = true :=
    fun a ha => hupA a (List.mem_append_left _ (List.mem_append_left _ ha))
  have hr : ∀ a ∈ (SKM.lay D ν u (SKM.Shape.cross i j) v).right, a.l.1 = true :=
    fun a ha => hupA a (List.mem_append_right _ ha)
  obtain rfl := (SPath.subsingleton_of_upward_probe_zero hupA rfl).elim pA
    (SPath.append (SPath.append pL
      (SPath.two (c₁ := Col.mk (up i) (SKM.wt D (SKM.wt D ν v) [up j]))
        (c₂ := Col.mk (up j) (SKM.wt D ν v)) false false hv₁ hv₂ hs)) pR)
  obtain rfl := (SPath.subsingleton_of_upward_probe_zero hupB rfl).elim pB
    (SPath.append (SPath.append pL
      (SPath.two (c₁ := Col.mk (up j) (SKM.wt D (SKM.wt D ν v) [up i]))
        (c₂ := Col.mk (up i) (SKM.wt D ν v)) false false hw₁ hw₂ rfl)) pR)
  have hy' := (congrArg (tensorTargetWordQuotientEquiv D Sc cutoff L s
      (tensorCrossLayer_domWord D ν u v i j)) hy).symm.trans
    (tensorTargetWordQuotientEquiv_cancel D Sc cutoff L s hwA
      (tensorCrossLayer_domWord D ν u v i j) _)
  have key := tensorMatrixQuotientObservation_cross D Sc m cutoff ΛP ΛR L hP hR s
    ν u v i j hv₁ hv₂ hw₁ hw₂ hs pL hl pR hr hij a leftward hEB hupA hupB x y hy'.symm
  exact (congrArg (tensorTargetWordQuotientEquiv D Sc cutoff L s hwB) key).trans
    (tensorTargetWordQuotientEquiv_cancel D Sc cutoff L s
      (tensorCrossLayer_codWord D ν u v i j) hwB _)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
