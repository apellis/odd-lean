/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.FiniteColourClassDetection
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.SpanBubbleProd

/-!
# Bubbles under finite-colour restriction

Brundan–Ellis, *Super Kac–Moody 2-categories*, (1.21)–(1.22) and Definition 1.5, as used
in `SwappedActionAssembly`, §8. Every generator image `betaSYMGen` of the all-colour bubble
homomorphism is written as an explicit finite formal sum of classes of normal-form layer
lists (`genS`). The formal sums are given by the same formula for every datum, so the
formal sum of a restricted generator includes onto the formal sum of the generator itself
(`pushS_genS`). Composition and rightmost placement of formal sums
(`compS`, `whS`) commute with inclusion as well.

No functor between presented categories is used: these comparisons are statements about
free formal sums, evaluated in each presentation separately by `evS`.
-/

noncomputable section
namespace OddMath.SKM.FiniteColour
open CategoryTheory StringDiagrams
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} (J : Finset I)
variable {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Formal sums of classes -/

variable (D Sc) in
/-- The value of a formal sum of layer lists between normal-form words. -/
def evS (μ : X) (s t : List (Letter I)) (L : List (k × List (LayerData I))) :
    (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t) :=
  (L.map fun p => p.1 • cl D Sc μ s t p.2).sum

/-- Inclusion of formal sums, layer list by layer list. -/
def pushS (L : List (k × List (LayerData J))) : List (k × List (LayerData I)) :=
  L.map fun p => (p.1, p.2.map (layerData J))

/-- The formal composite: `cl s t A ≫ cl t r B` is `cl s r (A ++ B)` when `A` chains from
`s` to `t`, and zero otherwise. -/
def compS (s t : List (Letter I)) (L M : List (k × List (LayerData I))) :
    List (k × List (LayerData I)) :=
  L.flatMap fun p => M.map fun q => (if SChain s p.2 t then p.1 * q.1 else 0, p.2 ++ q.2)

/-- Scalar multiplication of a formal sum. -/
def smulS (a : k) (L : List (k × List (LayerData I))) : List (k × List (LayerData I)) :=
  L.map fun p => (a * p.1, p.2)

/-- Placement to the right of the strands `v`. -/
def whS (v : List (Letter I)) (L : List (k × List (LayerData I))) :
    List (k × List (LayerData I)) :=
  L.map fun p => (p.1, p.2.map (whL v []))

variable (D Sc) in
@[simp] theorem evS_nil (μ : X) (s t : List (Letter I)) :
    evS D Sc μ s t ([] : List (k × List (LayerData I))) = 0 := rfl

variable (D Sc) in
@[simp] theorem evS_cons (μ : X) (s t : List (Letter I)) (p : k × List (LayerData I))
    (L : List (k × List (LayerData I))) :
    evS D Sc μ s t (p :: L) = p.1 • cl D Sc μ s t p.2 + evS D Sc μ s t L := by
  simp [evS]

variable (D Sc) in
theorem evS_append (μ : X) (s t : List (Letter I)) (L M : List (k × List (LayerData I))) :
    evS D Sc μ s t (L ++ M) = evS D Sc μ s t L + evS D Sc μ s t M := by
  simp [evS]

variable (D Sc) in
theorem evS_smulS (μ : X) (s t : List (Letter I)) (a : k) (L : List (k × List (LayerData I))) :
    evS D Sc μ s t (smulS a L) = a • evS D Sc μ s t L := by
  induction L with
  | nil => simp [smulS]
  | cons p L ih =>
    simp only [smulS, List.map_cons] at ih ⊢
    rw [evS_cons, evS_cons, ih, smul_add, smul_smul]

variable (D Sc) in
/-- Composition of classes, with no chain hypothesis. -/
theorem cl_comp_cl (μ : X) (s t r : List (Letter I)) (A B : List (LayerData I)) :
    cl D Sc μ s t A ≫ cl D Sc μ t r B =
      (if SChain s A t then (1 : k) else 0) • cl D Sc μ s r (A ++ B) := by
  by_cases hA : SChain s A t
  · simp only [hA, ↓reduceIte, one_smul]
    by_cases hB : SChain t B r
    · exact cl_comp hA hB
    · rw [cl_of_not hB, Limits.comp_zero, cl_of_not]
      intro h
      obtain ⟨a, h₁, h₂⟩ := h.split
      exact hB ((hA.eq_target h₁) ▸ h₂)
  · simp only [hA, ↓reduceIte, zero_smul, cl_of_not hA, Limits.zero_comp]

variable (D Sc) in
theorem evS_map_comp (μ : X) (s t r : List (Letter I)) (p : k × List (LayerData I))
    (M : List (k × List (LayerData I))) :
    evS D Sc μ s r (M.map fun q => (if SChain s p.2 t then p.1 * q.1 else 0, p.2 ++ q.2)) =
      (p.1 • cl D Sc μ s t p.2) ≫ evS D Sc μ t r M := by
  induction M with
  | nil => simp
  | cons q M ihM =>
    rw [List.map_cons, evS_cons, evS_cons, ihM, Preadditive.comp_add]
    congr 1
    rw [Linear.comp_smul, Linear.smul_comp, cl_comp_cl, smul_smul, smul_smul]
    dsimp only
    congr 1
    split_ifs <;> ring

variable (D Sc) in
theorem evS_compS (μ : X) (s t r : List (Letter I)) (L M : List (k × List (LayerData I))) :
    evS D Sc μ s r (compS s t L M) = evS D Sc μ s t L ≫ evS D Sc μ t r M := by
  induction L with
  | nil => simp [compS]
  | cons p L ih =>
    simp only [compS, List.flatMap_cons] at ih ⊢
    rw [evS_append, ih, evS_cons, Preadditive.add_comp, evS_map_comp]

variable (D Sc) in
theorem evS_whS (μ : X) (v : List (Letter I)) (L : List (k × List (LayerData I))) :
    evS D Sc μ v v (whS v L) = bubAt D Sc μ v (evS D Sc μ [] [] L) := by
  induction L with
  | nil => simp [whS]
  | cons p L ih =>
    simp only [whS, List.map_cons] at ih ⊢
    rw [evS_cons, evS_cons, ih, map_add, map_smul, bubAt_cl]

variable (D Sc) in
theorem evS_one (μ : X) (s : List (Letter I)) :
    evS D Sc μ s s [((1 : k), ([] : List (LayerData I)))] = 𝟙 _ := by
  rw [evS_cons, evS_nil, add_zero, one_smul, cl_nil]

/-! ## Inclusion of formal sums -/

omit [CommRing k] in
@[simp] theorem pushS_nil : pushS J ([] : List (k × List (LayerData J))) = [] := rfl

omit [CommRing k] in
@[simp] theorem pushS_cons (p : k × List (LayerData J)) (L : List (k × List (LayerData J))) :
    pushS J (p :: L) = (p.1, p.2.map (layerData J)) :: pushS J L := rfl

omit [CommRing k] in
theorem pushS_append (L M : List (k × List (LayerData J))) :
    pushS J (L ++ M) = pushS J L ++ pushS J M := List.map_append ..

theorem pushS_smulS (a : k) (L : List (k × List (LayerData J))) :
    pushS J (smulS a L) = smulS a (pushS J L) := by
  simp [pushS, smulS]

theorem pushS_compS (s t : List (Letter J)) (L M : List (k × List (LayerData J))) :
    pushS J (compS s t L M) = compS (s.map (letter J)) (t.map (letter J)) (pushS J L) (pushS J M) := by
  simp only [pushS, compS, List.map_flatMap, List.flatMap_map, List.map_map]
  refine List.flatMap_congr fun p _ => List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, chain_map_iff, List.map_append]

theorem layerData_whL (v : List (Letter J)) (x : LayerData J) :
    layerData J (whL v [] x) = whL (v.map (letter J)) [] (layerData J x) := by
  obtain ⟨a, g, b⟩ := x
  simp [layerData, whL]

omit [CommRing k] in
theorem pushS_whS (v : List (Letter J)) (L : List (k × List (LayerData J))) :
    pushS J (whS v L) = whS (v.map (letter J)) (pushS J L) := by
  simp only [pushS, whS, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [layerData_whL]

variable (D Sc) in
theorem evS_single (μ : X) (s t : List (Letter I)) (a : k) (A : List (LayerData I)) :
    evS D Sc μ s t [(a, A)] = a • cl D Sc μ s t A := by
  rw [evS_cons, evS_nil, add_zero]

/-! ## Generators as formal sums -/

/-- `η'` (2.10) as a formal sum. -/
def etaPS (i : I) (μ : X) : List (k × List (LayerData I)) :=
  if 0 < D.h i μ then [((cs.c μ i : k), dcupL i (D.h i μ - 1).toNat)]
  else [(zsign k (ipar D i μ) * (cs.c μ i : k), etaL i (-D.h i μ).toNat ++ lcrossL i i)]

/-- `ε'` (2.11) as a formal sum. -/
def epsPS (i : I) (μ : X) : List (k × List (LayerData I)) :=
  if D.h i μ < 0 then [((↑(cs.c μ i)⁻¹ : k), dcapL i (-D.h i μ - 1).toNat)]
  else [(-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k)),
    lcrossL i i ++ epsL i (D.h i μ).toNat)]

/-- The left bubble (2.13), (2.15) as a formal sum. -/
def bubLS (i : I) (μ : X) (n : ℤ) : List (k × List (LayerData I)) :=
  if 0 ≤ n then compS [] [up i, dn i] (etaPS cs i μ) [(1, epsL i n.toNat)]
  else if D.h i μ - 1 < n then
    [(-(zsign k (D.parity i * ((n + D.h i μ + 1 : ℤ) : ZMod 2))) * (cs.c μ i : k),
      etaL i (-D.h i μ).toNat ++ dcapL i (-n - 1).toNat)]
  else if n = D.h i μ - 1 then [((cs.c μ i : k), [])] else []

/-- The right bubble (2.14), (2.16) as a formal sum. -/
def bubRS (i : I) (μ : X) (n : ℤ) : List (k × List (LayerData I)) :=
  if 0 ≤ n then compS [] [dn i, up i] [(1, etaL i n.toNat)] (epsPS cs i μ)
  else if -D.h i μ - 1 < n then
    [(-(zsign k (D.parity i * ((n + D.h i μ + 1 : ℤ) : ZMod 2))) * (↑(cs.c μ i)⁻¹ : k),
      dcupL i (-n - 1).toNat ++ epsL i (D.h i μ).toNat)]
  else if n = -D.h i μ - 1 then [((↑(cs.c μ i)⁻¹ : k), [])] else []

/-- The odd bubble (2.18) as a formal sum. -/
def oddBubbleS (i : I) (μ : X) : List (k × List (LayerData I)) :=
  if 0 ≤ D.h i μ then smulS (↑(cs.c μ i)⁻¹ : k) (bubLS cs i μ (D.h i μ))
  else smulS (cs.c μ i : k) (bubRS cs i μ (-D.h i μ))

/-- The generator images of `betaSYM` as formal sums. -/
def genS (μ : X) : SYMGen D → List (k × List (LayerData I))
  | .inl (i, n) =>
    if D.parity i = 0 then smulS (↑(cs.c μ i)⁻¹ : k) (bubLS cs i μ ((n : ℤ) + 1 + D.h i μ - 1))
    else smulS (↑(cs.c μ i)⁻¹ : k) (bubLS cs i μ (2 * ((n : ℤ) + 1) + D.h i μ - 1))
  | .inr i => oddBubbleS cs i μ

theorem evS_etaPS (i : I) (μ : X) : evS D Sc μ [] [up i, dn i] (etaPS cs i μ) = etaP cs i μ := by
  unfold etaPS etaP
  split_ifs <;> rw [evS_single]

theorem evS_epsPS (i : I) (μ : X) : evS D Sc μ [dn i, up i] [] (epsPS cs i μ) = epsP cs i μ := by
  unfold epsPS epsP
  split_ifs <;> rw [evS_single]

theorem evS_bubLS (i : I) (μ : X) (n : ℤ) : evS D Sc μ [] [] (bubLS cs i μ n) = bubL cs i μ n := by
  unfold bubLS bubL
  split_ifs
  · rw [evS_compS, evS_etaPS, evS_single, one_smul]
  · rw [evS_single]
  · rw [evS_single, cl_nil]
  · rfl

theorem evS_bubRS (i : I) (μ : X) (n : ℤ) : evS D Sc μ [] [] (bubRS cs i μ n) = bubR cs i μ n := by
  unfold bubRS bubR
  split_ifs
  · rw [evS_compS, evS_epsPS, evS_single, one_smul]
  · rw [evS_single]
  · rw [evS_single, cl_nil]
  · rfl

theorem evS_oddBubbleS (i : I) (μ : X) :
    evS D Sc μ [] [] (oddBubbleS cs i μ) = oddBubble cs i μ := by
  unfold oddBubbleS oddBubble
  split_ifs <;> rw [evS_smulS] <;> simp only [evS_bubLS, evS_bubRS]

theorem evS_genS (μ : X) (g : SYMGen D) :
    evS D Sc μ [] [] (genS cs μ g) = betaSYMGen cs μ g := by
  rcases g with ⟨i, n⟩ | i
  · simp only [genS, betaSYMGen, betaGen, betaDGen, bubLs]
    split_ifs <;> rw [evS_smulS, evS_bubLS]
  · exact evS_oddBubbleS cs i μ

/-! ## Inclusion of the generators -/

/-- Inclusion of the generators of the coefficient algebra. -/
def genMap : SYMGen (D.restrictColours J) → SYMGen D
  | .inl (i, n) => .inl (i.val, n)
  | .inr i => .inr ⟨i.val.val, i.property⟩

/-! ## Inclusion of the generator layer lists -/

variable {J} in
theorem map_dotsL (u : List (Letter J)) (i : J) (v : List (Letter J)) (n : ℕ) :
    (dotsL u i v n).map (layerData J) = dotsL (u.map (letter J)) i.val (v.map (letter J)) n := by
  simp [dotsL, layerData, shape, List.map_replicate]

variable {J} in
theorem map_epsL (i : J) (n : ℕ) : (epsL i n).map (layerData J) = epsL i.val n := by
  simp [epsL, map_dotsL, layerData, shape, letter, dn]

variable {J} in
theorem map_etaL (i : J) (n : ℕ) : (etaL i n).map (layerData J) = etaL i.val n := by
  simp [etaL, map_dotsL, layerData, shape, letter, dn]

variable {J} in
theorem map_lcrossL (i j : J) : (lcrossL i j).map (layerData J) = lcrossL i.val j.val := rfl

variable {J} in
theorem map_dcupL (i : J) (n : ℕ) : (dcupL i n).map (layerData J) = dcupL i.val n := rfl

variable {J} in
theorem map_dcapL (i : J) (n : ℕ) : (dcapL i n).map (layerData J) = dcapL i.val n := rfl

variable {J} in
theorem pushS_etaPS (i : J) (μ : X) :
    pushS J (etaPS (cs.restrictColours D J Sc) i μ) = etaPS cs i.val μ := by
  have hh : (D.restrictColours J).h i μ = D.h i.val μ := rfl
  by_cases h : 0 < D.h i.val μ
  · simp only [etaPS, hh, h, ↓reduceIte, pushS, List.map_cons, List.map_nil, map_dcupL]; rfl
  · simp only [etaPS, hh, h, ↓reduceIte, pushS, List.map_cons, List.map_nil, List.map_append,
      map_etaL, map_lcrossL]; rfl

variable {J} in
theorem pushS_epsPS (i : J) (μ : X) :
    pushS J (epsPS (cs.restrictColours D J Sc) i μ) = epsPS cs i.val μ := by
  have hh : (D.restrictColours J).h i μ = D.h i.val μ := rfl
  by_cases h : D.h i.val μ < 0
  · simp only [epsPS, hh, h, ↓reduceIte, pushS, List.map_cons, List.map_nil, map_dcapL]; rfl
  · simp only [epsPS, hh, h, ↓reduceIte, pushS, List.map_cons, List.map_nil, List.map_append,
      map_lcrossL, map_epsL]; rfl


variable {J} in
theorem pushS_bubLS (i : J) (μ : X) (n : ℤ) :
    pushS J (bubLS (cs.restrictColours D J Sc) i μ n) = bubLS cs i.val μ n := by
  have hh : (D.restrictColours J).h i μ = D.h i.val μ := rfl
  unfold bubLS
  simp only [hh]
  split_ifs
  · rw [pushS_compS, pushS_etaPS]
    simp only [pushS, List.map_cons, List.map_nil, map_epsL]
    rfl
  · simp only [pushS, List.map_cons, List.map_nil, List.map_append, map_etaL, map_dcapL]
    rfl
  · rfl
  · rfl

variable {J} in
theorem pushS_bubRS (i : J) (μ : X) (n : ℤ) :
    pushS J (bubRS (cs.restrictColours D J Sc) i μ n) = bubRS cs i.val μ n := by
  have hh : (D.restrictColours J).h i μ = D.h i.val μ := rfl
  unfold bubRS
  simp only [hh]
  split_ifs
  · rw [pushS_compS, pushS_epsPS]
    simp only [pushS, List.map_cons, List.map_nil, map_etaL]
    rfl
  · simp only [pushS, List.map_cons, List.map_nil, List.map_append, map_dcupL, map_epsL]
    rfl
  · rfl
  · rfl

variable {J} in
theorem pushS_oddBubbleS (i : J) (μ : X) :
    pushS J (oddBubbleS (cs.restrictColours D J Sc) i μ) = oddBubbleS cs i.val μ := by
  have hh : (D.restrictColours J).h i μ = D.h i.val μ := rfl
  unfold oddBubbleS
  simp only [hh]
  split_ifs
  · rw [pushS_smulS, pushS_bubLS]; rfl
  · rw [pushS_smulS, pushS_bubRS]; rfl

/-- The generator formal sums commute with inclusion of colours. -/
theorem pushS_genS (μ : X) (g : SYMGen (D.restrictColours J)) :
    pushS J (genS (cs.restrictColours D J Sc) μ g) = genS cs μ (genMap J g) := by
  have hh : ∀ i : J, (D.restrictColours J).h i μ = D.h i.val μ := fun _ => rfl
  rcases g with ⟨i, n⟩ | ⟨i, hi⟩
  · have hp : (D.restrictColours J).parity i = D.parity i.val := rfl
    simp only [genS, genMap, hh, hp]
    split_ifs <;> rw [pushS_smulS, pushS_bubLS] <;> rfl
  · exact pushS_oddBubbleS cs i μ

/-! ## Words in the coefficient generators -/

/-- The formal sum of `betaSYM` applied to the product of a word of generators. -/
def wordS (μ : X) : List (SYMGen D) → List (k × List (LayerData I))
  | [] => [(1, [])]
  | g :: w => compS [] [] (wordS μ w) (genS cs μ g)

theorem evS_wordS (μ : X) (w : List (SYMGen D)) :
    evS D Sc μ [] [] (wordS cs μ w) = betaSYM cs μ ((w.map (SYM.ι D k)).prod) := by
  induction w with
  | nil => rw [wordS, evS_one, List.map_nil, List.prod_nil, map_one]; rfl
  | cons g w ih =>
    rw [wordS, evS_compS, ih, evS_genS, List.map_cons, List.prod_cons, map_mul, betaSYM_ι]
    rfl

theorem pushS_wordS (μ : X) (w : List (SYMGen (D.restrictColours J))) :
    pushS J (wordS (cs.restrictColours D J Sc) μ w) = wordS cs μ (w.map (genMap J)) := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    rw [wordS, pushS_compS, ih, pushS_genS, List.map_cons, wordS]
    rfl

/-- The colour of a coefficient generator. -/
def genColour : SYMGen D → I
  | .inl (i, _) => i
  | .inr i => i.val

/-- A generator whose colour lies in `J` comes from the restriction to `J`. -/
theorem exists_genMap_eq (g : SYMGen D) (hg : genColour g ∈ J) :
    ∃ g' : SYMGen (D.restrictColours J), genMap J g' = g := by
  rcases g with ⟨i, n⟩ | ⟨i, hi⟩
  · exact ⟨.inl (⟨i, hg⟩, n), rfl⟩
  · exact ⟨.inr ⟨⟨i, hg⟩, hi⟩, rfl⟩

/-- A word whose colours lie in `J` comes from the restriction to `J`. -/
theorem exists_map_genMap_eq (w : List (SYMGen D)) (hw : ∀ g ∈ w, genColour g ∈ J) :
    ∃ w' : List (SYMGen (D.restrictColours J)), w'.map (genMap J) = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons g w ih =>
    obtain ⟨g', hg'⟩ := exists_genMap_eq J g (hw g List.mem_cons_self)
    obtain ⟨w', hw'⟩ := ih fun g hg => hw g (List.mem_cons_of_mem _ hg)
    exact ⟨g' :: w', by rw [List.map_cons, hg', hw']⟩

/-! ## Inclusion of coefficient algebras -/

variable (D k) in
/-- Inclusion of the coefficient algebra of the restriction to `J`. -/
def symRestrict : SYM (D.restrictColours J) k →ₐ[k] SYM D k :=
  RingQuot.liftAlgHom k ⟨FreeAlgebra.lift k fun g => SYM.ι D k (genMap J g), by
    intro a b h
    cases h with
    | polynomial a b =>
      obtain ⟨i, m⟩ := a
      obtain ⟨j, n⟩ := b
      simpa [genMap, SYM.ι, map_mul] using
        RingQuot.mkAlgHom_rel k (SYMRel.polynomial (D := D) (k := k) (i.val, m) (j.val, n))
    | mixed a i =>
      obtain ⟨j, n⟩ := a
      simpa [genMap, SYM.ι, map_mul] using
        RingQuot.mkAlgHom_rel k (SYMRel.mixed (D := D) (k := k) (j.val, n) ⟨i.val.val, i.property⟩)
    | exterior i j =>
      simpa [genMap, SYM.ι, map_mul] using
        RingQuot.mkAlgHom_rel k (SYMRel.exterior (D := D) (k := k) ⟨i.val.val, i.property⟩
          ⟨j.val.val, j.property⟩)
    | square i =>
      simpa [genMap, SYM.ι, map_pow] using
        RingQuot.mkAlgHom_rel k (SYMRel.square (D := D) (k := k) ⟨i.val.val, i.property⟩)⟩

theorem symRestrict_ι (g : SYMGen (D.restrictColours J)) :
    symRestrict D J k (SYM.ι (D.restrictColours J) k g) = SYM.ι D k (genMap J g) := by
  simp [symRestrict, SYM.ι]

theorem symRestrict_prod (w : List (SYMGen (D.restrictColours J))) :
    symRestrict D J k ((w.map (SYM.ι (D.restrictColours J) k)).prod) =
      ((w.map (genMap J)).map (SYM.ι D k)).prod := by
  induction w with
  | nil => simp
  | cons g w ih => rw [List.map_cons, List.prod_cons, map_mul, ih, symRestrict_ι]; rfl

variable (D k) in
/-- Products of words in the generators span the coefficient algebra. -/
theorem span_wordProd :
    Submodule.span k (Set.range fun w : List (SYMGen D) => (w.map (SYM.ι D k)).prod) = ⊤ := by
  have hadj : Algebra.adjoin k (Set.range (SYM.ι D k)) = ⊤ := by
    have : Set.range (SYM.ι D k) = SYM.mk D k '' Set.range (FreeAlgebra.ι k) := by
      rw [← Set.range_comp]; rfl
    rw [this, ← AlgHom.map_adjoin, FreeAlgebra.adjoin_range_ι, Algebra.map_top,
      AlgHom.range_eq_top]
    exact RingQuot.mkAlgHom_surjective k (SYMRel D k)
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Subalgebra.toSubmodule (Algebra.adjoin k (Set.range (SYM.ι D k))) := by
    rw [hadj]; trivial
  rw [Algebra.adjoin_eq_span] at hx
  refine Submodule.span_le.mpr ?_ hx
  intro y hy
  obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hy
  have : ∃ w : List (SYMGen D), w.map (SYM.ι D k) = l := by
    clear hy
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons a l ih =>
      obtain ⟨g, rfl⟩ := hl a List.mem_cons_self
      obtain ⟨w, hw⟩ := ih fun b hb => hl b (List.mem_cons_of_mem _ hb)
      exact ⟨g :: w, by rw [List.map_cons, hw]⟩
  obtain ⟨w, rfl⟩ := this
  exact Submodule.subset_span ⟨w, rfl⟩

/-! ## Detection of relations among formal sums -/

variable (D Sc) in
theorem evS_eq_sum (μ : X) (s t : List (Letter I)) (L : List (k × List (LayerData I))) :
    evS D Sc μ s t L = ∑ m ∈ Finset.range L.length,
      (L.getD m (0, [])).1 • cl D Sc μ s t (L.getD m (0, [])).2 := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [evS_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]

variable (D Sc) in
/-- **Finite-colour detection of formal sums.** If a formal sum of full-colour classes
vanishes, there is one finite colour set `J₁` such that every restricted formal sum
including onto it, over any `J ⊇ J₁`, already vanishes. -/
theorem evS_eq_zero_restrict (μ : X) (s t : List (Letter I)) (L : List (k × List (LayerData I)))
    (h : evS D Sc μ s t L = 0) :
    ∃ J₁ : Finset I, ∀ J : Finset I, J₁ ⊆ J →
      ∀ (s' t' : List (Letter J)) (L' : List (k × List (LayerData J))),
        s'.map (letter J) = s → t'.map (letter J) = t → pushS J L' = L →
        evS (D.restrictColours J) (Sc.restrictColours D J) μ s' t' L' = 0 := by
  rw [evS_eq_sum] at h
  obtain ⟨J₁, hJ₁⟩ := sum_cl_eq_zero_restrict D Sc μ s t _ _ _ h
  refine ⟨J₁, fun J hJ s' t' L' hs ht hL => ?_⟩
  have hlen : L'.length = L.length := by rw [← hL, pushS, List.length_map]
  rw [evS_eq_sum, hlen]
  have hc : ∀ m, (L'.getD m (0, [])).1 = (L.getD m (0, [])).1 := by
    intro m
    rw [← hL, pushS, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases L'[m]? <;> rfl
  simp only [hc]
  refine hJ₁ J hJ s' t' (fun m => (L'.getD m (0, [])).2) hs ht fun m _ => ?_
  rw [← hL, pushS, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L'[m]? <;> rfl

end OddMath.SKM.FiniteColour
