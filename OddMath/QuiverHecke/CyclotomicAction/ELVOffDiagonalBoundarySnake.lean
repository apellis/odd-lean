import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCrossingHeight

/-! # The actual boundary-kernel map into the prescribed crossing source

The kernel arrow in the snake sequence of `DeformedRouquierMatrix.md` is
constructed from the existing source section, P map and short-cross decoder.
Its image is the kernel of the actual cyclotomic crossing. No exact-sequence
or faithful-action hypothesis is supplied.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open CategoryTheory StringDiagrams Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem offDiagonalShortCross_decode_of_mem (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i]))
    (hz : z ∈ appendCrossingSpan D Sc cutoff i v t) :
    shortCross D Sc cutoff i v t (ShortCrossCoordinates.decode D Sc cutoff i v t z) = z := by
  rw [← ShortCrossCoordinates.range_shortCross] at hz
  obtain ⟨y, rfl⟩ := hz
  rw [ShortCrossCoordinates.decode_shortCross]

def offDiagonalBoundarySnake (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) →ₗ[k]
      Source D Sc cutoff j.1 v t :=
  q D Sc cutoff j.1 v t ∘ₗ ShortCrossCoordinates.decode D Sc cutoff j.1 v t ∘ₗ
    pMap D Sc cutoff j.1 v (t ++ [j.1]) ∘ₗ offDiagonalSourceLongSection D Sc cutoff p j.1 v t ∘ₗ
      (LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t)).subtype

theorem offDiagonalBoundarySnake_lift (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t)) :
    shortCross D Sc cutoff j.1 v t
      (ShortCrossCoordinates.decode D Sc cutoff j.1 v t
        (pMap D Sc cutoff j.1 v (t ++ [j.1]) (offDiagonalSourceLongSection D Sc cutoff p j.1 v t f))) =
      pMap D Sc cutoff j.1 v (t ++ [j.1]) (offDiagonalSourceLongSection D Sc cutoff p j.1 v t f) := by
  apply offDiagonalShortCross_decode_of_mem
  rw [← appendC0_ker, LinearMap.mem_ker, appendC0_pMap_offDiagonal,
    offDiagonalLongExtraction_sourceLongSection]
  exact f.property

theorem offDiagonalToCyclotomic_boundarySnake (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t)) :
    toCyclotomic D Sc cutoff j.1 v t (offDiagonalBoundarySnake D Sc cutoff p j v t f) = 0 := by
  have hs := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t)
    (ShortCrossCoordinates.decode D Sc cutoff j.1 v t
      (pMap D Sc cutoff j.1 v (t ++ [j.1]) (offDiagonalSourceLongSection D Sc cutoff p j.1 v t f)))
  simp only [LinearMap.comp_apply] at hs
  change _ = toCyclotomic D Sc cutoff j.1 v t (offDiagonalBoundarySnake D Sc cutoff p j v t f) at hs
  rw [← hs, offDiagonalBoundarySnake_lift]
  have hm : pMap D Sc cutoff j.1 v (t ++ [j.1]) (offDiagonalSourceLongSection D Sc cutoff p j.1 v t f) ∈
      LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
    rw [ker_canonicalAppendTarget]
    exact ⟨_, rfl⟩
  exact hm

theorem offDiagonalBoundarySnake_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) :
    Function.Injective (offDiagonalBoundarySnake D Sc cutoff p j v t) := by
  suffices hzero : ∀ z, offDiagonalBoundarySnake D Sc cutoff p j v t z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero (x - y)
    have hs : offDiagonalBoundarySnake D Sc cutoff p j v t (x - y) = offDiagonalBoundarySnake D Sc cutoff p j v t x - offDiagonalBoundarySnake D Sc cutoff p j v t y :=
      map_sub (offDiagonalBoundarySnake D Sc cutoff p j v t) x y
    exact hs.trans (sub_eq_zero.mpr hxy)
  intro f hf
  have hy : ShortCrossCoordinates.decode D Sc cutoff j.1 v t
      (pMap D Sc cutoff j.1 v (t ++ [j.1]) (offDiagonalSourceLongSection D Sc cutoff p j.1 v t f)) ∈
      LinearMap.ker (q D Sc cutoff j.1 v t) := hf
  rw [← range_pprime_eq_ker_q] at hy
  obtain ⟨a, ha⟩ := hy
  have he : alpha D Sc cutoff j.1 v t a = offDiagonalSourceLongSection D Sc cutoff p j.1 v t f := by
    apply pMap_injective D Sc cutoff j.1 v (t ++ [j.1])
    have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a
    simp only [LinearMap.comp_apply] at hs
    exact hs.trans (by rw [ha, offDiagonalBoundarySnake_lift])
  have hb := congrArg (offDiagonalLongExtraction D Sc cutoff p j.1 v t) he
  rw [offDiagonalLongExtraction_alpha, offDiagonalLongExtraction_sourceLongSection] at hb
  exact Subtype.ext hb.symm

/-- Changing the source lift by its prescribed short coordinate does not
change the cyclotomic snake class. This permits using the original corrected
rho lifts in subsequent cap recurrences. -/
theorem offDiagonalBoundarySnake_eq_lift (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t))
    (z : Target D Sc cutoff j.1 v (t ++ [j.1]))
    (hz : offDiagonalLongExtraction D Sc cutoff p j.1 v t z = f) :
    offDiagonalBoundarySnake D Sc cutoff p j v t f =
      q D Sc cutoff j.1 v t (ShortCrossCoordinates.decode D Sc cutoff j.1 v t
        (pMap D Sc cutoff j.1 v (t ++ [j.1]) z)) := by
  have he := offDiagonalSource_reconstruction D Sc cutoff p j.1 v t z
  rw [hz] at he
  rw [← he, map_add]
  have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t)
    (extract D Sc cutoff j.1 v t z)
  simp only [LinearMap.comp_apply] at hs
  rw [hs, map_add, ShortCrossCoordinates.decode_shortCross, map_add]
  have hq : q D Sc cutoff j.1 v t
      (pprime D Sc cutoff j.1 v t (extract D Sc cutoff j.1 v t z)) = 0 := by
    have hm : pprime D Sc cutoff j.1 v t (extract D Sc cutoff j.1 v t z) ∈
        LinearMap.ker (q D Sc cutoff j.1 v t) := by
      rw [← range_pprime_eq_ker_q]
      exact ⟨_, rfl⟩
    exact hm
  rw [hq, zero_add]
  rfl

theorem offDiagonalRange_boundarySnake (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.range (offDiagonalBoundarySnake D Sc cutoff p j v t) =
      LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t) := by
  apply le_antisymm
  · rintro z ⟨f, rfl⟩
    exact offDiagonalToCyclotomic_boundarySnake D Sc cutoff p j v t f
  · intro z hz
    obtain ⟨y, rfl⟩ := q_surjective D Sc cutoff j.1 v t z
    have hy : shortCross D Sc cutoff j.1 v t y ∈
        LinearMap.ker (canonicalAppendTarget D Sc cutoff j.1 v (t ++ [j.1])) := by
      rw [LinearMap.mem_ker]
      have he := LinearMap.congr_fun (shortColumn_quotient_square D Sc cutoff j.1 v t) y
      exact he.trans hz
    rw [ker_canonicalAppendTarget] at hy
    obtain ⟨x, hx⟩ := hy
    have hc : appendC0 D Sc cutoff j.1 v t (shortCross D Sc cutoff j.1 v t y) = 0 := by
      apply appendCrossingSpan_le_ker D Sc cutoff j.1 v t
      rw [← ShortCrossCoordinates.range_shortCross]
      exact ⟨y, rfl⟩
    let f : LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) :=
      ⟨offDiagonalLongExtraction D Sc cutoff p j.1 v t x, by
        rw [LinearMap.mem_ker, ← appendC0_pMap_offDiagonal D Sc cutoff p j.1 v t, hx]
        exact hc⟩
    let a := extract D Sc cutoff j.1 v t x
    have he : y = pprime D Sc cutoff j.1 v t a +
        ShortCrossCoordinates.decode D Sc cutoff j.1 v t
          (pMap D Sc cutoff j.1 v (t ++ [j.1]) (offDiagonalSourceLongSection D Sc cutoff p j.1 v t f)) := by
      apply ShortCrossCoordinates.shortCross_injective D Sc cutoff j.1 v t
      rw [map_add, offDiagonalBoundarySnake_lift]
      have hs := LinearMap.congr_fun (shortColumn_square D Sc cutoff j.1 v t) a
      simp only [LinearMap.comp_apply] at hs
      rw [← hs, ← map_add, offDiagonalSource_reconstruction, hx]
    refine ⟨f, ?_⟩
    have hqa : q D Sc cutoff j.1 v t (pprime D Sc cutoff j.1 v t a) = 0 := by
      have hm : pprime D Sc cutoff j.1 v t a ∈ LinearMap.ker (q D Sc cutoff j.1 v t) := by
        rw [← range_pprime_eq_ker_q]
        exact ⟨a, rfl⟩
      exact hm
    rw [he, map_add, hqa, zero_add]
    rfl

/-- The actual kernel of the prescribed cyclotomic crossing is the boundary kernel. -/
def offDiagonalBoundarySnakeKernelEquiv (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) :
    LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) ≃ₗ[k]
      LinearMap.ker (toCyclotomic D Sc cutoff j.1 v t) :=
  LinearEquiv.ofBijective
    ((offDiagonalBoundarySnake D Sc cutoff p j v t).codRestrict _
      (fun f => offDiagonalToCyclotomic_boundarySnake D Sc cutoff p j v t f))
    ⟨fun f g hfg => offDiagonalBoundarySnake_injective D Sc cutoff p j v t (congrArg Subtype.val hfg),
      by
        intro z
        have hz : z.1 ∈ LinearMap.range (offDiagonalBoundarySnake D Sc cutoff p j v t) := by
          rw [offDiagonalRange_boundarySnake]
          exact z.property
        obtain ⟨f, hf⟩ := hz
        exact ⟨f, Subtype.ext hf⟩⟩

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
