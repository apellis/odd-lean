import OddMath.QuiverHecke.CyclotomicAction.ProbeMixedRelations
import OddMath.QuiverHecke.CyclotomicAction.ProbeFirstDot
import OddMath.SKM.BWWPureNilpotent

/-! # Actual rectangular corner relations for mixed probe dots

The affine slides and positive-dot remainders are compared with the literal
word-corner maps. These comparisons use the existing cyclotomic algebra,
including its actual finite Hom-matrix multiplication.

The hypothesis `Sc.PureNilpotent` (as `[Fact Sc.PureNilpotent]` on the dot unit) is a
route-only intermediate hypothesis for parameters with pure terms: homogeneous parameters
supply it (`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

theorem cyclotomicWordEntry_smul {n : ℕ} (s t : Word I (n+1)) (c : k)
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordEntry D Sc a s t (c • f) =
      c • cyclotomicWordEntry D Sc a s t f := by
  unfold cyclotomicWordEntry
  rw [FiniteHomMatrix.single_smul, map_smul]

abbrev probeMixedCornerDot (pre post : List I) (i j : I) (r : ℕ) :=
  cyclotomicWordEnd D Sc a (probeMixedWord pre post i j)
    (dotE D Sc (pre ++ [i,j] ++ post) r)

def probeMixedEntry (pre post : List I) (i j : I) :
    CyclotomicAlgebra D Sc a (pre.length+post.length+1) :=
  cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
    (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j)

theorem probeMixedCorner_slide (pre post : List I) (i j : I) (hij : i ≠ j) :
    (probeMixedCornerDot D Sc a pre post j i pre.length).val *
        probeMixedEntry D Sc a pre post i j =
      SKM.zsign k (D.parity i * D.parity j) •
        (probeMixedEntry D Sc a pre post i j *
          (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val) := by
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post j i) (dotE D Sc (pre ++ [j,i] ++ post) pre.length) *
      cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j) = _
  rw [← cyclotomicWordEntry_comp]
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
      (probeMixedWord pre post j i) _ =
    SKM.zsign k (D.parity i * D.parity j) •
      (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post j i) (probeMixedCross D Sc pre post i j) *
       cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post i j) (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)))
  rw [← cyclotomicWordEntry_comp, ← cyclotomicWordEntry_smul]
  exact congrArg (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
    (probeMixedWord pre post j i)) (probeMixedCross_slide D Sc pre post i j hij)

theorem probeMixedCorner_slide_reverse (pre post : List I) (i j : I) (hij : i ≠ j) :
    probeMixedEntry D Sc a pre post j i *
        (probeMixedCornerDot D Sc a pre post j i pre.length).val =
      SKM.zsign k (D.parity i * D.parity j) •
        ((probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val *
          probeMixedEntry D Sc a pre post j i) := by
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post i j) (probeMixedCross D Sc pre post j i) *
      cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
        (probeMixedWord pre post j i) (dotE D Sc (pre ++ [j,i] ++ post) pre.length) = _
  rw [← cyclotomicWordEntry_comp]
  change cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
      (probeMixedWord pre post i j) _ =
    SKM.zsign k (D.parity i * D.parity j) •
      (cyclotomicWordEntry D Sc a (probeMixedWord pre post i j)
        (probeMixedWord pre post i j) (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) *
       cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
        (probeMixedWord pre post i j) (probeMixedCross D Sc pre post j i))
  rw [← cyclotomicWordEntry_comp, ← cyclotomicWordEntry_smul]
  exact congrArg (cyclotomicWordEntry D Sc a (probeMixedWord pre post j i)
    (probeMixedWord pre post i j)) (probeMixedCross_slide_reverse D Sc pre post i j hij)

/-- The scalars act on a word corner through its identity: `c ↦ q(c • 1)`. -/
def cyclotomicWordCornerAlgebraMap {n : ℕ} (s : Word I (n+1)) :
    k →+* CyclotomicWordCorner D Sc a s :=
  (cyclotomicWordEnd D Sc a s).comp (algebraMap k (End (wordObj D Sc s)))

theorem cyclotomicWordCornerAlgebraMap_val {n : ℕ} (s : Word I (n+1)) (c : k) :
    (cyclotomicWordCornerAlgebraMap D Sc a s c).val =
      c • (1 : CyclotomicWordCorner D Sc a s).val := by
  change cyclotomicWordEntry D Sc a s s (algebraMap k (End (wordObj D Sc s)) c) = _
  rw [Algebra.algebraMap_eq_smul_one, cyclotomicWordEntry_smul]
  rfl

theorem cyclotomicWordCornerAlgebraMap_commute {n : ℕ} (s : Word I (n+1)) (c : k)
    (r : CyclotomicWordCorner D Sc a s) :
    cyclotomicWordCornerAlgebraMap D Sc a s c * r = r * cyclotomicWordCornerAlgebraMap D Sc a s c := by
  apply Subtype.ext
  change (cyclotomicWordCornerAlgebraMap D Sc a s c).val * r.val =
    r.val * (cyclotomicWordCornerAlgebraMap D Sc a s c).val
  rw [cyclotomicWordCornerAlgebraMap_val, smul_mul_assoc, mul_smul_comm]
  have h1 : (1 : CyclotomicWordCorner D Sc a s).val * r.val = r.val :=
    congrArg Subtype.val (one_mul r)
  have h2 : r.val * (1 : CyclotomicWordCorner D Sc a s).val = r.val :=
    congrArg Subtype.val (mul_one r)
  rw [h1, h2]

/-- The word corner as an algebra over the ground ring. -/
abbrev cyclotomicWordCornerAlgebra {n : ℕ} (s : Word I (n+1)) :
    Algebra k (CyclotomicWordCorner D Sc a s) :=
  (cyclotomicWordCornerAlgebraMap D Sc a s).toAlgebra'
    (cyclotomicWordCornerAlgebraMap_commute D Sc a s)

/-- Actual connected Q remainders in the source corner. The leading part `Qᵢⱼ(u, 0)` is a unit
because the preceding source dot `u` is a unit and the pure coefficients lie in a nilpotent
ideal (`ScalarData.PureNilpotent`; for parameters without pure terms the zero ideal). -/
theorem probeMixedCorner_remainders_connected (hP : Sc.PureNilpotent) (pre post : List I)
    (i j : I) (hij : i ≠ j) (hd : D.d i j ≠ 0)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length)) :
    ∃ U Rright Rleft : CyclotomicWordCorner D Sc a (probeMixedWord pre post i j),
      IsUnit U ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + Rright.val * (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val * Rleft.val := by
  let s := probeMixedWord pre post i j
  let _ : Algebra k (CyclotomicWordCorner D Sc a s) := cyclotomicWordCornerAlgebra D Sc a s
  let q : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) →+* CyclotomicWordCorner D Sc a s :=
    cyclotomicWordEnd D Sc a s
  let u := dotE D Sc (pre ++ [i,j] ++ post) pre.length
  let v := dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)
  let ε := SKM.zsign k (D.parity i * D.parity j)
  have hqs : ∀ (c : k) (f : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))),
      q (c • f) = c • q f := by
    intro c f
    rw [Algebra.smul_def c f, map_mul, Algebra.smul_def c (q f)]
    rfl
  have he : ε * ε = 1 := zsign_mul_self _
  have huv : u * v = ε • (v * u) := by
    have h := probeMixedDots_slide D Sc pre post i j
    change v * u = ε • (u * v) at h
    rw [h, smul_smul, he, one_smul]
  have hslide : ∀ p : ℕ, q u ^ p * q v = ε ^ p • (q v * q u ^ p) := by
    intro p
    rw [← map_pow, ← map_mul, ← map_mul, ← hqs]
    congr 1
    induction p with
    | zero => simp
    | succ p ih =>
      rw [pow_succ, mul_assoc, huv, mul_smul_comm, ← mul_assoc, ih, smul_mul_assoc,
        smul_smul, mul_assoc, ← pow_succ']
  obtain ⟨U, Rr, Rl, hU, hr, hl⟩ :=
    hP.exists_isUnit_quad_remainders hij hd (x := q u) (y := q v) hu ε hslide
  have hQ := probeMixedCross_quadratic D Sc pre post i j hij hd
  have hBA : probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
      (q (probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i)).val := by
    unfold probeMixedEntry
    rw [← cyclotomicWordEntry_comp]
    rfl
  have hq : q (probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i) =
      (Sc.t i j : k) • q u ^ D.dn i j + (Sc.t j i : k) • q v ^ D.dn j i +
        ∑ p ∈ Finset.range (D.dn i j), ∑ q' ∈ Finset.range (D.dn j i),
          Sc.s i j p q' • (q u ^ p * q v ^ q') := by
    rw [hQ]
    simp only [map_add, map_sum, hqs, map_mul, map_pow]
    abel
  refine ⟨U, Rr, Rl, hU, ?_, ?_⟩
  · rw [hBA, hq, hr]
    rfl
  · rw [hBA, hq, hl]
    rfl

/-- The disconnected quadratic supplies the same two remainder statements,
with zero remainders and its single scalar unit leading term. -/
theorem probeMixedCorner_remainders (hP : Sc.PureNilpotent) (pre post : List I) (i j : I)
    (hij : i ≠ j)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length)) :
    ∃ U Rright Rleft : CyclotomicWordCorner D Sc a (probeMixedWord pre post i j),
      IsUnit U ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + Rright.val * (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val ∧
      probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        U.val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val * Rleft.val := by
  by_cases hd : D.d i j = 0
  · let s := probeMixedWord pre post i j
    let q : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post))) →+* CyclotomicWordCorner D Sc a s :=
      cyclotomicWordEnd D Sc a s
    let c := algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))) (Sc.t i j : k)
    have hBA : probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val := by
      unfold probeMixedEntry
      rw [← cyclotomicWordEntry_comp]
      change (q (probeMixedCross D Sc pre post i j ≫
        probeMixedCross D Sc pre post j i)).val = (q c).val
      rw [probeMixedCross_quadratic_zero D Sc pre post i j hij hd]
      change (q ((Sc.t i j : k) • (1 : End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).val =
        (q (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))) (Sc.t i j : k))).val
      rw [Algebra.algebraMap_eq_smul_one]
    refine ⟨q c, 0, 0,
      (((Sc.t i j).isUnit.map (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [i,j] ++ post)))))).map q), ?_, ?_⟩
    · change probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val + (0 : CyclotomicAlgebra D Sc a (pre.length+post.length+1)) *
          (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val
      rw [zero_mul, add_zero]
      exact hBA
    · change probeMixedEntry D Sc a pre post j i * probeMixedEntry D Sc a pre post i j =
        (q c).val + (probeMixedCornerDot D Sc a pre post i j (pre.length+1)).val *
          (0 : CyclotomicAlgebra D Sc a (pre.length+post.length+1))
      rw [mul_zero, add_zero]
      exact hBA
  · exact probeMixedCorner_remainders_connected D Sc a hP pre post i j hij hd hu

/-- The actual distinct-colour probe step: preceding dots in the source and
swapped target corners are units, hence so is the following source dot.
All signed slides and Q factorization premises are discharged internally. -/
theorem probeMixedCorner_dot_isUnit [hP : Fact Sc.PureNilpotent] (pre post : List I) (i j : I)
    (hij : i ≠ j)
    (hu : IsUnit (probeMixedCornerDot D Sc a pre post i j pre.length))
    (hw : IsUnit (probeMixedCornerDot D Sc a pre post j i pre.length)) :
    IsUnit (probeMixedCornerDot D Sc a pre post i j (pre.length+1)) := by
  let s := probeMixedWord pre post i j
  let t := probeMixedWord pre post j i
  let q : End ((pres D Sc).obj (ob D (pre ++ [j,i] ++ post))) →+* CyclotomicWordCorner D Sc a t :=
    cyclotomicWordEnd D Sc a t
  let ε := SKM.zsign k (D.parity i * D.parity j)
  let v := probeMixedCornerDot D Sc a pre post i j (pre.length+1)
  let A := probeMixedEntry D Sc a pre post i j
  let B := probeMixedEntry D Sc a pre post j i
  let w := probeMixedCornerDot D Sc a pre post j i pre.length
  let W := q (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length)
  have he : ε * ε = 1 := zsign_mul_self _
  have hε : IsUnit ε := ⟨⟨ε, ε, he, he⟩, rfl⟩
  have hW : IsUnit W := by
    change IsUnit (q (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length))
    rw [Algebra.smul_def, map_mul]
    exact ((hε.map (algebraMap k (End ((pres D Sc).obj (ob D (pre ++ [j,i] ++ post)))))).map q).mul hw
  have hWval : W.val = ε • w.val := by
    change cyclotomicWordEntry D Sc a t t
      (ε • dotE D Sc (pre ++ [j,i] ++ post) pre.length) =
      ε • cyclotomicWordEntry D Sc a t t
        (dotE D Sc (pre ++ [j,i] ++ post) pre.length)
    exact cyclotomicWordEntry_smul D Sc a t t ε _
  have hs := probeMixedCorner_slide D Sc a pre post i j hij
  change w.val * A = ε • (A * v.val) at hs
  have hs' := probeMixedCorner_slide_reverse D Sc a pre post i j hij
  change B * w.val = ε • (v.val * B) at hs'
  have hslide : W.val * A = A * v.val := by
    rw [hWval, smul_mul_assoc, hs, smul_smul, he, one_smul]
  have hslide' : v.val * B = B * W.val := by
    symm
    rw [hWval, mul_smul_comm, hs', smul_smul, he, one_smul]
  obtain ⟨U, Rright, Rleft, hU, hr, hl⟩ :=
    probeMixedCorner_remainders D Sc a hP.out pre post i j hij hu
  exact cyclotomicWordEntry_distinct_isUnit_twoRemainders D Sc a s t
    (probeMixedCross D Sc pre post i j) (probeMixedCross D Sc pre post j i)
    v W U Rright Rleft hW hU hslide hslide' hr hl

end OddMath.QuiverHecke
