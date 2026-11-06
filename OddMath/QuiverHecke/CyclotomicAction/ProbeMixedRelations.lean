import OddMath.QuiverHecke.CyclotomicAction.ProbeDistinctUnits
import OddMath.QuiverHecke.MixedRelations

/-! # Literal crossings of distinct probe words

These are the actual affine morphisms between the two word objects, together
with their signed dot slides and quadratic formula. They precede the source
and target corner comparison; no invertibility assumption is used here.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

def probeMixedWord (pre post : List I) (i j : I) :
    Word I ((pre.length+post.length+1)+1) :=
  ⟨pre ++ [i,j] ++ post, by simp; omega⟩

theorem probeMixedChain (pre post : List I) (i j : I) :
    SChain (pre ++ [i,j] ++ post)
      (pl (pre ++ [i,j] ++ post) [.cross pre.length]) (pre ++ [j,i] ++ post) :=
  sChain_ofShape' pre post (.cross i j) rfl rfl rfl

def probeMixedCross (pre post : List I) (i j : I) :
    (pres D Sc).obj (ob D (pre ++ [i,j] ++ post)) ⟶
      (pres D Sc).obj (ob D (pre ++ [j,i] ++ post)) :=
  cl D Sc _ _ [.cross pre.length] (probeMixedChain pre post i j)

theorem probeMixedCross_slide (pre post : List I) (i j : I) (hij : i ≠ j) :
    probeMixedCross D Sc pre post i j ≫
      dotE D Sc (pre ++ [j,i] ++ post) pre.length =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ≫
          probeMixedCross D Sc pre post i j) := by
  change cl D Sc _ _ [.cross pre.length] _ ≫ dotE D Sc _ _ = _
  rw [dotE_eq, dotE_eq]
  simp only [probeMixedCross, cl_comp']
  exact slide_right_ne D Sc pre post i j hij _ _

/-- The reverse crossing supplies the second slide required by the direct
rectangular unit proof, with exactly the same sign. -/
theorem probeMixedCross_slide_reverse (pre post : List I) (i j : I) (hij : i ≠ j) :
    dotE D Sc (pre ++ [j,i] ++ post) pre.length ≫
      probeMixedCross D Sc pre post j i =
      SKM.zsign k (D.parity i * D.parity j) •
        (probeMixedCross D Sc pre post j i ≫
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) := by
  change dotE D Sc _ _ ≫ cl D Sc _ _ [.cross pre.length] _ = _
  rw [dotE_eq, dotE_eq]
  simp only [probeMixedCross, cl_comp']
  simpa only [List.cons_append, List.nil_append, mul_comm] using slide_left_ne D Sc pre post j i hij.symm
    (sChain_comp (sChain_pl _ [.dot pre.length]) (probeMixedChain pre post j i))
    (sChain_comp (probeMixedChain pre post j i)
      (sChain_pl _ [.dot (pre.length+1)]))

theorem probeMixedCross_quadratic_zero (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j = 0) :
    probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i =
      (Sc.t i j : k) • 𝟙 _ := by
  simp only [probeMixedCross, cl_comp']
  exact cross_cross_ne_zero D Sc pre post hij hd _

theorem probeMixedCross_quadratic (pre post : List I) (i j : I)
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    probeMixedCross D Sc pre post i j ≫ probeMixedCross D Sc pre post j i =
      (∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
        Sc.s i j p q • (dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ p *
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ^ q)) +
      ((Sc.t i j : k) • dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ D.dn i j +
        (Sc.t j i : k) • dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) ^ D.dn j i) := by
  simp only [probeMixedCross, cl_comp']
  exact cross_cross_ne D Sc pre post hij hd _

/-- The two literal dots obey the prescribed supercommutation sign. -/
theorem probeMixedDots_slide (pre post : List I) (i j : I) :
    dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) *
      dotE D Sc (pre ++ [i,j] ++ post) pre.length =
      SKM.zsign k (D.parity i * D.parity j) •
        (dotE D Sc (pre ++ [i,j] ++ post) pre.length *
          dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)) := by
  have h := genE_interchange D Sc pre [] post (.dot i) (.dot j) rfl rfl
    (w := pre ++ [i,j] ++ post) (by simp [Shape.dom, List.append_assoc])
    (p := pre.length) (q := pre.length+1) rfl (by simp [Shape.dom])
  simpa only [Shape.parity, PG.ofShape] using h

/-- Moving a dot past a power of the other dot records the explicit sign. -/
theorem probeMixedDots_pow_slide (pre post : List I) (i j : I) (p : ℕ) :
    dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ p *
      dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) =
      SKM.zsign k (D.parity i * D.parity j) ^ p •
        (dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1) *
          dotE D Sc (pre ++ [i,j] ++ post) pre.length ^ p) := by
  let u := dotE D Sc (pre ++ [i,j] ++ post) pre.length
  let v := dotE D Sc (pre ++ [i,j] ++ post) (pre.length+1)
  let ε := SKM.zsign k (D.parity i * D.parity j)
  have h0 := probeMixedDots_slide D Sc pre post i j
  change v * u = ε • (u * v) at h0
  have he : ε * ε = 1 := zsign_mul_self _
  have hb : u * v = ε • (v * u) := by
    rw [h0, smul_smul, he, one_smul]
  change u^p * v = ε^p • (v * u^p)
  induction p with
  | zero => simp only [pow_zero, one_mul, mul_one, one_smul]
  | succ p ih =>
    calc
      u^(p+1) * v = u^p * (u*v) := by rw [pow_succ, mul_assoc]
      _ = u^p * (ε • (v*u)) := by rw [hb]
      _ = ε • ((u^p*v)*u) := by rw [mul_smul_comm, ← mul_assoc]
      _ = ε • ((ε^p • (v*u^p))*u) := by rw [ih]
      _ = ε^(p+1) • (v*u^(p+1)) := by
        rw [smul_mul_assoc, smul_smul, ← pow_succ', mul_assoc, ← pow_succ]

end OddMath.QuiverHecke
