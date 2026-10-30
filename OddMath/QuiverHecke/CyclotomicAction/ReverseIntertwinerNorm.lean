/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ReverseIntertwinerChain
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPDistinct

/-!
# Endpoint polynomials for reverse moving chains

The independently defined append-end norm factors in
`DeformedBoundaryDivision.md` §2. The headline theorem
`reverseMoveHom_comp_moveHom_eq_endpointNorm` identifies the actual chain
composite, supplying the affine polynomial identity for quotient regularity.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke IntertwinerMeet
open scoped Classical

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

/-- One endpoint norm factor, in the order old strand, moving strand.
This definition involves only dots, not either moving chain. -/
def endpointNormFactor {B : Type*} [Ring B] [Algebra k B]
    (j i : I) (u v : B) : B :=
  if j = i then
    if D.parity j = 1 then -((v ^ 2 - u ^ 2) ^ 2 * (u ^ 2 + v ^ 2))
    else -((v - u) ^ 2)
  else if D.d j i = 0 then algebraMap k B (Sc.t j i : k)
  else qLeft u v (D.dn j i) (D.dn i j) (Sc.t j i : k) (Sc.t i j : k) (Sc.s j i)

/-- An ordered product evaluated in one fixed affine word. No intertwiner occurs
in this definition; the recursion just increments the old-strand dot position. -/
def endpointNormAux (i : I) (w : List I) (moving : ℕ) :
    ℕ → List I → End ((pres D Sc).obj (ob D w))
  | _, [] => 1
  | old, j :: ν => endpointNormFactor D Sc j i (dotE D Sc w old)
      (dotE D Sc w moving) * endpointNormAux i w moving (old + 1) ν

/-- The independent ordered endpoint polynomial. The first encountered factor
is on the left in the endomorphism ring, hence last in categorical composition. -/
def endpointNorm (i : I) (l ν : List I) :
    End ((pres D Sc).obj (ob D (l ++ ν ++ [i]))) :=
  endpointNormAux D Sc i (l ++ ν ++ [i]) (l.length + ν.length) l.length ν

/-- The independent polynomial definition agrees with the adjacent local square. -/
theorem endpointNormFactor_local (l r : List I) (j i : I) :
    endpointNormFactor D Sc j i
      (dotE D Sc (l ++ [j, i] ++ r) l.length)
      (dotE D Sc (l ++ [j, i] ++ r) (l.length + 1)) =
      intertwinerSquare D Sc l r j i := by
  simp only [endpointNormFactor, intertwinerSquare, Algebra.algebraMap_eq_smul_one,
    End.one_def]

@[simp] theorem endpointNorm_nil (i : I) (l : List I) :
    endpointNorm D Sc i l [] = 1 := by simp [endpointNorm, endpointNormAux]

/-- The zero-length norm is the empty ordered polynomial. -/
theorem reverseMoveHom_comp_moveHom_eq_endpointNorm_nil (i : I) (l : List I) :
    reverseMoveHom D Sc i l [] ≫ moveHom D Sc i l [] =
      endpointNorm D Sc i l [] := by
  simpa using reverseMoveHom_comp_moveHom_nil D Sc i l

/-- The one-letter chain produces the independently defined endpoint polynomial. -/
theorem reverseMoveHom_comp_moveHom_eq_endpointNorm_singleton (i j : I) :
    reverseMoveHom D Sc i [] [j] ≫ moveHom D Sc i [] [j] =
      endpointNorm D Sc i [] [j] := by
  rw [reverseMoveHom_comp_moveHom_singleton]
  simpa [endpointNorm, endpointNormAux] using (endpointNormFactor_local D Sc [] [] j i).symm

private theorem norm_comp_sub {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a b : End B) :
    g ≫ (a - b : End B) = g ≫ a - g ≫ b := Preadditive.comp_sub _ _ _

private theorem norm_sub_comp {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a b : End A) :
    (a - b : End A) ≫ g = a ≫ g - b ≫ g := Preadditive.sub_comp _ _ _

private theorem norm_comp_neg {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a : End B) :
    g ≫ (-a : End B) = -(g ≫ a) := Preadditive.comp_neg _ _

private theorem norm_neg_comp {C : Type*} [Category C] [Preadditive C]
    {A B : C} (g : A ⟶ B) (a : End A) :
    (-a : End A) ≫ g = -(a ≫ g) := Preadditive.neg_comp _ _

/-- Polynomial transport requires no inverse to the intertwiner. The parity support
of `Q` and the even powers in the repeated-colour factors remove all signs. -/
theorem comp_endpointNormFactor {A B : (pres D Sc).Presented} (g : A ⟶ B)
    (u' v' : End A) (u v : End B) (j i : I) (ea eb : k)
    (hu : g ≫ u = ea • (u' ≫ g)) (hv : g ≫ v = eb • (v' ≫ g))
    (hea : ∀ n : ℕ, (n : ZMod 2) * D.parity j = 0 → ea ^ n = 1)
    (heb : ∀ n : ℕ, (n : ZMod 2) * D.parity i = 0 → eb ^ n = 1) :
    g ≫ endpointNormFactor D Sc (B := End B) j i u v =
      endpointNormFactor D Sc (B := End A) j i u' v' ≫ g := by
  by_cases hji : j = i
  · subst j
    by_cases hp : D.parity i = 1
    · have hu2 : g ≫ (u ^ 2 : End B) = (u' ^ 2 : End A) ≫ g := by
        simpa only [hea 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]), one_smul] using
          comp_pow_of_signed g u' u ea hu 2
      have hv2 : g ≫ (v ^ 2 : End B) = (v' ^ 2 : End A) ≫ g := by
        simpa only [heb 2 (by rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]), one_smul] using
          comp_pow_of_signed g v' v eb hv 2
      have hsub : g ≫ (v ^ 2 - u ^ 2 : End B) =
          (1 : k) • ((v' ^ 2 - u' ^ 2 : End A) ≫ g) := by
        simp only [one_smul, norm_comp_sub, norm_sub_comp, hu2, hv2]
      have hadd : g ≫ (u ^ 2 + v ^ 2 : End B) =
          (1 : k) • ((u' ^ 2 + v' ^ 2 : End A) ≫ g) := by
        simp only [one_smul, comp_end_add, end_add_comp, hu2, hv2]
      have h := comp_monomial_of_signed g (v' ^ 2 - u' ^ 2) (u' ^ 2 + v' ^ 2)
        (v ^ 2 - u ^ 2) (u ^ 2 + v ^ 2) 1 1 hsub hadd 2 1
      simpa only [endpointNormFactor, ite_true, hp, norm_comp_neg,
        norm_neg_comp, one_pow, one_mul, one_smul, pow_one] using congrArg Neg.neg h
    · have hp0 := parity_eq_zero_of_ne_one hp
      have hea1 : ea = 1 := by simpa using hea 1 (by rw [hp0, mul_zero])
      have heb1 : eb = 1 := by simpa using heb 1 (by rw [hp0, mul_zero])
      have hsub : g ≫ (v - u : End B) = (1 : k) • ((v' - u' : End A) ≫ g) := by
        simp only [one_smul, norm_comp_sub, norm_sub_comp,
          hu, hv, hea1, heb1]
      have h := comp_pow_of_signed g (v' - u') (v - u) 1 hsub 2
      simpa only [endpointNormFactor, ite_true, hp, ite_false, norm_comp_neg,
        norm_neg_comp, one_pow, one_smul] using congrArg Neg.neg h
  · simpa only [endpointNormFactor, hji, ite_false, qPoly, qLeft,
      Algebra.algebraMap_eq_smul_one] using comp_qPoly D Sc g u' v' u v j i ea eb hu hv hea heb

/-- Transport the first norm factor along the forward tail. This is the concrete
producer: its hypotheses are only the datum, colours and word. -/
theorem endpointNormFactor_comp_moveHom (i j : I) (l ν : List I) :
    endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D ((l ++ [j]) ++ i :: ν)))) j i
      (dotE D Sc ((l ++ [j]) ++ i :: ν) l.length)
      (dotE D Sc ((l ++ [j]) ++ i :: ν) (l ++ [j]).length) ≫
        moveHom D Sc i (l ++ [j]) ν =
    moveHom D Sc i (l ++ [j]) ν ≫
      endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D ((l ++ [j]) ++ ν ++ [i])))) j i
        (dotE D Sc ((l ++ [j]) ++ ν ++ [i]) l.length)
        (dotE D Sc ((l ++ [j]) ++ ν ++ [i]) ((l ++ [j]).length + ν.length)) := by
  symm
  apply comp_endpointNormFactor D Sc _ _ _ _ _ j i
    (SKM.zsign k (D.parity j * (D.parity i * wordSumParity D ν)))
    (SKM.zsign k (D.parity i * wordSumParity D ν))
  · have h := dot_left_comp_moveHom D Sc i j l ν (l ++ [j]) [] (by simp)
    have h' := congrArg (SKM.zsign k (D.parity j * (D.parity i * wordSumParity D ν)) • ·) h
    simpa only [smul_smul, zsign_mul_self, one_smul] using h'.symm
  · have h := dot_comp_moveHom D Sc i (l ++ [j]) ν
    have h' := congrArg (SKM.zsign k (D.parity i * wordSumParity D ν) • ·) h
    simpa only [smul_smul, zsign_mul_self, one_smul] using h'.symm
  · intro n hn
    apply zsign_pow_eq_one
    rw [← mul_assoc, hn, zero_mul]
  · intro n hn
    apply zsign_pow_eq_one
    rw [← mul_assoc, hn, zero_mul]

private theorem normFactor_conj (i j : I) {w w' : List I} (h : w = w') (a b : ℕ) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
      endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D w'))) j i
        (dotE D Sc w' a) (dotE D Sc w' b) ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h.symm) =
    endpointNormFactor D Sc j i (dotE D Sc w a) (dotE D Sc w b) := by
  subst w'
  simp

private theorem normFactor_comp_eqToHom (i j : I) {w w' : List I} (h : w = w')
    (a b : ℕ) :
    endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D w))) j i
        (dotE D Sc w a) (dotE D Sc w b) ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) =
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
      endpointNormFactor D Sc (B := End ((pres D Sc).obj (ob D w'))) j i
        (dotE D Sc w' a) (dotE D Sc w' b) := by
  subst w'
  simp

private theorem normAux_conj (i : I) {w w' : List I} (h : w = w')
    (moving old : ℕ) (ν : List I) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h) ≫
      endpointNormAux D Sc i w' moving old ν ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) h.symm) =
    endpointNormAux D Sc i w moving old ν := by
  subst w'
  simp

/-- The affine append-end norm of an arbitrary chain is its independently defined
ordered endpoint polynomial. No injectivity or assumed square identity is used. -/
theorem reverseMoveHom_comp_moveHom_eq_endpointNorm (i : I) (l ν : List I) :
    reverseMoveHom D Sc i l ν ≫ moveHom D Sc i l ν = endpointNorm D Sc i l ν := by
  induction ν generalizing l with
  | nil => exact reverseMoveHom_comp_moveHom_eq_endpointNorm_nil D Sc i l
  | cons j ν ih =>
    have hloc := normFactor_conj D Sc i j
      (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp) l.length (l.length + 1)
    rw [endpointNormFactor_local] at hloc
    have hslide := endpointNormFactor_comp_moveHom D Sc i j l ν
    simp only [List.length_append, List.length_singleton] at hslide
    rw [reverseMoveHom_comp_moveHom_cons]
    rw [reassoc_of% hloc, reassoc_of% hslide]
    rw [← Category.assoc (reverseMoveHom D Sc i (l ++ [j]) ν), ih]
    rw [normFactor_comp_eqToHom]
    simp only [endpointNorm, List.length_append, List.length_singleton]
    rw [reassoc_of% normAux_conj]
    simp only [endpointNormAux, List.length_cons, End.mul_def]
    simp only [Nat.add_assoc, Nat.add_comm 1 ν.length]
    all_goals simp

end OddMath.QuiverHecke
