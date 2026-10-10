/-
# Atiyah–Sutcliffe Conjecture 1 is false

A single-file Lean 4 proof (toolchain 4.33.1, Mathlib 0df444a360eaa60ab8c11dca51a86af692955474) that the
Atiyah–Sutcliffe conjecture 1, as formalised in google-deepmind/formal-conjectures
(`FormalConjectures/Arxiv/1102.4662/AtiyahSutcliffe.lean`, `AtiyahSutcliffe.conjecture_one`), is false:
an explicit injective configuration of 46 points in `ℝ³` whose point polynomials are linearly dependent.

The file is the concatenation of the modules of the project
https://github.com/azakhtyamov/atiyah-sutcliffe-disproof/ (see its README for the mathematics and the layout):
the lemma library `Atiyah.Facts` (verified lemmas from the Crucian study that found the witness; statements
kept as generated), then the readable certificate layer `Atiyah.*` (interval arithmetic, dual numbers, the
coefficient program, elimination, the Newton–Kantorovich check, the witness, the kernel checks, the
assembly) and the final theorems. Compiling it takes about ten minutes, almost all of it kernel
evaluation of the 320-bit certificate (peak memory about 16 GB).

Verification: in a checkout of formal-conjectures at a commit with the same toolchain,
`lake build 'FormalConjectures.Arxiv.«1102.4662».AtiyahSutcliffe'` then
`lake env lean AtiyahSutcliffeDisproof.lean`; the last line printed is the axiom list of
`AtiyahSutcliffeDisproof.conjecture_one_false`: `[propext, Classical.choice, Quot.sound]`.
-/
import FormalConjectures.Arxiv.«1102.4662».AtiyahSutcliffe
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Analytic.Basic

/-! ## The lemma library of the study -/

/-! ### `Atiyah.Facts`: Interval -/

/-!
# Verified fixed-point interval arithmetic and dual numbers

Dyadic intervals as integer pairs with outward rounding, the five primitives with their enclosure
proofs, and optional dual numbers carrying Fréchet derivatives of the two free parameters.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- Integer Euclidean division gives exact lower and upper real rounding bounds for positive denominators -/
theorem int_div_bounds : (
∀ (a b : ℤ), 0 < b → ((a / b : ℤ) : ℝ) ≤ (a:ℝ)/(b:ℝ) ∧ (a:ℝ)/(b:ℝ) ≤ -(((-a / b : ℤ) : ℝ))
) := by
  intro a b hb
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hlo : ((a / b : ℤ):ℝ) * (b:ℝ) ≤ (a:ℝ) := by
    exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)
  have hhi : (((-a) / b : ℤ):ℝ) * (b:ℝ) ≤ -(a:ℝ) := by
    exact_mod_cast Int.ediv_mul_le (-a) (ne_of_gt hb)
  exact ⟨(le_div_iff₀ hb').mpr hlo, (div_le_iff₀ hb').mpr (by nlinarith)⟩

/-- The product of two real intervals lies between the minimum and maximum of the four corner products -/
theorem interval_mul_corners : (
∀ (a b c d l u x y : ℝ), a ≤ x → x ≤ b → c ≤ y → y ≤ d → l ≤ min (min (a*c) (a*d)) (min (b*c) (b*d)) → max (max (a*c) (a*d)) (max (b*c) (b*d)) ≤ u → l ≤ x*y ∧ x*y ≤ u
) := by
  intro a b c d l u x y hax hxb hcy hyd hl hu
  simp only [le_min_iff, max_le_iff] at hl hu
  have lin (t p q v L U : ℝ) (hp : p ≤ t) (hq : t ≤ q) (hLp : L ≤ v*p) (hLq : L ≤ v*q) (hpU : v*p ≤ U) (hqU : v*q ≤ U) : L ≤ v*t ∧ v*t ≤ U := by
    by_cases hv : 0 ≤ v
    · exact ⟨hLp.trans (mul_le_mul_of_nonneg_left hp hv), (mul_le_mul_of_nonneg_left hq hv).trans hqU⟩
    · have hv' := le_of_lt (lt_of_not_ge hv)
      exact ⟨hLq.trans (mul_le_mul_of_nonpos_left hq hv'), (mul_le_mul_of_nonpos_left hp hv').trans hpU⟩
  have h1 := lin y c d a l u hcy hyd hl.1.1 hl.1.2 hu.1.1 hu.1.2
  have h2 := lin y c d b l u hcy hyd hl.2.1 hl.2.2 hu.2.1 hu.2.2
  have h3 := lin x a b y l u hax hxb (by simpa [mul_comm] using h1.1) (by simpa [mul_comm] using h2.1) (by simpa [mul_comm] using h1.2) (by simpa [mul_comm] using h2.2)
  simpa only [mul_comm] using h3

/-- Fixed-denominator interval multiplication with integer floor/ceiling rounding encloses the exact real product -/
theorem fixed_mul_encloses : (
∀ (s a b c d : ℤ) (x y : ℝ), 0 < s → (a:ℝ)/(s:ℝ) ≤ x → x ≤ (b:ℝ)/(s:ℝ) → (c:ℝ)/(s:ℝ) ≤ y → y ≤ (d:ℝ)/(s:ℝ) → let L := min (min (a*c) (a*d)) (min (b*c) (b*d)); let U := max (max (a*c) (a*d)) (max (b*c) (b*d)); (((L / s : ℤ):ℝ)/(s:ℝ) ≤ x*y ∧ x*y ≤ ((-((-U) / s) : ℤ):ℝ)/(s:ℝ))
) := by
  intro s a b c d x y hs hax hxb hcy hyd
  dsimp only
  let L := min (min (a*c) (a*d)) (min (b*c) (b*d))
  let U := max (max (a*c) (a*d)) (max (b*c) (b*d))
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hp : (L:ℝ) ≤ (x*(s:ℝ))*(y*(s:ℝ)) ∧ (x*(s:ℝ))*(y*(s:ℝ)) ≤ (U:ℝ) := by
    apply interval_mul_corners
    · exact (div_le_iff₀ hs').mp hax
    · exact (le_div_iff₀ hs').mp hxb
    · exact (div_le_iff₀ hs').mp hcy
    · exact (le_div_iff₀ hs').mp hyd
    · dsimp [L]
      norm_cast
    · dsimp [U]
      norm_cast
  have hl := (int_div_bounds L s hs).1
  have hu := (int_div_bounds U s hs).2
  constructor
  · apply (div_le_iff₀ hs').mpr
    apply hl.trans
    apply (div_le_iff₀ hs').mpr
    nlinarith [hp.1]
  · apply (le_div_iff₀ hs').mpr
    have h : x*y*(s:ℝ) ≤ (U:ℝ)/(s:ℝ) := by
      apply (le_div_iff₀ hs').mpr
      nlinarith [hp.2]
    simpa only [Int.cast_neg] using h.trans hu

/-- Positive fixed-denominator interval reciprocal with integer outward rounding encloses the exact real inverse -/
theorem fixed_inv_encloses : (
∀ (s l u : ℤ) (x : ℝ), 0 < s → 0 < l → l ≤ u → (l:ℝ)/(s:ℝ) ≤ x → x ≤ (u:ℝ)/(s:ℝ) → (((s*s/u : ℤ):ℝ)/(s:ℝ) ≤ x⁻¹ ∧ x⁻¹ ≤ ((-((-(s*s))/l) : ℤ):ℝ)/(s:ℝ))
) := by
  intro s l u x hs hl hlu hxl hxu
  have hu : (0:ℤ) < u := lt_of_lt_of_le hl hlu
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hl' : (0:ℝ) < l := by exact_mod_cast hl
  have hu' : (0:ℝ) < u := by exact_mod_cast hu
  have hx : 0 < x := (div_pos hl' hs').trans_le hxl
  have hlo : (s:ℝ)/(u:ℝ) ≤ x⁻¹ := by
    simpa only [one_div, inv_div] using one_div_le_one_div_of_le hx hxu
  have hhi : x⁻¹ ≤ (s:ℝ)/(l:ℝ) := by
    simpa only [one_div, inv_div] using one_div_le_one_div_of_le (div_pos hl' hs') hxl
  have hroundlo := (int_div_bounds (s*s) u hu).1
  have hroundhi := (int_div_bounds (s*s) l hl).2
  simp only [Int.cast_mul] at hroundlo hroundhi
  have he (v : ℝ) : (((s:ℝ)*(s:ℝ))/v)/(s:ℝ) = (s:ℝ)/v := by
    field_simp
  constructor
  · calc
      (((s*s/u : ℤ):ℝ)/(s:ℝ)) ≤ (((s:ℝ)*(s:ℝ))/(u:ℝ))/(s:ℝ) := div_le_div_of_nonneg_right hroundlo hs'.le
      _ = (s:ℝ)/(u:ℝ) := he _
      _ ≤ x⁻¹ := hlo
  · calc
      x⁻¹ ≤ (s:ℝ)/(l:ℝ) := hhi
      _ = (((s:ℝ)*(s:ℝ))/(l:ℝ))/(s:ℝ) := (he _).symm
      _ ≤ ((-((-(s*s))/l) : ℤ):ℝ)/(s:ℝ) := by
        simpa only [Int.cast_neg] using div_le_div_of_nonneg_right hroundhi hs'.le

/-- Integer square inequalities certify fixed-denominator outward bounds for a real square root -/
theorem fixed_sqrt_encloses : (
∀ (s l u a b : ℤ) (x : ℝ), 0 < s → 0 ≤ l → 0 ≤ a → 0 ≤ b → (l:ℝ)/(s:ℝ) ≤ x → x ≤ (u:ℝ)/(s:ℝ) → a*a ≤ l*s → u*s ≤ b*b → (a:ℝ)/(s:ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ (b:ℝ)/(s:ℝ)
) := by
  intro s l u a b x hs hl ha hb hxl hxu hal hub
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hl' : (0:ℝ) ≤ l := by exact_mod_cast hl
  have ha' : (0:ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (0:ℝ) ≤ b := by exact_mod_cast hb
  have hx : 0 ≤ x := (div_nonneg hl' hs'.le).trans hxl
  have h1 := mul_le_mul_of_nonneg_right ((div_le_iff₀ hs').mp hxl) hs'.le
  have h2 := mul_le_mul_of_nonneg_right ((le_div_iff₀ hs').mp hxu) hs'.le
  have h3 : (a:ℝ)*(a:ℝ) ≤ (l:ℝ)*(s:ℝ) := by exact_mod_cast hal
  have h4 : (u:ℝ)*(s:ℝ) ≤ (b:ℝ)*(b:ℝ) := by exact_mod_cast hub
  have hroot : (Real.sqrt x*(s:ℝ))^2 = x*(s:ℝ)^2 := by rw [mul_pow, Real.sq_sqrt hx]
  have hpos : 0 ≤ Real.sqrt x*(s:ℝ) := mul_nonneg (Real.sqrt_nonneg x) hs'.le
  constructor
  · apply (div_le_iff₀ hs').mpr
    apply (sq_le_sq₀ ha' hpos).mp
    rw [hroot]
    nlinarith only [h1, h3]
  · apply (le_div_iff₀ hs').mpr
    apply (sq_le_sq₀ hpos hb').mp
    rw [hroot]
    nlinarith only [h2, h4]

/-- Concrete flagged fixed-point primitives preserve real enclosures and certify inverse/sqrt positive domains -/
theorem fixed_primitives_sound : (
∀ (s : ℤ), 0 < s →
let I := ℤ × ℤ × Bool
let R : I → ℝ → Prop := fun a x => a.2.2 = true → (a.1:ℝ)/(s:ℝ) ≤ x ∧ x ≤ (a.2.1:ℝ)/(s:ℝ)
let q : ℤ → ℤ → I := fun a b => (a*s/b,-((-a*s)/b),decide (0<b))
let add : I → I → I := fun a b => (a.1+b.1,a.2.1+b.2.1,a.2.2 && b.2.2)
let neg : I → I := fun a => (-a.2.1,-a.1,a.2.2)
let mul : I → I → I := fun a b => (min (min (a.1*b.1) (a.1*b.2.1)) (min (a.2.1*b.1) (a.2.1*b.2.1))/s,-((-max (max (a.1*b.1) (a.1*b.2.1)) (max (a.2.1*b.1) (a.2.1*b.2.1)))/s),a.2.2 && b.2.2)
let inv : I → I := fun a => (s*s/a.2.1,-((-(s*s))/a.1),a.2.2 && decide (0<a.1 ∧ a.1≤a.2.1))
let sq : I → I := fun a =>
 let l : ℤ := Nat.sqrt (a.1*s).toNat
 let u : ℤ := (Nat.sqrt (a.2.1*s).toNat : ℤ)+1
 (l,u,a.2.2 && decide (0<a.1 ∧ 0≤l ∧ 0≤u ∧ l*l≤a.1*s ∧ a.2.1*s≤u*u))
(∀ a b, R (q a b) ((a:ℝ)/(b:ℝ))) ∧
(∀ a b x y, R a x → R b y → R (add a b) (x+y)) ∧
(∀ a x, R a x → R (neg a) (-x)) ∧
(∀ a b x y, R a x → R b y → R (mul a b) (x*y)) ∧
(∀ a x, R a x → R (inv a) x⁻¹ ∧ ((inv a).2.2 = true → 0 < x)) ∧
(∀ a x, R a x → R (sq a) (Real.sqrt x) ∧ ((sq a).2.2 = true → 0 < x))
) := by
  intro s hs
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hs0 : (s:ℝ) ≠ 0 := ne_of_gt hsR
  have hand {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa using h
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hb
    have hb' : 0 < b := of_decide_eq_true hb
    have h := int_div_bounds (a*s) b hb'
    have hmid : ((a*s:ℤ):ℝ)/(b:ℝ)/(s:ℝ) = (a:ℝ)/(b:ℝ) := by
      push_cast
      field_simp
    constructor
    · simpa only [hmid] using div_le_div_of_nonneg_right h.1 hsR.le
    · have h' := div_le_div_of_nonneg_right h.2 hsR.le
      simpa only [hmid, Int.neg_mul, Int.cast_neg, neg_div] using h'
  · intro a b x y ha hb hab
    have ha' := ha (hand hab).1
    have hb' := hb (hand hab).2
    simp only [Int.cast_add, add_div]
    exact ⟨add_le_add ha'.1 hb'.1, add_le_add ha'.2 hb'.2⟩
  · intro a x ha h
    have ha' := ha h
    simp only [Int.cast_neg, neg_div]
    exact ⟨neg_le_neg ha'.2, neg_le_neg ha'.1⟩
  · intro a b x y ha hb hab
    have ha' := ha (hand hab).1
    have hb' := hb (hand hab).2
    exact fixed_mul_encloses s a.1 a.2.1 b.1 b.2.1 x y hs ha'.1 ha'.2 hb'.1 hb'.2
  · intro a x ha
    constructor
    · intro h
      rcases hand h with ⟨hf, hd⟩
      have hd' : 0 < a.1 ∧ a.1 ≤ a.2.1 := of_decide_eq_true hd
      exact fixed_inv_encloses s a.1 a.2.1 x hs hd'.1 hd'.2 (ha hf).1 (ha hf).2
    · intro h
      rcases hand h with ⟨hf, hd⟩
      have hd' : 0 < a.1 ∧ a.1 ≤ a.2.1 := of_decide_eq_true hd
      have hl : (0:ℝ) < a.1 := by exact_mod_cast hd'.1
      exact lt_of_lt_of_le (div_pos hl hsR) (ha hf).1
  · intro a x ha
    constructor
    · intro h
      rcases hand h with ⟨hf, hd⟩
      have hd' := of_decide_eq_true hd
      exact fixed_sqrt_encloses s a.1 a.2.1 _ _ x hs (le_of_lt hd'.1) hd'.2.1 hd'.2.2.1 (ha hf).1 (ha hf).2 hd'.2.2.2.1 hd'.2.2.2.2
    · intro h
      rcases hand h with ⟨hf, hd⟩
      have hd' := of_decide_eq_true hd
      have hl : (0:ℝ) < a.1 := by exact_mod_cast hd'.1
      exact lt_of_lt_of_le (div_pos hl hsR) (ha hf).1

/-- Constant-aware optional dual numbers preserve Fréchet derivatives and two directional interval enclosures -/
theorem dual_fderiv_sound : (
∀ {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
(V : I → Prop) (R : I → ℝ → Prop)
(ia im : I → I → I) (ine ii iq : I → I) (two : I)
(hav : ∀ a b, V (ia a b) → V a ∧ V b)
(hmv : ∀ a b, V (im a b) → V a ∧ V b)
(hnv : ∀ a, V (ine a) → V a)
(hiv : ∀ a, V (ii a) → V a)
(hqv : ∀ a, V (iq a) → V a)
(ha : ∀ a b x y, R a x → R b y → R (ia a b) (x+y))
(hm : ∀ a b x y, R a x → R b y → R (im a b) (x*y))
(hn : ∀ a x, R a x → R (ine a) (-x))
(hi : ∀ a x, R a x → R (ii a) x⁻¹)
(hq : ∀ a x, R a x → R (iq a) (Real.sqrt x))
(hin : ∀ a x, R a x → V (ii a) → x ≠ 0)
(hqn : ∀ a x, R a x → V (iq a) → x ≠ 0)
(htwo : R two 2) (x e₀ e₁ : E),
let D := I × Option (I × I)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun a d => match a with
 | none => d = 0
 | some p => R p.1 (d e₀) ∧ R p.2 (d e₁)
let J : D → (E → ℝ) → Prop := fun a f => V a.1 → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R a.1 (f x) ∧ O a.2 d
let da : D → D → D := fun a b => (ia a.1 b.1, match a.2,b.2 with
 | none,v => v | v,none => v | some u,some v => some (ia u.1 v.1,ia u.2 v.2))
let dn : D → D := fun a => (ine a.1,a.2.map (fun d => (ine d.1,ine d.2)))
let dm : D → D → D := fun a b => (im a.1 b.1, match a.2,b.2 with
 | none,none => none
 | none,some v => some (im a.1 v.1,im a.1 v.2)
 | some u,none => some (im u.1 b.1,im u.2 b.1)
 | some u,some v => some (ia (im u.1 b.1) (im a.1 v.1),ia (im u.2 b.1) (im a.1 v.2)))
let di : D → D := fun a => let v := ii a.1; (v,a.2.map (fun d => (im (im (ine d.1) v) v,im (im (ine d.2) v) v)))
let dq : D → D := fun a => let v := iq a.1; let t := ii (im two v); (v,a.2.map (fun d => (im t d.1,im t d.2)))
(∀ a c, R a c → J (a,none) (fun _ => c)) ∧
(∀ a b f g, J a f → J b g → J (da a b) (fun y => f y + g y)) ∧
(∀ a f, J a f → J (dn a) (fun y => -f y)) ∧
(∀ a b f g, J a f → J b g → J (dm a b) (fun y => f y * g y)) ∧
(∀ a f, J a f → J (di a) (fun y => (f y)⁻¹)) ∧
(∀ a f, J a f → J (dq a) (fun y => Real.sqrt (f y)))
) := by
  intro E I _ _ V R ia im ine ii iq two hav hmv hnv hiv hqv ha hm hn hi hq hin hqn htwo x e₀ e₁
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c h _
    exact ⟨0, hasFDerivAt_const c x, h, rfl⟩
  · rintro ⟨av, ad⟩ ⟨bv, bd⟩ f g hf hg hv
    rcases hav av bv hv with ⟨hva,hvb⟩
    rcases hf hva with ⟨df,hdf,hrf,hof⟩
    rcases hg hvb with ⟨dg,hdg,hrg,hog⟩
    refine ⟨df+dg,hdf.add hdg,ha _ _ _ _ hrf hrg,?_⟩
    cases ad <;> cases bd <;> dsimp only at hof hog ⊢
    · simp only [hof,hog,add_zero]
    · simpa only [hof,zero_add] using hog
    · simpa only [hog,add_zero] using hof
    · simp only [add_apply]
      exact ⟨ha _ _ _ _ hof.1 hog.1,ha _ _ _ _ hof.2 hog.2⟩
  · rintro ⟨av,ad⟩ f hf hv
    rcases hf (hnv av hv) with ⟨df,hdf,hrf,hof⟩
    refine ⟨-df,hdf.neg,hn _ _ hrf,?_⟩
    cases ad <;> dsimp only [Option.map] at hof ⊢
    · simp only [hof,neg_zero]
    · simp only [neg_apply]
      exact ⟨hn _ _ hof.1,hn _ _ hof.2⟩
  · rintro ⟨av,ad⟩ ⟨bv,bd⟩ f g hf hg hv
    rcases hmv av bv hv with ⟨hva,hvb⟩
    rcases hf hva with ⟨df,hdf,hrf,hof⟩
    rcases hg hvb with ⟨dg,hdg,hrg,hog⟩
    refine ⟨g x • df + f x • dg,?_,hm _ _ _ _ hrf hrg,?_⟩
    · convert! hdf.mul hdg using 1 <;> simp only [add_comm]
    · cases ad <;> cases bd <;> dsimp only at hof hog ⊢
      · simp only [hof,hog,smul_zero,add_zero]
      · simp only [hof,smul_zero,zero_add,smul_apply,smul_eq_mul]
        exact ⟨hm _ _ _ _ hrf hog.1,hm _ _ _ _ hrf hog.2⟩
      · simp only [hog,smul_zero,add_zero,smul_apply,smul_eq_mul]
        constructor
        · simpa only [mul_comm] using hm _ _ _ _ hof.1 hrg
        · simpa only [mul_comm] using hm _ _ _ _ hof.2 hrg
      · simp only [add_apply,smul_apply,smul_eq_mul]
        constructor
        · simpa only [mul_comm] using ha _ _ _ _ (hm _ _ _ _ hof.1 hrg) (hm _ _ _ _ hrf hog.1)
        · simpa only [mul_comm] using ha _ _ _ _ (hm _ _ _ _ hof.2 hrg) (hm _ _ _ _ hrf hog.2)
  · rintro ⟨av,ad⟩ f hf hv
    rcases hf (hiv av hv) with ⟨df,hdf,hrf,hof⟩
    have hne := hin av (f x) hrf hv
    have hri := hi av (f x) hrf
    refine ⟨(-(f x ^ 2)⁻¹) • df,(hasDerivAt_inv hne).comp_hasFDerivAt x hdf,hri,?_⟩
    cases ad <;> dsimp only [Option.map] at hof ⊢
    · simp only [hof,smul_zero]
    · simp only [smul_apply,smul_eq_mul]
      have he (t : ℝ) : -(f x ^ 2)⁻¹ * t = -t * (f x)⁻¹ * (f x)⁻¹ := by rw [← inv_pow]; ring
      rw [he,he]
      exact ⟨hm _ _ _ _ (hm _ _ _ _ (hn _ _ hof.1) hri) hri,hm _ _ _ _ (hm _ _ _ _ (hn _ _ hof.2) hri) hri⟩
  · rintro ⟨av,ad⟩ f hf hv
    rcases hf (hqv av hv) with ⟨df,hdf,hrf,hof⟩
    have hne := hqn av (f x) hrf hv
    have hrq := hq av (f x) hrf
    have hrt := hi _ _ (hm _ _ _ _ htwo hrq)
    refine ⟨(2 * Real.sqrt (f x))⁻¹ • df,?_,hrq,?_⟩
    · simpa only [one_div] using hdf.sqrt hne
    · cases ad <;> dsimp only [Option.map] at hof ⊢
      · simp only [hof,smul_zero]
      · simp only [smul_apply,smul_eq_mul]
        exact ⟨hm _ _ _ _ hrt hof.1,hm _ _ _ _ hrt hof.2⟩

/-- Exact fixed-point optional AD operations enclose genuine Fréchet derivatives when their value flag is true -/
theorem fixed_ad_ops_sound : (
∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : ℤ), 0 < s → ∀ (x e₀ e₁ : E),
let I := ℤ × ℤ × Bool
let D := I × Option (I × I)
let R : I → ℝ → Prop := fun a v => a.2.2 = true → (a.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (a.2.1:ℝ)/(s:ℝ)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun a d => match a with
 | none => d = 0 | some p => R p.1 (d e₀) ∧ R p.2 (d e₁)
let J : D → (E → ℝ) → Prop := fun a f => a.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R a.1 (f x) ∧ O a.2 d
let q : ℤ → ℤ → I := fun a b => (a*s/b,-((-a*s)/b),decide (0<b))
let ia : I → I → I := fun a b => (a.1+b.1,a.2.1+b.2.1,a.2.2 && b.2.2)
let ine : I → I := fun a => (-a.2.1,-a.1,a.2.2)
let im : I → I → I := fun a b => (min (min (a.1*b.1) (a.1*b.2.1)) (min (a.2.1*b.1) (a.2.1*b.2.1))/s,-((-max (max (a.1*b.1) (a.1*b.2.1)) (max (a.2.1*b.1) (a.2.1*b.2.1)))/s),a.2.2 && b.2.2)
let ii : I → I := fun a => (s*s/a.2.1,-((-(s*s))/a.1),a.2.2 && decide (0<a.1 ∧ a.1≤a.2.1))
let iq : I → I := fun a =>
 let l : ℤ := Nat.sqrt (a.1*s).toNat
 let u : ℤ := (Nat.sqrt (a.2.1*s).toNat : ℤ)+1
 (l,u,a.2.2 && decide (0<a.1 ∧ 0≤l ∧ 0≤u ∧ l*l≤a.1*s ∧ a.2.1*s≤u*u))
let da : D → D → D := fun a b => (ia a.1 b.1, match a.2,b.2 with
 | none,v => v | v,none => v | some u,some v => some (ia u.1 v.1,ia u.2 v.2))
let dn : D → D := fun a => (ine a.1,a.2.map (fun d => (ine d.1,ine d.2)))
let dm : D → D → D := fun a b => (im a.1 b.1, match a.2,b.2 with
 | none,none => none
 | none,some v => some (im a.1 v.1,im a.1 v.2)
 | some u,none => some (im u.1 b.1,im u.2 b.1)
 | some u,some v => some (ia (im u.1 b.1) (im a.1 v.1),ia (im u.2 b.1) (im a.1 v.2)))
let di : D → D := fun a => let v := ii a.1; (v,a.2.map (fun d => (im (im (ine d.1) v) v,im (im (ine d.2) v) v)))
let dq : D → D := fun a => let v := iq a.1; let t := ii (im (q 2 1) v); (v,a.2.map (fun d => (im t d.1,im t d.2)))
(∀ a c, R a c → J (a,none) (fun _ => c)) ∧
(∀ a b f g, J a f → J b g → J (da a b) (fun y => f y + g y)) ∧
(∀ a f, J a f → J (dn a) (fun y => -f y)) ∧
(∀ a b f g, J a f → J b g → J (dm a b) (fun y => f y * g y)) ∧
(∀ a f, J a f → J (di a) (fun y => (f y)⁻¹)) ∧
(∀ a f, J a f → J (dq a) (fun y => Real.sqrt (f y)))
) := by
  intro E _ _ s hs x e₀ e₁
  rcases fixed_primitives_sound s hs with ⟨hc,ha,hn,hm,hi,hq⟩
  have hand {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa using h
  dsimp only
  refine dual_fderiv_sound (fun a : ℤ × ℤ × Bool => a.2.2 = true) _ _ _ _
    (fun a => (s*s/a.2.1,-((-(s*s))/a.1),a.2.2 && decide (0<a.1 ∧ a.1≤a.2.1)))
    (fun a => let l : ℤ := Nat.sqrt (a.1*s).toNat; let u : ℤ := (Nat.sqrt (a.2.1*s).toNat : ℤ)+1; (l,u,a.2.2 && decide (0<a.1 ∧ 0≤l ∧ 0≤u ∧ l*l≤a.1*s ∧ a.2.1*s≤u*u)))
    (2*s/1,-((-2*s)/1),decide (0<(1:ℤ)))
    ?_ ?_ ?_ ?_ ?_ ha hm hn ?_ ?_ ?_ ?_ ?_ x e₀ e₁
  · intro a b h; exact hand h
  · intro a b h; exact hand h
  · intro a h; exact h
  · intro a h; exact (hand h).1
  · intro a h; exact (hand h).1
  · intro a y h; exact (hi a y h).1
  · intro a y h; exact (hq a y h).1
  · intro a y h hv; exact ne_of_gt ((hi a y h).2 hv)
  · intro a y h hv; exact ne_of_gt ((hq a y h).2 hv)
  · simpa using hc 2 1

/-- Complex pair arithmetic and real scaling preserve sound scalar function relations -/
theorem complex_pair_ops_sound : (
∀ {E D : Type} (J : D → (E → ℝ) → Prop) (da dm : D → D → D) (dn di : D → D)
(ha : ∀ a b f g, J a f → J b g → J (da a b) (fun y => f y + g y))
(hm : ∀ a b f g, J a f → J b g → J (dm a b) (fun y => f y * g y))
(hn : ∀ a f, J a f → J (dn a) (fun y => -f y))
(hi : ∀ a f, J a f → J (di a) (fun y => (f y)⁻¹)),
let Z := D × D
let K : Z → (E → ℂ) → Prop := fun a f => J a.1 (fun x => (f x).re) ∧ J a.2 (fun x => (f x).im)
let ds : D → D → D := fun a b => da a (dn b)
let za : Z → Z → Z := fun a b => (da a.1 b.1,da a.2 b.2)
let zn : Z → Z := fun a => (dn a.1,dn a.2)
let zs : Z → Z → Z := fun a b => za a (zn b)
let zm : Z → Z → Z := fun a b => (ds (dm a.1 b.1) (dm a.2 b.2),da (dm a.1 b.2) (dm a.2 b.1))
let zi : Z → Z := fun a => let t := di (da (dm a.1 a.1) (dm a.2 a.2)); (dm a.1 t,dm (dn a.2) t)
let zsc : Z → D → Z := fun a b => (dm a.1 b,dm a.2 b)
(∀ a b f g, K a f → K b g → K (za a b) (fun x => f x + g x)) ∧
(∀ a f, K a f → K (zn a) (fun x => -f x)) ∧
(∀ a b f g, K a f → K b g → K (zs a b) (fun x => f x - g x)) ∧
(∀ a b f g, K a f → K b g → K (zm a b) (fun x => f x * g x)) ∧
(∀ a f, K a f → K (zi a) (fun x => (f x)⁻¹)) ∧
(∀ a b f g, K a f → J b g → K (zsc a b) (fun x => f x * (g x:ℂ))) ∧
(∀ a b f g, J a f → J b g → K (a,b) (fun x => (f x:ℂ)+(g x:ℂ)*Complex.I))
) := by
  intro E D J da dm dn di ha hm hn hi
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro a b f g hf hg
    exact ⟨ha _ _ _ _ hf.1 hg.1,ha _ _ _ _ hf.2 hg.2⟩
  · intro a f hf
    exact ⟨hn _ _ hf.1,hn _ _ hf.2⟩
  · intro a b f g hf hg
    simpa only [Complex.sub_re,Complex.sub_im,sub_eq_add_neg,Complex.add_re,Complex.add_im,Complex.neg_re,Complex.neg_im] using
      And.intro (ha _ _ _ _ hf.1 (hn _ _ hg.1)) (ha _ _ _ _ hf.2 (hn _ _ hg.2))
  · intro a b f g hf hg
    simpa only [Complex.mul_re,Complex.mul_im,sub_eq_add_neg] using
      And.intro (ha _ _ _ _ (hm _ _ _ _ hf.1 hg.1) (hn _ _ (hm _ _ _ _ hf.2 hg.2)))
        (ha _ _ _ _ (hm _ _ _ _ hf.1 hg.2) (hm _ _ _ _ hf.2 hg.1))
  · intro a f hf
    have ht := hi _ _ (ha _ _ _ _ (hm _ _ _ _ hf.1 hf.1) (hm _ _ _ _ hf.2 hf.2))
    simpa only [Complex.inv_re,Complex.inv_im,Complex.normSq_apply,div_eq_mul_inv] using
      And.intro (hm _ _ _ _ hf.1 ht) (hm _ _ _ _ (hn _ _ hf.2) ht)
  · intro a b f g hf hg
    simpa only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,zero_add] using
      And.intro (hm _ _ _ _ hf.1 hg) (hm _ _ _ _ hf.2 hg)
  · intro a b f g hf hg
    simpa only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add] using And.intro hf hg

end Atiyah.Facts

/-! ### `Atiyah.Facts`: Lists -/

/-!
# Relational transport lemmas for list programs

Small lemmas showing that the list operations used by the numerical program preserve pointwise relations.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- List.Forall₂ is preserved by getD defaults and same-index set updates -/
theorem forall₂_getD_set : (
∀ {A B : Type} (R : A → B → Prop) (l : List A) (k : List B), List.Forall₂ R l k → ∀ a b, R a b → ∀ n : ℕ, R (l.getD n a) (k.getD n b) ∧ List.Forall₂ R (l.set n a) (k.set n b)
) := by
  intro A B R l k h
  induction h with
  | nil =>
    intro a b hab n
    simpa using And.intro hab (List.Forall₂.nil : List.Forall₂ R [] [])
  | @cons x y l k hxy hl ih =>
    intro a b hab n
    cases n with
    | zero => simpa using And.intro hxy (List.Forall₂.cons hab hl)
    | succ n =>
      rcases ih a b hab n with ⟨hget,hset⟩
      simpa using And.intro hget (List.Forall₂.cons hxy hset)

/-- List.zipWith preserves relations between arbitrary paired operand lists -/
theorem forall₂_zipWith : (
∀ {A B C D F G : Type} (R : A → B → Prop) (S : C → D → Prop) (T : F → G → Prop) (f : A → C → F) (g : B → D → G), (∀ a b c d, R a b → S c d → T (f a c) (g b d)) → ∀ (l : List A) (k : List B) (u : List C) (v : List D), List.Forall₂ R l k → List.Forall₂ S u v → List.Forall₂ T (List.zipWith f l u) (List.zipWith g k v)
) := by
  intro A B C D F G R S T f g hf l k u v hl
  induction hl generalizing u v with
  | nil => intro hu; simp
  | @cons a b l k hab hl ih =>
    intro hu
    cases hu with
    | nil => simp
    | cons hcd huv =>
      exact List.Forall₂.cons (hf _ _ _ _ hab hcd) (ih _ _ huv)

/-- List.mapIdx preserves element relations under a same-index relational map -/
theorem forall₂_mapIdx : (
∀ {A B C D : Type} (R : A → B → Prop) (S : C → D → Prop) (l : List A) (k : List B), List.Forall₂ R l k → ∀ (f : ℕ → A → C) (g : ℕ → B → D), (∀ n a b, R a b → S (f n a) (g n b)) → List.Forall₂ S (l.mapIdx f) (k.mapIdx g)
) := by
  intro A B C D R S l k h
  induction h with
  | nil => intro f g hf; simp
  | @cons a b l k hab hl ih =>
    intro f g hf
    simpa only [List.mapIdx_cons] using List.Forall₂.cons (hf 0 a b hab) (ih (fun n a => f (n+1) a) (fun n b => g (n+1) b) (fun n a b h => hf (n+1) a b h))

/-- Bounded checked transitions determine the fold over any consecutive range of stages -/
theorem fold_of_checked_transitions : (
∀ {α : Type} (f : α → ℕ → α) (v : ℕ → α) (n a : ℕ), (∀ k < n, f (v k) (k+a) = v (k+1)) → ((List.range n).map (fun k => k+a)).foldl f (v 0) = v n
) := by
  intro α f v n
  induction n with
  | zero => intro a h; rfl
  | succ n ih =>
    intro a h
    rw [List.range_succ, List.map_append, List.foldl_append]
    simpa only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      ih a (fun k hk => h k (Nat.lt_succ_of_lt hk))] using h n (Nat.lt_succ_self n)

end Atiyah.Facts

/-! ### `Atiyah.Facts`: Defs -/

/-!
# Point polynomials, coefficient matrices and lift conventions

The pinned definitions from the formal conjecture, the equivalence between linear independence of the
point polynomials and a nonzero coefficient determinant, and the freedom to rescale or re-chart lifts.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- Binary product coefficients vanish outside the n degree-(n−1) monomials -/
theorem binary_product_support : (
∀ {n : ℕ} (z w : Fin n → Fin n → ℂ) (i : Fin n) (d : Fin 2 →₀ ℕ),
    (∀ k : Fin n, d ≠ Finsupp.single 0 (n - 1 - k.val) + Finsupp.single 1 k.val) →
  MvPolynomial.coeff d (∏ j ∈ Finset.univ.erase i,
    (MvPolynomial.C (z i j) * MvPolynomial.X (0 : Fin 2) -
     MvPolynomial.C (w i j) * MvPolynomial.X 1)) = 0
) := by
  intro n z w i d hd
  classical
  have hhom : MvPolynomial.IsHomogeneous (∏ j ∈ Finset.univ.erase i,
      (MvPolynomial.C (z i j) * MvPolynomial.X (0 : Fin 2) -
       MvPolynomial.C (w i j) * MvPolynomial.X 1)) (n - 1) := by
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ.erase i)
      (fun j => MvPolynomial.C (z i j) * MvPolynomial.X (0 : Fin 2) -
        MvPolynomial.C (w i j) * MvPolynomial.X 1) (fun _ => 1)
      (fun j _ => (MvPolynomial.isHomogeneous_C_mul_X (z i j) (0 : Fin 2)).sub
        (MvPolynomial.isHomogeneous_C_mul_X (w i j) 1))
    simpa using h
  apply hhom.coeff_eq_zero
  intro he
  have hs : d 0 + d 1 = n - 1 := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_succ] using he
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hk : d 1 < n := by omega
  apply hd ⟨d 1, hk⟩
  ext k
  fin_cases k <;> simp <;> omega

/-- Supported binary polynomial independence iff coefficient matrix determinant is nonzero -/
theorem independent_iff_det_ne_zero : (
∀ {n : ℕ} (p : Fin n → MvPolynomial (Fin 2) ℂ),
    (∀ (i : Fin n) (d : Fin 2 →₀ ℕ),
      (∀ k : Fin n, d ≠ Finsupp.single 0 (n - 1 - k.val) + Finsupp.single 1 k.val) →
      MvPolynomial.coeff d (p i) = 0) →
  (LinearIndependent ℂ p ↔
    Matrix.det (fun k i : Fin n => MvPolynomial.coeff
      (Finsupp.single 0 (n - 1 - k.val) + Finsupp.single 1 k.val) (p i)) ≠ 0)
) := by
  intro n p hp
  classical
  let m : Fin n → Fin 2 →₀ ℕ := fun k =>
    Finsupp.single 0 (n - 1 - k.val) + Finsupp.single 1 k.val
  let M : Matrix (Fin n) (Fin n) ℂ := fun k i => MvPolynomial.coeff (m k) (p i)
  have heq : LinearIndependent ℂ p ↔ LinearIndependent ℂ M.col := by
    rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
    constructor
    · intro h c hc
      apply h c
      apply MvPolynomial.ext
      intro d
      by_cases hd : ∃ k : Fin n, d = m k
      · obtain ⟨k, rfl⟩ := hd
        have hk := congrFun hc k
        simpa [M, Matrix.col, Matrix.transpose, MvPolynomial.coeff_sum] using hk
      · simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
          MvPolynomial.coeff_zero, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i hi
        rw [hp i d (fun k hk => hd ⟨k, hk⟩), mul_zero]
    · intro h c hc
      apply h c
      funext k
      have hk := congrArg (MvPolynomial.coeff (m k)) hc
      simpa [M, Matrix.col, Matrix.transpose, MvPolynomial.coeff_sum] using hk
  change LinearIndependent ℂ p ↔ M.det ≠ 0
  rw [heq, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero]

/-- Dehomogenization preserves every supported degree-(n−1) binary coefficient -/
theorem dehomogenize_coeff : (
∀ (n : ℕ) (p : MvPolynomial (Fin 2) ℂ),
 (∀ d : Fin 2 →₀ ℕ, (∀ k : Fin n, d ≠ Finsupp.single 0 (n-1-k.val) + Finsupp.single 1 k.val) → MvPolynomial.coeff d p = 0) →
 ∀ k : Fin n, (MvPolynomial.eval₂ Polynomial.C ![(1:Polynomial ℂ),Polynomial.X] p).coeff k.val = MvPolynomial.coeff (Finsupp.single 0 (n-1-k.val) + Finsupp.single 1 k.val) p
) := by
  classical
  intro n p hp k
  let m : Fin n → Fin 2 →₀ ℕ := fun j => Finsupp.single 0 (n-1-j.val) + Finsupp.single 1 j.val
  have hm : Function.Injective m := by
   intro a b hab
   have hh := congrArg (fun d : Fin 2 →₀ ℕ => d 1) hab
   apply Fin.ext
   simpa [m] using hh
  have hex : p = ∑ j : Fin n, MvPolynomial.monomial (m j) (MvPolynomial.coeff (m j) p) := by
   ext d
   simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
   by_cases hd : ∃ j, d = m j
   · obtain ⟨j,rfl⟩ := hd
     simp [hm.eq_iff]
   · rw [hp d (fun j hj => hd ⟨j,hj⟩)]
     symm
     apply Finset.sum_eq_zero
     intro j hj
     simp [show m j ≠ d by intro h; exact hd ⟨j,h.symm⟩]
  let ev : MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C ![1,Polynomial.X]
  change (ev p).coeff k.val = MvPolynomial.coeff (m k) p
  have hev (j : Fin n) (c : ℂ) : ev (MvPolynomial.monomial (m j) c) = Polynomial.C c * Polynomial.X ^ j.val := by
   simp [ev, MvPolynomial.eval₂_monomial, Fin.prod_univ_two, m]
  calc
   (ev p).coeff k.val = (ev (∑ j : Fin n, MvPolynomial.monomial (m j) (MvPolynomial.coeff (m j) p))).coeff k.val := congrArg (fun t => (ev t).coeff k.val) hex
   _ = (∑ j : Fin n, Polynomial.C (MvPolynomial.coeff (m j) p) * Polynomial.X ^ j.val).coeff k.val := by simp only [map_sum, hev]
   _ = MvPolynomial.coeff (m k) p := by simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj]

/-- Binary point-product independence is equivalent to nonzero determinant of univariate coefficients -/
theorem independent_iff_univariate_det_ne_zero : (
∀ {n : ℕ} (z w : Fin n → Fin n → ℂ),
 (LinearIndependent ℂ (fun i : Fin n => ∏ j ∈ Finset.univ.erase i, (MvPolynomial.C (z i j) * MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (w i j) * MvPolynomial.X 1))) ↔
 Matrix.det (fun k i : Fin n => (∏ j ∈ Finset.univ.erase i, (Polynomial.C (z i j) - Polynomial.C (w i j)*Polynomial.X)).coeff k.val) ≠ 0
) := by
  classical
  intro n z w
  let p := fun i : Fin n => ∏ j ∈ Finset.univ.erase i, (MvPolynomial.C (z i j)*MvPolynomial.X (0 : Fin 2) - MvPolynomial.C (w i j)*MvPolynomial.X 1)
  have hs := binary_product_support z w
  have hdet := independent_iff_det_ne_zero p hs
  have hc (k i : Fin n) := dehomogenize_coeff n (p i) (hs i) k
  have hm : (fun k i : Fin n => MvPolynomial.coeff (Finsupp.single 0 (n-1-k.val) + Finsupp.single 1 k.val) (p i)) = (fun k i : Fin n => (∏ j ∈ Finset.univ.erase i, (Polynomial.C (z i j)-Polynomial.C (w i j)*Polynomial.X)).coeff k.val) := by
   funext k i
   symm
   simpa [p, MvPolynomial.eval₂_prod] using hc k i
  rw [hm] at hdet
  exact hdet

/-- Nonzero projective edge rescalings preserve independence of binary product families -/
theorem rescaling_preserves_independence : (
∀ {n : ℕ} (z w a : Fin n → Fin n → ℂ),
    (∀ i j, i ≠ j → a i j ≠ 0) →
  (LinearIndependent ℂ (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
    (MvPolynomial.C (a i j * z i j) * MvPolynomial.X (0 : Fin 2) -
     MvPolynomial.C (a i j * w i j) * MvPolynomial.X 1)) ↔
  LinearIndependent ℂ (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
    (MvPolynomial.C (z i j) * MvPolynomial.X (0 : Fin 2) -
     MvPolynomial.C (w i j) * MvPolynomial.X 1)))
) := by
  intro n z w a ha
  classical
  let A : Fin n → ℂ := fun i => ∏ j ∈ Finset.univ.erase i, a i j
  let p : Fin n → MvPolynomial (Fin 2) ℂ := fun i => ∏ j ∈ Finset.univ.erase i,
    (MvPolynomial.C (z i j) * MvPolynomial.X 0 - MvPolynomial.C (w i j) * MvPolynomial.X 1)
  have hA : ∀ i, A i ≠ 0 := by
    intro i
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact ha i j (Finset.ne_of_mem_erase hj).symm
  have heq : (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
      (MvPolynomial.C (a i j * z i j) * MvPolynomial.X (0 : Fin 2) -
       MvPolynomial.C (a i j * w i j) * MvPolynomial.X 1)) =
      (fun i => A i • p i) := by
    funext i
    dsimp [A, p]
    rw [← MvPolynomial.C_mul', map_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [map_mul]
    ring
  rw [heq]
  exact LinearIndependent.units_smul_iff (R := ℂ) p (fun i => Units.mk0 (A i) (hA i))

/-- Pole-free chart equivalence between raw continuous lifts and the exact pinned piecewise lifts -/
theorem raw_lift_chart_equivalence : (
∀ {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)),
  (∀ i j, i ≠ j → ‖x j - x i‖ - (x j - x i) 2 ≠ 0) →
  let L : EuclideanSpace ℝ (Fin 3) → ℂ × ℂ := fun v =>
    if ‖v‖ - v 2 = 0 then (1, 0)
    else (((v 0 : ℂ) + (v 1 : ℂ) * Complex.I) / (‖v‖ - v 2 : ℝ), 1)
  (LinearIndependent ℂ (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
    (MvPolynomial.C (((x j - x i) 0 : ℂ) + ((x j - x i) 1 : ℂ) * Complex.I) *
       MvPolynomial.X (0 : Fin 2) -
     MvPolynomial.C ((‖x j - x i‖ - (x j - x i) 2 : ℝ) : ℂ) * MvPolynomial.X 1)) ↔
   LinearIndependent ℂ (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
    (MvPolynomial.C (L (x j - x i)).1 * MvPolynomial.X (0 : Fin 2) -
     MvPolynomial.C (L (x j - x i)).2 * MvPolynomial.X 1)))
) := by
  intro n x hchart
  classical
  let L : EuclideanSpace ℝ (Fin 3) → ℂ × ℂ := fun v =>
    if ‖v‖ - v 2 = 0 then (1, 0)
    else (((v 0 : ℂ) + (v 1 : ℂ) * Complex.I) / (‖v‖ - v 2 : ℝ), 1)
  let a : Fin n → Fin n → ℂ := fun i j => ((‖x j - x i‖ - (x j - x i) 2 : ℝ) : ℂ)
  have ha : ∀ i j, i ≠ j → a i j ≠ 0 := by
    intro i j hij
    dsimp [a]
    exact_mod_cast hchart i j hij
  have hscale := rescaling_preserves_independence
    (fun i j => (L (x j - x i)).1) (fun i j => (L (x j - x i)).2) a ha
  have heq : (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
      (MvPolynomial.C (a i j * (L (x j - x i)).1) * MvPolynomial.X (0 : Fin 2) -
       MvPolynomial.C (a i j * (L (x j - x i)).2) * MvPolynomial.X 1)) =
      (fun i : Fin n => ∏ j ∈ Finset.univ.erase i,
      (MvPolynomial.C (((x j - x i) 0 : ℂ) + ((x j - x i) 1 : ℂ) * Complex.I) *
         MvPolynomial.X (0 : Fin 2) -
       MvPolynomial.C ((‖x j - x i‖ - (x j - x i) 2 : ℝ) : ℂ) * MvPolynomial.X 1)) := by
    funext i
    apply Finset.prod_congr rfl
    intro j hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hden : ((‖x j - x i‖ - (x j - x i) 2 : ℝ) : ℂ) ≠ 0 := ha i j hij
    simp only [L, if_neg (hchart i j hij), a, mul_one]
    congr 3
    field_simp
  rw [heq] at hscale
  exact hscale

/-- Injective horizontal projections imply injective configurations and nonzero chart denominators -/
theorem injective_of_horizontal_projection : (
∀ (ι : Type) (x : ι → EuclideanSpace ℝ (Fin 3)),
    Function.Injective (fun i => (x i 0, x i 1)) →
    Function.Injective x ∧
      (∀ i j, i ≠ j → ‖x j - x i‖ - (x j - x i) 2 ≠ 0)
) := by
  intro ι x hp
  constructor
  · intro i j hij
    exact hp (congrArg (fun v : EuclideanSpace ℝ (Fin 3) => (v 0, v 1)) hij)
  · intro i j hij hden
    have hs : ‖x j - x i‖ ^ 2 = ((x j - x i) 0) ^ 2 +
        ((x j - x i) 1) ^ 2 + ((x j - x i) 2) ^ 2 := by
      simpa [Fin.sum_univ_succ, add_assoc] using EuclideanSpace.real_norm_sq_eq (x j - x i)
    rw [sub_eq_zero.mp hden] at hs
    have h0 : (x j - x i) 0 = 0 := by nlinarith [sq_nonneg ((x j - x i) 1)]
    have h1 : (x j - x i) 1 = 0 := by nlinarith [sq_nonneg ((x j - x i) 0)]
    have h0' : x j 0 = x i 0 := by simpa only [PiLp.sub_apply, sub_eq_zero] using h0
    have h1' : x j 1 = x i 1 := by simpa only [PiLp.sub_apply, sub_eq_zero] using h1
    exact hij (hp (Prod.ext h0' h1')).symm

/-- Positive signed odd-height paired configurations are injective and avoid every stereographic chart pole -/
theorem odd_height_family_injective_pole_free : (
∀ {m : ℕ} (x : Fin m × Fin 2 → EuclideanSpace ℝ (Fin 3)) (b : ℝ), 0 < b → (∀ i, x i 1 = (if i.2 = 0 then (1:ℝ) else -1) * (2*(i.1.val:ℝ)+1) * b) → Function.Injective x ∧ (∀ i j, i ≠ j → ‖x j - x i‖ - (x j - x i) 2 ≠ 0)
) := by
  intro m x b hb hx
  apply injective_of_horizontal_projection (Fin m × Fin 2) x
  rintro ⟨i,a⟩ ⟨j,c⟩ he
  have h := congrArg Prod.snd he
  dsimp only at h
  rw [hx, hx] at h
  have heq := mul_right_cancel₀ (ne_of_gt hb) h
  fin_cases a <;> fin_cases c <;> norm_num at heq
  all_goals
    first
    | exact Prod.ext (Fin.ext heq) rfl
    | exfalso
      nlinarith [Nat.cast_nonneg (α := ℝ) i.val, Nat.cast_nonneg (α := ℝ) j.val]

/-- Ordered interval midpoints and exact odd heights give enclosed injective pole-free half-turn points -/
theorem cert_midpoints_injective_pole_free : (
∀ (m : ℕ) (s B H : ℤ), 0 < s → 0 < B → 0 < H →
∀ (p : Fin m → (ℤ × ℤ × Bool) × (ℤ × ℤ × Bool) × (ℤ × ℤ × Bool)),
(∀ i, (p i).1.1 ≤ (p i).1.2.1 ∧ (p i).2.2.1 ≤ (p i).2.2.2.1 ∧
 (p i).2.1.1 * H ≤ (2*(i.val:ℤ)+1)*B*s ∧
 (2*(i.val:ℤ)+1)*B*s ≤ (p i).2.1.2.1*H) →
let I := ℤ × ℤ × Bool
let mid : I → ℝ := fun a => ((a.1:ℝ)+(a.2.1:ℝ))/(2*(s:ℝ))
let neg : I → I := fun a => (-a.2.1,-a.1,a.2.2)
let R : I → ℝ → Prop := fun a v => a.2.2 = true → (a.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (a.2.1:ℝ)/(s:ℝ)
let pts : Fin m × Fin 2 → I × I × I := fun i =>
 if i.2 = 0 then p i.1 else (neg (p i.1).1,neg (p i.1).2.1,(p i.1).2.2)
let x : Fin m × Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i => WithLp.toLp 2
 ![(if i.2 = 0 then (1:ℝ) else -1) * mid (p i.1).1,
   (if i.2 = 0 then (1:ℝ) else -1) * (2*(i.1.val:ℝ)+1) * ((B:ℝ)/(H:ℝ)),
   mid (p i.1).2.2]
Function.Injective x ∧
(∀ i j, i ≠ j → ‖x j - x i‖ - (x j - x i) 2 ≠ 0) ∧
(∀ i, R (pts i).1 (x i 0) ∧ R (pts i).2.1 (x i 1) ∧ R (pts i).2.2 (x i 2))
) := by
  intro m s B H hs hB hH p hp I mid neg R pts x
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hH' : (0:ℝ) < H := by exact_mod_cast hH
  have hB' : (0:ℝ) < B := by exact_mod_cast hB
  have hb : (0:ℝ) < (B:ℝ)/(H:ℝ) := div_pos hB' hH'
  have geom := odd_height_family_injective_pole_free x ((B:ℝ)/(H:ℝ)) hb (by intro i; rfl)
  refine ⟨geom.1, geom.2, ?_⟩
  have hm (a : I) (h : a.1 ≤ a.2.1) : R a (mid a) := by
   intro _
   have h' : (a.1:ℝ) ≤ a.2.1 := by exact_mod_cast h
   dsimp [mid]
   constructor
   · apply (div_le_div_iff₀ hs' (mul_pos (by norm_num) hs')).mpr
     nlinarith
   · apply (div_le_div_iff₀ (mul_pos (by norm_num) hs') hs').mpr
     nlinarith
  have hn (a : I) (v : ℝ) (h : R a v) : R (neg a) (-v) := by
   intro hv
   have h' := h hv
   dsimp [neg]
   simp only [Int.cast_neg, neg_div]
   constructor <;> linarith
  intro i
  obtain ⟨h0,h2,hyl,hyu⟩ := hp i.1
  have h0' := hm (p i.1).1 h0
  have h2' := hm (p i.1).2.2 h2
  have hy : R (p i.1).2.1 ((2*(i.1.val:ℝ)+1)*((B:ℝ)/(H:ℝ))) := by
   intro _
   have hl : ((p i.1).2.1.1:ℝ)*(H:ℝ) ≤ (2*(i.1.val:ℝ)+1)*(B:ℝ)*(s:ℝ) := by exact_mod_cast hyl
   have hu : (2*(i.1.val:ℝ)+1)*(B:ℝ)*(s:ℝ) ≤ ((p i.1).2.1.2.1:ℝ)*(H:ℝ) := by exact_mod_cast hyu
   rw [← mul_div_assoc]
   exact ⟨(div_le_div_iff₀ hs' hH').mpr hl, (div_le_div_iff₀ hH' hs').mpr hu⟩
  by_cases h : i.2 = 0
  · simpa [pts,x,h] using And.intro h0' (And.intro hy h2')
  · have hy' : R (neg (p i.1).2.1) ((-1:ℝ)*(2*(i.1.val:ℝ)+1)*((B:ℝ)/(H:ℝ))) := by
     convert hn _ _ hy using 1 <;> ring
    simpa [pts,x,h] using And.intro (hn _ _ h0') (And.intro hy' h2')

/-- Exact concatenated half-turn point lists enclose the injective midpoint geometry -/
theorem cert_point_lists_enclose : (
∀ (m : ℕ) (s B H : ℤ), 0 < s → 0 < B → 0 < H →
let I := ℤ × ℤ × Bool
∀ (ps : List (I × I × I)) (pz : I × I × I), ps.length = m →
(∀ i : Fin m, let p := ps.getD i.val pz
 p.1.1 ≤ p.1.2.1 ∧ p.2.2.1 ≤ p.2.2.2.1 ∧
 p.2.1.1 * H ≤ (2*(i.val:ℤ)+1)*B*s ∧
 (2*(i.val:ℤ)+1)*B*s ≤ p.2.1.2.1*H) →
let mid : I → ℝ := fun a => ((a.1:ℝ)+(a.2.1:ℝ))/(2*(s:ℝ))
let neg : I → I := fun a => (-a.2.1,-a.1,a.2.2)
let R : I → ℝ → Prop := fun a v => a.2.2 = true → (a.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (a.2.1:ℝ)/(s:ℝ)
let T : (I × I × I) → EuclideanSpace ℝ (Fin 3) → Prop := fun p x => R p.1 (x 0) ∧ R p.2.1 (x 1) ∧ R p.2.2 (x 2)
let pts := ps ++ ps.map (fun p => (neg p.1,neg p.2.1,p.2.2))
let x : Fin m × Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i =>
 let p := ps.getD i.1.val pz
 WithLp.toLp 2 ![(if i.2 = 0 then (1:ℝ) else -1) * mid p.1,
 (if i.2 = 0 then (1:ℝ) else -1) * (2*(i.1.val:ℝ)+1) * ((B:ℝ)/(H:ℝ)),mid p.2.2]
let qts := List.ofFn (fun i : Fin m => x (i,0)) ++ List.ofFn (fun i : Fin m => x (i,1))
Function.Injective x ∧
(∀ i j, i ≠ j → ‖x j - x i‖ - (x j - x i) 2 ≠ 0) ∧
List.Forall₂ T pts qts
) := by
  intro m s B H hs hB hH I ps pz hlen hp mid neg R T pts x qts
  have hg := cert_midpoints_injective_pole_free m s B H hs hB hH (fun i => ps.getD i.val pz) hp
  change Function.Injective x ∧ (∀ i j, i ≠ j → ‖x j-x i‖-(x j-x i) 2 ≠ 0) ∧
    (∀ i : Fin m × Fin 2, T (if i.2 = 0 then ps.getD i.1.val pz else (neg (ps.getD i.1.val pz).1,neg (ps.getD i.1.val pz).2.1,(ps.getD i.1.val pz).2.2)) (x i)) at hg
  refine ⟨hg.1,hg.2.1,?_⟩
  have hpos : List.Forall₂ T ps (List.ofFn (fun i : Fin m => x (i,0))) := by
    apply List.forall₂_of_length_eq_of_get (by simpa using hlen)
    intro i hi hj
    have hi' : i < m := by omega
    have h := hg.2.2 (⟨i,hi'⟩,0)
    simpa [List.getD, hi, List.get_ofFn] using h
  have hneg : List.Forall₂ T (ps.map (fun p => (neg p.1,neg p.2.1,p.2.2))) (List.ofFn (fun i : Fin m => x (i,1))) := by
    apply List.forall₂_of_length_eq_of_get (by simpa using hlen)
    intro i hi hj
    have hi0 : i < ps.length := by simpa using hi
    have hi' : i < m := by omega
    have h := hg.2.2 (⟨i,hi'⟩,1)
    simpa [List.getD, hi0, List.get_ofFn] using h
  exact List.rel_append hpos hneg

end Atiyah.Facts

/-! ### `Atiyah.Facts`: HalfTurn -/

/-!
# Half-turn symmetric configurations

A configuration invariant under a half-turn has even coefficients of opposite sign on paired points, so
a relation among the even columns of the first half already forces dependence of all point polynomials.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- Half-turn paired 46-point raw polynomials have opposite even coefficients -/
theorem half_turn_even_coeff_parity : (
∀ (x : Fin 46 → EuclideanSpace ℝ (Fin 3)) (e : Equiv.Perm (Fin 46)),
 (∀ i, x (e i) = WithLp.toLp 2 ![-x i 0,-x i 1,x i 2]) →
 let P : Fin 46 → Polynomial ℂ := fun i => ∏ j ∈ Finset.univ.erase i,
  (Polynomial.C (((x j-x i) 0:ℂ)+((x j-x i) 1:ℂ)*Complex.I) - Polynomial.C ((‖x j-x i‖-(x j-x i) 2:ℝ):ℂ)*Polynomial.X)
 ∀ i k, (P (e i)).coeff (2*k) = -(P i).coeff (2*k)
) := by
  classical
  intro x e hx P i k
  let H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun v => WithLp.toLp 2 ![-v 0,-v 1,v 2]
  let F : EuclideanSpace ℝ (Fin 3) → Polynomial ℂ := fun v => Polynomial.C ((v 0:ℂ)+(v 1:ℂ)*Complex.I) - Polynomial.C ((‖v‖-v 2:ℝ):ℂ)*Polynomial.X
  have hnorm (v : EuclideanSpace ℝ (Fin 3)) : ‖H v‖ = ‖v‖ := by
   have h1 := EuclideanSpace.real_norm_sq_eq (H v)
   have h2 := EuclideanSpace.real_norm_sq_eq v
   simp [H, Fin.sum_univ_succ] at h1 h2
   nlinarith [norm_nonneg (H v), norm_nonneg v]
  have hF (v : EuclideanSpace ℝ (Fin 3)) : F (H v) = -(F v).comp (-Polynomial.X) := by
   dsimp only [F]
   rw [hnorm]
   have h0 : H v 0 = -v 0 := rfl
   have h1 : H v 1 = -v 1 := rfl
   have h2 : H v 2 = v 2 := rfl
   rw [h0,h1,h2]
   simp only [Complex.ofReal_neg, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp, neg_mul, ← neg_add, map_neg]
   ring
  have hdiff (a b : Fin 46) : x (e b) - x (e a) = H (x b-x a) := by
   rw [hx, hx]
   ext t
   fin_cases t <;> simp [H] <;> ring
  have hprod : P (e i) = -(P i).comp (-Polynomial.X) := by
   have hreindex : (∏ j ∈ Finset.univ.erase i, F (x (e j)-x (e i))) = ∏ j ∈ Finset.univ.erase (e i), F (x j-x (e i)) := by
    apply Finset.prod_bij (fun j _ => e j)
    · intro j hj
      simpa using hj
    · intro a ha b hb hab
      exact e.injective hab
    · intro j hj
      refine ⟨e.symm j, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, by simp⟩
      intro h
      apply (Finset.mem_erase.mp hj).1
      exact (e.apply_symm_apply j).symm.trans (congrArg e h)
    · intro j hj
      rfl
   change (∏ j ∈ Finset.univ.erase (e i), F (x j-x (e i))) = _
   rw [← hreindex]
   simp_rw [hdiff, hF]
   rw [Finset.prod_neg]
   have heval : (∏ j ∈ Finset.univ.erase i, (F (x j-x i)).comp (-Polynomial.X)) = (P i).comp (-Polynomial.X) := by
    exact (map_prod (Polynomial.compRingHom (-Polynomial.X : Polynomial ℂ)) (fun j => F (x j-x i)) (Finset.univ.erase i)).symm
   rw [heval]
   norm_num
  rw [hprod, Polynomial.coeff_neg]
  have heven : ((P i).comp (-Polynomial.X)).coeff (2*k) = (P i).coeff (2*k) := by
   have hh := Polynomial.comp_C_mul_X_coeff (p := P i) (r := (-1:ℂ)) (n := 2*k)
   simpa [pow_mul] using hh
  rw [heven]

/-- A common coefficient 0-in-even-column-span relation forces dependence of 46 binary point products -/
theorem even_column_relation_dependent : (
∀ (z w : Fin 46 → Fin 46 → ℂ) (v : Fin 22 → ℂ),
 let P := fun i : Fin 46 => ∏ j ∈ Finset.univ.erase i, (Polynomial.C (z i j)-Polynomial.C (w i j)*Polynomial.X)
 (∀ i, (∑ j : Fin 22, (P i).coeff (2*(j.val+1)) * v j) = (P i).coeff 0) →
 ¬ LinearIndependent ℂ (fun i : Fin 46 => ∏ j ∈ Finset.univ.erase i, (MvPolynomial.C (z i j)*MvPolynomial.X (0 : Fin 2)-MvPolynomial.C (w i j)*MvPolynomial.X 1))
) := by
  classical
  intro z w v P hv hli
  have hd := (independent_iff_univariate_det_ne_zero z w).mp hli
  let A : Matrix (Fin 46) (Fin 46) ℂ := fun i k => (P i).coeff k.val
  change A.transpose.det ≠ 0 at hd
  rw [Matrix.det_transpose] at hd
  have ha : LinearIndependent ℂ A.col := Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hd))
  let ev : Fin 23 → Fin 46 := fun k => ⟨2*k.val, by omega⟩
  have hei : Function.Injective ev := by
   intro a b hab
   apply Fin.ext
   have hh := congrArg Fin.val hab
   dsimp [ev] at hh
   omega
  have hs := ha.comp ev hei
  let c : Fin 23 → Fin 46 → ℂ := fun k i => (P i).coeff (2*k.val)
  change LinearIndependent ℂ c at hs
  have he : c 0 = ∑ j : Fin 22, v j • c j.succ := by
   funext i
   simpa [c, Finset.sum_apply, mul_comm] using (hv i).symm
  apply (linearIndependent_finSucc.mp hs).2
  rw [he]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j,rfl⟩

/-- Signed-height half-turn family with positive-row even relation is an injective counterexample to pinned independence -/
theorem half_turn_counterexample_interface : (
∀ (X : Fin 46 → EuclideanSpace ℝ (Fin 3)) (b : ℝ), 0 < b →
 (∀ i : Fin 23, X ⟨i.val+23,by omega⟩ = WithLp.toLp 2 ![-X ⟨i.val,by omega⟩ 0,-X ⟨i.val,by omega⟩ 1,X ⟨i.val,by omega⟩ 2]) →
 (∀ i : Fin 23, X ⟨i.val,by omega⟩ 1 = (2*(i.val:ℝ)+1)*b) →
 let P : Fin 46 → Polynomial ℂ := fun i => ∏ j ∈ Finset.univ.erase i, (Polynomial.C (((X j-X i) 0:ℂ)+((X j-X i) 1:ℂ)*Complex.I)-Polynomial.C ((‖X j-X i‖-(X j-X i) 2:ℝ):ℂ)*Polynomial.X)
 (∃ v : Fin 22 → ℂ, ∀ i : Fin 23, (∑ j : Fin 22, (P ⟨i.val,by omega⟩).coeff (2*(j.val+1))*v j) = (P ⟨i.val,by omega⟩).coeff 0) →
 Function.Injective X ∧ ¬ LinearIndependent ℂ (fun i : Fin 46 => ∏ j ∈ Finset.univ.erase i,
  let d := X j-X i
  let L : ℂ × ℂ := if ‖d‖-d 2 = 0 then (1,0) else (((d 0:ℂ)+(d 1:ℂ)*Complex.I)/(‖d‖-d 2:ℝ),1)
  MvPolynomial.C L.1*MvPolynomial.X (0 : Fin 2)-MvPolynomial.C L.2*MvPolynomial.X 1)
) := by
  classical
  intro X b hb hmate hheight P hrel
  let xx : Fin 23 × Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i => X ⟨i.1.val+23*i.2.val, by omega⟩
  have hxx : ∀ i, xx i 1 = (if i.2 = 0 then (1:ℝ) else -1)*(2*(i.1.val:ℝ)+1)*b := by
   rintro ⟨a,c⟩
   fin_cases c
   · simpa [xx] using hheight a
   · have hh := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) (hmate a)
     change X ⟨a.val+23,by omega⟩ 1 = -X ⟨a.val,by omega⟩ 1 at hh
     rw [hheight] at hh
     change X ⟨a.val+23,by omega⟩ 1 = (-1:ℝ)*(2*(a.val:ℝ)+1)*b
     rw [hh]
     ring
  obtain ⟨hxxi,hxxp⟩ := odd_height_family_injective_pole_free xx b hb hxx
  let r : Fin 46 → Fin 23 × Fin 2 := fun i => (⟨i.val%23,by omega⟩,⟨i.val/23,by omega⟩)
  have hri : Function.Injective r := by
   intro i j h
   apply Fin.ext
   have hh := congrArg (fun a : Fin 23 × Fin 2 => a.1.val+23*a.2.val) h
   dsimp [r] at hh
   omega
  have hr (i : Fin 46) : xx (r i) = X i := by
   apply congrArg X
   apply Fin.ext
   dsimp [xx,r]
   omega
  have hXi : Function.Injective X := by
   intro i j hij
   apply hri
   apply hxxi
   simpa only [hr] using hij
  have hXp : ∀ i j, i ≠ j → ‖X j-X i‖-(X j-X i) 2 ≠ 0 := by
   intro i j hij
   simpa only [hr] using hxxp (r i) (r j) (fun h => hij (hri h))
  let τ : Fin 46 → Fin 46 := fun i => if h : i.val < 23 then ⟨i.val+23,by omega⟩ else ⟨i.val-23,by omega⟩
  have ht : Function.Involutive τ := by
   intro i
   apply Fin.ext
   by_cases hi : i.val < 23
   · have hhi : ¬i.val+23 < 23 := by omega
     simp [τ,hi,hhi]
   · have hhi : i.val-23 < 23 := by omega
     simp [τ,hi,hhi]
     omega
  let e : Equiv.Perm (Fin 46) := ⟨τ,τ,ht,ht⟩
  have hepos (i : Fin 23) : e ⟨i.val,by omega⟩ = ⟨i.val+23,by omega⟩ := by
   change τ ⟨i.val,by omega⟩ = _
   simp [τ,i.isLt]
  have hegeom : ∀ i, X (e i) = WithLp.toLp 2 ![-X i 0,-X i 1,X i 2] := by
   intro i
   by_cases hi : i.val < 23
   · change X (τ i) = _
     simpa [τ,hi] using hmate ⟨i.val,hi⟩
   · let j : Fin 23 := ⟨i.val-23,by omega⟩
     have h1 : i = ⟨j.val+23,by omega⟩ := by apply Fin.ext; dsimp [j]; omega
     have h2 : e i = ⟨j.val,by omega⟩ := by change τ i = _; simp [τ,hi,j]
     have hg : X i = WithLp.toLp 2 ![-X ⟨j.val,by omega⟩ 0,-X ⟨j.val,by omega⟩ 1,X ⟨j.val,by omega⟩ 2] := (congrArg X h1).trans (hmate j)
     rw [h2,hg]
     ext t
     fin_cases t <;> simp
  have hp := half_turn_even_coeff_parity X e hegeom
  change ∀ i k, (P (e i)).coeff (2*k) = -(P i).coeff (2*k) at hp
  obtain ⟨v,hv⟩ := hrel
  have hall : ∀ i : Fin 46, (∑ j : Fin 22, (P i).coeff (2*(j.val+1))*v j) = (P i).coeff 0 := by
   intro i
   by_cases hi : i.val < 23
   · exact hv ⟨i.val,hi⟩
   · let a : Fin 23 := ⟨i.val-23,by omega⟩
     have hie : i = e ⟨a.val,by omega⟩ := by rw [hepos]; apply Fin.ext; dsimp [a]; omega
     rw [hie,hp _ 0]
     simp_rw [hp,neg_mul]
     rw [Finset.sum_neg_distrib,hv]
  have hraw := even_column_relation_dependent (fun i j => ((X j-X i) 0:ℂ)+((X j-X i) 1:ℂ)*Complex.I) (fun i j => ((‖X j-X i‖-(X j-X i) 2:ℝ):ℂ)) v hall
  refine ⟨hXi,fun h => hraw ?_⟩
  exact (raw_lift_chart_equivalence X hXp).mpr h

end Atiyah.Facts

/-! ### `Atiyah.Facts`: Coefficients -/

/-!
# Meaning of the numerical coefficient program

The coefficient-list recurrence is exact polynomial multiplication; the geometric factor is the raw lift;
the whole coefficient program encloses the geometric coefficient block on every input ball.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- The numerical coefficient-list recurrence exactly multiplies the polynomial by z-wX -/
theorem coeff_step_mul_linear : (
∀ {R : Type} [CommRing R],
let decode : List R → Polynomial R := fun p => p.foldr (fun c q => Polynomial.C c + Polynomial.X * q) 0
let times : List R → R × R → List R := fun p f => List.zipWith (· - ·) ((p.map (f.1 * ·)) ++ [0]) (0 :: p.map (· * f.2))
∀ p z w, decode (times p (z,w)) = (Polynomial.C z - Polynomial.C w * Polynomial.X) * decode p
) := by
  intro R _ decode times
  have hsub : ∀ (p q : List R), p.length = q.length → decode (List.zipWith (· - ·) p q) = decode p - decode q := by
    intro p
    induction p with
    | nil =>
      intro q h
      have hq : q = [] := List.length_eq_zero_iff.mp h.symm
      subst q
      simp [decode]
    | cons a p ih =>
      intro q h
      cases q with
      | nil => simp at h
      | cons b q =>
        change Polynomial.C (a-b) + Polynomial.X * decode (List.zipWith (· - ·) p q) = (Polynomial.C a + Polynomial.X * decode p) - (Polynomial.C b + Polynomial.X * decode q)
        rw [ih q (by simpa using h), map_sub]
        ring
  have hmap (z : R) : ∀ p : List R, decode (p.map (z * ·)) = Polynomial.C z * decode p := by
    intro p
    induction p with
    | nil => simp [decode]
    | cons a p ih =>
      change Polynomial.C (z*a) + Polynomial.X * decode (p.map (z * ·)) = Polynomial.C z * (Polynomial.C a + Polynomial.X * decode p)
      rw [ih,map_mul]
      ring
  have happend (p : List R) : decode (p ++ [0]) = decode p := by simp [decode,List.foldr_append]
  intro p z w
  dsimp only [times]
  rw [hsub _ _ (by simp),happend]
  change decode (p.map (z * ·)) - (Polynomial.C 0 + Polynomial.X * decode (p.map (· * w))) = _
  rw [hmap z]
  have hright : p.map (· * w) = p.map (w * ·) := by simp only [mul_comm]
  rw [hright,hmap w]
  simp only [map_zero,zero_add]
  ring

/-- Horner-decoded coefficient lists have exactly their getD entries as polynomial coefficients -/
theorem horner_coeff_getD : (
∀ {R : Type} [CommRing R] (p : List R) (k : ℕ), (p.foldr (fun c q => Polynomial.C c + Polynomial.X * q) (0 : Polynomial R)).coeff k = p.getD k 0
) := by
  intro R _ p
  induction p with
  | nil => intro k; simp
  | cons a p ih =>
    intro k
    cases k with
    | zero => simp
    | succ k => simpa using ih k

/-- Iterated coefficient-list updates yield the exact coefficients of every finite raw linear-factor product -/
theorem coeff_fold_product : (
∀ {R : Type} [CommRing R],
let decode : List R → Polynomial R := fun p => p.foldr (fun c q => Polynomial.C c + Polynomial.X * q) 0
let times : List R → R × R → List R := fun p f => List.zipWith (· - ·) ((p.map (f.1 * ·)) ++ [0]) (0 :: p.map (· * f.2))
∀ (fs : List (R × R)) (p : List R), decode (fs.foldl times p) = (fs.map (fun f => Polynomial.C f.1 - Polynomial.C f.2 * Polynomial.X)).prod * decode p ∧ ∀ k, (fs.foldl times p).getD k 0 = ((fs.map (fun f => Polynomial.C f.1 - Polynomial.C f.2 * Polynomial.X)).prod * decode p).coeff k
) := by
  intro R _ decode times
  have H : ∀ (fs : List (R × R)) (p : List R), decode (fs.foldl times p) = (fs.map (fun f => Polynomial.C f.1 - Polynomial.C f.2 * Polynomial.X)).prod * decode p := by
    intro fs
    induction fs with
    | nil => intro p; simp
    | cons f fs ih =>
      intro p
      simp only [List.foldl_cons,List.map_cons,List.prod_cons]
      rw [ih]
      have ht := coeff_step_mul_linear p f.1 f.2
      change decode (times p (f.1,f.2)) = _ at ht
      rw [ht]
      ring
  intro fs p
  refine ⟨H fs p,?_⟩
  intro k
  rw [← horner_coeff_getD (fs.foldl times p) k]
  change (decode (fs.foldl times p)).coeff k = _
  rw [H fs p]

/-- Indexed function-list raw factor recurrence gives exact evaluated polynomial product coefficients -/
theorem coeff_fold_product_fun : (
∀ (E A : Type) (fs : List A) (f : A → (E → ℂ) × (E → ℝ)) (p : List (E → ℂ)) (y : E) (k : ℕ),
 let tb : List (E → ℂ) → ((E → ℂ) × (E → ℝ)) → List (E → ℂ) := fun p f => List.zipWith (fun (a b : E → ℂ) y => a y-b y) ((p.map (fun a y => f.1 y*a y)) ++ [fun _ => 0]) ((fun _ => 0) :: p.map (fun a y => a y*(f.2 y:ℂ)))
 ((fs.foldl (fun p j => tb p (f j)) p).getD k (fun _ => 0)) y =
 (((fs.map (fun j => Polynomial.C ((f j).1 y) - Polynomial.C (((f j).2 y : ℝ):ℂ) * Polynomial.X)).prod) * ((p.map (fun (a : E → ℂ) => a y)).foldr (fun c q => Polynomial.C c + Polynomial.X*q) (0 : Polynomial ℂ))).coeff k
) := by
  intro E A fs f p y k tb
  let ff : A → (E → ℂ) × (E → ℂ) := fun j => ((f j).1, fun y => ((f j).2 y : ℂ))
  have h := coeff_fold_product (fs.map ff) p
  dsimp only at h
  rw [List.foldl_map] at h
  have hh := congrArg (fun a : E → ℂ => a y) (h.2 k)
  let ev := Pi.evalRingHom (fun _ : E => ℂ) y
  have hd : ∀ p : List (E → ℂ), Polynomial.map ev (p.foldr (fun c q => Polynomial.C c + Polynomial.X*q) 0) = (p.map (fun a => a y)).foldr (fun c q => Polynomial.C c + Polynomial.X*q) 0 := by
   intro p
   induction p with
   | nil => simp
   | cons a p ih => simp [ih, ev]
  have hp : Polynomial.map ev ((fs.map ff |>.map (fun f => Polynomial.C f.1 - Polynomial.C f.2 * Polynomial.X)).prod) = (fs.map (fun j => Polynomial.C ((f j).1 y) - Polynomial.C (((f j).2 y : ℝ):ℂ)*Polynomial.X)).prod := by
   simp [Polynomial.map_list_prod, List.map_map, Function.comp_def, ff, ev]
  change ((fs.foldl (fun p j => tb p (f j)) p).getD k 0) y = ev (((fs.map ff).map (fun f : (E → ℂ) × (E → ℂ) => Polynomial.C f.1 - Polynomial.C f.2 * Polynomial.X)).prod * (p.foldr (fun c q => Polynomial.C c + Polynomial.X*q) 0) |>.coeff k) at hh
  rw [← Polynomial.coeff_map, Polynomial.map_mul, hp, hd] at hh
  exact hh

/-- The numerical coordinate-difference factor exactly represents the Euclidean raw direction lift -/
theorem raw_factor_is_lift : (
∀ {E D : Type} (J : D → (E → ℝ) → Prop) (da dm : D → D → D) (dn dq : D → D)
(ha : ∀ a b f g, J a f → J b g → J (da a b) (fun y => f y + g y))
(hm : ∀ a b f g, J a f → J b g → J (dm a b) (fun y => f y * g y))
(hn : ∀ a f, J a f → J (dn a) (fun y => -f y))
(hq : ∀ a f, J a f → J (dq a) (fun y => Real.sqrt (f y))),
let K : (D × D) → (E → ℂ) → Prop := fun a f => J a.1 (fun x => (f x).re) ∧ J a.2 (fun x => (f x).im)
let T : (D × D × D) → (E → EuclideanSpace ℝ (Fin 3)) → Prop := fun a p => J a.1 (fun x => p x 0) ∧ J a.2.1 (fun x => p x 1) ∧ J a.2.2 (fun x => p x 2)
let ds : D → D → D := fun a b => da a (dn b)
let factor : (D × D × D) → (D × D × D) → (D × D) × D := fun p q =>
 let d0 := ds q.1 p.1
 let d1 := ds q.2.1 p.2.1
 let d2 := ds q.2.2 p.2.2
 ((d0,d1),ds (dq (da (da (dm d0 d0) (dm d1 d1)) (dm d2 d2))) d2)
∀ a b p q, T a p → T b q →
K (factor a b).1 (fun x => (((q x-p x) 0:ℝ):ℂ) + (((q x-p x) 1:ℝ):ℂ)*Complex.I) ∧
J (factor a b).2 (fun x => ‖q x-p x‖ - (q x-p x) 2)
) := by
  intro E D J da dm dn dq ha hm hn hq K T ds factor a b p q hp hq'
  have hnorm (v : EuclideanSpace ℝ (Fin 3)) : ‖v‖ = Real.sqrt (v 0*v 0 + v 1*v 1 + v 2*v 2) := by
    simpa [Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs,pow_two,add_assoc] using EuclideanSpace.norm_eq v
  have hsub (a b : D) (f g : E → ℝ) (hf : J a f) (hg : J b g) : J (ds a b) (fun x => f x - g x) := by
    simpa only [ds,sub_eq_add_neg] using ha _ _ _ _ hf (hn _ _ hg)
  have h0 : J (ds b.1 a.1) (fun x => (q x-p x) 0) := hsub _ _ _ _ hq'.1 hp.1
  have h1 : J (ds b.2.1 a.2.1) (fun x => (q x-p x) 1) := hsub _ _ _ _ hq'.2.1 hp.2.1
  have h2 : J (ds b.2.2 a.2.2) (fun x => (q x-p x) 2) := hsub _ _ _ _ hq'.2.2 hp.2.2
  constructor
  · dsimp only [K,factor]
    simpa only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add] using And.intro h0 h1
  · have hw := hsub _ _ _ _ (hq _ _ (ha _ _ _ _ (ha _ _ _ _ (hm _ _ _ _ h0 h0) (hm _ _ _ _ h1 h1)) (hm _ _ _ _ h2 h2))) h2
    simpa only [factor,hnorm] using hw

/-- Constant rows, moving-pair rows and scaled even coefficients preserve all compatible input relations -/
theorem coeff_rows_sound : (
∀ {A B U V PA PB : Type} (R : A → B → Prop) (S : U → V → Prop) (T : PA → PB → Prop)
(za oa : A) (zb ob : B) (pa : PA) (pb : PB)
(sa ma : A → A → A) (sb mb : B → B → B) (ca : A → U → A) (cb : B → V → B)
(fa : PA → PA → A × U) (fb : PB → PB → B × V)
(ra ea : ℕ → U) (rb eb : ℕ → V)
(hz : R za zb) (ho : R oa ob) (hp : T pa pb)
(hs : ∀ a b c d, R a b → R c d → R (sa a c) (sb b d))
(hm : ∀ a b c d, R a b → R c d → R (ma a c) (mb b d))
(hc : ∀ a b u v, R a b → S u v → R (ca a u) (cb b v))
(hf : ∀ p q p' q', T p q → T p' q' → R (fa p p').1 (fb q q').1 ∧ S (fa p p').2 (fb q q').2)
(hr : ∀ i, S (ra i) (rb i)) (he : ∀ i, S (ea i) (eb i)) (m mov : ℕ),
let L := List.Forall₂ R
let M := List.Forall₂ L
let timesA : List A → (A × U) → List A := fun p f => List.zipWith sa ((p.map (ma f.1)) ++ [za]) (za :: p.map (fun t => ca t f.2))
let timesB : List B → (B × V) → List B := fun p f => List.zipWith sb ((p.map (mb f.1)) ++ [zb]) (zb :: p.map (fun t => cb t f.2))
let prodA : List PA → ℕ → List ℕ → List A → List A := fun pts i js p => js.foldl (fun p j => timesA p (fa (pts.getD i pa) (pts.getD j pa))) p
let prodB : List PB → ℕ → List ℕ → List B → List B := fun pts i js p => js.foldl (fun p j => timesB p (fb (pts.getD i pb) (pts.getD j pb))) p
let constA : List PA → List (List A) := fun pts => (List.range m).map (fun i => if i = mov then [oa] else prodA pts i ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)) [oa])
let constB : List PB → List (List B) := fun pts => (List.range m).map (fun i => if i = mov then [ob] else prodB pts i ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)) [ob])
let blockA : List PA → List (List A) → List (List A) := fun pts C => (List.range m).map (fun i =>
 let js := if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov,mov+m]
 let p := prodA pts i js (C.getD i [oa])
 (List.range m).map (fun k => ca (ca (p.getD (2*k) za) (ea k)) (ra i)))
let blockB : List PB → List (List B) → List (List B) := fun pts C => (List.range m).map (fun i =>
 let js := if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov,mov+m]
 let p := prodB pts i js (C.getD i [ob])
 (List.range m).map (fun k => cb (cb (p.getD (2*k) zb) (eb k)) (rb i)))
(∀ p q a b, L p q → R a.1 b.1 → S a.2 b.2 → L (timesA p a) (timesB q b)) ∧
(∀ pts qts, List.Forall₂ T pts qts → ∀ i js p q, L p q → L (prodA pts i js p) (prodB qts i js q)) ∧
(∀ pts qts, List.Forall₂ T pts qts → M (constA pts) (constB qts)) ∧
(∀ pts qts C D, List.Forall₂ T pts qts → M C D → M (blockA pts C) (blockB qts D))
) := by
  intro A B U V PA PB R S T za oa zb ob pa pb sa ma sb mb ca cb fa fb ra ea rb eb hz ho hp hs hm hc hf hr he m mov L M timesA timesB prodA prodB constA constB blockA blockB
  have hone : L [oa] [ob] := List.Forall₂.cons ho List.Forall₂.nil
  have htimes : ∀ p q a b, L p q → R a.1 b.1 → S a.2 b.2 → L (timesA p a) (timesB q b) := by
    intro p q a b hpq hab huv
    dsimp only [timesA,timesB]
    apply forall₂_zipWith R R R sa sb (fun _ _ _ _ => hs _ _ _ _)
    · exact List.rel_append (List.rel_map (fun {_ _} h => hm _ _ _ _ hab h) hpq) (List.Forall₂.cons hz List.Forall₂.nil)
    · exact List.Forall₂.cons hz (List.rel_map (fun {_ _} h => hc _ _ _ _ h huv) hpq)
  have hprod : ∀ pts qts, List.Forall₂ T pts qts → ∀ i js p q, L p q → L (prodA pts i js p) (prodB qts i js q) := by
    intro pts qts hpts i js p q hpq
    have hget (j : ℕ) := (forall₂_getD_set T pts qts hpts pa pb hp j).1
    dsimp only [prodA,prodB]
    refine List.rel_foldl (R := (Eq : ℕ → ℕ → Prop)) ?_ hpq (List.forall₂_same.mpr (fun _ _ => rfl))
    intro p q hpq j k hjk
    subst k
    have hf' := hf _ _ _ _ (hget i) (hget j)
    exact htimes p q _ _ hpq hf'.1 hf'.2
  refine ⟨htimes,hprod,?_,?_⟩
  · intro pts qts hpts
    dsimp only [constA,constB]
    refine List.rel_map (R := (Eq : ℕ → ℕ → Prop)) ?_ (List.forall₂_same.mpr (fun _ _ => rfl))
    intro i j hij
    subst j
    dsimp only
    split_ifs with hi
    · exact hone
    · exact hprod pts qts hpts i _ _ _ hone
  · intro pts qts C D hpts hCD
    dsimp only [blockA,blockB]
    refine List.rel_map (R := (Eq : ℕ → ℕ → Prop)) ?_ (List.forall₂_same.mpr (fun _ _ => rfl))
    intro i j hij
    subst j
    have hinit := (forall₂_getD_set L C D hCD [oa] [ob] hone i).1
    have hrow := hprod pts qts hpts i (if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov,mov+m]) _ _ hinit
    refine List.rel_map (R := (Eq : ℕ → ℕ → Prop)) ?_ (List.forall₂_same.mpr (fun _ _ => rfl))
    intro k l hkl
    subst l
    have hval := (forall₂_getD_set R _ _ hrow za zb hz (2*k)).1
    exact hc _ _ _ _ (hc _ _ _ _ hval (he k)) (hr i)

/-- Value-only constant coefficient rows already satisfy the optional-AD geometric relation after none embedding -/
theorem constant_rows_ad_sound : (
∀ (s : ℤ), 0 < s → ∀ (x : Fin 2 → ℝ) (m mov : ℕ),
let I := ℤ × ℤ × Bool
let D := I × Option (I × I)
let E := Fin 2 → ℝ
let R : I → ℝ → Prop := fun a v => a.2.2 = true → (a.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (a.2.1:ℝ)/(s:ℝ)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun a d => match a with
 | none => d = 0 | some p => R p.1 (d (Pi.single 0 1)) ∧ R p.2 (d (Pi.single 1 1))
let J : D → (E → ℝ) → Prop := fun a f => a.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R a.1 (f x) ∧ O a.2 d
let J₀ : I → (E → ℝ) → Prop := fun a f => J (a,none) f
let K : (I × I) → (E → ℂ) → Prop := fun a f => J₀ a.1 (fun y => (f y).re) ∧ J₀ a.2 (fun y => (f y).im)
let T : (I × I × I) → (E → EuclideanSpace ℝ (Fin 3)) → Prop := fun a p => J₀ a.1 (fun y => p y 0) ∧ J₀ a.2.1 (fun y => p y 1) ∧ J₀ a.2.2 (fun y => p y 2)
let q : ℤ → ℤ → I := fun a b => (a*s/b,-((-a*s)/b),decide (0<b))
let add : I → I → I := fun a b => (a.1+b.1,a.2.1+b.2.1,a.2.2 && b.2.2)
let neg : I → I := fun a => (-a.2.1,-a.1,a.2.2)
let sub : I → I → I := fun a b => add a (neg b)
let mul : I → I → I := fun a b => (min (min (a.1*b.1) (a.1*b.2.1)) (min (a.2.1*b.1) (a.2.1*b.2.1))/s,-((-max (max (a.1*b.1) (a.1*b.2.1)) (max (a.2.1*b.1) (a.2.1*b.2.1)))/s),a.2.2 && b.2.2)
let inv : I → I := fun a => (s*s/a.2.1,-((-(s*s))/a.1),a.2.2 && decide (0<a.1 ∧ a.1≤a.2.1))
let sq : I → I := fun a =>
 let l : ℤ := Nat.sqrt (a.1*s).toNat
 let u : ℤ := (Nat.sqrt (a.2.1*s).toNat : ℤ)+1
 (l,u,a.2.2 && decide (0<a.1 ∧ 0≤l ∧ 0≤u ∧ l*l≤a.1*s ∧ a.2.1*s≤u*u))
let zm : (I × I) → (I × I) → (I × I) := fun a b => (sub (mul a.1 b.1) (mul a.2 b.2),add (mul a.1 b.2) (mul a.2 b.1))
let zs : (I × I) → (I × I) → (I × I) := fun a b => (sub a.1 b.1,sub a.2 b.2)
let scale : (I × I) → I → (I × I) := fun a b => (mul a.1 b,mul a.2 b)
let za : I × I := (q 0 1,q 0 1)
let oa : I × I := (q 1 1,q 0 1)
let pa : I × I × I := (q 0 1,q 0 1,q 0 1)
let fa : (I × I × I) → (I × I × I) → (I × I) × I := fun p q =>
 let d0 := sub q.1 p.1
 let d1 := sub q.2.1 p.2.1
 let d2 := sub q.2.2 p.2.2
 ((d0,d1),sub (sq (add (add (mul d0 d0) (mul d1 d1)) (mul d2 d2))) d2)
let fb : (E → EuclideanSpace ℝ (Fin 3)) → (E → EuclideanSpace ℝ (Fin 3)) → (E → ℂ) × (E → ℝ) := fun p q =>
 ((fun y => (((q y-p y) 0:ℝ):ℂ)+(((q y-p y) 1:ℝ):ℂ)*Complex.I),(fun y => ‖q y-p y‖-(q y-p y) 2))
let ta : List (I × I) → ((I × I) × I) → List (I × I) := fun p f => List.zipWith zs ((p.map (zm f.1)) ++ [za]) (za :: p.map (fun t => scale t f.2))
let tb : List (E → ℂ) → ((E → ℂ) × (E → ℝ)) → List (E → ℂ) := fun p f => List.zipWith (fun a b y => a y-b y) ((p.map (fun a y => f.1 y*a y)) ++ [fun _ => 0]) ((fun _ => 0) :: p.map (fun a y => a y*(f.2 y:ℂ)))
let ca : List (I × I × I) → List (List (I × I)) := fun pts => (List.range m).map (fun i => if i = mov then [oa] else ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)).foldl (fun p j => ta p (fa (pts.getD i pa) (pts.getD j pa))) [oa])
let cb : List (E → EuclideanSpace ℝ (Fin 3)) → List (List (E → ℂ)) := fun pts => (List.range m).map (fun i => if i = mov then [fun _ => 1] else ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)).foldl (fun p j => tb p (fb (pts.getD i (fun _ => 0)) (pts.getD j (fun _ => 0)))) [fun _ => 1])
∀ ps qs, List.Forall₂ T ps qs → List.Forall₂ (List.Forall₂ K) (ca ps) (cb qs)
) := by
  intro s hs x m mov I D E R O J J₀ K T q add neg sub mul inv sq zm zs scale za oa pa fa fb ta tb ca cb ps qs hps
  have hj := fixed_ad_ops_sound s hs x (Pi.single 0 1) (Pi.single 1 1)
  extract_lets at hj
  have hc : ∀ a c, R a c → J₀ a (fun _ => c) := hj.1
  have ha : ∀ a b f g, J₀ a f → J₀ b g → J₀ (add a b) (fun y => f y+g y) := by
    intro a b f g hf hg
    exact hj.2.1 (a,none) (b,none) f g hf hg
  have hn : ∀ a f, J₀ a f → J₀ (neg a) (fun y => -f y) := by
    intro a f hf
    exact hj.2.2.1 (a,none) f hf
  have hm : ∀ a b f g, J₀ a f → J₀ b g → J₀ (mul a b) (fun y => f y*g y) := by
    intro a b f g hf hg
    exact hj.2.2.2.1 (a,none) (b,none) f g hf hg
  have hi : ∀ a f, J₀ a f → J₀ (inv a) (fun y => (f y)⁻¹) := by
    intro a f hf
    exact hj.2.2.2.2.1 (a,none) f hf
  have hsq : ∀ a f, J₀ a f → J₀ (sq a) (fun y => Real.sqrt (f y)) := by
    intro a f hf
    exact hj.2.2.2.2.2 (a,none) f hf
  have hq : ∀ a b, R (q a b) ((a:ℝ)/(b:ℝ)) := (fixed_primitives_sound s hs).1
  have h0 : J₀ (q 0 1) (fun _ => 0) := hc _ 0 (by simpa using hq 0 1)
  have h1 : J₀ (q 1 1) (fun _ => 1) := hc _ 1 (by simpa using hq 1 1)
  have hz : K za (fun _ => 0) := by simpa only [K, za, Complex.zero_re, Complex.zero_im] using And.intro h0 h0
  have ho : K oa (fun _ => 1) := by simpa only [K, oa, Complex.one_re, Complex.one_im] using And.intro h1 h0
  have hp : T pa (fun _ => 0) := ⟨h0,h0,h0⟩
  have hzops := complex_pair_ops_sound J₀ add mul neg inv ha hm hn hi
  extract_lets at hzops
  have hs' : ∀ a f b g, K a f → K b g → K (zs a b) (fun y => f y-g y) := by
    intro a f b g hf hg
    exact hzops.2.2.1 a b f g hf hg
  have hm' : ∀ a f b g, K a f → K b g → K (zm a b) (fun y => f y*g y) := by
    intro a f b g hf hg
    exact hzops.2.2.2.1 a b f g hf hg
  have hc' : ∀ a f b g, K a f → J₀ b g → K (scale a b) (fun y => f y*(g y:ℂ)) := by
    intro a f b g hf hg
    exact hzops.2.2.2.2.2.1 a b f g hf hg
  have hf := raw_factor_is_lift J₀ add mul neg sq ha hm hn hsq
  extract_lets at hf
  have hfac : ∀ p q p' q', T p q → T p' q' → K (fa p p').1 (fb q q').1 ∧ J₀ (fa p p').2 (fb q q').2 := by
    intro p q p' q' hp hq
    exact hf p p' q q' hp hq
  have hall := coeff_rows_sound K J₀ T za oa (fun _ => 0) (fun _ => 1) pa (fun _ => 0) zs zm (fun f g y => f y-g y) (fun f g y => f y*g y) scale (fun f g y => f y*(g y:ℂ)) fa fb (fun _ => q 1 1) (fun _ => q 1 1) (fun _ _ => 1) (fun _ _ => 1) hz ho hp hs' hm' hc' hfac (fun _ => h1) (fun _ => h1) m mov
  extract_lets at hall
  exact hall.2.2.1 ps qs hps

/-- Symmetric rational optional-AD inputs enclose both exact coordinate projections on every Fin 2 sup ball -/
theorem coordinate_inputs_ad_sound : (
∀ (s a b : ℤ), 0 < s → 0 < b →
let I := ℤ × ℤ × Bool
let D := I × Option (I × I)
let E := Fin 2 → ℝ
let R : I → ℝ → Prop := fun c v => c.2.2 = true → (c.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (c.2.1:ℝ)/(s:ℝ)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun c d => match c with
 | none => d = 0 | some p => R p.1 (d (Pi.single 0 1)) ∧ R p.2 (d (Pi.single 1 1))
let J : E → D → (E → ℝ) → Prop := fun x c f => c.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R c.1 (f x) ∧ O c.2 d
let q : ℤ → ℤ → I := fun u v => (u*s/v,-((-u*s)/v),decide (0<v))
let v : I := ((q (-a) b).1,(q a b).2.1,true)
∀ x ∈ Metric.closedBall (0 : E) ((a:ℝ)/(b:ℝ)),
J x (v,some (q 1 1,q 0 1)) (fun y => y 0) ∧
J x (v,some (q 0 1,q 1 1)) (fun y => y 1)
) := by
  intro s a b hs hb I D E R O J q v x hx
  have hq : ∀ u w, R (q u w) ((u:ℝ)/(w:ℝ)) :=
    (fixed_primitives_sound s hs).1
  have hneg := hq (-a) b (by simpa [q] using hb)
  have hpos := hq a b (by simpa [q] using hb)
  have hzero : R (q 0 1) 0 := by simpa using hq 0 1
  have hone : R (q 1 1) 1 := by simpa using hq 1 1
  have hv (i : Fin 2) : R v (x i) := by
    intro _
    have hn : ‖x‖ ≤ (a:ℝ)/(b:ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    have hi0 : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hi : |x i| ≤ (a:ℝ)/(b:ℝ) := hi0.trans hn
    have hi' := abs_le.mp hi
    change (((q (-a) b).1:ℝ)/(s:ℝ) ≤ x i) ∧ (x i ≤ ((q a b).2.1:ℝ)/(s:ℝ))
    constructor
    · exact hneg.1.trans (by simpa only [Int.cast_neg, neg_div] using hi'.1)
    · exact hi'.2.trans hpos.2
  constructor
  · intro _
    refine ⟨ContinuousLinearMap.proj 0, (ContinuousLinearMap.proj (0 : Fin 2) : E →L[ℝ] ℝ).hasFDerivAt, hv 0, ?_⟩
    change R (q 1 1) ((Pi.single 0 1 : E) 0) ∧ R (q 0 1) ((Pi.single 1 1 : E) 0)
    simpa using And.intro hone hzero
  · intro _
    refine ⟨ContinuousLinearMap.proj 1, (ContinuousLinearMap.proj (1 : Fin 2) : E →L[ℝ] ℝ).hasFDerivAt, hv 1, ?_⟩
    change R (q 0 1) ((Pi.single 0 1 : E) 1) ∧ R (q 1 1) ((Pi.single 1 1 : E) 1)
    simpa using And.intro hzero hone

/-- Optional-AD embedding and both moving-pair set updates enclose the true coordinate-deformation point functions -/
theorem moving_pair_inputs_ad_sound : (
∀ (s a b : ℤ), 0 < s → 0 < b → ∀ (mov mate : ℕ),
let I := ℤ × ℤ × Bool
let D := I × Option (I × I)
let E := Fin 2 → ℝ
let R : I → ℝ → Prop := fun c v => c.2.2 = true → (c.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (c.2.1:ℝ)/(s:ℝ)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun c d => match c with
 | none => d = 0 | some p => R p.1 (d (Pi.single 0 1)) ∧ R p.2 (d (Pi.single 1 1))
let J : E → D → (E → ℝ) → Prop := fun x c f => c.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R c.1 (f x) ∧ O c.2 d
let q : ℤ → ℤ → I := fun u v => (u*s/v,-((-u*s)/v),decide (0<v))
let ia : I → I → I := fun c d => (c.1+d.1,c.2.1+d.2.1,c.2.2 && d.2.2)
let ine : I → I := fun c => (-c.2.1,-c.1,c.2.2)
let da : D → D → D := fun c d => (ia c.1 d.1, match c.2,d.2 with
 | none,v => v | v,none => v | some u,some v => some (ia u.1 v.1,ia u.2 v.2))
let dn : D → D := fun c => (ine c.1,c.2.map (fun d => (ine d.1,ine d.2)))
let v : I := ((q (-a) b).1,(q a b).2.1,true)
let h : D := (v,some (q 1 1,q 0 1))
let k : D := (v,some (q 0 1,q 1 1))
let V : (I × I × I) → EuclideanSpace ℝ (Fin 3) → Prop := fun p y => R p.1 (y 0) ∧ R p.2.1 (y 1) ∧ R p.2.2 (y 2)
∀ (ps : List (I × I × I)) (qs : List (EuclideanSpace ℝ (Fin 3))), List.Forall₂ V ps qs →
let pts := ps.map (fun p => ((p.1,none),(p.2.1,none),(p.2.2,none)))
let qts : List (E → EuclideanSpace ℝ (Fin 3)) := qs.map (fun p => fun _ => p)
let pz : D × D × D := ((q 0 1,none),(q 0 1,none),(q 0 1,none))
let old := pts.getD mov pz
let p := (da old.1 h,old.2.1,da old.2.2 k)
let oldq := qts.getD mov (fun _ => 0)
let newq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![oldq y 0+y 0,oldq y 1,oldq y 2+y 1]
let mateq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![-newq y 0,-newq y 1,newq y 2]
∀ x ∈ Metric.closedBall (0 : E) ((a:ℝ)/(b:ℝ)),
let T : (D × D × D) → (E → EuclideanSpace ℝ (Fin 3)) → Prop := fun p f => J x p.1 (fun y => f y 0) ∧ J x p.2.1 (fun y => f y 1) ∧ J x p.2.2 (fun y => f y 2)
List.Forall₂ T pts qts ∧
List.Forall₂ T ((pts.set mov p).set mate (dn p.1,dn p.2.1,p.2.2)) ((qts.set mov newq).set mate mateq)
) := by
  intro s a b hs hb mov mate I D E R O J q ia ine da dn v h k V ps qs hps pts qts pz old p oldq newq mateq x hx T
  have hj := fixed_ad_ops_sound s hs x (Pi.single 0 1) (Pi.single 1 1)
  extract_lets at hj
  have hc : ∀ c u, R c u → J x (c,none) (fun _ => u) := hj.1
  have ha : ∀ c d f g, J x c f → J x d g → J x (da c d) (fun y => f y+g y) := hj.2.1
  have hn : ∀ c f, J x c f → J x (dn c) (fun y => -f y) := hj.2.2.1
  have hoff := coordinate_inputs_ad_sound s a b hs hb x hx
  change J x h (fun y => y 0) ∧ J x k (fun y => y 1) at hoff
  have hpts : List.Forall₂ T pts qts := by
    exact List.rel_map (fun {_ _} hp => ⟨hc _ _ hp.1,hc _ _ hp.2.1,hc _ _ hp.2.2⟩) hps
  have hz0 : R (q 0 1) 0 := by simp [R, q]
  have hz : T pz (fun _ => 0) := ⟨hc _ _ hz0,hc _ _ hz0,hc _ _ hz0⟩
  have hold : T old oldq := (forall₂_getD_set T pts qts hpts pz (fun _ => 0) hz mov).1
  have hp : T p newq :=
    ⟨ha old.1 h (fun y => oldq y 0) (fun y => y 0) hold.1 hoff.1,
     hold.2.1,
     ha old.2.2 k (fun y => oldq y 2) (fun y => y 1) hold.2.2 hoff.2⟩
  have hmate : T (dn p.1,dn p.2.1,p.2.2) mateq :=
    ⟨hn p.1 (fun y => newq y 0) hp.1,hn p.2.1 (fun y => newq y 1) hp.2.1,hp.2.2⟩
  refine ⟨hpts,?_⟩
  have hset := (forall₂_getD_set T pts qts hpts p newq hp mov).2
  exact (forall₂_getD_set T _ _ hset _ _ hmate mate).2

/-- The complete constant/moving/scaled coefficient program encloses the exact deformed geometric block on every input ball -/
theorem coefficient_program_encloses_block : (
∀ (s a b : ℤ), 0 < s → 0 < b → ∀ (m mov : ℕ) (re ce : List ℕ),
let I := ℤ × ℤ × Bool
let D := I × Option (I × I)
let Z := D × D
let E := Fin 2 → ℝ
let R : I → ℝ → Prop := fun c v => c.2.2 = true → (c.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (c.2.1:ℝ)/(s:ℝ)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun c d => match c with | none => d = 0 | some p => R p.1 (d (Pi.single 0 1)) ∧ R p.2 (d (Pi.single 1 1))
let J : E → D → (E → ℝ) → Prop := fun x c f => c.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R c.1 (f x) ∧ O c.2 d
let K : E → Z → (E → ℂ) → Prop := fun x c f => J x c.1 (fun y => (f y).re) ∧ J x c.2 (fun y => (f y).im)
let V : (I × I × I) → EuclideanSpace ℝ (Fin 3) → Prop := fun p y => R p.1 (y 0) ∧ R p.2.1 (y 1) ∧ R p.2.2 (y 2)
let q : ℤ → ℤ → I := fun u v => (u*s/v,-((-u*s)/v),decide (0<v))
let ia : I → I → I := fun x y => (x.1+y.1,x.2.1+y.2.1,x.2.2 && y.2.2)
let ine : I → I := fun x => (-x.2.1,-x.1,x.2.2)
let im : I → I → I := fun x y => (min (min (x.1*y.1) (x.1*y.2.1)) (min (x.2.1*y.1) (x.2.1*y.2.1))/s,-((-max (max (x.1*y.1) (x.1*y.2.1)) (max (x.2.1*y.1) (x.2.1*y.2.1)))/s),x.2.2 && y.2.2)
let ii : I → I := fun x => (s*s/x.2.1,-((-(s*s))/x.1),x.2.2 && decide (0<x.1 ∧ x.1≤x.2.1))
let iq : I → I := fun x => let l : ℤ := Nat.sqrt (x.1*s).toNat; let u : ℤ := (Nat.sqrt (x.2.1*s).toNat : ℤ)+1; (l,u,x.2.2 && decide (0<x.1 ∧ 0≤l ∧ 0≤u ∧ l*l≤x.1*s ∧ x.2.1*s≤u*u))
let is : I → I → I := fun x y => ia x (ine y)
let da : D → D → D := fun x y => (ia x.1 y.1,match x.2,y.2 with | none,v => v | v,none => v | some u,some v => some (ia u.1 v.1,ia u.2 v.2))
let dn : D → D := fun x => (ine x.1,x.2.map (fun d => (ine d.1,ine d.2)))
let ds : D → D → D := fun x y => da x (dn y)
let dm : D → D → D := fun x y => (im x.1 y.1,match x.2,y.2 with | none,none => none | none,some v => some (im x.1 v.1,im x.1 v.2) | some u,none => some (im u.1 y.1,im u.2 y.1) | some u,some v => some (ia (im u.1 y.1) (im x.1 v.1),ia (im u.2 y.1) (im x.1 v.2)))
let di : D → D := fun x => let v := ii x.1; (v,x.2.map (fun d => (im (im (ine d.1) v) v,im (im (ine d.2) v) v)))
let dq : D → D := fun x => let v := iq x.1; let t := ii (im (q 2 1) v); (v,x.2.map (fun d => (im t d.1,im t d.2)))
let dc : ℤ → ℤ → D := fun u v => (q u v,none)
let zs : Z → Z → Z := fun x y => (ds x.1 y.1,ds x.2 y.2)
let zm : Z → Z → Z := fun x y => (ds (dm x.1 y.1) (dm x.2 y.2),da (dm x.1 y.2) (dm x.2 y.1))
let zsc : Z → D → Z := fun x t => (dm x.1 t,dm x.2 t)
let zz : Z := (dc 0 1,dc 0 1)
let zo : Z := (dc 1 1,dc 0 1)
let pz : D × D × D := (dc 0 1,dc 0 1,dc 0 1)
let fac : (D × D × D) → (D × D × D) → Z × D := fun p q => let d0 := ds q.1 p.1; let d1 := ds q.2.1 p.2.1; let d2 := ds q.2.2 p.2.2; ((d0,d1),ds (dq (da (da (dm d0 d0) (dm d1 d1)) (dm d2 d2))) d2)
let tim : List Z → (Z × D) → List Z := fun p f => List.zipWith zs ((p.map (zm f.1)) ++ [zz]) (zz :: p.map (fun t => zsc t f.2))
let zs0 : (I × I) → (I × I) → I × I := fun x y => (is x.1 y.1,is x.2 y.2)
let zm0 : (I × I) → (I × I) → I × I := fun x y => (is (im x.1 y.1) (im x.2 y.2),ia (im x.1 y.2) (im x.2 y.1))
let zsc0 : (I × I) → I → I × I := fun x t => (im x.1 t,im x.2 t)
let zz0 : I × I := (q 0 1,q 0 1)
let zo0 : I × I := (q 1 1,q 0 1)
let pz0 : I × I × I := (q 0 1,q 0 1,q 0 1)
let fac0 : (I × I × I) → (I × I × I) → (I × I) × I := fun p q => let d0 := is q.1 p.1; let d1 := is q.2.1 p.2.1; let d2 := is q.2.2 p.2.2; ((d0,d1),is (iq (ia (ia (im d0 d0) (im d1 d1)) (im d2 d2))) d2)
let tim0 : List (I × I) → ((I × I) × I) → List (I × I) := fun p f => List.zipWith zs0 ((p.map (zm0 f.1)) ++ [zz0]) (zz0 :: p.map (fun t => zsc0 t f.2))
let fb : (E → EuclideanSpace ℝ (Fin 3)) → (E → EuclideanSpace ℝ (Fin 3)) → (E → ℂ) × (E → ℝ) := fun p q => ((fun y => (((q y-p y) 0:ℝ):ℂ)+(((q y-p y) 1:ℝ):ℂ)*Complex.I),(fun y => ‖q y-p y‖-(q y-p y) 2))
let tb : List (E → ℂ) → ((E → ℂ) × (E → ℝ)) → List (E → ℂ) := fun p f => List.zipWith (fun a b y => a y-b y) ((p.map (fun a y => f.1 y*a y)) ++ [fun _ => 0]) ((fun _ => 0) :: p.map (fun a y => a y*(f.2 y:ℂ)))
∀ (ps : List (I × I × I)) (qs : List (EuclideanSpace ℝ (Fin 3))), List.Forall₂ V ps qs →
let pts := ps.map (fun p => ((p.1,none),(p.2.1,none),(p.2.2,none)))
let qts : List (E → EuclideanSpace ℝ (Fin 3)) := qs.map (fun p => fun _ => p)
let C0 := (List.range m).map (fun i => if i = mov then [zo0] else ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)).foldl (fun p j => tim0 p (fac0 (ps.getD i pz0) (ps.getD j pz0))) [zo0])
let C := C0.map (List.map (fun z => ((z.1,none),(z.2,none))))
let Cb := (List.range m).map (fun i => if i = mov then [fun _ => (1:ℂ)] else ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)).foldl (fun p j => tb p (fb (qts.getD i (fun _ => 0)) (qts.getD j (fun _ => 0)))) [fun _ => 1])
let v : I := ((q (-a) b).1,(q a b).2.1,true)
let h : D := (v,some (q 1 1,q 0 1))
let k : D := (v,some (q 0 1,q 1 1))
let old := pts.getD mov pz
let p := (da old.1 h,old.2.1,da old.2.2 k)
let pts' := (pts.set mov p).set (mov+m) (dn p.1,dn p.2.1,p.2.2)
let oldq := qts.getD mov (fun _ => 0)
let newq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![oldq y 0+y 0,oldq y 1,oldq y 2+y 1]
let mateq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![-newq y 0,-newq y 1,newq y 2]
let qts' := (qts.set mov newq).set (mov+m) mateq
let A := (List.range m).map (fun i =>
 let js := if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov,mov+m]
 let p := js.foldl (fun p j => tim p (fac (pts'.getD i pz) (pts'.getD j pz))) (C.getD i [zo])
 (List.range m).map (fun k => zsc (zsc (p.getD (2*k) zz) (dc 1 (2^(ce.getD k 0)))) (dc 1 (2^(re.getD i 0)))))
let B := (List.range m).map (fun i =>
 let js := if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov,mov+m]
 let p := js.foldl (fun p j => tb p (fb (qts'.getD i (fun _ => 0)) (qts'.getD j (fun _ => 0)))) (Cb.getD i [fun _ => 1])
 (List.range m).map (fun k => fun y => (p.getD (2*k) (fun _ => 0) y) * ((1/(2:ℝ)^(ce.getD k 0)):ℂ) * ((1/(2:ℝ)^(re.getD i 0)):ℂ)))
∀ x ∈ Metric.closedBall (0:E) ((a:ℝ)/(b:ℝ)), List.Forall₂ (List.Forall₂ (K x)) A B
) := by
  intro s a b hs hb m mov re ce I D Z E R O J K V q ia ine im ii iq is da dn ds dm di dq dc zs zm zsc zz zo pz fac tim zs0 zm0 zsc0 zz0 zo0 pz0 fac0 tim0 fb tb ps qs hps pts qts C0 C Cb v h k old p pts' oldq newq mateq qts' A B x hx
  have hj := fixed_ad_ops_sound s hs x (Pi.single 0 1) (Pi.single 1 1)
  extract_lets at hj
  have hc : ∀ u c, R u c → J x (u,none) (fun _ => c) := hj.1
  have ha : ∀ u v f g, J x u f → J x v g → J x (da u v) (fun y => f y+g y) := hj.2.1
  have hn : ∀ u f, J x u f → J x (dn u) (fun y => -f y) := hj.2.2.1
  have hm : ∀ u v f g, J x u f → J x v g → J x (dm u v) (fun y => f y*g y) := hj.2.2.2.1
  have hi : ∀ u f, J x u f → J x (di u) (fun y => (f y)⁻¹) := hj.2.2.2.2.1
  have hsq : ∀ u f, J x u f → J x (dq u) (fun y => Real.sqrt (f y)) := hj.2.2.2.2.2
  let T : (D × D × D) → (E → EuclideanSpace ℝ (Fin 3)) → Prop := fun c f => J x c.1 (fun y => f y 0) ∧ J x c.2.1 (fun y => f y 1) ∧ J x c.2.2 (fun y => f y 2)
  let T0 : (I × I × I) → (E → EuclideanSpace ℝ (Fin 3)) → Prop := fun c f => J x (c.1,none) (fun y => f y 0) ∧ J x (c.2.1,none) (fun y => f y 1) ∧ J x (c.2.2,none) (fun y => f y 2)
  have hps0 : List.Forall₂ T0 ps qts := by
   apply List.forall₂_map_right_iff.mpr
   exact hps.imp (fun c f hc0 => ⟨hc _ _ hc0.1,hc _ _ hc0.2.1,hc _ _ hc0.2.2⟩)
  have hC0 := constant_rows_ad_sound s hs x m mov
  extract_lets at hC0
  specialize hC0 ps qts hps0
  have hC : List.Forall₂ (List.Forall₂ (K x)) C Cb := by
   apply List.forall₂_map_left_iff.mpr
   apply hC0.imp
   intro u v huv
   exact List.forall₂_map_left_iff.mpr huv
  have hp' := moving_pair_inputs_ad_sound s a b hs hb mov (mov+m)
  extract_lets at hp'
  specialize hp' ps qs hps
  extract_lets at hp'
  specialize hp' x hx
  have hpairs : List.Forall₂ T pts' qts' := hp'.2
  have hq : ∀ u v, R (q u v) ((u:ℝ)/(v:ℝ)) := (fixed_primitives_sound s hs).1
  have h0 : J x (dc 0 1) (fun _ => 0) := hc _ 0 (by simpa using hq 0 1)
  have h1 : J x (dc 1 1) (fun _ => 1) := hc _ 1 (by simpa using hq 1 1)
  have hz : K x zz (fun _ => 0) := by simpa only [K,zz,Complex.zero_re,Complex.zero_im] using And.intro h0 h0
  have ho : K x zo (fun _ => 1) := by simpa only [K,zo,Complex.one_re,Complex.one_im] using And.intro h1 h0
  have hp : T pz (fun _ => 0) := ⟨h0,h0,h0⟩
  have hzops := complex_pair_ops_sound (J x) da dm dn di ha hm hn hi
  extract_lets at hzops
  have hs' : ∀ u f v g, K x u f → K x v g → K x (zs u v) (fun y => f y-g y) := by
   intro u f v g hf hg
   exact hzops.2.2.1 u v f g hf hg
  have hm' : ∀ u f v g, K x u f → K x v g → K x (zm u v) (fun y => f y*g y) := by
   intro u f v g hf hg
   exact hzops.2.2.2.1 u v f g hf hg
  have hc' : ∀ u f v g, K x u f → J x v g → K x (zsc u v) (fun y => f y*(g y:ℂ)) := by
   intro u f v g hf hg
   exact hzops.2.2.2.2.2.1 u v f g hf hg
  have hf := raw_factor_is_lift (J x) da dm dn dq ha hm hn hsq
  extract_lets at hf
  have hfac : ∀ u v u' v', T u v → T u' v' → K x (fac u u').1 (fb v v').1 ∧ J x (fac u u').2 (fb v v').2 := by
   intro u v u' v' hu hv
   exact hf u u' v v' hu hv
  have hscale : ∀ e : ℕ, J x (dc 1 (2^e)) (fun _ => 1/(2:ℝ)^e) := by
   intro e
   apply hc
   simpa only [Int.cast_one, Int.cast_pow, Int.cast_ofNat] using hq 1 (2^e)
  have hall := coeff_rows_sound (K x) (J x) T zz zo (fun _ => 0) (fun _ => 1) pz (fun _ => 0) zs zm (fun f g y => f y-g y) (fun f g y => f y*g y) zsc (fun f g y => f y*(g y:ℂ)) fac fb (fun i => dc 1 (2^(re.getD i 0))) (fun i => dc 1 (2^(ce.getD i 0))) (fun i _ => 1/(2:ℝ)^(re.getD i 0)) (fun i _ => 1/(2:ℝ)^(ce.getD i 0)) hz ho hp hs' hm' hc' hfac (fun i => hscale _) (fun i => hscale _) m mov
  extract_lets L M timB prodA prodB constA constB blockA blockB at hall
  clear_value fac fb zs zm zsc dc pts' qts' C Cb
  have hAA : blockA pts' C = A := by rfl
  have htimB : timB = tb := by funext u f; rfl
  have hBB : blockB qts' Cb = B := by
   dsimp only [blockB,prodB]
   rw [htimB]
   simp only [B, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_one]
  rw [← hAA, ← hBB]
  exact hall.2.2.2 pts' qts' C Cb hpairs hC

end Atiyah.Facts

/-! ### `Atiyah.Facts`: LU -/

/-!
# Pivoted elimination and back substitution

Algebraic correctness of the exact list LU and backsolve, and the consequence that a zero Schur residual
with nonzero pivots is a column dependence of the square block.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- Every LU stage, back-substitution and Schur residual preserves any compatible scalar relation -/
theorem lu_schur_sound : (
∀ {A B : Type} (R : A → B → Prop) (za : A) (zb : B)
(sa ma : A → A → A) (sb mb : B → B → B) (ia : A → A) (ib : B → B)
(hz : R za zb)
(hs : ∀ a b c d, R a b → R c d → R (sa a c) (sb b d))
(hm : ∀ a b c d, R a b → R c d → R (ma a c) (mb b d))
(hi : ∀ a b, R a b → R (ia a) (ib b)) (n : ℕ) (piv : List ℕ),
let L := List.Forall₂ R
let M := List.Forall₂ L
let stepA : List (List A) → ℕ → List (List A) := fun X k =>
 let p := piv.getD k k
 let X := (X.set k (X.getD p [])).set p (X.getD k [])
 let row := X.getD k []
 let ip := ia (row.getD k za)
 X.mapIdx (fun i r => if k < i then
  let v := ma (r.getD k za) ip
  r.mapIdx (fun j z => if k < j then sa z (ma v (row.getD j za)) else z) else r)
let stepB : List (List B) → ℕ → List (List B) := fun X k =>
 let p := piv.getD k k
 let X := (X.set k (X.getD p [])).set p (X.getD k [])
 let row := X.getD k []
 let ip := ib (row.getD k zb)
 X.mapIdx (fun i r => if k < i then
  let v := mb (r.getD k zb) ip
  r.mapIdx (fun j z => if k < j then sb z (mb v (row.getD j zb)) else z) else r)
let backA : List (List A) → List A := fun X =>
 (List.range n).reverse.foldl (fun v i =>
  let row := X.getD i []
  let t := (List.range n).foldl (fun t j => if i < j then sa t (ma (row.getD j za) (v.getD j za)) else t) (row.getD n za)
  v.set i (ma t (ia (row.getD i za)))) (List.replicate n za)
let backB : List (List B) → List B := fun X =>
 (List.range n).reverse.foldl (fun v i =>
  let row := X.getD i []
  let t := (List.range n).foldl (fun t j => if i < j then sb t (mb (row.getD j zb) (v.getD j zb)) else t) (row.getD n zb)
  v.set i (mb t (ib (row.getD i zb)))) (List.replicate n zb)
let resA : List (List A) → List A → A := fun X row =>
 (List.range n).foldl (fun z k => sa z (ma (row.getD (k+1) za) ((backA X).getD k za))) (row.getD 0 za)
let resB : List (List B) → List B → B := fun X row =>
 (List.range n).foldl (fun z k => sb z (mb (row.getD (k+1) zb) ((backB X).getD k zb))) (row.getD 0 zb)
(∀ X Y, M X Y → ∀ k, M (stepA X k) (stepB Y k)) ∧
(∀ X Y, M X Y → ∀ stages : List ℕ, M (stages.foldl stepA X) (stages.foldl stepB Y)) ∧
(∀ X Y, M X Y → L (backA X) (backB Y)) ∧
(∀ X Y rowA rowB, M X Y → L rowA rowB → R (resA X rowA) (resB Y rowB))
) := by
  intro A B R za zb sa ma sb mb ia ib hz hs hm hi n piv L M stepA stepB backA backB resA resB
  have getR (l : List A) (k : List B) (h : L l k) (i : ℕ) : R (l.getD i za) (k.getD i zb) :=
    (forall₂_getD_set R l k h za zb hz i).1
  have setR (l : List A) (k : List B) (h : L l k) (a : A) (b : B) (hab : R a b) (i : ℕ) : L (l.set i a) (k.set i b) :=
    (forall₂_getD_set R l k h a b hab i).2
  have getL (l : List (List A)) (k : List (List B)) (h : M l k) (i : ℕ) : L (l.getD i []) (k.getD i []) :=
    (forall₂_getD_set L l k h [] [] List.Forall₂.nil i).1
  have setL (l : List (List A)) (k : List (List B)) (h : M l k) (a : List A) (b : List B) (hab : L a b) (i : ℕ) : M (l.set i a) (k.set i b) :=
    (forall₂_getD_set L l k h a b hab i).2
  have foldR {U W : Type} (S : U → W → Prop) (f : U → ℕ → U) (g : W → ℕ → W)
      (hf : ∀ u w i, S u w → S (f u i) (g w i)) (ns : List ℕ) (u : U) (w : W) (huw : S u w) : S (ns.foldl f u) (ns.foldl g w) := by
    refine List.rel_foldl (R := (Eq : ℕ → ℕ → Prop)) ?_ huw ?_
    · intro u w h i j hij
      subst j
      exact hf u w i h
    · exact List.forall₂_same.mpr (fun _ _ => rfl)
  have hstep : ∀ X Y, M X Y → ∀ k, M (stepA X k) (stepB Y k) := by
    intro X Y hXY k
    let p := piv.getD k k
    let X' := (X.set k (X.getD p [])).set p (X.getD k [])
    let Y' := (Y.set k (Y.getD p [])).set p (Y.getD k [])
    have hswap : M X' Y' := setL _ _ (setL _ _ hXY _ _ (getL _ _ hXY p) k) _ _ (getL _ _ hXY k) p
    have hrow := getL _ _ hswap k
    have hip := hi _ _ (getR _ _ hrow k)
    dsimp only [stepA,stepB]
    apply forall₂_mapIdx L L _ _ hswap
    intro i r t hrt
    split_ifs with hki
    · have hv := hm _ _ _ _ (getR _ _ hrt k) hip
      apply forall₂_mapIdx R R _ _ hrt
      intro j a b hab
      split_ifs with hkj
      · exact hs _ _ _ _ hab (hm _ _ _ _ hv (getR _ _ hrow j))
      · exact hab
    · exact hrt
  have hback : ∀ X Y, M X Y → L (backA X) (backB Y) := by
    intro X Y hXY
    have hinit : ∀ m, L (List.replicate m za) (List.replicate m zb) := by
      intro m
      induction m with
      | zero => exact List.Forall₂.nil
      | succ m ih => simpa only [L, List.replicate_succ] using List.Forall₂.cons hz ih
    dsimp only [backA,backB]
    refine foldR L _ _ ?_ _ _ _ (hinit n)
    intro v w i hvw
    have hrow := getL _ _ hXY i
    apply setR _ _ hvw
    apply hm
    · refine foldR R _ _ ?_ _ _ _ (getR _ _ hrow n)
      intro t u j htu
      split_ifs with hij
      · exact hs _ _ _ _ htu (hm _ _ _ _ (getR _ _ hrow j) (getR _ _ hvw j))
      · exact htu
    · exact hi _ _ (getR _ _ hrow i)
  refine ⟨hstep,?_,hback,?_⟩
  · intro X Y hXY stages
    exact foldR M stepA stepB (fun X Y k h => hstep X Y h k) stages X Y hXY
  · intro X Y rowA rowB hXY hrow
    dsimp only [resA,resB]
    refine foldR R _ _ ?_ _ _ _ (getR _ _ hrow 0)
    intro a b k hab
    exact hs _ _ _ _ hab (hm _ _ _ _ (getR _ _ hrow (k+1)) (getR _ _ (hback X Y hXY) k))

/-- Exact pivoted list LU step preserves rectangular shape and has the expected scalar entry formula -/
theorem lu_step_shape : (
∀ (n k p : ℕ) (X : List (List ℂ)), X.length = n → (∀ i < n, (X.getD i []).length = n+1) → k < n → p < n →
 let σ : ℕ → ℕ := fun i => if i = k then p else if i = p then k else i
 let A : ℕ → ℕ → ℂ := fun i j => (X.getD (σ i) []).getD j 0
 let S := (X.set k (X.getD p [])).set p (X.getD k [])
 let row := S.getD k []
 let ip := (row.getD k 0)⁻¹
 let Y := S.mapIdx (fun i r => if k < i then
  let v := (r.getD k 0) * ip
  r.mapIdx (fun j z => if k < j then z - v * (row.getD j 0) else z) else r)
 Y.length = n ∧ (∀ i < n, (Y.getD i []).length = n+1) ∧
 ∀ i < n, ∀ j ≤ n, (Y.getD i []).getD j 0 =
   if k < i ∧ k < j then A i j - (A i k * (A k k)⁻¹) * A k j else A i j
) := by
  classical
  intro n k p X hx hr hk hp σ A S row ip Y
  have hget : ∀ {α : Type} (v : List α) (i : ℕ) (c d : α), i < v.length →
      ∀ j, (v.set i c).getD j d = if i = j then c else v.getD j d := by
    intro α v i c d hi j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_of_lt' c v hi]
    split <;> simp_all
  have hmap : ∀ {α β : Type} (l : List α) (f : ℕ → α → β) (i : ℕ) (a : α) (b : β),
      i < l.length → (l.mapIdx f).getD i b = f i (l.getD i a) := by
    intro α β l f i a b hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some]
  have hsl : S.length = n := by simp [S, hx]
  have hsg : ∀ i, S.getD i [] = X.getD (σ i) [] := by
    intro i
    dsimp only [S]
    rw [hget _ p _ [] (by simpa [hx] using hp) i, hget _ k _ [] (by simpa only [hx] using hk) i]
    by_cases hik : i = k
    · subst i
      by_cases hkp : k = p <;> simp [σ, hkp, eq_comm]
    · by_cases hip : i = p
      · subst i; simp [σ, hik, Ne.symm hik]
      · simp [σ, hik, hip, Ne.symm hik, Ne.symm hip]
  have hσ : ∀ i < n, σ i < n := by
    intro i hi
    dsimp only [σ]
    split
    · exact hp
    · split
      · exact hk
      · exact hi
  have hsr : ∀ i < n, (S.getD i []).length = n+1 := by
    intro i hi
    rw [hsg]
    exact hr _ (hσ i hi)
  have hrow : ∀ j, row.getD j 0 = A k j := by intro j; dsimp only [row, A]; rw [hsg]
  have hy : ∀ i < n, Y.getD i [] =
      if k < i then (S.getD i []).mapIdx (fun j z => if k < j then z - ((S.getD i []).getD k 0 * ip) * row.getD j 0 else z)
      else S.getD i [] := by
    intro i hi
    exact hmap S _ i [] [] (by simpa only [hsl] using hi)
  refine ⟨by simp [Y, hsl], ?_, ?_⟩
  · intro i hi
    rw [hy i hi]
    split <;> simp only [List.length_mapIdx, hsr i hi]
  · intro i hi j hj
    rw [hy i hi]
    by_cases hki : k < i
    · rw [if_pos hki, hmap _ _ j 0 0 (by rw [hsr i hi]; omega)]
      simp only [hsg, hrow, ip, A, hki, true_and]
    · simp only [if_neg hki, hsg, hki, false_and, if_false, A]

/-- Stale-entry Gaussian elimination preserves triangular-frontier solutions at a nonzero pivot -/
theorem elim_preserves_frontier : (
∀ (n k : ℕ) (A : ℕ → ℕ → ℂ) (v : ℕ → ℂ), k < n → A k k ≠ 0 →
 let B : ℕ → ℕ → ℂ := fun i j => if k < i ∧ k < j then A i j - (A i k * (A k k)⁻¹) * A k j else A i j
 (∀ i < n, (∑ j ∈ Finset.range n, if min i (k+1) ≤ j then B i j * v j else 0) = B i n) →
 ∀ i < n, (∑ j ∈ Finset.range n, if min i k ≤ j then A i j * v j else 0) = A i n
) := by
  classical
  intro n k A v hk hp B hs
  have hsplit : ∀ r : ℕ → ℂ,
      (∑ j ∈ Finset.range n, if k ≤ j then r j * v j else 0) =
      r k * v k + ∑ j ∈ Finset.range n, if k < j then r j * v j else 0 := by
    intro r
    calc
      _ = ∑ j ∈ Finset.range n, ((if j = k then r k * v k else 0) +
          (if k < j then r j * v j else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases he : j = k
        · subst j; simp
        · by_cases hl : k < j
          · simp [he, hl, Nat.le_of_lt hl]
          · simp [he, hl, show ¬ k ≤ j by omega]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [hk]
  have hrow : A k k * v k + (∑ j ∈ Finset.range n, if k < j then A k j * v j else 0) = A k n := by
    have h := hs k hk
    simpa only [B, lt_self_iff_false, false_and, if_false, min_eq_left (by omega : k ≤ k+1), hsplit] using h
  intro i hi
  by_cases hik : i ≤ k
  · have h := hs i hi
    simpa only [B, show ¬ k < i by omega, false_and, if_false,
      min_eq_left hik, min_eq_left (by omega : i ≤ k+1)] using h
  · have hki : k < i := by omega
    have hnext : (∑ j ∈ Finset.range n, if k < j then A i j * v j else 0) -
        (A i k * (A k k)⁻¹) * (∑ j ∈ Finset.range n, if k < j then A k j * v j else 0) =
        A i n - (A i k * (A k k)⁻¹) * A k n := by
      have h := hs i hi
      rw [min_eq_right (by omega : k+1 ≤ i)] at h
      have he : (∑ j ∈ Finset.range n, if k+1 ≤ j then B i j * v j else 0) =
          (∑ j ∈ Finset.range n, if k < j then A i j * v j else 0) -
          (A i k * (A k k)⁻¹) * (∑ j ∈ Finset.range n, if k < j then A k j * v j else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hkj : k < j
        · simp only [show k+1 ≤ j by omega, if_true, B, hki, hkj, true_and, and_self, if_true]
          ring
        · simp [hkj, show ¬ k+1 ≤ j by omega]
      rw [he] at h
      simpa only [B, hki, hk, and_self, if_true] using h
    rw [min_eq_right (by omega : k ≤ i), hsplit]
    have hmul : (A i k * (A k k)⁻¹) * A k k = A i k := by field_simp
    calc
      _ = (A i k * (A k k)⁻¹) *
          (A k k * v k + (∑ j ∈ Finset.range n, if k < j then A k j * v j else 0)) +
          ((∑ j ∈ Finset.range n, if k < j then A i j * v j else 0) -
            (A i k * (A k k)⁻¹) * (∑ j ∈ Finset.range n, if k < j then A k j * v j else 0)) := by
        rw [mul_add, ← mul_assoc, hmul]
        ring
      _ = A i n := by rw [hrow, hnext]; ring

/-- Actual pivoted list LU step transports frontier solutions backward and propagates pivot diagonals -/
theorem lu_step_frontier : (
∀ (n k p : ℕ) (X : List (List ℂ)), X.length = n → (∀ i < n, (X.getD i []).length = n+1) → k < n → k ≤ p → p < n → (X.getD p []).getD k 0 ≠ 0 →
 let S := (X.set k (X.getD p [])).set p (X.getD k [])
 let row := S.getD k []
 let ip := (row.getD k 0)⁻¹
 let Y := S.mapIdx (fun i r => if k < i then
  let v := r.getD k 0 * ip
  r.mapIdx (fun j z => if k < j then z - v * row.getD j 0 else z) else r)
 Y.length = n ∧ (∀ i < n, (Y.getD i []).length = n+1) ∧
 (∀ i < k, (Y.getD i []).getD i 0 = (X.getD i []).getD i 0) ∧
 (Y.getD k []).getD k 0 = (X.getD p []).getD k 0 ∧
 ∀ v : ℕ → ℂ,
  (∀ i < n, (∑ j ∈ Finset.range n, if min i (k+1) ≤ j then (Y.getD i []).getD j 0 * v j else 0) = (Y.getD i []).getD n 0) →
  ∀ i < n, (∑ j ∈ Finset.range n, if min i k ≤ j then (X.getD i []).getD j 0 * v j else 0) = (X.getD i []).getD n 0
) := by
  classical
  intro n k p X hx hr hk hkp hp hnz S row ip Y
  have ht := lu_step_shape n k p X hx hr hk hp
  extract_lets σ A at ht
  change Y.length = n ∧ (∀ i < n, (Y.getD i []).length = n+1) ∧
    (∀ i < n, ∀ j ≤ n, (Y.getD i []).getD j 0 = if k < i ∧ k < j then A i j - (A i k * (A k k)⁻¹) * A k j else A i j) at ht
  rcases ht with ⟨hyl, hyr, he⟩
  refine ⟨hyl, hyr, ?_, ?_, ?_⟩
  · intro i hi
    rw [he i (by omega) i (by omega)]
    simp [show ¬ k < i by omega, A, σ, show i ≠ k by omega, show i ≠ p by omega]
  · rw [he k hk k (by omega)]
    simp [A, σ]
  · intro v hs
    let B : ℕ → ℕ → ℂ := fun i j => if k < i ∧ k < j then A i j - (A i k * (A k k)⁻¹) * A k j else A i j
    change ∀ i < n, ∀ j ≤ n, (Y.getD i []).getD j 0 = B i j at he
    have hb : ∀ i < n, (∑ j ∈ Finset.range n, if min i (k+1) ≤ j then B i j * v j else 0) = B i n := by
      intro i hi
      rw [← he i hi n le_rfl]
      rw [← hs i hi]
      apply Finset.sum_congr rfl
      intro j hj
      rw [he i hi j (Nat.le_of_lt (Finset.mem_range.mp hj))]
    have ha : A k k ≠ 0 := by simpa [A, σ] using hnz
    have hh := elim_preserves_frontier n k A v hk ha hb
    have hσk : σ k = p := by simp [σ]
    have hσp : σ p = k := by by_cases h : p = k <;> simp [σ, h]
    intro i hi
    by_cases hik : i = k
    · subst i
      have h := hh p hp
      simpa only [A, hσp, min_eq_right hkp, min_self] using h
    · by_cases hip : i = p
      · subst i
        have h := hh k hk
        simpa only [A, hσk, min_self, min_eq_right hkp] using h
      · have hσi : σ i = i := by simp [σ, hik, hip]
        simpa only [A, hσi] using hh i hi

/-- Exact reverse-list back substitution solves every upper-triangular row with nonzero diagonal -/
theorem backsolve_correct : (
∀ (n : ℕ) (X : List (List ℂ)),
 (∀ i < n, (X.getD i []).getD i 0 ≠ 0) →
 let step : List ℂ → ℕ → List ℂ := fun v i =>
  let row := X.getD i []
  let t := (List.range n).foldl (fun t j => if i < j then t - (row.getD j 0) * (v.getD j 0) else t) (row.getD n 0)
  v.set i (t * (row.getD i 0)⁻¹)
 let v := (List.range n).reverse.foldl step (List.replicate n 0)
 v.length = n ∧ ∀ i < n, (∑ j ∈ Finset.range n, if i ≤ j then (X.getD i []).getD j 0 * v.getD j 0 else 0) = (X.getD i []).getD n 0
) := by
  classical
  intro n X hp
  dsimp only
  let a : ℕ → ℕ → ℂ := fun i j => (X.getD i []).getD j 0
  let upd : List ℂ → ℕ → List ℂ := fun v i => v.set i
    ((a i n - ∑ j ∈ Finset.range n, if i < j then a i j * v.getD j 0 else 0) * (a i i)⁻¹)
  have hfold : ∀ (f : ℕ → ℂ) (m : ℕ) (b : ℂ),
      (List.range m).foldl (fun t j => t - f j) b = b - ∑ j ∈ Finset.range m, f j := by
    intro f m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Finset.sum_range_succ, ih]
      ring
  have hstep : (fun (v : List ℂ) i =>
      v.set i (((List.range n).foldl (fun t j => if i < j then t - (X.getD i []).getD j 0 * v.getD j 0 else t)
        ((X.getD i []).getD n 0)) * ((X.getD i []).getD i 0)⁻¹)) = upd := by
    funext v i
    have hf : (fun (t : ℂ) j => if i < j then t - a i j * v.getD j 0 else t) =
        (fun t j => t - (if i < j then a i j * v.getD j 0 else 0)) := by
      funext t j
      split <;> simp_all
    change v.set i (((List.range n).foldl _ (a i n)) * (a i i)⁻¹) = _
    rw [hf, hfold]
  rw [hstep]
  change ((List.range n).reverse.foldl upd (List.replicate n 0)).length = n ∧
    ∀ i < n, (∑ j ∈ Finset.range n, if i ≤ j then a i j * ((List.range n).reverse.foldl upd (List.replicate n 0)).getD j 0 else 0) = a i n
  have hget : ∀ (v : List ℂ) (i : ℕ) (c : ℂ), i < v.length →
      ∀ j, (v.set i c).getD j 0 = if i = j then c else v.getD j 0 := by
    intro v i c hi j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_of_lt' c v hi]
    split <;> simp_all
  have hsplit : ∀ (v : List ℂ) (i : ℕ), i < n →
      (∑ j ∈ Finset.range n, if i ≤ j then a i j * v.getD j 0 else 0) =
      a i i * v.getD i 0 + ∑ j ∈ Finset.range n, if i < j then a i j * v.getD j 0 else 0 := by
    intro v i hi
    calc
      _ = ∑ j ∈ Finset.range n, ((if j = i then a i i * v.getD i 0 else 0) +
          (if i < j then a i j * v.getD j 0 else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases he : j = i
        · subst j; simp
        · by_cases hl : i < j
          · simp [he, hl, Nat.le_of_lt hl]
          · simp [he, hl, show ¬ i ≤ j by omega]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [hi]
  have go : ∀ k ≤ n, ∀ (v : List ℂ), v.length = n →
      (∀ i, k ≤ i → i < n → (∑ j ∈ Finset.range n, if i ≤ j then a i j * v.getD j 0 else 0) = a i n) →
      ((List.range k).reverse.foldl upd v).length = n ∧
      ∀ i < n, (∑ j ∈ Finset.range n, if i ≤ j then a i j * ((List.range k).reverse.foldl upd v).getD j 0 else 0) = a i n := by
    intro k
    induction k with
    | zero =>
      intro hk v hv hs
      simpa using And.intro hv (fun i hi => hs i (Nat.zero_le i) hi)
    | succ k ih =>
      intro hk v hv hs
      have hkn : k < n := by omega
      have hvl : (upd v k).length = n := by simp [upd, hv]
      have htail : ∀ i, k ≤ i →
          (∑ j ∈ Finset.range n, if i < j then a i j * (upd v k).getD j 0 else 0) =
          (∑ j ∈ Finset.range n, if i < j then a i j * v.getD j 0 else 0) := by
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i < j
        · have hkj : k ≠ j := by omega
          simp only [if_pos hij, upd, hget v k _ (by omega) j, if_neg hkj]
        · simp [hij]
      have hvs : ∀ i, k ≤ i → i < n →
          (∑ j ∈ Finset.range n, if i ≤ j then a i j * (upd v k).getD j 0 else 0) = a i n := by
        intro i hi hin
        by_cases hik : i = k
        · subst i
          rw [hsplit _ _ hkn, htail k le_rfl]
          rw [show (upd v k).getD k 0 =
            (a k n - ∑ j ∈ Finset.range n, if k < j then a k j * v.getD j 0 else 0) * (a k k)⁻¹ by
              change (v.set k _).getD k 0 = _
              rw [hget v k _ (by omega) k, if_pos rfl]]
          have hnz : a k k ≠ 0 := hp k hkn
          field_simp
          <;> ring
        · calc
            _ = ∑ j ∈ Finset.range n, if i ≤ j then a i j * v.getD j 0 else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hij : i ≤ j
              · have hkj : k ≠ j := by omega
                simp only [if_pos hij, upd, hget v k _ (by omega) j, if_neg hkj]
              · simp [hij]
            _ = a i n := hs i (by omega) hin
      simpa only [List.range_succ, List.reverse_append, List.reverse_singleton,
        List.foldl_append, List.foldl_cons, List.foldl_nil] using
        ih (by omega) (upd v k) hvl hvs
  exact go n le_rfl (List.replicate n 0) (by simp) (by intro i hi hin; omega)

/-- Exact pivoted stale-entry list LU and reverse backsolve solve every original augmented equation -/
theorem lu_backsolve_correct : (
∀ (n : ℕ) (piv : List ℕ) (X : List (List ℂ)), X.length = n → (∀ i < n, (X.getD i []).length = n+1) →
 let step : List (List ℂ) → ℕ → List (List ℂ) := fun X k =>
  let p := piv.getD k k
  let S := (X.set k (X.getD p [])).set p (X.getD k [])
  let row := S.getD k []
  let ip := (row.getD k 0)⁻¹
  S.mapIdx (fun i r => if k < i then
   let v := r.getD k 0 * ip
   r.mapIdx (fun j z => if k < j then z - v * row.getD j 0 else z) else r)
 (∀ k < n, k ≤ piv.getD k k ∧ piv.getD k k < n ∧
  ((((List.range k).foldl step X).getD (piv.getD k k) []).getD k 0 ≠ 0)) →
 let U := (List.range n).foldl step X
 let backstep : List ℂ → ℕ → List ℂ := fun v i =>
  let row := U.getD i []
  let t := (List.range n).foldl (fun t j => if i < j then t - row.getD j 0 * v.getD j 0 else t) (row.getD n 0)
  v.set i (t * (row.getD i 0)⁻¹)
 let v := (List.range n).reverse.foldl backstep (List.replicate n 0)
 v.length = n ∧ ∀ i < n, (∑ j ∈ Finset.range n, (X.getD i []).getD j 0 * v.getD j 0) = (X.getD i []).getD n 0
) := by
  classical
  intro n piv X hx hr step hp U backstep v
  let T : ℕ → List (List ℂ) := fun k => (List.range k).foldl step X
  have hT : ∀ k, T (k+1) = step (T k) k := by
    intro k
    simp only [T, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have go : ∀ k ≤ n,
      (T k).length = n ∧ (∀ i < n, ((T k).getD i []).length = n+1) ∧
      (∀ i < k, ((T k).getD i []).getD i 0 ≠ 0) ∧
      ∀ w : ℕ → ℂ,
       (∀ i < n, (∑ j ∈ Finset.range n, if min i k ≤ j then ((T k).getD i []).getD j 0 * w j else 0) = ((T k).getD i []).getD n 0) →
       ∀ i < n, (∑ j ∈ Finset.range n, (X.getD i []).getD j 0 * w j) = (X.getD i []).getD n 0 := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨hx, hr, ?_, ?_⟩
      · intro i hi; omega
      · intro w hw i hi
        simpa only [T, List.range_zero, List.foldl_nil, min_zero, Nat.zero_le, if_true] using hw i hi
    | succ k ih =>
      intro hkn
      have hk : k < n := by omega
      rcases ih (by omega) with ⟨hl, hrows, hd, hs⟩
      rcases hp k hk with ⟨hkp, hpn, hnz⟩
      have ht := lu_step_frontier n k (piv.getD k k) (T k) hl hrows hk hkp hpn hnz
      change (step (T k) k).length = n ∧ (∀ i < n, ((step (T k) k).getD i []).length = n+1) ∧
        (∀ i < k, ((step (T k) k).getD i []).getD i 0 = ((T k).getD i []).getD i 0) ∧
        ((step (T k) k).getD k []).getD k 0 = ((T k).getD (piv.getD k k) []).getD k 0 ∧
        (∀ w : ℕ → ℂ,
          (∀ i < n, (∑ j ∈ Finset.range n, if min i (k+1) ≤ j then ((step (T k) k).getD i []).getD j 0 * w j else 0) = ((step (T k) k).getD i []).getD n 0) →
          ∀ i < n, (∑ j ∈ Finset.range n, if min i k ≤ j then ((T k).getD i []).getD j 0 * w j else 0) = ((T k).getD i []).getD n 0) at ht
      rw [← hT] at ht
      rcases ht with ⟨hl', hrows', hold, hnew, hsolve⟩
      refine ⟨hl', hrows', ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · subst i
          rw [hnew]
          exact hnz
        · rw [hold i (by omega)]
          exact hd i (by omega)
      · intro w hw
        exact hs w (hsolve w hw)
  rcases go n le_rfl with ⟨hl, hrows, hd, hs⟩
  have hb := backsolve_correct n U hd
  change v.length = n ∧ (∀ i < n, (∑ j ∈ Finset.range n, if i ≤ j then (U.getD i []).getD j 0 * v.getD j 0 else 0) = (U.getD i []).getD n 0) at hb
  refine ⟨hb.1, hs (fun j => v.getD j 0) ?_⟩
  intro i hi
  simpa only [min_eq_left (Nat.le_of_lt hi)] using hb.2 i hi

/-- Every prefix pivot equals its final LU diagonal without assuming any pivot nonzero -/
theorem pivot_eq_final_diagonal : (
∀ (n : ℕ) (piv : List ℕ) (X : List (List ℂ)), X.length = n → (∀ i < n, (X.getD i []).length = n+1) →
 (∀ k < n, k ≤ piv.getD k k ∧ piv.getD k k < n) →
 let step : List (List ℂ) → ℕ → List (List ℂ) := fun X k =>
  let p := piv.getD k k
  let S := (X.set k (X.getD p [])).set p (X.getD k [])
  let row := S.getD k []
  let ip := (row.getD k 0)⁻¹
  S.mapIdx (fun i r => if k < i then
   let v := r.getD k 0 * ip
   r.mapIdx (fun j z => if k < j then z - v * row.getD j 0 else z) else r)
 let T : ℕ → List (List ℂ) := fun k => (List.range k).foldl step X
 (T n).length = n ∧ (∀ i < n, ((T n).getD i []).length = n+1) ∧
 ∀ k < n, ((T n).getD k []).getD k 0 = ((T k).getD (piv.getD k k) []).getD k 0
) := by
  classical
  intro n piv X hx hr hp step T
  have hT : ∀ k, T (k+1) = step (T k) k := by
    intro k
    simp only [T, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have go : ∀ m ≤ n,
      (T m).length = n ∧ (∀ i < n, ((T m).getD i []).length = n+1) ∧
      ∀ k < m, ((T m).getD k []).getD k 0 = ((T k).getD (piv.getD k k) []).getD k 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      exact ⟨hx, hr, by intro k hk; omega⟩
    | succ m ih =>
      intro hm
      have hmn : m < n := by omega
      rcases ih (by omega) with ⟨hl, hrows, hd⟩
      rcases hp m hmn with ⟨hmp, hpn⟩
      have ht := lu_step_shape n m (piv.getD m m) (T m) hl hrows hmn hpn
      extract_lets σ A S row ip Y at ht
      have hY : Y = T (m+1) := (hT m).symm
      rw [hY] at ht
      rcases ht with ⟨hl', hrows', he⟩
      refine ⟨hl', hrows', ?_⟩
      intro k hk
      rw [he k (by omega) k (by omega)]
      by_cases hkm : k = m
      · subst k
        simp [A, σ]
      · have hlt : k < m := by omega
        have hkp : k ≠ piv.getD m m := by omega
        simpa only [show ¬ m < k by omega, false_and, if_false, A, σ,
          if_neg hkm, if_neg hkp] using hd k hlt
  exact go n le_rfl

/-- Function-list LU/backsolve solves the original system pointwise whenever final diagonal values are nonzero -/
theorem lu_backsolve_fun_correct : (
∀ (E : Type) (n : ℕ) (piv : List ℕ) (X : List (List (E → ℂ))) (y : E), X.length = n → (∀ i < n, (X.getD i []).length = n+1) →
 (∀ k < n, k ≤ piv.getD k k ∧ piv.getD k k < n) →
 let step : List (List (E → ℂ)) → ℕ → List (List (E → ℂ)) := fun X k =>
  let p := piv.getD k k
  let S := (X.set k (X.getD p [])).set p (X.getD k [])
  let row := S.getD k []
  let ip := (row.getD k 0)⁻¹
  S.mapIdx (fun i r => if k < i then
   let v := r.getD k 0 * ip
   r.mapIdx (fun j z => if k < j then z - v * row.getD j 0 else z) else r)
 let U := (List.range n).foldl step X
 (∀ i < n, ((U.getD i []).getD i 0) y ≠ 0) →
 let back : List (List (E → ℂ)) → List (E → ℂ) := fun U =>
  (List.range n).reverse.foldl (fun v i =>
   let row := U.getD i []
   let t := (List.range n).foldl (fun t j => if i < j then t - row.getD j 0 * v.getD j 0 else t) (row.getD n 0)
   v.set i (t * (row.getD i 0)⁻¹)) (List.replicate n 0)
 let v := back U
 v.length = n ∧ ∀ i < n, (∑ j ∈ Finset.range n, ((X.getD i []).getD j 0) y * (v.getD j 0) y) = ((X.getD i []).getD n 0) y
) := by
  classical
  intro E n piv X y hx hr hp step U hd back v
  let R : (E → ℂ) → ℂ → Prop := fun f c => f y = c
  have hz : R 0 0 := rfl
  have hs : ∀ f c g d, R f c → R g d → R (f-g) (c-d) := by
    intro f c g d hf hg
    change f y - g y = c-d
    rw [hf, hg]
  have hm : ∀ f c g d, R f c → R g d → R (f*g) (c*d) := by
    intro f c g d hf hg
    change f y * g y = c*d
    rw [hf, hg]
  have hi : ∀ f c, R f c → R f⁻¹ c⁻¹ := by
    intro f c hf
    change (f y)⁻¹ = c⁻¹
    rw [hf]
  have hsem := lu_schur_sound R 0 0 (fun f g => f-g) (fun f g => f*g) (fun c d => c-d) (fun c d => c*d) (fun f => f⁻¹) (fun c => c⁻¹) hz hs hm hi n piv
  extract_lets L M stepA stepB backA backB resA resB at hsem
  have hstep : stepA = step := by rfl
  have hback : backA = back := by rfl
  rw [hstep, hback] at hsem
  let C := X.map (fun r => r.map (fun f => f y))
  have hXC : M X C := by
    dsimp only [M, C]
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro r hr
    dsimp only [L]
    rw [List.forall₂_map_right_iff, List.forall₂_same]
    intro f hf
    rfl
  have getR (l : List (E → ℂ)) (k : List ℂ) (h : L l k) (i : ℕ) : R (l.getD i 0) (k.getD i 0) :=
    (forall₂_getD_set R l k h 0 0 hz i).1
  have getL (l : List (List (E → ℂ))) (k : List (List ℂ)) (h : M l k) (i : ℕ) : L (l.getD i []) (k.getD i []) :=
    (forall₂_getD_set L l k h [] [] List.Forall₂.nil i).1
  have hcl : C.length = n := hXC.length_eq.symm.trans hx
  have hcr : ∀ i < n, (C.getD i []).length = n+1 := by
    intro i hi
    exact (getL X C hXC i).length_eq.symm.trans (hr i hi)
  let V := (List.range n).foldl stepB C
  have hUV : M U V := hsem.2.1 X C hXC (List.range n)
  have hdV : ∀ i < n, (V.getD i []).getD i 0 ≠ 0 := by
    intro i hin h0
    apply hd i hin
    exact (getR _ _ (getL _ _ hUV i) i).trans h0
  have hfinal := pivot_eq_final_diagonal n piv C hcl hcr hp
  change V.length = n ∧ (∀ i < n, (V.getD i []).length = n+1) ∧
    ∀ k < n, (V.getD k []).getD k 0 = (((List.range k).foldl stepB C).getD (piv.getD k k) []).getD k 0 at hfinal
  have hpC : ∀ k < n, k ≤ piv.getD k k ∧ piv.getD k k < n ∧
      (((List.range k).foldl stepB C).getD (piv.getD k k) []).getD k 0 ≠ 0 := by
    intro k hk
    refine ⟨(hp k hk).1, (hp k hk).2, ?_⟩
    rw [← hfinal.2.2 k hk]
    exact hdV k hk
  have hsolve := lu_backsolve_correct n piv C hcl hcr hpC
  change (backB V).length = n ∧ ∀ i < n,
    (∑ j ∈ Finset.range n, (C.getD i []).getD j 0 * (backB V).getD j 0) = (C.getD i []).getD n 0 at hsolve
  have hv : L v (backB V) := hsem.2.2.1 U V hUV
  refine ⟨hv.length_eq.trans hsolve.1, ?_⟩
  intro i hin
  calc
    _ = ∑ j ∈ Finset.range n, (C.getD i []).getD j 0 * (backB V).getD j 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [getR _ _ (getL _ _ hXC i) j, getR _ _ hv j]
    _ = (C.getD i []).getD n 0 := hsolve.2 i hin
    _ = ((X.getD i []).getD n 0) y := (getR _ _ (getL _ _ hXC i) n).symm

/-- Zero exact Schur residual and nonzero final LU diagonals imply full square-block column dependence -/
theorem schur_zero_column_dependence : (
∀ (E : Type) (n r : ℕ) (ids piv : List ℕ) (B : List (List (E → ℂ))) (y : E),
 ids.length = n → (∀ i < n+1, i ≠ r → i ∈ ids) →
 (∀ k < n, k ≤ piv.getD k k ∧ piv.getD k k < n) →
 let X := ids.map (fun i => ((List.range n).map (fun j => (B.getD i []).getD (j+1) 0)) ++ [(B.getD i []).getD 0 0])
 let step : List (List (E → ℂ)) → ℕ → List (List (E → ℂ)) := fun X k =>
  let p := piv.getD k k
  let S := (X.set k (X.getD p [])).set p (X.getD k [])
  let row := S.getD k []
  let ip := (row.getD k 0)⁻¹
  S.mapIdx (fun i r => if k < i then
   let v := r.getD k 0 * ip
   r.mapIdx (fun j z => if k < j then z - v * row.getD j 0 else z) else r)
 let U := (List.range n).foldl step X
 let augmented := U ++ [B.getD r []]
 (∀ i < n, ((augmented.getD i []).getD i 0) y ≠ 0) →
 let back : List (List (E → ℂ)) → List (E → ℂ) := fun U =>
  (List.range n).reverse.foldl (fun v i =>
   let row := U.getD i []
   let t := (List.range n).foldl (fun t j => if i < j then t - row.getD j 0 * v.getD j 0 else t) (row.getD n 0)
   v.set i (t * (row.getD i 0)⁻¹)) (List.replicate n 0)
 let res : E → ℂ :=
  let row := augmented.getD n []
  (List.range n).foldl (fun z k => z - row.getD (k+1) 0 * (back (augmented.take n)).getD k 0) (row.getD 0 0)
 res y = 0 → ∃ v : ℕ → ℂ, ∀ i < n+1,
  (∑ j ∈ Finset.range n, ((B.getD i []).getD (j+1) 0) y * v j) = ((B.getD i []).getD 0 0) y
) := by
  classical
  intro E n r ids piv B y hids hcover hp X step U augmented hd back res hz
  let row : ℕ → List (E → ℂ) := fun i =>
    ((List.range n).map (fun j => (B.getD i []).getD (j+1) 0)) ++ [(B.getD i []).getD 0 0]
  have hX : X = ids.map row := rfl
  have hx : X.length = n := by simp [hX, hids]
  have hr : ∀ i < n, (X.getD i []).length = n+1 := by
    intro i hi
    simp [hX, row, List.getElem?_eq_getElem (show i < ids.length by omega)]
  have hslen : ∀ (st : List ℕ) (T : List (List (E → ℂ))), (st.foldl step T).length = T.length := by
    intro st
    induction st with
    | nil => intro T; rfl
    | cons k st ih =>
      intro T
      rw [List.foldl_cons, ih]
      simp [step]
  have hul : U.length = n := (hslen (List.range n) X).trans hx
  have hget (i : ℕ) (hi : i < n) : augmented.getD i [] = U.getD i [] := by
    simp only [augmented, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < U.length by omega)]
  have hlast : augmented.getD n [] = B.getD r [] := by
    simp [augmented, List.getElem?_append_right (show U.length ≤ n by omega), hul]
  have htake : augmented.take n = U := List.take_left' hul
  have hdn : ∀ i < n, ((U.getD i []).getD i 0) y ≠ 0 := by
    intro i hi
    simpa only [hget i hi] using hd i hi
  have hsolve := lu_backsolve_fun_correct E n piv X y hx hr hp hdn
  change (back U).length = n ∧ (∀ i < n, (∑ j ∈ Finset.range n, ((X.getD i []).getD j 0) y * ((back U).getD j 0) y) = ((X.getD i []).getD n 0) y) at hsolve
  have hrowj : ∀ i j, j < n → (row i).getD j 0 = (B.getD i []).getD (j+1) 0 := by
    intro i j hj
    simp [row, List.getElem?_append, hj, List.getElem?_range hj]
  have hrown : ∀ i, (row i).getD n 0 = (B.getD i []).getD 0 0 := by
    intro i
    simp [row, List.getElem?_append_right]
  have hfold : ∀ (f : ℕ → E → ℂ) (m : ℕ) (b : E → ℂ),
      ((List.range m).foldl (fun t j => t - f j) b) y = b y - ∑ j ∈ Finset.range m, f j y := by
    intro f m
    induction m with
    | zero => intro b; simp
    | succ m ih =>
      intro b
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Pi.sub_apply, ih, Finset.sum_range_succ]
      ring
  have hmiss : (∑ j ∈ Finset.range n, ((B.getD r []).getD (j+1) 0) y * ((back U).getD j 0) y) = ((B.getD r []).getD 0 0) y := by
    dsimp only [res] at hz
    rw [hlast, htake, hfold] at hz
    exact (sub_eq_zero.mp hz).symm
  refine ⟨fun j => ((back U).getD j 0) y, ?_⟩
  intro i hi
  by_cases hir : i = r
  · subst i
    exact hmiss
  · have hm : row i ∈ X := by
      rw [hX]
      exact List.mem_map.mpr ⟨i, hcover i hi hir, rfl⟩
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hm
    have hg : X.getD k [] = row i := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] using he
    have hh := hsolve.2 k (by omega)
    rw [hg, hrown] at hh
    calc
      _ = ∑ j ∈ Finset.range n, ((row i).getD j 0) y * ((back U).getD j 0) y := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hrowj i j (Finset.mem_range.mp hj)]
      _ = _ := hh

end Atiyah.Facts

/-! ### `Atiyah.Facts`: Newton -/

/-!
# A quantitative local-zero criterion

Banach fixed-point zero certificate for a preconditioned residual on a closed ball, in the form used
by the numerical certificate: centre residual and derivative-defect row sums.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- The exact fixed rational Schur preconditioner is an injective continuous linear map -/
theorem preconditioner_injective : (
let A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi ![
 (-1568197533577/(10^8):ℝ) • ContinuousLinearMap.proj 0 + (511635929049/(10^8):ℝ) • ContinuousLinearMap.proj 1,
 (-627448744629/(10^8):ℝ) • ContinuousLinearMap.proj 0 + (-448228210076/(10^8):ℝ) • ContinuousLinearMap.proj 1]
Function.Injective A
) := by
  intro A x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change (-1568197533577/(10^8):ℝ)*x 0 + (511635929049/(10^8):ℝ)*x 1 = (-1568197533577/(10^8):ℝ)*y 0 + (511635929049/(10^8):ℝ)*y 1 at h0
  change (-627448744629/(10^8):ℝ)*x 0 + (-448228210076/(10^8):ℝ)*x 1 = (-627448744629/(10^8):ℝ)*y 0 + (-448228210076/(10^8):ℝ)*y 1 at h1
  norm_num at h0 h1
  have hzero : x 0 = y 0 := by linarith
  have hone : x 1 = y 1 := by linarith
  ext i
  fin_cases i
  · exact hzero
  · exact hone

/-- Quantitative Banach zero certificate for an injectively preconditioned residual on a closed ball -/
theorem banach_zero_certificate : (
∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (F : E → E) (A : E →L[ℝ] E) (c : E) (r : ℝ) (K : NNReal), 0 ≤ r → K < 1 → Function.Injective A → ‖A (F c)‖ ≤ (1-(K:ℝ))*r → (∀ x ∈ Metric.closedBall c r, ∀ y ∈ Metric.closedBall c r, ‖(x-y)-A (F x-F y)‖ ≤ (K:ℝ)*‖x-y‖) → ∃ z ∈ Metric.closedBall c r, F z = 0
) := by
  intro E _ _ _ F A c r K hr hK hA hc hLip
  let T : E → E := fun x => x - A (F x)
  have hdiff (x y : E) : T x - T y = (x-y)-A (F x-F y) := by
    dsimp [T]
    rw [map_sub]
    abel
  have hdist (x : E) (hx : x ∈ Metric.closedBall c r) (y : E) (hy : y ∈ Metric.closedBall c r) :
      dist (T x) (T y) ≤ (K:ℝ)*dist x y := by
    simpa only [dist_eq_norm, hdiff] using hLip x hx y hy
  have hcc : c ∈ Metric.closedBall c r := by simpa using hr
  have hcent : dist (T c) c ≤ (1-(K:ℝ))*r := by
    have he : T c - c = -A (F c) := by dsimp [T]; abel
    simpa only [dist_eq_norm, he, norm_neg] using hc
  have hmap : Set.MapsTo T (Metric.closedBall c r) (Metric.closedBall c r) := by
    intro x hx
    apply Metric.mem_closedBall.mpr
    calc
      dist (T x) c ≤ dist (T x) (T c) + dist (T c) c := dist_triangle _ _ _
      _ ≤ (K:ℝ)*dist x c + (1-(K:ℝ))*r := add_le_add (hdist x hx c hcc) hcent
      _ ≤ (K:ℝ)*r + (1-(K:ℝ))*r := add_le_add (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hx) K.coe_nonneg) le_rfl
      _ = r := by ring
  have hcon : ContractingWith K (hmap.restrict T (Metric.closedBall c r) (Metric.closedBall c r)) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact hdist x.val x.property y.val y.property
  obtain ⟨z, hz, hfix, _⟩ := ContractingWith.exists_fixedPoint' Metric.isClosed_closedBall.isComplete hmap hcon hcc (edist_ne_top c (T c))
  refine ⟨z, hz, hA ?_⟩
  rw [map_zero]
  have he : z - A (F z) = z := hfix
  exact sub_eq_self.mp he

/-- An injectively preconditioned residual has a local zero if its center residual and derivative defect satisfy explicit closed-ball bounds -/
theorem local_zero_of_bounds : (
∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (F : E → E) (D : E → E →L[ℝ] E) (A : E →L[ℝ] E) (c : E) (r : ℝ) (K : NNReal), 0 ≤ r → K < 1 → Function.Injective A → ‖A (F c)‖ ≤ (1-(K:ℝ))*r → (∀ x ∈ Metric.closedBall c r, HasFDerivAt F (D x) x) → (∀ x ∈ Metric.closedBall c r, ‖ContinuousLinearMap.id ℝ E - A.comp (D x)‖ ≤ (K:ℝ)) → ∃ z ∈ Metric.closedBall c r, F z = 0
) := by
  intro E _ _ _ F D A c r K hr hK hA hc hd hb
  apply banach_zero_certificate F A c r K hr hK hA hc
  let T : E → E := fun x => x - A (F x)
  have hder : ∀ x ∈ Metric.closedBall c r, HasFDerivWithinAt T (ContinuousLinearMap.id ℝ E - A.comp (D x)) (Metric.closedBall c r) x := by
    intro x hx
    exact ((hasFDerivAt_id x).sub (A.hasFDerivAt.comp x (hd x hx))).hasFDerivWithinAt
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hb (convex_closedBall c r) hy hx
  have he : T x - T y = (x-y)-A (F x-F y) := by dsimp [T]; rw [map_sub]; abel
  rwa [he] at h

/-- Two coordinate-direction row sums bound the Fin 2 sup operator norm -/
theorem fin2_sup_norm_bound : (
∀ (L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (c : ℝ), 0 ≤ c → (∀ i, |L (Pi.single 0 1) i| + |L (Pi.single 1 1) i| ≤ c) → ‖L‖ ≤ c
) := by
  intro L c hc h
  apply L.opNorm_le_bound hc
  intro x
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg x))).mpr
  intro i
  have hx : x = x 0 • (Pi.single 0 1 : Fin 2 → ℝ) + x 1 • Pi.single 1 1 := by
   ext j
   fin_cases j <;> simp
  have he : L x i = x 0 * L (Pi.single 0 1) i + x 1 * L (Pi.single 1 1) i := by
   conv_lhs => rw [hx]
   simp
  rw [Real.norm_eq_abs, he]
  calc
   |x 0 * L (Pi.single 0 1) i + x 1 * L (Pi.single 1 1) i| ≤ |x 0 * L (Pi.single 0 1) i| + |x 1 * L (Pi.single 1 1) i| := abs_add_le _ _
   _ = |x 0| * |L (Pi.single 0 1) i| + |x 1| * |L (Pi.single 1 1) i| := by rw [abs_mul, abs_mul]
   _ ≤ ‖x‖ * |L (Pi.single 0 1) i| + ‖x‖ * |L (Pi.single 1 1) i| := add_le_add (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x 0) (abs_nonneg _)) (mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x 1) (abs_nonneg _))
   _ = (|L (Pi.single 0 1) i| + |L (Pi.single 1 1) i|) * ‖x‖ := by ring
   _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)

/-- Fin 2 coordinate center and derivative row-sum half-contraction bounds imply an exact local zero -/
theorem local_zero_of_row_sums : (
∀ (F : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (r : ℝ), 0 ≤ r → Function.Injective A →
(∀ i, |A (F 0) i| ≤ r/2) →
(∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) r, ∃ D : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ), HasFDerivAt F D x ∧
 ∀ i, |(ContinuousLinearMap.id ℝ (Fin 2 → ℝ) - A.comp D) (Pi.single 0 1) i| + |(ContinuousLinearMap.id ℝ (Fin 2 → ℝ) - A.comp D) (Pi.single 1 1) i| ≤ 1/2) →
∃ z ∈ Metric.closedBall (0 : Fin 2 → ℝ) r, F z = 0
) := by
  classical
  intro F A r hr hA hc hd
  let D : (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := fun x => if h : x ∈ Metric.closedBall (0 : Fin 2 → ℝ) r then (hd x h).choose else 0
  have hD (x : Fin 2 → ℝ) (hx : x ∈ Metric.closedBall (0 : Fin 2 → ℝ) r) : HasFDerivAt F (D x) x ∧ ∀ i, |(ContinuousLinearMap.id ℝ (Fin 2 → ℝ) - A.comp (D x)) (Pi.single 0 1) i| + |(ContinuousLinearMap.id ℝ (Fin 2 → ℝ) - A.comp (D x)) (Pi.single 1 1) i| ≤ 1/2 := by
   simpa only [D, dif_pos hx] using (hd x hx).choose_spec
  apply local_zero_of_bounds F D A 0 r (1/2 : NNReal) hr (by norm_num) hA
  · have hnorm : ‖A (F 0)‖ ≤ r/2 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => by simpa only [Real.norm_eq_abs] using hc i)
    norm_num at ⊢
    linarith
  · exact fun x hx => (hD x hx).1
  · intro x hx
    apply fin2_sup_norm_bound
    · norm_num
    · simpa using (hD x hx).2

/-- The exact final flagged postprocessing turns sound residual/AD enclosures into a radius 10^-40 zero -/
theorem postprocessing_yields_zero : (
∀ (s : ℤ), 0 < s →
let I := ℤ × ℤ × Bool
let D := I × Option (I × I)
let E := Fin 2 → ℝ
let R : I → ℝ → Prop := fun a v => a.2.2 = true → (a.1:ℝ)/(s:ℝ) ≤ v ∧ v ≤ (a.2.1:ℝ)/(s:ℝ)
let O : Option (I × I) → (E →L[ℝ] ℝ) → Prop := fun a d => match a with
 | none => d = 0 | some p => R p.1 (d (Pi.single 0 1)) ∧ R p.2 (d (Pi.single 1 1))
let J : E → D → (E → ℝ) → Prop := fun x a f => a.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ R a.1 (f x) ∧ O a.2 d
let q : ℤ → ℤ → I := fun a b => (a*s/b,-((-a*s)/b),decide (0<b))
let ia : I → I → I := fun x y => (x.1+y.1,x.2.1+y.2.1,x.2.2 && y.2.2)
let ine : I → I := fun x => (-x.2.1,-x.1,x.2.2)
let im : I → I → I := fun x y => (min (min (x.1*y.1) (x.1*y.2.1)) (min (x.2.1*y.1) (x.2.1*y.2.1))/s,-((-max (max (x.1*y.1) (x.1*y.2.1)) (max (x.2.1*y.1) (x.2.1*y.2.1)))/s),x.2.2 && y.2.2)
let iz := q 0 1
let io := q 1 1
let pre : ℕ → ℕ → I := fun i j => q (if i = 0 then (if j = 0 then -1568197533577 else 511635929049) else (if j = 0 then -627448744629 else -448228210076)) (10^8)
let der := fun (d : D) => d.2.getD (iz,iz)
let ab := fun (x : I) => max |x.1| |x.2.1|
∀ (F : E → E) (cen bx : D × D),
(R cen.1.1 (F 0 0) ∧ R cen.2.1 (F 0 1)) →
(∀ x ∈ Metric.closedBall (0:E) (1/(10^40:ℝ)), J x bx.1 (fun y => F y 0) ∧ J x bx.2 (fun y => F y 1)) →
let c0 := ia (im (pre 0 0) cen.1.1) (im (pre 0 1) cen.2.1)
let c1 := ia (im (pre 1 0) cen.1.1) (im (pre 1 1) cen.2.1)
let e00 := ia io (ine (ia (im (pre 0 0) (der bx.1).1) (im (pre 0 1) (der bx.2).1)))
let e01 := ine (ia (im (pre 0 0) (der bx.1).2) (im (pre 0 1) (der bx.2).2))
let e10 := ine (ia (im (pre 1 0) (der bx.1).1) (im (pre 1 1) (der bx.2).1))
let e11 := ia io (ine (ia (im (pre 1 0) (der bx.1).2) (im (pre 1 1) (der bx.2).2)))
(bx.1.1.2.2 && bx.2.1.2.2 && c0.2.2 && c1.2.2 && e00.2.2 && e01.2.2 && e10.2.2 && e11.2.2 && decide (2 * (max (ab c0) (ab c1)) * 10^40 ≤ s ∧ 2 * (ab e00 + ab e01) ≤ s ∧ 2 * (ab e10 + ab e11) ≤ s)) = true →
∃ z ∈ Metric.closedBall (0:E) (1/(10^40:ℝ)), F z = 0
) := by
  intro s hs I D E R O J q ia ine im iz io pre der ab F cen bx hcen hbox c0 c1 e00 e01 e10 e11 hcert
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have flags : bx.1.1.2.2 = true ∧ bx.2.1.2.2 = true ∧ c0.2.2 = true ∧ c1.2.2 = true ∧ e00.2.2 = true ∧ e01.2.2 = true ∧ e10.2.2 = true ∧ e11.2.2 = true ∧ (2 * max (ab c0) (ab c1) * 10^40 ≤ s ∧ 2*(ab e00+ab e01) ≤ s ∧ 2*(ab e10+ab e11) ≤ s) := by
   simpa [and_assoc] using hcert
  rcases flags with ⟨fb0,fb1,fc0,fc1,fe00,fe01,fe10,fe11,hcenter,he0,he1⟩
  obtain ⟨hq,ha,hn,hm,-,-⟩ := fixed_primitives_sound s hs
  let N : ℕ → ℕ → ℤ := fun i j => if i=0 then (if j=0 then -1568197533577 else 511635929049) else (if j=0 then -627448744629 else -448228210076)
  let P : ℕ → ℕ → ℝ := fun i j => (N i j:ℝ)/(10^8:ℝ)
  have hp (i j : ℕ) : R (pre i j) (P i j) := by
   have hh : R (pre i j) ((N i j:ℝ)/((10^8:ℤ):ℝ)) := hq (N i j) (10^8)
   simpa only [P,Int.cast_pow,Int.cast_ofNat] using hh
  have rz : R iz 0 := by simpa only [iz,Int.cast_zero,Int.cast_one,zero_div] using hq 0 1
  have ro : R io 1 := by simpa only [io,Int.cast_one,div_one] using hq 1 1
  have lin (i : ℕ) (a b : I) (u v : ℝ) (hu : R a u) (hv : R b v) : R (ia (im (pre i 0) a) (im (pre i 1) b)) (P i 0*u+P i 1*v) := ha _ _ _ _ (hm _ _ _ _ (hp i 0) hu) (hm _ _ _ _ (hp i 1) hv)
  have absb (a : I) (u : ℝ) (hu : R a u) (ha : a.2.2 = true) : |u| ≤ (ab a:ℝ)/(s:ℝ) := by
   obtain ⟨hl,hh⟩ := hu ha
   have hlow : -ab a ≤ a.1 := le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _)
   have hhigh : a.2.1 ≤ ab a := le_trans (le_abs_self _) (le_max_right _ _)
   have hl' : -(ab a:ℝ) ≤ (a.1:ℝ) := by exact_mod_cast hlow
   have hh' : (a.2.1:ℝ) ≤ (ab a:ℝ) := by exact_mod_cast hhigh
   apply abs_le.mpr
   constructor
   · have := (div_le_div_of_nonneg_right hl' hs'.le).trans hl
     simpa only [neg_div] using this
   · exact hh.trans (div_le_div_of_nonneg_right hh' hs'.le)
  have rowb (a b : I) (u v : ℝ) (hu : R a u) (hv : R b v) (fa : a.2.2 = true) (fb : b.2.2 = true) (hb : 2*(ab a+ab b) ≤ s) : |u|+|v| ≤ (1/2:ℝ) := by
   have ht : (2:ℝ)*((ab a:ℝ)+(ab b:ℝ)) ≤ (s:ℝ) := by exact_mod_cast hb
   have hh := add_le_add (absb a u hu fa) (absb b v hv fb)
   apply hh.trans
   rw [← add_div]
   apply (div_le_iff₀ hs').mpr
   linarith
  have cenb (a : I) (u : ℝ) (hu : R a u) (fa : a.2.2 = true) (hb : ab a ≤ max (ab c0) (ab c1)) : |u| ≤ (1/(10^40:ℝ))/2 := by
   have ht : (2:ℝ)*(max (ab c0) (ab c1):ℤ)*(10:ℝ)^40 ≤ (s:ℝ) := by exact_mod_cast hcenter
   have hb' : (ab a:ℝ) ≤ max (ab c0:ℝ) (ab c1:ℝ) := by exact_mod_cast hb
   apply (absb a u hu fa).trans
   apply (div_le_iff₀ hs').mpr
   norm_num at ht ⊢
   linarith
  let A : E →L[ℝ] E := ContinuousLinearMap.pi ![P 0 0 • ContinuousLinearMap.proj 0 + P 0 1 • ContinuousLinearMap.proj 1, P 1 0 • ContinuousLinearMap.proj 0 + P 1 1 • ContinuousLinearMap.proj 1]
  have hA : Function.Injective A := by
   convert preconditioner_injective using 1 <;> norm_num [A,P,N] <;> rfl
  apply local_zero_of_row_sums F A (1/(10^40:ℝ)) (by positivity) hA
  · intro i
    fin_cases i
    · exact cenb c0 _ (lin 0 _ _ _ _ hcen.1 hcen.2) fc0 (le_max_left _ _)
    · exact cenb c1 _ (lin 1 _ _ _ _ hcen.1 hcen.2) fc1 (le_max_right _ _)
  · intro x hx
    obtain ⟨d0,hd0,hv0,ho0⟩ := (hbox x hx).1 fb0
    obtain ⟨d1,hd1,hv1,ho1⟩ := (hbox x hx).2 fb1
    have hd (a : D) (d : E →L[ℝ] ℝ) (h : O a.2 d) : R (der a).1 (d (Pi.single 0 1)) ∧ R (der a).2 (d (Pi.single 1 1)) := by
     cases he : a.2 with
     | none =>
       have hz : d = 0 := by simpa only [O,he] using h
       subst d
       simpa [der,he] using And.intro rz rz
     | some p => simpa only [O,der,he,Option.getD_some] using h
    obtain ⟨r00,r01⟩ := hd bx.1 d0 ho0
    obtain ⟨r10,r11⟩ := hd bx.2 d1 ho1
    let DD : E →L[ℝ] E := ContinuousLinearMap.pi ![d0,d1]
    have hf : HasFDerivAt F DD x := by
     apply hasFDerivAt_pi.mpr
     intro i
     fin_cases i
     · exact hd0
     · exact hd1
    refine ⟨DD,hf,?_⟩
    have rE00 : R e00 (1 + -(P 0 0*d0 (Pi.single 0 1)+P 0 1*d1 (Pi.single 0 1))) := ha _ _ _ _ ro (hn _ _ (lin 0 _ _ _ _ r00 r10))
    have rE01 : R e01 (-(P 0 0*d0 (Pi.single 1 1)+P 0 1*d1 (Pi.single 1 1))) := hn _ _ (lin 0 _ _ _ _ r01 r11)
    have rE10 : R e10 (-(P 1 0*d0 (Pi.single 0 1)+P 1 1*d1 (Pi.single 0 1))) := hn _ _ (lin 1 _ _ _ _ r00 r10)
    have rE11 : R e11 (1 + -(P 1 0*d0 (Pi.single 1 1)+P 1 1*d1 (Pi.single 1 1))) := ha _ _ _ _ ro (hn _ _ (lin 1 _ _ _ _ r01 r11))
    intro i
    fin_cases i
    · simpa [A,DD,sub_eq_add_neg] using rowb e00 e01 _ _ rE00 rE01 fe00 fe01 he0
    · simpa [A,DD,sub_eq_add_neg] using rowb e10 e11 _ _ rE10 rE11 fe10 fe11 he1

end Atiyah.Facts

/-! ### `Atiyah.Facts`: Assembly -/

/-!
# From the certified block to the counterexample

Identification of the certified block with the even coefficients of the actual 45-factor point polynomials
and the transfer of its column dependence to the pinned point polynomials.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Facts

/-- The constant factors followed by moving indices 17 and 40 permute the full deleted 46-point list -/
theorem moving_index_permutation : (
∀ i : Fin 23, i.val ≠ 17 → (((List.range 46).filter (fun j => j != i.val && j != 17 && j != 40)) ++ [17,40]).Perm ((List.range 46).filter (fun j => j != i.val))
) := by
  decide +kernel

/-- The exact split-row block equals scaled even coefficients of full updated 45-factor polynomial products -/
theorem split_rows_are_even_coefficients : (
∀ (E Q : Type) [Zero Q]
 (fb : Q → Q → (E → ℂ) × (E → ℝ)) (qts qts' : List Q)
 (hfix : ∀ j < 46, j ≠ 17 → j ≠ 40 → qts'.getD j 0 = qts.getD j 0)
 (re ce : List ℕ),
 let tb : List (E → ℂ) → ((E → ℂ) × (E → ℝ)) → List (E → ℂ) := fun p f => List.zipWith (fun (a b : E → ℂ) y => a y-b y) ((p.map (fun a y => f.1 y*a y)) ++ [fun _ => 0]) ((fun _ => 0) :: p.map (fun a y => a y*(f.2 y:ℂ)))
 let Cb := (List.range 23).map (fun i => if i = 17 then [fun _ => (1:ℂ)] else ((List.range 46).filter (fun j => j != i && j != 17 && j != 40)).foldl (fun p j => tb p (fb (qts.getD i 0) (qts.getD j 0))) [fun _ => 1])
 let B := (List.range 23).map (fun i =>
  let js := if i = 17 then (List.range 46).filter (fun j => j != i) else [17,40]
  let p := js.foldl (fun p j => tb p (fb (qts'.getD i 0) (qts'.getD j 0))) (Cb.getD i [fun _ => 1])
  (List.range 23).map (fun k => fun y => (p.getD (2*k) (fun _ => 0) y) * ((1/(2:ℝ)^(ce.getD k 0)):ℂ) * ((1/(2:ℝ)^(re.getD i 0)):ℂ)))
 ∀ i < 23, ∀ k < 23, ∀ y : E,
 ((B.getD i []).getD k (fun _ => 0)) y =
 ((((List.range 46).filter (fun j => j != i)).map (fun j =>
  let f := fb (qts'.getD i 0) (qts'.getD j 0)
  Polynomial.C (f.1 y) - Polynomial.C ((f.2 y:ℝ):ℂ)*Polynomial.X)).prod).coeff (2*k) * ((1/(2:ℝ)^(ce.getD k 0)):ℂ) * ((1/(2:ℝ)^(re.getD i 0)):ℂ)
) := by
  classical
  intro E Q _ fb qts qts' hfix re ce tb Cb B i hi k hk y
  have hcoeff (ls : List ℕ) :
   ((ls.foldl (fun p j => tb p (fb (qts'.getD i 0) (qts'.getD j 0))) [fun _ => 1]).getD (2*k) (fun _ => 0)) y =
   ((ls.map (fun j => let f := fb (qts'.getD i 0) (qts'.getD j 0); Polynomial.C (f.1 y) - Polynomial.C ((f.2 y:ℝ):ℂ)*Polynomial.X)).prod).coeff (2*k) := by
   simpa using coeff_fold_product_fun E ℕ ls (fun j => fb (qts'.getD i 0) (qts'.getD j 0)) [fun _ => 1] y (2*k)
  have hget : Cb.getD i [fun _ => 1] = if i = 17 then [fun _ => 1] else ((List.range 46).filter (fun j => j != i && j != 17 && j != 40)).foldl (fun p j => tb p (fb (qts.getD i 0) (qts.getD j 0))) [fun _ => 1] := by
   simp [Cb, List.getD, hi]
  have getmap {T : Type} (n : ℕ) (f : ℕ → T) (d : T) (i : ℕ) (hi : i < n) : ((List.range n).map f).getD i d = f i := by
   simp [List.getD, hi]
  dsimp only [B]
  rw [getmap 23 _ [] i hi, getmap 23 _ (fun _ => 0) k hk, hget]
  by_cases hn : i = 17
  · simp only [if_pos hn]
    rw [hcoeff]
  · simp only [if_neg hn]
    have hself : qts'.getD i 0 = qts.getD i 0 := hfix i (by omega) hn (by omega)
    have hfold (ls : List ℕ) (hl : ∀ j ∈ ls, j < 46 ∧ j ≠ 17 ∧ j ≠ 40) (p : List (E → ℂ)) :
     ls.foldl (fun p j => tb p (fb (qts.getD i 0) (qts.getD j 0))) p = ls.foldl (fun p j => tb p (fb (qts'.getD i 0) (qts'.getD j 0))) p := by
     induction ls generalizing p with
     | nil => rfl
     | cons j ls ih =>
       obtain ⟨hj,h17,h40⟩ := hl j (by simp)
       simp only [List.foldl_cons]
       have he : tb p (fb (qts.getD i 0) (qts.getD j 0)) = tb p (fb (qts'.getD i 0) (qts'.getD j 0)) := by rw [hself, hfix j hj h17 h40]
       rw [he]
       exact ih (fun t ht => hl t (by simp [ht])) _
    rw [hfold _ (by
     intro j hj
     simp only [List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne] at hj
     exact ⟨hj.1, hj.2.1.2, hj.2.2⟩)]
    rw [← List.foldl_append, hcoeff]
    have hp : (((List.range 46).filter (fun j => j != i && j != 17 && j != 40)) ++ [17,40]).Perm ((List.range 46).filter (fun j => j != i)) := by
     exact moving_index_permutation ⟨i,hi⟩ hn
    rw [(hp.map _).prod_eq]

/-- The exact 17/40 list updates preserve half-turn pairing and odd heights and leave all other entries fixed -/
theorem moving_updates_preserve_half_turn : (
∀ (x : Fin 23 × Fin 2 → EuclideanSpace ℝ (Fin 3)) (b : ℝ),
 (∀ i : Fin 23, x (i,1) = WithLp.toLp 2 ![-x (i,0) 0,-x (i,0) 1,x (i,0) 2]) →
 (∀ i : Fin 23, x (i,0) 1 = (2*(i.val:ℝ)+1)*b) →
 let E := Fin 2 → ℝ
 let qs := List.ofFn (fun i : Fin 23 => x (i,0)) ++ List.ofFn (fun i : Fin 23 => x (i,1))
 let qts : List (E → EuclideanSpace ℝ (Fin 3)) := qs.map (fun p => fun _ => p)
 let oldq := qts.getD 17 (fun _ => 0)
 let newq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![oldq y 0+y 0,oldq y 1,oldq y 2+y 1]
 let mateq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![-newq y 0,-newq y 1,newq y 2]
 let qts' := (qts.set 17 newq).set 40 mateq
 (∀ j < 46, j ≠ 17 → j ≠ 40 → qts'.getD j (fun _ => 0) = qts.getD j (fun _ => 0)) ∧
 ∀ y : E, let X : Fin 46 → EuclideanSpace ℝ (Fin 3) := fun i => (qts'.getD i.val (fun _ => 0)) y
 (∀ i : Fin 23, X ⟨i.val+23,by omega⟩ = WithLp.toLp 2 ![-X ⟨i.val,by omega⟩ 0,-X ⟨i.val,by omega⟩ 1,X ⟨i.val,by omega⟩ 2]) ∧
 (∀ i : Fin 23, X ⟨i.val,by omega⟩ 1 = (2*(i.val:ℝ)+1)*b)
) := by
  classical
  intro x b hm hh E qs qts oldq newq mateq qts'
  have hlen : qts.length = 46 := by simp [qts,qs]
  have hget (j : ℕ) (hj : j < 46) : qts'.getD j (fun _ => 0) = if j = 40 then mateq else if j = 17 then newq else qts.getD j (fun _ => 0) := by
   by_cases h40 : j = 40
   · subst j
     simp [qts',List.getD,List.getElem?_set,hlen]
   · by_cases h17 : j = 17
     · subst j
       simp [qts',List.getD,List.getElem?_set,hlen]
     · simp [qts',List.getD,List.getElem?_set,hlen,hj,h40,h17,Ne.symm h40,Ne.symm h17]
  have hpos (i : Fin 23) (y : E) : (qts.getD i.val (fun _ => 0)) y = x (i,0) := by
   simp only [qts,qs,List.getD,List.getElem?_map,List.getElem?_append,List.length_ofFn,if_pos i.isLt,List.getElem?_ofFn,dif_pos i.isLt,Option.map_some,Option.getD_some]
  have hneg (i : Fin 23) (y : E) : (qts.getD (i.val+23) (fun _ => 0)) y = x (i,1) := by
   simp only [qts,qs,List.getD,List.getElem?_map,List.getElem?_append,List.length_ofFn,if_neg (show ¬i.val+23 < 23 by omega),Nat.add_sub_cancel,List.getElem?_ofFn,dif_pos i.isLt,Option.map_some,Option.getD_some]
  refine ⟨?_,?_⟩
  · intro j hj h17 h40
    rw [hget j hj,if_neg h40,if_neg h17]
  · intro y X
    have hp (i : Fin 23) : X ⟨i.val,by omega⟩ = if i.val = 17 then newq y else x (i,0) := by
     change (qts'.getD i.val (fun _ => 0)) y = _
     rw [hget _ (by omega),if_neg (by omega)]
     split_ifs <;> simp [hpos]
    have hn (i : Fin 23) : X ⟨i.val+23,by omega⟩ = if i.val = 17 then mateq y else x (i,1) := by
     change (qts'.getD (i.val+23) (fun _ => 0)) y = _
     rw [hget _ (by omega)]
     by_cases hi : i.val = 17
     · simp [hi]
     · simp [show i.val+23 ≠ 40 by omega,show i.val+23 ≠ 17 by omega,hi,hneg]
    constructor
    · intro i
      rw [hp,hn]
      by_cases hi : i.val = 17
      · simp only [if_pos hi]
        rfl
      · simp only [if_neg hi]
        exact hm i
    · intro i
      rw [hp]
      by_cases hi : i.val = 17
      · rw [if_pos hi]
        change oldq y 1 = _
        have ho := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) (hpos (17:Fin 23) y)
        change oldq y 1 = x (17,0) 1 at ho
        rw [ho,hh]
        simp [hi]
      · rw [if_neg hi,hh]

/-- Deleted-index range-list products equal erased finite-index products -/
theorem deleted_range_product : (
∀ {R : Type} [CommMonoid R] (n : ℕ) (i : Fin n) (f : ℕ → R), (((List.range n).filter (fun j => j != i.val)).map f).prod = ∏ j ∈ Finset.univ.erase i, f j.val
) := by
  classical
  intro R _ n i f
  rw [← List.prod_toFinset f (List.nodup_range.filter _)]
  symm
  apply Finset.prod_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    simp [List.mem_toFinset, j.isLt, show j.val ≠ i.val from fun h => hj (Fin.ext h)]
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro j hj
    have hj' : j < n ∧ j ≠ i.val := by simpa using hj
    refine ⟨⟨j,hj'.1⟩,?_,rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    exact hj'.2 (congrArg Fin.val h)
  · intro j hj
    rfl

/-- The exact split geometric B column dependence yields an injective counterexample to pinned point-polynomial independence -/
theorem block_dependence_counterexample : (
∀ (x : Fin 23 × Fin 2 → EuclideanSpace ℝ (Fin 3)) (b : ℝ), 0 < b →
 (∀ i : Fin 23, x (i,1) = WithLp.toLp 2 ![-x (i,0) 0,-x (i,0) 1,x (i,0) 2]) →
 (∀ i : Fin 23, x (i,0) 1 = (2*(i.val:ℝ)+1)*b) →
 ∀ (re ce : List ℕ), ce.getD 0 0 = 0 →
 let E := Fin 2 → ℝ
 let qs := List.ofFn (fun i : Fin 23 => x (i,0)) ++ List.ofFn (fun i : Fin 23 => x (i,1))
 let qts : List (E → EuclideanSpace ℝ (Fin 3)) := qs.map (fun p => fun _ => p)
 let fb : (E → EuclideanSpace ℝ (Fin 3)) → (E → EuclideanSpace ℝ (Fin 3)) → (E → ℂ) × (E → ℝ) := fun p q => ((fun y => (((q y-p y) 0:ℝ):ℂ)+(((q y-p y) 1:ℝ):ℂ)*Complex.I),(fun y => ‖q y-p y‖-(q y-p y) 2))
 let tb : List (E → ℂ) → ((E → ℂ) × (E → ℝ)) → List (E → ℂ) := fun p f => List.zipWith (fun (a b : E → ℂ) y => a y-b y) ((p.map (fun a y => f.1 y*a y)) ++ [fun _ => 0]) ((fun _ => 0) :: p.map (fun a y => a y*(f.2 y:ℂ)))
 let Cb := (List.range 23).map (fun i => if i = 17 then [fun _ => (1:ℂ)] else ((List.range 46).filter (fun j => j != i && j != 17 && j != 40)).foldl (fun p j => tb p (fb (qts.getD i (fun _ => 0)) (qts.getD j (fun _ => 0)))) [fun _ => 1])
 let oldq := qts.getD 17 (fun _ => 0)
 let newq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![oldq y 0+y 0,oldq y 1,oldq y 2+y 1]
 let mateq : E → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![-newq y 0,-newq y 1,newq y 2]
 let qts' := (qts.set 17 newq).set 40 mateq
 let B := (List.range 23).map (fun i =>
  let js := if i = 17 then (List.range 46).filter (fun j => j != i) else [17,40]
  let p := js.foldl (fun p j => tb p (fb (qts'.getD i (fun _ => 0)) (qts'.getD j (fun _ => 0)))) (Cb.getD i [fun _ => 1])
  (List.range 23).map (fun k => fun y => (p.getD (2*k) (fun _ => 0) y) * ((1/(2:ℝ)^(ce.getD k 0)):ℂ) * ((1/(2:ℝ)^(re.getD i 0)):ℂ)))
 ∀ (y : E) (v : ℕ → ℂ),
 (∀ i < 23, (∑ j ∈ Finset.range 22, ((B.getD i []).getD (j+1) (fun _ => 0)) y * v j) = ((B.getD i []).getD 0 (fun _ => 0)) y) →
 let X : Fin 46 → EuclideanSpace ℝ (Fin 3) := fun i => (qts'.getD i.val (fun _ => 0)) y
 Function.Injective X ∧ ¬ LinearIndependent ℂ (fun i : Fin 46 => ∏ j ∈ Finset.univ.erase i,
  let d := X j-X i
  let L : ℂ × ℂ := if ‖d‖-d 2 = 0 then (1,0) else (((d 0:ℂ)+(d 1:ℂ)*Complex.I)/(‖d‖-d 2:ℝ),1)
  MvPolynomial.C L.1*MvPolynomial.X (0 : Fin 2)-MvPolynomial.C L.2*MvPolynomial.X 1)
) := by
  classical
  intro x b hb hm hh re ce hce E qs qts fb tb Cb oldq newq mateq qts' B y v hv X
  have hg := moving_updates_preserve_half_turn x b hm hh
  have hfix : ∀ j < 46, j ≠ 17 → j ≠ 40 → qts'.getD j (fun _ => 0) = qts.getD j (fun _ => 0) := hg.1
  have hgeom := hg.2 y
  change (∀ i : Fin 23, X ⟨i.val+23,by omega⟩ = WithLp.toLp 2 ![-X ⟨i.val,by omega⟩ 0,-X ⟨i.val,by omega⟩ 1,X ⟨i.val,by omega⟩ 2]) ∧ (∀ i : Fin 23, X ⟨i.val,by omega⟩ 1 = (2*(i.val:ℝ)+1)*b) at hgeom
  have hc := split_rows_are_even_coefficients E (E → EuclideanSpace ℝ (Fin 3)) fb qts qts' hfix re ce
  let P : Fin 46 → Polynomial ℂ := fun i => ∏ j ∈ Finset.univ.erase i, (Polynomial.C (((X j-X i) 0:ℂ)+((X j-X i) 1:ℂ)*Complex.I)-Polynomial.C ((‖X j-X i‖-(X j-X i) 2:ℝ):ℂ)*Polynomial.X)
  let cs : ℕ → ℂ := fun k => ((1/(2:ℝ)^(ce.getD k 0)):ℂ)
  let rs : ℕ → ℂ := fun i => ((1/(2:ℝ)^(re.getD i 0)):ℂ)
  have hc' (i k : Fin 23) : ((B.getD i.val []).getD k.val (fun _ => 0)) y = (P ⟨i.val,by omega⟩).coeff (2*k.val)*cs k.val*rs i.val := by
   have h := hc i.val i.isLt k.val k.isLt y
   let f : ℕ → Polynomial ℂ := fun j => let a := fb (qts'.getD i.val (fun _ => 0)) (qts'.getD j (fun _ => 0)); Polynomial.C (a.1 y)-Polynomial.C ((a.2 y:ℝ):ℂ)*Polynomial.X
   have hl := deleted_range_product 46 ⟨i.val,by omega⟩ f
   change (((List.range 46).filter (fun j => j != i.val)).map f).prod = P ⟨i.val,by omega⟩ at hl
   change ((B.getD i.val []).getD k.val (fun _ => 0)) y = ((((List.range 46).filter (fun j => j != i.val)).map f).prod).coeff (2*k.val)*cs k.val*rs i.val at h
   rw [hl] at h
   exact h
  clear_value B
  have hfinal := half_turn_counterexample_interface X b hb hgeom.1 hgeom.2
  apply hfinal
  let w : Fin 22 → ℂ := fun j => cs (j.val+1)*v j.val
  refine ⟨w,?_⟩
  intro i
  change (∑ j : Fin 22, (P ⟨i.val,by omega⟩).coeff (2*(j.val+1))*w j) = (P ⟨i.val,by omega⟩).coeff 0
  have hrs : rs i.val ≠ 0 := by simp [rs]
  apply mul_right_cancel₀ hrs
  calc
   (∑ j : Fin 22, (P ⟨i.val,by omega⟩).coeff (2*(j.val+1))*w j)*rs i.val = ∑ j : Fin 22, (P ⟨i.val,by omega⟩).coeff (2*(j.val+1))*cs (j.val+1)*rs i.val*v j.val := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [w]
    ring
   _ = ∑ j : Fin 22, ((B.getD i.val []).getD (j.val+1) (fun _ => 0)) y*v j.val := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc' i ⟨j.val+1,by omega⟩]
   _ = ((B.getD i.val []).getD 0 (fun _ => 0)) y := by
    exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => ((B.getD i.val []).getD (j+1) (fun _ => 0)) y*v j) 22).trans (hv i.val i.isLt)
   _ = (P ⟨i.val,by omega⟩).coeff 0 * rs i.val := by
    have hcs : cs 0 = 1 := by dsimp only [cs]; rw [hce]; norm_num
    simpa only [Fin.val_zero,mul_zero,hcs,mul_one] using hc' i (0:Fin 23)

end Atiyah.Facts

/-! ## The certificate layer -/

/-! ### `Atiyah`: Fixed -/

/-!
# Fixed-point interval arithmetic

Numbers are represented at a global integer scale `s`: the integer `n` stands for the real `n / s`.
An interval is a pair of integer endpoints together with a validity flag; every operation rounds
outward, and an operation whose domain condition cannot be certified clears the flag.

The enclosure lemmas are the soundness of this arithmetic: whenever the inputs enclose real numbers,
the output encloses the corresponding real result (and a valid inverse or square root certifies that
its argument was positive).
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Fixed

/-- A fixed-point interval: lower numerator, upper numerator, validity flag. -/
abbrev Ival := ℤ × ℤ × Bool

instance : DecidableEq Ival := inferInstance

variable (s : ℤ)

/-- The rational `a / b` rounded outward (invalid when `b ≤ 0`). -/
def ofRat (a b : ℤ) : Ival := (a * s / b, -((-a * s) / b), decide (0 < b))

def add (a b : Ival) : Ival := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 && b.2.2)

def neg (a : Ival) : Ival := (-a.2.1, -a.1, a.2.2)

def sub (a b : Ival) : Ival := add a (neg b)

def mul (a b : Ival) : Ival :=
  (min (min (a.1 * b.1) (a.1 * b.2.1)) (min (a.2.1 * b.1) (a.2.1 * b.2.1)) / s,
   -((-max (max (a.1 * b.1) (a.1 * b.2.1)) (max (a.2.1 * b.1) (a.2.1 * b.2.1))) / s),
   a.2.2 && b.2.2)

/-- Reciprocal; valid only when the interval is certified positive. -/
def inv (a : Ival) : Ival :=
  (s * s / a.2.1, -((-(s * s)) / a.1), a.2.2 && decide (0 < a.1 ∧ a.1 ≤ a.2.1))

/-- Square root by integer square roots of the scaled endpoints, certified by integer squares. -/
def sqrt (a : Ival) : Ival :=
  let l : ℤ := Nat.sqrt (a.1 * s).toNat
  let u : ℤ := (Nat.sqrt (a.2.1 * s).toNat : ℤ) + 1
  (l, u, a.2.2 && decide (0 < a.1 ∧ 0 ≤ l ∧ 0 ≤ u ∧ l * l ≤ a.1 * s ∧ a.2.1 * s ≤ u * u))

/-- The real number `x` lies in the interval `a` whenever `a` is valid. -/
def Encloses (a : Ival) (x : ℝ) : Prop :=
  a.2.2 = true → (a.1 : ℝ) / (s : ℝ) ≤ x ∧ x ≤ (a.2.1 : ℝ) / (s : ℝ)

variable {s}

theorem encloses_ofRat (hs : 0 < s) (a b : ℤ) : Encloses s (ofRat s a b) ((a : ℝ) / (b : ℝ)) :=
  (Atiyah.Facts.fixed_primitives_sound s hs).1 a b

theorem encloses_add (hs : 0 < s) {a b : Ival} {x y : ℝ} (ha : Encloses s a x) (hb : Encloses s b y) :
    Encloses s (add a b) (x + y) :=
  (Atiyah.Facts.fixed_primitives_sound s hs).2.1 a b x y ha hb

theorem encloses_neg (hs : 0 < s) {a : Ival} {x : ℝ} (ha : Encloses s a x) : Encloses s (neg a) (-x) :=
  (Atiyah.Facts.fixed_primitives_sound s hs).2.2.1 a x ha

theorem encloses_mul (hs : 0 < s) {a b : Ival} {x y : ℝ} (ha : Encloses s a x) (hb : Encloses s b y) :
    Encloses s (mul s a b) (x * y) :=
  (Atiyah.Facts.fixed_primitives_sound s hs).2.2.2.1 a b x y ha hb

theorem encloses_inv (hs : 0 < s) {a : Ival} {x : ℝ} (ha : Encloses s a x) :
    Encloses s (inv s a) x⁻¹ ∧ ((inv s a).2.2 = true → 0 < x) :=
  (Atiyah.Facts.fixed_primitives_sound s hs).2.2.2.2.1 a x ha

theorem encloses_sqrt (hs : 0 < s) {a : Ival} {x : ℝ} (ha : Encloses s a x) :
    Encloses s (sqrt s a) (Real.sqrt x) ∧ ((sqrt s a).2.2 = true → 0 < x) :=
  (Atiyah.Facts.fixed_primitives_sound s hs).2.2.2.2.2 a x ha

theorem encloses_sub (hs : 0 < s) {a b : Ival} {x y : ℝ} (ha : Encloses s a x) (hb : Encloses s b y) :
    Encloses s (sub a b) (x - y) := by
  rw [sub_eq_add_neg]; exact encloses_add hs ha (encloses_neg hs hb)

/-- A valid interval separated from zero. -/
def nonzero (a : Ival) : Bool := a.2.2 && (decide (0 < a.1) || decide (a.2.1 < 0))

theorem valid_of_nonzero {a : Ival} (h : nonzero a = true) : a.2.2 = true := by
  simp only [nonzero, Bool.and_eq_true] at h
  exact h.1

theorem ne_zero_of_nonzero (hs : 0 < s) {a : Ival} {x : ℝ} (ha : Encloses s a x) (h : nonzero a = true) : x ≠ 0 := by
  simp only [nonzero, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hu⟩ := ha h.1
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  rintro rfl
  rcases h.2 with h0 | h0
  · have : (0 : ℝ) < (a.1 : ℝ) / (s : ℝ) := div_pos (by exact_mod_cast h0) hsR
    linarith
  · have : (a.2.1 : ℝ) / (s : ℝ) < 0 := div_neg_of_neg_of_pos (by exact_mod_cast h0) hsR
    linarith

end Atiyah.Fixed

/-! ### `Atiyah`: Dual -/

/-!
# Complex intervals, dual intervals and complex dual intervals

The certificate needs enclosures of the Schur residual *and* of its derivative with respect to the two
free parameters. A dual interval carries a value interval together with an optional pair of intervals
enclosing the two directional derivatives (`none` means the derivative is identically zero, the cheap
case of constant data). Complex quantities are pairs (real part, imaginary part).

Soundness is stated against functions `f : E → ℝ` of the parameters: `JetEncloses s x e₀ e₁ a f` says
that, when `a` is valid, `f` is differentiable at `x` with value and directional derivatives enclosed.

The enclosure lemmas below are the generated study Facts `fixed_ad_ops_sound` and
`complex_pair_ops_sound`, restated for the named operations. Those Facts spell the operations out as
`let`-bound lambdas with their own `match` expressions, so they are applied with smart unfolding switched
off, which lets the elaborator unfold both `match` compilations.
-/

set_option maxHeartbeats 5000000

namespace Atiyah

open Fixed

/-! ## Complex intervals (no derivative data) -/

/-- A complex interval: real-part and imaginary-part intervals. -/
abbrev Cval := Ival × Ival

instance : DecidableEq Cval := inferInstance

namespace Cval

variable (s : ℤ)

def sub (a b : Cval) : Cval := (Fixed.sub a.1 b.1, Fixed.sub a.2 b.2)

def mul (a b : Cval) : Cval :=
  (Fixed.sub (Fixed.mul s a.1 b.1) (Fixed.mul s a.2 b.2), Fixed.add (Fixed.mul s a.1 b.2) (Fixed.mul s a.2 b.1))

/-- Multiplication by a real interval. -/
def scale (a : Cval) (t : Ival) : Cval := (Fixed.mul s a.1 t, Fixed.mul s a.2 t)

def zero : Cval := (ofRat s 0 1, ofRat s 0 1)

def one : Cval := (ofRat s 1 1, ofRat s 0 1)

end Cval

/-! ## Dual intervals -/

/-- A dual interval: value interval and optional derivative-pair enclosure. -/
abbrev Dual := Ival × Option (Ival × Ival)

instance : DecidableEq Dual := inferInstance

namespace Dual

variable (s : ℤ)

def add (a b : Dual) : Dual :=
  (Fixed.add a.1 b.1, match a.2, b.2 with
    | none, v => v
    | v, none => v
    | some u, some v => some (Fixed.add u.1 v.1, Fixed.add u.2 v.2))

def neg (a : Dual) : Dual := (Fixed.neg a.1, a.2.map (fun d => (Fixed.neg d.1, Fixed.neg d.2)))

def sub (a b : Dual) : Dual := add a (neg b)

def mul (a b : Dual) : Dual :=
  (Fixed.mul s a.1 b.1, match a.2, b.2 with
    | none, none => none
    | none, some v => some (Fixed.mul s a.1 v.1, Fixed.mul s a.1 v.2)
    | some u, none => some (Fixed.mul s u.1 b.1, Fixed.mul s u.2 b.1)
    | some u, some v => some (Fixed.add (Fixed.mul s u.1 b.1) (Fixed.mul s a.1 v.1),
                              Fixed.add (Fixed.mul s u.2 b.1) (Fixed.mul s a.1 v.2)))

def inv (a : Dual) : Dual :=
  let v := Fixed.inv s a.1
  (v, a.2.map (fun d => (Fixed.mul s (Fixed.mul s (Fixed.neg d.1) v) v,
                         Fixed.mul s (Fixed.mul s (Fixed.neg d.2) v) v)))

def sqrt (a : Dual) : Dual :=
  let v := Fixed.sqrt s a.1
  let t := Fixed.inv s (Fixed.mul s (Fixed.ofRat s 2 1) v)
  (v, a.2.map (fun d => (Fixed.mul s t d.1, Fixed.mul s t d.2)))

/-- A constant: exact value interval, zero derivative. -/
def const (a : Ival) : Dual := (a, none)

/-- The constant rational `a / b`. -/
def ofRat (a b : ℤ) : Dual := (Fixed.ofRat s a b, none)

/-- The interval `[-a/b, a/b]` with derivative `1` along the first parameter: the first moving coordinate. -/
def coordinate₀ (a b : ℤ) : Dual :=
  (((Fixed.ofRat s (-a) b).1, (Fixed.ofRat s a b).2.1, true), some (Fixed.ofRat s 1 1, Fixed.ofRat s 0 1))

/-- The interval `[-a/b, a/b]` with derivative `1` along the second parameter. -/
def coordinate₁ (a b : ℤ) : Dual :=
  (((Fixed.ofRat s (-a) b).1, (Fixed.ofRat s a b).2.1, true), some (Fixed.ofRat s 0 1, Fixed.ofRat s 1 1))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `none` encloses the zero derivative; `some (p₀, p₁)` encloses the derivatives along `e₀` and `e₁`. -/
def DerivEncloses (e₀ e₁ : E) (a : Option (Ival × Ival)) (d : E →L[ℝ] ℝ) : Prop :=
  match a with
  | none => d = 0
  | some p => Encloses s p.1 (d e₀) ∧ Encloses s p.2 (d e₁)

/-- A valid dual interval encloses the value and the two directional derivatives of `f` at `x`. -/
def JetEncloses (x e₀ e₁ : E) (a : Dual) (f : E → ℝ) : Prop :=
  a.1.2.2 = true → ∃ d : E →L[ℝ] ℝ, HasFDerivAt f d x ∧ Encloses s a.1 (f x) ∧ DerivEncloses s e₀ e₁ a.2 d

section Rules

variable {s} (hs : 0 < s) (x e₀ e₁ : E)
include hs

set_option smartUnfolding false

theorem jet_const {a : Ival} {c : ℝ} (h : Encloses s a c) : JetEncloses s x e₀ e₁ (const a) (fun _ => c) :=
  (Atiyah.Facts.fixed_ad_ops_sound (E := E) s hs x e₀ e₁).1 a c h

theorem jet_add {a b : Dual} {f g : E → ℝ} (ha : JetEncloses s x e₀ e₁ a f) (hb : JetEncloses s x e₀ e₁ b g) :
    JetEncloses s x e₀ e₁ (add a b) (fun y => f y + g y) :=
  (Atiyah.Facts.fixed_ad_ops_sound (E := E) s hs x e₀ e₁).2.1 a b f g ha hb

theorem jet_neg {a : Dual} {f : E → ℝ} (ha : JetEncloses s x e₀ e₁ a f) :
    JetEncloses s x e₀ e₁ (neg a) (fun y => -f y) :=
  (Atiyah.Facts.fixed_ad_ops_sound (E := E) s hs x e₀ e₁).2.2.1 a f ha

theorem jet_mul {a b : Dual} {f g : E → ℝ} (ha : JetEncloses s x e₀ e₁ a f) (hb : JetEncloses s x e₀ e₁ b g) :
    JetEncloses s x e₀ e₁ (mul s a b) (fun y => f y * g y) :=
  (Atiyah.Facts.fixed_ad_ops_sound (E := E) s hs x e₀ e₁).2.2.2.1 a b f g ha hb

theorem jet_inv {a : Dual} {f : E → ℝ} (ha : JetEncloses s x e₀ e₁ a f) :
    JetEncloses s x e₀ e₁ (inv s a) (fun y => (f y)⁻¹) :=
  (Atiyah.Facts.fixed_ad_ops_sound (E := E) s hs x e₀ e₁).2.2.2.2.1 a f ha

theorem jet_sqrt {a : Dual} {f : E → ℝ} (ha : JetEncloses s x e₀ e₁ a f) :
    JetEncloses s x e₀ e₁ (sqrt s a) (fun y => Real.sqrt (f y)) :=
  (Atiyah.Facts.fixed_ad_ops_sound (E := E) s hs x e₀ e₁).2.2.2.2.2 a f ha

theorem jet_sub {a b : Dual} {f g : E → ℝ} (ha : JetEncloses s x e₀ e₁ a f) (hb : JetEncloses s x e₀ e₁ b g) :
    JetEncloses s x e₀ e₁ (sub a b) (fun y => f y - g y) := by
  simp only [sub_eq_add_neg]; exact jet_add hs x e₀ e₁ ha (jet_neg hs x e₀ e₁ hb)

theorem jet_ofRat (a b : ℤ) : JetEncloses s x e₀ e₁ (ofRat s a b) (fun _ => (a : ℝ) / (b : ℝ)) :=
  jet_const hs x e₀ e₁ (encloses_ofRat hs a b)

end Rules

end Dual

/-! ## Complex dual intervals -/

/-- A complex dual interval: real and imaginary parts. -/
abbrev Cdual := Dual × Dual

instance : DecidableEq Cdual := inferInstance

namespace Cdual

variable (s : ℤ)

def add (a b : Cdual) : Cdual := (Dual.add a.1 b.1, Dual.add a.2 b.2)

def neg (a : Cdual) : Cdual := (Dual.neg a.1, Dual.neg a.2)

def sub (a b : Cdual) : Cdual := (Dual.sub a.1 b.1, Dual.sub a.2 b.2)

def mul (a b : Cdual) : Cdual :=
  (Dual.sub (Dual.mul s a.1 b.1) (Dual.mul s a.2 b.2), Dual.add (Dual.mul s a.1 b.2) (Dual.mul s a.2 b.1))

def inv (a : Cdual) : Cdual :=
  let t := Dual.inv s (Dual.add (Dual.mul s a.1 a.1) (Dual.mul s a.2 a.2))
  (Dual.mul s a.1 t, Dual.mul s (Dual.neg a.2) t)

/-- Multiplication by a real dual interval. -/
def scale (a : Cdual) (t : Dual) : Cdual := (Dual.mul s a.1 t, Dual.mul s a.2 t)

def zero : Cdual := (Dual.ofRat s 0 1, Dual.ofRat s 0 1)

def one : Cdual := (Dual.ofRat s 1 1, Dual.ofRat s 0 1)

/-- A complex interval as a constant complex dual interval. -/
def ofCval (z : Cval) : Cdual := ((z.1, none), (z.2, none))

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Real and imaginary parts are jet-enclosed. -/
def Encloses (x e₀ e₁ : E) (a : Cdual) (f : E → ℂ) : Prop :=
  Dual.JetEncloses s x e₀ e₁ a.1 (fun y => (f y).re) ∧ Dual.JetEncloses s x e₀ e₁ a.2 (fun y => (f y).im)

section Rules

variable {s} (hs : 0 < s) (x e₀ e₁ : E)
include hs

/-- The generic complex-pair Fact, instantiated with the dual-interval rules. -/
local macro "pair_rules" : term =>
  `(Atiyah.Facts.complex_pair_ops_sound (Dual.JetEncloses s x e₀ e₁) Dual.add (Dual.mul s) Dual.neg (Dual.inv s)
      (fun _ _ _ _ ha hb => Dual.jet_add hs x e₀ e₁ ha hb) (fun _ _ _ _ ha hb => Dual.jet_mul hs x e₀ e₁ ha hb)
      (fun _ _ ha => Dual.jet_neg hs x e₀ e₁ ha) (fun _ _ ha => Dual.jet_inv hs x e₀ e₁ ha))

theorem encloses_add {a b : Cdual} {f g : E → ℂ} (ha : Encloses s x e₀ e₁ a f) (hb : Encloses s x e₀ e₁ b g) :
    Encloses s x e₀ e₁ (add a b) (fun y => f y + g y) := (pair_rules).1 a b f g ha hb

theorem encloses_neg {a : Cdual} {f : E → ℂ} (ha : Encloses s x e₀ e₁ a f) :
    Encloses s x e₀ e₁ (neg a) (fun y => -f y) := (pair_rules).2.1 a f ha

theorem encloses_sub {a b : Cdual} {f g : E → ℂ} (ha : Encloses s x e₀ e₁ a f) (hb : Encloses s x e₀ e₁ b g) :
    Encloses s x e₀ e₁ (sub a b) (fun y => f y - g y) := (pair_rules).2.2.1 a b f g ha hb

theorem encloses_mul {a b : Cdual} {f g : E → ℂ} (ha : Encloses s x e₀ e₁ a f) (hb : Encloses s x e₀ e₁ b g) :
    Encloses s x e₀ e₁ (mul s a b) (fun y => f y * g y) := (pair_rules).2.2.2.1 a b f g ha hb

theorem encloses_inv {a : Cdual} {f : E → ℂ} (ha : Encloses s x e₀ e₁ a f) :
    Encloses s x e₀ e₁ (inv s a) (fun y => (f y)⁻¹) := (pair_rules).2.2.2.2.1 a f ha

theorem encloses_scale {a : Cdual} {b : Dual} {f : E → ℂ} {g : E → ℝ}
    (ha : Encloses s x e₀ e₁ a f) (hb : Dual.JetEncloses s x e₀ e₁ b g) :
    Encloses s x e₀ e₁ (scale s a b) (fun y => f y * (g y : ℂ)) := (pair_rules).2.2.2.2.2.1 a b f g ha hb

theorem encloses_mk {a b : Dual} {f g : E → ℝ} (ha : Dual.JetEncloses s x e₀ e₁ a f) (hb : Dual.JetEncloses s x e₀ e₁ b g) :
    Encloses s x e₀ e₁ (a, b) (fun y => (f y : ℂ) + (g y : ℂ) * Complex.I) := (pair_rules).2.2.2.2.2.2 a b f g ha hb

theorem encloses_zero : Encloses s x e₀ e₁ (zero s) (fun _ => 0) := by
  have h := Dual.jet_ofRat hs x e₀ e₁ 0 1
  simp only [Int.cast_zero, Int.cast_one, zero_div] at h
  exact ⟨h, h⟩

theorem encloses_one : Encloses s x e₀ e₁ (one s) (fun _ => 1) := by
  have h0 := Dual.jet_ofRat hs x e₀ e₁ 0 1
  have h1 := Dual.jet_ofRat hs x e₀ e₁ 1 1
  simp only [Int.cast_zero, Int.cast_one, div_one] at h0 h1
  exact ⟨h1, h0⟩

end Rules

end Cdual

end Atiyah

/-! ### `Atiyah`: Coefficients -/

/-!
# The coefficient program

A point polynomial is the product of the linear factors `z - w·X` of the directions from the base point
to every other point, where `(z, w) = (d₀ + i d₁, ‖d‖ - d₂)` is the raw stereographic lift of the
direction `d`. The program multiplies these factors into coefficient lists (ascending powers of `X`).

The configuration has `2m` points: `m` base points followed by their half-turn images. Point `mov` and
its mate `mov + m` move; all other points are fixed. Row `i` of the even block is built in two steps:

* the *constant row*: the product over the fixed points other than `i` (computed once, in plain interval
  arithmetic);
* the *moving block*: the constant row times the factors to the moving pair (or, for the moving row,
  times the factors to every other point), keeping the even coefficients, rescaled by powers of two.

The same program is written three times: on complex intervals (`Cval`), on complex dual intervals
(`Cdual`) and on functions of the moving parameters (`Geom`). `block_encloses` says that the interval
version encloses the geometric one; it is the generated Fact `coefficient_program_encloses_block`.
-/

set_option maxHeartbeats 5000000

namespace Atiyah

open Fixed

/-! ## On complex intervals -/

namespace Cval

/-- A point with interval coordinates. -/
abbrev Point := Ival × Ival × Ival

variable (s : ℤ)

/-- The linear factor of the direction `d = q - p`: numerator `d₀ + i d₁` and denominator `‖d‖ - d₂`. -/
def factor (p q : Point) : Cval × Ival :=
  let d0 := Fixed.sub q.1 p.1
  let d1 := Fixed.sub q.2.1 p.2.1
  let d2 := Fixed.sub q.2.2 p.2.2
  ((d0, d1), Fixed.sub (Fixed.sqrt s (Fixed.add (Fixed.add (Fixed.mul s d0 d0) (Fixed.mul s d1 d1)) (Fixed.mul s d2 d2))) d2)

/-- Multiply a coefficient list by the linear factor `z - w·X`. -/
def times (p : List Cval) (f : Cval × Ival) : List Cval :=
  List.zipWith (sub) ((p.map (mul s f.1)) ++ [zero s]) (zero s :: p.map (fun t => scale s t f.2))

def origin : Point := (ofRat s 0 1, ofRat s 0 1, ofRat s 0 1)

/-- The product, starting from `p`, of the factors from point `i` to the points `js`. -/
def product (pts : List Point) (i : ℕ) (js : List ℕ) (p : List Cval) : List Cval :=
  js.foldl (fun p j => times s p (factor s (pts.getD i (origin s)) (pts.getD j (origin s)))) p

/-- Row `i` of the constant part: the product over every point other than `i`, `mov` and its mate. -/
def constantRows (m mov : ℕ) (pts : List Point) : List (List Cval) :=
  (List.range m).map (fun i => if i = mov then [one s] else
    product s pts i ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)) [one s])

/-- The point `y` lies in the interval box `p`. -/
def Point.Encloses (p : Point) (y : EuclideanSpace ℝ (Fin 3)) : Prop :=
  Fixed.Encloses s p.1 (y 0) ∧ Fixed.Encloses s p.2.1 (y 1) ∧ Fixed.Encloses s p.2.2 (y 2)

end Cval

/-! ## On complex dual intervals -/

namespace Cdual

/-- A point with dual-interval coordinates. -/
abbrev Point := Dual × Dual × Dual

variable (s : ℤ)

def factor (p q : Point) : Cdual × Dual :=
  let d0 := Dual.sub q.1 p.1
  let d1 := Dual.sub q.2.1 p.2.1
  let d2 := Dual.sub q.2.2 p.2.2
  ((d0, d1), Dual.sub (Dual.sqrt s (Dual.add (Dual.add (Dual.mul s d0 d0) (Dual.mul s d1 d1)) (Dual.mul s d2 d2))) d2)

def times (p : List Cdual) (f : Cdual × Dual) : List Cdual :=
  List.zipWith (sub) ((p.map (mul s f.1)) ++ [zero s]) (zero s :: p.map (fun t => scale s t f.2))

def origin : Point := (Dual.ofRat s 0 1, Dual.ofRat s 0 1, Dual.ofRat s 0 1)

def product (pts : List Point) (i : ℕ) (js : List ℕ) (p : List Cdual) : List Cdual :=
  js.foldl (fun p j => times s p (factor s (pts.getD i (origin s)) (pts.getD j (origin s)))) p

/-- The scaled even block: row `i` extends its constant row `C[i]` by the factors to the moving pair (for
the moving row, by the factors to every other point), keeps the even coefficients `0, 2, …, 2(m-1)` and
rescales entry `k` of row `i` by `2^-ce[k] · 2^-re[i]`. -/
def block (m mov : ℕ) (re ce : List ℕ) (pts : List Point) (C : List (List Cdual)) : List (List Cdual) :=
  (List.range m).map (fun i =>
    let js := if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov, mov+m]
    let p := product s pts i js (C.getD i [one s])
    (List.range m).map (fun k =>
      scale s (scale s (p.getD (2*k) (zero s)) (Dual.ofRat s 1 (2^(ce.getD k 0)))) (Dual.ofRat s 1 (2^(re.getD i 0)))))

/-- A constant point (zero derivatives). -/
def Point.ofCval (p : Cval.Point) : Point := ((p.1, none), (p.2.1, none), (p.2.2, none))

/-- Displace point `mov` by `(h, 0, k)` and its mate by the half-turn image of that displacement. -/
def movePair (m mov : ℕ) (h k : Dual) (pts : List Point) : List Point :=
  let old := pts.getD mov (origin s)
  let p := (Dual.add old.1 h, old.2.1, Dual.add old.2.2 k)
  (pts.set mov p).set (mov+m) (Dual.neg p.1, Dual.neg p.2.1, p.2.2)

end Cdual

/-! ## On functions of the moving parameters -/

namespace Geom

noncomputable section

variable {E : Type}

/-- The raw stereographic lift of the direction from `p` to `q`, as functions of the parameters. -/
def factor (p q : E → EuclideanSpace ℝ (Fin 3)) : (E → ℂ) × (E → ℝ) :=
  ((fun y => (((q y - p y) 0 : ℝ) : ℂ) + (((q y - p y) 1 : ℝ) : ℂ) * Complex.I),
   (fun y => ‖q y - p y‖ - (q y - p y) 2))

def times (p : List (E → ℂ)) (f : (E → ℂ) × (E → ℝ)) : List (E → ℂ) :=
  List.zipWith (fun (a b : E → ℂ) y => a y - b y)
    ((p.map (fun a y => f.1 y * a y)) ++ [fun _ => 0]) ((fun _ => 0) :: p.map (fun a y => a y * (f.2 y : ℂ)))

def constantRows (m mov : ℕ) (qts : List (E → EuclideanSpace ℝ (Fin 3))) : List (List (E → ℂ)) :=
  (List.range m).map (fun i => if i = mov then [fun _ => (1 : ℂ)] else
    ((List.range (2*m)).filter (fun j => j != i && j != mov && j != mov+m)).foldl
      (fun p j => times p (factor (qts.getD i (fun _ => 0)) (qts.getD j (fun _ => 0)))) [fun _ => 1])

def block (m mov : ℕ) (re ce : List ℕ) (qts : List (E → EuclideanSpace ℝ (Fin 3))) (C : List (List (E → ℂ))) :
    List (List (E → ℂ)) :=
  (List.range m).map (fun i =>
    let js := if i = mov then (List.range (2*m)).filter (fun j => j != i) else [mov, mov+m]
    let p := js.foldl (fun p j => times p (factor (qts.getD i (fun _ => 0)) (qts.getD j (fun _ => 0)))) (C.getD i [fun _ => 1])
    (List.range m).map (fun k => fun y =>
      (p.getD (2*k) (fun _ => 0) y) * ((1/(2:ℝ)^(ce.getD k 0)):ℂ) * ((1/(2:ℝ)^(re.getD i 0)):ℂ)))

/-- Point `mov` displaced by the parameters `(y 0, 0, y 1)`, its mate by the half-turn image. -/
def movePair (m mov : ℕ) (qts : List ((Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 3))) :
    List ((Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 3)) :=
  let oldq := qts.getD mov (fun _ => 0)
  let newq : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![oldq y 0 + y 0, oldq y 1, oldq y 2 + y 1]
  let mateq : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 3) := fun y => WithLp.toLp 2 ![-newq y 0, -newq y 1, newq y 2]
  (qts.set mov newq).set (mov+m) mateq

end

end Geom

/-! ## Soundness -/

set_option smartUnfolding false in
/-- Over the box of radius `a/b` around the centre, the interval block built from base points enclosing
the real points encloses the geometric block of the moved configuration.

This is the generated Fact `coefficient_program_encloses_block`. Its statement spells every operation out
as a `let`-bound lambda; each is identified with the named definition once (function-level `rfl`), after
which the two programs are syntactically the same. -/
theorem block_encloses (s a b : ℤ) (hs : 0 < s) (hb : 0 < b) (m mov : ℕ) (re ce : List ℕ)
    (ps : List Cval.Point) (qs : List (EuclideanSpace ℝ (Fin 3))) (hpq : List.Forall₂ (Cval.Point.Encloses s) ps qs) :
    ∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) ((a : ℝ) / (b : ℝ)),
      List.Forall₂ (List.Forall₂ (Cdual.Encloses s x (Pi.single 0 1) (Pi.single 1 1)))
        (Cdual.block s m mov re ce
          (Cdual.movePair s m mov (Dual.coordinate₀ s a b) (Dual.coordinate₁ s a b) (ps.map Cdual.Point.ofCval))
          ((Cval.constantRows s m mov ps).map (List.map Cdual.ofCval)))
        (Geom.block m mov re ce (Geom.movePair m mov (qs.map (fun p _ => p)))
          (Geom.constantRows m mov (qs.map (fun p _ => p)))) := by
  have h := Atiyah.Facts.coefficient_program_encloses_block s a b hs hb m mov re ce
  extract_lets I D Z E R O J K V q ia ine im ii iq is da dn ds dm di dq dc zs zm zsc zz zo pz fac tim
    zs0 zm0 zsc0 zz0 zo0 pz0 fac0 tim0 fb tb at h
  have hV : V = Cval.Point.Encloses s := rfl
  have hK : K = fun x => Cdual.Encloses s x (Pi.single 0 1) (Pi.single 1 1) := rfl
  have hda : da = Dual.add := rfl
  have hdn : dn = Dual.neg := rfl
  have hdc : dc = Dual.ofRat s := rfl
  have hzsc : zsc = Cdual.scale s := rfl
  have hzz : zz = Cdual.zero s := rfl
  have hzo : zo = Cdual.one s := rfl
  have hpz : pz = Cdual.origin s := rfl
  have hfac : fac = Cdual.factor s := rfl
  have htim : tim = Cdual.times s := rfl
  have hzo0 : zo0 = Cval.one s := rfl
  have hpz0 : pz0 = Cval.origin s := rfl
  have hfac0 : fac0 = Cval.factor s := rfl
  have htim0 : tim0 = Cval.times s := rfl
  have hfb : fb = Geom.factor := rfl
  have htb : tb = Geom.times := rfl
  rw [hV] at h
  specialize h ps qs hpq
  simp only [hK, hda, hdn, hdc, hzsc, hzz, hzo, hpz, hfac, htim, hzo0, hpz0, hfac0, htim0, hfb, htb] at h
  exact h

end Atiyah

/-! ### `Atiyah`: LU -/

/-!
# Gaussian elimination with a fixed pivot sequence

The even block has `m` rows and `m` columns. Taking column `0` as the right-hand side and the rows other
than `r` as the system, elimination with the recorded pivots and back substitution produce a solution
`v`; the *Schur residual* is what row `r` leaves over. Row-sum relations are preserved exactly by every
step, so a zero residual means that column `0` is a combination of the other columns on all `m` rows.

The program is generic in the scalar operations: it runs on complex dual intervals for the certificate
and on functions of the moving parameters for its meaning. `eliminate_encloses` and `residual_encloses`
transport enclosures through it (the generated Fact `lu_schur_sound`); `column_dependence_of_residual`
is the exact algebra (the Fact `schur_zero_column_dependence`).
-/

set_option maxHeartbeats 5000000

namespace Atiyah.LU

section Program

variable {α : Type} (sub mul : α → α → α) (inv : α → α) (zero : α) (piv : List ℕ)

/-- Stage `k`: swap row `piv[k]` into position `k` and eliminate column `k` below the diagonal. -/
def step (X : List (List α)) (k : ℕ) : List (List α) :=
  let p := piv.getD k k
  let X := (X.set k (X.getD p [])).set p (X.getD k [])
  let row := X.getD k []
  let ip := inv (row.getD k zero)
  X.mapIdx (fun i r => if k < i then
    let v := mul (r.getD k zero) ip
    r.mapIdx (fun j z => if k < j then sub z (mul v (row.getD j zero)) else z) else r)

/-- Stages `0, …, n-1`. -/
def eliminate (n : ℕ) (X : List (List α)) : List (List α) := (List.range n).foldl (step sub mul inv zero piv) X

/-- Back substitution on an eliminated augmented system with `n` unknowns (column `n` is the right-hand side). -/
def backsolve (n : ℕ) (U : List (List α)) : List α :=
  (List.range n).reverse.foldl (fun v i =>
    let row := U.getD i []
    let t := (List.range n).foldl (fun t j => if i < j then sub t (mul (row.getD j zero) (v.getD j zero)) else t) (row.getD n zero)
    v.set i (mul t (inv (row.getD i zero)))) (List.replicate n zero)

/-- The residual of the block row `row` (right-hand side first) against the solution of `U`. -/
def residual (n : ℕ) (U : List (List α)) (row : List α) : α :=
  (List.range n).foldl (fun z k => sub z (mul (row.getD (k+1) zero) ((backsolve sub mul inv zero n U).getD k zero))) (row.getD 0 zero)

/-- Rows `ids` of a block, as the augmented system `[columns 1 … n | column 0]`. -/
def system (n : ℕ) (ids : List ℕ) (B : List (List α)) : List (List α) :=
  ids.map (fun i => ((List.range n).map (fun j => (B.getD i []).getD (j+1) zero)) ++ [(B.getD i []).getD 0 zero])

end Program

/-! ## Enclosures are preserved -/

/-- Reading an entry of related lists (with related defaults) gives related entries. -/
theorem forall₂_getD {α β : Type} {R : α → β → Prop} {l : List α} {k : List β} (h : List.Forall₂ R l k)
    {a : α} {b : β} (hab : R a b) (i : ℕ) : R (l.getD i a) (k.getD i b) :=
  (Atiyah.Facts.forall₂_getD_set R l k h a b hab i).1


section Sound

variable {s : ℤ} (hs : 0 < s) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (x e₀ e₁ : E) (n : ℕ) (piv : List ℕ)
include hs

theorem eliminate_encloses {X : List (List Cdual)} {Y : List (List (E → ℂ))}
    (h : List.Forall₂ (List.Forall₂ (Cdual.Encloses s x e₀ e₁)) X Y) :
    List.Forall₂ (List.Forall₂ (Cdual.Encloses s x e₀ e₁))
      (eliminate Cdual.sub (Cdual.mul s) (Cdual.inv s) (Cdual.zero s) piv n X)
      (eliminate (· - ·) (· * ·) (·⁻¹) 0 piv n Y) :=
  (Atiyah.Facts.lu_schur_sound (Cdual.Encloses s x e₀ e₁) (Cdual.zero s) (0 : E → ℂ)
      Cdual.sub (Cdual.mul s) (· - ·) (· * ·) (Cdual.inv s) (·⁻¹)
      (Cdual.encloses_zero hs x e₀ e₁)
      (fun _ _ _ _ ha hb => Cdual.encloses_sub hs x e₀ e₁ ha hb)
      (fun _ _ _ _ ha hb => Cdual.encloses_mul hs x e₀ e₁ ha hb)
      (fun _ _ ha => Cdual.encloses_inv hs x e₀ e₁ ha) n piv).2.1 X Y h (List.range n)

theorem residual_encloses {X : List (List Cdual)} {Y : List (List (E → ℂ))} {row : List Cdual} {row' : List (E → ℂ)}
    (h : List.Forall₂ (List.Forall₂ (Cdual.Encloses s x e₀ e₁)) X Y)
    (hrow : List.Forall₂ (Cdual.Encloses s x e₀ e₁) row row') :
    Cdual.Encloses s x e₀ e₁
      (residual Cdual.sub (Cdual.mul s) (Cdual.inv s) (Cdual.zero s) n X row)
      (residual (· - ·) (· * ·) (·⁻¹) 0 n Y row') :=
  (Atiyah.Facts.lu_schur_sound (Cdual.Encloses s x e₀ e₁) (Cdual.zero s) (0 : E → ℂ)
      Cdual.sub (Cdual.mul s) (· - ·) (· * ·) (Cdual.inv s) (·⁻¹)
      (Cdual.encloses_zero hs x e₀ e₁)
      (fun _ _ _ _ ha hb => Cdual.encloses_sub hs x e₀ e₁ ha hb)
      (fun _ _ _ _ ha hb => Cdual.encloses_mul hs x e₀ e₁ ha hb)
      (fun _ _ ha => Cdual.encloses_inv hs x e₀ e₁ ha) n []).2.2.2 X Y row row' h hrow

end Sound

/-! ## Exact algebra -/

/-- If the Schur residual of row `r` vanishes at `y` and every pivot is nonzero there, column `0` of the
block is a combination of columns `1 … n` on all `n+1` rows. -/
theorem column_dependence_of_residual (E : Type) (n r : ℕ) (ids piv : List ℕ) (B : List (List (E → ℂ))) (y : E)
    (hids : ids.length = n) (hcover : ∀ i < n+1, i ≠ r → i ∈ ids)
    (hpiv : ∀ k < n, k ≤ piv.getD k k ∧ piv.getD k k < n)
    (hdiag : ∀ i < n, (((eliminate (· - ·) (· * ·) (·⁻¹) 0 piv n (system 0 n ids B) ++ [B.getD r []]).getD i []).getD i 0) y ≠ 0)
    (hres : residual (· - ·) (· * ·) (·⁻¹) 0 n
      ((eliminate (· - ·) (· * ·) (·⁻¹) 0 piv n (system 0 n ids B) ++ [B.getD r []]).take n)
      ((eliminate (· - ·) (· * ·) (·⁻¹) 0 piv n (system 0 n ids B) ++ [B.getD r []]).getD n []) y = 0) :
    ∃ v : ℕ → ℂ, ∀ i < n+1, (∑ j ∈ Finset.range n, ((B.getD i []).getD (j+1) 0) y * v j) = ((B.getD i []).getD 0 0) y :=
  Atiyah.Facts.schur_zero_column_dependence E n r ids piv B y hids hcover hpiv hdiag hres

end Atiyah.LU

/-! ### `Atiyah`: Newton -/

/-!
# A Newton–Kantorovich zero certificate

For a map `F : ℝ² → ℝ²`, an approximate inverse Jacobian `P` (the *preconditioner*, a rational `2 × 2`
matrix) and the box of radius `ρ = 10⁻⁴⁰` around `0`: if `|P·F(0)| ≤ ρ/2` in every coordinate and
`I - P·DF(x)` has row sums of absolute values at most `1/2` throughout the box, then `x ↦ x - P·F(x)`
contracts the box into itself and `F` has a zero there (Banach fixed point; the generated Fact
`local_zero_of_row_sums`).

`check` evaluates these conditions on interval data: `cen` encloses `F(0)` and `bx` encloses the jet of
`F` over the box; `zero_of_check` is the resulting zero.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Newton

open Fixed

variable (s : ℤ)

/-- The derivative pair of a dual interval (`(0, 0)` when it carries no derivative data). -/
def deriv (d : Dual) : Ival × Ival := d.2.getD (ofRat s 0 1, ofRat s 0 1)

/-- A bound on `|x|` over the interval, in scaled units. -/
def mag (x : Ival) : ℤ := max |x.1| |x.2.1|

/-- Entry `(i, j)` of the preconditioner with integer entries `N` over the common denominator `D`. -/
def pre (N : ℕ → ℕ → ℤ) (D : ℤ) (i j : ℕ) : Ival := ofRat s (N i j) D

/-- Coordinate `i` of the preconditioned centre residual `P·F(0)`. -/
def centre (N : ℕ → ℕ → ℤ) (D : ℤ) (cen : Cdual) (i : ℕ) : Ival :=
  add (mul s (pre s N D i 0) cen.1.1) (mul s (pre s N D i 1) cen.2.1)

/-- Entry `(i, j)` of the preconditioned derivative defect `I - P·DF` over the box. -/
def defect (N : ℕ → ℕ → ℤ) (D : ℤ) (bx : Cdual) (i j : ℕ) : Ival :=
  let dj : Dual → Ival := fun d => if j = 0 then (deriv s d).1 else (deriv s d).2
  let pd := add (mul s (pre s N D i 0) (dj bx.1)) (mul s (pre s N D i 1) (dj bx.2))
  if i = j then add (ofRat s 1 1) (neg pd) else neg pd

/-- The Kantorovich conditions, with every validity flag: `2·|P·F(0)| ≤ 10⁻⁴⁰` and row sums of
`|I - P·DF|` at most `1/2`. -/
def check (N : ℕ → ℕ → ℤ) (D : ℤ) (cen bx : Cdual) : Bool :=
  bx.1.1.2.2 && bx.2.1.2.2 &&
  (centre s N D cen 0).2.2 && (centre s N D cen 1).2.2 &&
  (defect s N D bx 0 0).2.2 && (defect s N D bx 0 1).2.2 && (defect s N D bx 1 0).2.2 && (defect s N D bx 1 1).2.2 &&
  decide (2 * max (mag (centre s N D cen 0)) (mag (centre s N D cen 1)) * 10^40 ≤ s ∧
    2 * (mag (defect s N D bx 0 0) + mag (defect s N D bx 0 1)) ≤ s ∧
    2 * (mag (defect s N D bx 1 0) + mag (defect s N D bx 1 1)) ≤ s)

variable {s}

/-- The real preconditioner as a continuous linear map `ℝ² → ℝ²`. -/
noncomputable def preMap (P : ℕ → ℕ → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![P 0 0 • ContinuousLinearMap.proj 0 + P 0 1 • ContinuousLinearMap.proj 1,
                           P 1 0 • ContinuousLinearMap.proj 0 + P 1 1 • ContinuousLinearMap.proj 1]

theorem preMap_injective {P : ℕ → ℕ → ℝ} (hdet : P 0 0 * P 1 1 - P 0 1 * P 1 0 ≠ 0) : Function.Injective (preMap P) := by
  intro x y h
  have h0 : P 0 0 * x 0 + P 0 1 * x 1 = P 0 0 * y 0 + P 0 1 * y 1 := congrFun h 0
  have h1 : P 1 0 * x 0 + P 1 1 * x 1 = P 1 0 * y 0 + P 1 1 * y 1 := congrFun h 1
  have e0 : (x 0 - y 0) * (P 0 0 * P 1 1 - P 0 1 * P 1 0) = 0 := by linear_combination P 1 1 * h0 - P 0 1 * h1
  have e1 : (x 1 - y 1) * (P 0 0 * P 1 1 - P 0 1 * P 1 0) = 0 := by linear_combination P 0 0 * h1 - P 1 0 * h0
  ext i
  fin_cases i
  · exact sub_eq_zero.mp ((mul_eq_zero.mp e0).resolve_right hdet)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp e1).resolve_right hdet)

theorem abs_le_mag (hs : 0 < s) {a : Ival} {u : ℝ} (hu : Encloses s a u) (ha : a.2.2 = true) :
    |u| ≤ (mag a : ℝ) / (s : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  obtain ⟨hl, hh⟩ := hu ha
  have hlow : -mag a ≤ a.1 := le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _)
  have hhigh : a.2.1 ≤ mag a := le_trans (le_abs_self _) (le_max_right _ _)
  have hl' : -(mag a : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast hlow
  have hh' : (a.2.1 : ℝ) ≤ (mag a : ℝ) := by exact_mod_cast hhigh
  apply abs_le.mpr
  constructor
  · have := (div_le_div_of_nonneg_right hl' hs'.le).trans hl
    simpa only [neg_div] using this
  · exact hh.trans (div_le_div_of_nonneg_right hh' hs'.le)

/-- If `cen` encloses `F 0`, `bx` encloses the jet of `F` over the box, the preconditioner is invertible
and the check passes, then `F` has a zero in the box. -/
theorem zero_of_check (hs : 0 < s) (N : ℕ → ℕ → ℤ) (D : ℤ) (hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0) (hD : D ≠ 0)
    (F : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (cen bx : Cdual)
    (hcen : Encloses s cen.1.1 (F 0 0) ∧ Encloses s cen.2.1 (F 0 1))
    (hbox : ∀ x ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ)),
      Dual.JetEncloses s x (Pi.single 0 1) (Pi.single 1 1) bx.1 (fun y => F y 0) ∧
      Dual.JetEncloses s x (Pi.single 0 1) (Pi.single 1 1) bx.2 (fun y => F y 1))
    (hcheck : check s N D cen bx = true) :
    ∃ z ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ)), F z = 0 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨fb0, fb1⟩, fc0⟩, fc1⟩, fe00⟩, fe01⟩, fe10⟩, fe11⟩, hcenter, he0, he1⟩ := hcheck
  -- the real preconditioner and the enclosures of its action
  let P : ℕ → ℕ → ℝ := fun i j => (N i j : ℝ) / (D : ℝ)
  have hp (i j : ℕ) : Encloses s (pre s N D i j) (P i j) := encloses_ofRat hs (N i j) D
  have rz : Encloses s (ofRat s 0 1) 0 := by simpa using encloses_ofRat hs 0 1
  have ro : Encloses s (ofRat s 1 1) 1 := by simpa using encloses_ofRat hs 1 1
  have lin (i : ℕ) {a b : Ival} {u v : ℝ} (hu : Encloses s a u) (hv : Encloses s b v) :
      Encloses s (add (mul s (pre s N D i 0) a) (mul s (pre s N D i 1) b)) (P i 0 * u + P i 1 * v) :=
    encloses_add hs (encloses_mul hs (hp i 0) hu) (encloses_mul hs (hp i 1) hv)
  have rowb {a b : Ival} {u v : ℝ} (hu : Encloses s a u) (hv : Encloses s b v) (fa : a.2.2 = true) (fb : b.2.2 = true)
      (hb : 2 * (mag a + mag b) ≤ s) : |u| + |v| ≤ (1/2 : ℝ) := by
    have ht : (2 : ℝ) * ((mag a : ℝ) + (mag b : ℝ)) ≤ (s : ℝ) := by exact_mod_cast hb
    apply (add_le_add (abs_le_mag hs hu fa) (abs_le_mag hs hv fb)).trans
    rw [← add_div]
    apply (div_le_iff₀ hs').mpr
    linarith
  have cenb {a : Ival} {u : ℝ} (hu : Encloses s a u) (fa : a.2.2 = true)
      (hb : mag a ≤ max (mag (centre s N D cen 0)) (mag (centre s N D cen 1))) : |u| ≤ (1 / (10^40 : ℝ)) / 2 := by
    have ht : (2 : ℝ) * (max (mag (centre s N D cen 0)) (mag (centre s N D cen 1)) : ℤ) * (10 : ℝ)^40 ≤ (s : ℝ) := by
      exact_mod_cast hcenter
    have hb' : (mag a : ℝ) ≤ max (mag (centre s N D cen 0) : ℝ) (mag (centre s N D cen 1) : ℝ) := by exact_mod_cast hb
    apply (abs_le_mag hs hu fa).trans
    apply (div_le_iff₀ hs').mpr
    norm_num at ht ⊢
    linarith
  -- the preconditioner is injective
  have hA : Function.Injective (preMap P) := by
    apply preMap_injective
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD
    have : P 0 0 * P 1 1 - P 0 1 * P 1 0 = ((N 0 0 * N 1 1 - N 0 1 * N 1 0 : ℤ) : ℝ) / ((D : ℝ) * (D : ℝ)) := by
      simp only [P]
      field_simp
      push_cast
      ring
    rw [this]
    exact div_ne_zero (by exact_mod_cast hdet) (mul_ne_zero hD' hD')
  apply Atiyah.Facts.local_zero_of_row_sums F (preMap P) (1 / (10^40 : ℝ)) (by positivity) hA
  · -- the preconditioned centre residual is at most half the radius
    intro i
    fin_cases i
    · exact cenb (lin 0 hcen.1 hcen.2) fc0 (le_max_left _ _)
    · exact cenb (lin 1 hcen.1 hcen.2) fc1 (le_max_right _ _)
  · -- the preconditioned derivative defect has row sums at most 1/2
    intro x hx
    obtain ⟨d0, hd0, -, ho0⟩ := (hbox x hx).1 fb0
    obtain ⟨d1, hd1, -, ho1⟩ := (hbox x hx).2 fb1
    have hd (a : Dual) (d : (Fin 2 → ℝ) →L[ℝ] ℝ) (h : Dual.DerivEncloses s (Pi.single 0 1) (Pi.single 1 1) a.2 d) :
        Encloses s (deriv s a).1 (d (Pi.single 0 1)) ∧ Encloses s (deriv s a).2 (d (Pi.single 1 1)) := by
      cases he : a.2 with
      | none =>
        have hz : d = 0 := by simpa only [Dual.DerivEncloses, he] using h
        subst hz
        simpa [deriv, he] using And.intro rz rz
      | some p => simpa only [Dual.DerivEncloses, deriv, he, Option.getD_some] using h
    obtain ⟨r00, r01⟩ := hd bx.1 d0 ho0
    obtain ⟨r10, r11⟩ := hd bx.2 d1 ho1
    let DD : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := ContinuousLinearMap.pi ![d0, d1]
    have hf : HasFDerivAt F DD x := by
      apply hasFDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact hd0
      · exact hd1
    refine ⟨DD, hf, ?_⟩
    have rE00 : Encloses s (defect s N D bx 0 0) (1 + -(P 0 0 * d0 (Pi.single 0 1) + P 0 1 * d1 (Pi.single 0 1))) :=
      encloses_add hs ro (encloses_neg hs (lin 0 r00 r10))
    have rE01 : Encloses s (defect s N D bx 0 1) (-(P 0 0 * d0 (Pi.single 1 1) + P 0 1 * d1 (Pi.single 1 1))) :=
      encloses_neg hs (lin 0 r01 r11)
    have rE10 : Encloses s (defect s N D bx 1 0) (-(P 1 0 * d0 (Pi.single 0 1) + P 1 1 * d1 (Pi.single 0 1))) :=
      encloses_neg hs (lin 1 r00 r10)
    have rE11 : Encloses s (defect s N D bx 1 1) (1 + -(P 1 0 * d0 (Pi.single 1 1) + P 1 1 * d1 (Pi.single 1 1))) :=
      encloses_add hs ro (encloses_neg hs (lin 1 r01 r11))
    intro i
    fin_cases i
    · simpa [preMap, DD, sub_eq_add_neg] using rowb rE00 rE01 fe00 fe01 he0
    · simpa [preMap, DD, sub_eq_add_neg] using rowb rE10 rE11 fe10 fe11 he1

end Atiyah.Newton

/-! ### `Atiyah`: Certificate -/

/-!
# The 46-point certificate

The witness is a half-turn symmetric helix: 23 base points

  `p_j = (sin((2j+1)θ), (2j+1)·b, cos((2j+1)θ))`,  `j = 0, …, 22`,

followed by their images under the half-turn `(x, y, z) ↦ (-x, -y, z)`, with twist `tan(θ/2) = a`
and rise `b` given below to 76 and 75 decimal digits. Point `17` and its mate are then displaced by a
common parameter `(y₀, 0, y₁)` (mate: `(-y₀, 0, y₁)`), and the Schur residual of the even coefficient
block (column `0` against columns `1 … 22` on the rows other than `17`) is a map `ℝ² → ℝ²` of the
parameters. The certificate shows that it vanishes somewhere in the box of radius `10⁻⁴⁰` around `0`:
the block is evaluated in 320-bit fixed-point interval arithmetic, once at the centre and once with
derivatives over the whole box, eliminated with the recorded pivots, and the Newton–Kantorovich
conditions of `Newton.check` are verified by the kernel.

The real configuration takes the midpoints of the computed coordinate intervals, so that every point
has exact rational coordinates except the moving pair, whose displacement is the zero found.
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Certificate

open Fixed

/-! ## The data -/

/-- The fixed-point scale: integers stand for multiples of `2⁻³²⁰`. -/
def s : ℤ := 2^320

/-- Twist: `a = twistNum / 10^76` with `tan(θ/2) = a`. -/
def twistNum : ℤ := 685930529198825463380874179177993836428333332312773298096071048879689764276

/-- Rise: `b = riseNum / 10^75`. -/
def riseNum : ℤ := 301899619823684910039407341117171786396603682459437763370865376869900723964

def twist : Ival := ofRat s twistNum (10^76)

def rise : Ival := ofRat s riseNum (10^75)

/-- Pivot rows of the 22 elimination stages. -/
def pivots : List ℕ := [9,11,7,14,12,5,16,18,10,21,12,15,19,16,21,20,17,21,19,20,21,21]

/-- Row scalings `2^-rowScale[i]` and column scalings `2^-colScale[k]` of the even block. -/
def rowScale : List ℕ := [123,124,124,123,122,121,121,121,122,122,124,126,129,133,136,140,145,150,155,160,166,173,180]

def colScale : List ℕ := [0,4,8,11,13,15,17,18,19,20,20,20,20,20,20,19,18,16,14,12,10,6,2]

/-- The moving point. -/
abbrev mov : ℕ := 17

/-- Number of base points. -/
abbrev m : ℕ := 23

/-! ## The points -/

/-- `e^{iθ} = ((1 - a²)/(1 + a²), 2a/(1 + a²))`. -/
def unit : Cval :=
  let den := inv s (add (ofRat s 1 1) (mul s twist twist))
  (mul s (sub (ofRat s 1 1) (mul s twist twist)) den, mul s (mul s (ofRat s 2 1) twist) den)

/-- The base points `(Im w, (2j+1)·b, Re w)` with `w = e^{i(2j+1)θ}`. -/
def basePoints : List Cval.Point :=
  ((List.range m).foldl (fun (st : Cval × List Cval.Point) j =>
      (Cval.mul s st.1 (Cval.mul s unit unit), (st.1.2, mul s (ofRat s (2*(j:ℤ)+1) 1) rise, st.1.1) :: st.2))
    (unit, [])).2.reverse

/-- All 46 points: the base points and their half-turn images. -/
def allPoints : List Cval.Point := basePoints ++ basePoints.map (fun p => (neg p.1, neg p.2.1, p.2.2))

/-! ## The computation -/

/-- The constant rows, in plain interval arithmetic. -/
def constantRows : List (List Cval) := Cval.constantRows s m mov allPoints

/-- The points with the moving pair displaced by the box of radius `r/10^40` (`r = 0`: the centre). -/
def movedPoints (r : ℕ) : List Cdual.Point :=
  Cdual.movePair s m mov (Dual.coordinate₀ s r (10^40)) (Dual.coordinate₁ s r (10^40)) (allPoints.map Cdual.Point.ofCval)

/-- The even block over the box of radius `r/10^40`, from constant rows `C`. -/
def blockOf (C : List (List Cval)) (r : ℕ) : List (List Cdual) :=
  Cdual.block s m mov rowScale colScale (movedPoints r) (C.map (List.map Cdual.ofCval))

def block (r : ℕ) : List (List Cdual) := blockOf constantRows r

/-- The rows other than `mov`, as the system `[columns 1 … 22 | column 0]`. -/
def rowIds : List ℕ := (List.range m).filter (· != mov)

/-- The eliminated system of a block, followed by the row of the moving point. -/
def tableOf (B : List (List Cdual)) : List (List Cdual) :=
  LU.eliminate Cdual.sub (Cdual.mul s) (Cdual.inv s) (Cdual.zero s) pivots (m-1)
    (LU.system (Cdual.zero s) (m-1) rowIds B) ++ [B.getD mov []]

def table (r : ℕ) : List (List Cdual) := tableOf (block r)

/-- The Schur residual of the moving row of a table. -/
def schurOf (T : List (List Cdual)) : Cdual :=
  LU.residual Cdual.sub (Cdual.mul s) (Cdual.inv s) (Cdual.zero s) (m-1) (T.take (m-1)) (T.getD (m-1) [])

def schur (r : ℕ) : Cdual := schurOf (table r)

/-- Every diagonal entry of an eliminated box system is separated from zero. -/
def diagonalsOf (T : List (List Cdual)) : Bool :=
  (List.range (m-1)).all fun k =>
    let d := (T.getD k []).getD k (Cdual.zero s)
    nonzero d.1.1 || nonzero d.2.1

/-- The preconditioner: an approximate inverse of the Jacobian at the centre, entries over `10^8`. -/
def preconditionerNum (i j : ℕ) : ℤ :=
  if i = 0 then (if j = 0 then -1568197533577 else 511635929049) else (if j = 0 then -627448744629 else -448228210076)

def preconditionerDen : ℤ := 10^8

/-- The Newton–Kantorovich check of the centre residual and of the residual jet over the box. -/
def newtonOf (cen bx : Cdual) : Bool := Newton.check s preconditionerNum preconditionerDen cen bx

def diagonalsOk : Bool := diagonalsOf (table 1)

def newtonOk : Bool := newtonOf (schur 0) (schur 1)

/-- The whole certificate. -/
def ok : Bool := diagonalsOk && newtonOk

end Atiyah.Certificate

/-! ### `Atiyah`: Check/Data -/

/-!
# Snapshots of the computation

Each intermediate result of `Certificate` is computed by compiled code when this file is elaborated
(`eval%`) and stored as a literal; the kernel never sees the compiled code. The modules `Check.*`
re-verify, row by row, that the program produces each snapshot from the previous one.
-/

set_option maxRecDepth 100000

namespace Atiyah.Certificate

/-- The constant rows. -/
noncomputable def constantRowsData : List (List Cval) := eval% constantRows

/-- The even blocks over the centre (`0`) and the box (`1`). -/
noncomputable def blockData : List (List (List Cdual)) := eval% [block 0, block 1]

/-- The eliminated tables over the centre (`0`) and the box (`1`). -/
noncomputable def tableData : List (List (List Cdual)) := eval% [table 0, table 1]

end Atiyah.Certificate

/-! ### `Atiyah`: Check/ConstantRows -/

set_option maxHeartbeats 0

namespace Atiyah.Certificate

/-- The program produces the constant-row snapshot. -/
theorem constantRows_rows (i : Fin m) : constantRows.getD i.val [] = constantRowsData.getD i.val [] := by
  fin_cases i <;> decide +kernel

end Atiyah.Certificate

/-! ### `Atiyah`: Check/Block0 -/

set_option maxHeartbeats 0

namespace Atiyah.Certificate

/-- The program produces the centre block from the constant rows: one kernel evaluation per row. -/
theorem block_rows_0 (i : Fin m) :
    (blockOf constantRowsData 0).getD i.val [] = (blockData.getD 0 []).getD i.val [] := by
  fin_cases i <;> decide +kernel

end Atiyah.Certificate

/-! ### `Atiyah`: Check/Block1 -/

set_option maxHeartbeats 0

namespace Atiyah.Certificate

/-- The program produces the box block from the constant rows: one kernel evaluation per row. -/
theorem block_rows_1 (i : Fin m) :
    (blockOf constantRowsData 1).getD i.val [] = (blockData.getD 1 []).getD i.val [] := by
  fin_cases i <;> decide +kernel

end Atiyah.Certificate

/-! ### `Atiyah`: Check/Table0 -/

set_option maxHeartbeats 0

namespace Atiyah.Certificate

/-- Elimination produces the centre table from the centre block. -/
theorem table_rows_0 : ∀ i < m, (tableOf (blockData.getD 0 [])).getD i [] = (tableData.getD 0 []).getD i [] := by decide +kernel

end Atiyah.Certificate

/-! ### `Atiyah`: Check/Table1 -/

set_option maxHeartbeats 0

namespace Atiyah.Certificate

/-- Elimination produces the box table from the box block. -/
theorem table_rows_1 : ∀ i < m, (tableOf (blockData.getD 1 [])).getD i [] = (tableData.getD 1 []).getD i [] := by decide +kernel

end Atiyah.Certificate

/-! ### `Atiyah`: Check/Final -/

set_option maxHeartbeats 0

namespace Atiyah.Certificate

/-- The diagonal flags of the box table and the Newton–Kantorovich check of the two residuals. -/
theorem final_ok :
    (diagonalsOf (tableData.getD 1 []) && newtonOf (schurOf (tableData.getD 0 [])) (schurOf (tableData.getD 1 []))) = true := by
  decide +kernel

/-- Every stage has `m` rows. -/
theorem lengths :
    constantRows.length = m ∧ constantRowsData.length = m ∧
    (blockOf constantRowsData 0).length = m ∧ (blockOf constantRowsData 1).length = m ∧
    (blockData.getD 0 []).length = m ∧ (blockData.getD 1 []).length = m ∧
    (tableOf (blockData.getD 0 [])).length = m ∧ (tableOf (blockData.getD 1 [])).length = m ∧
    (tableData.getD 0 []).length = m ∧ (tableData.getD 1 []).length = m := by
  decide +kernel

end Atiyah.Certificate

/-! ### `Atiyah`: Check -/

/-!
# The kernel computation

`Certificate.ok` is verified by the Lean kernel in stages that follow the computation: the constant
rows, the two even blocks (centre and box), the two eliminated tables, and the final residuals with the
Newton–Kantorovich check. `Check.Data` holds the snapshots and `Check.*` the stage checks, which are
independent and are built in parallel; this file only assembles them.
-/

namespace Atiyah.Certificate

/-- Two lists of the same length that agree entrywise are equal. -/
theorem ext_of_getD {α : Type} {l₁ l₂ : List α} {n : ℕ} (d : α) (h₁ : l₁.length = n) (h₂ : l₂.length = n)
    (h : ∀ i < n, l₁.getD i d = l₂.getD i d) : l₁ = l₂ := by
  apply List.ext_getElem (h₁.trans h₂.symm)
  intro i hi₁ hi₂
  have := h i (h₁ ▸ hi₁)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂, Option.getD_some] using this

theorem ok_eq_true : ok = true := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ := lengths
  have hc : constantRows = constantRowsData := ext_of_getD [] l1 l2 fun i hi => constantRows_rows ⟨i, hi⟩
  have hb0 : block 0 = blockData.getD 0 [] := by rw [block, hc]; exact ext_of_getD [] l3 l5 fun i hi => block_rows_0 ⟨i, hi⟩
  have hb1 : block 1 = blockData.getD 1 [] := by rw [block, hc]; exact ext_of_getD [] l4 l6 fun i hi => block_rows_1 ⟨i, hi⟩
  have ht0 : table 0 = tableData.getD 0 [] := by rw [table, hb0]; exact ext_of_getD [] l7 l9 table_rows_0
  have ht1 : table 1 = tableData.getD 1 [] := by rw [table, hb1]; exact ext_of_getD [] l8 l10 table_rows_1
  rw [ok, diagonalsOk, newtonOk, schur, schur, ht0, ht1]
  exact final_ok

end Atiyah.Certificate

/-! ### `Atiyah`: Residual -/

/-!
# From the certificate to the column dependence

The real configuration takes the midpoints of the computed coordinate intervals and the exact heights
`(2j+1)·b`. The interval data enclose it (`points_enclosed`), hence the interval block, table and Schur
residual enclose their geometric counterparts over the box (`block_encloses_geom`, `table_encloses`,
`schur_encloses`). With the kernel-checked certificate, `Newton.zero_of_check` gives a zero of the
geometric Schur residual in the box (`geomSchur_zero`), and the exact elimination algebra turns it into
a column dependence of the even block there (`even_block_dependence`).
-/

set_option maxHeartbeats 5000000

namespace Atiyah.Certificate

open Fixed

/-! ## The real configuration -/

noncomputable section

/-- The midpoint of an interval. -/
def mid (v : Ival) : ℝ := ((v.1 : ℝ) + (v.2.1 : ℝ)) / (2 * (s : ℝ))

/-- The 46-point configuration: point `(i, 0)` has the midpoint coordinates of base point `i` and the
exact height `(2i+1)·b`; point `(i, 1)` is its half-turn image. -/
def configuration : Fin 23 × Fin 2 → EuclideanSpace ℝ (Fin 3) := fun i =>
  let p := basePoints.getD i.1.val (Cval.origin s)
  WithLp.toLp 2 ![(if i.2 = 0 then (1:ℝ) else -1) * mid p.1,
    (if i.2 = 0 then (1:ℝ) else -1) * (2*(i.1.val:ℝ)+1) * ((riseNum : ℝ) / ((10^75 : ℤ) : ℝ)), mid p.2.2]

/-- The points as a list: base points, then their mates. -/
def points : List (EuclideanSpace ℝ (Fin 3)) :=
  List.ofFn (fun i : Fin 23 => configuration (i, 0)) ++ List.ofFn (fun i : Fin 23 => configuration (i, 1))

/-- The points as constant functions of the moving parameters. -/
def qts : List ((Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 3)) := points.map (fun p _ => p)

/-- The geometric even block of the moved configuration. -/
def geomBlock : List (List ((Fin 2 → ℝ) → ℂ)) :=
  Geom.block m mov rowScale colScale (Geom.movePair m mov qts) (Geom.constantRows m mov qts)

def geomTable : List (List ((Fin 2 → ℝ) → ℂ)) :=
  LU.eliminate (· - ·) (· * ·) (·⁻¹) 0 pivots (m-1) (LU.system 0 (m-1) rowIds geomBlock) ++ [geomBlock.getD mov []]

/-- The geometric Schur residual of the moving row, as a function of the moving parameters. -/
def geomSchur : (Fin 2 → ℝ) → ℂ :=
  LU.residual (· - ·) (· * ·) (·⁻¹) 0 (m-1) (geomTable.take (m-1)) (geomTable.getD (m-1) [])

end

/-- Enclosure at the parameters `y`, with derivatives along the two coordinate directions. -/
abbrev Encl (y : Fin 2 → ℝ) : Cdual → ((Fin 2 → ℝ) → ℂ) → Prop := Cdual.Encloses s y (Pi.single 0 1) (Pi.single 1 1)

theorem s_pos : 0 < s := by unfold s; positivity

/-! ## Enclosures -/

/-- The computed base point intervals are ordered and enclose the exact heights. -/
theorem basePoints_ordered : ∀ i : Fin 23,
    let p := basePoints.getD i.val (Cval.origin s)
    p.1.1 ≤ p.1.2.1 ∧ p.2.2.1 ≤ p.2.2.2.1 ∧
    p.2.1.1 * 10^75 ≤ (2*(i.val:ℤ)+1) * riseNum * s ∧ (2*(i.val:ℤ)+1) * riseNum * s ≤ p.2.1.2.1 * 10^75 := by
  decide +kernel

theorem points_enclosed : List.Forall₂ (Cval.Point.Encloses s) allPoints points :=
  (Atiyah.Facts.cert_point_lists_enclose 23 s riseNum (10^75) s_pos (by decide) (by decide)
    basePoints (Cval.origin s) (by decide) basePoints_ordered).2.2

theorem block_encloses_geom (r : ℕ) :
    ∀ y ∈ Metric.closedBall (0 : Fin 2 → ℝ) ((r : ℝ) / (10^40 : ℝ)), List.Forall₂ (List.Forall₂ (Encl y)) (block r) geomBlock := by
  intro y hy
  exact Atiyah.block_encloses s r (10^40) s_pos (by positivity) m mov rowScale colScale allPoints points points_enclosed y
    (by simpa only [Int.cast_natCast, Int.cast_pow, Int.cast_ofNat] using hy)

theorem table_encloses (r : ℕ) (y : Fin 2 → ℝ) (hy : y ∈ Metric.closedBall (0 : Fin 2 → ℝ) ((r : ℝ) / (10^40 : ℝ))) :
    List.Forall₂ (List.Forall₂ (Encl y)) (table r) geomTable := by
  have hb := block_encloses_geom r y hy
  have hz := Cdual.encloses_zero s_pos y (Pi.single 0 1) (Pi.single 1 1)
  have hsys : List.Forall₂ (List.Forall₂ (Encl y))
      (LU.system (Cdual.zero s) (m-1) rowIds (block r)) (LU.system 0 (m-1) rowIds geomBlock) := by
    unfold LU.system
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro i _
    apply List.rel_append
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      intro j _
      exact LU.forall₂_getD (LU.forall₂_getD hb List.Forall₂.nil i) hz (j+1)
    · exact List.Forall₂.cons (LU.forall₂_getD (LU.forall₂_getD hb List.Forall₂.nil i) hz 0) List.Forall₂.nil
  exact List.rel_append (LU.eliminate_encloses s_pos y _ _ (m-1) pivots hsys)
    (List.Forall₂.cons (LU.forall₂_getD hb List.Forall₂.nil mov) List.Forall₂.nil)

theorem schur_encloses (r : ℕ) (y : Fin 2 → ℝ) (hy : y ∈ Metric.closedBall (0 : Fin 2 → ℝ) ((r : ℝ) / (10^40 : ℝ))) :
    Encl y (schur r) geomSchur := by
  have ht := table_encloses r y hy
  unfold schur schurOf geomSchur
  exact LU.residual_encloses s_pos y _ _ (m-1) (List.forall₂_take (m-1) ht) (LU.forall₂_getD ht List.Forall₂.nil (m-1))

/-! ## The zero and the dependence -/

theorem pivots_ok : ∀ k < m-1, k ≤ pivots.getD k k ∧ pivots.getD k k < m-1 := by decide

theorem checks_ok : diagonalsOk = true ∧ newtonOk = true := by
  simpa only [ok, Bool.and_eq_true] using ok_eq_true

theorem diagonals_ok : ∀ k < m-1,
    let d := ((table 1).getD k []).getD k (Cdual.zero s)
    nonzero d.1.1 = true ∨ nonzero d.2.1 = true := by
  intro k hk
  have h := checks_ok.1
  simp only [diagonalsOk, diagonalsOf, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  exact h k hk

/-- The geometric Schur residual has a zero in the box of radius `10⁻⁴⁰`. -/
theorem geomSchur_zero : ∃ z ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ)), geomSchur z = 0 := by
  let F : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun y => ![(geomSchur y).re, (geomSchur y).im]
  have hcen := schur_encloses 0 0 (by simp)
  have hbox : ∀ y ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ)), Encl y (schur 1) geomSchur :=
    fun y hy => schur_encloses 1 y (by simpa using hy)
  have hcR : Encloses s (schur 0).1.1 (F 0 0) ∧ Encloses s (schur 0).2.1 (F 0 1) := by
    constructor
    · intro hflag
      exact ((hcen.1 hflag).choose_spec.2.1) hflag
    · intro hflag
      exact ((hcen.2 hflag).choose_spec.2.1) hflag
  have hbJ : ∀ y ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ)),
      Dual.JetEncloses s y (Pi.single 0 1) (Pi.single 1 1) (schur 1).1 (fun z => F z 0) ∧
      Dual.JetEncloses s y (Pi.single 0 1) (Pi.single 1 1) (schur 1).2 (fun z => F z 1) :=
    fun y hy => hbox y hy
  obtain ⟨z, hz, hz0⟩ := Newton.zero_of_check s_pos preconditionerNum preconditionerDen (by decide) (by decide)
    F (schur 0) (schur 1) hcR hbJ checks_ok.2
  exact ⟨z, hz, Complex.ext (congrFun hz0 0) (congrFun hz0 1)⟩

theorem geomTable_diagonals_nonzero (y : Fin 2 → ℝ) (hy : y ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ))) :
    ∀ k < m-1, ((geomTable.getD k []).getD k 0) y ≠ 0 := by
  intro k hk
  have ht := table_encloses 1 y (by simpa using hy)
  have hz := Cdual.encloses_zero s_pos y (Pi.single 0 1) (Pi.single 1 1)
  have he := LU.forall₂_getD (LU.forall₂_getD ht List.Forall₂.nil k) hz k
  intro heq
  rcases diagonals_ok k hk with hd | hd
  · exact ne_zero_of_nonzero s_pos (he.1 (valid_of_nonzero hd)).choose_spec.2.1 hd (congrArg Complex.re heq)
  · exact ne_zero_of_nonzero s_pos (he.2 (valid_of_nonzero hd)).choose_spec.2.1 hd (congrArg Complex.im heq)

/-- Column `0` of the geometric even block is a combination of the other columns at some parameter in
the box. -/
theorem even_block_dependence : ∃ z ∈ Metric.closedBall (0 : Fin 2 → ℝ) (1 / (10^40 : ℝ)), ∃ v : ℕ → ℂ,
    ∀ i < m, (∑ j ∈ Finset.range (m-1), ((geomBlock.getD i []).getD (j+1) 0) z * v j) = ((geomBlock.getD i []).getD 0 0) z := by
  obtain ⟨z, hz, hz0⟩ := geomSchur_zero
  exact ⟨z, hz, LU.column_dependence_of_residual (Fin 2 → ℝ) (m-1) mov rowIds pivots geomBlock z (by decide) (by decide)
    pivots_ok (geomTable_diagonals_nonzero z hz) hz0⟩

end Atiyah.Certificate

/-! ### `Atiyah`: Disproof -/

/-!
# Atiyah–Sutcliffe Conjecture 1 is false

The 46-point configuration of `Certificate` (the helix with its moving pair at the zero of the Schur
residual) is injective, and the column dependence of its even block (`even_block_dependence`) is a
linear dependence of its point polynomials (`block_dependence_counterexample`). This contradicts the
pinned statement `atiyah_sutcliffe_conjecture_one`.
-/

set_option maxHeartbeats 5000000

open Atiyah.Certificate

/-- The formal disproof target of the study manifest, verbatim. -/
theorem atiyah_sutcliffe_conjecture_one_disproof :
    ¬ ∀ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 3)), Function.Injective x →
    LinearIndependent ℂ
        ((fun (directionLift : EuclideanSpace ℝ (Fin 3) → ℂ × ℂ)
            (linearFactor : ℂ × ℂ → MvPolynomial (Fin 2) ℂ) =>
            fun i : Fin n => ∏ j ∈ Finset.univ.erase i, linearFactor (directionLift (x j - x i)))
          (fun v => if ‖v‖ - v 2 = 0 then (1, 0)
            else (((v 0 : ℂ) + (v 1 : ℂ) * Complex.I) / (‖v‖ - v 2 : ℝ), 1))
          (fun zw => MvPolynomial.C zw.1 * MvPolynomial.X 0 - MvPolynomial.C zw.2 * MvPolynomial.X 1)) := by
  classical
  intro hAll
  obtain ⟨y, hy, v, hv⟩ := even_block_dependence
  let b : ℝ := (riseNum : ℝ) / ((10^75 : ℤ) : ℝ)
  have hb : 0 < b := by unfold b riseNum; positivity
  have hmate : ∀ i : Fin 23, configuration (i, 1) =
      WithLp.toLp 2 ![-configuration (i, 0) 0, -configuration (i, 0) 1, configuration (i, 0) 2] := by
    intro i
    ext k
    fin_cases k
    · simp [configuration]
    · simp [configuration]; ring
    · simp [configuration]
  have hheight : ∀ i : Fin 23, configuration (i, 0) 1 = (2 * (i.val : ℝ) + 1) * b := by
    intro i
    simp [configuration, b]
  have h := Atiyah.Facts.block_dependence_counterexample configuration b hb hmate hheight rowScale colScale rfl
  obtain ⟨hinj, hdep⟩ := h y v hv
  exact hdep (hAll 46 _ hinj)


/-! ## The conjecture of the repository is false -/

namespace AtiyahSutcliffeDisproof

/-- Atiyah–Sutcliffe Conjecture 1, `AtiyahSutcliffe.conjecture_one` of formal-conjectures, is false: the
46-point configuration of `Atiyah.Certificate` is injective and its point polynomials are linearly
dependent. formal-conjectures records this statement as `AtiyahSutcliffe.conjecture_one_false` (PR #6966);
it is proved here under the file's own namespace so that the file checks against the repository both
before and after that PR. -/
theorem conjecture_one_false :
    ¬ ∀ {n : ℕ} (x : Fin n → AtiyahSutcliffe.Point), Function.Injective x →
      LinearIndependent ℂ (AtiyahSutcliffe.pointPolynomial x) :=
  fun h => atiyah_sutcliffe_conjecture_one_disproof fun _ x hx => h x hx

end AtiyahSutcliffeDisproof

#print axioms AtiyahSutcliffeDisproof.conjecture_one_false
