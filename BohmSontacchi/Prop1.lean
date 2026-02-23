/-
  Bohm-Sontacchi 1978 -- Proposition 1

  PROPOSITION 1. For all x in Q and all (n_0, n_1, ..., n_m) in N^{m+1} we have:

    f^{n_m} g f^{n_{m-1}} g ... f^{n_1} g f^{n_0}(x)
      = c^m * a^{n-m} * x
        + b * (a^{n_m} - 1)/(a - 1)
        + sum_{j=1}^{m} a^{sum_{i=j}^{m} n_i} * c^{m-j}
          * (b*c*(a^{n_{j-1}} - 1)/(a - 1) + d)

    where n = m + sum_{j=0}^{m} n_j.

  We formalize this by defining the composed function recursively and proving
  that it is affine (of the form alpha * x + beta) where
  alpha = c^m * a^{n_0 + n_1 + ... + n_m}.
-/
import BohmSontacchi.Defs

namespace BohmSontacchi

/-! ## The composed function f^{n_m} g f^{n_{m-1}} g ... f^{n_1} g f^{n_0}

We define `composeFromRight a b c d n0 gs x` which applies f^{n0} first,
then for each n_j in gs, applies g then f^{n_j}.
The list `gs = [n_1, ..., n_m]` encodes the exponents after each
g-application, from inner to outer. -/

/-- Build the composition from the right.
    `composeFromRight a b c d n0 gs x` applies f^{n0} first, then for each
    n_j in gs, applies g then f^{n_j}. -/
def composeFromRight (a b c d : ℚ) (n0 : ℕ) : List ℕ → ℚ → ℚ
  | [], x => iterateAffine a b n0 x
  | nj :: rest, x =>
    composeFromRight a b c d nj rest (affineG c d (iterateAffine a b n0 x))

/-! ## Affine form of iterated f -/

/-- The constant term of f^n: iterateAffine a b n x = a^n * x + iterateAffine_const a b n. -/
def iterateAffine_const (a b : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => a * iterateAffine_const a b n + b

/-- f^n(x) = a^n * x + iterateAffine_const a b n. -/
theorem iterateAffine_eq (a b : ℚ) (n : ℕ) (x : ℚ) :
    iterateAffine a b n x = a ^ n * x + iterateAffine_const a b n := by
  induction n with
  | zero => simp [iterateAffine, iterateAffine_const]
  | succ n ih =>
    simp only [iterateAffine, iterateAffine_const, affineF]
    rw [ih]
    ring

/-! ## The composition is affine

The main theorem of Proposition 1: every composition of the form
f^{n_m} g f^{n_{m-1}} g ... g f^{n_0} is an affine function of x.

We prove this by induction on the list of g-applications, generalizing
over the initial exponent n0. -/

/-- **Proposition 1** (key theorem): The composition is affine.
    There exist alpha, beta in Q such that
    composeFromRight a b c d n0 gs x = alpha * x + beta for all x. -/
theorem proposition1_is_affine (a b c d : ℚ) (n0 : ℕ) (gs : List ℕ) :
    ∃ α β : ℚ,
      ∀ x : ℚ, composeFromRight a b c d n0 gs x = α * x + β := by
  induction gs generalizing n0 with
  | nil =>
    exact ⟨a ^ n0, iterateAffine_const a b n0,
      fun x => iterateAffine_eq a b n0 x⟩
  | cons nj rest ih =>
    obtain ⟨α', β', hαβ⟩ := ih nj
    use α' * c * a ^ n0
    use α' * (c * iterateAffine_const a b n0 + d) + β'
    intro x
    simp only [composeFromRight]
    rw [hαβ]
    simp only [affineG, iterateAffine_eq]
    ring

/-! ## The slope formula

The slope (leading coefficient) of the composed map with exponents
[n_0, n_1, ..., n_m] (where there are m g-applications) equals
  alpha = c^m * a^{n_0 + n_1 + ... + n_m}

We prove this by extracting the slope from the affine representation. -/

/-- Compute the slope and intercept simultaneously, matching
    composeFromRight's recursion structure.
    Returns (alpha, beta) such that
    composeFromRight a b c d n0 gs x = alpha * x + beta. -/
def composeCoeffs' (a b c d : ℚ) : ℕ → List ℕ → ℚ × ℚ
  | n0, [] => (a ^ n0, iterateAffine_const a b n0)
  | n0, nj :: rest =>
    -- f^{n0} has coefficients (a^{n0}, iterConst n0)
    -- g . f^{n0} has coefficients (c * a^{n0}, c * iterConst n0 + d)
    -- Then compose with (nj, rest) applied to that result
    let (α_inner, β_inner) := composeCoeffs' a b c d nj rest
    -- composeFromRight nj rest y = α_inner * y + β_inner
    -- where y = g(f^{n0}(x)) = c * a^{n0} * x + (c * iterConst n0 + d)
    -- So the total is α_inner * (c * a^{n0} * x + (c * iterConst n0 + d)) + β_inner
    --   = (α_inner * c * a^{n0}) * x + (α_inner * (c * iterConst n0 + d) + β_inner)
    (α_inner * c * a ^ n0,
     α_inner * (c * iterateAffine_const a b n0 + d) + β_inner)

/-- Correctness of composeCoeffs'. -/
theorem composeFromRight_eq_composeCoeffs'
    (a b c d : ℚ) (n0 : ℕ) (gs : List ℕ) (x : ℚ) :
    composeFromRight a b c d n0 gs x =
      (composeCoeffs' a b c d n0 gs).1 * x +
      (composeCoeffs' a b c d n0 gs).2 := by
  induction gs generalizing n0 x with
  | nil =>
    simp only [composeFromRight, composeCoeffs']
    exact iterateAffine_eq a b n0 x
  | cons nj rest ih =>
    simp only [composeFromRight, composeCoeffs']
    rw [ih]
    simp only [affineG, iterateAffine_eq]
    ring

/-- Helper: foldl of addition distributes. -/
private theorem foldl_add_comm (ns : List ℕ) (a b : ℕ) :
    ns.foldl (· + ·) (a + b) = a + ns.foldl (· + ·) b := by
  induction ns generalizing a b with
  | nil => simp
  | cons n rest ih =>
    simp only [List.foldl_cons]
    rw [show a + b + n = a + (b + n) from by omega]
    exact ih a (b + n)

/-- foldl of addition with nonzero start. -/
private theorem foldl_add_start (ns : List ℕ) (k : ℕ) :
    ns.foldl (· + ·) k = k + ns.foldl (· + ·) 0 := by
  induction ns generalizing k with
  | nil => simp
  | cons n rest ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih, ih n]
    omega

/-- Sum of exponents helper. -/
private theorem sumExponents_cons (n0 nj : ℕ) (rest : List ℕ) :
    n0 + (nj :: rest).foldl (· + ·) 0 =
    nj + rest.foldl (· + ·) 0 + n0 := by
  simp only [List.foldl_cons, Nat.zero_add]
  rw [foldl_add_start]
  omega

/-- The slope of composeCoeffs' equals c^m * a^{n_0 + n_1 + ... + n_m}. -/
theorem composeCoeffs'_slope_eq (a b c d : ℚ) (n0 : ℕ) (gs : List ℕ) :
    (composeCoeffs' a b c d n0 gs).1 =
      c ^ gs.length * a ^ (n0 + gs.foldl (· + ·) 0) := by
  induction gs generalizing n0 with
  | nil => simp [composeCoeffs']
  | cons nj rest ih =>
    simp only [composeCoeffs', List.length_cons]
    rw [ih]
    rw [sumExponents_cons, pow_succ, pow_add]
    ring

/-! ## Proposition 1: Summary statements -/

/-- Base case: with no g-applications, the result is just f^{n_0}(x). -/
theorem proposition1_base (a b c d : ℚ) (n0 : ℕ) (x : ℚ) :
    composeFromRight a b c d n0 [] x = iterateAffine a b n0 x := by
  simp [composeFromRight]

/-- Inductive step: one more g-application.
    composeFromRight a b c d n0 (nj :: rest) x
      = composeFromRight a b c d nj rest (g(f^{n0}(x))) -/
theorem proposition1_step (a b c d : ℚ) (n0 nj : ℕ) (rest : List ℕ)
    (x : ℚ) :
    composeFromRight a b c d n0 (nj :: rest) x =
      composeFromRight a b c d nj rest
        (affineG c d (iterateAffine a b n0 x)) := by
  simp [composeFromRight]

/-- **Proposition 1** (slope formula).
    The composition f^{n_m} g ... g f^{n_0} equals
    (c^m * a^{sum n_i}) * x + beta for some beta.

    Here m = gs.length (the number of g-applications) and the sum
    is over all exponents n_0, n_1, ..., n_m. -/
theorem proposition1_slope (a b c d : ℚ) (n0 : ℕ) (gs : List ℕ)
    (x : ℚ) :
    ∃ β : ℚ,
      composeFromRight a b c d n0 gs x =
        c ^ gs.length * a ^ (n0 + gs.foldl (· + ·) 0) * x + β := by
  use (composeCoeffs' a b c d n0 gs).2
  rw [composeFromRight_eq_composeCoeffs']
  rw [composeCoeffs'_slope_eq]

end BohmSontacchi
