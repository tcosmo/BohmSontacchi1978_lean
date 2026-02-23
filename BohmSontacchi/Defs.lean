/-
  Böhm-Sontacchi 1978: Core definitions for the formalization.

  This file defines:
  - The generalized piecewise-linear iteration (class L)
  - The Collatz-like function u
  - Iteration, cycles, and the key sequences v_i
-/
import Mathlib.Tactic

namespace BohmSontacchi

/-! ## Part I: Generic piecewise-linear functions over ℚ (class L) -/

/-- The "f" branch: f(x) = a*x + b. -/
def affineF (a b : ℚ) (x : ℚ) : ℚ := a * x + b

/-- The "g" branch: g(x) = c*x + d. -/
def affineG (c d : ℚ) (x : ℚ) : ℚ := c * x + d

/-- Iterate f n times: f^n(x) = a^n * x + b*(a^n - 1)/(a - 1).
    We define it recursively for simplicity. -/
def iterateAffine (a b : ℚ) : ℕ → ℚ → ℚ
  | 0, x => x
  | n + 1, x => affineF a b (iterateAffine a b n x)

/-! ## Part II: The Collatz function u -/

/-- The compressed Collatz function u : ℤ → ℤ.
  u(x) = x/2 if x is even, (3x+1)/2 if x is odd.
  (This is the "shortcut" Collatz map used in the paper.) -/
def collatzU (x : ℤ) : ℤ :=
  if x % 2 = 0 then x / 2 else (3 * x + 1) / 2

/-- Iterate u n times. -/
def collatzU_iterate : ℕ → ℤ → ℤ
  | 0, x => x
  | n + 1, x => collatzU (collatzU_iterate n x)

/-- x belongs to a cycle of length n under u. -/
def isCycleOfU (n : ℕ) (x : ℤ) : Prop :=
  0 < n ∧ collatzU_iterate n x = x

/-- The set U: integers that eventually reach 1. -/
def reachesOne (x : ℤ) : Prop :=
  ∃ n : ℕ, collatzU_iterate n x = 1

/-! ## Basic properties of the Collatz function -/

/-- u applied to an even integer halves it. -/
lemma collatzU_even {x : ℤ} (hx : x % 2 = 0) : collatzU x = x / 2 := by
  unfold collatzU; simp [hx]

/-- u applied to an odd integer applies (3x+1)/2 (negation form). -/
lemma collatzU_odd {x : ℤ} (hx : ¬ (x % 2 = 0)) :
    collatzU x = (3 * x + 1) / 2 := by
  unfold collatzU; simp [hx]

/-- u applied to an odd integer (with positive parity form). -/
lemma collatzU_odd' {x : ℤ} (hx : x % 2 = 1) :
    collatzU x = (3 * x + 1) / 2 := by
  exact collatzU_odd (by omega)

/-! ## Part III: Schedules and formulas -/

/-- Recursive definition of the numerator sum for a plain list of positions.
  listNumSum [v₀, v₁, ..., v_{m-1}] = ∑_{k=0}^{m-1} 3^{m-k-1} · 2^{v_k} -/
def listNumSum : List ℕ → ℤ
  | [] => 0
  | v :: rest => 3 ^ rest.length * 2 ^ v + listNumSum rest

/-- A "schedule" is a strictly increasing list of naturals
  v₀ < v₁ < ... < v_{m-1} with m ≥ 1, encoding which steps apply g.
  The total number of steps is n (a separate field, satisfying v_k < n for all k).
  We store the list of v-values. The number of g-applications is m = vals.length. -/
structure Schedule where
  vals : List ℕ
  total : ℕ
  nonempty : vals ≠ []
  strictMono : vals.Pairwise (· < ·)
  bound : ∀ i, i ∈ vals → i < total

/-- Number of g-applications. In the paper this is called m. -/
def Schedule.m (s : Schedule) : ℕ := s.vals.length

/-- Total number of steps. -/
def Schedule.n (s : Schedule) : ℕ := s.total

/-- Helper: get the k-th v-value, with default 0. -/
def Schedule.v (s : Schedule) (k : ℕ) : ℕ :=
  s.vals.getD k 0

/-- The numerator sum: ∑_{k=0}^{m-1} 3^{m-k-1} · 2^{v_k},
    defined via the recursive listNumSum. -/
def Schedule.numSum (s : Schedule) : ℤ := listNumSum s.vals

/-- The cycle formula (*):
  x = (∑_{k=0}^{m-1} 3^{m-k-1} · 2^{v_k}) / (2^n - 3^m) -/
def cycleFormula (s : Schedule) : ℚ :=
  (s.numSum : ℚ) / ((2 ^ s.n - 3 ^ s.m : ℤ) : ℚ)

/-- The reaching-1 formula (**):
  x = (2^{v_m} - ∑_{k=0}^{m-1} 3^{m-k-1} · 2^{v_k}) / 3^m -/
def reachOneFormula (s : Schedule) : ℚ :=
  ((2 ^ s.n - s.numSum : ℤ) : ℚ) / ((3 ^ s.m : ℤ) : ℚ)

/-- The iteration formula for u^n(x) from Proposition 4:
  u^n(x) = (3^m · x + ∑_{k=0}^{m-1} 3^{m-k-1} · 2^{v_k}) / 2^n -/
def collatzIterFormula (s : Schedule) (x : ℤ) : ℚ :=
  ((3 ^ s.m * x + s.numSum : ℤ) : ℚ) / ((2 ^ s.n : ℤ) : ℚ)

end BohmSontacchi
