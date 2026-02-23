/-
  Bohm-Sontacchi 1978 -- Proposition 4

  PROPOSITION 4. For all x in Z and for all (n_0, n_1, ..., n_m) in N^{m+1} we have:

    u^n(x) = (3^m * x + sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}) / 2^n

  where v_i = i + sum_{j=0}^{i} n_j and n = v_m.

  This specializes Proposition 1 to f(x) = x/2, g(x) = (3x+1)/2,
  i.e., a = 1/2, b = 0, c = 3/2, d = 1/2.
-/
import BohmSontacchi.Defs

namespace BohmSontacchi

/-! ## Compatibility of schedules with Collatz trajectories -/

/-- A schedule `s` is compatible with the trajectory of `x` under `u` if
  at each step `i < s.n`, the intermediate value `collatzU_iterate i x` is odd
  exactly when `i` appears in the schedule's v-values. That is, the schedule
  correctly records which steps are "odd" (g-branch) applications. -/
def Schedule.CompatibleWith (s : Schedule) (x : ℤ) : Prop :=
  ∀ i : ℕ, i < s.n →
    (i ∈ s.vals ↔ collatzU_iterate i x % 2 = 1)

/-! ## Key rational-valued identities

  When working over ℚ, the Collatz function has clean forms:
  - f(x) = x/2 corresponds to a = 1/2, b = 0
  - g(x) = (3x+1)/2 corresponds to c = 3/2, d = 1/2

  These lemmas express collatzU in ℚ without integer division rounding. -/

/-- Cast of collatzU to ℚ when x is even:  u(x) = x / 2  over ℚ. -/
lemma collatzU_cast_even {x : ℤ} (hx : x % 2 = 0) :
    (collatzU x : ℚ) = (x : ℚ) / 2 := by
  rw [collatzU_even hx]
  have h2 : (2 : ℤ) ∣ x := Int.dvd_of_emod_eq_zero hx
  obtain ⟨c, hc⟩ := h2
  subst hc
  simp [Int.mul_ediv_cancel_left c (by norm_num : (2:ℤ) ≠ 0)]

/-- Cast of collatzU to ℚ when x is odd:  u(x) = (3x + 1) / 2  over ℚ. -/
lemma collatzU_cast_odd {x : ℤ} (hx : x % 2 = 1) :
    (collatzU x : ℚ) = (3 * (x : ℚ) + 1) / 2 := by
  rw [collatzU_odd' hx]
  have h2 : (2 : ℤ) ∣ (3 * x + 1) := by
    rw [Int.dvd_iff_emod_eq_zero]; omega
  obtain ⟨c, hc⟩ := h2
  rw [hc, Int.mul_ediv_cancel_left c (by norm_num : (2:ℤ) ≠ 0)]
  have : (2 * c : ℤ) = 3 * x + 1 := hc.symm
  have := congr_arg (Int.cast : ℤ → ℚ) this
  push_cast at this
  linarith

/-! ## Helper lemmas for the proof of Proposition 4 -/

/-- listNumSum of appending a singleton: listNumSum (v ++ [k]) = 3 * listNumSum v + 2^k. -/
private lemma listNumSum_append_singleton (v : List ℕ) (k : ℕ) :
    listNumSum (v ++ [k]) = 3 * listNumSum v + 2 ^ k := by
  induction v with
  | nil => simp [listNumSum]
  | cons a rest ih =>
    simp only [List.cons_append, listNumSum, List.length_append, List.length_cons,
               List.length_nil]
    rw [ih]
    ring

/-- If a sorted list has all elements < n+1 and n is in the list,
    then the last element is n. -/
private lemma sorted_last_eq {v : List ℕ} {n : ℕ}
    (hne : v ≠ [])
    (hsorted : v.Pairwise (· < ·))
    (hbound : ∀ i, i ∈ v → i < n + 1)
    (hmem : n ∈ v) :
    v.getLast hne = n := by
  -- The last element L satisfies L < n+1, i.e. L ≤ n
  have hlast_mem := v.getLast_mem hne
  have hL_bound : v.getLast hne < n + 1 := hbound _ hlast_mem
  -- We show n ≤ L: if n is in dropLast, then n < L by Pairwise
  -- If n = L, done.
  suffices n ≤ v.getLast hne by omega
  -- n ∈ v, so either n ∈ v.dropLast or n = v.getLast hne
  rw [← List.dropLast_append_getLast hne] at hmem
  rcases List.mem_append.mp hmem with h | h
  · -- n ∈ v.dropLast, so n < v.getLast hne
    exact le_of_lt (hsorted.rel_dropLast_getLast h)
  · -- n = v.getLast hne
    exact le_of_eq (List.mem_singleton.mp h)

/-- For a sorted list with last element n, elements of dropLast are < n. -/
private lemma mem_dropLast_lt {v : List ℕ} {n : ℕ}
    (hne : v ≠ [])
    (hsorted : v.Pairwise (· < ·))
    (hlast : v.getLast hne = n)
    (i : ℕ) (hi : i ∈ v.dropLast) : i < n := by
  have := hsorted.rel_dropLast_getLast hi
  rw [hlast] at this
  exact this

/-- For a sorted list with last element = n, membership in dropLast for i < n
    is equivalent to membership in v. -/
private lemma mem_dropLast_iff {v : List ℕ} {n : ℕ}
    (hne : v ≠ [])
    (hlast : v.getLast hne = n)
    (i : ℕ) (hi : i < n) : i ∈ v.dropLast ↔ i ∈ v := by
  constructor
  · exact fun h => List.dropLast_subset v h
  · intro h
    rw [← List.dropLast_append_getLast hne, hlast] at h
    rcases List.mem_append.mp h with h1 | h2
    · exact h1
    · simp at h2; omega

/-- Empty list has no elements less than 0. -/
private lemma list_empty_of_bound_zero {v : List ℕ}
    (hbound : ∀ i, i ∈ v → i < 0) : v = [] := by
  by_contra h
  have ⟨a, ha⟩ := List.exists_mem_of_ne_nil v h
  exact absurd (hbound a ha) (by omega)

/-! ## The core integer formula -/

/-- The core integer formula: 2^n * u^n(x) = 3^|v| * x + listNumSum v.
    This is proved by induction on n with a plain list v (not a Schedule). -/
theorem collatzU_iterate_int_formula (x : ℤ) (n : ℕ) (v : List ℕ)
    (hv_sorted : v.Pairwise (· < ·))
    (hv_bound : ∀ i, i ∈ v → i < n)
    (hcompat : ∀ i, i < n → (i ∈ v ↔ collatzU_iterate i x % 2 = 1)) :
    (2 : ℤ) ^ n * collatzU_iterate n x = 3 ^ v.length * x + listNumSum v := by
  induction n generalizing v with
  | zero =>
    have hv_empty : v = [] := list_empty_of_bound_zero hv_bound
    subst hv_empty
    simp [collatzU_iterate, listNumSum]
  | succ n ih =>
    set y := collatzU_iterate n x with hy_def
    have hcompat_n : n ∈ v ↔ y % 2 = 1 := hcompat n (by omega)
    have hparity : y % 2 = 0 ∨ y % 2 = 1 := by omega
    rcases hparity with heven | hodd
    · -- Even case: n ∉ v, collatzU y = y / 2
      have hn_notin : n ∉ v := by rw [hcompat_n]; omega
      have hv_bound' : ∀ i, i ∈ v → i < n := by
        intro i hi
        have h1 := hv_bound i hi
        have h2 : i ≠ n := fun heq => by subst heq; exact hn_notin hi
        omega
      have hcompat' : ∀ i, i < n → (i ∈ v ↔ collatzU_iterate i x % 2 = 1) :=
        fun i hi => hcompat i (by omega)
      have ih_result := ih v hv_sorted hv_bound' hcompat'
      have hstep : collatzU_iterate (n + 1) x = y / 2 := by
        change collatzU y = y / 2
        exact collatzU_even heven
      rw [hstep]
      have hdvd : (2 : ℤ) ∣ y := Int.dvd_of_emod_eq_zero heven
      have hcancel : y / 2 * 2 = y := Int.ediv_mul_cancel hdvd
      calc (2 : ℤ) ^ (n + 1) * (y / 2)
          = 2 ^ n * (2 * (y / 2)) := by ring
        _ = 2 ^ n * y := by congr 1; linarith [hcancel]
        _ = 3 ^ v.length * x + listNumSum v := ih_result
    · -- Odd case: n ∈ v, collatzU y = (3*y+1)/2
      have hn_in : n ∈ v := hcompat_n.mpr hodd
      have hv_ne : v ≠ [] := fun h => by subst h; simp at hn_in
      have hlast : v.getLast hv_ne = n :=
        sorted_last_eq hv_ne hv_sorted hv_bound hn_in
      have hv_eq : v = v.dropLast ++ [n] := by
        conv_lhs => rw [← List.dropLast_append_getLast hv_ne]; rw [hlast]
      have hv'_sorted : v.dropLast.Pairwise (· < ·) :=
        List.Pairwise.sublist (List.dropLast_sublist v) hv_sorted
      have hv'_bound : ∀ i, i ∈ v.dropLast → i < n :=
        mem_dropLast_lt hv_ne hv_sorted hlast
      have hcompat' : ∀ i, i < n → (i ∈ v.dropLast ↔ collatzU_iterate i x % 2 = 1) := by
        intro i hi
        rw [mem_dropLast_iff hv_ne hlast i hi]
        exact hcompat i (by omega)
      have ih_result := ih v.dropLast hv'_sorted hv'_bound hcompat'
      have hstep : collatzU_iterate (n + 1) x = (3 * y + 1) / 2 := by
        change collatzU y = (3 * y + 1) / 2
        exact collatzU_odd' hodd
      rw [hstep]
      have h_len : v.length = v.dropLast.length + 1 := by
        rw [List.length_dropLast]
        have : 0 < v.length := List.length_pos_of_ne_nil hv_ne
        omega
      have h_numsum : listNumSum v = 3 * listNumSum v.dropLast + 2 ^ n := by
        conv_lhs => rw [hv_eq]
        exact listNumSum_append_singleton v.dropLast n
      have hdvd : (2 : ℤ) ∣ (3 * y + 1) := by
        rw [Int.dvd_iff_emod_eq_zero]; omega
      have hcancel : (3 * y + 1) / 2 * 2 = 3 * y + 1 := Int.ediv_mul_cancel hdvd
      calc (2 : ℤ) ^ (n + 1) * ((3 * y + 1) / 2)
          = 2 ^ n * (2 * ((3 * y + 1) / 2)) := by ring
        _ = 2 ^ n * (3 * y + 1) := by
            congr 1; linarith [hcancel]
        _ = 3 * (2 ^ n * y) + 2 ^ n := by ring
        _ = 3 * (3 ^ v.dropLast.length * x + listNumSum v.dropLast) + 2 ^ n := by
            rw [ih_result]
        _ = 3 ^ (v.dropLast.length + 1) * x + (3 * listNumSum v.dropLast + 2 ^ n) := by
            ring
        _ = 3 ^ v.length * x + listNumSum v := by
            rw [← h_len, ← h_numsum]

/-! ## Proposition 4: iteration formula -/

/-- **Proposition 4** (Bohm-Sontacchi 1978).
  For any integer `x` and any schedule `s` that is compatible with the trajectory
  of `x` under the Collatz function `u`, the `s.n`-th iterate of `u` applied to `x`
  equals the formula:

    u^n(x) = (3^m * x + sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}) / 2^n

  where m = s.m is the number of odd steps (g-applications), n = s.n is the total
  number of steps, and the v_k are the positions of the odd steps.

  In other words, `(collatzU_iterate s.n x : Q)` equals `collatzIterFormula s x`. -/
theorem prop4 (x : ℤ) (s : Schedule) (hcompat : s.CompatibleWith x) :
    (collatzU_iterate s.n x : ℚ) = collatzIterFormula s x := by
  have hint := collatzU_iterate_int_formula x s.n s.vals s.strictMono
    (fun i hi => s.bound i hi) (fun i hi => hcompat i hi)
  -- hint : 2^s.n * collatzU_iterate s.n x = 3^s.vals.length * x + listNumSum s.vals
  -- Goal: (collatzU_iterate s.n x : ℚ) = collatzIterFormula s x
  -- collatzIterFormula s x = ((3^s.m * x + s.numSum : ℤ) : ℚ) / ((2^s.n : ℤ) : ℚ)
  -- s.m = s.vals.length, s.n = s.total, s.numSum = listNumSum s.vals
  change (collatzU_iterate s.total x : ℚ) =
    ((3 ^ s.vals.length * x + listNumSum s.vals : ℤ) : ℚ) / ((2 ^ s.total : ℤ) : ℚ)
  rw [eq_comm, div_eq_iff]
  · push_cast
    have : (2 : ℤ) ^ s.total * collatzU_iterate s.total x =
      3 ^ s.vals.length * x + listNumSum s.vals := hint
    have h := congr_arg (Int.cast : ℤ → ℚ) this
    push_cast at h ⊢
    linarith
  · exact_mod_cast pow_ne_zero s.total (by norm_num : (2 : ℤ) ≠ 0)

/-- A useful corollary: the iteration formula yields an integer when the
  schedule is compatible, since collatzU_iterate always produces an integer. -/
theorem prop4_integer (x : ℤ) (s : Schedule) (hcompat : s.CompatibleWith x) :
    ∃ y : ℤ, (y : ℚ) = collatzIterFormula s x ∧ y = collatzU_iterate s.n x := by
  exact ⟨collatzU_iterate s.n x, prop4 x s hcompat, rfl⟩

end BohmSontacchi
