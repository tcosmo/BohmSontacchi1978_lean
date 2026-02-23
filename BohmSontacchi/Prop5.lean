/-
  Böhm-Sontacchi 1978 — Proposition 5
-/
import BohmSontacchi.Defs
import BohmSontacchi.Prop4

namespace BohmSontacchi

def oddSteps (x : ℤ) (n : ℕ) : List ℕ :=
  (List.range n).filter (fun i => decide (collatzU_iterate i x % 2 = 1))

lemma oddSteps_strictMono (x : ℤ) (n : ℕ) :
    (oddSteps x n).Pairwise (· < ·) := by
  unfold oddSteps; exact List.Pairwise.filter _ List.pairwise_lt_range

private lemma oddSteps_bound (x : ℤ) (n : ℕ) :
    ∀ i, i ∈ oddSteps x n → i < n := by
  intro i hi; unfold oddSteps at hi
  simp only [List.mem_filter, List.mem_range] at hi; exact hi.1

private lemma oddSteps_compat (x : ℤ) (n : ℕ) :
    ∀ i, i < n → (i ∈ oddSteps x n ↔ collatzU_iterate i x % 2 = 1) := by
  intro i hi; unfold oddSteps
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

private lemma pow2_ne_pow3 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (2 : ℤ) ^ n ≠ (3 : ℤ) ^ m := by
  intro h
  have h_nat : (2 : ℕ) ^ n = (3 : ℕ) ^ m := by exact_mod_cast h
  have h2_even : 2 ∣ (2 : ℕ) ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  have h3_odd : ¬ 2 ∣ (3 : ℕ) ^ m := by
    rw [(Nat.prime_iff.mp Nat.prime_two).dvd_pow_iff_dvd (by omega)]; omega
  exact h3_odd (h_nat ▸ h2_even)

/-! ## listNumSum lemmas -/

private lemma listNumSum_append (a b : List ℕ) :
    listNumSum (a ++ b) = 3 ^ b.length * listNumSum a + listNumSum b := by
  induction a with
  | nil => simp [listNumSum]
  | cons x rest ih =>
    simp only [List.cons_append, listNumSum, List.length_append]; rw [ih]; ring

private lemma listNumSum_tail_dvd (v : List ℕ) (k : ℕ)
    (hv_bound : ∀ i, i ∈ v → k + 1 ≤ i) :
    (2 : ℤ) ^ (k + 1) ∣ listNumSum v := by
  induction v with
  | nil => simp [listNumSum]
  | cons a rest ih =>
    simp only [listNumSum]
    apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply pow_dvd_pow
      exact hv_bound a List.mem_cons_self
    · exact ih (fun i hi => hv_bound i (List.mem_cons_of_mem _ hi))

private lemma three_pow_mod_two (n : ℕ) : (3 : ℤ) ^ n % 2 = 1 := by
  induction n with
  | zero => simp
  | succ m ih => omega

private lemma three_pow_two_pow_coprime (a b : ℕ) :
    IsCoprime ((3 : ℤ) ^ a) ((2 : ℤ) ^ b) := by
  apply IsCoprime.pow
  rw [Int.isCoprime_iff_gcd_eq_one]; decide

/-! ## Filter split for sorted lists -/

private lemma sorted_filter_split (v : List ℕ) (k : ℕ)
    (hv : v.Pairwise (· < ·)) :
    v = v.filter (· < k) ++ v.filter (fun i => ¬(i < k)) := by
  induction v with
  | nil => simp
  | cons a rest ih =>
    have hrest := hv.tail
    by_cases ha : a < k
    · simp only [List.filter_cons, ha, decide_true, ↓reduceIte, List.cons_append]
      exact congrArg (a :: ·) (ih hrest)
    · -- a ≥ k, so all of rest is also ≥ k
      have hall : ∀ b ∈ rest, ¬(b < k) := by
        intro b hb
        have := List.rel_of_pairwise_cons hv hb; omega
      have hfilt_nil : (a :: rest).filter (· < k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb; simp only [decide_eq_true_eq]
        rcases List.eq_or_mem_of_mem_cons hb with rfl | hb'
        · exact ha
        · exact hall b hb'
      have hfilt_neg : (a :: rest).filter (fun i => ¬(i < k)) = a :: rest := by
        rw [List.filter_eq_self]
        intro b hb; simp only [decide_eq_true_eq]
        rcases List.eq_or_mem_of_mem_cons hb with rfl | hb'
        · exact ha
        · exact hall b hb'
      rw [hfilt_nil, hfilt_neg, List.nil_append]

/-! ## Key parity lemma -/

private lemma schedule_compat_step (x : ℤ) (s : Schedule) (k : ℕ) (hk : k < s.n)
    (hx_rearr : (2 : ℤ) ^ s.n * x = 3 ^ s.vals.length * x + listNumSum s.vals)
    (hcompat_prefix : ∀ j, j < k → (j ∈ s.vals ↔ collatzU_iterate j x % 2 = 1)) :
    (k ∈ s.vals ↔ collatzU_iterate k x % 2 = 1) := by
  set pfx := s.vals.filter (· < k) with hpfx_def
  set tail := s.vals.filter (fun i => ¬(i < k)) with htail_def
  -- Prefix properties
  have hpfx_sorted : pfx.Pairwise (· < ·) := List.Pairwise.filter _ s.strictMono
  have hpfx_bound : ∀ j, j ∈ pfx → j < k := by
    intro j hj; simp only [hpfx_def, List.mem_filter, decide_eq_true_eq] at hj; exact hj.2
  have hpfx_compat : ∀ j, j < k → (j ∈ pfx ↔ collatzU_iterate j x % 2 = 1) := by
    intro j hj; constructor
    · intro hj_mem
      have : j ∈ s.vals := by
        simp only [hpfx_def, List.mem_filter, decide_eq_true_eq] at hj_mem; exact hj_mem.1
      exact (hcompat_prefix j hj).mp this
    · intro hodd
      simp only [hpfx_def, List.mem_filter, decide_eq_true_eq]
      exact ⟨(hcompat_prefix j hj).mpr hodd, hj⟩
  -- Prefix formula
  have hpfx_formula := collatzU_iterate_int_formula x k pfx hpfx_sorted hpfx_bound hpfx_compat
  -- s.vals = pfx ++ tail
  have hsplit : s.vals = pfx ++ tail := sorted_filter_split s.vals k s.strictMono
  have hlen : s.vals.length = pfx.length + tail.length := by rw [hsplit, List.length_append]
  have hnumSum_split : listNumSum s.vals =
      3 ^ tail.length * listNumSum pfx + listNumSum tail := by
    conv_lhs => rw [hsplit, listNumSum_append]
  -- Key equation
  have hkey : (3 : ℤ) ^ tail.length * (2 ^ k * collatzU_iterate k x) =
      2 ^ s.n * x - listNumSum tail := by
    have h1 : (3 : ℤ) ^ tail.length * (2 ^ k * collatzU_iterate k x) =
        3 ^ (pfx.length + tail.length) * x + 3 ^ tail.length * listNumSum pfx := by
      rw [hpfx_formula]; ring
    -- From h1, hx_rearr, hlen, hnumSum_split:
    -- h1: LHS = 3^(pfx.len + tail.len) * x + 3^tail.len * listNumSum pfx
    -- hx_rearr: 2^n * x = 3^s.vals.len * x + listNumSum s.vals
    -- hlen: s.vals.len = pfx.len + tail.len
    -- hnumSum_split: listNumSum s.vals = 3^tail.len * listNumSum pfx + listNumSum tail
    -- Subst hlen into hx_rearr:
    have h2 : (2 : ℤ) ^ s.n * x =
        3 ^ (pfx.length + tail.length) * x + listNumSum tail +
        3 ^ tail.length * listNumSum pfx := by
      rw [hlen] at hx_rearr; linarith [hnumSum_split]
    linarith
  -- Tail ≥ k
  have htail_ge : ∀ j, j ∈ tail → k ≤ j := by
    intro j hj; simp only [htail_def, List.mem_filter, decide_eq_true_eq] at hj; omega
  -- 2^{k+1} | 2^n * x
  have hdvd_2nx : (2 : ℤ) ^ (k + 1) ∣ 2 ^ s.n * x :=
    dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : k + 1 ≤ s.n)) x
  constructor
  · -- k ∈ s.vals → u^k(x) is odd
    intro hk_mem
    have hk_tail : k ∈ tail := by
      simp only [htail_def, List.mem_filter, decide_eq_true_eq]; exact ⟨hk_mem, by omega⟩
    have htail_sorted : tail.Pairwise (· < ·) := List.Pairwise.filter _ s.strictMono
    have htail_ne : tail ≠ [] := List.ne_nil_of_mem hk_tail
    obtain ⟨thd, trest, htail_eq⟩ := List.exists_cons_of_ne_nil htail_ne
    have hthd_eq : thd = k := by
      have hge : k ≤ thd := htail_ge thd (by rw [htail_eq]; exact List.mem_cons_self)
      have hle : thd ≤ k := by
        rw [htail_eq] at hk_tail
        rcases List.eq_or_mem_of_mem_cons hk_tail with h | h
        · omega
        · rw [htail_eq] at htail_sorted
          exact le_of_lt ((List.pairwise_cons.mp htail_sorted).1 k h)
      omega
    rw [hthd_eq] at htail_eq
    have htail_numsum : listNumSum tail =
        3 ^ trest.length * 2 ^ k + listNumSum trest := by
      rw [htail_eq]; simp [listNumSum]
    have htrest_bound : ∀ j, j ∈ trest → k + 1 ≤ j := by
      intro j hj; rw [htail_eq] at htail_sorted
      exact Nat.succ_le_of_lt ((List.pairwise_cons.mp htail_sorted).1 j hj)
    have hdvd_rest : (2 : ℤ) ^ (k + 1) ∣ listNumSum trest :=
      listNumSum_tail_dvd trest k htrest_bound
    -- Suppose even → contradiction
    by_contra hne; push_neg at hne
    have heven : collatzU_iterate k x % 2 = 0 := by
      rcases Int.emod_two_eq_zero_or_one (collatzU_iterate k x) with h | h <;> omega
    have hdvd_uk : (2 : ℤ) ∣ collatzU_iterate k x := Int.dvd_of_emod_eq_zero heven
    have hdvd_prod : (2 : ℤ) ^ (k + 1) ∣ 2 ^ k * collatzU_iterate k x := by
      rw [pow_succ]; exact mul_dvd_mul_left _ hdvd_uk
    have hdvd_lhs : (2 : ℤ) ^ (k + 1) ∣
        3 ^ tail.length * (2 ^ k * collatzU_iterate k x) :=
      dvd_mul_of_dvd_right hdvd_prod _
    rw [hkey] at hdvd_lhs
    have hdvd_tail : (2 : ℤ) ^ (k + 1) ∣ listNumSum tail := by
      have h1 := dvd_sub hdvd_2nx hdvd_lhs
      rwa [show (2 : ℤ) ^ s.n * x - (2 ^ s.n * x - listNumSum tail) =
        listNumSum tail from by ring] at h1
    have hdvd_term : (2 : ℤ) ^ (k + 1) ∣ 3 ^ trest.length * 2 ^ k := by
      rw [htail_numsum] at hdvd_tail
      have := dvd_sub hdvd_tail hdvd_rest
      rwa [show (3 : ℤ) ^ trest.length * 2 ^ k + listNumSum trest - listNumSum trest =
        3 ^ trest.length * 2 ^ k from by ring] at this
    have h2k_ne : (2 : ℤ) ^ k ≠ 0 := by positivity
    have h2_dvd_3 : (2 : ℤ) ∣ 3 ^ trest.length := by
      rwa [show (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 from by ring,
           show (3 : ℤ) ^ trest.length * 2 ^ k = 2 ^ k * 3 ^ trest.length from by ring,
           mul_dvd_mul_iff_left h2k_ne] at hdvd_term
    exact absurd (Int.emod_eq_zero_of_dvd h2_dvd_3) (by rw [three_pow_mod_two]; omega)
  · -- u^k(x) is odd → k ∈ s.vals
    intro hodd; by_contra hk_nmem
    have htail_gt : ∀ j, j ∈ tail → k + 1 ≤ j := by
      intro j hj; have hge := htail_ge j hj
      have hne : j ≠ k := by
        intro heq; subst heq
        simp only [htail_def, List.mem_filter, decide_eq_true_eq] at hj; exact hk_nmem hj.1
      omega
    have hdvd_tail : (2 : ℤ) ^ (k + 1) ∣ listNumSum tail :=
      listNumSum_tail_dvd tail k htail_gt
    have hdvd_rhs : (2 : ℤ) ^ (k + 1) ∣ (2 ^ s.n * x - listNumSum tail) :=
      dvd_sub hdvd_2nx hdvd_tail
    have hdvd_lhs : (2 : ℤ) ^ (k + 1) ∣
        3 ^ tail.length * (2 ^ k * collatzU_iterate k x) := by
      rw [hkey]; exact hdvd_rhs
    have hdvd_prod : (2 : ℤ) ^ (k + 1) ∣ 2 ^ k * collatzU_iterate k x := by
      have hc := three_pow_two_pow_coprime tail.length (k + 1)
      rw [show (3 : ℤ) ^ tail.length * (2 ^ k * collatzU_iterate k x) =
          (2 ^ k * collatzU_iterate k x) * 3 ^ tail.length from by ring] at hdvd_lhs
      exact hc.symm.dvd_of_dvd_mul_right hdvd_lhs
    have h2k_ne : (2 : ℤ) ^ k ≠ 0 := by positivity
    have hdvd_uk : (2 : ℤ) ∣ collatzU_iterate k x := by
      rwa [show (2 : ℤ) ^ (k + 1) = 2 ^ k * 2 from by ring,
           mul_dvd_mul_iff_left h2k_ne] at hdvd_prod
    exact absurd hodd (by rw [Int.emod_eq_zero_of_dvd hdvd_uk]; omega)

/-! ## Proposition 5 -/

theorem prop5_forward (x : ℤ) (n : ℕ) (hn : 0 < n) (hcycle : collatzU_iterate n x = x)
    (hm : 0 < (oddSteps x n).length) :
    ∃ s : Schedule, s.n = n ∧ (x : ℚ) = cycleFormula s := by
  set v := oddSteps x n
  have hv_ne : v ≠ [] := by intro h; rw [h] at hm; simp at hm
  have hv_sorted : v.Pairwise (· < ·) := oddSteps_strictMono x n
  have hv_bound : ∀ i, i ∈ v → i < n := oddSteps_bound x n
  have hv_compat : ∀ i, i < n → (i ∈ v ↔ collatzU_iterate i x % 2 = 1) :=
    oddSteps_compat x n
  refine ⟨⟨v, n, hv_ne, hv_sorted, hv_bound⟩, rfl, ?_⟩
  have hformula := collatzU_iterate_int_formula x n v hv_sorted hv_bound hv_compat
  rw [hcycle] at hformula
  have hkey : x * ((2 : ℤ) ^ n - 3 ^ v.length) = listNumSum v := by linarith
  have hdiff_ne : (2 : ℤ) ^ n - 3 ^ v.length ≠ 0 :=
    sub_ne_zero.mpr (pow2_ne_pow3 hn hm)
  change (x : ℚ) = (listNumSum v : ℚ) / ((2 ^ n - 3 ^ v.length : ℤ) : ℚ)
  rw [eq_div_iff (by exact_mod_cast hdiff_ne : ((2 ^ n - 3 ^ v.length : ℤ) : ℚ) ≠ 0)]
  push_cast; exact_mod_cast hkey

theorem prop5_backward (x : ℤ) (s : Schedule) (hn : 0 < s.n)
    (hx : (x : ℚ) = cycleFormula s) :
    collatzU_iterate s.n x = x := by
  have hm_pos : 0 < s.m := List.length_pos_of_ne_nil s.nonempty
  have hdiff_ne : (2 : ℤ) ^ s.n - 3 ^ s.m ≠ 0 :=
    sub_ne_zero.mpr (pow2_ne_pow3 hn hm_pos)
  have hdiff_ne_q : ((2 ^ s.n - 3 ^ s.m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hdiff_ne
  have hx_eq : (x : ℚ) * ((2 ^ s.n - 3 ^ s.m : ℤ) : ℚ) = (s.numSum : ℚ) := by
    rw [hx]; exact div_mul_cancel₀ _ hdiff_ne_q
  have hx_int : x * ((2 : ℤ) ^ s.n - 3 ^ s.m) = s.numSum := by exact_mod_cast hx_eq
  have hx_rearr : (2 : ℤ) ^ s.n * x = 3 ^ s.vals.length * x + listNumSum s.vals := by
    have : x * (2 ^ s.n - 3 ^ s.vals.length) = listNumSum s.vals := hx_int
    nlinarith
  suffices h : (2 : ℤ) ^ s.n * collatzU_iterate s.n x = (2 : ℤ) ^ s.n * x by
    exact mul_left_cancel₀ (show (2 : ℤ) ^ s.n ≠ 0 by positivity) h
  suffices hcompat : s.CompatibleWith x by
    have hf := collatzU_iterate_int_formula x s.n s.vals s.strictMono
      (fun i hi => s.bound i hi) (fun i hi => hcompat i hi)
    linarith
  suffices hall : ∀ k, k ≤ s.n → ∀ j, j < k →
      (j ∈ s.vals ↔ collatzU_iterate j x % 2 = 1) by
    exact fun i hi => hall s.n le_rfl i hi
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k' ihk =>
    intro hk' j hj
    by_cases hjk : j < k'
    · exact ihk (by omega) j hjk
    · have hjk' : j = k' := by omega
      subst hjk'
      exact schedule_compat_step x s j (by omega) hx_rearr (ihk (by omega))

/-- If x ≠ 0 is a cycle point, the trajectory has at least one odd step. -/
private lemma cycle_has_odd_step (x : ℤ) (n : ℕ) (hn : 0 < n)
    (hcycle : collatzU_iterate n x = x) (hx : x ≠ 0) :
    0 < (oddSteps x n).length := by
  by_contra hm
  push_neg at hm
  have hlen : (oddSteps x n).length = 0 := by omega
  have hv_empty : oddSteps x n = [] := List.eq_nil_of_length_eq_zero hlen
  have hv_compat := oddSteps_compat x n
  -- Apply the integer formula with v = [] (no odd steps)
  have hformula := collatzU_iterate_int_formula x n []
    List.Pairwise.nil (fun _ h => nomatch h)
    (fun i hi => by rw [← hv_empty]; exact hv_compat i hi)
  simp [listNumSum] at hformula
  -- hformula : 2^n * collatzU_iterate n x = x
  rw [hcycle] at hformula
  -- hformula : 2^n * x = x, so x * (2^n - 1) = 0
  have : x * ((2 : ℤ) ^ n - 1) = 0 := by linarith
  have h2n_pos : (2 : ℤ) ^ n - 1 > 0 := by
    have : (2 : ℤ) ^ n ≥ 2 ^ 1 := by
      exact_mod_cast Nat.pow_le_pow_right (by omega) hn
    linarith [show (2 : ℤ) ^ 1 = 2 from by ring]
  have : x = 0 := by
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · omega
  exact hx this

/-- **Proposition 5** (Bohm-Sontacchi 1978, combined).
  A nonzero integer x is a cycle point of u if and only if it can be expressed
  via the cycle formula (*) for some valid schedule.
  Note: x = 0 is excluded because it is a trivial fixed point (u(0) = 0) that
  cannot be represented via any Schedule (which requires at least one odd step). -/
theorem prop5 (x : ℤ) (hx : x ≠ 0) :
    (∃ n : ℕ, 0 < n ∧ collatzU_iterate n x = x) ↔
    (∃ s : Schedule, 0 < s.n ∧ (x : ℚ) = cycleFormula s) := by
  constructor
  · rintro ⟨n, hn, hcycle⟩
    have hm := cycle_has_odd_step x n hn hcycle hx
    obtain ⟨s, hs_n, hs_eq⟩ := prop5_forward x n hn hcycle hm
    exact ⟨s, hs_n ▸ hn, hs_eq⟩
  · rintro ⟨s, hs, hformula⟩
    exact ⟨s.n, hs, prop5_backward x s hs hformula⟩

end BohmSontacchi
