/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/

import data.nat.choose.basic
import data.nat.choose.sum
import data.nat.multiplicity
import number_theory.padics.padic_norm

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `nat.choose (2 * n) n`).

## Main definition and results

* `nat.central_binom`: the central binomial coefficient, `(2 * n).choose n`.
* `nat.central_binom_induction`: the inductive relationship between successive central binomial
  coefficients.
* `nat.four_pow_n_lt_n_mul_central_binom`: an exponential lower bound on the central binomial
  coefficient.
* `nat.multiplicity_central_binom_le`: a logarithmic upper bound on the multiplicity of a prime in
  the central binomial coefficient.
* `nat.multiplicity_central_binom_of_large_le_one`: sufficiently large primes appear at most once in
  the factorisation of the central binomial coefficient.
* `nat.multiplicity_central_binom_of_large_eq_zero`: sufficiently large primes do not appear in the
  factorisation of the central binomial coefficient.
-/

namespace nat

def central_binom (n : ℕ) := (2 * n).choose n

lemma central_binom_def (n : ℕ) : central_binom n = (2 * n).choose n := rfl
local attribute [simp] central_binom_def

lemma central_binom_pos (n : ℕ) : 0 < central_binom n :=
choose_pos (nat.le_mul_of_pos_left zero_lt_two)

lemma central_binom_ne_zero (n : ℕ) : central_binom n ≠ 0 :=
(central_binom_pos n).ne'

lemma choose_le_central_binom (r n : ℕ) : choose (2 * n) r ≤ central_binom n :=
calc (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) : choose_le_middle r (2 * n)
... = (2 * n).choose n : by rw nat.mul_div_cancel_left n zero_lt_two

lemma two_le_central_binom (n : ℕ) (n_pos : 0 < n) : 2 ≤ central_binom n :=
calc 2 ≤ 2 * n : le_mul_of_pos_right n_pos
... = (2 * n).choose 1 : (choose_one_right (2 * n)).symm
... ≤ (2 * n).choose n : choose_le_central_binom 1 n

lemma succ_mul_central_binom_succ (n : ℕ) :
  (n + 1) * (central_binom (n + 1)) = (2 * (2 * n + 1)) * central_binom n :=
calc (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) : mul_comm _ _
... = (2 * n + 1).choose n * (2 * n + 2) : by rw [choose_succ_right_eq, choose_mul_succ_eq]
... = 2 * ((2 * n + 1).choose n * (n + 1)) : by ring
... = 2 * ((2 * n + 1).choose n * ((2 * n + 1) - n)) :
  by rw [two_mul n, add_assoc, nat.add_sub_cancel_left]
... = 2 * ((2 * n).choose n * (2 * n + 1)) : by rw choose_mul_succ_eq
... = (2 * (2 * n + 1)) * (2 * n).choose n : by rw [mul_assoc, mul_comm (2 * n + 1)]

-- This bound is of interest because it appears in Tochiori's refinement of Erdős's proof
-- of Bertrand's postulate
-- (https://en.wikipedia.org/w/index.php?title=Proof_of_Bertrand%27s_postulate&oldid=859165151#Proof_by_Shigenori_Tochiori)
lemma four_pow_n_lt_n_mul_central_binom : ∀ (n : ℕ) (n_big : 4 ≤ n), 4 ^ n < n * central_binom n
| 0 n_big := by norm_num at n_big
| 1 n_big := by norm_num at n_big
| 2 n_big := by norm_num at n_big
| 3 n_big := by norm_num at n_big
| 4 n_big := by { norm_num, unfold nat.choose, norm_num }
| (m + 5) n_big :=
calc 4 ^ (m + 5) < 4 * ((m + 4) * central_binom (m + 4)) :
  (mul_lt_mul_left zero_lt_four).mpr (four_pow_n_lt_n_mul_central_binom (m + 4) le_add_self)
... = (4 * (m + 4)) * central_binom (m + 4) : (mul_assoc _ _ _).symm
... ≤ (2 * (2 * (m + 4) + 1)) * central_binom (m + 4) : by linarith
... = (m + 5) * central_binom (m + 5) : (succ_mul_central_binom_succ (m + 4)).symm

-- This bound is of interest because it appears in Erdős's proof of Bertrand's postulate.
lemma four_pow_le_two_mul_n_mul_central_binom : ∀ (n : ℕ) (n_pos : 0 < n),
  4 ^ n ≤ (2 * n) * central_binom n
| 0 pr := by linarith
| 1 pr := by norm_num
| 2 pr := by { norm_num, unfold nat.choose, norm_num }
| 3 pr := by { norm_num, unfold nat.choose, norm_num }
| (m + 4) _ :=
calc 4 ^ (m + 4) ≤ (m + 4) * central_binom (m + 4) :
  le_of_lt (four_pow_n_lt_n_mul_central_binom (m + 4) le_add_self)
... ≤ 2 * ((m + 4) * central_binom (m + 4)) : nat.le_mul_of_pos_left zero_lt_two
... = 2 * (m + 4) * central_binom (m + 4) : (mul_assoc _ _ _).symm

lemma multiplicity_central_binom_le
  (p : ℕ)
  [hp : fact p.prime]
  (n : ℕ)
  (n_pos : 0 < n)
  : padic_val_nat p (central_binom n) ≤ log p (2 * n)
  :=
begin
  rw @padic_val_nat_def p hp (central_binom n) (central_binom_ne_zero n),
  unfold central_binom,
  have two_n_sub : 2 * n - n = n, by rw [two_mul n, nat.add_sub_cancel n n],
  simp only
    [
      nat.prime.multiplicity_choose hp.out (le_mul_of_pos_left zero_lt_two) (lt_add_one _),
      two_n_sub, ←two_mul, enat.get_coe', finset.filter_congr_decidable
    ],
  have p_pow : p ^ log p (2 * n) ≤ 2 * n := nat.pow_log_le_self hp.out.one_lt (by linarith),
  have one_le_p : 1 ≤ p := trans one_le_two hp.out.two_le,
  calc _  ≤ (finset.Ico 1 (log p (2 * n) + 1)).card : finset.card_filter_le _ _
      ... = (log p (2 * n) + 1) - 1                 : nat.card_Ico _ _,
end

lemma multiplicity_central_binom_of_large_le_one
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_pos : 0 < n)
  (p_large : 2 * n < p ^ 2)
  : (padic_val_nat p (central_binom n)) ≤ 1
  :=
begin
  have u : log p (2 * n) ≤ 1,
    { let e := log_le_log_of_le _,
    sorry,
    },
  exact le_trans (multiplicity_central_binom_le p n n_pos) u,
end

lemma prime_le_three_is_two : ∀ {p : ℕ} (hp : prime p) (p_small : p < 3), p = 2
| 0 prime _ := by { exfalso, exact not_prime_zero prime}
| 1 prime _ := by { exfalso, exact not_prime_one prime }
| 2 _ _ := rfl
| (n + 3) _ big := by linarith

lemma multiplicity_central_binom_of_large_eq_zero
  (p : nat)
  [hp : fact p.prime]
  (n : nat)
  (n_big : 2 < n)
  (small : p ≤ n)
  (big : 2 * n < 3 * p)
  : padic_val_nat p (central_binom n) = 0
  :=
begin
  rw @padic_val_nat_def p hp (central_binom n) (central_binom_ne_zero n),
  unfold central_binom,
  have two_n_sub : 2 * n - n = n, by rw [two_mul n, nat.add_sub_cancel n n],
  simp only [
    nat.prime.multiplicity_choose hp.out (le_mul_of_pos_left zero_lt_two) (lt_add_one _),
    two_n_sub, ←two_mul, finset.card_eq_zero, enat.get_coe', finset.filter_congr_decidable
  ],
  clear two_n_sub,

  have three_lt_p : 3 ≤ p ,
  { rcases le_or_lt 3 p with H|H,
    { exact H, },
    { have p_two : p = 2 := prime_le_three_is_two hp.out H,
      linarith, }, },
  have p_pos : 0 < p := nat.prime.pos hp.out,

  apply finset.filter_false_of_mem,
  intros i i_in_interval,
  rw finset.mem_Ico at i_in_interval,
  refine not_le.mpr _,

  rcases lt_trichotomy 1 i with H|rfl|H,
  { have two_le_i : 2 ≤ i := nat.succ_le_of_lt H,
    have two_n_lt_pow_p_i : 2 * n < p ^ i,
    { calc 2 * n < 3 * p : big
             ... ≤ p * p : (mul_le_mul_right p_pos).2 three_lt_p
             ... = p ^ 2 : (sq _).symm
             ... ≤ p ^ i : nat.pow_le_pow_of_le_right p_pos two_le_i, },
    have n_mod : n % p ^ i = n,
    { apply nat.mod_eq_of_lt,
      calc n ≤ n + n : nat.le.intro rfl
         ... = 2 * n : (two_mul n).symm
         ... < p ^ i : two_n_lt_pow_p_i, },
    rw n_mod,
    exact two_n_lt_pow_p_i, },

  { rw [pow_one],
    suffices h23 : 2 * (p * (n / p)) + 2 * (n % p) < 2 * (p * (n / p)) + p,
    { exact (add_lt_add_iff_left (2 * (p * (n / p)))).mp h23, },
    have n_big : 1 ≤ (n / p) := (nat.le_div_iff_mul_le' p_pos).2 (trans (one_mul _).le small),
    rw [←mul_add, nat.div_add_mod],
    calc  2 * n < 3 * p : big
            ... = 2 * p + p : nat.succ_mul _ _
            ... ≤ 2 * (p * (n / p)) + p : add_le_add_right ((mul_le_mul_left zero_lt_two).mpr
            $ ((le_mul_iff_one_le_right p_pos).mpr n_big)) _ },

  { have : i = 0 := nat.le_zero_iff.mp (nat.le_of_lt_succ H),
    rw [this, pow_zero, nat.mod_one, mul_zero],
    exact zero_lt_one, },
end

end nat
