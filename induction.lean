-- This module serves as the root of the `Try` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Data.Nat.Dist -- distance function
import Mathlib.Data.Nat.GCD.Basic -- gcd
import Mathlib.Data.Nat.ModEq -- modular arithmetic
import Mathlib.Data.Nat.Prime.Basic -- prime number stuff
import Mathlib.Data.Nat.Factors -- factors
import Mathlib.Tactic.NormNum.Prime -- a tactic for fast computations
import Init.Prelude
import Mathlib.Tactic
import Mathlib.Data.List.Range
import Mathlib.Data.Int.Range
import Mathlib.Data.Finset.Range


--open_locale big_operators -- enable notation
--open finset

open Nat

#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique

def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

  example : fac 0 = 1 :=
  rfl

  example : fac 0 = 1:= by
 rw[fac]

example (n : ℕ): fac (n+1) = (n+1) * fac n :=
rfl

theorem fac_pos (n : ℕ) : 0 < fac n := by
induction' n with n ih
rw[fac]; exact zero_lt_one;
rw[fac];  exact mul_pos n.succ_pos ih


theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  exact absurd ipos (not_lt_of_ge ile)
  rw[fac]
  rcases Nat.of_le_succ ile with h | h
  apply dvd_mul_of_dvd_right (ih h)
  rw[h]
  apply dvd_mul_right

 theorem sum_id (n : ℕ) : ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
   symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
   induction' n with n ih
   simp
   rw [Finset.sum_range_succ, mul_add 2, ← ih]
   ring

theorem sum_sqr (n : ℕ) : ∑ i in Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  simp
  rw[Finset.sum_range_succ, mul_add 6, <- ih]
  ring

theorem sum_third (n : ℕ) : ∑ i in Finset.range (n + 1), i ^ 3 = n ^2 * (n + 1)^2 / 4 := by
    symm; apply Nat.div_eq_of_eq_mul_right (by norm_num: 0 < 4)
    induction' n with n ih
    simp
    rw[Finset.sum_range_succ, mul_add 4, <- ih]
    ring

theorem pow_of_two (n : ℕ) : ∑ i in Finset.range (n + 1), 2^i = 2^(n+1) -1 := by
    symm; apply Nat.sub_eq_of_eq_add
    induction' n with n ih
    simp
    rw[Finset.sum_range_succ, pow_add 2 (n+1)]; simp; rw[mul_two]; rw[ih]
    ring

theorem pow_of_three (n : ℕ) : ∑ i in Finset.range (n + 1), 3^i = (3^(n+1) -1)/2 := by
    symm; apply Nat.div_eq_of_eq_mul_right (by norm_num: 0 < 2);apply Nat.sub_eq_of_eq_add
    induction' n with n ih
    simp
    rw[Finset.sum_range_succ, mul_add 2, pow_add 3 (n+1)]; simp; rw[ih]
    ring




def fib : ℕ → ℕ
  | 0 => 0
  | 1=> 1
  | 2=> 1
  | n + 2 => fib (n + 1) + fib n

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

theorem pow_of_p (p:ℕ) ( n : ℕ) :1<p → ∑ i in Finset.range (n + 1), p^i = (p^(n+1) -1)/(p-1) := by
    intro h1
    symm
    apply Nat.div_eq_of_eq_mul_right
    · omega
    induction' n with n ih
    simp
    symm; symm at ih; rw[Finset.sum_range_succ,mul_add (p-1),pow_add p (n+1)]; simp; rw[ih]
    ring_nf
    refine Eq.symm (Nat.sub_eq_of_eq_add ?H2.succ.h)
    apply?
