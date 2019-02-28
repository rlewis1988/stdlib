import tactic.fin_cases
import data.nat.prime
import group_theory.perm
import tactic.norm_num

example (p : ℕ) (h : p ∈ list.range 2) : true :=
begin
  cases h,
  trivial,
  cases h,
  trivial,
  cases h,
end

example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *,
  all_goals { assumption }
end

example (x2 : fin 2) (x3 : fin 3) (n : nat) (y : fin n) : x2.val * x3.val = x3.val * x2.val :=
begin
  fin_cases x2;
  fin_cases x3,
  success_if_fail { fin_cases * },
  success_if_fail { fin_cases y },
  all_goals { simp },
end

open finset
example (x : ℕ) (h : x ∈ Ico 2 5) : x = 2 ∨ x = 3 ∨ x = 4 :=
begin
  fin_cases h; simp
end

open nat
example (x : ℕ) (h : x ∈ [2,3,5,7]) : x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 7 :=
begin
  fin_cases h; simp
end

instance (n : ℕ) : decidable (prime n) := decidable_prime_1 n
example (x : ℕ) (h : x ∈ (range 10).filter prime) : x = 2 ∨ x = 3 ∨ x = 5 ∨ x = 7 :=
begin
  fin_cases h; exact dec_trivial
end

open equiv.perm
example (x : (Σ (a : fin 4), fin 4)) (h : x ∈ fin_pairs_lt 4) : x.1.val < 4 :=
begin
  fin_cases h; simp,
  any_goals { exact dec_trivial },
end

example (x : fin 3) : x.val < 5 :=
begin
  fin_cases x; exact dec_trivial
end

example (f : ℕ → Prop) (p : fin 3) (h0 : f 0) (h1 : f 1) (h2 : f 2) : f p.val :=
begin
  fin_cases *,
  all_goals { assumption }
end
