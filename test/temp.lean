import tactic.norm_cast
import all
#check ne_from_not_eq
--run_cmd tactic.classify_type_test `ne_from_not_eq

#check ℕ
open tactic

@[reducible] meta def name.is_coe (n : name) : Prop :=
n = `has_coe.coe ∨ n = `coe ∨ n = `coe_fn

meta def expr.contains_coe' (e : expr) : bool :=
e.contains_constant name.is_coe

meta def expr.is_coe : expr → bool
| (expr.const n _) := n.is_coe
| _ := ff


/- run_cmd do
check_attr_name `move_cast >> check_attr_name `elim_cast >> check_attr_name `squash_cast  -/

/-
todo: add coe_to_fun
-/

namespace bah
open norm_cast
section
set_option eqn_compiler.max_steps 14000

/-- rhs has the same number of or fewer casts at the beginning then lhs -/
meta def same_or_fewer_initial_casts : expr → expr → bool | lhs rhs :=
let lhs_head := lhs.get_app_fn, rhs_head := rhs.get_app_fn in
match lhs_head.is_coe, rhs_head.is_coe with
| tt, tt := same_or_fewer_initial_casts lhs.app_arg rhs.app_arg
| ff, tt := ff
| _, _ := tt
end

/- meta def same_or_fewer_initial_casts : expr → expr → bool
| `(↑%%lhs) `(↑%%rhs) := same_initial_casts lhs rhs
| `(↑%%_) _ := ff
| _ `(↑%%_) := ff
| _ _ := tt -/

private def squash_cast_fail :=
"norm_cast lemmas starting with ↑↑ on the LHS must be squash_cast lemmas, " ++
  "but squash_cast lemmas must remove at least one ↑."

end

meta def classify_type_aux (lhs rhs : expr) : tactic (user_attribute simp_lemmas) :=
let lhs_head := lhs.get_app_fn in
if lhs_head.is_coe then
  let lhs_body := lhs.app_arg,
      lhs_body_head := lhs_body.get_app_fn in
  if lhs_body_head.is_coe then
    let rhs_head := rhs.get_app_fn in
    if rhs_head.is_coe then
      if same_or_fewer_initial_casts lhs_body.app_arg rhs.app_arg then
        return squash_cast_attr
      else fail squash_cast_fail
    else fail squash_cast_fail
  else if rhs.contains_coe' then return move_cast_attr
  else return squash_cast_attr
else if rhs.contains_coe' then
  fail $ "norm_cast lemmas starting without ↑ on the LHS must be elim_cast lemmas," ++
                       " but elim_cast lemmas cannot contain ↑ on the RHS"
else if ! lhs.contains_coe' then
  fail "norm_cast lemmas must contain ↑"
else return elim_cast_attr


/- meta def classify_type_aux : expr → expr → tactic (user_attribute simp_lemmas)
| `(↑↑%%lhs) `(↑%%rhs) := if same_initial_casts lhs rhs then return squash_cast_attr
                          else fail squash_cast_fail
| `(↑↑%%lhs) _ := fail squash_cast_fail
| `(↑%%_) `(↑%%_) := fail "norm_cast lemmas cannot start with ↑ on both the LHS and RHS"
| `(↑%%_) rhs := if rhs.contains_coe' then return move_cast_attr
                 else return squash_cast_attr
| lhs rhs := if rhs.contains_coe'
             then fail $ "norm_cast lemmas starting without ↑ on the LHS must be elim_cast lemmas," ++
                       " but elim_cast lemmas cannot contain ↑ on the RHS"
             else if ! lhs.contains_coe'
             then fail "norm_cast lemmas must contain ↑"
             else return elim_cast_attr
end -/


meta def classify_type (lemma_type : expr) : tactic (user_attribute simp_lemmas) :=
do (args, tp) ← mk_local_pis lemma_type,
match tp with
| `(%%lhs = %%rhs) := classify_type_aux lhs rhs
| `(%%lhs ↔ %%rhs) := classify_type_aux lhs rhs
| _ := fail "norm_cast lemmas must be = or ↔"
end

meta def classify_type_test (n : name) : tactic unit :=
do e ← mk_const n >>= infer_type >>= classify_type, trace e.name


end bah
--set_option pp.notation false
#check num.to_of_nat

#check coe_monoid_hom

run_cmd bah.classify_type_test `num.to_of_nat

meta def check_attr_name (attr_name : name) : tactic unit :=
attribute.get_instances attr_name >>= mmap' (λ n, (do
  c ← mk_const n >>= infer_type,
  guessed_attr ← user_attribute.name <$> bah.classify_type c,
  when (guessed_attr ≠ attr_name) $ trace format!"#check {n} -- has attribute {attr_name} but we guessed {guessed_attr}")
  <|> tactic.trace format!"#check {n}  -- has attribute {attr_name} but we failed to guess one")

run_cmd do
check_attr_name `move_cast >> check_attr_name `elim_cast >> check_attr_name `squash_cast

--set_option pp.notation false

#check polynomial.coe_C -- maybe the suggestion of move_cast is okay?

#check @polynomial.coe_X
#check @polynomial.coe_monomial
#check continuous_linear_map.coe_apply' -- add coe_to_fun
#check multiplicity.int.coe_nat_multiplicity -- this is weird?
#check cardinal.nat_succ -- this looks wrong?
#check @polynomial.coe_add


/- weird ones -/
#check multiplicity.int.coe_nat_multiplicity  -- has attribute move_cast but we failed to guess one
#check uniform_space.completion.coe_zero  -- has attribute elim_cast but we failed to guess one
#check cardinal.nat_succ  -- has attribute elim_cast but we failed to guess one
#check complex.abs_cast_nat  -- has attribute elim_cast but we failed to guess one
#check complex.rat_cast_re  -- has attribute elim_cast but we failed to guess one
#check complex.int_cast_re  -- has attribute elim_cast but we failed to guess one
#check complex.nat_cast_re  -- has attribute elim_cast but we failed to guess one
#check @continued_fraction.coe_to_generalized_continued_fraction -- has attribute elim_cast but we guessed move_cast
#check rat.coe_nat_num  -- has attribute elim_cast but we failed to guess one
#check int.coe_nat_abs  -- has attribute elim_cast but we failed to guess one
#check nat.abs_cast  -- has attribute elim_cast but we failed to guess one
#check num.cast_to_znum -- has attribute squash_cast but we guessed move_cast
#check continuous_linear_map.restrict_scalars_coe_eq_coe' -- has attribute squash_cast but we guessed move_cast
#check linear_map.coe_restrict_scalars_eq_coe -- has attribute squash_cast but we guessed move_cast



/- follow suggestion -/
#check uniform_space.completion.coe_one -- has attribute elim_cast but we guessed squash_cast
#check polynomial.coe_X -- has attribute elim_cast but we guessed squash_cast
#check polynomial.coe_mul -- has attribute elim_cast but we guessed move_cast
#check polynomial.coe_add -- has attribute elim_cast but we guessed move_cast
#check polynomial.coe_one -- has attribute elim_cast but we guessed squash_cast
#check polynomial.coe_zero -- has attribute elim_cast but we guessed squash_cast
#check mv_polynomial.coe_X -- has attribute elim_cast but we guessed squash_cast
#check mv_polynomial.coe_mul -- has attribute elim_cast but we guessed move_cast
#check mv_polynomial.coe_add -- has attribute elim_cast but we guessed move_cast
#check mv_polynomial.coe_one -- has attribute elim_cast but we guessed squash_cast
#check mv_polynomial.coe_zero -- has attribute elim_cast but we guessed squash_cast
#check linear_map_with_bound_coe -- has attribute elim_cast but we guessed squash_cast
#check continuous_linear_map.coe_id' -- has attribute elim_cast but we guessed squash_cast
#check continuous_linear_map.coe_id -- has attribute elim_cast but we guessed squash_cast
#check continuous_linear_map.coe_zero' -- has attribute elim_cast but we guessed squash_cast
#check continuous_linear_map.coe_zero -- has attribute elim_cast but we guessed squash_cast
#check ennreal.coe_one -- has attribute elim_cast but we guessed squash_cast
#check ennreal.coe_zero -- has attribute elim_cast but we guessed squash_cast
#check continued_fraction.coe_to_simple_continued_fraction -- has attribute elim_cast but we guessed squash_cast
#check simple_continued_fraction.coe_to_generalized_continued_fraction -- has attribute elim_cast but we guessed squash_cast
#check int.cast_id -- has attribute elim_cast but we guessed squash_cast
#check nat.cast_id -- has attribute elim_cast but we guessed squash_cast
#check znum.cast_bit1 -- has attribute squash_cast but we guessed move_cast
#check znum.cast_bit0 -- has attribute squash_cast but we guessed move_cast
#check num.cast_bit1 -- has attribute squash_cast but we guessed move_cast
#check num.cast_bit0 -- has attribute squash_cast but we guessed move_cast
#check rat.cast_bit1 -- has attribute squash_cast but we guessed move_cast
#check rat.cast_bit0 -- has attribute squash_cast but we guessed move_cast
#check pos_num.cast_bit1 -- has attribute squash_cast but we guessed move_cast
#check pos_num.cast_bit0 -- has attribute squash_cast but we guessed move_cast



/- suggestion is wrong -/
#check polynomial.coe_C -- has attribute elim_cast but we guessed move_cast
#check polynomial.coe_monomial -- has attribute elim_cast but we guessed move_cast
#check polynomial.coeff_coe  -- has attribute elim_cast but we failed to guess one -- INVESTIGATE FIRST
#check mv_polynomial.coe_C -- has attribute elim_cast but we guessed move_cast
#check mv_polynomial.coe_monomial -- has attribute elim_cast but we guessed move_cast
#check mv_polynomial.coeff_coe  -- has attribute elim_cast but we failed to guess one
#check znum.to_of_int  -- has attribute squash_cast but we failed to guess one
#check znum.of_to_int  -- has attribute squash_cast but we failed to guess one
#check num.of_to_nat  -- has attribute squash_cast but we failed to guess one
#check num.to_of_nat  -- has attribute squash_cast but we failed to guess one
#check ring_equiv.coe_add_equiv -- has attribute squash_cast but we guessed move_cast
#check ring_equiv.coe_mul_equiv -- has attribute squash_cast but we guessed move_cast
#check coe_add_monoid_hom -- has attribute squash_cast but we guessed move_cast
#check coe_monoid_hom -- has attribute squash_cast but we guessed move_cast


/- these are internal and can be ignored -/
#check ne_from_not_eq  -- has attribute elim_cast but we failed to guess one
#check gt_from_lt  -- has attribute elim_cast but we failed to guess one
#check ge_from_le  -- has attribute elim_cast but we failed to guess one







#exit

structure  p (α : Type) extends has_add α :=
[v : has_one α]

meta def structure_fields_full (env : environment) (n : name) : option (list name) :=
(env.structure_fields n).map (list.map $ λ n', n ++ n')

run_cmd do e ← get_env, trace $ e.get_projections `p

run_cmd do e ← get_env, trace $ structure_fields_full e `p

#exit


import tactic.omega  tactic.linarith  tactic.find
#check ℕ

open tactic

meta def prf (h : expr) (s : simp_lemmas): tactic expr :=
prod.snd <$> solve_aux h (simp_target s >> done)

#check eq.mpr

#check native.rb_lmap

example (m : ℕ) (h : m > 0) : m / 3 < m :=
by {apply nat.div_lt_self h,  }

lemma fuel_wf (m : ℕ) (h : 9 ≤ m) : m / 3 - 2 < m :=
have m / 3 ≤ m, from nat.div_le_self _ _,
by omega

lemma afuel_wf (m : ℕ) : m - 2 ≤ m :=
by omega

#check nat.mod

#eval char.to_lower 'α'
#check string
def string.to_lower (s : string) : string :=
list.as_string $ s.to_list.map char.to_lower

#eval "ABC'".to_lower

lemma exi_eq (a b : ℕ) : ∃ k l : ℕ, a / b = k ∧ l + b * k  = a :=
⟨a / b, a % b, rfl, nat.mod_add_div _ _⟩

-- omega isn't happy with nat division
lemma foo1 (m : ℕ) : m / 3 ≤ m :=
by omega -- failed

-- it's even less happy when you try to help it out.
lemma foo2 (m : ℕ) : m / 3 ≤ m :=
by { have h : m % 3 + 3 * (m / 3) = m := nat.mod_add_div m 3,
     omega } -- invalid eval_expr, expression must be closed

-- if you generalize the `/` in `h` it succeeds
lemma foo3 (m p : ℕ) (h : m % 3 + 3 * p = m) : p ≤ m :=
by omega -- succeeds

lemma foo4 (m p : ℕ) (h : m % 3 + 3 * p = m) (h2 : p = m / 3) : m / 3 ≤ m :=
by omega -- succeeds



lemma foo (m : ℕ) : m / 3 ≤ m :=
begin
 -- obtain ⟨o, ho⟩ : ∃ o, o + 3 * (m / 3) = m := ⟨_, nat.mod_add_div m _⟩,
  have := nat.mod_add_div m 3,
  set o := m % 3,
  set s := m / 3,
  omega
end

#exit

#check environment.structure_fields
run_cmd mk_simp_attr `my_simp_attr
constants a b : ℕ
@[my_simp_attr] lemma l1 : a = 2 := sorry

run_cmd mk_simp_attr `my_new_simp_attr [`my_simp_attr]

--@[my_new_simp_attr] lemma l2 : b = 2 := sorry

example : a = 2 := by simp only with my_new_simp_attr

example : b = 2 := by simp only with my_new_simp_attr

#check user_attribute
↦
#check tactic.dsimp_config
#exit

import data.finset
import data.fintype
import tactic.omega tactic.linarith

variables {X : Type*}
variables [fintype X] [decidable_eq X]
variables {r : ℕ}

constant rset (r : ℕ) (X) [fintype X] : Type
constant f1 (r : ℕ) (A : finset (finset X)) : finset (rset r X)
constant f2 {r : ℕ} (B : finset (rset (r+1) X)) : finset (rset r X)

instance foo (Y : Type) : has_union (finset Y) := sorry

def stupid (n k : ℕ) (h : n - k = n - (k + 1) + 1) :
  finset (rset (n - k) X) → finset (rset (n - (k + 1) + 1) X) :=
λ t, by rwa h at t

noncomputable def decompose' {n : ℕ} (A : finset (finset X)) : Π (k : ℕ), k ≤ n → finset (rset (n-k) X)
| 0 _ := f1 n A
| (k+1) hk := f1 _ A ∪ (
    have h : n - k = n - (k + 1) + 1 := begin clear decompose' _inst_1 _inst_2 A, omega, end,

    #exit

import tactic.ring  data.rat.basic

#check ℕ



@[user_command]
meta def uc (_ : interactive.parse (lean.parser.tk "ec")) : lean.parser unit :=
lean.parser.emit_code_here "section new_sect"

#check ℕ

ec

variables a b c d e f g h : ℚ


end new_sect

def good (n : ℕ) : Prop := 3 ∣ n
def f (n : ℕ) (h : good n) := n
lemma toto {n : ℕ} : n = n + 1 - 1 := by { norm_num }
example {n : ℕ} (h : good n) : 3 ∣ f n h :=
    begin revert h,
        rw (@toto n),
        sorry
    end

#exit

@[derive decidable] def good (n : ℕ) : Prop := 3 ∣ n

def f (n : ℕ) : ℕ := if h : good n then n else default _

lemma f_val {n : ℕ} (h : good n) : f n = n := by simp [f, h]

lemma toto {n : ℕ} : n = n + 1 - 1 := by { norm_num }
example {n : ℕ} (h : good n) : 3 ∣ f n :=
    begin
        rw [(@toto n)] at h ⊢,
        sorry
    end


#check a
--example : ((((-19 a+17 b-4 c-7 d+20 e-16 f+19 g+16 h)+(18 a+15 b-9 c+9 d+4 e-7 f-6 g-19 h)+(5 a+6 b+c+17 d-9 e-f+17 g+4 h)+(14 a-8 b+7 c+20 d+15 e-f+12 g-20 h))+((14 a+3 b+5 c-12 d+13 f-3 g+9 h)+(5 a+16 b-15 c+4 d+17 e+15 f+7 g-17 h)+(8 a-4 b-16 c+20 d+2 e+19 g-10 h)+(-a+20 b+9 c+7 d+14 e+f+11 g-13 h))+((-3 a-4 b-16 c-10 d-5 e+6 f-18 g-4 h)+(-15 a-3 b+2 c+9 e-5 f-2 g-5 h)+(-11 a-20 b-8 c+18 d-18 e+2 f+7 g+15 h)+(-11 a-2 b-7 c-5 d-4 e-17 f-8 g-13 h))+((-19 a-10 b-10 c+6 d-6 e-13 f+16 g+6 h)+(12 a-18 b+4 c+13 d+18 e+12 f+19 g-3 h)+(3 a+19 b+7 c-20 d+14 e-f-2 g-16 h)+(11 a+15 b-9 c+14 d+17 e-2 f+2 g+2 h)))+(((10 a+15 b-10 c-20 d-20 e-3 f+g-7 h)+(-15 a+14 b+8 c+6 d-10 e-3 f-6 g-11 h)+(15 a-18 b-6 c+8 d+6 e+9 f-11 g-8 h)+(14 a-15 b+11 c-19 d+15 e+18 f-20 g-4 h))+((9 a-14 b+6 c+5 d+6 e+5 f+10 g+12 h)+(13 a+3 b-6 c+4 d-10 e+13 f-9 g+9 h)+(-5 a-9 b+20 c-3 d-5 e-17 g-20 h)+(13 a-c+15 d+20 e-10 f-16 g+2 h))+((14 a+b-20 c+9 d-13 e+2 f-16 g-6 h)+(15 a-14 b-12 c+5 d-2 e-12 f+10 g-11 h)+(-9 a+14 b+13 c+16 d-5 e+6 f+16 g-8 h)+(-17 a+8 b+11 c+6 d+18 e+10 f+19 g+3 h))+((-4 a-8 b+2 c-9 d+12 e+4 f+18 g+6 h)+(15 a+16 b-15 c-7 d+20 e+4 f+6 g-h)+(-20 a+20 b+c-14 d+10 e+18 f+18 g+6 h)+(-12 a+b-19 c-11 e+6 f-19 g+18 h)))+(((-16 a+11 b-18 c-4 d+2 e-11 f+6 g-6 h)+(16 a+16 b-20 c+17 d-13 e-11 f-5 g+5 h)+(15 a-20 b-12 c+12 d+6 e-5 f+11 g+15 h)+(9 a+20 b+10 c+17 d+11 e+11 f-15 g-2 h))+((7 a-12 b+c+3 d-2 f-18 g-6 h)+(-a-11 b+11 c-2 d+12 e+20 f+20 g-6 h)+(9 a+5 b+8 c-12 d+13 e+5 f-3 g+3 h)+(-15 a-13 b-18 c+16 d-9 e-f-5 g-16 h))+((13 a+b+15 c+18 d-4 e-13 f+2 g-18 h)+(-2 b+20 c-4 d+17 e+11 f+13 g-7 h)+(10 a+6 b+5 d-10 e+12 f-7 g-14 h)+(-6 a+6 b-15 c-6 d+17 e-7 f-10 g+18 h))+((16 a-6 b-6 c-e+7 f-13 g-14 h)+(2 a-3 b-4 c+15 d+10 e-12 f-9 g+6 h)+(4 a-10 b-9 c-12 d-19 e-f-19 g-6 h)+(16 a+2 b-7 c-2 d+9 e+f-19 g-15 h)))+(((-13 a+10 b+17 c+6 d-13 e+7 g-5 h)+(-11 a-15 b-6 c+18 d-7 e-12 f-13 g+5 h)+(8 a+16 b+14 c+12 d-14 e+14 f+g-19 h)+(-11 a+14 b-12 c+3 d-13 e-4 f-18 g-6 h))+((-4 a-13 b+9 c+6 d-15 e-f+16 g-2 h)+(9 a-14 b+11 c-17 d+13 e+19 f-6 g+17 h)+(-4 a-3 b+c+17 d+16 e-6 f+9 g+7 h)+(-15 a+b+3 c-14 d+16 e+15 f-11 g-3 h))+((-19 a-11 b-20 c+3 d-e-16 f+3 g+7 h)+(14 a-3 b+17 c+18 d-11 e-19 f-13 g+15 h)+(4 a-7 b-20 c-19 d+12 e-f-4 g-7 h)+(-13 a-18 b-19 c-19 d-13 e-8 f-2 g-3 h))+((16 a+19 b-10 c-2 d-13 e-14 f-14 g-20 h)+(-2 a+18 b+7 c+3 d+15 e-10 f+19 g+h)+(-8 a-5 b-17 c+18 d-13 e+20 f+2 g-14 h)+(14 a-7 b-14 c-12 d+17 e-15 f-15 h))))+((((2 a+16 b-9 c-3 d-11 e-18 f+4 g+19 h)+(-4 a+16 b-20 c-3 d-12 e-10 f+9 g+19 h)+(-13 a+5 b-4 c-17 d-2 e+8 f-5 g+15 h)+(6 b-15 c-18 d-6 e+5 f-18 g-15 h))+((-15 b+8 c+8 d-14 e+18 f-17 g-16 h)+(9 a-b-17 c+5 d+11 e-8 f+g-14 h)+(-11 a-16 b-10 c-10 d+4 e+17 f-g+4 h)+(-8 a-11 b+18 c-12 d+15 e+6 f-9 g-6 h))+((-17 a+19 b-19 c-13 d+11 e-12 f-g-14 h)+(11 a+13 b-9 c-13 d-6 e-11 f+8 g)+(11 a-12 b+2 c-12 d-9 e+9 f+19 g-h)+(-9 a+17 b+4 c+15 d+9 e-18 f+12 g-2 h))+((7 a+5 b-17 c-18 d-14 e-2 f+3 g-7 h)+(7 a+12 b-17 c+12 d-10 e-8 f+9 g-19 h)+(-19 a-8 b-17 c-19 d-2 e-13 f-10 g+4 h)+(-17 a-b+20 c+5 d-4 e-f+18 g-h)))+(((-6 a-7 b-19 c+16 d-16 e+13 f-20 g-4 h)+(-11 a-12 b-12 c+7 d-3 e-20 f+18 g+6 h)+(4 a-14 b-c-3 d-11 e-11 f-15 g+20 h)+(9 a-20 b+12 c-17 d+16 e+18 f-8 g-2 h))+((-16 a-8 b-15 c+d-12 e+16 f-g-14 h)+(-16 a-5 b-7 c+14 d+11 e+11 f-11 g+12 h)+(14 a+7 b+13 c-4 d-2 e-5 f-5 g-15 h)+(4 a-18 b+6 c+7 d-6 e+4 f+4 g-4 h))+((10 a-7 b-4 c-15 d-17 e-15 f-9 g-2 h)+(7 a+17 b+7 c+14 d+2 e-12 f+5 g+10 h)+(-17 a+20 b+18 c+6 d+18 e+19 f+5 g-12 h)+(-3 a-11 b-2 c-6 d+e+19 f-9 g-4 h))+((-18 a-10 b-8 c-12 d-12 e-5 f+17 g-6 h)+(-7 a-9 b+4 c+6 d+6 e-2 f-18 g+10 h)+(-5 a+2 b-11 c-2 d+12 e-12 f-9 g-13 h)+(6 a-17 b+8 c-12 d-12 e+18 f-9 g+19 h)))+(((5 a+b+15 c-17 d-12 e+7 f-9 g+5 h)+(-7 a+17 b+12 c-4 d-20 e-4 f-5 g+h)+(18 a+11 b+3 c-4 d-13 e+7 f+5 g-4 h)+(7 a-13 b+5 c-8 d-7 e-f+7 g+19 h))+((-14 a-13 b+19 c+15 d+5 e-19 f+6 g+18 h)+(15 a+18 b-2 c+5 d+15 e-19 f-18 g+16 h)+(3 a+7 b+17 c-13 d+15 e-9 f-3 g+13 h)+(18 a-19 b-2 c+15 d+5 e+19 f+13 g-8 h))+((-14 b+6 c+17 d-2 e+5 f-3 g-9 h)+(8 b-9 c-15 d-3 e+2 f+7 g-6 h)+(14 a-16 b-6 c-18 d-7 e+5 f-14 g-17 h)+(3 a+10 b-15 c+18 d-14 f+4 g+15 h))+((-15 a-3 b-12 c-16 d+15 e-19 f-6 g-5 h)+(6 a-16 c+5 d-12 e+14 f-5 g-6 h)+(20 a-10 b+8 c+12 d-12 e-19 g-19 h)+(a+6 b-4 c+16 d+20 e+5 f-11 g-6 h)))+(((5 a+13 b+12 c-15 d+2 e+3 f-12 g-3 h)+(3 a-3 b-5 c+3 d+19 e+f-7 g+10 h)+(17 a+10 b+16 c+2 d-11 e+20 f-10 g+18 h)+(-10 a+b+8 c-12 d-9 e+15 f-11 g-13 h))+((-9 a+8 b+18 c+9 d+5 e+19 f-12 g-11 h)+(19 a-9 b-6 c-15 d-e-6 f-7 g+7 h)+(16 a-19 b-9 c-9 d-5 e+4 f-2 g+7 h)+(-2 a-16 b-8 c+19 d+5 e-3 f+20 g+18 h))+((14 a+8 b+6 c+7 d-7 e+4 f+3 g+15 h)+(-12 a-11 b+12 c+17 d+10 e-16 f+2 g+3 h)+(-6 a+7 b-3 c+17 d-4 e+15 f-10 g+20 h)+(-6 b-20 c+8 d+12 e+17 f-7 g-17 h))+((-9 a+2 b+16 c+17 d-2 e+4 f+7 g+18 h)+(11 a-4 b-14 c-19 d+18 e+14 f+20 g-14 h)+(-14 a-4 b+10 c-19 d-16 e+18 f+9 g-20 h)+(-19 a+13 b-7 c+11 d+9 e+f-3 g+16 h))))+((((17 a+5 b+3 c-17 d+18 e+10 f+6 g)+(-17 a-16 b-8 c+18 d+e-18 f+18 g+15 h)+(20 a-6 b-3 c-10 d+9 e+3 f-14 g-6 h)+(a+5 b+19 c+12 d-13 e-17 f+2 g+15 h))+((-14 a+11 b-19 c+3 d-19 e-13 f+6 g-16 h)+(2 a+5 b+19 c-2 d-17 e+12 f+12 g-7 h)+(4 a+5 b+14 c+11 d+2 e-11 f+4 g-17 h)+(19 a+16 b+14 c+14 d+2 e+7 f-14 g-4 h))+((-14 a+3 b-8 c+4 d+20 e+2 f-3 g-19 h)+(8 a+2 b-16 c+4 d-e-18 f-17 g-7 h)+(15 a-15 b+8 c-17 d-18 e-3 f-4 g+20 h)+(-7 a+3 b-11 c-19 d-13 e-10 f+2 g+10 h))+((13 a-17 b+11 c+8 d+19 e+8 f+3 g+16 h)+(-20 a-4 b+20 c-20 d+10 e+19 f-13 g+4 h)+(-4 a-b+10 c+7 d-6 e-16 f+19 g)+(a+9 b+11 c-4 d-11 e-2 f+3 g-18 h)))+(((14 a+9 b-4 c+9 d-12 f-7 g+4 h)+(-13 a+3 b-13 c-13 d-12 e-19 f-4 g-8 h)+(-12 a-4 b-13 c-20 d-e+7 f-3 g+19 h)+(-8 a+8 b+15 c-16 d+16 e+15 f-g+9 h))+((3 a+16 b-5 c+6 d+9 e+16 f-10 g+10 h)+(-18 a-11 b-20 c-15 d-11 e+18 f-3 g-7 h)+(-6 a+15 b-3 c-13 d+7 e+f+7 g+3 h)+(5 a+19 b+19 c-3 d-15 e+5 f+10 g+11 h))+((-7 a+b+6 c-15 d+e+2 f-5 g+7 h)+(7 a+13 c+19 d+14 e+14 f+14 g-2 h)+(-18 a+18 b+14 c-16 d+13 e-16 f-11 g-5 h)+(-12 a-14 b+6 c+19 d+15 e-7 f+13 g+2 h))+((6 a-16 b-14 c+20 d+3 e+17 f+11 g-11 h)+(-9 a-17 b-5 c-d+e-14 f+19 g-6 h)+(17 a-10 b-8 c+14 d-12 e-7 f-10 g-15 h)+(6 a-4 b-14 c+17 d-14 e-11 f-14 g-12 h)))+(((-18 a+5 b-16 c-10 d+20 e-12 f-2 g+20 h)+(15 a-12 b+15 c-3 d-8 e+20 f-5 g-19 h)+(-a-7 b+14 c-18 d-8 e-7 f-2 g+6 h)+(-19 a+3 b-13 c-2 d-12 e-9 f+4 g-4 h))+((-6 a-5 b+3 c+6 d-16 e-7 f-9 g+h)+(-16 a+11 b-4 c-10 d+14 e+4 f+5 g+12 h)+(-13 a+11 b-19 c+12 d+7 e-14 f-10 g-8 h)+(2 a+8 b-17 c+11 d-5 e-18 f-3 g-5 h))+((7 a-5 b-2 c+8 d-7 e+9 f+10 g+5 h)+(-2 a+16 b+16 c+14 d-15 e-17 f-3 g-20 h)+(4 a-2 b-9 c+13 d+7 e-16 f+6 g+19 h)+(7 a-4 b-15 c-11 d-5 e+2 f-11 g-3 h))+((-2 a+20 b+16 c+8 d-14 e-13 f+11 g+2 h)+(-5 a+7 b-6 c-15 d+17 e+2 f-13 g+2 h)+(7 a+12 b+6 c+6 d+3 e-8 f+9 g-7 h)+(-2 a-8 b+10 c+5 d+13 e-13 g-19 h)))+(((-17 a-4 b-16 c+3 d+4 e-14 f+5 g+14 h)+(17 a+15 b-14 c+20 d-17 e-14 f-19 g+19 h)+(15 a-17 b-12 c-12 d+3 e-13 f-2 g+9 h)+(-15 a-14 b+14 c-11 d+9 e-15 f+11 g+18 h))+((-19 a+8 b+3 c+15 d+5 e-11 f-3 g-12 h)+(3 a-7 b-8 c+8 d-6 e-12 f+14 g-16 h)+(-4 a-5 b-10 c-10 d-8 e-12 g+4 h)+(a+17 b+2 d-8 e-14 f-16 g-16 h))+((-17 a+11 b+9 c+12 d+19 e-16 f+6 g-18 h)+(-9 a+19 b-3 c+2 d+16 e-13 f+10 g-10 h)+(-a-4 b+18 c-19 d+17 e+6 f+6 g+14 h)+(5 a-19 b+4 c+13 d-4 e-4 f-8 g-13 h))+((-5 a+7 b-9 c+9 d+15 e-17 f-3 g+3 h)+(-9 a+10 b+2 c-4 d+4 e-12 f-19 g)+(2 a+b+16 c+13 d+14 e-7 f-11 g+15 h)+(-18 a-2 b+10 c-19 d-6 e-3 f+12 g+3 h))))+((((-11 a+7 b-20 c-9 d-14 e-10 f+20 g-6 h)+(12 a-15 b+9 c-9 e-14 f+11 g-15 h)+(7 a+12 b-4 c-11 d+14 e+6 f-19 g+3 h)+(9 a-10 b-18 c+3 d+17 e+3 f-12 g-14 h))+((2 a-10 b-18 c-15 d-9 e+16 f+10 g+20 h)+(5 a+15 b-8 c+5 d-9 e-18 f+10 g+3 h)+(-10 a+17 b+8 c+9 d+3 e-4 f-19 g+5 h)+(13 a-17 b-c+9 d-15 e-9 f-g+8 h))+((-5 a+6 b-5 c-5 d-18 e+10 f-8 g+8 h)+(-16 a+8 b+20 c+3 d+11 e-20 f-2 g+10 h)+(2 a-13 b+4 c-18 d+9 e+7 f-4 g-10 h)+(-5 a-17 b+2 c+12 d+4 e-4 f+11 g+11 h))+((4 a-16 b+10 c-20 d+4 e-20 f+3 g+9 h)+(-15 a+5 b+10 c+20 d-19 e-15 f+3 g-2 h)+(11 a-9 b+c+10 d-9 e-7 f-g+9 h)+(3 a+b-9 c+17 d-7 e+17 f+14 g+8 h)))+(((-4 a-15 c+19 d+19 e-2 f-10 g+19 h)+(5 a+15 b-12 c-6 d-13 e+6 f-18 g+11 h)+(10 b-7 c+15 d+6 e-20 f-4 g+7 h)+(-2 a-10 b-10 c+4 d+2 e+12 f-16 g-7 h))+((-10 a-20 b-20 c-3 d-14 e-f-6 g+12 h)+(-11 a-11 b+13 c-2 d-5 e+11 f-7 g-10 h)+(-a-9 b+17 c+15 d-10 e-5 f+4 g-3 h)+(-17 a+9 b-4 c+20 d+5 e+10 f-17 g+12 h))+((4 a+12 b-13 c-7 d-20 e+13 f-19 g-16 h)+(-10 b-17 c+19 d+19 e-17 f-18 g-4 h)+(-11 a+20 b+19 c-9 d+5 e+8 f+12 g+9 h)+(a-4 b+11 c-10 d-11 e-16 f+3 g+10 h))+((6 a+19 b+4 c-13 d+9 e-20 f+8 g-18 h)+(2 a-12 b+4 c+11 d+9 e-5 f+7 g+17 h)+(-5 a-5 b+4 c+8 e-5 f+18 g+6 h)+(-a-18 d-4 e-20 f-12 g+10 h)))+(((3 a+10 b-16 c-8 d+3 e-10 f+11 g-3 h)+(11 a-17 b-14 c-2 d+19 e-13 f+2 g+7 h)+(-7 a-16 b-14 c+8 e+8 f+6 g+9 h)+(-13 a-15 b+15 c-9 d-9 e-3 f-9 g+7 h))+((-14 a+12 b+20 d+19 e+7 f-17 g+16 h)+(4 a+17 b-10 c-12 d-3 e+18 f+20 g-10 h)+(13 a+16 b+19 c+7 d-11 e-17 f+15 g-18 h)+(-10 a-8 b-20 c+9 d+13 f+13 g+13 h))+((-4 a-19 b+4 c+3 d-20 e+4 f-5 g+7 h)+(-11 a+19 c-5 d+20 e-5 f+2 g-7 h)+(-16 a-18 b+8 c+4 d-20 e+20 f-g+13 h)+(-a-11 b+15 c+9 d-4 e+11 f+12 g-13 h))+((-19 a+7 b-13 c-20 d-17 e+14 f+13 g-16 h)+(3 a+19 b+7 c+18 d-20 e-18 f+5 g-13 h)+(14 a-9 b-4 c+6 e-19 f+2 g+4 h)+(-3 a-14 b+10 c+3 d-10 e-19 f-20 g-11 h)))+(((5 a+9 b+c+20 d-6 f+11 g-3 h)+(10 a-15 b+9 c+12 d+11 e+16 f-18 g+10 h)+(-17 a-c+6 d+12 e-16 g-16 h)+(-11 a-8 b-8 c-4 d+12 e+3 f-h))+((7 a+19 b-3 c-19 d-e+7 f-13 g+16 h)+(a+6 b+10 c+13 e-8 f+14 g-12 h)+(3 a+3 b-12 c-2 d+16 e-2 f-14 g+13 h)+(19 a-12 b-6 c-12 d+15 e-f-11 g+14 h))+((7 a-9 b+5 c-16 d+11 e+11 f+10 g+12 h)+(9 a+13 c-5 d+15 e+19 f-3 g-h)+(-19 a+10 b-4 c-d+e-18 f+20 g-4 h)+(8 a+12 b+2 c+17 d-e+12 f-8 g+2 h))+((11 a-2 b+12 c-14 d+7 e-10 f+5 g+4 h)+(-4 a-3 b-19 c+8 d-9 e+6 f-15 g+7 h)+(5 a-4 b+16 c-17 d-4 e-19 f+17 g)+(-3 a-11 b+2 c+17 d-11 e-14 f+9 g+7 h))))




#exit

import tactic.core

/-! foo -/

open tactic
setup_tactic_parser

@[user_command]
meta def doc_section_cmd (_ : parse $ tk "doc_section") : lean.parser unit :=
do n ← ident,
   emit_code_here sformat!"section {n} /-! ### {n} -/" .

doc_section d

run_cmd
olean_doc_strings >>= trace
-- prints: (none, [(⟨3, 0⟩, foo), (⟨1, 0⟩, ### d)])
end d

#exit

@[ext] structure dumb (V : Type) := (val : V)

#check expr.of_nat

#check dumb.ext
#check tactic.ext_iff

#exit

import data.nat.basic
open nat
#eval choose 5 6

#check @tactic.is_def_eq

#exit

import tactic -- order.bounds
#check preorder

instance : preorder ℕ :=
{ le := λ _ _, true,
  le_refl := λ _, trivial,
  le_trans := λ _ _ _ _ _, trivial,
  lt_iff_le_not_le := begin intros, simp [(≤), (<)] end  }

theorem t1 : is_least set.univ 2 := ⟨set.mem_univ _, λ _ _, trivial⟩
theorem t2 : is_least set.univ 3 := ⟨set.mem_univ _, λ _ _, trivial⟩

#check tactic.iterate
#check tactic.repeat


#exit
import tactic.core tactic.lint
import all
#check ℕ

#check tactic.is_in_mathlib
open tactic

#check tactic.apply

run_cmd
do e ← get_env,
   trace $ e.decl_pos `tactic.apply

#check lin_equiv_matrix

#exit
import measure_theory.ae_eq_fun tactic.core meta.expr

#check ℕ
variable a : Type
def f := a

open name
/- def last_string : name → string
| anonymous        := "[anonymous]"
| (mk_string s _)  := s
| (mk_numeral _ n) := last_string n -/

/-

meta def last : name → string
| (mk_string s _)  := s
| (mk_numeral n _) := repr n
| anonymous        := "[anonymous]"
-/

#eval last_string `a.b.c.d.e
#eval to_string $ name.last `a.b.c.d.e

#check @f
#check tactic.interactive.filter_upwards
#check tactic.mk_exists_lst
#exit
import tactic.norm_cast data.nat.prime
open tactic

example (x y : ℕ) : true :=
by do
  a ← mk_local_def `x `(4),
  trace_state,
  eval_expr ℕ a >>= trace,
  triv

set_option old_structure_cmd true
structure f {α : Type} (p : ℕ) extends group α :=
(a b c : ℕ)
(h : a = p)

#check tactic.interactive.apply_mod_cast

theorem cor8 (p : ℕ) (a b : ℤ):
nat.prime p ∧ ↑p ∣ a*b → (↑p ∣ a) ∨ (↑p ∣ b) :=
begin
 intros hp,
 have := (iff.elim_left (nat.prime.dvd_mul hp.left)),
 -- goal not match
 -- have this (p ∣ a) ∨ (p ∣ b)
end

run_cmd trace $ subobject_names `f

inductive dec | a | b
#check @dec.no_confusion

#check int.coe_nat_add.reversed

#check declaration.is_auto_generated

#exit
import tactic

#check ℕ
#check unchecked_cast
#check tactic.change_with_at
#check tactic.interactive.change'
#check @discrete.lift
#exit
import all
attribute [nolint]
old_conv.match_expr
finset.choose
turing.TM1to1.write
equiv.to_pequiv
pos_sum_of_encodable
tactic.match_fn
measure_theory.measure.integral
equiv.empty_arrow_equiv_punit
filter.is_bounded_under
equiv.pempty_sum
where.select_for_which
measurable_equiv.prod_sum_distrib
turing.TM1to1.read
auto.case_some_hyp_aux
category_theory.limits.cofan.mk
fderiv
turing.TM0.machine
tactic.rewrite_all.tracked_rewrite.replace_target
auto.case_hyp
omega.nat.prove_unsat_neg_free
metric.mem_nhds_iff
tactic.interactive.same_function
exists_mem_ne_zero_of_dim_pos
perfect_closure.eq_iff'
free_comm_ring_punit_equiv_polynomial_int
category_theory.limits.functor_category_is_colimit_cocone
encodable.encode_multiset
abelianization
multiset.sections
encodable.encode_sigma
measure_theory.ae_eq_fun.lift_rel
equiv.pempty_equiv_pempty
tactic.interactive.bin_op_right
alg_hom.comp
nat.decreasing_induction
omega.nat.form.sat
nnreal.le_of_forall_epsilon_le
tactic.interactive.clean_ids
linarith.mk_int_pfs_of_nat_pf
writer_t.monad_except
turing.TM1to0.tr_eval
function.embedding.Pi_congr_right
field.direct_limit.field
encodable.decode_subtype
num.succ'
tree
category_theory.equivalence.equivalence_of_fully_faithfully_ess_surj
Set.mk
category_theory.limits.limit.lift
Mon.colimits.cocone_fun
pfun.preimage
tactic.add_coinductive_predicate.coind_pred.impl_params
adjoin_root
category_theory.limits.cone_morphism
category_theory.limits.cone.extensions
emetric.is_open_iff
expr.to_implicit_binder
omega.find_scalars_core
archimedean.floor_ring
holor.assoc_left
measure_theory.ae_eq_fun.integrable
tactic.local_cache.internal.block_local.get_name
tactic.interactive.compact_decl
localization.fraction_ring.eq_zero_of_ne_zero_of_mul_eq_zero
tactic.rcases_patt_parse_list
filter.realizer.of_eq
topological_space.opens.map_comp
pSet.resp.equiv
equiv.mul_left
measure_theory.simple_func.bind
eckmann_hilton.comm_monoid
matrix.sub_up
wseq.think_congr
equiv_of_unique_of_unique
linarith.rearr_comp
monoid.closure
turing.tape.nth
category_theory.limits.equalizer.ι
tactic.interactive.old_conv
tactic.impl_graph.add_edge
subalgebra.comap
equiv.unique_of_equiv
equiv.fin_equiv_subtype
category_theory.limits.cones.forget
function.bicompl
polynomial.degree_eq_iff_nat_degree_eq_of_pos
monad_cont
continuous_map.ev
zmod.cast
topological_space.opens.map_iso
continuous_of_uniform_limit_of_continuous
tactic.interactive.tidy
measure_theory.simple_func.ennreal_rat_embed_encode
old_conv.interactive.itactic
ideal.lt_order_embedding_of_surjective
is_subgroup.mem_trivial
tactic.expanded_field_list'
ennreal.ennreal_equiv_sum
lists'
monoid.foldl.of_free_monoid
pell.pell_zd_succ_succ
localization.away.lift
field.direct_limit.inv
tactic.abel.normal_expr.e
traversable.pure_transformation
holor_index.assoc_right
tactic.add_refl
tactic.interactive.mk_mapp'
category_theory.monoidal_functor.ε_iso
with_top.coe_zero
tensor_product.lift
omega.ee
linarith.map_lt
filter.is_cobounded_under
eq_of_forall_edist_le
lists'.of_list
conv.discharge_eq_lhs
expr.of_nat
linear_map.lcomp
dfinsupp.zip_with_def
algebra.lmul_right
pos_num.one_bits
except_t.call_cc
category_theory.limits.limit.hom_iso'
finsupp.supported
turing.TM2to1.tr_init
zsqrtd.norm
tactic.find_eq_type
pell.eq_of_xn_modeq_lem3
measure_theory.ae_eq_fun.comp_edist
old_conv.mk_match_expr
measure_theory.ae_eq_fun
Mon.colimits.prequotient
tactic.valid_types
tactic.triv'
quot.hrec_on₂
linarith.list.mfind
pnat.xgcd_type.a
tactic.mk_op_lst
omega.nat.form.valid
wseq.lift_rel_o
polynomial.eval_sub_factor
quotient_group.left_rel
real.pi_gt_314
polynomial.decidable_dvd_monic
ennreal.le_of_real_iff_to_real_le
tactic.metavariables
category_theory.limits.is_limit.hom_iso'
equiv.false_equiv_pempty
tactic.ring2.horner_expr.mul_const
old_conv.congr_binder
power_series.order_ge_nat
tactic.expanded_field_list
pell.pell_zd_re
measure_theory.ae_eq_fun.comp
is_subgroup.center
ge.is_refl
matrix.sub_down_right
seq.corec.F
tactic.local_cache.internal.load_data
old_conv.lift_tactic
linear_map.id
int.of_snum
linarith.mk_coe_nat_nonneg_prf
tactic.contradiction_symm
tactic.interactive.fold_assoc1
int.range
old_conv.interactive.change
omega.nat.univ_close
tactic.interactive.collect_struct
tactic.last_explicit_arg
tactic.get_classes
normed_field
tactic.assoc_rewrite_target
tactic.local_cache.internal.mk_full_namespace
metric.cauchy_seq_iff
tactic.interactive.traversable_law_starter
cau_seq.inv_aux
tactic.clear_aux_decl_aux
omega.nat.form.fresh_index
category_theory.small_groupoid
complex.real_prod_homeo
tactic.reduce_ifs_at
dfinsupp.support
tactic.interactive.mono_function
fp.float
list.func.get_neg
associates.factor_set.prod
measure_theory.simple_func.integral
where.collect_by
turing.TM1to1.Λ'
linear_map.lflip
fin_dim_vectorspace_equiv
old_conv.map
equiv.perm_congr
tactic.mk_instance_cache
magma.free_semigroup.map
free_magma.repr'
continuous_map
pell.x_sub_y_dvd_pow
pfun.equiv_subtype
cau_seq.is_complete
omega.int.dnf
pmf.of_multiset
bounded_continuous_function.arzela_ascoli₁
tactic.add_coinductive_predicate.coind_pred.add_theorem
nat.even
tactic.exact_dec_trivial
tensor_product.uncurry
category_theory.is_left_adjoint
primcodable.subtype
continuous_map.induced
equiv.traverse
tactic.interactive.arity
category_theory.adjunction.core_unit_counit
tactic.abel.normal_expr.pp
uniformity_dist_of_mem_uniformity
perms_of_list
pmf.seq
category_theory.right_adjoint
filter.pcomap'
zorn.super_chain
tactic.intros1
omega.prove_unsat
tactic.interactive.conv_lhs
equiv.Pi_congr_right
tactic.local_cache.internal.def_local.clear
tactic.tidy.run_tactics
pell.xn
measurable_space
submodule.quotient.mk
le_of_forall_le_of_dense
padic.padic_norm_e_lim_le
snum.mul
list.permutations_aux.rec
tactic.abel.term
equiv.nonzero_comm_ring
omega.nat.preterm
category_theory.is_iso_of_op
tactic.add_coinductive_predicate.coind_pred.impl_locals
equiv.comm_group
is_ring_hom.to_module
hyperreal.pos_of_infinite_pos
filter.map_binfi_eq
traversable.foldr
category_theory.limits.cocone.of_pushout_cocone
list.insert_nth
associates.factors'
list.kreplace
semiquot.mk
padic_norm_e.defn
equiv.set.sum_compl
category_theory.yoneda.is_iso
old_conv.fail
list.traverse
metric.glue_space
localization.r
category_theory.iso.trans
nat.min_fac_aux
irrational
pell.eq_pell_zd
category_theory.over.map
tendsto_orderable
tactic.ring2.horner_expr.add_const
list.lex
old_conv.interactive.dsimp
continuous_linear_map.bounds_nonempty
tactic.interactive.pi_instance
omega.nat.nonnegate
list.kextract
category_theory.limits.sigma.desc
omega.head_eq
ring_equiv.to_equiv
matrix.col
old_conv.congr
tactic.interactive.traverse_constructor
turing.TM2to1.tr_supp
Gromov_Hausdorff.GH_dist
with_top.top_ne_zero
old_conv.step
differentiable
omega.nat.preterm.fresh_index
equiv.sigma_subtype_preimage_equiv_subtype
quotient.fin_choice
decidable_linear_order.lift
nat.rfind_x
free_ring.of
tactic.wlog
tactic.list_Pi
ordinal.add_absorp_iff
snum.tail
units
tactic.modify_ref
trunc.lift_on
matrix.sub_left
is_least
isometric.to_homeomorph
mv_polynomial.restrict_degree
category_theory.whisker_left
function.embedding.arrow_congr_left
equiv.perm.support_swap
equiv_of_dim_eq_dim
tensor_product.map
algebra.adjoin
well_founded_submodule_gt
category_theory.limits.colimit.pre
num.sub'
equiv_type_constr
tactic.replacer_attr
associates.factors
algebra.comap.to_comap
tactic.interactive.mk_rel
tactic.mk_replacer₁
side.to_string
set.fintype_bind
uniform_space.completion.cpkg
pell.yn_modeq_a_sub_one
free_semigroup.traverse'
omega.find_min_coeff
nat.partrec.code.id
ennreal.to_real_of_real_mul
mul_action.orbit_equiv_quotient_stabilizer
auto.split_hyps_aux
bounded_continuous_function.arzela_ascoli
with_zero.ordered_comm_monoid
tactic.mk_eq_proof
tactic.rcases_core
omega.nat.preterm.repr
metric.pos_of_mem_ball
where.compile_variable_list
category_theory.comma.map_right_comp
conv.repeat_count
is_add_subgroup.add_center
complex.tanh
polynomial.tendsto_infinity
omega.nat.is_nnf
omega.nat.bools.or
num.test_bit
state_t.call_cc
turing.TM1.init
filter.hyperfilter
pSet.resp.f
metric.mem_closure_iff'
nnnorm
dioph.pell_dioph
filter.is_bounded_under_inf
category_theory.functor.to_cocone
connected_component
turing.TM0.machine.map_respects
mv_polynomial.evalₗ
pfun.fix
tactic.rcases_patt_inverted.invert_list
linarith.ineq_const_mul_nm
category_theory.limits.fork.of_ι
quotient_group.fintype
fin.cons
rat_mul_continuous_lemma
equiv.division_ring
finsupp.dom_congr
tactic.ring.eval_atom
tactic.mllist.fixl
quotient.congr_right
linarith.add_exprs
tactic.split_if1
linear_map.to_bilin
category_theory.over
cau_seq.bounded'
isometric.symm
nat.galois_connection_mul_div
num.shiftr
set_fintype
measure_theory.simple_func.ennreal_rat_embed
cont_t
equiv.nat_prod_nat_equiv_nat
category_theory.limits.reflects_colimits
semiquot.univ
snum.head
eq_of_le_of_forall_le_of_dense
semiquot.blur'
tactic.explode_cmd
omega.symmod
vector3.cons_elim
topological_space.opens.to_Top
measurable_space.dynkin_system.to_measurable_space
tactic.rewrite_all.congr.expr_lens.congr
snum.bit1
writer_t
equiv.field
ideal.map
pequiv.single_mul_single_right
relator.left_unique
roption.equiv_option
measurable_equiv.set.range_inl
category_theory.limits.cofan
tactic.local_cache.internal.poke_data
equiv.sigma_equiv_prod_of_equiv
free_semigroup.traverse
localization.at_prime
surreal.add
order_embedding.nat_gt
metric.tendsto_nhds_nhds
set.image_factorization
null_measurable
tactic.rcases_patt.invert'
turing.TM1to0.tr
finsupp.restrict_dom
tactic.tfae.arrow
tactic.interactive.parse_config
tactic.ring.horner_expr.xadd'
turing.dwrite
category_theory.adjunction.adjunction_of_equiv_left
finsupp.of_multiset
omega.ee.repr
encodable.decidable_range_encode
with_zero.map
fintype.fintype_prod_right
category_theory.limits.prod
equiv.semigroup
padic_seq.norm_nonneg
tactic.to_pfmt
unique_factorization_domain.of_unique_irreducible_factorization
buffer.list_equiv_buffer
pequiv.to_matrix
nat.rfind_opt
category_theory.functor.const.op_obj_op
uniform_space.of_core_eq
pos_num.sqrt_aux
obviously.attr
tactic.interactive.source_fields
category_theory.prod.swap
lattice.fixed_points.next_fixed
turing.TM1to1.move
monotonicity
free_magma.traverse
dfinsupp
where.get_all_in_namespace
category_theory.limits.cocone.equiv
metric.second_countable_of_countable_discretization
omega.is_lia_term
is_linear_map
category_theory.limits.coprod.inl
tactic.interactive.one_line
tactic.assumption_with
computation.parallel.aux2
saturate_fun
category_theory.comma.map_right_id
category_theory.has_hom
equiv.refl
equiv.has_inv
tactic.explode.entries.add
turing.TM2.supports_stmt
list.func.add
tactic.ring.eval_horner
with_zero.div
monoid.mfoldr.of_free_monoid
free_comm_ring_equiv_mv_polynomial_int
metric.totally_bounded_of_finite_discretization
category_theory.under.hom_mk
category_theory.single_obj
tactic.mk_and_lst
conv.interactive.norm_num1
tactic.interactive.ac_mono_ctx'
category_theory.comma_morphism
fp.float.mul
tactic.interactive.traverse_field
pell.xn_modeq_x2n_add_lem
omega.int.form.valid
pnat.xgcd_type.w
finset.min
free_magma.map
homeomorph.inv
add_monoid_hom.comp
tactic.get_lift_prf
pilex
tactic.replaceable_attr
quotient_add_group.inhabited
tactic.interactive.fsplit
category_theory.under.mk
where.strip_pi_binders_aux
fp.next_up_pos
tactic.mllist.mfilter_map
equiv.set.sep
category_theory.limits.pushout_cocone
category_theory.limits.cone.equiv
tactic.alias.make_left_right
local_of_nonunits_ideal
equiv.set.union
equiv.sigma_congr_left
omega.coeffs.val
tactic.interactive.ac_mono_ctx
setoid.map
uniform_space.core.mk'
linarith.partition_by_type_aux
has_inner
pSet.definable.resp
order_embedding.well_founded_iff_no_descending_seq
category_theory.limits.pullback_cone.snd
algebra.lmul_left
tactic.get_nth_rewrite
where.format_variable
category_theory.core.forget_functor_to_core
dfinsupp.sum_apply
category_theory.iso.to_equiv
monoid.foldr
old_conv.seq
tactic.rcases_patt_parse_core
erased.mk
real.of_rat
omega.nat.sub_elim
pnat.xgcd_type.flip
nzsnum.drec'
quotient.lift_on'
tactic.suggest.decl_data
fp.float.zero
function.embedding.set_value
add_monoid_hom.id
monad_cont.goto
monoid.foldl.mk
subalgebra.to_submodule
denumerable.of_nat
ordinal.CNF_rec
tactic.abel.smul
tactic.interactive.get_current_field
turing.TM1to1.tr_supp
tactic.interactive.list_cast_of_aux
uniformity_edist_nnreal
pos_num.of_znum'
cardinal.aleph_idx.initial_seg
denumerable.of_encodable_of_infinite
omega.int.form.equiv
bifunctor.snd
pell.yz_succ_succ
cardinal.cantor_function
category_theory.limits.prod.map
equiv.int_equiv_nat_sum_nat
tactic.unify_prefix
format.intercalate
cont_t.map
tactic.explode.entries
set.pointwise_add
category_theory.over.mk
tactic.mk_congr_arg_using_dsimp'
multiset.rec_on
to_additive.attr
omega.nat.form.induce
side.other
tactic.ext_patt
enat.to_with_top
measure_theory.l1.simple_func.integral
option.to_list
pell.dz_val
measure_theory.ae_eq_fun.const
order_of_pos
functor.comp.mk
tactic.flatten
omega.term
metric.diam_ball
linear_equiv.to_linear_map
list.partition_map
strict_order.cof
category_theory.functor.const.op_obj_unop
semiquot.blur
metric.completion.uniformity_dist
category_theory.yoneda_lemma
list.map_head
is_add_group_hom.ker
quotient.hrec_on₂
pos_num.sub'
equiv.subtype_congr
equiv.option_equiv_sum_punit
category_theory.limits.binary_cofan.mk
finset.sum_ite
nnreal.le_of_real_iff_coe_le
right_add_coset
functor.add_const.run
submodule.quotient_rel
commutator
max_le_add_of_nonneg
matrix.vec_mul_vec
tactic.interactive.ac_monotonicity_goal
tactic.local_decls
omega.int.preterm.fresh_index
equiv.domain
turing.respects
quotient_group.quotient_ker_equiv_of_surjective
equiv.pempty_of_not_nonempty
category_theory.limits.binary_cofan
tactic.local_cache.internal.block_local.try_get_name
pell.xz_sub
onote.oadd_lt_oadd_3
category_theory.limits.fan
subtype.restrict
tactic.interactive.field
equiv.perm.cycle_factors
tactic.interactive.last_two
znum.bit0
filter.Liminf_le_Liminf
measure_theory.simple_func.const
gaussian_int.mod
measurable_space.dynkin_system.of_measurable_space
vector.traverse_def
where.resolve_vars_aux
tactic.rewrite_all.congr.expr_lens.replace
metric.mem_closure_range_iff
fp.float.sign
old_conv.pure
omega.int.preterm.repr
rel.restrict_domain
functor.const.run
category_theory.limits.types.colimit_is_colimit
equiv.list_nat_equiv_nat
pell.pell_zd_im
monoid.mfoldr.get
omega.nat.sub_elim_core
omega.unsat_lin_comb
conv.interactive.ring
category_theory.nat_iso.is_iso_of_is_iso_app
principal_ideal_domain.factors
ideal.le_order_embedding_of_surjective
category_theory.limits.pi.map
pell.eq_pell_lem
norm_num.eval_prime
norm_num.min_fac_helper
is_open_map
snum.cadd
initial_seg.lt_or_eq
pell.ysq_dvd_yy
is_add_subgroup.group_equiv_quotient_times_subgroup
tactic.abel.mk_cache
metric.glue_premetric
quotient.lift_on₂'
function.uncurry'
metric.cauchy_seq_iff'
linarith.find_cancel_factor
monoid_hom.one
pell.yn_one
pnat.div
tactic.local_cache.internal.def_local.get_tag_with_status
tactic.ring.eval_neg
module.core
erased.choice
finsupp.lmap_domain
list.insert_nth_remove_nth_of_ge
category_theory.nat_iso.hcomp
tactic.setup_tactic_parser_cmd
filter.is_trans_ge
cau_seq.completion.Cauchy
linarith.comp_source.flatten
tactic.interactive.repeat_or_not
znum.transfer_rw
pequiv.single
wseq.destruct_append.aux
tactic.subst_locals
polynomial.binom_expansion
tactic.interactive.mono_selection
list.reverse_rec_on
linarith.expr_contains
finite_cover_balls_of_compact
constr_smul
old_conv.congr_fun
forall_ge_le_of_forall_le_succ
ordinal.lift.principal_seg
nat.rfind
tactic.derive_reassoc_proof
zmodp
option.comp_traverse
Class
direct_sum.lmk
equiv.perm.same_cycle
algebra.comap.comm_ring
AddMon
category_theory.nat_trans.of_function
sum.comp_traverse
monoid.mfoldr
uniformity_edist''
filter.Limsup
algebra.gi
omega.subst
real.le_mk_of_forall_le
comm_ring.equiv_to_anti_equiv
nat.partrec.code.eval
encodable.of_inj
category_theory.limits.pair
equiv.perm.sign_aux2
set.pi
equiv.add_right
where.fetch_potential_variable_names
category_theory.limits.preserves_colimits
num.shiftl
equiv.trans
dfinsupp.lmk
tactic.interactive.ac_mono_ctx'.map
computation.corec.F
mzip_with
linarith.term_of_ineq_prf
padic_norm_e.nonneg
equiv.sum_pempty
tactic.abel.normal_expr
omega.int.form.unsat
tactic.replacer_core
local_ring.nonunits_ideal
encodable.trunc_encodable_of_fintype
equiv.perm.sign_aux3
vector.reverse
fp.of_rat
omega.nat.to_form
num.bit1
multiset.choose
omega.clause.append
uniform_space.separation_quotient.map
rat.num_denom_cases_on'
rank
num.gcd_aux
equiv.subtype_congr_right
tactic.tfae.mk_name
localization.fraction_ring.inv_aux
monoid.foldr.mk
unique.of_surjective
linarith.ineq.max
normed_group
fp.emin
category_theory.ess_surj
onote.to_string_aux1
push_neg.push_neg_at_hyp
category_theory.prod.associativity
mv_power_series.trunc_fun
magma.free_semigroup.r
equiv.add_semigroup
category_theory.as_iso
gt.is_irrefl
old_conv.bottom_up
old_conv.funext'
tactic.mk_replacer
category_theory.limits.is_limit.mk_cone_morphism
filter.pointwise_add_add_monoid
fintype.subtype
fp.next_dn
tactic.closure
omega.prove_unsat_lin_comb
tactic.interactive.match_imp
finsupp.to_multiset
category_theory.comma.map_left
category_theory.epi
pSet.subset
finsupp.lsingle
set.enumerate
finsupp.split_support
vector_space.dim
tactic.mono
decidable_linear_order_of_is_well_order
fp.of_rat_dn
equiv.empty_prod
measure_theory.ae_eq_fun.neg
tactic.chain_eq_trans
multiset.powerset
metric.second_countable_of_almost_dense_set
category_theory.yoneda_evaluation
with_one.lift
pell.yn_succ_succ
filter.le_Liminf_of_le
tactic.mk_assoc_instance
nat.subtype.succ
equiv.equiv_empty
finsupp.lsubtype_domain
category_theory.nat_trans.on_presheaf
CommRing.colimits.colimit_is_colimit
category_theory.nat_trans.of_homs
pell.is_pell_nat
tactic.mllist.append
unique_factorization_domain.exists_mem_factors_of_dvd
localization.mk
category_theory.limits.cofork.of_cocone
denumerable.mk'
list.sublists_len_aux
tactic.get_ancestors
tactic.mllist.mfilter
multiset.decidable_forall_multiset
category_theory.monad.comparison_forget
category_theory.obviously'
list.mem_ext
simp_attr.monad_norm
tactic.set_binder
has_fderiv_within_at
initial_seg.le_lt
tactic.list_Sigma
linarith.mk_prod_prf
equiv.d_array_equiv_fin
vector.mmap
category_theory.equivalence.symm
where.is_variable_name
nat.dist_eq_sub_of_ge
tactic.alias.get_alias_target
nat.partrec
is_cobounded_under_ge_of_tendsto
category_theory.large_groupoid
tactic.local_cache.internal.def_local.get_name
complex.norm_sq
omega.nat.desugar
turing.tape
tactic.interactive.best_match
category_theory.eq_to_iso
uniform_space.completion.completion_separation_quotient_equiv
category_theory.nat_trans.right_op
equiv.sum_comm
equiv.perm.cycle_factors_aux
omega.lin_comb
local_of_unique_max_ideal
tactic.add_prime
option.traverse
binder_eq_elim
num.pred
equiv.sum_congr
pnat.xgcd_type.v
pnat.xgcd_type.finish
category_theory.limits.cocone_left_op_of_cone
tactic.interactive.guard_expr_eq'
opposite.unop
homeomorph.neg
znum.transfer
free_comm_ring.is_supported
polynomial.lcoeff
nzsnum.bit1
tactic.to_implicit
tactic.mk_instance'
equiv.true_equiv_punit
ring_invo.to_ring_anti_equiv
filter.is_bounded_ge_of_bot
category_theory.functor.map_cone_morphism
auto.auto_config
alg_hom.range
finset.choose_x
tactic.ring.lift
is_add_subgroup.normalizer_is_add_subgroup
pell.xy_modeq_yn
reader_t.mk_label
category_theory.yoneda_sections
turing.TM2.cfg
list.func.get
tactic.add_coinductive_predicate.coind_pred.pred_g
equiv.vector_equiv_fin
category_theory.functor.op
subalgebra.fg
omega.revert_cond
category_theory.functor.op_inv
category_theory.limits.has_products
fp.prec
is_cyclic.comm_group
CommRing.colimits.desc_fun
tactic.interactive.derive_lawful_traversable
function.involutive.to_equiv
tactic.trans_conv
znum.cmp_to_int
differentiable_on
metric.nhds_eq
set.pointwise_add_fintype
snum.sign
where.inflate
bounded_continuous_function.const
tactic.interactive.same_function_aux
direct_sum.set_to_set
filter.pointwise_mul_monoid
finsupp.equiv_fun_on_fintype
category_theory.limits.fork
measurable_equiv.sum_prod_distrib
tactic.select
linarith.get_contr_lemma_name
conv.interactive.norm_cast
trunc.map
omega.is_lna_form
filter.liminf
list.to_finmap
homeomorph.prod_congr
omega.nat.form.neg_free
polynomial.mod
equiv.sum_prod_distrib
category_theory.limits.cocone.of_cofork
metric.completion.uniformity_dist'
ring.direct_limit
equiv.ulift
computation.map_congr
filter.map_infi_eq
old_conv.bind
equiv.arrow_punit_equiv_punit
pnat.gcd_b'
pos_num.divmod_aux
auto.preprocess_hyps
totally_separated_space
uniformity_edist'
old_conv.top_down
push_neg.push_neg_at_goal
category_theory.equivalence.counit_inv
where.trace_where
pell.yn_modeq_two
linarith.mk_neg_one_lt_zero_pf
complex.cos
linarith.comp.lt
equiv.set.of_eq
principal_seg
tactic.abel.normal_expr.zero'
differentiable_at
hyperreal.epsilon_lt_pos
algebra.to_comap
quotient.mk'
tactic.rcases_patt.invert_list
encodable.fintype_arrow
tactic.local_cache.internal.def_local.RADIX
linear_equiv.to_equiv
integral_closure
writer_t.listen
equiv.perm.is_swap
ennreal.tendsto_at_top
cau_seq.completion.of_rat
tactic.interactive.get_equations_of
real.cosh
add_monoid_hom.zero
old_conv.find
order_embedding
turing.TM2to1.Γ'
category_theory.limits.prod.snd
field.closure
tactic.abel.eval_neg
real.pi_gt_sqrt_two_add_series
mv_power_series.inv
pnat.xgcd_type.is_special'
order_embedding.refl
hyperreal.infinite_neg_mul_of_not_infinitesimal_pos_infinite_neg
direct_sum.to_module
dense_embedding.subtype_emb
list.take'
old_conv.whnf
localization.fraction_ring.equiv_of_equiv
abelianization.lift.unique
category_theory.limits.limit.cone
category_theory.whiskering_right
pell.yn_succ
bdd_below
omega.select_domain
encodable.of_equiv
where.binder_less_important
fp.rmode
rel.comp
metric.is_open_iff
omega.eq_elim
tactic.abel.eval_add
measure_theory.volume
uniform_space.separation_quotient
tactic.interactive.ac_mono_ctx.to_tactic_format
tactic.transfer
gaussian_int.div
monoid.mfoldl
pnat.gcd_a'
continuous_of_locally_uniform_limit_of_continuous
equiv.false_equiv_empty
pell.pell_zd_succ
category_theory.has_limits_of_reflective
tensor_product.lift.equiv
tactic.explode.entry
polynomial.nonzero_comm_semiring.of_polynomial_ne
omega.int.neg_elim
tactic.interactive.refine_one
category_theory.adjunction.comp
add_comm_group.is_Z_bilin
vector.traverse
real.mk_near_of_forall_near
omega.int.form
classical.all_definable
pmf.of_fintype
homeomorph.prod_assoc
is_basis.to_dual_flip
exists_eq_elim
sequence
is_bounded_ge_nhds
category_theory.limits.cocone_of_cone_left_op
auto.eelim
num.ppred
zmodp.legendre_sym
fin2.elim0
cau_seq.cauchy₃
writer_t.bind
category_theory.functor.map_cone_inv
tactic.interactive.mono_law
equiv.prod_sum_distrib
subalgebra.under
filter
free_abelian_group.of
equiv.Pi_curry
equiv.quot_equiv_of_quot'
list.sublists'_aux
units.mk_of_mul_eq_one
pell.xy_modeq_of_modeq
ordinal.unbounded_range_of_sup_ge
linarith.ineq_pf_tp
finset.empty
tactic.ext1
writer_t.monad_map
tactic.interactive.match_ac
lattice.fixed_points.prev
algebra.comap.of_comap
encodable.equiv_range_encode
function.embedding.equiv_of_surjective
infi_eq_elim
tactic.check_defn
hyperreal.lt_of_pos_of_infinitesimal
turing.TM1.stmts
supr_eq_elim
tactic.rewrite_all.congr.rewrite_at_lens
tactic.alias.alias_iff
filter.rmap
loc.to_string
linear_map.llcomp
real.pi_gt_three
category_theory.limits.has_colimit_of_equivalence_comp
equiv.pi_equiv_subtype_sigma
old_conv.current_relation
lebesgue_number_lemma_of_metric
finset.powerset
measure_theory.l1.simple_func.exists_simple_func_near
category_theory.adjunction.functoriality_unit'
fintype.fintype_prod_left
normed_space
rat_add_continuous_lemma
algebra.comap.has_scalar
category_theory.sum.associativity
tactic.mllist.take
measure_theory.outer_measure.to_measure
category_theory.iso.symm
filter.filter_product.abs_def
category_theory.limits.cone_left_op_of_cocone
exists.classical_rec_on
equiv.pempty_arrow_equiv_punit
nat.totient
finite_field.field_of_integral_domain
tactic.add_coinductive_predicate.coind_pred.corec_functional
simp_attr.sugar
mul_action.orbit_rel
tactic.using_texpr
Set.mem
linarith.comp_source.to_string
uniform_space.mk'
complex.lim_aux
fin_prod_fin_equiv
cardinal.cantor_function_aux
tactic.mllist.mfirst
tactic.rewrite_all.congr.rewrite_all
monoid.mfoldl.get
category_theory.limits.has_terminal
int.eq_mul_div_of_mul_eq_mul_of_dvd_left
tactic.find_matching_head
free_ring.map
tactic.explode.format_aux
real.Sup
category_theory.adjunction.right_adjoint_of_equiv
category_theory.Kleisli.id_def
tactic.interactive.get_monotonicity_lemmas
turing.TM1.supports_stmt
filter.is_cobounded_ge_of_top
tactic.tidy.core
tactic.ring.eval'
fderiv_within
is_basis.repr
znum.abs
category_theory.limits.cone.whisker
function.embedding.image
equiv.unique_congr
measure_theory.measure.of_measurable
tactic.interactive.revert_all
add_monoid_hom.mk'
tactic.local_cache.internal.def_local.kill_name
category_theory.is_equivalence.mk
initial_seg.le_add
set.pointwise_mul_semiring
tactic.ring.horner_expr.e
gt.is_strict_order
tactic.ring.horner_expr.pp
tactic.ring.ring_m
cau_seq.inv
equiv.prod_equiv_of_equiv_nat
equiv.set_congr
num.sub
mul_equiv.to_equiv
wseq.drop.aux
category_theory.functor.ulift_up_down
hyperreal.infinite_pos_def
tactic.add_edge
relator.right_unique
polynomial.degree_le
free_ring.lift
category_theory.whiskering_left
is_local_ring
category_theory.limits.coprod.desc
compact.realizer
ennreal.ennreal_equiv_nnreal
tactic.ring.get_transparency
multiplicity.finite_mul_aux
traversable
omega_int
finset.pi.cons
polynomial.div_mod_by_monic_aux
measure_theory.simple_func.ite
int.modeq
tactic.add_coinductive_predicate.coind_pred.le
tactic.interactive.same_operator
tactic.abel.eval
category_theory.functor.ulift_up
associates_int_equiv_nat
tactic.interactive.match_chaining_rules
equiv.sum_assoc
has_fderiv_at
omega.int.form.repr
is_bounded_linear_map.to_linear_map
pequiv.mul_matrix_apply
set.pointwise_mul_comm_semiring
conv.interactive.erw
list.permutations_aux
tactic.interactive.conv_rhs
is_glb
linarith.monad.elim_var
quotient_add_group.lift
cau_seq.of_near
omega.goal_domain_aux
dfinsupp.map_range_single
ideal.quotient.map_mk
set.pointwise_mul_semigroup
fintype.of_injective
option.rel
where.binder_priority
padic_seq.stationary_point_spec
pos_num.bit
complex.cau_seq_re
is_local_ring_hom
linarith.ineq.to_string
writer_t.pass
ideal.quotient.nonzero_comm_ring
equiv.false_arrow_equiv_punit
fintype.choose_x
encodable.decode_multiset
local_ring.residue_field.map
free_ring_punit_equiv_polynomial_int
tactic.chain
direct_sum.id
add_monoid.smul
pnat.xgcd_type.succ₂
abelianization.lift
fin.succ_rec
free_semigroup_free_magma
category_theory.limits.pushout.inl
turing.TM2.supports
auto.split_hyps
localization.lift
tactic.interactive.mk_congr_law
tactic.interactive.list_cast_of
list.map_last
category_theory.limits.pair_function
option_t.mk_label
traversable.foldl
complex.cau_seq_abs
mul_action.fixed_points
category_theory.limits.evaluate_functor_category_colimit_cocone
category_theory.op_op
bicompr.bitraverse
filter.rtendsto'
alg_hom.id
multiset.pi.empty
set.pointwise_one
category_theory.adjunction.left_adjoint_of_equiv
induced_orderable_topology'
tactic.add_coinductive_predicate.coind_pred.f₂_l
num.one_bits
num.to_znum
where.is_in_namespace_nonsynthetic
is_subgroup.normalizer_is_subgroup
fp.float.sub
tactic.interactive.op_induction
category_theory.limits.fork.ι
linarith.mk_non_strict_int_pf_of_strict_int_pf
tactic.interactive.solve_mvar
measure_theory.l1.simple_func.mk
sum_fin_sum_equiv
category_theory.monad.forget_creates_limits
tactic.interactive.refine_recursively
subalgebra.val
pos_num.sqrt_aux1
tactic.ring.get_cache
fp.float.sign'
linear_map.with_bound
pnat.mod_div
filter.map_at_top_eq_of_gc
znum.of_int'
omega.nat.push_neg
linarith.is_nat_int_coe
num.size
filter.pointwise_mul
category_theory.limits.fan.mk
category_theory.over.post
name.last_string
tactic.interactive.coinduction
is_cau_of_decreasing_bounded
roption.get_or_else
nat.unpaired
tactic.simp_bottom_up'
ordinal.lift.initial_seg
turing.TM1to0.tr_stmts
snum.rec'
free_group.free_group_unit_equiv_int
submodule.of_le
finset.attach_fin
quotient_add_group.ker_lift
well_founded.succ
omega.nat.preterm.val
category_theory.adjunction.mk_of_hom_equiv
local_of_is_local_ring
pequiv.matrix_mul_apply
metric.continuous_iff'
category_theory.representable
norm_cast.derive
category_theory.yoneda_pairing
Top.colimit
category_theory.limits.sigma.map
category_theory.limits.initial
equiv.inv
lazy_list.list_equiv_lazy_list
turing.TM2to1.stackel
omega.set_les
tactic.lambdas
category_theory.under.map
category_theory.ulift_functor
tactic.abel.cache.iapp
category_theory.limits.binary_fan.mk
tactic.interactive.list.minimum_on
traversable.mfoldr
measurable_equiv.set.prod
polynomial.map_injective
old_conv.apply_simp_set
category_theory.under.forget_limit_is_limit
localization.lift'
quotient_add_group.quotient
tactic.interactive.mono_cfg
pell.xz
continuous_map.compact_open.gen
infinite
equiv.perm.is_cycle_swap_mul_aux₁
omega.get_ees
functor.add_const
tactic.interactive.repeat_until
pell.y_dvd_iff
CommRing.colimits.cocone_morphism
tactic.interactive.simp_functor
pi.linear_independent_std_basis
measurable_equiv.symm
equiv.nat_sum_punit_equiv_nat
tactic.mk_assoc
ideal.quotient.mk
equiv.prod_pempty
linarith.preferred_type_of_goal
topological_space.open_nhds.inclusion
category_theory.limits.has_pushouts
auto.normalize_hyp
category_theory.limits.colimit.ι
category_theory.under
quadratic_reciprocity_aux.filter_range_p_mul_q_div_two_eq
trunc.rec_on_subsingleton
ring_equiv.to_add_equiv
real.Inf
tactic.repeat_with_results
category_theory.monad.algebra.hom.id
is_complete
is_basis.coord_fun
omega.int.is_nnf
declaration.update_with_fun
trunc.bind
cau_seq.completion.mk
omega.int.form.holds
turing.TM2to1.tr_stmts₁
category_theory.Kleisli.comp_def
free_comm_ring.restriction
quotient_group.map
omega.nat.form.repr
infinite.nat_embedding
linarith.mul_expr
omega.int.dnf_core
category_theory.comma.nat_trans
list.head'
omega.int.preterm
tactic.add_coinductive_predicate.coind_pred
equiv.arrow_congr
power_series.order_ge
pgame.numeric.move_left_lt
free_semigroup.lift
prime_multiset.of_pnat_multiset
equiv.to_embedding
category_theory.equivalence.mk
category_theory.Aut
tactic.assoc_rewrite_hyp
open_locale_cmd
omega.int.prove_lia
traversable.length
omega.nat.nonneg_consts_core
category_theory.hom_of_element
tactic.closure.merge
category_theory.functor.inv
list.sublists_len
turing.TM1.eval
tactic.assoc_rewrite
category_theory.limits.has_initial
computation.mem
tactic.local_cache.internal.def_local.present
dfinsupp.lsingle
tactic.enum_assoc_subexpr'
state_t.mk_label
apply_fun_name
homeomorph.refl
auto.classical_normalize_lemma_names
equiv.perm.disjoint
category_theory.limits.terminal
equiv.mul_right
ideal.of_polynomial
category_theory.limits.pullback_cone.fst
filter.pointwise_add
mv_polynomial.restrict_total_degree
omega.prove_forall_mem_eq_zero
real.of_near
tactic.closure.prove_eqv
category_theory.has_hom.hom.op
euclidean_domain.xgcd_aux
int.bit_cases_on
ideal.comap
omega.nat.prove_sub_free
dioph.xn_dioph
linarith.partition_by_type
omega.terms.fresh_index
wseq.destruct_join.aux
multiset.powerset_aux
floor_ring
sum.traverse
add_equiv.trans
tactic.interactive.auto_simp_lemma
category_theory.ess_surj.iso
prime_multiset.of_nat_multiset
tactic.abel.cache.int_to_expr
powers
category_theory.adjunction.has_colimit_of_comp_equivalence
omega.nat.dnf
linear_map.compl₂
algebraic_geometry.PresheafedSpace.id
relator.bi_total
tactic.abel.eval_smul
open_add_subgroup.sum
equiv.subtype_subtype_equiv_subtype_exists
pos_num.ldiff
filter.rtendsto
is_group_hom.ker
category_theory.limits.limit
pnat.mod
tactic.rcases_patt_inverted.invert
category_theory.limits.sigma.ι
pell.asq_pos
rel.dom
tactic.mllist.join
znum.mul
quot.congr
inducing
tactic.local_cache.internal.def_local.is_name_dead
finsupp.split
omega.nat.terms.vars
filter.Liminf_le_Limsup
linarith.ineq.is_lt
fintype.of_subsingleton
homeomorph.sigma_prod_distrib
where.resolve_var
category_theory.functor.adjunction
is_seq_closed
pnat.lcm
multiset.powerset_len
tactic.interactive.apply_rel
pnat.xgcd_type.r
tactic.ring2.horner_expr.add_aux
tendsto_pow_at_top_at_top_of_gt_1
tactic.mllist.monad_lift
padic_norm.neg
nat.partrec.code
fin.succ_rec_on
tactic.ring.cache.cs_app
filter.pmap
set.seq
lattice.fixed_points
tensor_product.smul.aux
simp_attr.sugar_nat
id.mk
measure_theory.outer_measure.map
conv.replace_lhs
tactic.interactive.mk_one_instance
int.div_eq_div_of_mul_eq_mul
complex.sinh
lists.of_list
measure_theory.ae_eq_fun.lift_pred
erased.join
pos_num.of_znum
semiquot.of_trunc
pos_num.shiftr
polynomial.rec_on_horner
category_theory.limits.pullback.fst
category_theory.core
finset.lt_wf
tactic.interactive.return_cast
real.mk_le_of_forall_le
real.mk
nzsnum.not
category_theory.limits.types.limit_is_limit
order_iso.of_surjective
encodable.decode_list
linarith.to_comp
tactic.find_ancestors
tactic.rcases.continue
category_theory.limits.preserves_limit
num.div2
hyperreal.infinitesimal_def
power_series.order_mul_ge
homeomorph.symm
category_theory.equivalence.refl
module.direct_limit
tactic.mllist.filter_map
simp_attr.split_if_reduction
monoid.foldr.of_free_monoid
pos_num.lor
category_theory.limits.has_finite_coproducts
omega.get_gcd
free_magma.lift
euclidean_domain
metric.uniform_continuous_iff
category_theory.adjunction.adjunction_of_equiv_right
turing.reaches₀
turing.TM1to0.tr_cfg
equiv.decidable_eq
gt.is_trichotomous
tactic.ring2.horner_expr.neg
num.of_nat'
omega.rhs
quotient_add_group.quotient_ker_equiv_of_surjective
category_theory.limits.binary_fan
tactic.interactive.find
tactic.interactive.parse_list
ennreal.of_real_eq_coe_nnreal
tactic.goals
equiv.subtype_quotient_equiv_quotient_subtype
tactic.add_coinductive_predicate.coind_pred.construct
turing.TM1to0.Λ'
Top.presheaf
tactic.interactive.abel.mode
localization.away
functor.add_const.mk
pnat.xgcd_type.z
finsupp.supported_eq_span_single
omega.int.preterm.add_one
fp.float_cfg
topological_add_group.to_uniform_space
functor.comp.run
category_theory.limits.is_colimit.mk_cocone_morphism
category_theory.limits.colim_coyoneda
associated.setoid
equiv.comm_semiring
function.restrict
tactic.mk_assoc_pattern
category_theory.limits.coequalizer.π
pell.eq_of_xn_modeq_lem1
tactic.iff_mpr_core
tactic.rewrite_all.congr.rewrite_without_new_mvars
sylow.mk_vector_prod_eq_one
tactic.explode_expr
pequiv.refl
dfinsupp.to_module
omega.form_domain
hyperreal.lt_of_tendsto_zero_of_pos
tactic.tidy.tidy_attribute
is_cyclic
pell.is_pell
binder_eq_elim.check
order_embedding.trans
mul_action.comp_hom
pos_num.pred_to_nat
order_embedding.nat_lt
CommRing.colimits.desc_morphism
tactic.explode.pad_right
finset.pi.empty
empty.elim
pell.x_increasing
pos_num.add
matrix.sub_right
category_theory.limits.has_binary_products
tactic.with_impl_graph
measure_theory.ae_eq_fun.smul
pell.y_increasing
list.reduce_option
category_theory.limits.evaluate_functor_category_limit_cone
finset.map
tactic.interactive.mono_law.to_tactic_format
where.get_variables_core
simple_add_group
tactic.interactive.side
measure_theory.ae_eq_fun.integrable_smul
equiv.punit_equiv_punit
free_comm_ring_pempty_equiv_int
category_theory.limits.pi.lift
linear_map.mk₂
num.lor
tactic.rewrite_all.congr.rewrite_is_of_entire
omega.nat.sub_fresh_index
omega.sgm
finsupp.restrict_support_equiv
category_theory.limits.map_pair
fin.add_nat_val
finsupp.dom_lcongr
category_theory.limits.cocone_morphism
norm_num.prove_min_fac
list.map_with_index_core
norm_num.derive
tactic.abel.cache.app
emetric.totally_bounded_iff
norm_num.derive1
nonempty_interior_of_Union_of_closed
omega.int.form.fresh_index
to_additive.aux_attr
list.tfae
equiv.list_equiv_of_equiv
nondiscrete_normed_field
nat.strong_rec'
ideal.quotient.lift
Meas
finsupp.frange
fin_zero_equiv
pell.xn_modeq_x4n_sub
sum.bitraverse
encodable.encode_subtype
relation.join
omega.nat.neg_elim_core
category_theory.limits.has_pullbacks
perfect_closure.has_inv
category_theory.limits.initial.to
omega.gcd
turing.tape.map
zorn.chain_closure
quotient_add_group.eq_class_eq_left_coset
znum.div
pell.pell_eqz
turing.TM2to1.stmt_st_rec
tactic.local_cache.internal.block_local.present
ordinal.order_iso_out
exists_pos_bound_of_bound
CommRing.colimits.prequotient
tactic.alias.alias_direct
equiv.symm
omega.nat.form.equiv
category_theory.curry_obj
trunc.rec_on
matrix
real.tanh
category_theory.functor.sections
pnat.gcd_d
filter.infi_sets_eq'
category_theory.limits.has_coproducts
auto.split_hyp
tactic.assert_fresh
get_ext_subject
pSet.resp.eval_aux
omega.nat.neg_elim
rel.preimage
measure_theory.l1.simple_func
direct_sum.component
pos_num.shiftl
category_theory.iso
omega.prove_unsats
order_dual
omega.abort
quotient.choice
algebra.of_id
pell.eq_pow_of_pell_lem
function.embedding.congr
computation.lift_rel_aux
pnat.gcd_z
linear_map.comp
tactic.interactive.compare
pell.eq_pow_of_pell
holor_index.drop
equiv.perm.card_support_swap
filter.infi_sets_eq
ideal.span
times_cont_diff.times_cont_diff_fderiv_apply
monoid.mfoldl.mk
encodable.fintype_pi
old_conv.apply
is_lawful_traversable
filter.tendsto_at_top'
category_theory.sum.inverse_associator
denumerable.eqv
category_theory.iso.hom_congr
tactic.interactive.mono_head_candidates
tactic.alias.alias_cmd
AddCommMon
turing.TM0to1.tr
category_theory.discrete
equiv.semiring
znum.zneg
category_theory.uncurry
tactic.ring.get_atom
wseq.mem
tactic.ancestor_attr
finsupp.lapply
linarith.comp.coeff_of
list.of_fn_aux
omega.clauses.sat
omega.nat.term.vars_core
tactic.split_ifs
tactic.ring2.horner_expr.add
cfilter.to_realizer
category_theory.limits.colimit.hom_iso
linarith.mul_neg
function.embedding.of_not_nonempty
relator.left_total
equiv.subtype_pi_equiv_pi
Top.limit_is_limit
tactic.interactive.bin_op
function.embedding.subtype_map
nzsnum.sign
normed_group.tendsto_nhds_zero
category_theory.functor.obj_preimage
category_theory.full_subcategory_inclusion
linarith.norm_hyp_aux
category_theory.prod.braiding
pfun.core
nzsnum.bit0
associates.factor_set.coe_add
onote.oadd_lt_oadd_1
measure_theory.ae_eq_fun.mk
omega.type_domain
tactic.ring.horner_expr
turing.TM1to1.read_aux
computation.parallel.aux1
category_theory.limits.cofork.of_π
Mon.colimits.colimit_cocone
multiset.sup_le
ordinal.initial_seg_out
category_theory.limits.colimit.cocone
free_semigroup.map
dfinsupp.mk
equiv.bool_equiv_punit_sum_punit
tactic.interactive.rep_arity
matrix.row
category_theory.limits.cones.postcompose
category_theory.evaluation_uncurried
pmf.support
pmf.bind
equiv.cast
unique_unique_equiv
tactic.interactive.mono_function.to_tactic_format
tactic.rcases_patt_parse
linarith.update
tactic.mllist.mmap
turing.TM0.machine.map
adjoin_root.mk
metric.mem_ball_self
tactic.interactive.functor_derive_handler
finset.map_embedding
tactic.interactive.get_operator
category_theory.nat_iso.of_components
omega.term_domain
category_theory.limits.has_binary_coproducts
category_theory.nat_iso.is_iso_app_of_is_iso
filter.mk_of_closure
linarith.elim_with_set
algebra.adjoin_eq_range
category_theory.limits.cocones.precompose_comp
category_theory.prod.symmetry
old_conv.apply_propext_lemmas_core
set.sigma_to_Union
with_top.canonically_ordered_comm_semiring
is_integral
set.fintype_of_fintype_image
free_monoid
omega.set_eqs
linarith.rem_neg
pell.dnsq
fin_one_equiv
measure_theory.simple_func.restrict
nat.partrec'.vec
tactic.interactive.lawful_traversable_derive_handler'
tactic.interactive.with_prefix
num.psub
omega.clause.holds
list.mmap_accumr
card_trivial
tactic.pformat
mem_nhds_orderable_dest
tactic.interactive.apply_normed
erased.equiv
tactic.is_default_local
list.forall₂
equiv.prod_assoc
list.to_alist
holor_index.take
expr.of_int
tactic.alias.mk_iff_mp_app
num.cmp
list.sublists_aux
is_totally_disconnected
mv_polynomial.indicator
omega.coeffs_reduce
category_theory.limits.preserves_limits
tactic.mllist.uncons
is_null_measurable
fp.of_pos_rat_dn
nhds_contain_boxes
where.trace_end
category_theory.limits.walking_cospan.hom.comp
hyperreal.infinite_pos_iff_infinite_of_pos
function.graph
measurable_equiv.prod_comm
ext_param_type
linarith.norm_hyp
tactic.mllist
is_lawful_bitraversable
linarith.map_of_expr_mul_aux
complex.real_prod_equiv
isometric.trans
tactic.rcases_patt.invert
ge.is_preorder
function.embedding.refl
turing.TM1to1.step_aux_move
tactic.interactive.mono_aux
lattice.fixed_points.prev_fixed
list.func.pointwise
category_theory.functor.ulift_down_up
snum.neg
turing.TM2to1.stackel_equiv
tactic.apply_mod_cast
directed_order
turing.tape.mk
linarith.cast_expr
writer_t.mk_label
equiv.set.univ
omega.find_scalars
monoid.foldl.get
pell.xy_coprime
where.get_opens
pell.xz_succ_succ
set.fintype_subset
old_conv.congr_core
pnat.div_exact
list.of_fn_nth_val
localization.away.inv_self
tactic.mllist.bind_
category_theory.yoneda
category_theory.limits.pullback_cone
equiv.perm.eq_swap_of_is_cycle_of_apply_apply_eq_self
linear_map.compr₂
writer_t.pure
tactic.drop_binders
magma.free_semigroup.of
finsupp.finsupp_prod_equiv
equiv.set.prod
mv_polynomial.evalᵢ
tactic.interactive.loc.get_local_uniq_names
turing.TM2to1.tr
with_one.map
measure_theory.ae_eq_fun.eintegral
measurable_equiv.set.singleton
free_abelian_group
measure_theory.simple_func.map
tactic.interactive.lawful_functor_derive_handler
tactic.derive_field_subtype
tactic.rewrite_all.congr.expr_lens
decidable_of_iff
filter.Liminf_le_Liminf_of_le
set.pointwise_add_add_monoid
ennreal.tendsto_nhds
free_group.free_group_empty_equiv_unit
tactic.use
category_theory.comma.fst
filter.limsup_eq_infi_supr_of_nat
tactic.interactive.bin_op_left
lean.parser.emit_code_here
pos_num.of_nat
cont_t.run
tactic.mllist.fixl_with
tactic.mllist.of_list
tactic.local_def_value
turing.eval
tactic.exact_mod_cast
omega_nat
tactic.impl_graph
power_series.mk
CommRing.colimits.cocone_fun
turing.TM1to1.tr_tape'
linear_map.sup_quotient_to_quotient_inf
holor.assoc_right
expr.replace_with
category_theory.is_iso_of_fully_faithful
finmap.foldl
cardinal.aleph'.order_iso
measurable_equiv.set.image
turing.TM2to1.tr_stk
perfect_closure.r
tactic.fill_args
monoid.mfoldl.of_free_monoid
tactic.rewrite_all.tracked_rewrite.eval
omega.nat.preterm.prove_sub_free
category_theory.monad.comparison
category_theory.comma
measure_theory.l1.smul
summable_iff_vanishing_norm
algebra.to_top
simp_attr.functor_norm
Top.presheaf.pushforward.id
is_bounded_bilinear_map
tactic.mk_local
omega.nat.nnf
category_theory.limits.reflects_limits
category_theory.functor.map_cocone_morphism
measure_theory.measure
omega.form_wf
ideal.is_principal
category_theory.functor.flip
pfun.res
tensor_product.curry
tactic.trace_output
function.embedding.sigma_congr_right
category_theory.prod.inverse_associator
tactic.interactive.compact_decl_aux
old_conv.save_info
tactic.rcases_patt_inverted.format
turing.TM1.step
emetric.exists_ball_subset_ball
Top.presheaf.pushforward
binder_eq_elim.old_conv
pell.xn_one
tactic.higher_order_attr
hyperreal.infinite_pos_mul_of_infinite_pos_not_infinitesimal_pos
tensor_product.congr
tactic.mllist.concat
category_theory.Aut.units_End_eqv_Aut
algebra_map
tactic.op_induction.find_opposite_hyp
category_theory.limits.has_colimit_of_iso
is_subgroup.left_coset_equiv_subgroup
erased.bind
omega.nat.form.sub_subst
fin.find
snum.bits
string.is_suffix_of
pell.modeq_of_xn_modeq
fp.valid_finite
measure_theory.lintegral_eq_nnreal
int.induction_on'
omega.int.neg_free
is_subgroup.normalizer
complex.sin
CommRing.colimits.colimit
tensor_product.lcurry
tactic.abel.eval'
snum.sub
vector.m_of_fn
function.embedding.prod_congr
cauchy_seq_bdd
is_cau_seq.cauchy₃
computation.cases_on
category_theory.limits.parallel_pair
principal_seg.trans
pell.xn_succ_succ
units.to_Aut
is_lawful_bifunctor
tactic.rcases_hint.continue
bounded_continuous_function.equicontinuous_of_continuity_modulus
equiv.nat_equiv_nat_sum_punit
tactic.assertv_fresh
turing.TM1to0.tr_aux
category_theory.coyoneda.is_iso
tactic.interactive.collect_struct'
category_theory.prod.associator
nat.elim
linarith.validate
tactic.interactive.match_rule
writer_t.adapt
equiv.zero_ne_one_class
tactic.add_symm_proof
pi.lex
ring_equiv.to_mul_equiv
lists.induction_mut
ideal.quotient_inf_to_pi_quotient
free_semigroup
principal_ideal_domain
sum.traverse_map
category_theory.over.forget
category_theory.ulift_trivial
infi_real_pos_eq_infi_nnreal_pos
binder_eq_elim.pull
tactic.op_induction.is_opposite
omega.update
units.map
tactic.interactive.find_one_difference
omega.nat.term.vars
Mon.colimits.desc_fun
tactic.explode.entries.find
linarith.linarith_monad
list.choose
znum.cmp
filter.infi_neq_bot_of_directed
abelianization.of
tactic.assoc_refl'
functor.const.mk
ge_iff_le
omega.revert_cond_all
pnat.xgcd_type.b
equiv.sigma_subtype_preimage_equiv
category_theory.limits.reflects_limits_of_shape
quotient.out'
tactic.interactive.derive_functor
quotient.congr
except_t.pass_aux
pell.xn_modeq_x2n_sub_lem
tactic.ring2.horner_expr.pow
tactic.mllist.range
tactic.var_names
matrix.sub_down_left
equiv.sigma_congr_right
find_cmd
bilin_form.to_linear_map
equiv.plift
cau_seq
ring_equiv
fin.clamp
tactic.interactive.mono_key
znum.bit1
tactic.enum_assoc_subexpr
nat.subtype.denumerable
free_group.map.aux
has_norm
tactic.assumption_mod_cast
pos_num.is_one
num.of_znum
measure_theory.l1.mk
emetric.nhds_eq
ordinal.CNF_sorted
rat.add
mtry
homeomorph.homeomorph_of_continuous_open
equiv.equiv_pempty
finsupp.supported_equiv_finsupp
matrix.diagonal
tactic.repeat_count
localization.non_zero_divisors
hidden
category_theory.functor.right_unitor
complex.tan
with_bot
adjoin_root.of
linarith.mk_coe_nat_nonneg_prfs
continuous.comap
localization.map
uniform_space.sep_quot_equiv_ring_quot
category_theory.limits.walking_span.hom.comp
old_conv.lhs
tactic.interactive.derive_traverse
tactic.local_cache.internal.def_local.hash_byte
linarith.pcomp.is_contr
pell.matiyasevic
euclidean_domain.gcd
Mon.colimits.relation
linear_independent_monoid_hom
omega.get_les
equiv.comm_ring
tactic.merge_list
equiv.decidable_eq_of_equiv
real.sin_gt_sub_cube
snum.test_bit
Top.presheaf.pushforward.comp
order_iso.symm
num.bit0
tactic.explode.entries.head
tactic.perform_nth_rewrite
omega.ee_state
topological_space.opens.map_id
tactic.abel.normal_expr.to_string
turing.TM1.stmts₁
ctop.realizer.nhds
category_theory.functor.to_cone
omega.elim_eq
uniform_embedding
where.find_var
expr.local_binder_info
omega.nat.form.implies
omega.rev_lia
list.find_indexes_aux
Set.map_definable_aux
topological_space.opens.gi
lists.is_list
cauchy_product
nat.partrec.code.of_nat_code
category_theory.limits.equalizer
category_theory.adjunction.functoriality_right_adjoint
equiv.is_lawful_traversable'
where.trace_opens
category_theory.nat_iso.of_isos
linarith.find_contr
magma.free_semigroup
old_conv.interactive.whnf
fp.div_nat_lt_two_pow
omega.run
znum.mod
group.in_closure
category_theory.limits.coequalizer
pell.xn_modeq_x2n_add
tactic.ring.ring_m.run
old_conv.interactive.find
tactic.mk_theorem
ideal.quotient
category_theory.limits.equalizer.lift
equiv.set.pempty
is_noetherian_ring
equiv.add_comm_semigroup
ennreal.nhds_of_ne_top
set.Union_eq_sigma_of_disjoint
snum.succ
category_theory.functor.map_iso
except_t.mk_label
module.direct_limit.totalize
category_theory.limits.is_colimit.iso_unique_cocone_morphism
measure_theory.simple_func.has_scalar
tactic.all_rewrites_using
lists.atom
set.pointwise_mul
char_p.char_is_prime_of_ge_two
tactic.calculated_Prop
omega.rev_lna
pos_num.of_nat_succ
traversable.free.map
equiv.comm_semigroup
omega.term.to_string
dlist.list_equiv_dlist
dfinsupp.decidable_eq
tactic.interactive.ac_mono_ctx_ne
omega.nat.preterm.sub_free
rat.sqrt
polynomial.eval₂_zero
omega.int.canonize
category_theory.limits.has_coequalizers
category_theory.limits.reflects_colimits_of_shape
encodable.of_left_inverse
dlist.join
complex.I
lists'.cons
measure_theory.measure.map
category_theory.limits.colimit
equiv.pempty_prod
metric.uniformity_edist'
tactic.interactive.match_ac'
omega.coeffs.val_between
equiv.integral_domain
category_theory.limits.cocones.forget
old_conv.find_pattern
omega.cancel
turing.pointed_map
AddCommMon.of
tactic.interactive.mk_paragraph_aux
matrix.mul_vec
writer_t.call_cc
category_theory.adjunction.functoriality_unit
tactic.interactive.derive_lawful_functor
snum.czadd
tactic.rewrite_all.congr.rewrite_all_lazy
tactic.add_coinductive_predicate.coind_pred.rec'
omega.term.sub
sequence_of_directed
continuous_linear_map
is_bounded_bilinear_map.deriv
rat.nonneg
omega.nat.prove_lna
equiv.add_group
omega.int.prove_univ_close
equiv.perm.cycle_of
category_theory.currying
category_theory.functor.ulift_down
where.resolve_vars
category_theory.limits.functor_category_limit_cone
le_of_forall_ge_of_dense
equiv.perm.is_cycle_swap
Top.presheaf.pushforward_eq
exists_gpow_eq_one
tactic.subobject_names
tactic.explode
category_theory.left_adjoint
dfinsupp.map_range_def
set.pointwise_inv
auto.add_simps
list.map_with_index
function.embedding.arrow_congr_right
filter.limsup
category_theory.limits.cocones.precompose_id
pequiv.trans_single_of_eq_none
tensor_product.mk
category_theory.limits.is_colimit.of_iso_colimit
measure_theory.simple_func.eapprox
equiv.pnat_equiv_nat
tactic.add_theorem_by
uniform_continuous
tactic.interactive.work_on_goal
pell.xn_zero
equiv.empty_sum
omega.term.val
linarith.mk_cast_eq_and_nonneg_prfs
category_theory.limits.limit.is_limit
mul_action.mul_left_cosets
direct_sum.to_group
turing.tape.move
measure_theory.integrable
category_theory.category_struct
mem_uniformity_edist
category_theory.limits.preserves_limits_of_shape
omega.clause.unsat
filter.pointwise_zero
tactic.elim_gen_prod
omega.nat.form.sub_terms
category_theory.comma.map_right
dfinsupp.pre
gt.is_antisymm
tactic.ring.eval_add
filter.tendsto_at_top_at_bot
omega.symdiv
quotient_add_group.left_rel
category_theory.limits.pi.π
tactic.ring.eval
is_conj
semiquot.pure
topological_space.open_nhds.map
denumerable.lower'
tactic.rcases_parse_depth
min_le_add_of_nonneg_right
conv.slice_rhs
is_clopen
snum.drec'
rat_inv_continuous_lemma
vector3.nil_elim
category_theory.functor.fun_obj_preimage_iso
nzsnum.head
tactic.file_simp_attribute_decl
tactic.mllist.squash
cau_seq.abv_pos_of_not_lim_zero
mzip_with'
Well_order
category_theory.functor.associator
tactic.explode.may_be_proof
ordinal.typein.principal_seg
cau_seq.completion.discrete_field
list.revzip
turing.TM2.step_aux
auto.normalize_hyps
tactic.interactive.parse_ac_mono_function
znum.gcd
category_theory.limits.prod.lift
turing.TM2to1.tr_cfg
to_additive.map_namespace
tactic.rewrite_all.tracked_rewrite
real.comm_ring_aux
int.to_nat'
tactic.pformat.mk
tactic.local_cache.internal.def_local.FNV_OFFSET_BASIS
ideal.is_maximal
loc.to_string_aux
tactic.abel.normalize_mode
measure_theory.simple_func.approx
fp.to_rat
relation.map
tactic.local_cache.internal.block_local.clear
add_equiv.to_add_monoid_hom
fintype.bij_inv
pnat.xgcd_type.mk'
pell.n_lt_a_pow
real.sqrt
omega.nat.preterm.sub_terms
cau_seq.cauchy₂
pell.yz_sub
lattice.conditionally_complete_linear_order
bifunctor
order_iso.sum_lex_congr
is_add_subgroup.mem_trivial
tactic.tidy.cfg
equiv.swap_core
filter.filter_product.of_seq
equiv.Prop_equiv_bool
category_theory.iso_whisker_left
tactic.contradiction_with
measure_theory.l1.simple_func.to_simple_func
pell.eq_of_xn_modeq_le
lean.parser.get_namespace
tactic.transport_with_prefix_dict
fin.cases
principal_seg.equiv_lt
filter.ptendsto'
tactic.interactive.mk_congr_args
omega.clear_unused_hyp
linarith.comp.add
omega.find_ees
free_add_monoid
lattice.complete_lattice.copy
is_noetherian
hyperreal.neg_lt_of_tendsto_zero_of_pos
metric.uniform_embedding_iff
tactic.closure.root
metric.mem_closed_ball_self
tactic.rewrite_all.congr.app_map
metric.completion.mem_uniformity_dist
tensor_product.assoc
category_theory.limits.cones.postcompose_equivalence
tactic.coinductive_predicate
tactic.mllist.fix
rat.inv
quot.rep
simp_attr.parity_simps
metric.uniformity_dist'
hyperreal.infinite_pos_iff_infinite_of_nonneg
measurable_equiv.prod_congr
Mon.colimits.colimit_type
equiv.set.image
category_theory.comma.map_left_comp
writer
is_ring_hom.ker
hyperreal.gt_of_neg_of_infinitesimal
category_theory.limits.preserves_colimit
pfun.graph'
equiv.sum_equiv_sigma_bool
computation.bisim_o
category_theory.limits.types.colimit
category_theory.limits.prod.fst
prime_multiset.to_pnat_multiset
function.embedding
measure_theory.measure.with_density
pos_num.transfer_rw
partial_order.lift
nat.le_rec_on
rel.inv
Mon.colimits.desc_fun_lift
multiset.le_inf
equiv.sum_arrow_equiv_prod_arrow
normal_of_eq_add_cosets
zmod
finsupp.curry
tensor_product.lid
measurable_equiv.set.range_inr
turing.TM0to1.Λ'
right_coset
tactic.alias.get_lambda_body
pell.yn_ge_n
AddMon.of
multiset.powerset_len_aux
tactic.strip_prefix'
padic_norm_z
equiv.perm.swap_factors_aux
tactic.mk_replacer₂
omega.sym_sym
finsupp.comap_domain
category_theory.nat_trans.left_op
category_theory.limits.coprod.map
list.mmap_accuml
equiv.has_neg
with_zero
order_embedding.collapse_F
smooth_manifold_with_corners
turing.TM1to1.tr_tape
tactic.tfae.mk_implication
auto.normalize_negations
finset.insert_none
tactic.abel.normal_expr.term'
localization.away_to_away_right
tactic.mk_patterns
wseq.tail.aux
omega.find_neg_const
classical.exists_cases
filter.ultrafilter.map
num.nat_size
tactic.trace_error
tactic.interactive.mk_mapp_aux'
tactic.local_cache.internal.def_local.FNV_PRIME
is_cobounded_ge_nhds
tactic.def_replacer_cmd
add_monoid_hom.add
pell.is_pell_conj
cardinal.aleph_idx.order_iso
nat.sqrt_aux
fin.tail
cont_t.monad_lift
traversable.fold_map
filter.Liminf_le_of_le
dfinsupp.subtype_domain_sum
hash_map.valid.modify
traversable.mfoldl
tactic.rcases_hint_core
filter.mem_infi
Set.subset
set.pointwise_mul_action
category_theory.equivalence.to_adjunction
metric_space.replace_uniformity
option.lift_or_get
turing.tape.mk'
tactic.expr_list_to_list_expr
measure_theory.l1
denumerable.equiv₂
list.erase_dupkeys
is_closed_map
nat.partrec.code.evaln
equiv.sigma_preimage_equiv
subgroup_units_cyclic
tactic.interactive.squeeze_simpa
equiv.map
denumerable.raise'
finset.max
multiset.traverse
omega.term.neg
order_iso.refl
complex.abs
Mon.colimits.colimit
finmap.all
omega.term.div
omega.set_ees
Module.of
num.lxor
additive
uniform_space.separation_setoid
omega.factor
pnat.gcd_w
pell.az
fp.next_up
conv.interactive.ring2
tactic.interactive.parse_assoc_chain
pSet.definable.eq_mk
left_coset
continuous_map.coev
tactic.interactive.guard_hyp_nums
isometric.refl
lean.parser.of_tactic'
tactic.local_cache.internal.def_local.apply_tag
emetric.cauchy_seq_iff'
tactic.fin_cases_at
omega.clear_unused_hyps
omega.int.push_neg
string.split_on
uniform_space.completion.map₂
matrix.vec_mul
omega.clause.sat
binder_eq_elim.check_eq
equiv.subtype_congr_prop
adjoin_root.lift
num.add
tactic.interactive.lawful_traversable_derive_handler
encodable.encode_sum
filter.map_div_at_top_eq_nat
tactic.interactive.parse_assoc_chain'
dfinsupp.single
tactic.op_induction
tactic.interactive.obtain_parse
conv.interactive.norm_num
set.countable.to_encodable
multiples
category_theory.limits.coequalizer.desc
pell.is_pell_norm
measure_theory.integral
num.land
tactic.classical
nat.primrec'.vec
uniform_inducing
zorn.is_max_chain
linarith.get_comps
int.shift2
filter.is_bounded_default
turing.TM2to1.st_var
pgame.numeric.lt_move_right
category_theory.limits.coprod.inr
mul_action.orbit
tactic.mllist.filter
pnat.xgcd_type.q
tactic.interactive.rec.to_tactic_format
equiv.quot_equiv_of_quot
writer_t.monad_cont
turing.TM2.stmts
omega.goal_domain
option_t.pass_aux
eckmann_hilton.is_unital
equiv.perm.is_cycle
lazy_list.thunk.mk
ideal.radical_pow
old_conv.funext
fp.float.is_zero
topological_space.open_nhds
tactic.local_cache.internal.run_once_under_name
tactic.unprime
pmf.bernoulli
multiset.decidable_exists_multiset
category_theory.iso.op
functor.comp.map
pfun.image
polynomial.comp
omega.eqelim
where.collect_by_aux
asymptotics.is_O
pos_num.cmp
equiv.of_bijective
metric.to_glue_r
is_noetherian_iff_well_founded
equiv.set.singleton
nat.partrec.code.curry
ctop.realizer.id
tactic.clear_aux_decl
roption.restrict
category_theory.functor.op_hom
tactic.abel.termg
linear_map.lsmul
matrix.sub_down
computation.is_bisimulation
tactic.ring.cache
equiv.discrete_field
rel
category_theory.functor.left_op
expr.get_pis
opposite.op_induction
where.strip_pi_binders
finsupp.total_on
measure_theory.simple_func.seq
category_theory.adjunction.cocones_iso
category_theory.limits.cones.postcompose_id
canonically_ordered_comm_semiring
alist.foldl
category_theory.equivalence.fun_inv_id_assoc
old_conv.match_pattern
rel.core
adjoin_root.root
filter.rcomap'
real.sinh
omega.get_eqs
category_theory.Kleisli
multiset.length_ndinsert_of_not_mem
num.bit
emetric.uniform_embedding_iff
category_theory.equivalence.inv_fun_id_assoc
pell.eq_of_xn_modeq
tactic.instance_cache
writer_t.tell
omega.elim_var_aux
equiv.empty_equiv_pempty
associates.prime
order_embedding.lt_embedding_of_le_embedding
tactic.rintro
turing.TM2to1.Λ'
real.sin
equiv.prop_equiv_punit
tactic.ring2.horner_expr.mul_aux
category_theory.limits.cofork.π
tactic.iff_mp_core
computation.parallel_rec
is_bounded_under_ge_of_tendsto
hyperreal.infinitesimal_pos_iff_infinite_pos_inv
category_theory.limits.has_limits_of_shape_of_equivalence
tactic.apply_assumption
tactic.find_if_cond
function.embedding.sum_congr
where.get_namespace_core
equiv.is_lawful_traversable
finsets
encodable.encodable_of_list
where.trace_includes
pos_num.cmp_to_nat
lean.parser.get_includes
tactic.rewrite_all.congr.expr_lens.to_sides
orderable_topology_of_nhds_abs
linarith.mul_eq
where.get_includes_core
free_comm_ring.map
pnat.gcd_y
tactic.interactive.ac_mono_ctx'.traverse
expr.get_app_fn_args
decidable_of_iff'
fintype_perm
turing.TM2.reaches
algebra.comap.ring
measure_theory.outer_measure.Inf_gen
tactic.match_assoc_pattern'
padic_norm_e.rat_norm
function.embedding.trans
omega.term.fresh_index
list.extractp
category_theory.nat_iso.op
filter.lift_infi'
equiv.perm.sign_bij_aux
quotient_add_group.quotient_ker_equiv_range
pell.xn_modeq_x4n_add
tensor_product.lift_aux
comp.seq
submodule.fg
encodable.decidable_eq_of_encodable
tree.repr
category_theory.functor.of_function
metric.exists_ball_subset_ball
ge_of_eq
hyperreal.infinite_pos_iff_infinitesimal_inv_pos
category_theory.monad.forget_creates_limits.cone_point
omega.preprocess
nonneg_comm_group.to_decidable_linear_ordered_comm_group
Gromov_Hausdorff.aux_gluing
old_conv.trace_lhs
with_top
tactic.assoc_root
equiv.group
pos_num.nat_size
homeomorph.mul_right
linear_order.lift
norm_num.eval_div_ext
interaction_monad.get_result
category_theory.comma.map_left_id
tactic.interactive.mk_pattern
category_theory.monad.forget_creates_limits.c
equiv.add_comm_group
equiv.set.congr
polynomial.pow_add_expansion
relator.bi_unique
free_group.to_group.aux
gt_from_lt
free_group.mk
uniformity_edist
tactic.interactive.congr_core'
category_theory.limits.colimit.is_colimit
string.map_tokens
pos_num.mul
snum.pred
tactic.local_cache.internal.def_local.hash_string
erased.out
sum.map
tactic.change_core
equiv.inhabited_of_equiv
is_add_group_hom.to_linear_map
normed_ring
pgame.add_lt_add
const.bitraverse
linarith.guard_is_nat_prop
quotient_group.quotient_ker_equiv_range
set.kern_image
turing.TM1to1.tr_cfg
tactic.interactive.injections_and_clear
set.fintype_insert'
turing.TM2to1.tr_normal
omega.nat.form
tensor_product
units.map_equiv
order_iso.trans
measure_theory.outer_measure.trim
tactic.ring.ring_m.mk_app
with_top.zero_ne_top
convex_on_linorder
equiv.set.image_of_inj_on
principal_seg.trans_top
function.bicompr
nhds_eq_orderable
ideal.is_prime
measure_theory.simple_func.range
finmap.any
euclidean_domain.lcm
measure_theory.simple_func
eckmann_hilton.comm_group
tactic.add_coinductive_predicate.coind_pred.pred
old_conv.apply_lemmas
category_theory.adjunction.has_limit_of_comp_equivalence
auto.case_option
tactic.rewrite_all.cfg
pell.n_lt_xn
tactic.interactive.guard_class
filter.filter_product.of_seq_one
linear_map.map_finsupp_total
polynomial.of_subring
linarith.get_vars
pell.pell_zd_sub
category_theory.limits.pullback.snd
linarith.pelim_var
nat.to_pexpr
finsupp.erase
metric.cauchy_iff
left_add_coset
Cauchy.gen
tactic.chain_core
free_ring.subsingleton_equiv_free_comm_ring
tactic.add_coinductive_predicate.coind_pred.func_g
computation.bind.G
well_founded.sup
asymptotics.is_o
pell.xn_ge_a_pow
matrix.det
padic.complete'
tactic.mk_exists_lst
equiv.vector_equiv_array
category_theory.limits.limit.post
filter.ptendsto
znum.add
computation.mem_rec_on
ordering.compares.eq_gt
CommRing.colimits.colimit_cocone
emetric.mem_closure_iff'
with_zero.lift
tactic.rcases_patt.invert_many
fp.next_dn_pos
list.choose_x
category_theory.adjunction.functoriality_is_right_adjoint
ℓ_infty_ℝ
tactic.prove_eqv_target
submodule.annihilator
expr.flip_eq
CpltSepUniformSpace.to_UniformSpace
equiv.bool_prod_nat_equiv_nat
homeomorph.mul_left
turing.TM0.machine.map_step
equiv.subtype_subtype_equiv_subtype_inter
pell.xn_succ
is_field_hom
expr.traverse
nat.cases
classical.DLO
auto.mk_hinst_lemmas
tactic.ring2.horner_expr.to_string
category_theory.limits.cofork
tactic.tauto_state
category_theory.coyoneda
direct_sum.lset_to_set
auto.common_normalize_lemma_names
push_neg.whnf_reducible
tactic.interactive.convert_to_core
add_group.in_closure
tactic.match_assoc_pattern
real.pi
homeomorph.add_right
gt_iff_lt
linarith.get_var_list
auto_cases_at
linarith.linarith_monad.run
finset.prod_ite
polynomial.monomial
measurable_equiv.refl
tactic.closure.mk_closure
add_group.closure
finmap.disjoint
category_theory.nat_trans.unop
set.pointwise_mul_fintype
omega.prove_neg
pos_num.transfer
encodable.decode_sigma
direct_sum.of
tactic.rintro_parse
turing.reaches₁
num.cmp_to_nat
power_series.order_add_ge
rat.neg
free_comm_ring
category_theory.limits.is_limit.lift_cone_morphism
category_theory.nat_trans.op
tactic.ext
tactic.constr_to_prop
filter.tendsto_at_top_principal
pell.pell_zd_add
equiv.monoid
seq.cases_on
linarith.linarith_config
tactic.interactive.as_goal
Gromov_Hausdorff.candidates_b_dist
filter.gi_generate
ennreal.of_real_lt_iff_lt_to_real
exists_forall_ge_and
tactic.drop_pis
snum.bit
prime_multiset.of_pnat_list
category_theory.limits.cocone.extensions
tactic.interactive.match_prefix
polynomial.root_multiplicity
category_theory.limits.cones.functoriality
omega.trisect
omega.int.to_form_core
znum.bitm1
tactic.derive_field
tensor_product.relators
emetric.tendsto_nhds
measure_theory.l1.integral
linear_map
lower_bounds
ext_param
ctop.realizer.nhds_σ
equiv.int_equiv_nat
category_theory.eq_to_hom
omega.nat.nonneg_consts
multiset.sum
traversable.map_fold
omega.is_lia_form
computation.bind.F
list.func.length_neg
localization.le_order_embedding
semiquot.is_pure
tactic.mllist.enum
omega.elim_var
finsupp.lsum
conv.slice_lhs
padic.exi_rat_seq_conv
tree.map
equiv.perm.support
tactic.mllist.map
turing.reaches
decidable.lt_by_cases
fpow
category_theory.comma.snd
add_monoid_hom.neg
free_ring_pempty_equiv_int
has_edist
expr.mfoldl
tactic.interactive.check_ac
tactic.local_cache.internal.cache_scope
tactic.interactive.erase_simp_arg
old_conv.apply_propext_simp_set
partrec
tactic.ring.normalize
num.of_znum'
list.erasep
equiv.sigma_prod_distrib
metric.exists_delta_of_continuous
fin_zero_elim'
set.bUnion_eq_sigma_of_disjoint
finset.min'
mv_polynomial.R
topological_space.seq_tendsto_iff
tactic.extract_def
old_conv.conversion
pell.yn_zero
category_theory.limits.pushout_cocone.inr
omega.int.form.induce
is_subfield
quotient_group.lift
omega.int.univ_close
real.cos
left_add_coset_equiv
turing.TM2to1.stackel.get
equiv.arrow_arrow_equiv_prod_arrow
pell.is_pell_one
complex.exp
multiset.length_ndinsert_of_mem
old_conv.to_tactic
filter.Liminf
is_comm_applicative
with_top.coe_eq_zero
category_theory.limits.has_colimits_of_shape_of_equivalence
equiv.traversable
seq.mem
rat.mul
ordinal.principal_seg_out
equiv.units_equiv_ne_zero
tactic.mk_local_pisn
emetric.cauchy_seq_iff
mul_mono_nonpos
tactic.tidy.default_tactics
tactic.abel.cache.mk_term
expr.get_app_fn_args_aux
num.to_znum_neg
localized_cmd
norm_num.prove_pos
pell.eq_of_xn_modeq_lem2
pell.pell_val
multiset.pi.cons
principal_seg.lt_equiv
category_theory.equivalence.unit_inv
homeomorph.prod_comm
where.get_def_variables
category_theory.equivalence.unit
tactic.interactive.unify_with_instance
old_conv.orelse
ctop.to_realizer
list.mpartition
list.func.equiv
tactic.ext_parse
Gromov_Hausdorff.aux_gluing_struct
linarith.is_numeric
omega.nat.prove_univ_close
auto.preprocess_goal
finset.max'
semiquot.lift_on
tactic.ring.eval_const_mul
omega.int.nnf
equiv.has_mul
metric.uniformity_dist
tactic.mllist.enum_from
tactic.mllist.force
semiquot.to_trunc
computation.terminates_rec_on
tactic.abel.normalize
measurable_equiv.sum_prod_sum
polynomial.pow_sub_pow_factor
units.mul
prime_multiset.prod
ge.is_linear_order
tactic.mk_mvar_list
tactic.ring2.horner_expr.mul
tactic.assumption_symm
tactic.interactive.delete_expr
finsupp.congr
linarith.get_rel_sides
homeomorph.trans
tactic.interactive.monotoncity.check_rel
ideal.radical
turing.TM2to1.stackel.is_bottom
complex.of_real
equiv.add_monoid
where.collect_implicit_names
linarith.ineq_const_nm
turing.TM2.stmts₁
category_theory.limits.has_finite_colimits
vector3.rec_on
list.scanr_aux
category_theory.functor.left_unitor
pos_num.pred
is_totally_separated
equiv.prod_punit
pell.x_pos
with_top.has_one
tactic.mk_user_fresh_name
list.func.set
direct_sum.lid
tactic.rcases_patt
tactic.abel.add_g
continuous_linear_map.bounds_bdd_below
ctop.realizer.of_equiv
free_abelian_group.lift
old_conv.apply_lemmas_core
bifunctor.fst
polynomial.coeff_coe_to_fun
category_theory.evaluation
complex.cosh
omega.clauses.unsat
tactic.to_texpr
semiquot.map
list.sublists_aux₁
omega.nat.form.sub_free
eq_of_forall_dist_le
irreducible_component
tactic.explode.head'
associates.unique'
linarith.pcomp.add
can_lift_attr
pell.xz_succ
tactic.interactive.parse_ac_mono_function'
relator.right_total
CommRing.colimits.colimit_type
num.succ
alist.disjoint
rat.le
complex.cau_seq_im
ring_invo.id
ideal.closure
category_theory.adjunction.functoriality_left_adjoint
finset.preimage
simple_group
function.embedding.of_surjective
tactic.rewrite_all.tracked_rewrite.replace_target_lhs
turing.TM1to1.supports_stmt_move
sylow.vectors_prod_eq_one
category_theory.is_right_adjoint
real.sqrt_two_add_series_nonneg
Top.limit
traversable.free.mk
tactic.assoc_rewrite_intl
tactic.instance_cache.mk_app
tactic.alias.alias_attr
category_theory.functor.as_equivalence
old_conv.apply_propext_lemmas
lattice.Inf_eq_bot
category_theory.limits.types.types_colimit_pre
complex.cau_seq_conj
polynomial.div
equiv.punit_prod
to_additive.parser
AddGroup.of
equiv.perm.sign_aux
tactic.op_induction'
primcodable.of_equiv
padic.rat_dense
category_theory.limits.walking_parallel_pair_hom.comp
complex
Top.colimit_is_colimit
category_theory.equivalence.trans
tactic.generalize_proofs
category_theory.limits.cones.postcompose_comp
cau_seq.of_eq
tactic.closure.is_eqv
list.pairwise_gt_iota
uniform_space.of_core
ordinal.limit_rec_on
znum.pred
magma.free_semigroup.lift
equiv.bool_prod_equiv_sum
category_theory.limits.cocone.whisker
tactic.rcases_patt.name
perfect_closure.of
category_theory.mono
tactic.interactive.higher_order_derive_handler
category_theory.limits.colimit.post
category_theory.discrete.lift
pell.yz_succ
local_of_unit_or_unit_one_sub
cast_znum
category_theory.iso.refl
finite_dimensional.findim
auto.case_some_hyp
fp.of_rat_up
snum.bit0
rel.codom
set.pointwise_mul_monoid
fp.float.add
category_theory.limits.pushout_cocone.mk
card_subgroup_dvd_card
AddCommGroup.of
turing.TM1to1.writes
submodule.colon
measure_theory.ae_eq_fun.add
setoid.is_partition
eq_of_le_of_forall_ge_of_dense
turing.TM2to1.st_write
tactic.impl_graph.mk_scc
bounded_continuous_function.arzela_ascoli₂
omega.nat.preterm.induce
associates
tactic.mllist.head
category_theory.limits.has_finite_limits
normal_of_eq_cosets
category_theory.limits.cone.of_fork
measurable_space.dynkin_system.generate
turing.TM1to1.step_aux_write
denumerable.raise
algebraic_geometry.PresheafedSpace.stalk
tactic.mllist.empty
category_theory.induced_category
tactic.add_coinductive_predicate.coind_pred.f₁_l
swap_right
polynomial.splits
cont
archimedean
expr.flip_iff
pell.d_pos
tactic.assoc_refl
filter.liminf_eq_supr_infi_of_nat
tactic.interactive.pi_head
is_linear_map.mk'
lists.of'
category_theory.adjunction.functoriality_counit'
auto.whnf_reducible
order_iso.to_order_embedding
is_add_subgroup.left_coset_equiv_subgroup
ordinal.typein_iso
equiv.to_iso
flip.bitraverse
tactic.add_coinductive_predicate.coind_pred.mono
nat.modeq.chinese_remainder
pos_num.land
function.update
mul_action.to_perm
category_theory.induced_functor
where.trace_nl
pnat.xgcd_type.is_reduced'
equiv.add_comm_monoid
to_additive.value_type
measurable_equiv.set.univ
pmf.map
is_greatest
nat.choose
relator.lift_fun
linarith.guard_is_strict_int_prop
pell.pell_eq
list.of_fn
pell.eq_of_xn_modeq'
bilin_form.bilin_linear_map_equiv
quotient_group.preimage_mk_equiv_subgroup_times_set
list.func.sub
category_theory.monad.forget_creates_limits.γ
semiquot.bind
num.mod
tactic.rcases_patt_inverted.format_list
category_theory.over.forget_colimit_is_colimit
monad_cont.label
complex.cpow
monoid.in_closure
hyperreal.lt_neg_of_pos_of_infinitesimal
tactic.mk_iff
lazy_list.traverse
cont_t.with_cont_t
turing.TM1to1.tr_tape_drop_right
tactic.simp_lemmas_from_file
principal_seg.top_lt_top
tactic.interactive.apply_iff_congr_core
normalize
turing.TM0.cfg.map
filter.infi_neq_bot_iff_of_directed
padic.rat_dense'
real.le
linarith.elim_all_vars
category_theory.equivalence.counit
category_theory.limits.cocones.precompose_equivalence
znum.succ
measurable_equiv.sum_congr
to_additive.guess_name
equiv.set.empty
add_monoid.closure
tactic.rcases_patt.merge
gaussian_int.to_complex
metric.tendsto_nhds
old_conv.change
category_theory.under.post
tactic.elide.replace
free_abelian_group.lift.universal
wseq.bisim_o
push_neg.normalize_negations
turing.frespects
nat.subtype.of_nat
real.sqrt_aux
tactic.local_binding_info
measure_theory.simple_func.integral_map
to_additive.proceed_fields
equiv.prod_congr
measure_theory.ae_eq_fun.comp₂
nzsnum.tail
tactic.fin_cases_at_aux
real.sqrt_two_add_series_zero_nonneg
metric_space.induced
tactic.pis
old_conv.istep
list.func.neg
filter.monad
emetric.mem_nhds_iff
measurable_equiv.cast
category_theory.limits.has_finite_products
localized_attr
semiquot.get
int.even
pnat.prime
linarith.add_neg_eq_pfs
tactic.elim_gen_sum
equiv.perm.subtype_perm
differentiable_within_at
old_conv_result
pmf.pure
set.pairwise_disjoint
uniform_space.completion.extension₂
tactic.abstract_if_success
category_theory.limits.fork.of_cone
tactic.interactive.ring.mode
premetric_space
prod.bitraverse
omega.clause
cast_num
pell.x_sub_y_dvd_pow_lem
category_theory.limits.colimit.desc
set.fintype_bUnion
prod.lex.decidable
omega.nat.form.unsat
Top.presheaf.stalk_pushforward
perfect_closure.UMP
pos_num.sub
category_theory.limits.terminal.from
tactic.transport_with_prefix_fun
linarith.pcomp.scale
bdd_above
old_conv.dsimp
opt_minus
tactic.ring2.horner_expr.inv
ge.is_partial_order
tactic.symmetry_hyp
real.log
list.fin_range
monoid.foldr.get
separated
lean.parser.emit_command_here
ideal.is_principal.generator
rel.image
lists
not.elim
multiplicity.finite
equiv.arrow_prod_equiv_prod_arrow
omega.find_min_coeff_core
filter.mem_at_top_sets
list.transpose_aux
tactic.replace
list.comp_traverse
turing.TM2.step
dfinsupp.to_has_scalar
nonunits
equiv.add_left
pell.is_pell_mul
ring_hom.to_monoid_hom
tactic.abel.normal_expr.to_list
filter.liminf_le_liminf
completion
subrel.order_embedding
is_cau_of_mono_bounded
topological_space.opens.interior
category_theory.discrete.opposite
succeeds
filter.rcomap
gt_of_mul_lt_mul_neg_right
zorn.succ_chain
metric.to_glue_l
equiv.set.union'
category_theory.monad
nat.partrec.code.const
quotient_group.inhabited
equiv.has_add
upper_bounds
measure_theory.measure'
tensor_product.comm
CommRing.colimits.relation
pell.dvd_of_ysq_dvd
category_theory.limits.limit.π
category_theory.limits.limit.cone_morphism
encodable.decode2
onote.power_aux
associates.mk
equiv.subtype_equiv_of_subtype'
cau_seq.le_of_exists
tactic.ring.eval_pow
topological_vector_space
restate_axiom_cmd
pos_num.divmod
omega.term.add
finset.strong_induction_on
real.tan
multiset.to_finsupp
num.transfer_rw
decidable_zero_symm
old_conv.first
complex.conj
relation.comp
vector.insert_nth
category_theory.limits.pushout_cocone.inl
tactic.symm_apply
tactic.add_coinductive_predicate
turing.TM2to1.st_run
old_conv.findp
fin_two_equiv
lin_equiv_matrix
category_theory.limits.pushout.desc
applicative_transformation
auto.add_conjuncts
category_theory.adjunction.id
category_theory.under.limit
lattice.fixed_points.next
tactic.explode.append_dep
is_subgroup.group_equiv_quotient_times_subgroup
tactic.ring.horner_expr.to_string
direct_sum.lof
sylow.rotate_vectors_prod_eq_one
matrix.sub_up_left
tactic.abel.eval_atom
function.injective.decidable_eq
erased.out_type
locally_finite.realizer
tactic.abel.normal_expr.refl_conv
equiv.sigma_equiv_prod
tactic.local_cache.internal.def_local.mk_dead_name
tactic.add_coinductive_predicate.coind_pred.func
old_conv.trace
turing.TM1to1.supports_stmt_write
measure_theory.outer_measure.sum
metric.mem_uniformity_dist
old_conv.execute
ge.is_trans
category_theory.whisker_right
tactic.replacer
category_theory.limits.limit.pre
norm_num.prove_lt
conv.slice
omega.nat.prove_neg_free
tactic.closure.root'
measure_theory.dominated_convergence_nn
onote.oadd_lt_oadd_2
open_subgroup.prod
matrix.mul
tactic.impl_graph.dfs_at
quotient_group.mk
AddGroup
metric.sum.dist
old_conv.repeat
pequiv.of_set
where.sort_variable_list
equiv.set.insert
finmap.sdiff
metric.continuous_iff
linear_map.sum_apply
is_add_subgroup.add_normalizer
equiv.prod_empty
category_theory.monadic_creates_limits
category_theory.limits.pullback.lift
turing.TM2to1.tr_st_act
category_theory.monad.forget
tactic.rcases_patt.format
AddCommGroup
equiv.set.union_sum_inter
cau_seq.cauchy
linarith.ineq
zsqrtd.lt
zmod.units_equiv_coprime
auto.eelims
category_theory.limits.cone_of_cocone_left_op
category_theory.adjunction.functoriality_is_left_adjoint
string.ltb
nat.partrec.code.encode_code
filter.filter_product.of_seq_zero
linear_map.flip
snum.not
equiv.neg
category_theory.functor.right_op
bicompl.bitraverse
turing.TM2.init
tactic.add_coinductive_predicate.coind_pred.destruct
omega.int.preterm.val
free_ring.to_free_comm_ring
tactic.mk_higher_order_type
localization.equiv_of_equiv
to_additive.tokens_dict
tactic.local_cache.internal.def_local.try_get_name
unique
ennreal.Icc_mem_nhds
metric.diam_closed_ball
padic_seq
linarith.add_exprs_aux
category_theory.monad.free
category_theory.limits.colimit.hom_iso'
denumerable.lower
omega.coeffs.val_except
gaussian_int
equiv.perm.of_subtype
linarith.to_comp_fold
old_conv.apply'
category_theory.adjunction.core_hom_equiv
category_theory.Kleisli.mk
associates.factor_set
tactic.explode.entries.size
multiset.choose_x
normed_group.of_core
tactic.abel.cache.mk_app
category_theory.limits.lim_yoneda
list.nodupkeys
omega.nat.to_form_core
free_magma.length
category_theory.limits.is_colimit.hom_iso'
sum.elim
category_theory.functor.inv_fun_id
complex.exp'
omega.nat.preterm.add_one
category_theory.functor.unop
category_theory.limits.preserves_colimits_of_shape
omega.ee_commit
set.pointwise_neg
category_theory.limits.pullback_cone.of_cone
category_theory.limits.reflects_limit
category_theory.limits.pushout.inr
snum.add
tensor_product.direct_sum
ideal
nat.xgcd_aux
gmultiples
ring_anti_equiv.refl
omega.int.to_preterm
bounded_continuous_function.dist_eq
category_theory.iso_whisker_right
pequiv.trans
trunc.rec
continuous_linear_map.bound
algebraic_geometry.PresheafedSpace.stalk_map
tactic.interactive.tfae_have
category_theory.limits.has_limit_of_equivalence_comp
gt.is_trans
category_theory.yoneda_sections_small
tactic.ring.horner_expr.refl_conv
measure_theory.measure.is_complete
tactic.rcases_hint
linarith.elab_arg_list
old_conv.failed
order_iso.prod_lex_congr
tactic.interactive.guard_tags
linarith.replace_nat_pfs
tactic.interactive.assert_or_rule
where.mk_flag
finsupp.split_comp
omega.nat.to_preterm
norm_num.eval_ineq
emetric.tendsto_at_top
measure_theory.simple_func.pair
monoid.mfoldr.mk
category_theory.limits.pushout_cocone.of_cocone
finset.powerset_len
equiv.ring
traversable.mfoldl.unop_of_free_monoid
omega.nat.is_diff
category_theory.functor.fun_inv_id
is_lub
computable₂
where.strip_namespace
linarith.comp.is_contr
conv.repeat_with_results
category_theory.limits.cocones.precompose
unique_irreducible_factorization
where.trace_variables
matrix.minor
tactic.abel.smulg
tactic.try_intros
free_ring
pfun.fix_induction
equiv.has_zero
old_conv.skip
dfinsupp.zip_with
linarith.get_nat_comps
ge_from_le
writer_t.lift
computable
tactic.mk_or_lst
functor.map_equiv
omega.int.form.implies
tactic.interactive.loc.get_local_pp_names
turing.TM1to1.tr
tactic.add_coinductive_predicate.coind_pred.u_params
ge.is_antisymm
multiplicative
list.split_on_p_aux
category_theory.limits.pullback_cone.mk
Mon.colimits.colimit_is_colimit
category_theory.limits.types.limit
has_fderiv_at_filter
cardinal.ord.order_embedding
add_monoid.in_closure
pell.yn_add
matrix.sub_up_right
tactic.instance_cache.append_typeclasses
polynomial.nonzero_comm_ring.of_polynomial_ne
pnat.gcd_x
local_ring
direct_sum
normal_add_subgroup
emetric.totally_bounded_iff'
lebesgue_number_lemma_of_metric_sUnion
tactic.interactive.side_conditions
category_theory.has_hom.hom.unop
filter.ultrafilter
pell.yz
pos_num.test_bit
rat.repr
lists'.to_list
category_theory.limits.functor_category_colimit_cocone
pos_num.lxor
re_pred
equiv.has_one
free_semigroup.of
alg_hom.to_ring_hom
tactic.local_cache.internal.def_local.get_root_name
fp.float.neg
pnat.xgcd_type.qp
uniform_space.separation_quotient.lift
localization.fraction_ring.map
is_bounded_linear_map
fp.float.is_finite
emetric.uniform_continuous_iff
quotient_add_group.mk
algebraic_geometry.PresheafedSpace.comp
power_series.inv
pell.yn
tactic.interactive.hide_meta_vars'
add_equiv.to_equiv
pell.xn_modeq_x2n_sub
tactic.mk_comp
free_comm_ring.lift
turing.TM2to1.stackel.is_top
tactic.ring.horner
encodable.decode_sum
padic.lim_seq
normal_subgroup
linarith.rb_map.find_defeq
bisequence
nnreal.of_real
gt_mem_sets_of_Liminf_gt
old_conv.congr_arg
pos_num.div'
equiv.list_equiv_self_of_equiv_nat
mul_action.stabilizer
omega.nat.preterm.sub_subst
manifold_core.to_manifold
category_theory.sum.associator
binder_eq_elim.push
turing.TM2to1.st_act
is_cau_seq.cauchy₂
cau_seq.lim_zero
omega.int.form.sat
quadratic_reciprocity_aux.prod_range_div_two_erase_zero
multiset.powerset_aux'
tactic.local_cache.internal.save_data
measure_theory.limsup_lintegral_le
tactic.interactive.lawful_functor_derive_handler'
rat.num_denom_cases_on
submodule.subtype
omega.term.mul
category_theory.over.colimit
category_theory.curry
lattice.conditionally_complete_linear_order_bot
lists.mem
hyperreal.is_st_iff_abs_sub_lt_delta
linarith.mul_nonpos
lattice.infi_eq_bot
pos_num.size
CommRing.colimits.desc_fun_lift
num.mul
pell.eq_pell
quotient_add_group.map
set.range_factorization
pell.y_mul_dvd
local_ring.residue_field
tactic.mk_assoc_pattern'
where.trace_namespace
category_theory.equivalence.ess_surj_of_equivalence
partrec₂
num.div
omega.int.desugar
decidable_of_bool
turing.TM0.stmt.map
omega.int.to_form
tactic.tidy
holor_index.assoc_left
category_theory.limits.has_limit_of_iso
associated
old_conv.propext'
omega.add_ee
category_theory.single_obj.star
set.pointwise_add_add_semigroup
category_theory.under.forget
zorn.max_chain
auto.do_substs
metric.diam_le_of_forall_dist_le
quadratic_reciprocity_aux.card_range_p_mul_q_filter_not_coprime
tactic.rewrite_all.tracked_rewrite.replace_target_rhs
principal_seg.lt_le
manifold_core.local_homeomorph
to_additive.target_name
pnat.gcd
category_theory.adjunction.functoriality_counit
min_le_add_of_nonneg_left
dfinsupp.erase
old_conv.applyc
metric.mem_of_closed'
hyperreal.infinite_pos_iff_infinite_and_pos
enat
measurable_equiv.trans
topological_space.open_nhds.inclusion_map_iso
tactic.explode.status
measure_theory.outer_measure
tactic.interactive.filter_instances
tactic.explode.args
encodable.of_left_injection
omega.nat.form.holds
real.exp
tactic.interactive.find_lemma
pell.xn_add
with_one
measurable_space.gi_generate_from
metric.tendsto_at_top
field.direct_limit.discrete_field
omega.prove_unsat_ef
quotient_group.eq_class_eq_left_coset
metric.mem_uniformity_edist
ideal.is_coprime
num.gcd
old_conv.head_beta
forall_eq_elim
tactic.interactive.monotoncity.check
filter.ultrafilter.pure
metric.Hausdorff_dist_le_of_inf_dist
tactic.ring.add_atom
tactic.interactive.traversable_derive_handler
equiv.psum_equiv_sum
equiv.comm_monoid
tactic.elide.unelide
cau_seq.equiv_def₃
category_theory.limits.has_equalizers
lists.to_list
gpowers
ge.is_total
encodable.encode_list
free_semigroup.lift'
string_hash
old_conv.congr_rule
option.cases_on'
tactic.rcases_hint.process_constructors
lex
equiv.empty_of_not_nonempty
open_add_subgroup
category_theory.limits.coprod
category_theory.limits.cone.of_pullback_cone
direct_sum.mk
ring.closure
turing.TM2.eval
tactic.interactive.fold_assoc
linarith.mk_single_comp_zero_pf
category_theory.limits.cocones.functoriality
set.pointwise_zero
category_theory.over.hom_mk
pos_num.pred'
omega.nat.dnf_core
sum.bind
norm_num.prove_non_prime
string.over_list
pnat.xgcd
fintype.choose
wseq.cases_on
omega.nat.prove_unsat_sub_free
category_theory.monad.algebra.hom.comp
old_conv.interactive.trace_state
multiset.subsingleton_equiv
writer_t.ext
cau_seq.lim
tactic.root
emetric.cauchy_iff
auto.do_subst
linarith.comp_source
side
finset.subtype
ctop.realizer.nhds_F
pos_num.mod'
tactic.explode.core
vector.to_array
gsmul
real
category_theory.adjunction.mk_of_unit_counit
fp.float.div
cast_pos_num
omega.update_zero
seq.bisim_o
lean.parser.get_variables
tactic.abel.cache
category_theory.monoidal_functor.μ_iso
pell.xy_succ_succ
transfer.analyse_decls
Mon.colimits.desc_morphism
transfer.compute_transfer
Cauchy.extend
category_theory.functor.const
tactic.ring.eval_mul
pos_num.succ
bounded_continuous_function.dist_set_exists
category_theory.limits.is_colimit.desc_cocone_morphism
tactic.symm_eq
category_theory.limits.limit.hom_iso
comm_ring.anti_equiv_to_equiv
category_theory.limits.functor_category_is_limit_cone
encodable.choose
pequiv.symm
is_add_subgroup.trivial
num.ldiff
equiv.set.range
equiv.sum_empty
tactic.mllist.m_of_list
ring_hom.to_add_monoid_hom
option_t.call_cc
equiv.equiv_congr
measurable_space.mk_of_closure
finsupp.equiv_multiset
fin2.cases'
topological_space.opens.is_basis
pexpr.get_uninst_pis
category_theory.monad.algebra.hom
add_equiv.symm
opposite.op
sylow.fixed_points_mul_left_cosets_equiv_quotient
nonneg_ring.to_linear_nonneg_ring
perms_of_finset
turing.tape.write
gt.is_asymm
omega.is_lna_term
free_magma
linarith.pcomp
units.inv'
pell.pell_zd
norm_num.eval_pow
old_conv
quot.encodable_quotient
filter.ultrafilter.bind
abv_sum_le_sum_abv
ge.is_total_preorder
equiv.perm.sign_cycle
filter.pointwise_one
tactic.rintro_hint
equiv.punit_arrow_equiv
omega.elim_eqs
equiv.conj
equiv.nat_sum_nat_equiv_nat
hash_map.mk_as_list
tactic.interactive.mk_fun_app
module.of_core
tactic.local_cache.internal.def_local.hash_context
multiset.strong_induction_on
pempty.elim
category_theory.functor.star
computable_pred
linarith.mk_lt_zero_pf_aux
denumerable.of_equiv
pell.is_pell_pell_zd
real.rpow
with_zero.inv
exists_pow_eq_one
tactic.tidy_hole_cmd
function.embedding.subtype
encodable.choose_x
tactic.tidy.name_to_tactic
measurable_space.dynkin_system.restrict_on
seq.is_bisimulation
subalgebra
equiv_punit_of_unique
left_coset_equiv
finsupp.antidiagonal
equiv.psigma_equiv_sigma
tactic.instance_cache.get
le_nhds_of_Limsup_eq_Liminf
linarith.comp.scale
dense_or_discrete
tactic.interactive.format_names
tactic.interactive.arg.to_tactic_format
category_theory.limits.reflects_colimit
tactic.match_head
tactic.strip_prefix
nnreal.of_real_lt_iff_lt_coe
is_absolute_value.mem_uniformity
finsupp.uncurry
where.where_cmd
homemorph.to_measurable_equiv
associates.out
is_ring_anti_hom
linarith.parse_into_comp_and_expr
tactic.interactive.functor_derive_handler'
category_theory.limits.is_limit.iso_unique_cone_morphism
num.transfer
tactic.interactive.find_rule
tactic.add_coinductive_predicate.coind_rule
tensor_product.tmul
category_theory.limits.is_limit.of_iso_limit
denumerable.raise'_finset
preorder.lift
turing.TM0to1.tr_cfg
tactic.ring.normalize_mode
tactic.library_search_hole_cmd
add_equiv.refl
equiv.array_equiv_fin
uniform_continuous₂
equiv.perm.trunc_swap_factors
measurable_equiv.set.range
matrix.transpose
list.permutations_aux2
algebra.adjoin_singleton_eq_range
tactic.replace_at
bitraversable
equiv.functor
finset.sum
category_theory.adjunction.cones_iso
category_theory.core.inclusion
free_comm_ring.of
tactic.interactive.squeeze_simp
omega.nat.canonize
tactic.interactive.traversable_derive_handler'
metric.totally_bounded_iff
is_cau_series_of_abv_le_cau
fp.emax
denumerable.pair
functor.const.mk'
tactic.tidy.ext1_wrapper
power_series.inv.aux
quotient.fin_choice_aux
tactic.find_if_cond_at
tactic.interactive.ac_refine
linarith.replace_strict_int_pfs
category_theory.limits.colimit.cocone_morphism
perfect_closure.frobenius_equiv
finset.pi
totally_disconnected_space
reader_t.call_cc
tactic.interactive.monotonicity.attr
Mon.colimits.cocone_morphism
equiv.prod_comm
tactic.eval_expr'
is_lawful_monad_cont
tactic.interactive.record_lit
classical.inhabited_of_nonempty'
tactic.tautology
tactic.refl_conv
tactic.rewrite_all.congr.expr_lens.to_tactic_string
zsqrtd.le
zmod.to_module'
tactic.rcases.process_constructors
real.le_of_forall_epsilon_le
category_theory.equivalence.adjointify_η
homeomorph.add_left
turing.TM1to1.tr_normal
