/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import tactic.norm_cast
import data.int.basic

/-!
# A tactic to shift `ℕ` goals to `ℤ`

It is often easier to work in `ℤ`, where subtraction is well behaved, than in `ℕ` where it isn't.
`zify` is a tactic that casts goals and hypotheses about natural numbers to ones about integers.
It makes use of `push_cast`, part of the `norm_cast` family, to simplify these goals.

## Implementation notes

`zify` is extensible.
TODO
-/

open tactic

namespace zify

mk_simp_attribute zify ""
/- @[user_attribute]
meta def zify_attr : user_attribute unit unit :=
{ name := `zify,
  descr := ""/- ,
  after_set := some $ λ n _ _, do
    d ← get_decl n,
    guard (d.type = `(expr → tactic  (expr × expr)))
      <|> fail "zify patterns must have type `expr → tactic (expr × expr)`" -/ } -/
/-
/-- Returns a list of all `zify` patterns in the context. -/
meta def get_patterns : tactic (list (expr → tactic  (expr × expr))) :=
attribute.get_instances `zify >>= mmap (λ t, mk_const t >>= eval_expr (expr → tactic (expr × expr)))

private meta def mk_app_tuple (lem : name) (lhs rhs : expr) (pe : pexpr) : tactic (expr × expr) :=
do type ← to_expr pe,
   eq_pf ← mk_app lem [lhs, rhs],
   return (type, eq_pf)

/-- A `zify` pattern for equalities and inequalities. -/
@[zify]
meta def comparison : expr → tactic (expr × expr)
| `(@has_le.le ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_le_coe_nat_iff lhs rhs ``((%%lhs : ℤ) ≤ %%rhs)
| `(@has_lt.lt ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_lt_coe_nat_iff lhs rhs ``((%%lhs : ℤ) < %%rhs)
| `(@ge ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_le_coe_nat_iff rhs lhs ``((%%lhs : ℤ) ≥ %%rhs)
| `(@gt ℕ %%_ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_lt_coe_nat_iff rhs lhs ``((%%lhs : ℤ) > %%rhs)
| `(@eq ℕ %%lhs %%rhs) := mk_app_tuple ``int.coe_nat_eq_coe_nat_iff lhs rhs ``((%%lhs : ℤ) = %%rhs)
| _ := failed -/

meta def lift_to_z (e : expr) : tactic (expr × expr) :=
do ns ← attribute.get_instances `zify >>= mmap (λ n, do c ← mk_const n, return (c, tt)),
   sl ← simp_lemmas.mk.append_with_symm ns,
   simplify sl [] e


attribute [zify] int.coe_nat_le_coe_nat_iff int.coe_nat_lt_coe_nat_iff int.coe_nat_eq_coe_nat_iff


end zify

/--
Given `e` a proposition about natural numbers,
`zify e` tries to translate it to a proposition `e'` about integers.
Returns `e'` and a proof that `e = e'`. -/
meta def tactic.zify1 (e : expr) : tactic (expr × expr) :=
do --zify_patterns ← zify.get_patterns,
  --  trace "1",
  --  (zv, iff_pf) ← zify.lift_to_z e <|> fail "failed to lift to ℤ", --zify_patterns.mfirst (λ f, f e),
  --  trace zv,
   (s, _) ← mk_simp_set tt [`push_cast] [],
  --  (newe, cast_eq) ← simplify (s.erase [`int.coe_nat_succ]) [] e {fail_if_unchanged := ff},
  --  --pex_pf ← mk_app `propext [iff_pf] >>= mk_eq_symm,
  --  prod.mk newe <$> mk_eq_trans pex_pf cast_eq
  simplify (s.erase [`int.coe_nat_succ]) [] e {fail_if_unchanged := ff}

meta def tactic.zify : expr → tactic (expr × expr) := λ z,
do ((), z1, p1) ← simplify_bottom_up () (λ _ e, prod.mk () <$> zify.lift_to_z e) z,
trace "1", trace z1,
   ((), z2, p2) ← simplify_bottom_up () (λ _ e, prod.mk () <$> tactic.zify1 e) z1 {fail_if_unchanged := ff},
   trace "2",
   prod.mk z2 <$> mk_eq_trans p1 p2

/--
Given `h` a proof of a proposition about natural numbers,
`zify_proof h` tries to translate it to a proof of a proposition about integers.
-/
meta def tactic.zify_proof (h : expr) : tactic expr :=
do (_, pf) ← infer_type h >>= tactic.zify,
   mk_eq_mp pf h

section

setup_tactic_parser

meta def tactic.interactive.zify (l : parse location) : tactic unit :=
do locs ← l.get_locals,
replace_at tactic.zify locs l.include_goal >>= guardb

end
example (a b c x y z : ℕ) (h : ¬ x*y*z < 0) : a + 3*b < c :=
begin
  simp only with zify,
  zify at h ⊢,
  guard_hyp h := ¬↑x * ↑y * ↑z < (0 : ℤ),
  guard_target (↑a : ℤ) + 3 * ↑b > ↑c,
  admit
end

example (a b : ℕ) : a ≤ b :=
begin
  zify,
  guard_target (a : ℤ) ≤ b,
  admit
end
