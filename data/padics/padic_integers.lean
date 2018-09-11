/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

Define the p-adic integers ℤ_p as a subtype of ℚ_p. Construct algebraic structures on ℤ_p.
-/

import data.padics.padic_rationals tactic.subtype_instance ring_theory.ideals
open nat padic
noncomputable theory
local attribute [instance] classical.prop_decidable

def padic_int {p : ℕ} (hp : prime p) := {x : ℚ_[hp] // ∥x∥ ≤ 1}
notation `ℤ_[`hp`]` := padic_int hp

namespace padic_int 
variables {p : ℕ} {hp : prime p}

def add : ℤ_[hp] → ℤ_[hp] → ℤ_[hp]
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x+y, 
    le_trans (padic_norm_e.nonarchimedean _ _) (max_le_iff.2 ⟨hx,hy⟩)⟩

def mul : ℤ_[hp] → ℤ_[hp] → ℤ_[hp]
| ⟨x, hx⟩ ⟨y, hy⟩ := ⟨x*y, 
    begin rw padic_norm_e.mul, apply mul_le_one; {assumption <|> apply norm_nonneg} end⟩

def neg : ℤ_[hp] → ℤ_[hp]
| ⟨x, hx⟩ := ⟨-x, by simpa⟩

instance : ring ℤ_[hp] :=
begin 
  refine { add := add,
           mul := mul,
           neg := neg,
           zero := ⟨0, by simp [zero_le_one]⟩,
           one := ⟨1, by simp⟩,
           .. };
  {repeat {rintro ⟨_, _⟩}, simp [mul_assoc, left_distrib, right_distrib, add, mul, neg]}
end 

lemma zero_def : ∀ x : ℤ_[hp], x = 0 ↔ x.val = 0 
| ⟨x, _⟩ := ⟨subtype.mk.inj, λ h, by simp at h; simp only [h]; refl⟩

@[simp] lemma add_def : ∀ (x y : ℤ_[hp]), (x+y).val = x.val + y.val 
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mul_def : ∀ (x y : ℤ_[hp]), (x*y).val = x.val * y.val 
| ⟨x, hx⟩ ⟨y, hy⟩ := rfl

@[simp] lemma mk_zero {h} : (⟨0, h⟩ : ℤ_[hp]) = (0 : ℤ_[hp]) := rfl

instance : has_coe ℤ_[hp] ℚ_[hp] := ⟨subtype.val⟩

@[simp] lemma val_eq_coe (z : ℤ_[hp]) : z.val = ↑z := rfl

@[simp] lemma coe_add : ∀ (z1 z2 : ℤ_[hp]), (↑(z1 + z2) : ℚ_[hp]) = ↑z1 + ↑z2 
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma coe_mul : ∀ (z1 z2 : ℤ_[hp]), (↑(z1 * z2) : ℚ_[hp]) = ↑z1 * ↑z2 
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma coe_neg : ∀ (z1 : ℤ_[hp]), (↑(-z1) : ℚ_[hp]) = -↑z1
| ⟨_, _⟩ := rfl

@[simp] lemma coe_sub : ∀ (z1 z2 : ℤ_[hp]), (↑(z1 - z2) : ℚ_[hp]) = ↑z1 - ↑z2 
| ⟨_, _⟩ ⟨_, _⟩ := rfl

@[simp] lemma coe_coe : ∀ n : ℕ, (↑(↑n : ℤ_[hp]) : ℚ_[hp]) = (↑n : ℚ_[hp])
| 0 := rfl
| (k+1) := by simp [coe_coe]; refl

@[simp] lemma coe_one : (↑(1 : ℤ_[hp]) : ℚ_[hp]) = 1 := rfl 

lemma mk_coe : ∀ (k : ℤ_[hp]), (⟨↑k, k.2⟩ : ℤ_[hp]) = k
| ⟨_, _⟩ := rfl

def inv : ℤ_[hp] → ℤ_[hp]
| ⟨k, _⟩ := if h : ∥k∥ = 1 then ⟨1/k, by simp [h]⟩ else 0

end padic_int 

section instances
variables {p : ℕ} {hp : p.prime}

@[reducible] def padic_norm_z (z : ℤ_[hp]) : ℝ := ∥z.val∥

instance : metric_space ℤ_[hp] := 
subtype.metric_space
 
instance : has_norm ℤ_[hp] := ⟨padic_norm_z⟩ 

instance : normed_ring ℤ_[hp] :=
{ dist_eq := λ ⟨_, _⟩ ⟨_, _⟩, rfl,
  norm_mul := λ ⟨_, _⟩ ⟨_, _⟩, norm_mul _ _ }

instance padic_norm_z.is_absolute_value {p} {hp : prime p} : is_absolute_value (λ z : ℤ_[hp], ∥z∥) := 
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := λ ⟨_, _⟩, by simp [norm_eq_zero, padic_int.zero_def],
  abv_add := λ ⟨_,_⟩ ⟨_, _⟩, norm_triangle _ _,
  abv_mul := λ _ _, by unfold norm; simp [padic_norm_z] }

protected lemma padic_int.pmul_comm : ∀ z1 z2 : ℤ_[hp], z1*z2 = z2*z1 
| ⟨q1, h1⟩ ⟨q2, h2⟩ := show (⟨q1*q2, _⟩ : ℤ_[hp]) = ⟨q2*q1, _⟩, by simp [mul_comm]

instance : comm_ring ℤ_[hp] :=
{ mul_comm := padic_int.pmul_comm,
  ..padic_int.ring }

protected lemma padic_int.zero_ne_one : (0 : ℤ_[hp]) ≠ 1 := 
show (⟨(0 : ℚ_[hp]), _⟩ : ℤ_[hp]) ≠ ⟨(1 : ℚ_[hp]), _⟩, from mt subtype.ext.1 zero_ne_one

protected lemma padic_int.eq_zero_or_eq_zero_of_mul_eq_zero : 
          ∀ (a b : ℤ_[hp]), a * b = 0 → a = 0 ∨ b = 0
| ⟨a, ha⟩ ⟨b, hb⟩ := λ h : (⟨a * b, _⟩ : ℤ_[hp]) = ⟨0, _⟩, 
have a * b = 0, from subtype.ext.1 h,
(mul_eq_zero_iff_eq_zero_or_eq_zero.1 this).elim
  (λ h1, or.inl (by simp [h1]; refl))
  (λ h2, or.inr (by simp [h2]; refl)) 

instance {p : ℕ} {hp : prime p} : integral_domain ℤ_[hp] :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := padic_int.eq_zero_or_eq_zero_of_mul_eq_zero,
  zero_ne_one := padic_int.zero_ne_one,
  ..padic_int.comm_ring }

end instances

namespace padic_norm_z

variables {p : ℕ} {hp : p.prime}

lemma le_one : ∀ z : ℤ_[hp], ∥z∥ ≤ 1 
| ⟨_, h⟩ := h

@[simp] lemma mul (z1 z2 : ℤ_[hp]) : ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ :=
by unfold norm; simp [padic_norm_z]

theorem nonarchimedean : ∀ (q r : ℤ_[hp]), ∥q + r∥ ≤ max (∥q∥) (∥r∥)
| ⟨_, _⟩ ⟨_, _⟩ := padic_norm_e.nonarchimedean _ _

@[simp] lemma norm_one : ∥(1 : ℤ_[hp])∥ = 1 := norm_one 

end padic_norm_z 

namespace padic_int 
variables {p : ℕ} {hp : p.prime}
local attribute [reducible] padic_int 

lemma mul_inv : ∀ {z : ℤ_[hp]}, ∥z∥ = 1 → z * z.inv = 1 
| ⟨k, _⟩ h := 
  begin
    have hk : k ≠ 0, from λ h', @zero_ne_one ℚ_[hp] _ (by simpa [h'] using h),
    unfold padic_int.inv, split_ifs, 
    { change (⟨k * (1/k), _⟩ : ℤ_[hp]) = 1,
      simp [hk], refl },
    { apply subtype.ext.2, simp [mul_inv_cancel hk] }
  end 

lemma inv_mul {z : ℤ_[hp]} (hz : ∥z∥ = 1) : z.inv * z = 1 := 
by rw [mul_comm, mul_inv hz]

def maximal_ideal {p : ℕ} (hp : prime p) : set ℤ_[hp] := λ z, ∥z∥ < 1

lemma maximal_ideal_add {z1 z2 : ℤ_[hp]} (hz1 : ∥z1∥ < 1) (hz2 : ∥z2∥ < 1) : ∥z1 + z2∥ < 1 := 
lt_of_le_of_lt (padic_norm_z.nonarchimedean _ _) (max_lt hz1 hz2)

private lemma mul_lt_one  {α} [decidable_linear_ordered_comm_ring α] {a b : α} (hbz : 0 < b)
  (ha : a < 1) (hb : b < 1) : a * b < 1 :=
suffices a*b < 1*1, by simpa,
mul_lt_mul ha (le_of_lt hb) hbz zero_le_one

private lemma mul_lt_one_of_le_of_lt {α} [decidable_linear_ordered_comm_ring α] {a b : α} (ha : a ≤ 1) 
  (hbz : 0 ≤ b) (hb : b < 1) : a * b < 1 := 
if hb' : b = 0 then by simpa [hb'] using zero_lt_one 
else if ha' : a = 1 then by simpa [ha']
else mul_lt_one (lt_of_le_of_ne hbz (ne.symm hb')) (lt_of_le_of_ne ha ha') hb

lemma maximal_ideal_mul {z1 z2 : ℤ_[hp]} (hz2 : ∥z2∥ < 1) : ∥z1 * z2∥ < 1 := 
calc  ∥z1 * z2∥ = ∥z1∥ * ∥z2∥ : by simp 
           ... < 1 : mul_lt_one_of_le_of_lt (padic_norm_z.le_one _) (norm_nonneg _) hz2

instance : is_submodule (maximal_ideal hp) :=
{ zero_ := show ∥(0 : ℤ_[hp])∥ < 1, by simp [zero_lt_one],
  add_ := @maximal_ideal_add _ _,
  smul := @maximal_ideal_mul _ _ }

lemma maximal_ideal_ne_univ : maximal_ideal hp ≠ set.univ := 
mt set.eq_univ_iff_forall.mp 
  begin
    rw [not_forall],
    existsi (1 : ℤ_[hp]),
    change ¬ (_ < _),
    apply not_lt_of_ge,
    simp, apply le_refl 
  end  

lemma maximal_ideal_eq_nonunits : maximal_ideal hp = nonunits _ :=
begin 
  ext,
  constructor,
  { intros hx hex,
    cases hex with y hy,
    have hym : ∥(y*x)∥ < 1, from is_submodule.smul _ hx,
    apply lt_irrefl (1 : ℝ),
    rw hy at hym, simpa using hym },
  { intro hx,
    by_contradiction hnm,
    apply hx,
    have : ∥x∥ = 1, from le_antisymm (padic_norm_z.le_one _) (le_of_not_gt hnm),
    existsi x.inv, apply inv_mul this }
end  

instance : is_proper_ideal (maximal_ideal hp) :=
{ ne_univ := maximal_ideal_ne_univ }

lemma maximal_ideal_eq_or_univ_of_subset (T : set ℤ_[hp]) [_inst_2 : is_ideal T]
      (hss : maximal_ideal hp ⊆ T) : T = maximal_ideal hp ∨ T = set.univ :=
have T ≠ maximal_ideal hp → T = set.univ, from
  (assume h : T ≠ maximal_ideal hp,
   let ⟨k, hkt, hknm⟩ := set.exists_of_ssubset ⟨hss, ne.symm h⟩ in 
   set.eq_univ_of_forall $ λ z,
     have hknm : ∥k∥ = 1, from le_antisymm (padic_norm_z.le_one _) (le_of_not_gt hknm),
     have hkzt : z*k ∈ T, from is_submodule.smul _ hkt,
     have hkzt' : (inv k)*(z*k) ∈ T, from is_submodule.smul _ hkzt,
     by rw [mul_comm, mul_assoc, mul_inv] at hkzt'; simpa using hkzt'),
if hT : T = maximal_ideal hp then or.inl hT else or.inr (this hT) 

instance : is_maximal_ideal (maximal_ideal hp) := 
{ eq_or_univ_of_subset := maximal_ideal_eq_or_univ_of_subset }

lemma maximal_ideal_unique (T : set ℤ_[hp]) [_inst_2 : is_maximal_ideal T] : maximal_ideal hp = T :=
let htmax := @is_maximal_ideal.eq_or_univ_of_subset _ _ T _ (maximal_ideal hp) _ in 
have htsub : T ⊆ maximal_ideal hp, 
  by rw maximal_ideal_eq_nonunits; apply not_unit_of_mem_proper_ideal,
or.resolve_right (htmax htsub) maximal_ideal_ne_univ

instance : local_ring ℤ_[hp] :=
{ S := maximal_ideal hp,
  max := by apply_instance,
  unique := maximal_ideal_unique }

end padic_int