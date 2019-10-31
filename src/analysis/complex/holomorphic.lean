import analysis.calculus.deriv analysis.complex.exponential data.nat.parity

noncomputable theory

structure modular :=
(a b c d : ℤ)
(restr : a*d - b*c = 1)

lemma int.nat_abs_eq_one_of_mul_eq_one_left (z1 z2 : ℤ) (h : z1 * z2 = 1) : z1.nat_abs = 1 :=
sorry

lemma int.nat_abs_eq_one_of_mul_eq_one_right {z1 z2 : ℤ} (h : z1 * z2 = 1) : z2.nat_abs = 1 :=
sorry


lemma modular.ad_eq (m : modular) : m.a * m.d = m.b * m.c + 1 :=
eq.symm $ add_eq_of_eq_sub' $ eq.symm m.restr

lemma modular.b_nat_abs_eq_one_of_a_zero {m : modular} (h : m.a = 0) : m.b.nat_abs = 1 :=
sorry

lemma modular.b_nat_abs_eq_one_of_d_zero {m : modular} (h : m.d = 0) : m.b.nat_abs = 1 :=
sorry

lemma modular.c_nat_abs_eq_one_of_a_zero {m : modular} (h : m.a = 0) : m.c.nat_abs = 1 :=
sorry

lemma modular.c_nat_abs_eq_one_of_d_zero {m : modular} (h : m.d = 0) : m.c.nat_abs = 1 :=
sorry

lemma modular.a_nat_abs_eq_one_of_b_zero {m : modular} (h : m.b = 0) : m.a.nat_abs = 1 :=
sorry

lemma modular.a_nat_abs_eq_one_of_c_zero {m : modular} (h : m.c = 0) : m.a.nat_abs = 1 :=
sorry

lemma modular.d_nat_abs_eq_one_of_b_zero {m : modular} (h : m.b = 0) : m.d.nat_abs = 1 :=
sorry

lemma modular.d_nat_abs_eq_one_of_c_zero {m : modular} (h : m.c = 0) : m.d.nat_abs = 1 :=
sorry

lemma modular.b_ne_zero_of_a_zero {m : modular} (h : m.a = 0) : m.b ≠ 0 :=
sorry

lemma modular.b_ne_zero_of_d_zero {m : modular} (h : m.d = 0) : m.b ≠ 0 :=
sorry

lemma modular.c_ne_zero_of_a_zero {m : modular} (h : m.a = 0) : m.c ≠ 0 :=
sorry

lemma modular.c_ne_zero_of_d_zero {m : modular} (h : m.d = 0) : m.c ≠ 0 :=
sorry

lemma modular.a_ne_zero_of_b_zero {m : modular} (h : m.b = 0) : m.a ≠ 0 :=
sorry

lemma modular.a_ne_zero_of_c_zero {m : modular} (h : m.c = 0) : m.a ≠ 0 :=
sorry

lemma modular.d_ne_zero_of_b_zero {m : modular} (h : m.b = 0) : m.d ≠ 0 :=
sorry

lemma modular.d_ne_zero_of_c_zero {m : modular} (h : m.c = 0) : m.d ≠ 0 :=
sorry

def complex.half_plane : set ℂ := {z : ℂ | 0 < z.im}

notation `ℍ` := complex.half_plane

@[simp] lemma complex.half_plane_def {z : ℂ} : z ∈ ℍ ↔ 0 < z.im :=
by simp [complex.half_plane]

open complex

lemma complex.ne_of_im_ne_im {z1 z2 : ℂ} (h_ne : z1.im ≠ z2.im) : z1 ≠ z2 :=
λ h, h_ne $ by rw h

def modular.to_fun (m : modular) : ℂ → ℂ :=
λ z, (z*m.a + m.b) / (z*m.c + m.d)

lemma modular.to_fun_mem_halfplane (m : modular) {z : ℂ} (hz : z ∈ ℍ) : m.to_fun z ∈ ℍ :=
begin
  rw half_plane_def at hz ⊢,
  rw [modular.to_fun, complex.div_im, sub_pos, div_lt_div_right],
  { suffices : z.im * (↑(m.b)* ↑(m.c) + z.re * ↑(m.a)* ↑(m.c)) < z.im * (↑(m.a) *↑(m.d) + z.re * ↑(m.a) * ↑(m.c)),
    { convert this using 1; simp; ring },
    apply mul_lt_mul_of_pos_left (add_lt_add_right _ _) hz,
    norm_cast,
    linarith [m.ad_eq] },
  { by_cases hmc : m.c = 0,
    { simp [hmc, modular.d_ne_zero_of_c_zero hmc] },
    { rw norm_sq_pos,
      apply complex.ne_of_im_ne_im,
      simp [hmc, ne_of_gt hz] } }
end

def holomorphic_on (f : ℂ → ℂ) (u : set ℂ) : Prop :=
∀ z ∈ u, ∃ v ⊆ u, is_open v ∧ z ∈ v ∧ differentiable_on ℂ f v

structure modular_form :=
(to_fun : ℂ → ℂ)
(to_fun_holo : holomorphic_on to_fun ℍ)
(weight : ℕ)
(comp_modular (m : modular) (z : ℂ) : to_fun (m.to_fun z) = (z * m.c + m.d)^weight * to_fun z)
-- also holo at ∞I ?

lemma nat.odd_pow {α} [field α] {n : ℕ} (hn : ¬ n.even) : (-1 : α) ^ n = -1 :=
sorry

@[simp] lemma zero_iff_eq_neg_self {α} [discrete_field α] {a : α} : a = -a ↔ a = 0 :=
sorry
--⟨λ h, have h' : _ := add_eq_zero_iff_eq_neg.2 h, begin ring at h', rw mul_eq_zero_iff_eq_zero_or_eq_zero at h, end, _⟩

namespace modular_form

@[simp] lemma to_fun_succ (m : modular_form) (z : ℂ) : m.to_fun (z + 1) = m.to_fun z :=
by convert m.comp_modular ⟨1, 1, 0, 1, by norm_num⟩ z; simp [modular.to_fun]

lemma to_fun_neg_inv (m : modular_form) (z : ℂ) : m.to_fun (-1/z) = z^m.weight * m.to_fun z :=
by convert m.comp_modular ⟨0, -1, 1, 0, by norm_num⟩ z; simp [modular.to_fun]

lemma zero_of_odd_weight {m : modular_form} (h_weight : ¬ m.weight.even) (z : ℂ) : m.to_fun z = 0 :=
by simpa [nat.odd_pow h_weight, modular.to_fun, div_neg] using m.comp_modular ⟨-1, 0, 0, -1, by norm_num⟩ z

end modular_form
