import data.matrix.basic linear_algebra.determinant analysis.calculus.deriv tactic.fin_cases

universe u

section
variables (n : ℕ) (K : Type u) [comm_ring K]
@[derive λ t, has_coe t (matrix (fin n) (fin n) K)]
def SL := {m : matrix (fin n) (fin n) K // m.det = 1}
end

namespace SL

variables {n : ℕ} {K : Type u} [comm_ring K]

@[extensionality] lemma ext {m1 m2 : SL n K} : m1 = m2 ↔ m1.val = m2.val :=
subtype.ext

lemma det_mul (m1 m2 : SL n K) : (m1.val * m2.val).det = 1 :=
by rw [matrix.det_mul, m1.property, m2.property, one_mul]

/- def inv : SL n K → SL n K := sorry

lemma inv_left_inv (m : SL n K) : (inv m).val * m.val = 1 := sorry -/

instance : monoid (SL n K) :=
{ mul := λ m1 m2, ⟨m1.val * m2.val, det_mul _ _⟩,
  mul_assoc := λ _ _ _, ext.2 $ semiring.mul_assoc _ _ _,
  one := ⟨1, matrix.det_one⟩,
  one_mul := λ _, ext.2 $ monoid.one_mul _,
  mul_one := λ _, ext.2 $ monoid.mul_one _ }

end SL

@[derive [monoid, λ t, has_coe t (matrix (fin 2) (fin 2) ℤ)]]
def SL2Z := SL 2 ℤ

namespace SL2Z

variable (m : SL2Z)
def a := m.val ⟨0, dec_trivial⟩ ⟨0, dec_trivial⟩
def b := m.val ⟨0, dec_trivial⟩ ⟨1, dec_trivial⟩
def c := m.val ⟨1, dec_trivial⟩ ⟨0, dec_trivial⟩
def d := m.val ⟨1, dec_trivial⟩ ⟨1, dec_trivial⟩

@[simp] lemma a_def {p q} : m.val ⟨0, p⟩ ⟨0, q⟩ = m.a := rfl
@[simp] lemma b_def {p q} : m.val ⟨0, p⟩ ⟨1, q⟩ = m.b := rfl
@[simp] lemma c_def {p q} : m.val ⟨1, p⟩ ⟨0, q⟩ = m.c := rfl
@[simp] lemma d_def {p q} : m.val ⟨1, p⟩ ⟨1, q⟩ = m.d := rfl

lemma det_reduce : m.val.det = (1*(m.a*(m.d*1))) + (((-1)*(m.c*(m.b*1))) + 0) :=
rfl

lemma det : m.val.det = m.a*m.d - m.c * m.b :=
by simpa using m.det_reduce

lemma det_eq_one : m.a * m.d - m.c * m.b = 1 :=
by rw [←det, m.property]

private def val_inv : matrix (fin 2) (fin 2) ℤ
| ⟨0, _⟩ ⟨0, _⟩ := m.d
| ⟨0, _⟩ ⟨1, _⟩ := -m.b
| ⟨1, _⟩ ⟨0, _⟩ := -m.c
| ⟨1, _⟩ ⟨1, _⟩ := m.a
| _ _ := 0

lemma val_inv_mul_left : val_inv m * m.val = 1 :=
begin
  ext i j, fin_cases i; fin_cases j; simp [matrix.mul_val]; show _ * _ +( _* _ + _) = _;
  simp [val_inv]; ring; convert det_eq_one m using 1; ring
end

lemma val_inv_det : (val_inv m).det = 1 :=
have h_det : (val_inv m * m.val).det = 1, by simp [val_inv_mul_left],
by rwa [matrix.det_mul, m.property, mul_one] at h_det

def inv : SL2Z := ⟨val_inv m, val_inv_det m⟩

instance : group SL2Z :=
{ inv := inv,
  mul_left_inv := λ _, subtype.ext.2 $ val_inv_mul_left _,
  ..SL2Z.monoid_1 }

section
variable {m}
lemma int.nat_abs_eq_one_of_mul_eq_one_left (z1 z2 : ℤ) (h : z1 * z2 = 1) : z1.nat_abs = 1 :=
sorry

lemma int.nat_abs_eq_one_of_mul_eq_one_right {z1 z2 : ℤ} (h : z1 * z2 = 1) : z2.nat_abs = 1 :=
sorry

lemma b_nat_abs_eq_one_of_a_zero (h : m.a = 0) : m.b.nat_abs = 1 :=
sorry

lemma b_nat_abs_eq_one_of_d_zero (h : m.d = 0) : m.b.nat_abs = 1 :=
sorry

lemma c_nat_abs_eq_one_of_a_zero (h : m.a = 0) : m.c.nat_abs = 1 :=
sorry

lemma c_nat_abs_eq_one_of_d_zero (h : m.d = 0) : m.c.nat_abs = 1 :=
sorry

lemma a_nat_abs_eq_one_of_b_zero (h : m.b = 0) : m.a.nat_abs = 1 :=
sorry

lemma a_nat_abs_eq_one_of_c_zero (h : m.c = 0) : m.a.nat_abs = 1 :=
sorry

lemma d_nat_abs_eq_one_of_b_zero (h : m.b = 0) : m.d.nat_abs = 1 :=
sorry

lemma d_nat_abs_eq_one_of_c_zero (h : m.c = 0) : m.d.nat_abs = 1 :=
sorry

lemma b_ne_zero_of_a_zero (h : m.a = 0) : m.b ≠ 0 :=
sorry

lemma b_ne_zero_of_d_zero (h : m.d = 0) : m.b ≠ 0 :=
sorry

lemma c_ne_zero_of_a_zero (h : m.a = 0) : m.c ≠ 0 :=
sorry

lemma c_ne_zero_of_d_zero (h : m.d = 0) : m.c ≠ 0 :=
sorry

lemma a_ne_zero_of_b_zero (h : m.b = 0) : m.a ≠ 0 :=
sorry

lemma a_ne_zero_of_c_zero (h : m.c = 0) : m.a ≠ 0 :=
sorry

lemma d_ne_zero_of_b_zero (h : m.b = 0) : m.d ≠ 0 :=
sorry

lemma d_ne_zero_of_c_zero (h : m.c = 0) : m.d ≠ 0 :=
sorry
end

noncomputable def to_fun : ℂ → ℂ :=
λ z, (z*m.a + m.b) / (z*m.c + m.d)

lemma complex.ne_of_im_ne_im {z1 z2 : ℂ} (h_ne : z1.im ≠ z2.im) : z1 ≠ z2 :=
λ h, h_ne $ by rw h

lemma to_fun_mem_halfplane {z : ℂ} (hz : 0 < z.im) : 0 < (m.to_fun z).im :=
begin
  rw [to_fun, complex.div_im, sub_pos, div_lt_div_right],
  { suffices : z.im * (↑(m.c) * ↑(m.b) + z.re * ↑(m.a)* ↑(m.c)) < z.im * (↑(m.a) *↑(m.d) + z.re * ↑(m.a) * ↑(m.c)),
    { convert this using 1; simp; ring },
    apply mul_lt_mul_of_pos_left (add_lt_add_right _ _) hz,
    norm_cast,
    linarith [m.det_eq_one] },
  { by_cases hmc : m.c = 0,
    { simp [hmc, d_ne_zero_of_c_zero hmc] },
    { rw complex.norm_sq_pos,
      apply complex.ne_of_im_ne_im,
      simp [hmc, ne_of_gt hz] } }
end

end SL2Z
