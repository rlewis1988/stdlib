import analysis.calculus.deriv analysis.complex.exponential data.nat.parity .sl2z topology.basic

noncomputable theory


def complex.half_plane : set ℂ := {z : ℂ | 0 < z.im}

notation `ℍ` := complex.half_plane

@[simp] lemma complex.half_plane_def {z : ℂ} : z ∈ ℍ ↔ 0 < z.im :=
by simp [complex.half_plane]

lemma half_plane_open : is_open ℍ :=
sorry

open complex

def holomorphic_at_on (f : ℂ → ℂ) (u : set ℂ) (z : ℂ) : Prop :=
∃ v ⊆ u, is_open v ∧ z ∈ v ∧ differentiable_on ℂ f v

def csmul : has_scalar ℂ (ℂ → ℂ) := pi.has_scalar
--set_option trace.class_instances true
def csmulact : mul_action ℂ ℂ := by apply_instance
--def csmulact : mul_action ℂ (ℂ → ℂ) := by try_for 2000 {exact  pi.mul_action _}
local attribute [instance, priority 10000] csmul
local attribute [instance, priority 10000] csmulact

lemma smul_holomorphic_at_on (c : ℂ) {f : ℂ → ℂ} {u : set ℂ} {z : ℂ} :
  Π (h : holomorphic_at_on f u z), holomorphic_at_on (c•f) u z
| ⟨v, v_sub_u, open_v, z_mem_v, diffable⟩ := ⟨v, v_sub_u, open_v, z_mem_v, diffable.smul _⟩

lemma neg_holomorphic_at_on {f : ℂ → ℂ} {u : set ℂ} {z : ℂ} :
  Π (h : holomorphic_at_on f u z), holomorphic_at_on (-f) u z
| ⟨v, v_sub_u, open_v, z_mem_v, diffable⟩ := ⟨v, v_sub_u, open_v, z_mem_v, diffable.neg⟩

lemma add_holomorphic_at_on {f g : ℂ → ℂ} {u : set ℂ} {z : ℂ} :
  Π (hf : holomorphic_at_on f u z) (hg : holomorphic_at_on g u z), holomorphic_at_on (f+g) u z
| ⟨x, x_sub_u, open_x, z_mem_x, f_diffable⟩ ⟨y, y_sub_u, open_y, z_mem_y, g_diffable⟩ :=
  ⟨x ∩ y, λ _ ⟨h1, _⟩, x_sub_u h1, is_open_inter open_x open_y, by simp [z_mem_x, z_mem_y],
    differentiable_on.add (f_diffable.mono (by simp)) (g_diffable.mono (by simp))⟩

def holomorphic_on (f : ℂ → ℂ) (u : set ℂ) : Prop :=
∀ z ∈ u, holomorphic_at_on f u z

lemma smul_holomorphic_on (c : ℂ) {f : ℂ → ℂ} {u : set ℂ} (h : holomorphic_on f u) :
  holomorphic_on (c•f) u :=
λ _, smul_holomorphic_at_on _ ∘ h _

lemma neg_holomorphic_on {f : ℂ → ℂ} {u : set ℂ} (h : holomorphic_on f u) :
  holomorphic_on (-f) u :=
λ _, neg_holomorphic_at_on ∘ h _

lemma add_holomorphic_on {f g : ℂ → ℂ} {u : set ℂ}
  (hf : holomorphic_on f u) (hg : holomorphic_on g u) : holomorphic_on (f+g) u :=
λ _ h, add_holomorphic_at_on (hf _ h) (hg _ h)

def isolated_from (z : ℂ) (u : set ℂ) : Prop :=
∃ u' : set ℂ, is_open u' ∧ z ∈ u' ∧ ∀ z' ∈ u, z' ≠ z → z' ∉ u'

def poles (f : ℂ → ℂ) (u : set ℂ) : set ℂ :=
{z | z ∈ u ∧ ¬ holomorphic_at_on f u z}

def meromorphic_on (f : ℂ → ℂ) (u : set ℂ) : Prop :=
∀ p ∈ poles f u, isolated_from p (poles f u)

structure modular_form (weight : ℕ) :=
(to_fun : ℂ → ℂ)
(to_fun_holo : holomorphic_on to_fun ℍ)
(comp_modular (m : SL2Z) (z : ℂ) : to_fun (m.to_fun z) = (z * m.c + m.d)^weight * to_fun z)
-- also holo at ∞I ?



--instance : module ℂ modular_form :=

lemma nat.odd_pow {α} [field α] {n : ℕ} (hn : ¬ n.even) : (-1 : α) ^ n = -1 :=
sorry

@[simp] lemma zero_iff_eq_neg_self {α} [discrete_field α] {a : α} : a = -a ↔ a = 0 :=
sorry
--⟨λ h, have h' : _ := add_eq_zero_iff_eq_neg.2 h, begin ring at h', rw mul_eq_zero_iff_eq_zero_or_eq_zero at h, end, _⟩

namespace modular_form
open SL2Z

def add {n} : modular_form n → modular_form n → modular_form n
| ⟨f, f_holo, f_comp⟩ ⟨g, g_holo, g_comp⟩ :=
  ⟨f+g, add_holomorphic_on f_holo g_holo, λ m z, by simp [f_comp m z, g_comp m z]; ring⟩

def smul {n} (c : ℂ) : modular_form n → modular_form n
| ⟨f, f_holo, f_comp⟩ := ⟨c•f, smul_holomorphic_on _ f_holo, λ m z, by simp [f_comp m z]; ring⟩

lemma smul_add {n} (c) : ∀ f g : modular_form n, smul c (add f g) = add (smul c f) (smul c g)
| ⟨f, _, _⟩ ⟨g, _, _⟩ := by simp only [_root_.smul_add,smul,add]

lemma one_smul {n} : ∀ f : modular_form n, smul 1 f = f
| ⟨f, _, _⟩ := by {simp [smul]}

lemma mul_smul {n} (r s : ℂ) : ∀ f : modular_form n, smul (r * s)  f = smul r (smul s f)
| ⟨f, _, _⟩ := by {simp [smul, _root_.mul_smul r s f] }

def neg {n} : modular_form n → modular_form n
| ⟨f, f_holo, f_comp⟩ := ⟨-f, neg_holomorphic_on f_holo, by simp [f_comp]⟩

def zero (n) : modular_form n :=
⟨λ _, 0, λ x hx, ⟨ℍ, λ _, id, half_plane_open, hx, differentiable_on_const _⟩, by simp⟩

instance (n) : add_comm_group (modular_form n) :=
{ add := add,
  add_assoc := by rintros ⟨⟩ ⟨⟩ ⟨⟩; simp [add],
  zero := zero n,
  zero_add := by rintros ⟨⟩; simp [add, zero]; refl,
  add_zero := by rintros ⟨⟩; dsimp [(+)]; simp [add, zero]; refl,
  neg := neg,
  add_left_neg := by rintros ⟨⟩; simp [add, neg]; refl,
  add_comm := by {rintros ⟨⟩ ⟨⟩, dsimp [(+)], simp [add]} }

instance (n) : module ℂ (modular_form n) :=
module.of_core $
{ smul := smul,
  smul_add := smul_add,
  add_smul := by rintros _ ⟨⟩ ⟨⟩; simp only [_root_.add_smul, smul, add]; refl,
  mul_smul := mul_smul,
  one_smul := one_smul }

@[simp] lemma to_fun_succ {n} (m : modular_form n) (z : ℂ) : m.to_fun (z + 1) = m.to_fun z :=
by convert m.comp_modular (of_tuple 1 1 0 1) z; simp [SL2Z.to_fun]

lemma to_fun_neg_inv {weight} (m : modular_form weight) (z : ℂ) :
  m.to_fun (-1/z) = z^weight * m.to_fun z :=
by convert m.comp_modular (of_tuple 0 (-1) 1 0) z; simp [SL2Z.to_fun]

lemma zero_of_odd_weight {weight} {m : modular_form weight} (h_weight : ¬ weight.even) (z : ℂ) :
  m.to_fun z = 0 :=
by simpa [nat.odd_pow h_weight, SL2Z.to_fun, div_neg]
     using m.comp_modular (of_tuple (-1) 0 0 (-1)) z

--def q (z : ℂ) : ℂ := exp (2*real.pi*I*z)

end modular_form
