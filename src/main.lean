import action group_theory.quotient_group

open quotient_group mul_action

section

parameter {α : Type}
parameters (H : set (free_group α)) [is_subgroup H]
def Q := quotient H
def r : Q := mk 1

lemma r_mk_one : r = mk 1 := rfl

instance mul_act : mul_action (free_group α) Q := mul_action.mul_action H

lemma mul_mk (g g') : g • (mk g' : Q) = mk (g * g') := rfl

lemma smul_r (g : free_group α) : g • r = mk g
  := by rw [r_mk_one, mul_mk, mul_one]

lemma trans_act : orbit (free_group α) r = set.univ
  := set.ext $ λ q, (quot.ind $ λ a, (iff_true _).mpr (⟨a, smul_r a⟩)) q

lemma mk_eq_iff (g g') : (mk g : Q) = mk g' ↔ g⁻¹ * g' ∈ H
  := quotient_group.eq

lemma h_is_stab : H = stabilizer _ r := set.ext $ λ x, begin
  simp,
  rw [smul_r, r_mk_one, mk_eq_iff, mul_one],
  symmetry,
  exact is_subgroup.inv_mem_iff H,
end

def h_isom : H ≃* stabilizer (free_group α) r
  := ⟨λ ⟨x, h⟩, ⟨x, h_is_stab ▸ h⟩,
  λ ⟨x, h⟩, ⟨x, h_is_stab.symm ▸ h⟩,
  λ ⟨_, _⟩, rfl, λ ⟨_, _⟩, rfl, λ ⟨_, _⟩ ⟨_, _⟩, rfl⟩

theorem nielsen_schreier : ∃ (R : Type), nonempty (H ≃* free_group R) ∧ nonempty (Q × α ⊕ unit ≃ Q ⊕ R)
  := ⟨R Q r trans_act, ⟨mul_equiv.trans h_isom $ isom _ _ _⟩, ⟨index_equiv _ _ _⟩⟩

end