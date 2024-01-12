import EuclideanGeometry.Foundation.Axiom.Basic.Angle

namespace EuclidGeom

theorem dir_eq_of_angvalue_eq {d₁ : Dir} {d₂ : Dir} : d₁ = d₂ ↔ d₁.toAngValue = d₂.toAngValue := sorry

theorem theta_sub_half_theta_eq_half_theta {θ : AngValue} : θ - (2⁻¹ * θ.toReal).toAngValue = (2⁻¹ * θ.toReal).toAngValue := sorry

theorem neg_half_pi_le_half_angvalue {θ : AngValue} : -π < 2⁻¹ * θ.toReal := by
  rcases le_or_gt 0 θ.toReal with h | h
  · have : -π < 0 := by norm_num; positivity
    apply lt_of_lt_of_le this
    positivity
  · apply lt_trans (AngValue.neg_pi_lt_toreal (θ := θ))
    field_simp
    linarith

theorem half_angvalue_le_half_pi {θ : AngValue} : 2⁻¹ * θ.toReal ≤ π := by
  rcases le_or_gt 0 θ.toReal with h | h
  · apply le_trans _ (AngValue.toreal_le_pi (θ := θ))
    field_simp
    exact h
  · apply le_of_lt
    have : 0 < π := by positivity
    apply lt_trans _ this
    field_simp
    linarith

theorem real_eq_toangvalue_toreal_real_iff_neg_pi_le_real_le_pi {θ : ℝ} : θ = θ.toAngValue.toReal ↔ (-π < θ) ∧ (θ ≤ π) := sorry

theorem half_angvalue_is_pos_if_angvalue_is_pos {α : AngValue} {β : AngValue} (g : α.toReal = 2⁻¹ * β.toReal) (h : β.IsPos) : α.IsPos := sorry

theorem half_angvalue_is_neg_if_angvalue_is_neg {α : AngValue} {β : AngValue} (g : α.toReal = 2⁻¹ * β.toReal) (h : β.IsNeg) : α.IsNeg := sorry

theorem toreal_eq_half_pi_of_eq_half_pi_toangvalue {θ : AngValue} (g : θ.toReal = 2⁻¹ * π) : θ = (2⁻¹ * π).toAngValue := sorry

end EuclidGeom
