import EuclideanGeometry.Foundation.Axiom.Linear.Ray_trash
import EuclideanGeometry.Foundation.Axiom.Position.Angle
import EuclideanGeometry.Foundation.Axiom.Position.Angle_ex
import EuclideanGeometry.Foundation.Axiom.Position.Angle_trash
import EuclideanGeometry.Foundation.Axiom.Linear.Perpendicular
import EuclideanGeometry.Foundation.Axiom.Triangle.Basic
import EuclideanGeometry.Foundation.Axiom.Circle.Basic
import EuclideanGeometry.Foundation.Axiom.Basic.Angle_trash
/-!

-/
noncomputable section
namespace EuclidGeom

variable {P : Type _} [EuclideanPlane P]

-- Feel free to change the name of the theorems and comments into better ones, or add sections to better organize theorems.
-- `Currently, the theorems are not well-organized, please follow the plan file to write and add theorems in this file into the plan file if they are not already in the plan`

-- we don't need to put the following definitions in the namespace Angle, since we will certainly not use it in the form of `ang.IsBis ray`
-- if only one condition is used, please change `structure : Prop` back to `def : Prop`, if more than one condition is used, please name each condition under structure, please do not use `∧`.



structure IsAngBis (ang : Angle P) (ray : Ray P) : Prop where
  eq_source : ang.source = ray.source
  eq_value : (Angle.mk_start_ray ang ray eq_source).value = (Angle.mk_ray_end ang ray eq_source).value
  same_sgn : ((Angle.mk_start_ray ang ray eq_source).value.IsPos ∧ ang.value.IsPos) ∨ ((Angle.mk_start_ray ang ray eq_source).value.IsNeg ∧ ang.value.IsNeg) ∨ ((Angle.mk_start_ray ang ray eq_source).value = (2⁻¹ * π).toAngValue ∧ ang.value = π ) ∨ ((Angle.mk_start_ray ang ray eq_source).value = 0 ∧ ang.value = 0)


structure IsAngBisLine (ang : Angle P) (l : Line P) : Prop where
  source_on : ang.source LiesOn l

structure IsExAngBis

structure IsExAngBiscetorLine

namespace Angle


/- when the Angle is flat, bis is on the left side-/
def AngBis (ang : Angle P) : Ray P where
  source := ang.source
  toDir := ang.start_ray.toDir * (2⁻¹ * ang.value.toReal).toAngValue.toDir

def AngBisLine (ang : Angle P) : Line P := ang.AngBis.toLine

def ExAngBis (ang : Angle P) : Ray P where
  source := ang.source
  toDir := ang.start_ray.toDir * (2⁻¹ * ang.value.toReal + 2⁻¹ * π).toAngValue.toDir

def ExAngBisLine (ang : Angle P) : Line P := ang.ExAngBis.toLine

end Angle

namespace Angle

theorem eq_source {ang : Angle P} : ang.source = ang.AngBis.source := rfl

theorem mk_start_ray_value_eq_half_angvalue {ang : Angle P} : (Angle.mk_start_ray ang ang.AngBis eq_source).value.toReal = 2⁻¹ * ang.value.toReal := by
  rw [mk_start_ray_value_eq_angdiff eq_source]
  rw [Dir.AngDiff]
  unfold AngBis
  simp only [mul_div_cancel''', todir_toangvalue_eq_self]
  have h₁ : (-π < 2⁻¹ * (value ang).toReal) ∧ (2⁻¹ * (value ang).toReal ≤ π) := by simp only [neg_half_pi_le_half_angvalue, half_angvalue_le_half_pi, and_self]
  simp only [h₁, toangvalue_toreal_eq_self_of_neg_pi_lt_le_pi]

theorem angbis_is_angbis {ang : Angle P} : IsAngBis ang ang.AngBis where
  eq_source := rfl
  eq_value := by
    have h : ang.source = ang.AngBis.source := rfl
    rw [mk_start_ray_value_eq_angdiff h, mk_ray_end_value_eq_angdiff h]
    rw [Dir.AngDiff, Dir.AngDiff, ← dir_eq_of_angvalue_eq]
    rw [AngBis]
    rw [end_ray_eq_start_ray_mul_value]
    simp only [mul_div_cancel''', mul_div_mul_left_eq_div]
    rw [← sub_todir_eq_todir_div]
    exact congrArg AngValue.toDir (ang.value.sub_half_eq_half).symm
  same_sgn := by
    rcases g with g₁|g₂|g₃|g₄
    · exact Or.inl (by simp only [g₁, and_true, half_angvalue_is_pos_if_angvalue_is_pos mk_start_ray_value_eq_half_angvalue g₁])
    · exact Or.inr (Or.inl (by simp only [g₂, and_true,half_angvalue_is_neg_if_angvalue_is_neg mk_start_ray_value_eq_half_angvalue g₂]))
    · exact Or.inr (Or.inr (Or.inl (⟨toreal_eq_half_pi_of_eq_half_pi_toangvalue (by simp only [mk_start_ray_value_eq_half_angvalue, g₃, neg_lt_self_iff, AngValue.toreal_pi]),g₃⟩)))
    · exact Or.inr (Or.inr (Or.inr (⟨AngValue.eq_zero_of_toreal_eq_zero (by simp only [mk_start_ray_value_eq_half_angvalue, g₄, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, AngValue.toreal_eq_zero_iff, or_true]),g₄⟩)))



theorem angbis_iff_angbis {ang : Angle P} {r : Ray P} : IsAngBis ang r ↔ r = ang.AngBis := by
  constructor
  · intro h
    have eq_source : r.source = ang.AngBis.source := by
      rw [← h.eq_source]
      apply eq_source
    have eq_todir : r.toDir = ang.AngBis.toDir := by
      unfold AngBis
      rw [mul_comm]
      apply eq_mul_of_div_eq
      apply dir_eq_of_angvalue_eq.mpr
      rw [← Dir.AngDiff, ← mk_start_ray_value_eq_angdiff h.eq_source]
      rcases or_assoc.mpr h.same_sgn with h' | h' | h'
      · simp
        have h₁ : value (mk_start_ray ang r h.eq_source) + value (mk_ray_end ang r h.eq_source) = ang.value := by
          rw [mk_start_ray_value_eq_angdiff, mk_ray_end_value_eq_angdiff, Dir.AngDiff, Dir.AngDiff, ← mul_toangvalue_eq_toangvalue_add]
          apply dir_eq_of_angvalue_eq.mp
          simp; rfl
        convert h₁ using 0
        rw [← h.eq_value]
        rw [← AngValue.toreal_toangvalue_eq_self (θ := value (mk_start_ray ang r h.eq_source)), AngValue.add_coe, ← two_mul]
        nth_rw 2 [← AngValue.toreal_toangvalue_eq_self (θ := value ang)]
        constructor
        · intro h₂
          rcases toAngValue_eq_iff.mp h₂ with ⟨k, h₃⟩
          apply toAngValue_eq_iff.mpr
          use 2 * k
          norm_num
          rw [← one_mul (value ang).toReal, ← mul_inv_cancel (a := 2) (by norm_num), mul_assoc, ← mul_sub, mul_assoc]
          exact congrArg (HMul.hMul 2) h₃
        · intro h₂
          rcases toAngValue_eq_iff.mp h₂ with ⟨k, h₃⟩
          have : k = 0 := by
            have aux₁ : -2 * π < 2 * (value (mk_start_ray ang r h.eq_source)).toReal - (value ang).toReal ∧ 2 * (value (mk_start_ray ang r h.eq_source)).toReal - (value ang).toReal < 2 * π := by
              have pi_pos : 0 < π := by positivity
              rcases h' with hp | hn
              · constructor
                · have : -2 * π < -π := by linarith [pi_pos]
                  apply lt_trans this
                  convert add_lt_add (mul_pos (a := 2) (by norm_num) (AngValue.ispos_iff.mp hp.1).1) (mul_lt_mul_of_neg_left (c := -1) (AngValue.ispos_iff.mp hp.2).2 (by norm_num)) using 1
                  simp
                  ring
                · convert add_lt_add ((mul_lt_mul_left (a := 2) (by norm_num)).mpr (AngValue.ispos_iff.mp hp.1).2) (mul_neg_of_neg_of_pos (a := -1) (by norm_num) (AngValue.ispos_iff.mp hp.2).1) using 1
                  ring
                  simp
              · constructor
                · convert add_lt_add ((mul_lt_mul_left (a := 2) (by norm_num)).mpr (AngValue.neg_pi_lt_toreal (θ := value (mk_start_ray ang r h.eq_source)))) (mul_pos_of_neg_of_neg (a := -1) (by norm_num) (AngValue.isneg_iff.mp hn.2)) using 1
                  simp
                  ring
                · have : π < 2 * π := by linarith [pi_pos]
                  apply lt_trans _ this
                  convert add_lt_add (mul_neg_of_pos_of_neg (a := 2) (by norm_num) (AngValue.isneg_iff.mp hn.1)) (mul_lt_mul_of_neg_left (c := -1) (AngValue.neg_pi_lt_toreal (θ := value ang)) (by norm_num)) using 1
                  ring
                  simp
            by_contra kne
            have aux₂ : 2 * (value (mk_start_ray ang r h.eq_source)).toReal - (value ang).toReal ≤ -2 * π ∨ 2 * π ≤ 2 * (value (mk_start_ray ang r h.eq_source)).toReal - (value ang).toReal := by
              rcases lt_trichotomy k 0 with klt | keq | kgt
              · left
                rw [h₃, neg_mul, neg_eq_neg_one_mul]
                apply (mul_le_mul_right (by positivity)).mpr
                exact Int.cast_le_neg_one_of_neg klt
              · exfalso
                exact kne keq
              · right
                rw [h₃]
                nth_rw 1 [← one_mul (2 * π)]
                apply (mul_le_mul_right (by positivity)).mpr
                exact Int.cast_one_le_of_pos kgt
            absurd aux₂
            rw [not_or, not_le, not_le]
            exact aux₁
          rw [this] at h₃
          simp at h₃
          rw [← one_mul (value ang).toReal, ← mul_inv_cancel (a := 2) (by norm_num), mul_assoc, ← mul_sub] at h₃
          apply toAngValue_eq_iff.mpr
          use 0
          simp
          linarith
      · rw [h'.1, h'.2]
        simp
      · rw [h'.1, h'.2]
        simp
        nth_rw 1 [← AngValue.toreal_toangvalue_eq_self (θ := 0)]
        apply toAngValue_eq_iff.mpr
        use 0
        field_simp
        ring_nf
        norm_num
    apply Ray.ext _ _ eq_source eq_todir
  · exact fun h ↦ (by rw [h]; apply angbis_is_angbis)


theorem ang_source_rev_eq_source_bis {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) : ang.reverse.source = r.source := by rw[ang.ang_source_rev_eq_source, h.eq_source]

--if a ray is the bisector of an angle whose value is not π , then it is also the bisector of the reverse angle.
theorem nonpi_eq_rev_angbis_of_angbis {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) (nonpi : ang.value ≠ π ): IsAngBis ang.reverse r where
  eq_source := by rw[h.eq_source.symm, ang.ang_source_rev_eq_source]
  eq_value := by
    rw [(by rfl : (Angle.mk_start_ray ang.reverse r (ang_source_rev_eq_source_bis h)) = (Angle.mk_ray_end ang r h.eq_source).reverse), (Angle.mk_ray_end ang r h.eq_source).ang_value_rev_eq_neg_value]
    rw [(by rfl : (Angle.mk_ray_end ang.reverse r (ang_source_rev_eq_source_bis h)) = (Angle.mk_start_ray ang r h.eq_source).reverse), (Angle.mk_start_ray ang r h.eq_source).ang_value_rev_eq_neg_value]
    simp only[h.eq_value]
  same_sgn := by
    rw [(by rfl : (Angle.mk_start_ray ang.reverse r (ang_source_rev_eq_source_bis h)) = (Angle.mk_ray_end ang r h.eq_source).reverse)]
    rw [(Angle.mk_ray_end ang r h.eq_source).ang_value_rev_eq_neg_value,ang.ang_value_rev_eq_neg_value]
    simp only [AngValue.neg_ispos_iff_isneg, AngValue.neg_isneg_iff_ispos, neg_eq_zero]
    rw [h.eq_value.symm]
    rcases h.same_sgn with h₁ | h₂ | h₃ | h₄
    · exact Or.inr (Or.inl h₁)
    · exact Or.inl h₂
    · absurd nonpi
      exact h₃.2
    · exact Or.inr (Or.inr (Or.inr h₄))

--if an angle does not values π, its reverse angle shares the same bisector.
theorem nonpi_angbis_eq_rev_angbis {ang : Angle P} (nonpi : ang.value ≠ π ): ang.AngBis = ang.reverse.AngBis := angbis_iff_angbis.mp (by simp only [angbis_is_angbis, ne_eq, nonpi, not_false_eq_true, nonpi_eq_rev_angbis_of_angbis])


--two lemma for theorem rev_angbis_of_pi_ang
theorem pi_ang_angbis_mk_ray_end_is_half_pi {ang : Angle P} (pi : ang.value = π ) : (Angle.mk_ray_end ang ang.AngBis eq_source).value = (2⁻¹ * π).toAngValue := by
  have : IsAngBis ang ang.AngBis := angbis_is_angbis
  apply toreal_eq_half_pi_of_eq_half_pi_toangvalue
  · field_simp
    simp only [← this.eq_value, mk_start_ray_value_eq_half_angvalue, pi, neg_lt_self_iff,
      AngValue.toreal_pi]
    ring

theorem pi_ang_rev_angbis_rev_mk_start_ray_is_half_pi {ang : Angle P} (pi : ang.value = π ) : (Angle.mk_start_ray ang.reverse ang.AngBis.reverse ang_source_rev_eq_source).value  = (2⁻¹ * π).toAngValue := by
  have : IsAngBis ang ang.AngBis := angbis_is_angbis
  let ang1 := Angle.mk_ray_end ang ang.AngBis eq_source
  let ang2 := Angle.mk_start_ray ang.reverse ang.AngBis.reverse ang_source_rev_eq_source
  calc
        ang2.value = π - ang1.value := by
          have h : ang1.value + ang2.value = π := by
            apply (reverse_ray_iff_sum_of_angle_eq_pi (by rfl)).mp
            · rw [(by rfl : ang2 = (Angle.mk ang.end_ray ang.AngBis.reverse _)), Ray.rev_rev_eq_self];
              rfl
          simp only [← h, add_sub_cancel']
        _ = (2⁻¹ * π).toAngValue := by
            simp only [pi_ang_angbis_mk_ray_end_is_half_pi pi, AngValue.sub_coe]
            ring_nf

--if an angle values π, the bisector of its reverse angle is the reverse ray of its bisector
theorem angrev_rev_angbis_of_pi_ang {ang : Angle P}(pi : ang.value = π ) : IsAngBis ang.reverse ang.AngBis.reverse where
  eq_source := ang_source_rev_eq_source
  eq_value := by
    have : IsAngBis ang ang.AngBis := angbis_is_angbis
    let ang1 := Angle.mk_ray_end ang.reverse ang.AngBis.reverse ang_source_rev_eq_source
    let ang2 := Angle.mk_start_ray ang ang.AngBis eq_source
    have h : ang1.value =  (2⁻¹ * π).toAngValue := by
      calc
        ang1.value = π - ang2.value := by simp only [← ((reverse_ray_iff_sum_of_angle_eq_pi (by rfl)).mp (by rfl) : ang1.value + ang2.value = π),add_sub_cancel]
        _ = π - (2⁻¹ * π).toAngValue := by simp only [this.eq_value, pi,pi_ang_angbis_mk_ray_end_is_half_pi, AngValue.sub_coe]
        _ = (2⁻¹ * π).toAngValue := by norm_num; ring_nf
    simp only [pi_ang_rev_angbis_rev_mk_start_ray_is_half_pi pi,h]
  same_sgn := Or.inr (Or.inr (Or.inl (⟨ pi_ang_rev_angbis_rev_mk_start_ray_is_half_pi pi, pi_ang_rev_is_pi pi⟩)))

--if a ray is the bisector of an angle whose value is π , then its reverse ray is the bisector of the reverse angle.
theorem rev_angbis_of_bis_pi_ang {ang : Angle P} {r : Ray P} (h : IsAngBis ang r) (pi : ang.value = π ): IsAngBis ang.reverse r.reverse := by simp only [angbis_iff_angbis.mp h,angrev_rev_angbis_of_pi_ang pi]





theorem angbisline_is_angbisline : sorry := sorry

theorem exangbis_is_exangbis : sorry := sorry

theorem exangbisline_is_exangbisline : sorry := sorry

end Angle

/-definition property: lies on the bis means bisect the angle-/
theorem lie_on_angbis (ang: Angle P) (A : P) (h : A ≠ ang.source): A LiesOn ang.AngBis ↔ IsAngBis ang (RAY _ _ h) := by
  rw [Angle.angbis_iff_angbis]
  exact ⟨fun g ↦ (by rw [← Ray.pt_pt_eq_ray ⟨g, h⟩]; rfl),
    fun g ↦ (by rw [← g]; apply Ray.pt_lies_on_pt_pt)⟩

/- underlying line of bis as the locus satisfying the sum of distance to each ray of the angle is 0 -/
theorem lie_on_angbisline_of_distance_zero (ang: Angle P) : sorry := sorry

theorem lie_on_angbis_of_lie_on_angbisline_inside_angle (ang : Angle P)  : sorry := sorry

/-bis lies inside the angle-/

/-construct the intercentor as the intersection of two bis-/

/-a triangle_nd admit an unique intercenter-/

structure IsIncenter (tri_nd : Triangle_nd P) (I : P) : Prop where

structure IsExcenter1 (tri_nd : Triangle_nd P) (E : P) : Prop where

structure IsIncircle (tri_nd : Triangle_nd P) (cir : Circle P) : Prop where

structure IsExcircle1 (tri_nd : Triangle_nd P) (cir : Circle P) : Prop where

namespace Triangle_nd

theorem angbisline_of_angle₁_angle₂_not_parallel {tri_nd : Triangle_nd P} : ¬ tri_nd.angle₁.AngBis.toLine ∥ tri_nd.angle₂.AngBis.toLine := by
  by_contra g
  let A₁ := (Angle.mk_start_ray tri_nd.angle₁ tri_nd.angle₁.AngBis tri_nd.angle₁.eq_source).reverse
  let A₂ := Angle.mk_ray_end tri_nd.angle₂ tri_nd.angle₂.AngBis tri_nd.angle₂.eq_source
  have sr : A₁.start_ray.toDir = A₂.start_ray.toDir := by
    have h₁ : A₁.start_ray = tri_nd.angle₁.AngBis := rfl
    have h₂ : A₂.start_ray = tri_nd.angle₂.AngBis := rfl
    rw [Ray.para_iff_para_toline] at g
    rw [← h₁] at g
    rw [← h₂] at g
    sorry
  have er : A₁.end_ray.toDirLine = A₂.end_ray.toDirLine.reverse := by
    have h₃ : A₁.end_ray = tri_nd.edge_nd₃.toRay := rfl
    have h₄ : A₂.end_ray = tri_nd.edge_nd₃.reverse.toRay := rfl
    rw [h₃]
    rw [h₄]
    have h₅ : tri_nd.edge_nd₃.reverse.toDirLine.reverse = tri_nd.edge_nd₃.reverse.reverse.toDirLine := by rw [Seg_nd.todirline_rev_eq_rev_toline]
    have h₆ : tri_nd.edge_nd₃.reverse.reverse.toDirLine = tri_nd.edge_nd₃.toDirLine := rfl
    rw [h₆] at h₅
    exact id h₅.symm
  have g₁ : IsConsecutiveIntAng A₁ A₂ := by
    constructor
    · rw [sr]
    · rw [er]
  have g₂ : A₁.value - A₂.value = π := by rw [value_sub_eq_pi_of_isconsecutiveintang g₁]
  sorry


def Incenter (tri_nd : Triangle_nd P) : P := Line.inx tri_nd.angle₁.AngBis.toLine tri_nd.angle₂.AngBis.toLine angbisline_of_angle₁_angle₂_not_parallel


def Excenter1 (tri_nd : Triangle_nd P) : P := sorry

def Incircle (tri_nd : Triangle_nd P) : Circle P := sorry

def Excircle1 (tri_nd : Triangle_nd P) : Circle P := sorry

end Triangle_nd

namespace Triangle_nd

theorem incenter_is_incenter : sorry := sorry

theorem excenter1_is_excenter1 : sorry := sorry

theorem incircle_is_incircle : sorry := sorry

theorem excircle1_is_excircle1 : sorry := sorry

end Triangle_nd

/-the intercenter lies inside of the triangle-/

theorem incenter_lies_int_triangle (triangle_nd : Triangle_nd P): sorry := sorry

end EuclidGeom
