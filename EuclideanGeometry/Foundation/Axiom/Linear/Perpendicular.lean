import EuclideanGeometry.Foundation.Axiom.Linear.Parallel

noncomputable section
namespace EuclidGeom

open Line

variable {P : Type _} [EuclideanPlane P] {α β γ : Type*} [ProjObj α] [ProjObj β] [ProjObj γ]
  {l₁ : α} {l₂ : β} {l₃ : γ}

def perpendicular (l₁ : α) (l₂ : β) : Prop :=
  ProjObj.toProj l₁ = (ProjObj.toProj l₂).perp

scoped infix : 50 "IsPerpendicularTo" => perpendicular
scoped infix : 50 "⟂" => perpendicular

namespace perpendicular

@[simp]
protected theorem irrefl (l : α) : ¬ (l ⟂ l) :=
  fun h ↦ Proj.one_ne_I (mul_right_cancel ((one_mul (ProjObj.toProj l)).trans h))

protected theorem symm (h : l₁ ⟂ l₂) : (l₂ ⟂ l₁) := by
  rw[perpendicular, Proj.perp, h, Proj.perp, ← mul_assoc , Proj.I_mul_I_eq_one_of_Proj, one_mul]

end perpendicular

section Perpendicular_and_parallel

theorem parallel_of_perp_perp (h₁ : l₁ ⟂ l₂) (h₂ : l₂ ⟂ l₃) : l₁ ∥ l₃ := by
  unfold perpendicular at h₂
  simp only [perpendicular, h₂, Proj.perp_perp_eq_self] at h₁
  exact h₁

theorem perp_of_parallel_perp (h₁ : l₁ ∥ l₂) (h₂ : l₂ ⟂ l₃) : l₁ ⟂ l₃ := h₁.trans h₂

theorem perp_of_perp_parallel (h₁ : l₁ ⟂ l₂) (h₂ : l₂ ∥ l₃) : l₁ ⟂ l₃ := h₁.trans (congrArg Proj.perp h₂)

theorem toproj_ne_toproj_of_perp (h : l₁ ⟂ l₂) : ProjObj.toProj l₁ ≠ ProjObj.toProj l₂ :=
  fun hp ↦ Proj.one_ne_I (mul_right_cancel (((one_mul (ProjObj.toProj l₂)).trans hp.symm).trans h))

theorem not_parallel_of_perp (h : l₁ ⟂ l₂) : ¬ l₁ ∥ l₂ := toproj_ne_toproj_of_perp h

end Perpendicular_and_parallel

section Perpendicular_constructions

def perp_line (A : P) (l : Line P) := Line.mk_pt_proj A (l.toProj.perp)

@[simp]
theorem toproj_of_perp_line_eq_toproj_perp (A : P) (l : Line P) : (perp_line A l).toProj = l.toProj.perp :=
  proj_eq_of_mk_pt_proj A l.toProj.perp

theorem perp_foot_preparation (A : P) (l : Line P) : l.toProj ≠ (perp_line A l).toProj :=
  Ne.trans_eq (perpendicular.irrefl l) (toproj_of_perp_line_eq_toproj_perp A l).symm

def perp_foot (A : P) (l : Line P) : P := Line.inx l (perp_line A l) (perp_foot_preparation A l)

def dist_pt_line (A : P) (l : Line P) := Seg.length (SEG A (perp_foot A l))

theorem perp_foot_lies_on_line (A : P) (l : Line P) : perp_foot A l LiesOn l := (Line.inx_is_inx _).1

theorem perp_foot_eq_self_iff_lies_on (A : P) (l : Line P) : perp_foot A l = A ↔ A LiesOn l := ⟨
  fun h ↦ Eq.mpr (h.symm ▸ Eq.refl (A LiesOn l)) (perp_foot_lies_on_line A l),
  fun h ↦ (inx_of_line_eq_inx _ ⟨h, (pt_lies_on_of_mk_pt_proj A (Proj.perp (Line.toProj l)))⟩).symm⟩

theorem line_of_self_perp_foot_eq_perp_line_of_not_lies_on {A : P} {l : Line P} (h : ¬ A LiesOn l) : LIN A (perp_foot A l) ((perp_foot_eq_self_iff_lies_on A l).mp.mt h) = perp_line A l :=
  eq_line_of_pt_pt_of_ne ((perp_foot_eq_self_iff_lies_on A l).mp.mt h) (pt_lies_on_of_mk_pt_proj A l.toProj.perp) (Line.inx_is_inx (perp_foot_preparation A l)).2

theorem dist_eq_zero_iff_lies_on (A : P) (l : Line P) : dist_pt_line A l = 0 ↔ A LiesOn l :=
  length_eq_zero_iff_deg.trans ((Eq.congr rfl rfl).trans (perp_foot_eq_self_iff_lies_on A l))

theorem dist_pt_line_shortest (A B : P) {l : Line P} (h : B LiesOn l) : dist A B ≥ dist_pt_line A l := sorry

end Perpendicular_constructions

end EuclidGeom
