import EuclideanGeometry.Foundation.Axiom.Basic.Plane
import EuclideanGeometry.Foundation.Axiom.Basic.Class

/-!
# Segments and rays

In this file, we define the class of segments, rays, and their coercions, as well as basic properties.  A more precise plan in terms of sections is as follows:
(1) (definition) We define the corresponding classes: rays, segments, and nondegenerate segments.
(2) (make) We define the make functions of rays, segments, and nondegenerate segments.
(3) (coercion) We define the coercions among rays, segments, and nondegenerate segments, as well as coercions to directions, or projective directions.
(4) (coercion-compatibility) We discuss compatibility of coercion functions.
(5) (lieson-compatibility) We discuss compatibility regarding points lying on or in the interior of segments or rays.
(6) (reverse) We introduce the concept of reversing a segment and reversing a ray.
(7) (extension) We define the extension ray of a nondegenerate segment.

We define the length function of a segment.

We define the concept of extending a segment into a ray.

We define the function that gives the midpoint of a segment.

We discuss the Archimedean property of a segment.

## Important definitions

* Class `Ray` : A \emph{ray} consists of the pair of its source point $P$ and its direction.
* Class `Seg` : A \emph{segment} consists of a pair of points: the source and the target. (We allow the source and the target to be the same.)
* Subclass `Seg_nd` : A \emph{nondegenerate segment} is a segment whose source and target are not equal.
* Definition `Seg.length` : The function that gives the length of a given segment.
* Definition `Ray.reverse` : Given a ray, this function returns the ray with the same source but with reversed direction.
* Definition `Seg.reverse` : Given a segment, this function swapped its source and target point.
* Definition `Seg_nd.reverse` : Given a nondegenerate segment, this function swapped its source and target point.
* Definition `Seg_nd.extension` : Given a nondegenerate segment, this function returns the extension ray of the segment.
* Definition `Seg.midpoint` : This function returns the hmidpoint of a segment.


## List of notations

* `SEG A B` : notation for the segment with source $A$ and target $B$.
* `SEG_nd A B` : notation for the segment with source $A$ and target $B$, where $h$ is a proof of that $A \neq B$.
* `RAY A B h` : notation for the ray with source $A$ in the direction of $B$, where $h$ is a proof of that $A \neq B$.

## List of main theorems

## Implementation notes

## Further works

-/


noncomputable section
namespace EuclidGeom

section definition

/-- A \emph{ray} consists of a pair of a point $P$ and a direction; it is the ray that starts at the point and extends in the given direction. -/
@[ext]
structure Ray (P : Type _) [EuclideanPlane P] where
  /-- returns the source of the ray. -/
  source : P
  /-- returns the direction of the ray. -/
  toDir : Dir

/-- A \emph{Segment} consists of a pair of points: the source and the target; it is the segment from the source to the target. (We allow the source and the target to be the same.) -/
@[ext]
structure Seg (P : Type _) [EuclideanPlane P] where
  /-- returns the source of the segment. -/
  source : P
  /-- returns the target of the segment. -/
  target : P

namespace Seg

/-- Given a segment $AB$, this function returns whether the segment $AB$ is nondegenerate, i.e. whether $A \neq B$. -/
def is_nd {P : Type _} [EuclideanPlane P] (seg : Seg P) : Prop := seg.target ≠ seg.source

end Seg

/-- A \emph{nondegenerate segment} is a segment $AB$ that is nondegenerate, i.e. $A \neq B$. -/
def Seg_nd (P : Type _) [EuclideanPlane P] := {seg : Seg P // seg.is_nd}


end definition

variable {P : Type _} [EuclideanPlane P]


section make

/-- Given two points $A$ and $B$, this returns the segment with source $A$ and target $B$; it is an abbreviation of  \verb|Seg.mk|. -/
scoped notation "SEG" => Seg.mk

/-- Given two distinct points $A$ and $B$, this function returns a nondegenerate segment with source $A$ and target $B$. -/
def Seg_nd.mk (A B : P) (h : B ≠ A) : Seg_nd P where
  val := SEG A B
  property := h

/-- This is to abbreviate the function \verb|Seg_nd.mk| into \verb|SEG_nd|. -/
scoped notation "SEG_nd" => Seg_nd.mk

/-- Given two distinct points $A$ and $B$, this function returns the ray starting from $A$ in the direction of $B$.  By definition, the direction of the ray is given by the normalization of the vector from $A$ to $B$, using \verb|toDir| function. -/
def Ray.mk_pt_pt (A B : P) (h : B ≠ A) : Ray P where
  source := A
  toDir := Vec_nd.toDir ⟨VEC A B, (vsub_ne_zero.mpr h)⟩

/-- This is to abbreviate \verb|Ray.mk_pt_pt| into \verb|RAY|. -/
scoped notation "RAY" => Ray.mk_pt_pt

end make


section coersion

namespace Ray

/-- Given a ray, this function returns its projective direction; it is the projective direction of the direction of the ray.  -/
def toProj (ray : Ray P) : Proj := (ray.toDir : Proj)

/-- Given a point $X$ and a ray $ray$, this function returns whether $X$ lies on $ray$; here saying that $X$ lies on $ray$ means that the vector from the start point of the ray to $X$ is some nonnegative multiple of the direction vector of the ray. -/
protected def IsOn (X : P) (ray : Ray P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ VEC ray.source X = t • ray.toDir.toVec

/-- Given a point $X$ and a ray, this function returns whether the point lies in the interior of the ray; here saying that a point lies in the interior of a ray means that it lies on the ray and is not equal to the source of the ray. -/
protected def IsInt (X : P) (ray : Ray P) : Prop := Ray.IsOn X ray ∧ X ≠ ray.source

/-- Given a ray, its carrier is the set of points that lie on the ray. -/
protected def carrier (ray : Ray P) : Set P := { X : P | Ray.IsOn X ray }

/-- Given a ray, its interior is the set of points that lie in the interior of the ray. -/
protected def interior (ray : Ray P) : Set P := { X : P | Ray.IsInt X ray }

/-- This is to register that a ray is an instance of a class of objects that we may speak of both carrier and interior (and that the interior is a subset of the carrier). -/
instance : IntFig Ray where
  carrier := Ray.carrier
  interior := Ray.interior
  interior_subset_carrier := fun _ [EuclideanPlane _] _ _ => And.left

end Ray

namespace Seg

/-- Given a segment, this function returns the vector associated to the segment, that is, the vector from the source of the segment to the target of the segment. -/
def toVec (seg : Seg P) : Vec := VEC seg.source seg.target

/-- Given a point $X$ and a segment $seg$, this function returns whether $X$ lies on $seg$; here saying that $X$ lies on $seg$ means that the vector from the source of $seg$ to $X$ is a real multiple $t$ of the vector of $seg$ with $0 \leq t \leq 1$. -/
protected def IsOn (X : P) (seg : Seg P) : Prop :=
  ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ VEC seg.source X  = t • (VEC seg.source seg.target)

/-- Given a point $X$ and a segment $seg$, this function returns whether $X$ lies in the interior of $seg$; here saying that $X$ lies in the interior of $seg$ means $X$ lies on $seg$ and is different from the source and the target of $seg$. -/
protected def IsInt (X : P) (seg : Seg P) : Prop := Seg.IsOn X seg ∧ X ≠ seg.source ∧ X ≠ seg.target

/-- Given a segment, this function returns the set of points that lie on the segment. -/
protected def carrier (seg : Seg P) : Set P := { X : P | Seg.IsOn X seg }

/-- Given a segment, this function returns the set of points that lie in the interior of the segment. -/
protected def interior (seg : Seg P) : Set P := { X : P | Seg.IsInt X seg }

/-- Instance \verb|IntFig Seg|: This is to register that a segment is an instance of a class of objects that we may speak of both carrier and interior (and that the interior is a subset of the carrier). -/
instance : IntFig Seg where
  carrier := Seg.carrier
  interior := Seg.interior
  interior_subset_carrier := fun _ [EuclideanPlane _] _ _ => And.left

end Seg

namespace Seg_nd

/-- One may naturally coerce a nondegenerate segment into a segment. -/
instance : Coe (Seg_nd P) (Seg P) where
  coe := fun x => x.1

/-- Given a nondegenerate segment, this function returns the source of the segment. -/
@[simp, pp_dot]
def source (seg_nd : Seg_nd P) : P := seg_nd.1.source

/-- Given a nondegenerate segment, this function returns the target of the segment. -/
@[simp, pp_dot]
def target (seg_nd : Seg_nd P) : P := seg_nd.1.target

/-- Given a nondegenerate segment $AB$, this function returns the nondegenerate vector $\overrightarrow{AB}$. -/
@[pp_dot]
def toVec_nd (seg_nd : Seg_nd P) : Vec_nd := ⟨VEC seg_nd.source seg_nd.target, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩

/-- Given a nondegenerate segment $AB$, this function returns the direction associated to the segment, defined by normalizing the nondegenerate vector $\overrightarrow{AB}$. -/
@[pp_dot]
def toDir (seg_nd : Seg_nd P) : Dir := Vec_nd.toDir seg_nd.toVec_nd

/-- Given a nondegenerate segment $AB$, this function returns the ray $AB$, whose source is $A$ in the direction of $B$. -/
@[pp_dot]
def toRay (seg_nd : Seg_nd P) : Ray P where
  source := seg_nd.1.source
  toDir := seg_nd.toDir

/-- Given a nondegenerate segment $AB$, this function returns the projective direction  of $AB$, defined as the projective direction of the nondegenerate vector $\overrightarrow{AB}$.  -/
@[pp_dot]
def toProj (seg_nd : Seg_nd P) : Proj := (seg_nd.toVec_nd.toProj : Proj)

/-- Given a point $A$ and a nondegenerate segment $seg_nd$, this function returns whether $A$ lies on $seg_nd$, namely, whether it lies on the corresponding segment.-/
protected def IsOn (X : P) (seg_nd : Seg_nd P) : Prop := Seg.IsOn X seg_nd.1

/-- Given a point $A$ and a nondegenerate segment $seg_nd$, this function returns whether $A$ lies in the interior of $seg_nd$, namely, whether it lies in the interior of the corresponding segment. -/
protected def IsInt (X : P) (seg_nd : Seg_nd P) : Prop := Seg.IsInt X seg_nd.1

/-- Given a nondegenerate segment, this function returns the set of points that lie on the segment. -/
protected def carrier (seg_nd : Seg_nd P) : Set P := { X : P | Seg_nd.IsOn X seg_nd }

/-- Given a nondegenerate segment, this function returns the set of points that lie in the interior of the segment. -/
protected def interior (seg_nd : Seg_nd P) : Set P := { X : P | Seg.IsInt X seg_nd }

/-- This is to register that a nondegenerate segment is an instance of a class of objects that we may speak of both carrier and interior (and that the interior is a subset of the carrier). -/
instance : IntFig Seg_nd where
  carrier := Seg_nd.carrier
  interior := Seg_nd.interior
  interior_subset_carrier := fun _ [EuclideanPlane _] _ _ => And.left

end Seg_nd

end coersion



section coersion_compatibility

/-- Given a nondegenerate segment, the direction of to the ray associated to the segment is the same as the direction of the segment. -/
@[simp]
theorem Seg_nd.toray_todir_eq_todir {seg_nd : Seg_nd P} : seg_nd.toRay.toDir = seg_nd.toDir := rfl

/-- Given a nondegenerate segment, the projective direction of the ray associated to the segment is the same as the projective direction of the segment. -/
@[simp]
theorem Seg_nd.toray_toproj_eq_toproj {seg_nd : Seg_nd P} : seg_nd.toRay.toProj = seg_nd.toProj := rfl


/-- Given two points $A$ and $B$, the vector associated to the segment $AB$ is same as vector $\overrightarrow{AB}$. -/
@[simp]
theorem seg_tovec_eq_vec {A B : P} : (SEG A B).toVec = VEC A B := rfl

/-- Given a segment $AB$, $A$ is same as $B$ if and only if vector $\overrightarrow{AB}$ is zero  -/
theorem tovec_eq_zero_of_deg {l : Seg P} : (l.target = l.source) ↔ l.toVec = 0 := by
  rw [Seg.toVec, Vec.mk_pt_pt, vsub_eq_zero_iff_eq]

/-- Given two distinct points $A$ and $B$, the direction of ray $AB$ is same as the negative direction of ray $BA$ -/
theorem Ray.todir_eq_neg_todir_of_mk_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toDir = - (RAY B A h.symm).toDir := by
  simp only [Ray.mk_pt_pt, ne_eq]
  exact (neg_todir_eq_todir_smul_neg ⟨VEC B A, (ne_iff_vec_ne_zero _ _).mp h.symm⟩ ⟨VEC A B, (ne_iff_vec_ne_zero _ _).mp h⟩ (by rw [neg_smul, one_smul, neg_vec]) (by norm_num)).symm

/-- Given two distinct points $A$ and $B$, the projective direction of ray $AB$ is same as that of ray $BA$. -/
theorem Ray.toproj_eq_toproj_of_mk_pt_pt {A B : P} (h : B ≠ A) : (RAY A B h).toProj = (RAY B A h.symm).toProj := (Dir.eq_toproj_iff _ _).mpr (.inr (todir_eq_neg_todir_of_mk_pt_pt h))

/-- Given two distinct points $A$ and $B$, the ray associated to the segment $AB$ is same as ray $AB$. -/
theorem pt_pt_seg_toray_eq_pt_pt_ray {A B : P} (h : B ≠ A) : (Seg_nd.mk A B h).toRay = Ray.mk_pt_pt A B h := rfl

/-- Given a segment $AB$, $AB$ is nondegenerate if and only if vector  $\overrightarrow{AB}$ is nonzero. -/
theorem Seg.is_nd_iff_tovec_ne_zero {l : Seg P} : l.is_nd ↔ l.toVec ≠ 0 := tovec_eq_zero_of_deg.not

/-- If $ray_1$ and $ray_2$ are two rays with the same projective direction, then the direction vector of $ray_2$ is a real multiple of the direction vector of $ray_1$. -/
theorem dir_parallel_of_same_proj {ray₁ ray₂ : Ray P} (h : ray₁.toProj = ray₂.toProj) : ∃t : ℝ, ray₂.toDir.toVec = t • ray₁.toDir.toVec := by
  rcases (Dir.eq_toproj_iff _ _).mp h with xy | xy
  · use 1
    rw [one_smul, xy]
  · use -1
    rw [xy, Dir.tovec_neg_eq_neg_tovec, smul_neg, neg_smul, one_smul, neg_neg]

end coersion_compatibility



section lieson_compatibility

/-- Given a nondegenerate segment, a point lies on the nondegenerate segment if and only if it lies on the corresponding segment (without knowing the nondegenate condition). -/
@[simp]
theorem Seg_nd.lies_on_of_lies_on {X : P} {seg_nd : Seg_nd P} : X LiesOn seg_nd ↔ X LiesOn seg_nd.1 := ⟨ fun a => a, fun a => a ⟩

/-- Given a nondegenerate segment, a point lies in the interior of the nondegenerate segment if and only if it lies in the interior of the corresponding segment (without knowing the nondegenate condition). -/
@[simp]
theorem Seg_nd.lies_int_of_lies_int {X : P} {seg_nd : Seg_nd P} : X LiesInt seg_nd ↔ X LiesInt seg_nd.1 := ⟨ fun a => a, fun a => a ⟩

/-- Given a ray, a point $X$ lies on the ray if and only if the vector from the source of the ray to $X$ is a nonnegative multiple of the direction of ray. -/
theorem Ray.lies_on_iff {X : P} {ray : Ray P} : X LiesOn ray ↔ ∃ (t : ℝ) , 0 ≤ t ∧ VEC ray.source X = t • ray.toDir.toVec := Iff.rfl

/-- Given a ray, a point $X$ lies in the interior of the ray if and only if the vector from the source of the ray to $X$ is a positive multiple of the direction of ray. -/
theorem Ray.lies_int_iff {X : P} {ray : Ray P} : X LiesInt ray ↔ ∃ (t : ℝ) , 0 < t ∧ VEC ray.source X = t • ray.toDir.toVec := by
  constructor
  intro ⟨⟨t, tnonneg, ht⟩, ns⟩
  · use t
    constructor
    · contrapose! ns
      have : t = 0 := by linarith
      rw [eq_iff_vec_eq_zero, ht, this, zero_smul]
    · exact ht
  · intro ⟨t, tpos, ht⟩
    constructor
    · exact ⟨t, by linarith, ht⟩
    · rw [ne_iff_vec_ne_zero, ht, smul_ne_zero_iff]
      exact ⟨by linarith, Dir.tovec_ne_zero ray.toDir⟩

/-- For a nondegenerate segment $AB$, a point $X$ lies on $AB$ if and only if there exist a real number $t$ satisfying that $0 \leq t \leq 1$ and that the vector $\overrightarrow{AX}$ is same as $t \cdot \overrightarrow{AB}$. -/
theorem Seg_nd.lies_on_iff {X : P} {seg_nd : Seg_nd P}: X LiesOn seg_nd ↔ ∃ (t : ℝ) , 0 ≤ t ∧ t ≤ 1 ∧ VEC seg_nd.source X = t • seg_nd.toVec_nd.1 := Iff.rfl

/-- For a nondegenerate segment $AB$, a point $X$ lies in the interior of $AB$ if and only if there exist a real number $t$ satisfying that $0 < t < 1$ and that the vector $\overrightarrow{AX}$ is same as $t \cdot \overrightarrow{AB}$. -/
theorem Seg_nd.lies_int_iff {X : P} {seg_nd : Seg_nd P}: X LiesInt seg_nd ↔ ∃ (t : ℝ) , 0 < t ∧ t < 1 ∧ VEC seg_nd.source X = t • seg_nd.toVec_nd.1 := by
  constructor
  · intro ⟨⟨t, tnonneg, tle1, ht⟩, ns, nt⟩
    rw [ne_iff_vec_ne_zero] at ns nt
    use t
    constructor
    · contrapose! ns
      have : t = 0 := by linarith
      rw [ht, this, zero_smul]
    · constructor
      · contrapose! nt
        have : t = 1 := by linarith
        simp [this] at ht
        rw [← vec_sub_vec seg_nd.source]
        exact sub_eq_zero_of_eq ht
      · exact ht
  · intro ⟨t, tpos, tlt1, ht⟩
    constructor
    · exact ⟨t, by linarith, by linarith, ht⟩
    · constructor
      · rw [ne_iff_vec_ne_zero]
        rw [Seg_nd.source] at ht
        rw [ht, smul_ne_zero_iff]
        exact ⟨ by linarith, seg_nd.toVec_nd.2⟩
      · simp [Seg_nd.toVec_nd] at ht
        rw [ne_iff_vec_ne_zero]
        have h1 : VEC seg_nd.target X = (t - 1) • seg_nd.toVec_nd.1 := by
          rw [sub_smul]
          simp [Seg_nd.toVec_nd]
          rw [← ht]
          exact (vec_sub_vec _ _ _).symm
        rw [Seg_nd.target] at h1
        rw [h1, smul_ne_zero_iff]
        exact ⟨ by linarith, seg_nd.toVec_nd.2⟩

/-- For a segment $AB$, if there exists an interior point $X$, then it is nondegenerate. -/
theorem Seg.is_nd_of_pt_liesint {seg : Seg P} {X : P} (h : X LiesInt seg) : seg.is_nd := sorry

/-- For a segment $AB$, a point $X$ lies in the interior of $AB$ if and only if $AB$ is nondegenerate, and there exist a real number $t$ satisfying that $0 < t < 1$ and that the vector $\overrightarrow{AX}$ is same as $t \cdot \overrightarrow{AB}$. -/
theorem Seg.lies_int_iff {X : P} {seg : Seg P}: X LiesInt seg ↔ seg.is_nd ∧ (∃ (t : ℝ) , 0 < t ∧ t < 1 ∧ VEC seg.source X = t • seg.toVec) := by
  constructor
  · intro h1
    let segnd : Seg_nd P := ⟨ seg, seg.is_nd_of_pt_liesint h1 ⟩
    exact ⟨ segnd.2, (segnd.lies_int_iff).mp h1 ⟩
  · intro h2
    let segnd : Seg_nd P := ⟨ seg, h2.1 ⟩
    exact (segnd.lies_int_iff).mpr h2.2


/-- Given a segment $AB$, the source $A$ of the segment lies on the segment. -/
theorem Seg.source_lies_on {seg : Seg P} : seg.source LiesOn seg :=
  ⟨0, by rfl, zero_le_one, by rw [vec_same_eq_zero, zero_smul]⟩

/--  Given a segment $AB$, the target $B$ lies on the segment $AB$. -/
theorem Seg.target_lies_on {seg : Seg P} : seg.target LiesOn seg := ⟨1, zero_le_one, by rfl, by rw [one_smul]⟩

/-- Given a segment $AB$, the source $A$ does not belong to the interior of $AB$. -/
theorem Seg.source_not_lies_int {seg : Seg P} : ¬ seg.source LiesInt seg := fun h ↦ h.2.1 rfl

/-- Given a segment $AB$, the target $B$ does not belong to the interior of $AB$. -/
theorem Seg.target_not_lies_int {seg : Seg P} : ¬ seg.target LiesInt seg := fun h ↦ h.2.2 rfl

/-- For a segment $AB$, every point of the interior of $AB$ lies on the segment $AB$. -/
theorem Seg.lies_on_of_lies_int {X : P} {seg : Seg P} (h : X LiesInt seg) : X LiesOn seg := h.1

/-- Given a nondegenerate segment $AB$, the source $A$ of the segment lies on the segment. -/
theorem Seg_nd.source_lies_on {seg_nd : Seg_nd P} : seg_nd.source LiesOn seg_nd := seg_nd.1.source_lies_on

/-- Given a nondegenerate segment $AB$, the target $B$ lies on the segment $AB$. -/
theorem Seg_nd.target_lies_on {seg_nd : Seg_nd P} : seg_nd.target LiesOn seg_nd := seg_nd.1.target_lies_on

/-- Given a nondegenerate segment $AB$, the source $A$ does not belong to the interior of $AB$. -/
theorem Seg_nd.source_not_lies_int {seg_nd : Seg_nd P} : ¬ seg_nd.source LiesInt seg_nd := fun h ↦ h.2.1 rfl

/-- Given a nondegenerate segment $AB$, the target $B$ does not belong to the interior of $AB$. -/
theorem Seg_nd.target_not_lies_int {seg_nd : Seg_nd P} : ¬ seg_nd.target LiesInt seg_nd := fun h ↦ h.2.2 rfl

/-- For a nondegenerate segment $AB$, every point of the interior of $AB$ lies on the segment $AB$. -/
theorem Seg_nd.lies_on_of_lies_int {X : P} {seg_nd : Seg_nd P} (h : X LiesInt seg_nd) : X LiesOn seg_nd := h.1

/-- Given a ray, the source of the ray lies on the ray. -/
theorem Ray.source_lies_on {ray : Ray P} : ray.source LiesOn ray := ⟨0, by rfl, by rw [vec_same_eq_zero, zero_smul]⟩

/-- Given a ray, the source of the ray does not lie in the interior of the ray. -/
theorem Ray.source_not_lies_int {ray : Ray P} : ¬ ray.source LiesInt ray := fun h ↦ h.2 rfl

/-- For a ray, every point of the interior of the ray lies on the ray. -/
theorem Ray.lies_on_of_lies_int {X : P} {ray : Ray P} (h : X LiesInt ray) : X LiesOn ray := h.1


/-- Given a ray, a point lies in the interior of the ray if and only if it lies on the ray and is different from the source of ray. -/
theorem Ray.lies_int_def {X : P} {ray : Ray P} : X LiesInt ray ↔ X LiesOn ray ∧ X ≠ ray.source := Iff.rfl


/-- For a nondegenerate segment $AB$, every point of the segment $AB$ lies on the ray associated to $AB$.  -/
theorem Seg_nd.lies_on_toray_of_lies_on {X : P} {seg_nd : Seg_nd P} (h : X LiesOn seg_nd) : X LiesOn seg_nd.toRay := by
  rcases h with ⟨t, ht0, _, h⟩
  refine' ⟨t * Vec.norm (VEC seg_nd.source seg_nd.target),
    mul_nonneg ht0 (Vec.norm_nonnegative (VEC seg_nd.source seg_nd.target)), _⟩
  simp only [toRay, h, Complex.real_smul, Complex.ofReal_mul, mul_assoc]
  exact congrArg (HMul.hMul _) seg_nd.toVec_nd.norm_smul_todir_eq_self.symm

/-- For a nondegenerate segment $seg_nd$, every point of the interior of the $seg_nd$ lies in the interior of the ray associated to the $seg_nd$. -/
theorem Seg_nd.lies_int_toray_of_lies_int {X : P} {seg_nd : Seg_nd P} (h : X LiesInt seg_nd) : X LiesInt seg_nd.toRay :=
  ⟨Seg_nd.lies_on_toray_of_lies_on h.1, h.2.1⟩

/-- Given two distinct points $A$ and $B$, $B$ lies on the ray $AB$. -/
theorem Ray.snd_pt_lies_on_mk_pt_pt {A B : P} (h : B ≠ A) : B LiesOn (RAY A B h) := by
  show B LiesOn (SEG_nd A B h).toRay
  exact Seg_nd.lies_on_toray_of_lies_on Seg.target_lies_on

/-- Given a point $A$ on a ray, the direction of the ray is the same as the direction from the source of the ray to $A$. -/
@[simp]
theorem Ray.pt_pt_todir_eq_ray_todir {ray : Ray P} {A : P} (h : A LiesInt ray) : (RAY ray.1 A h.2).toDir = ray.toDir := by
  rcases (lies_int_iff).mp h with ⟨t, ht, eq⟩
  exact (todir_eq_todir_smul_pos ray.2.toVec_nd ⟨VEC ray.1 A, _⟩ eq ht).symm.trans ray.2.tovec_nd_todir_eq_self

/-- Given a point $A$ on a ray, the ray starting at the source of the ray in the direction of $A$ is the same as the original ray. -/
@[simp]
theorem Ray.pt_pt_eq_ray {ray : Ray P} {A : P} (h : A LiesInt ray) : RAY ray.1 A h.2 = ray :=
  (Ray.ext _ ray) rfl (pt_pt_todir_eq_ray_todir h)


/-- Given a point $A$ on a ray, the ray associated to the segment from the source of the ray to $A$ is the same as the original ray. -/
@[simp]
theorem Ray.source_int_toray_eq_ray {ray : Ray P} {A : P} (h : A LiesInt ray) : (SEG_nd ray.source A h.2).toRay = ray :=
  Ray.pt_pt_eq_ray h


/-- Given two segments $seg_1$ and $seg_2$, if the source and the target of the $seg_1$ both lie on $seg_2$, then every point of $seg_1$ lies on $seg_2$. -/
theorem every_pt_lies_on_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesOn seg₁) : (A LiesOn seg₂) := by
  rcases h₁ with ⟨x,xnonneg,xle1,hx⟩
  rcases h₂ with ⟨y,ynonneg,yle1,hy⟩
  rcases ha with ⟨t,tnonneg,tleone,ht⟩
  rw[←vec_add_vec seg₁.source seg₂.source,←vec_add_vec seg₁.source seg₂.source seg₁.target,←neg_vec,hx,hy,neg_add_eq_iff_eq_add,←neg_smul,smul_add,smul_smul,smul_smul,←add_smul,←add_smul,←add_assoc,mul_neg,←sub_eq_add_neg,←one_mul x,←mul_assoc,←sub_mul,mul_one] at ht
  use ( (1- t) * x + t * y)
  constructor
  apply add_nonneg
  apply mul_nonneg
  linarith
  linarith
  apply mul_nonneg tnonneg ynonneg
  constructor
  nth_rw 2[←sub_add_cancel 1 t,←mul_one (1-t)]
  nth_rw 4[←mul_one t]
  apply add_le_add
  apply mul_le_mul _ xle1 xnonneg
  linarith
  simp only [le_refl]
  apply mul_le_mul _ yle1 ynonneg tnonneg
  simp only [le_refl]
  rw [ht]

/-- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie in the interior of $seg_2$, and if $A$ is a point on $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_pt_lies_int_seg_of_source_and_target_lies_int_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesInt seg₂) (h₂ : seg₁.target LiesInt seg₂) {A : P} (ha : A LiesOn seg₁) : A LiesInt seg₂ := by
  rw[Seg.lies_int_iff]
  constructor
  apply ((Seg.lies_int_iff).mp h₁).1
  rw[Seg.lies_int_iff] at h₁ h₂
  rcases h₁ with ⟨ _ ,x,xpos,xlt1,hx⟩
  rcases h₂ with ⟨ _ ,y,ypos,ylt1,hy⟩
  rcases ha with ⟨t,tnonneg,tle1,ht⟩
  use ( (1- t) * x + t * y)
  by_cases h : 0=t
  constructor
  simp only [←h, sub_zero, one_mul, zero_mul, add_zero]
  exact xpos
  constructor
  simp only [←h, sub_zero, one_mul, zero_mul, add_zero]
  exact xlt1
  rw[←h,zero_smul,←eq_iff_vec_eq_zero] at ht
  simp only [← h, sub_zero, one_mul, zero_mul, add_zero,ht,hx]
  constructor
  apply lt_of_lt_of_le (mul_pos (lt_of_le_of_ne tnonneg h) ypos)
  simp only [le_add_iff_nonneg_left, gt_iff_lt, sub_pos]
  apply mul_nonneg
  linarith
  linarith
  constructor
  have: (1-t)*x+t*y<(1-t)*x+t:=by
    simp only [add_lt_add_iff_left, gt_iff_lt]
    nth_rw 2[←mul_one t]
    apply mul_lt_mul_of_pos_left ylt1 (lt_of_le_of_ne tnonneg h)
  apply lt_of_lt_of_le this
  have :1=1-t+t:=by norm_num
  nth_rw 2 [this]
  apply add_le_add
  nth_rw 2[←mul_one (1-t)]
  apply mul_le_mul
  linarith
  linarith
  linarith
  linarith
  linarith
  rw[←vec_add_vec seg₂.1 seg₁.1 A,ht,←vec_sub_vec seg₂.1 seg₁.1 seg₁.2,hy,hx,←sub_smul,smul_smul,←add_smul,←sub_eq_zero,←sub_smul,smul_eq_zero]
  left
  ring

/-- Given two segments $seg_1$ and $seg_2$, if the source and the target of $seg_1$ both lie on $seg_2$, and if $A$ is a point in the interior of $seg_1$, then $A$ lies in the interior of $seg_2$. -/
theorem every_int_pt_lies_int_seg_of_source_and_target_lies_on_seg {seg₁ seg₂ : Seg P} (h₁ : seg₁.source LiesOn seg₂) (h₂ : seg₁.target LiesOn seg₂) {A : P} (ha : A LiesInt seg₁) : A LiesInt seg₂ := by
  apply (Seg.lies_int_iff).mpr
  rcases h₁ with ⟨x,xnonneg,xle1,hx⟩
  rcases h₂ with ⟨y,ynonneg,yle1,hy⟩
  rcases (Seg.lies_int_iff).mp ha with ⟨nd,t,tpos,tlt1,ht⟩
  constructor
  rw[Seg.is_nd,ne_iff_vec_ne_zero]
  contrapose! nd
  rw[nd,smul_zero,←eq_iff_vec_eq_zero] at hx hy
  rw[Seg.is_nd,not_not,eq_iff_vec_eq_zero,hx,hy,vec_same_eq_zero]
  rw[Seg.toVec,←vec_sub_vec seg₂.1,← vec_sub_vec seg₂.1 seg₁.1 seg₁.2,sub_eq_iff_eq_add,hx,hy,←sub_smul,smul_smul,←add_smul] at ht
  use ( (1- t) * x + t * y)
  have ynex:y≠x:= by
    contrapose! nd
    rw[Seg.is_nd,not_not,eq_iff_vec_eq_zero,←vec_sub_vec seg₂.1,hx,hy,←sub_smul,nd,sub_self,zero_smul]
  constructor
  by_cases h : 0=x
  rw[←h,mul_zero,zero_add]
  apply mul_pos
  exact tpos
  apply lt_of_le_of_ne
  exact ynonneg
  rw[h]
  symm
  exact ynex
  have :0<(1-t)*x:=by
    apply mul_pos
    linarith
    apply lt_of_le_of_ne xnonneg h
  apply lt_of_lt_of_le this
  simp only [le_add_iff_nonneg_right, gt_iff_lt]
  apply mul_nonneg
  linarith
  linarith
  constructor
  by_cases h : 1=x
  simp only [←h,mul_one,sub_add,sub_lt_iff_lt_add,lt_add_iff_pos_right, sub_pos, gt_iff_lt]
  nth_rw 2[←mul_one t]
  apply mul_lt_mul_of_pos_left
  apply lt_of_le_of_ne
  exact yle1
  rw[h]
  exact ynex
  exact tpos
  have :(1-t)*x+t*y<(1-t)+t*y:=by
    simp only [add_lt_add_iff_right, gt_iff_lt, sub_pos]
    nth_rw 2 [← mul_one (1-t)]
    apply mul_lt_mul_of_pos_left
    apply lt_of_le_of_ne xle1
    symm
    exact h
    linarith
  apply lt_of_lt_of_le this
  rw[sub_add,tsub_le_iff_right, le_add_iff_nonneg_right, sub_nonneg,←mul_one t,mul_assoc,one_mul]
  apply mul_le_mul _ yle1 ynonneg
  linarith
  linarith
  rw[ht,←sub_eq_zero,Seg.toVec,←sub_smul,smul_eq_zero]
  left
  ring

/-- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point on the segment, then $A$ lies on the ray. -/
theorem every_pt_lies_on_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂: seg.target LiesOn ray) {A : P} (ha : A LiesOn seg) : A LiesOn ray :=by
  rcases h₁ with ⟨x,xnonneg,hx⟩
  rcases h₂ with ⟨y,ynonneg,hy⟩
  rcases ha with ⟨t,tnonneg,tleone,ht⟩
  rw[←vec_add_vec seg.source ray.source,←vec_add_vec seg.source ray.source seg.target,←neg_vec,hx,hy,neg_add_eq_iff_eq_add,←neg_smul,smul_add,smul_smul,smul_smul,←add_smul,←add_smul,←add_assoc,mul_neg,←sub_eq_add_neg,←one_mul x,←mul_assoc,←sub_mul,mul_one] at ht
  use ( (1- t) * x + t * y)
  constructor
  apply add_nonneg
  apply mul_nonneg
  linarith
  linarith
  apply mul_nonneg
  linarith
  linarith
  rw[ht]

/-- Given a segment and a ray, if the source and the target of the segment both lie in the interior of the ray, and if $A$ is a point on the segment, then $A$ lies in the interior of the ray.-/
theorem every_pt_lies_int_ray_of_source_and_target_lies_int_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesInt ray) (h₂ : seg.target LiesInt ray) {A : P} (ha : A LiesOn seg) : A LiesInt ray := by
  rcases (Ray.lies_int_iff.mp h₁) with ⟨x,xpos,hx⟩
  rcases (Ray.lies_int_iff.mp h₂) with ⟨y,ypos,hy⟩
  apply Ray.lies_int_iff.mpr
  rcases ha with ⟨t,tnonneg,tle1,ht⟩
  rw[←vec_sub_vec ray.source,←vec_sub_vec ray.source seg.source seg.target,hx,hy,sub_eq_iff_eq_add,←sub_smul,smul_smul,←add_smul,mul_sub] at ht
  use (t*y+(1-t)*x)
  constructor
  by_cases h : 0=t
  rw[←h]
  linarith
  apply lt_of_lt_of_le (mul_pos (lt_of_le_of_ne tnonneg h) ypos)
  simp only [le_add_iff_nonneg_right, gt_iff_lt, sub_pos]
  apply mul_nonneg
  linarith
  linarith
  rw[ht,←sub_eq_zero,←sub_smul,smul_eq_zero]
  left
  ring

/-- Given a segment and a ray, if the source and the target of the segment both lie on the ray, and if $A$ is a point in the interior of the segment, then $A$ lies in the interior of the ray. -/
theorem every_int_pt_lies_int_ray_of_source_and_target_lies_on_ray {seg : Seg P} {ray : Ray P} (h₁ : seg.source LiesOn ray) (h₂ : seg.target LiesOn ray) {A : P} (ha : A LiesInt seg) : A LiesInt ray := by
  rcases h₁ with ⟨x,xnonneg,hx⟩
  rcases h₂ with ⟨y,ynonneg,hy⟩
  rcases Seg.lies_int_iff.mp ha with ⟨nd, t, tpos, tlt1, ht⟩
  simp only [Seg.toVec,←vec_sub_vec ray.1 seg.1,hx,hy,sub_eq_iff_eq_add,←sub_smul,smul_smul,←add_smul] at ht
  apply Ray.lies_int_iff.mpr
  use (1-t)*x+t*y
  have ynex:y≠x:= by
    contrapose! nd
    rw[Seg.is_nd,not_not,eq_iff_vec_eq_zero,←vec_sub_vec ray.1,hx,hy,←sub_smul,nd,sub_self,zero_smul]
  constructor
  by_cases h : 0=x
  rw[←h,mul_zero,zero_add]
  apply mul_pos
  exact tpos
  apply lt_of_le_of_ne
  exact ynonneg
  rw[h]
  symm
  exact ynex
  have :0<(1-t)*x:=by
    apply mul_pos
    linarith
    apply lt_of_le_of_ne xnonneg h
  apply lt_of_lt_of_le this
  simp only [le_add_iff_nonneg_right, gt_iff_lt]
  apply mul_nonneg
  linarith
  linarith
  rw[ht,←sub_eq_zero,←sub_smul,smul_eq_zero]
  left
  ring

/-- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies on $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies on $ray_2$. -/
theorem every_pt_lies_on_ray_of_source_lies_on_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesOn ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesOn ray₂ := by
  rcases h with ⟨x,xnonneg,hx⟩
  rcases ha with ⟨t,tnonneg,ht⟩
  use x+t
  constructor
  linarith
  rw[←vec_add_vec ray₂.source ray₁.source A,hx,ht,e,add_smul]

/-- Given two rays $ray_1$ and $ray_2$ with same direction, if the source of $ray_1$ lies in the interior of $ray_2$, and if $A$ is a point on $ray_1$, then $A$ lies in the interior of $ray_2$. -/
theorem every_pt_lies_int_ray_of_source_lies_int_ray_and_same_dir {ray₁ ray₂ : Ray P} (e : ray₁.toDir = ray₂.toDir) (h : ray₁.source LiesInt ray₂) {A : P} (ha : A LiesOn ray₁) : A LiesInt ray₂ := by
  apply Ray.lies_int_iff.mpr
  rcases ha with ⟨t,tnonneg,ht⟩
  rcases Ray.lies_int_iff.mp h with ⟨x, xpos, hx⟩
  rw[e] at ht
  use x+t
  constructor
  linarith
  rw[←vec_add_vec ray₂.1 ray₁.1,hx,ht,add_smul]

end lieson_compatibility



section reverse

/-- Given a ray, this function returns the ray with the same source but with reversed direction. -/
@[pp_dot]
def Ray.reverse (ray : Ray P): Ray P where
  source := ray.source
  toDir := - ray.toDir

/-- Given a segment $AB$, this function returns its reverse, i.e. the segment $BA$. -/
@[pp_dot]
def Seg.reverse (seg : Seg P): Seg P where
  source := seg.target
  target := seg.source

/-- The reverse of segment $AB$ is the segment $BA$. -/
@[simp]
theorem seg_rev {A B : P} : (SEG A B).reverse = SEG B A := rfl

/-- If a segment is nondegenerate, so is its reverse segment. -/
theorem nd_of_rev_of_nd {seg : Seg P} (nd : seg.is_nd) : seg.reverse.is_nd := by
  simp only [Seg.is_nd]
  push_neg
  symm
  apply nd

/-- Given a nondegenerate segment $AB$, this function returns the reversed nondegenerate segment $BA$. -/
def Seg_nd.reverse (seg_nd : Seg_nd P) : Seg_nd P := ⟨seg_nd.1.reverse, nd_of_rev_of_nd seg_nd.2⟩

/-- The reverse of a nondegenerate segment $AB$ is the nondegenerate segment $BA$. -/
@[simp]
theorem seg_nd_rev {A B : P} (h : B ≠ A) : (SEG_nd A B h).reverse = SEG_nd B A h.symm := rfl

/-- Given a nondegenerate segment, first viewing it as a segment and then reversing it is the same as first reversing it and then viewing it as a segment. -/
@[simp]
theorem Seg_nd.rev_toseg_eq_toseg_rev {seg_nd : Seg_nd P} :  seg_nd.reverse.1 = seg_nd.1.reverse := rfl

/-- Given a ray, the source of the reversed ray is the source of the ray. -/
@[simp]
theorem Ray.source_of_rev_eq_source {ray : Ray P} : ray.reverse.source = ray.source := rfl

/-- Reversing a ray twice gives back to the original ray. -/
@[simp]
theorem Ray.rev_rev_eq_self {ray : Ray P} : ray.reverse.reverse = ray := by
  simp only [reverse, neg_neg]

/-- Reversing a segment twice gives back to the original segment. -/
@[simp]
theorem Seg.rev_rev_eq_self {seg : Seg P} : seg.reverse.reverse = seg := rfl

/-- Reversing a nondegenerate segment twice gives back to the original nondegenerate segment. -/
@[simp]
theorem Seg_nd.rev_rev_eq_self {seg_nd : Seg_nd P} : seg_nd.reverse.reverse = seg_nd := rfl

/--Given a ray, the direction of the reversed ray is the negative of the direction of the ray. -/
@[simp]
theorem Ray.todir_of_rev_eq_neg_todir {ray : Ray P} : ray.reverse.toDir = - ray.toDir := rfl

/-- Given a ray, the direction vector of the reversed ray is the negative of the direction vector of the ray. -/
@[simp]
theorem Ray.tovec_of_rev_eq_neg_tovec {ray : Ray P} : ray.reverse.toDir.toVec = - ray.toDir.toVec := rfl

/-- Given a ray, the projective direction of the reversed ray is the same as that of the ray. -/
@[simp]
theorem Ray.toproj_of_rev_eq_toproj {ray : Ray P} : ray.reverse.toProj = ray.toProj := by
  apply (Dir.eq_toproj_iff _ _).mpr
  right
  rfl

/-- Given a segment, the vector associated to the reversed segment is the negative of the vector associated to the segment. -/
@[simp]
theorem Seg.tovec_of_rev_eq_neg_tovec {seg : Seg P} : seg.reverse.toVec = - seg.toVec := by
  simp only [reverse,toVec,neg_vec]

/-- Given a nondegenerate segment, the nondegenerate vector associated to the reversed nondegenerate segment is the negative of the nondegenerate vector associated to the nondegenerate segment. -/
@[simp]
theorem Seg_nd.tovec_nd_of_rev_eq_neg_tovec_nd {seg_nd : Seg_nd P} : seg_nd.reverse.toVec_nd = - seg_nd.toVec_nd := by
  apply Subtype.eq
  apply Seg.tovec_of_rev_eq_neg_tovec

/-- Given a nondegenerate segment, the direction of the reversed nondegenerate segment is the negative direction of the nondegenerate segment. -/
@[simp]
theorem Seg_nd.todir_of_rev_eq_neg_todir {seg_nd : Seg_nd P} : seg_nd.reverse.toDir = - seg_nd.toDir := by
  rw [toDir, toDir]
  simp only [tovec_nd_of_rev_eq_neg_tovec_nd, neg_todir_eq_todir_eq]

/-- Given a nondegenerate segment, the projective direction of the reversed nondegenerate segment is the same projective direction of the nondegenerate segment. -/
@[simp]
theorem Seg_nd.toproj_of_rev_eq_toproj {seg_nd : Seg_nd P} : seg_nd.reverse.toProj = seg_nd.toProj := by
  apply (Dir.eq_toproj_iff _ _).mpr
  simp only [tovec_nd_of_rev_eq_neg_tovec_nd, neg_todir_eq_todir_eq, or_true]

/-- The source of a ray lies on the reverse of the ray. -/
theorem Ray.source_lies_on_rev {ray : Ray P} : ray.source LiesOn ray.reverse := source_lies_on

/-- The source of a segment lies on the reverse of the segment. -/
theorem Seg.source_lies_on_rev {seg : Seg P} : seg.source LiesOn seg.reverse := target_lies_on

/-- The target of a segment lies on the reverse of the segment. -/
theorem Seg.target_lies_on_rev {seg : Seg P} : seg.target LiesOn seg.reverse := source_lies_on

/-- The source of a nondegenerate segment lies on the reverse of the segment. -/
theorem Seg_nd.source_lies_on_rev {seg_nd : Seg_nd P} : seg_nd.source LiesOn seg_nd.reverse := target_lies_on

/-- The target of a nondegenerate segment lies on the reverse of the segment.-/
theorem Seg_nd.target_lies_on_rev {seg_nd : Seg_nd P} : seg_nd.target LiesOn seg_nd.reverse := source_lies_on

/-- Given a ray, a point $X$ lies on the ray or its reverse if and only if $X$ lies on the reverse ray or the reverse of reverse ray. -/
theorem Ray.lies_on_rev_or_lies_on_iff {X : P} {ray : Ray P} : X LiesOn ray ∨ X LiesOn ray.reverse ↔ X LiesOn ray.reverse ∨ X LiesOn ray.reverse.reverse := by
  simp only [Ray.rev_rev_eq_self]
  exact ⟨ Or.symm, Or.symm ⟩

/-- If a point lies on a segment, then it lies on the reversed segment. -/
theorem Seg.lies_on_rev_of_lies_on {A : P} {seg : Seg P} : A LiesOn seg → A LiesOn seg.reverse := by
  unfold lies_on Fig.carrier instIntFigSeg
  simp only [Set.setOf_mem_eq]
  intro h
  rcases h with ⟨t, ⟨ h1, ⟨ h2, h3 ⟩⟩⟩
  use 1-t
  constructor
  · linarith
  · constructor
    · linarith
    · simp only [reverse]
      rw [(vec_add_vec seg.target seg.source A).symm, h3, ← neg_vec seg.target seg.source, sub_smul]
      rw [one_smul, smul_neg]
      ring

/-- A point lies on the reverse of a segment if and only if it lies on the segment. -/
@[simp]
theorem Seg.lies_on_rev_iff_lies_on {A : P} {seg : Seg P} : A LiesOn seg.reverse ↔ A LiesOn seg := ⟨ Seg.lies_on_rev_of_lies_on (seg := seg.reverse), Seg.lies_on_rev_of_lies_on ⟩


/-- A point lies in the interior of the reverse of a segment if and only if it lies in the interior of the segment. -/
@[simp]
theorem Seg.lies_int_rev_iff_lies_int {A : P} {seg : Seg P} : A LiesInt seg.reverse ↔ A LiesInt seg := by
  constructor
  rintro ⟨ha,⟨nonsource,nontarget⟩⟩
  exact ⟨Seg.lies_on_rev_iff_lies_on.mp ha,⟨nontarget,nonsource⟩⟩
  rintro ⟨ha,⟨nonrevsource,nonrevtarget⟩⟩
  exact ⟨Seg.lies_on_rev_iff_lies_on.mpr ha,⟨nonrevtarget,nonrevsource⟩⟩


/-- Given a nondegenerate segment, a point lies on the reverse of the segment if and only if it lies on the segment. -/
@[simp]
theorem Seg_nd.lies_on_rev_iff_lies_on {A : P} {seg_nd : Seg_nd P} : A LiesOn seg_nd.reverse ↔ A LiesOn seg_nd := seg_nd.1.lies_on_rev_iff_lies_on

/-- Given a nondegenerate segment, a point lies in the interior of the reverse of the segment if and only if it lies in the interior of the segment. -/
@[simp]
theorem Seg_nd.lies_int_rev_iff_lies_int {A : P} {seg_nd : Seg_nd P} : A LiesInt seg_nd.reverse ↔ A LiesInt seg_nd := seg_nd.1.lies_int_rev_iff_lies_int


/-- Given a ray, a point $A$ lies on the ray if and only if there exists a nonpositive real number $t$ such that the vector from the source of the ray to $A$ is $t$ times the direction vector of the ray. -/
theorem pt_lies_on_ray_rev_iff_vec_opposite_dir {A : P} {ray : Ray P} : A LiesOn ray.reverse ↔ ∃ t : ℝ, (t ≤ 0) ∧ VEC ray.source A = t • ray.toDir.toVec := by
  constructor
  · rintro ⟨u, ⟨_, h⟩⟩
    use -u
    rw [Ray.tovec_of_rev_eq_neg_tovec, Ray.source_of_rev_eq_source] at h
    constructor
    · linarith
    · simp only [h, smul_neg, Complex.real_smul, neg_smul]
  · rintro ⟨u, ⟨_, h⟩⟩
    use -u
    rw [Ray.tovec_of_rev_eq_neg_tovec, Ray.source_of_rev_eq_source]
    constructor
    · linarith
    · simp only [h, Complex.real_smul, smul_neg, neg_smul, neg_neg]


/-- A point $A$ lies on the lines determined by a ray $ray$ (i.e. lies on the ray or its reverse) if and only if the vector from the source of ray to $A$ is a real multiple of the direction vector of $ray$. -/
theorem pt_lies_on_line_from_ray_iff_vec_parallel {A : P} {ray : Ray P} : (A LiesOn ray ∨ A LiesOn ray.reverse) ↔ ∃t : ℝ, VEC ray.source A = t • ray.toDir.toVec := by
  constructor
  · rintro (⟨t, _, ha⟩ | ⟨t, _, ha⟩)
    · use t
    · use - t
      simp only [Ray.tovec_of_rev_eq_neg_tovec, smul_neg, ← neg_smul] at ha
      exact ha
  · rintro ⟨t, h⟩
    by_cases g : 0 ≤ t
    · exact .inl ⟨t, ⟨g, h⟩⟩
    · right
      use - t
      constructor
      · linarith
      · simp only [Ray.source_of_rev_eq_source, Ray.todir_of_rev_eq_neg_todir, Dir.tovec_neg_eq_neg_tovec, smul_neg, neg_smul, Complex.real_smul, neg_neg]
        exact h

/-- A point is equal to the source of a ray if and only if it lies on the ray and it lies on the reverse of the ray. -/
theorem Ray.eq_source_iff_lies_on_and_lies_on_rev {A : P} {ray : Ray P} : A = ray.source ↔ (A LiesOn ray) ∧ (A LiesOn ray.reverse) := by
  constructor
  intro h
  constructor
  use 0
  simp only [le_refl, zero_smul, true_and]
  rw[h,vec_same_eq_zero]
  use 0
  simp only [le_refl, Dir.tovec_neg_eq_neg_tovec, smul_neg, zero_smul, neg_zero, true_and,Ray.reverse]
  rw[h,vec_same_eq_zero]
  simp only [and_imp]
  rintro ⟨a,⟨anneg,h⟩⟩ ⟨b,⟨bnneg,h'⟩⟩
  simp only [Ray.reverse,Dir.tovec_neg_eq_neg_tovec, smul_neg,h] at h'
  rw[←add_zero a,← sub_self b,add_sub,sub_smul] at h'
  simp only [sub_eq_neg_self, mul_eq_zero] at h'
  have h'': a+b=0:=by
    contrapose! h'
    apply smul_ne_zero
    exact h'
    apply Dir.tovec_ne_zero
  have:a=0:=by
    linarith
  rw[this] at h
  simp only [zero_smul] at h
  rw[eq_iff_vec_eq_zero,h]

/-- If a point lies in the interior of the reverse of a ray, then it does not lie on the ray. -/
theorem Ray.not_lies_on_of_lies_int_rev {A : P} {ray : Ray P} (liesint : A LiesInt ray.reverse) : ¬ A LiesOn ray := by
  by_contra h
  rcases liesint with ⟨h',nsource⟩
  have: A LiesOn ray.reverse:=by
    apply h'
  have :A=ray.source:=by
    rw [Ray.eq_source_iff_lies_on_and_lies_on_rev]
    constructor
    exact h
    exact this
  trivial

/-- If a point lies on of the reverse of a ray, then it does not lie in the interior of the ray. -/
theorem Ray.not_lies_int_of_lies_on_rev {A : P} {ray : Ray P} (liesint : A LiesOn ray.reverse) : ¬ A LiesInt ray := by
  by_contra h
  rw [← Ray.rev_rev_eq_self (ray:=ray)] at h
  have : ¬ (A LiesOn ray.reverse) := by
    apply not_lies_on_of_lies_int_rev
    exact h
  trivial

/-- A point lies on a nondegenerate segment $AB$ if and only if it lies on the ray $AB$ and on the reverse ray $BA$. -/
theorem lies_on_iff_lies_on_toray_and_rev_toray {X : P} {seg_nd : Seg_nd P} : X LiesOn seg_nd.1 ↔ (X LiesOn seg_nd.toRay) ∧ (X LiesOn seg_nd.reverse.toRay) := by
  constructor
  intro liesonseg
  constructor
  apply Seg_nd.lies_on_toray_of_lies_on
  trivial
  apply Seg_nd.lies_on_toray_of_lies_on
  apply Seg.lies_on_rev_iff_lies_on.mp
  trivial
  rintro ⟨⟨a,anneg,h⟩,b,bnneg,h'⟩
  simp only [Seg_nd.toRay] at h h'
  rw [Seg_nd.todir_of_rev_eq_neg_todir,Dir.tovec_neg_eq_neg_tovec,smul_neg] at h'
  simp only [Seg_nd.reverse,Seg.reverse] at h'
  have asumbvec : (a + b) • seg_nd.toDir.toVec_nd.1 = seg_nd.toVec_nd.1 := by
    simp only [Seg_nd.toVec_nd, Dir.toVec_nd]
    rw[add_smul, ← h, ← vec_add_vec seg_nd.source X seg_nd.target, ← neg_vec seg_nd.target X, Seg_nd.source, Seg_nd.target, h', neg_neg]
  have asumbeqnorm : a + b = (Vec_nd.norm seg_nd.toVec_nd):=by
    rw [← Vec_nd.norm_smul_todir_eq_self seg_nd.toVec_nd] at asumbvec
    apply eq_of_smul_Vec_nd_eq_smul_Vec_nd asumbvec
  use a * (Vec_nd.norm seg_nd.toVec_nd)⁻¹
  have : VEC seg_nd.1.source seg_nd.1.target = seg_nd.toVec_nd:=by
    rfl
  constructor
  apply mul_nonneg anneg
  simp only [ne_eq, inv_nonneg]
  linarith
  constructor
  rw [← mul_inv_cancel (Vec_nd.norm_ne_zero seg_nd.toVec_nd)]
  apply mul_le_mul
  linarith
  trivial
  simp only[inv_nonneg]
  linarith
  linarith
  rw [h, mul_smul, this, ← Vec_nd.norm_smul_todir_eq_self seg_nd.toVec_nd, smul_smul, smul_smul, mul_assoc,inv_mul_cancel (Vec_nd.norm_ne_zero seg_nd.toVec_nd),mul_one]
  rfl

-- `This theorem really concerns about the total order on a line`
/-- Let $ray$ be a ray, and let $A$ be a point on $ray$, and $B$ a point on the reverse of $ray$. Then $A$ lies on the ray starting at $B$ in the same direction of $\ray$. -/
theorem lies_on_pt_todir_of_pt_lies_on_rev {A B : P} {ray : Ray P} (hA : A LiesOn ray) (hB : B LiesOn ray.reverse) : A LiesOn Ray.mk B ray.toDir := by
  rcases hA with ⟨a, anonneg, ha⟩
  rcases hB with ⟨b, bnonneg, hb⟩
  simp only [Dir.toVec,Ray.reverse, smul_neg] at hb
  use a + b
  constructor
  linarith
  simp only
  rw [add_smul, ← vec_sub_vec ray.source, ha, hb]
  simp only [Complex.real_smul, Dir.tovec_neg_eq_neg_tovec, smul_neg, sub_neg_eq_add]

/-- Given two rays $ray_1$ and $ray_2$ in same direction, the source of $ray_1$ lies on $ray_2$ if and only if the source of $ray_2$ lies on the reverse of $ray_1$. -/
theorem lies_on_iff_lies_on_rev_of_same_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = ray₂.toDir) : ray₁.source LiesOn ray₂ ↔ ray₂.source LiesOn ray₁.reverse := by
  constructor
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    simp only [Ray.source_of_rev_eq_source, Ray.todir_of_rev_eq_neg_todir,
      Dir.tovec_neg_eq_neg_tovec, smul_neg, h]
    rw [← eq]
    exact (neg_vec ray₂.source ray₁.source).symm
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    simp only [Ray.source_of_rev_eq_source, Ray.todir_of_rev_eq_neg_todir,
      Dir.tovec_neg_eq_neg_tovec, smul_neg] at eq
    rw [← neg_vec, h] at eq
    exact neg_inj.mp eq

/-- Given two rays $ray_1$ and $ray_2$ in same direction, the source of $ray_1$ lies in the interior of $ray_2$ if and only if the source of $ray_2$ lies in the interior of the reverse of $ray_1$. -/
theorem lies_int_iff_lies_int_rev_of_same_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = ray₂.toDir) : ray₁.source LiesInt ray₂ ↔ ray₂.source LiesInt ray₁.reverse := ⟨
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_rev_of_same_todir h).mp hl, ne.symm⟩,
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_rev_of_same_todir h).mpr hl, ne.symm⟩⟩

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies on $ray_2$ if and only if the source of $ray_2$ lies on $ray_1$. -/
theorem lies_on_iff_lies_on_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesOn ray₂ ↔ ray₂.source LiesOn ray₁ := by
  constructor
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    rw [h, Dir.tovec_neg_eq_neg_tovec, smul_neg, ← eq]
    exact (neg_vec ray₂.source ray₁.source).symm
  · intro ⟨t, ht, eq⟩
    refine' ⟨t, ht, _⟩
    rw [h, Dir.tovec_neg_eq_neg_tovec, smul_neg, ← neg_vec] at eq
    exact neg_inj.mp eq

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies in the interior of $ray_2$ if and only if the source of $ray_2$ lies in the interior of $ray_1$. -/
theorem lies_int_iff_lies_int_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesInt ray₂ ↔ ray₂.source LiesInt ray₁ := ⟨
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_of_neg_todir h).mp hl, ne.symm⟩,
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_iff_lies_on_of_neg_todir h).mpr hl, ne.symm⟩⟩

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies on the reverse of $ray_2$ if and only if the source of $ray_2$ lies on the reverse of $ray_1$. -/
theorem lies_on_rev_iff_lies_on_rev_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesOn ray₂.reverse ↔ ray₂.source LiesOn ray₁.reverse := by
  have h₁ : ray₁.reverse.toDir = - ray₂.reverse.toDir := by
    apply neg_eq_iff_eq_neg.mp
    simp only [Ray.todir_of_rev_eq_neg_todir, neg_neg, h]
  apply lies_on_iff_lies_on_of_neg_todir h₁

/-- Given two rays $ray_1$ and $ray_2$ in the opposite direction, the source of $ray_1$ lies in the interior of the reverse of $ray_2$ if and only if the source of $ray_2$ lies in the interior of the reverse of $ray_1$. -/
theorem lies_int_rev_iff_lies_int_rev_of_neg_todir {ray₁ ray₂ : Ray P} (h : ray₁.toDir = - ray₂.toDir) : ray₁.source LiesInt ray₂.reverse ↔ ray₂.source LiesInt ray₁.reverse := ⟨
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_rev_iff_lies_on_rev_of_neg_todir h).mp hl, ne.symm⟩,
  fun ⟨hl, ne⟩ ↦ ⟨(lies_on_rev_iff_lies_on_rev_of_neg_todir h).mpr hl, ne.symm⟩⟩

/-- Given a ray, a point $A$ lies on the ray or its reverse ray if and only if there exists a real number $t$ such that the vector from the source of the ray to $A$ is $t$ times the direction of the ray. -/
theorem lies_on_or_rev_iff_exist_real_vec_eq_smul {A : P} {ray : Ray P} : (A LiesOn ray ∨ A LiesOn ray.reverse) ↔ ∃ t : ℝ, VEC ray.source A = t • ray.2.1 := by
  constructor
  · intro h
    rcases h with ⟨t, _, eq⟩ | ⟨t, _, eq⟩
    · use t, eq
    · use - t
      simp only [Ray.source_of_rev_eq_source, Ray.todir_of_rev_eq_neg_todir,
        Dir.tovec_neg_eq_neg_tovec, smul_neg] at eq
      rw [← neg_smul] at eq
      exact eq
  · intro h
    choose t ht using h
    by_cases k : 0 ≤ t
    · exact .inl ⟨t,k,ht⟩
    have hu : VEC ray.reverse.1 A = (- t) • ray.reverse.2.1 := by
      simp only [Ray.source_of_rev_eq_source, Ray.todir_of_rev_eq_neg_todir,
        Dir.tovec_neg_eq_neg_tovec, smul_neg, neg_smul, Complex.real_smul, neg_neg]
      exact ht
    exact .inr ⟨- t, neg_nonneg.mpr (le_of_lt (not_le.mp k)), hu⟩

/-- Given two distinct points $A$ and $B$ and a ray, if both $A$ and $B$ lies on the ray or its reversed ray, then the projective direction of the ray is the same as the projective direction of the ray $AB$. -/
theorem ray_toproj_eq_mk_pt_pt_toproj {A B : P} {ray : Ray P} (h : B ≠ A) (ha : A LiesOn ray ∨ A LiesOn ray.reverse) (hb : B LiesOn ray ∨ B LiesOn ray.reverse) : ray.toProj = (RAY A B h).toProj := by
  rcases lies_on_or_rev_iff_exist_real_vec_eq_smul.mp ha with ⟨ta, eqa⟩
  rcases lies_on_or_rev_iff_exist_real_vec_eq_smul.mp hb with ⟨tb, eqb⟩
  have heq : VEC A B = (tb - ta) • ray.2.1 := by rw [← vec_sub_vec _ A B, eqa, eqb, sub_smul]
  calc
    _ = ray.2.toVec_nd.toProj := congrArg Dir.toProj (Dir.dir_tovec_nd_todir_eq_self ray.2).symm
    _ = _ := eq_toproj_of_smul ray.2.toVec_nd ⟨VEC A B, (vsub_ne_zero.mpr h)⟩ heq


end reverse


section extension

namespace Seg_nd

/-- Define the extension ray of a nondegenerate segment to be the ray whose origin is the target of the segment whose direction is the same as that of the segment. -/
@[pp_dot]
def extension (seg_nd : Seg_nd P) : Ray P where
  source := seg_nd.target
  toDir := seg_nd.toDir

/-- The extension of a nondegenerate segment is the same as first reverse the segment, then take the ray associated to the segment, and finally reverse the ray. -/
theorem extn_eq_rev_toray_rev {seg_nd : Seg_nd P} : seg_nd.extension = seg_nd.reverse.toRay.reverse := by
  ext : 1
  · rfl
  · simp only [Ray.todir_of_rev_eq_neg_todir, Seg_nd.toray_todir_eq_todir, Seg_nd.todir_of_rev_eq_neg_todir, neg_neg]
    rfl

/-- The extension of the reverse of a nondegenerate segment is the same as the reverse of the ray associated to the segment. -/
theorem rev_extn_eq_toray_rev {seg_nd : Seg_nd P} : seg_nd.reverse.extension = seg_nd.toRay.reverse :=
  seg_nd.reverse.extn_eq_rev_toray_rev

/-- The direction of the extension ray of a nondegenerate segment is the same as the direction of the segment. -/
@[simp]
theorem extn_todir {seg_nd : Seg_nd P} : seg_nd.extension.toDir = seg_nd.toDir := rfl

/-- The projective direction of the extension ray of a nondegenerate segment is the same as the projective direction of the segment. -/
@[simp]
theorem extn_toproj {seg_nd : Seg_nd P} : seg_nd.extension.toProj = seg_nd.toProj := rfl

/-- Given a nondegenerate segment, a point is equal to its target if and only if it lies on the segment and its extension ray. -/
theorem eq_target_iff_lies_on_lies_on_extn {A : P} {seg_nd : Seg_nd P} : (A LiesOn seg_nd) ∧ (A LiesOn seg_nd.extension) ↔ A = seg_nd.target := by
  constructor
  · intro ⟨ h1, h2 ⟩
    rw [extn_eq_rev_toray_rev] at h2
    rw [← Seg_nd.lies_on_rev_iff_lies_on] at h1
    exact Ray.eq_source_iff_lies_on_and_lies_on_rev.mpr ⟨ (Seg_nd.lies_on_toray_of_lies_on h1), h2 ⟩
  · intro h
    rw [h]
    exact ⟨Seg_nd.target_lies_on, Ray.source_lies_on⟩

/-- Given a nondegenerate segment $AB$, if a point $X$ belongs to the interior of the extension ray of $AB$, then $B$ lies in the interior of $AX$. -/
theorem target_lies_int_seg_source_pt_of_pt_lies_int_extn {X : P} {seg_nd : Seg_nd P} (liesint : X LiesInt seg_nd.extension) : seg_nd.target LiesInt SEG seg_nd.source X := by
  sorry
/- To come back to clean up this proof later.
  rcases liesint with ⟨⟨a,anonneg,ha⟩,nonsource⟩
  have raysourcesegtarget:seg_nd.1.target=seg_nd.extension.1:=by
    rfl
  have sourcetargetA:VEC seg_nd.1.source seg_nd.1.target+VEC seg_nd.1.target X=VEC seg_nd.1.source X:=by
    rw[vec_add_vec]
  have vec_ndtovec:VEC seg_nd.1.source seg_nd.1.target=seg_nd.toVec_nd.1:=by
    rfl
  have apos:0 < a:=by
    contrapose! nonsource
    have:a=0:=by linarith
    rw[this] at ha
    simp only [Dir.tovec_neg_eq_neg_tovec, smul_neg, zero_smul, neg_zero] at ha
    apply (eq_iff_vec_eq_zero _ _).mpr
    exact ha
  have raysourcesource:seg_nd.extension.source=seg_nd.1.target:=by
    rfl
  have seg_pos:0< Vec_nd.norm (Seg_nd.toVec_nd seg_nd):=by
    simp only [ne_eq, norm_of_Vec_nd_eq_norm_of_Vec_nd_fst,Vec.norm]
    apply norm_pos_iff.mpr (seg_nd.toVec_nd.2)
  have seg_nonzero:Vec_nd.norm (Seg_nd.toVec_nd seg_nd)≠0:=by linarith
  have aseg_pos:0 < Vec_nd.norm (Seg_nd.toVec_nd seg_nd)+a:=by
    linarith
  have aseg_nonzero:Vec_nd.norm (Seg_nd.toVec_nd seg_nd)+a≠ 0:=by
    linarith
  have raydir:seg_nd.extension.toDir.toVec=seg_nd.toVec_nd.toDir.toVec:=by
    rw[Ray.todir_of_rev_eq_neg_todir]
    rw[Ray.todir_of_rev_eq_neg_todir,←Seg_nd.todir_eq_toray_todir,Seg_nd.todir_of_rev_eq_neg_todir,neg_neg]
  constructor
  use (seg_nd.toVec_nd.norm)*(seg_nd.toVec_nd.norm+a)⁻¹
  constructor
  apply mul_nonneg
  linarith[seg_pos]
  norm_num
  rw[←norm_of_Vec_nd_eq_norm_of_Vec_nd_fst]
  linarith
  constructor
  rw[←mul_inv_cancel aseg_nonzero]
  apply mul_le_mul
  linarith
  linarith
  norm_num
  rw[← norm_of_Vec_nd_eq_norm_of_Vec_nd_fst]
  linarith
  linarith
  simp only [Seg.target]
  rw[←raysourcesegtarget] at ha
  rw[←sourcetargetA,ha,vec_ndtovec,←Vec_nd.norm_smul_todir_eq_self (seg_nd.toVec_nd),←norm_of_Vec_nd_eq_norm_of_Vec_nd_fst,raydir]
  rw[←add_smul,← mul_smul,mul_assoc,inv_mul_cancel,mul_one]
  linarith
  constructor
  exact seg_nd.2
  rw[←raysourcesegtarget] at nonsource
  symm
  exact nonsource
-/


/-- If a point lies on the ray associated to a segment, then either it lies on the segment or it lies on the extension ray of the segment. -/
theorem lies_on_seg_nd_or_extension_of_lies_on_toray {seg_nd : Seg_nd P} {A : P} (h : A LiesOn seg_nd.toRay) : A LiesOn seg_nd ∨ A LiesOn seg_nd.extension := by
  rcases h with ⟨t, tpos, eq⟩
  let v : Vec_nd := ⟨VEC seg_nd.1.1 seg_nd.1.2, (ne_iff_vec_ne_zero _ _).mp seg_nd.2⟩
  by_cases h : t > ‖v.1‖
  · refine' Or.inr ⟨t - ‖v.1‖, sub_nonneg.mpr (le_of_lt h), _⟩
    simp only [Seg_nd.toray_todir_eq_todir] at eq
    rw [sub_smul]
    simp only [Seg_nd.extn_todir]
    rw [← eq]
    refine' eq_sub_of_add_eq (add_eq_of_eq_sub' _)
    rw [vec_sub_vec']
    exact v.norm_smul_todir_eq_self
  · have eq : VEC seg_nd.1.1 A = t * v.toDir.1 := eq
    exact Or.inl ⟨t * ‖v.1‖⁻¹, mul_nonneg tpos (inv_nonneg.mpr (norm_nonneg v.1)),
      (mul_inv_le_iff (norm_pos_iff.2 v.2)).mpr (by rw [mul_one]; exact not_lt.mp h),
      by simpa only [eq, Vec_nd.toDir, ne_eq, Vec.norm, Complex.real_smul, Complex.ofReal_inv,
      Complex.norm_eq_abs, Complex.ofReal_mul] using by ring⟩

end Seg_nd

end extension

section length

/-- This function gives the length of a given segment, which is the norm of the vector associated to the segment. -/
@[pp_dot]
def Seg.length (seg : Seg P) : ℝ := norm (seg.toVec)

/-- This function defines the length of a nondegenerate segment, which is just the length of the segment. -/
@[pp_dot]
def Seg_nd.length (seg_nd : Seg_nd P) : ℝ := seg_nd.1.length

/-- Every segment has nonnegative length. -/
theorem length_nonneg {seg : Seg P} : 0 ≤ seg.length := norm_nonneg _

/-- A segment has positive length if and only if it is nondegenerate. -/
theorem length_pos_iff_nd {seg : Seg P} : 0 < seg.length ↔ seg.is_nd := norm_pos_iff.trans tovec_eq_zero_of_deg.symm.not

/-- The length of a given segment is nonzero if and only if the segment is nondegenerate. -/
theorem length_ne_zero_iff_nd {seg : Seg P} : 0 ≠ seg.length ↔ seg.is_nd :=
  (ne_iff_lt_iff_le.mpr (norm_nonneg _)).trans length_pos_iff_nd

/--  A nondegenerate segment has strictly positive length. -/
theorem length_pos {seg_nd : Seg_nd P} : 0 < seg_nd.length := length_pos_iff_nd.mpr seg_nd.2

/-- Given a segment, the square of its length is equal to the the inner product of the associated vector with itself. -/
theorem length_sq_eq_inner_tovec_tovec {seg : Seg P} : seg.length ^ 2 = inner seg.toVec seg.toVec :=
  (real_inner_self_eq_norm_sq (Seg.toVec seg)).symm

/-- The length of a segment is zero if and only if it is degenerate, i.e. it has same source and target. -/
theorem length_eq_zero_iff_deg {seg : Seg P} : seg.length = 0 ↔ (seg.target = seg.source) :=
  ((tovec_eq_zero_of_deg).trans norm_eq_zero.symm).symm


/-- Reversing a segment does not change its length. -/
@[simp]
theorem Seg.length_of_rev_eq_length {seg : Seg P} : seg.reverse.length = seg.length := by
  unfold Seg.length
  simp only [Complex.norm_eq_abs, Seg.tovec_of_rev_eq_neg_tovec, norm_neg]

/-- Reversing a segment does not change its length. -/
@[simp]
theorem Seg_nd.length_of_rev_eq_length {seg_nd : Seg_nd P} : seg_nd.reverse.length = seg_nd.length := by
  unfold Seg_nd.length
  simp only [rev_toseg_eq_toseg_rev, Seg.length_of_rev_eq_length]

/-- The length of segment $AB$ is the same as the length of segment $BA$. -/
theorem length_of_rev_eq_length' {A B : P} : (SEG B A).length = (SEG A B).length := by
  unfold Seg.length
  simp only [seg_tovec_eq_vec, Complex.norm_eq_abs]
  rw [← neg_vec]
  simp only [map_neg_eq_map]

/-- Given a segment and a point that lies on the segment, the additional point will separate the segment into two segments, whose lengths add up to the length of the original segment. -/
theorem length_eq_length_add_length {seg : Seg P} {A : P} (lieson : A LiesOn seg) : seg.length = (SEG seg.source A).length + (SEG A seg.target).length := by
  rcases lieson with ⟨t, ⟨a, b, c⟩⟩
  have h : VEC seg.source seg.target = VEC seg.source A + VEC A seg.target := by rw [vec_add_vec]
  have s : VEC A seg.target = (1 - t) • VEC seg.source seg.target := by
    rw [c] at h
    rw [sub_smul, one_smul]
    exact eq_sub_of_add_eq' h.symm
  rw [Seg.length, Seg.length, Seg.length, seg_tovec_eq_vec, seg_tovec_eq_vec, seg_tovec_eq_vec, c, s,
    norm_smul, norm_smul, ← add_mul, Real.norm_of_nonneg a, Real.norm_of_nonneg (sub_nonneg.mpr b)]
  linarith

end length

section midpoint

/-- Given a segment $AB$, this function returns the midpoint of $AB$, defined as moving from $A$ by the vector $\overrightarrow{AB}/2$. -/
@[pp_dot]
def Seg.midpoint (seg : Seg P): P := (1 / 2 : ℝ) • seg.toVec +ᵥ seg.source

@[pp_dot]
def Seg_nd.midpoint (seg_nd : Seg_nd P): P := seg_nd.1.midpoint

theorem Seg.vec_source_midpt {seg : Seg P} : VEC seg.1 seg.midpoint = 1 / 2 * VEC seg.1 seg.2 := by
  simp only [midpoint, one_div, Complex.real_smul, Complex.ofReal_inv, vec_of_pt_vadd_pt_eq_vec]
  rfl

/-- Given a segment $AB$, the vector from the midpoint of $AB$ to $B$ is half of the vector from $A$ to $B$-/
theorem Seg_nd.vec_source_midpt {seg_nd : Seg_nd P} : VEC seg_nd.source seg_nd.midpoint = 1 / 2 * VEC seg_nd.source seg_nd.target := by
  simp only [Seg_nd.midpoint]
  exact seg_nd.1.vec_source_midpt


theorem Seg.vec_midpt_target {seg : Seg P} : VEC seg.midpoint seg.2 = 1 / 2 * VEC seg.1 seg.2 := by
  rw [midpoint, ← vec_add_vec _ seg.1 _, ← neg_vec, vec_of_pt_vadd_pt_eq_vec]
  field_simp
  calc
    _ = VEC seg.1 seg.2 * (- 1) + VEC seg.1 seg.2 * 2 := by
      rw [mul_neg, mul_one]
      rfl
    _ = _ := by
      rw [← mul_add]
      norm_num

theorem Seg_nd.vec_midpt_target {seg_nd : Seg_nd P} : VEC seg_nd.midpoint seg_nd.target = 1 / 2 * VEC seg_nd.source seg_nd.target := by
  simp only [Seg_nd.midpoint]
  exact  seg_nd.1.vec_midpt_target


/-- Given a segment $AB$, the vector from $A$ to the midpoint of $AB$ is same as the vector from the midpoint of $AB$ to $B$ -/
theorem Seg.vec_midpt_eq {seg : Seg P} : VEC seg.1 seg.midpoint = VEC seg.midpoint seg.2 := by
  rw[seg.vec_source_midpt, seg.vec_midpt_target]

theorem Seg_nd.vec_midpt_eq {seg_nd : Seg_nd P} : VEC seg_nd.source seg_nd.midpoint = VEC seg_nd.midpoint seg_nd.target := by
  exact seg_nd.1.vec_midpt_eq

/-- Given a segment $AB$ and its midpoint P, the vector from $A$ to $P$ is same as the vector from $P$ to $B$ -/
theorem Seg.vec_eq_of_eq_midpt {seg : Seg P} (h : X = seg.midpoint) : VEC seg.1 X = VEC X seg.2 := by
  rw [h]
  exact seg.vec_midpt_eq

theorem Seg_nd.vec_eq_of_eq_midpt {seg_nd : Seg_nd P} (h : A = seg_nd.midpoint) : VEC seg_nd.source A = VEC A seg_nd.target := by
  exact seg_nd.1.vec_eq_of_eq_midpt h

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{AP}$ is half of vector $\overrightarrow{AB}$, P is the midpoint of $AB$  -/
theorem midpt_of_vector_from_source {seg : Seg P} (h : VEC seg.1 A = 1 / 2 * VEC seg.1 seg.2) :A = seg.midpoint := by
  rw [← start_vadd_vec_eq_end seg.1 A, h, Seg.midpoint, Complex.real_smul]
  norm_num
  rfl

theorem nd_midpt_of_vector_from_source {seg_nd : Seg_nd P} (h : VEC seg_nd.source A = 1 / 2 * VEC seg_nd.source seg_nd.target) :A = seg_nd.midpoint := by
  exact midpt_of_vector_from_source h

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{PB}$ is half of vector $\overrightarrow{AB}$, P is the midpoint of $AB$  -/
theorem midpt_of_vector_to_target {seg : Seg P} (h : VEC A seg.2 = 1 / 2 * VEC seg.1 seg.2) :A = seg.midpoint := by
  refine' midpt_of_vector_from_source _
  nth_rw 1 [eq_sub_of_add_eq (vec_add_vec seg.1 A seg.2), h, ← one_mul (VEC seg.1 seg.2), ← sub_mul]
  norm_num

theorem nd_midpt_of_vector_to_target {seg_nd : Seg_nd P} (h : VEC A seg_nd.target = 1 / 2 * VEC seg_nd.source seg_nd.target) :A = seg_nd.midpoint := by
  exact midpt_of_vector_to_target h

/-- Given a segment $AB$ and a point P, if vector $\overrightarrow{AP}$ is same as vector $\overrightarrow{PB}$, P is the midpoint of $AB$  -/
theorem midpt_of_same_vector_to_source_and_target {seg : Seg P} (h : VEC seg.1 A = VEC A seg.2) :A = seg.midpoint := by
  refine' midpt_of_vector_from_source _
  field_simp
  rw [mul_two, ← vec_add_vec seg.1 A seg.2]
  exact congrArg (HAdd.hAdd _) h

theorem midpt_of_same_vector_to_source_and_target_nd {seg_nd : Seg_nd P} (h : VEC seg_nd.source A = VEC A seg_nd.target) :A = seg_nd.midpoint := by
   exact midpt_of_same_vector_to_source_and_target h

/-- The midpoint of a segment lies on the segment. -/
theorem Seg.midpt_lies_on {seg : Seg P} : seg.midpoint LiesOn seg := ⟨1 / 2, by norm_num; exact seg.vec_source_midpt⟩

/-- The midpoint of a segment lies on the segment. -/
theorem Seg.lies_on_of_eq_midpt {seg : Seg P} (h : A = seg.midpoint) : A LiesOn seg := by
  rw [h]
  exact seg.midpt_lies_on

/-- The midpoint of a nondegenerate segment lies in the interior of the segment. -/
theorem Seg_nd.midpt_lies_int {seg_nd : Seg_nd P} :seg_nd.midpoint LiesInt seg_nd :=
  Seg.lies_int_iff.mpr ⟨seg_nd.2, ⟨1 / 2, by norm_num; exact seg_nd.vec_source_midpt⟩⟩

/-- The midpoint of a nondegenerate segment lies in the interior of the segment. -/
theorem Seg_nd.lies_int_of_eq_midpt {seg_nd : Seg_nd P} (h : A = seg_nd.midpoint) : A LiesInt seg_nd := by
  rw [h]
  exact seg_nd.midpt_lies_int

/-- A point $X$ on a given segment $AB$ is the midpoint if and only if the vector $\overrightarrow{AX}$ is the same as the vector $\overrightarrow{XB}$. -/
theorem midpt_iff_same_vector_to_source_and_target {X : P} {seg : Seg P} : X = seg.midpoint ↔ (SEG seg.source X).toVec = (SEG X seg.target).toVec :=
  ⟨fun h ↦ Seg.vec_eq_of_eq_midpt h, fun h ↦ midpt_of_same_vector_to_source_and_target h⟩

theorem Seg_nd.midpt_iff_same_vector_to_source_and_target {X : P} {seg_nd : Seg_nd P} : X = seg_nd.midpoint ↔ (SEG seg_nd.source X).toVec = (SEG X seg_nd.target).toVec :=
  ⟨fun h ↦ Seg.vec_eq_of_eq_midpt h, fun h ↦ midpt_of_same_vector_to_source_and_target h⟩

/-- The midpoint of a segment has same distance to the source and to the target of the segment. -/
theorem dist_target_eq_dist_source_of_midpt {seg : Seg P} : (SEG seg.source seg.midpoint).length = (SEG seg.midpoint seg.target).length := congrArg norm seg.vec_midpt_eq

/-- The midpoint of a segment has same distance to the source and to the target of the segment. -/
theorem dist_target_eq_dist_source_of_eq_midpt {X : P} {seg : Seg P} (h : X = seg.midpoint) : (SEG seg.1 X).length = (SEG X seg.2).length := by
  rw [h]
  exact dist_target_eq_dist_source_of_midpt

/-- A point $X$ is the midpoint of a segment $AB$ if and only if $X$ lies on $AB$ and $X$ has equal distance to $A$ and $B$. -/
theorem eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source {X : P} {seg : Seg P} : X = seg.midpoint ↔ (X LiesOn seg) ∧ (SEG seg.source X).length = (SEG X seg.target).length := by
  refine' ⟨fun h ↦ ⟨Seg.lies_on_of_eq_midpt h, dist_target_eq_dist_source_of_eq_midpt h⟩, _⟩
  intro ⟨⟨t, ht0, ht1, ht⟩, hv⟩
  have hv : ‖VEC seg.1 X‖ = ‖VEC X seg.2‖ := hv
  by_cases h0 : ‖VEC X seg.2‖ = 0
  · apply midpt_of_same_vector_to_source_and_target
    rw [h0] at hv
    rw [norm_eq_zero.mp h0, norm_eq_zero.mp hv]
  · have h := ht
    rw [← one_smul ℝ (VEC seg.1 X), ← vec_add_vec seg.1 X seg.2, smul_add, add_comm] at h
    have h := sub_eq_of_eq_add h
    rw [← sub_smul 1 t _] at h
    have h := congrArg norm h
    simp only [norm_smul, hv, Real.norm_of_nonneg ht0, Real.norm_of_nonneg (sub_nonneg.mpr ht1)] at h
    have h : t = 1 / 2 := by
      apply eq_one_div_of_mul_eq_one_left
      rw [mul_two]
      exact (eq_add_of_sub_eq (mul_right_cancel₀ h0 h)).symm
    exact midpt_of_vector_from_source (by rw [ht, h]; norm_num)

theorem Seg_nd_eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source {X : P} {seg_nd : Seg_nd P} : X = seg_nd.midpoint ↔ (X LiesOn seg_nd) ∧ (SEG seg_nd.source X).length = (SEG X seg_nd.target).length := by
  exact eq_midpoint_iff_in_seg_and_dist_target_eq_dist_source

end midpoint

section existence

/-- Given a segment $AB$, the midpoint of $A$ and $B + \overrightarrow{AB}$ is B  -/
theorem target_eq_vec_vadd_target_midpt {seg : Seg P} : seg.2 = (SEG seg.1 (seg.toVec +ᵥ seg.2)).midpoint :=
  midpt_of_same_vector_to_source_and_target (vadd_vsub seg.toVec seg.2).symm

theorem Seg_nd.target_eq_vec_vadd_target_midpt {seg_nd : Seg_nd P} : seg_nd.target = (SEG seg_nd.source (seg_nd.toVec_nd.1 +ᵥ seg_nd.target)).midpoint :=
  midpt_of_same_vector_to_source_and_target (vadd_vsub seg_nd.toVec_nd.1 seg_nd.target).symm

/-- Given a nondegenerate segment $AB$, B lies in the interior of the segment of $A(B + \overrightarrow{AB})$  -/
theorem Seg_nd.target_lies_int_seg_source_vec_vadd_target {seg_nd : Seg_nd P} : seg_nd.target LiesInt (SEG seg_nd.source (seg_nd.toVec_nd.1 +ᵥ seg_nd.target)) := by sorry


/-- Archimedean property I : given a directed segment AB (with A ≠ B), then there exists a point P such that B lies on the directed segment AP and P ≠ B. -/
theorem Seg_nd.exist_pt_beyond_pt (l : Seg_nd P) : (∃ q : P, l.target LiesInt (SEG l.source q)) :=
  ⟨l.1.toVec +ᵥ l.1.target, l.target_lies_int_seg_source_vec_vadd_target⟩

/-- Archimedean property II: On an nontrivial directed segment, one can always find a point in its interior.  `This will be moved to later disccusion about midpoint of a segment, as the midpoint is a point in the interior of a nontrivial segment`
    If a segment contains an interior point, then it is nondegenerate-/
theorem Seg.nd_of_exist_int_pt {X : P} {seg : Seg P} (h : X LiesInt seg) : seg.is_nd := by
  rcases h with ⟨⟨_, ⟨_, _, e⟩⟩, ⟨p_ne_s, _⟩⟩
  have t : VEC seg.source X ≠ 0 := (ne_iff_vec_ne_zero seg.source X).mp p_ne_s
  rw [e] at t
  exact Iff.mp vsub_ne_zero (right_ne_zero_of_smul t)

/-- A segment is nondegenerate if and only if it contains an interior point -/
theorem Seg.nd_iff_exist_int_pt {seg : Seg P} : (∃ (X : P), X LiesInt seg) ↔ seg.is_nd :=
  ⟨fun ⟨_, b⟩ ↦ nd_of_exist_int_pt b, fun h ↦ ⟨seg.midpoint, Seg_nd.midpt_lies_int (seg_nd :=⟨seg, h⟩)⟩⟩

/-- If a segment is nondegenerate, it contains an interior point -/
theorem Seg_nd.exist_int_pt {seg_nd : Seg_nd P} : ∃ (X : P), X LiesInt seg_nd := ⟨seg_nd.midpoint, midpt_lies_int⟩

/-- A segment contains an interior point if and only if its length is positive -/
theorem Seg.length_pos_iff_exist_int_pt {seg : Seg P} : 0 < seg.length ↔ (∃ (X : P), X LiesInt seg) :=
  length_pos_iff_nd.trans nd_iff_exist_int_pt.symm

theorem Seg_nd.length_pos_iff_exist_int_pt {seg_nd : Seg_nd P} : 0 < seg_nd.length ↔ (∃ (X : P), X LiesInt seg_nd) := by
  exact Seg.length_pos_iff_exist_int_pt

/-- A r ay contains two distinct points -/
theorem Ray.nontriv (ray : Ray P) : ∃ (A B : P), (A ∈ ray.carrier) ∧ (B ∈ ray.carrier) ∧ (B ≠ A) :=
  ⟨ray.1, (ray.2.toVec +ᵥ ray.1), source_lies_on,
  ⟨1 ,zero_le_one ,(vec_of_pt_vadd_pt_eq_vec ray.1 ray.2.toVec).trans (one_smul ℝ ray.2.toVec).symm⟩, by
  rw [ne_eq, vadd_eq_self_iff_vec_eq_zero]
  exact ray.2.tovec_ne_zero⟩

end existence

end EuclidGeom
