import YM.SU5.Obstruction.Support
import YM.SU5.Rotation.Plane
import YM.SU5.Macro.Layout
/-!
# Rotate the *actual support* of the mask (in `Home.Siam` units)

In `Early`, coord 0 flat. Time here 3 (match Skyline), so use rotation at (0,3).
Version applying to ANY such flat cell structure and paid resolution.
Adapt from two rotation proofs in verified release.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 7200
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.SatinRotation

open Function Filter MeasureTheory Metric
open Lattice SU Buffered Buffered.Afterglow Tapestry Satin
open Py Py.Rate LocalLimit Preparation Journey Vale
open Tapestry.Altitude
open Tower Tower.Selected Tower.Vacancy Tower.PhaseChoice Tower.Reconstruction
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder Classical
attribute [local instance] opCStarAlgebra
namespace Tilt
open Real (sin cos)
section R
open Matrix
def table (φ : ℝ) : Matrix Axis Axis ℝ :=
  !![Real.cos φ, 0, 0, -Real.sin φ;
     0, 1, 0, 0;
     0, 0, 1, 0;
     Real.sin φ, 0, 0, Real.cos φ]
lemma ok (φ : ℝ) : table φ ∈ Matrix.specialOrthogonalGroup Axis ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff]
  have h := Real.sin_sq_add_cos_sq φ
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [table, Matrix.mul_apply, Axis, Fin.sum_univ_succ] <;> nlinarith
  rw [det_succ_row (table φ) 2, Finset.sum_eq_single (2:Axis)]
  · rw [Matrix.det_fin_three]
    set c:= cos φ
    set s:= sin φ
    change (-1)^((2:ℕ)+2)* 1*(c*1*c- c*0*0-0*0*c+0*0*s+ -s*0*0- -s*1*s)=1
    norm_num; nlinarith
  · intro i _ hx; have he : table φ 2 i=0:=by fin_cases i <;> first|rfl|exact (hx rfl).elim
    rw [he]; ring
  simp
def tilt (φ : ℝ) : SO := ⟨table φ,ok φ⟩
lemma t_zero : tilt 0=1:= by
  apply Subtype.ext; ext i j; change table 0 i j=(1:Matrix Axis Axis ℝ) i j; fin_cases i <;> fin_cases j <;> simp [table]
lemma t_cont : Continuous tilt:=by
  apply Continuous.subtype_mk
  apply continuous_matrix; intro i j; fin_cases i <;> fin_cases j <;> simp [table] <;> fun_prop
lemma mixes {θ : ℝ}(h : θ ≠ 0) (p : |θ| < Real.pi / 2) : (tilt θ).val 3 0 ≠ 0 := _root_.YM.SU5Rotation.Plane.sin_ne h p
lemma proj (φ:ℝ)(x:Axis → ℝ) : cos φ * roll (tilt φ) x 0 + sin φ * roll (tilt φ) x 3=x 0 := by
  simp [roll,tilt,table,mulVec,dotProduct,Axis,Fin.sum_univ_succ]
  nlinarith [show (Real.sin φ ^ 2 + Real.cos φ ^ 2)*x 0=x 0 from by rw [Real.sin_sq_add_cos_sq];simp]
lemma inv (φ:ℝ)(x:RSpace): roll (tilt (-φ)) (roll (tilt φ) x)= x := by
  unfold roll
  rw [mulVec_mulVec,show (tilt (-φ)).val=(tilt φ).val.transpose from ?_,(Matrix.mem_orthogonalGroup_iff' ..).mp (Matrix.mem_specialOrthogonalGroup_iff.mp (tilt φ).property).1,one_mulVec]
  ext i j; change table (-φ) i j=table φ j i; fin_cases i <;> fin_cases j <;> simp [table]
end R

variable (Λ: Preparation)(l:ℕ)(n:ℕ)
local notation "r" t:max => (reserve Λ l : ℝ)*gaugeMesh Λ t
local notation "p" t:max x:max => gaugePosition Λ t x
private lemma scale {a b : ℕ} (h:a ≤ b) : (r b) ≤ r a := by
  have hp:0 < (Λ.R.L.val:ℝ):= by positivity
  unfold gaugeMesh; gcongr
  exact_mod_cast Λ.R.L.property

private lemma width_pos : 0 < (r n) := mul_pos (Nat.cast_pos.mpr (Nat.succ_pos _)) (gaugeMesh_pos _ n)

private lemma corner (θ:ℝ) (x: Cover) (i:ℕ):
    ∃ v∈stamp Λ l i x,∃ w∈stamp Λ l i x,
      cos θ*w 0+sin θ*w 3-(cos θ*v 0+sin θ*v 3)=2*(r i)*(cos θ+|sin θ|):= by
  -- extremal offsets (needed projection at orientations near zero)
  let a:= (r i); have ha:0≤a:= (width_pos Λ l i).le; let b:= if 0 ≤ sin θ then a else -a
  have hb: |b|=a:= by unfold b; split <;> simp [abs_of_nonneg ha]
  have hk: (sin θ)* b=|sin θ| * a:=by unfold b; split_ifs with h; rw [abs_of_nonneg h]; rw [abs_of_neg (lt_of_not_ge h),mul_neg,neg_mul]
  have uv(x₁ x₂:ℝ)(u:|x₁|≤a)(v:|x₂|≤a) : ∃ X∈stamp Λ l i x, X 0=(p i x) 0+x₁ ∧ X 3=(p i x) 3+x₂ := by
     let X(j:Axis) := (p i x) j+(if j=0 then x₁ else if j=3 then x₂ else 0)
     refine ⟨X,stamp_abs.mpr (fun j=> ?_),?_⟩; · unfold X; split_ifs <;> simp only [add_sub_cancel_left, abs_zero] <;> assumption
     simp [X,show (3:Axis) ≠ 0 by decide]
  obtain ⟨w,y,z,t⟩:= uv a b (le_of_eq (abs_of_nonneg ha)) hb.le
  obtain ⟨v,h,u,d⟩:= uv (-a) (-b) (by rw [abs_neg,abs_of_nonneg ha]) (by rw [abs_neg,hb])
  refine ⟨v,h,w,y,?_⟩; rw [z,u,t,d]; change _= 2*a*(cos θ+|sin θ|); linarith only [hk]

/-- Refuting core geometry in the arbitrary resolution $s$. -/
theorem no_fit {m:ℤ}{S: Finset Cover}(h:∀ x∈ S, x 0=m)(θ:ℝ)(hx: θ ≠ 0)(e:|θ| < Real.pi / 2) : ∃ W:Set RSpace, IsOpen W ∧ Bornology.IsBounded W ∧ footprint Λ l n S ⊆ W ∧ ∀ (i:ℕ),i≤ n → ∀ x:Cover, ¬ collar Λ l i x ⊆ roll (tilt θ) '' W:= by
  let f : Set RSpace:= footprint Λ l n S; let M:ℝ:=(m:ℝ)*gaugeMesh Λ n
  let Q:= (cos θ+|sin θ|); have hQ:1<Q:= _root_.YM.SU5Rotation.Plane.more_width hx e
  let B := {x : RSpace| |x 0-M| < (r n)*Q}
  have hB:IsOpen B:= isOpen_lt (((continuous_apply (0:Axis)).sub continuous_const).abs) continuous_const
  have sub : f ⊆ B:= by
    intro x p'; obtain ⟨u,hx,x'⟩:= silhouette_iff.mp ((Selection.Home.Siam.footprint_eq Λ n l S) ▸ (show x∈footprint Λ l n S from p'))
    have ht:= stamp_abs.mp x' 0
    rw [gaugePosition,h u hx] at ht; exact lt_of_le_of_lt ht (lt_mul_of_one_lt_right (width_pos Λ l n) hQ)
  obtain ⟨b,h⟩:= (footprint_compact Λ l n S).isBounded.subset_ball 0
  refine ⟨B∩ ball 0 b,hB.inter isOpen_ball,isBounded_ball.subset Set.inter_subset_right,(fun x h'=> ⟨sub h',h h'⟩),?_⟩
  intro i he x p₀; obtain ⟨v,u,w,h,K⟩:= corner Λ l θ x i
  rw [←Selection.Home.Siam.ball_eq] at p₀
  obtain ⟨v,y,rfl⟩:=p₀ u; obtain ⟨w,hb,rfl⟩:= p₀ h; rw [proj,proj] at K
  have H:= (abs_lt.mp (show  |v 0-M| < (r n)*Q from y.1)).1; have he:=scale Λ l he; have hB:= (abs_lt.mp (show  |w 0-M| < (r n)*Q from hb.1)).2
  change w 0-v 0=2*_ * Q at K; nlinarith

section motion
-- scope test: why not assert with fixed slack near zero within∪.
lemma fixed_slack (S:Finset Cover)(W:Set RSpace)(a:IsOpen W)(p':footprint Λ l n S ⊆ W) :
    ∀ᶠ θ:ℝ in 𝓝 0, footprint Λ l n S ⊆ roll (tilt θ) '' W:= by
  let f(x:ℝ×RSpace):= roll (tilt (-x.1)) x.2
  have hc:Continuous f:=(((continuous_subtype_val.comp t_cont).comp (continuous_fst.neg))).matrix_mulVec continuous_snd
  have he: ({0}:Set ℝ)×ˢ footprint Λ l n S ⊆ f ⁻¹' W:= by
    rintro ⟨θ,x⟩ ⟨(t : θ=0), hx⟩; subst θ; change f (0,x)∈ W; change roll _ x∈ W; simp only [neg_zero,t_zero]; rw [show roll 1 x=x from Matrix.one_mulVec x]; exact p' hx
  obtain ⟨U,O,u,w,p',p₀,h⟩:= generalized_tube_lemma isCompact_singleton (footprint_compact Λ l n S) (a.preimage hc) he
  filter_upwards [u.mem_nhds (p' (Set.mem_singleton _))] with θ zz x t
  exact ⟨f (θ,x), h (a:=(θ,x)) ⟨zz,p₀ t⟩,by unfold f; simpa only [neg_neg] using inv (-θ) x⟩
end motion
end Tilt
end YM.CF.SatinRotation

#print axioms YM.CF.SatinRotation.Tilt.no_fit
#print axioms YM.CF.SatinRotation.Tilt.fixed_slack
