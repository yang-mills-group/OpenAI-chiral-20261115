import ExactRunning.Step.Wages

/-!
# Longitudinal slot

A lifted pure-gauge *tangent* (lift solves linearized high stationarity)
is invisible at zero field even in mixed `zEnergy` Hessian response
(testing in the other slot e.g. with coarse alone). Subtract the coarse
gauge tangent, itself invisible: this brings us to a tangent in high slots
alone, in the kernel of `thick`. By invertible completion this must be
pure fine gauge (and by translation properties on the torus the parameter
can still be taken translation-fixed, see `every_body`).
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree


lemma Latitude.preserves {D : Latitude} {m : Side} {G : Gauge}
    (x : BaseSites G m) : D.repeats (gradientA G m x) ↔ D.repeats x := by
  have hv (z : Site m) (t : Axis) (a) :
      gradientA G m x (z,coord t,a) = x (z+step t,vac,a)-x (z,vac,a) :=
    congrArg (fun b:G.Color=> b a) (gradientC x z t)
  constructor
  · intro h
    ext1 ⟨i,w,a⟩
    have hx : w=vac := vac_only w
    subst w
    let S := D.stepIV m
    let A i := x (i,vac,a)
    let F i := A (i+S)-A i
    have hu (z) : F (z+step 3)=F z := by
      have ht : gradientA G m x (z+S,coord 3,a) = gradientA G m x (z,coord 3,a) :=
        congr_fun (h : _ = _) (z,coord 3,a)
      rw [hv,hv,add_right_comm z] at ht
      unfold F A; linarith
    have ho (k:ℕ) : F (i + k•step 3)=F i := by
      induction k with
      | zero => simp
      | succ k ik => rw [succ_nsmul,← add_assoc,hu,ik]
    have hx (k:ℕ) : A (i+k•S)=A i+k*F i := by
      induction k with
      | zero => simp
      | succ k ik =>
        rw [Nat.cast_succ,add_mul,one_mul,← add_assoc,← ik,succ_nsmul,← add_assoc]
        have h1 : F (i+k•S)=F i := by
          rw [show k•S=k•(D.cycle.val • step 3) from rfl,← mul_smul, ho]
        rw [← h1]
        unfold F; abel
    have ht : m.val • S = 0 := by
      ext; rw [Pi.smul_apply,nsmul_eq_mul,ZMod.natCast_self];simp
    have ha := hx m.val
    rw [ht,add_zero, left_eq_add, mul_eq_zero] at ha
    exact sub_eq_zero.mp (ha.resolve_left (side_pos m).ne')
  intro h
  ext1 ⟨i,q,a⟩
  obtain ⟨t,rfl⟩ := axisEquiv.surjective q
  simp only [Function.comp_apply,D.shift_how,coord_map,hv]
  have hu (z:Site m) : x (z+D.stepIV m,vac,a) = x (z,vac,a) := congr_fun h (z,vac,a)
  rw [add_right_comm,hu,hu]

namespace BlockTie
variable {G : Gauge} {m : Side} {E I : Pylon G} (X : BlockTie E I)
variable {r : ℝ}
lemma sitting_zero :
    ContDiffAt ℝ ω (X.sitting (m:=m) 1 1) 0 :=
  (X.full_fare (Thaw.fixed _ (0:ℝ)) rfl (Army.park _ _)).self_of_nhds

lemma explosives_zero :
    Explosives (X.S m) (X.choice m) (G:=G) 1 1 :=
  (X.movers (Thaw.fixed _ (0:ℝ)) rfl).self_of_nhds

lemma every_body {y : Vault G m (X.up m)}
    (s : X.Stable (m:=m) 1 1) (p : IsUnit (X.high (m:=m) 1 1).det)
    (h : X.thick 1 1 *ᵥ cash (helmets _ _ _) y=0)
    (hk : (X.back r).repeats y.1) :
    ∃ a, (X.back r).repeats a ∧ y=corps (X.S m) 1 a := by
  let Y := cash (helmets G m (X.up m)) y
  let C:=X.restored (m:=m) 1
  let a := (C * stood (X.S m) 1)⁻¹ *ᵥ (C *ᵥ Y)
  have ha : IsUnit (C * stood (X.S m) 1).det := by
    dsimp only [C];rw [X.restored_stood X.explosives_zero]; exact fund_det (grenade_safe _ X.hμ)
  have hh : y=corps (X.S m) 1 a := by
    apply (cash (helmets G m _)).injective
    rw [← stands]
    apply mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det _).mpr p)
    simp only [high,Matrix.add_mulVec,h,zero_add,mulVec_mulVec]
    rw [Matrix.add_mul,(X.wort X.sitting_zero s).1, zero_add,
      Matrix.mul_assoc _ (X.restored _) (stood (X.S m) 1)]
    simp only [← mulVec_mulVec]
    have hA : (C * stood (X.S m) 1) *ᵥ a = C *ᵥ Y := by
      unfold a; rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ ha, one_mulVec]
    rw [mulVec_mulVec a,show (X.restored 1*stood (X.S m) 1) *ᵥ a = C *ᵥ Y from hA]
  refine ⟨a,((X.back r).preserves a).mp ?_,hh⟩
  rw [hh,(soldier_mounted _ _ _).1, show (1:Joint G m (X.up m)).1=(1:Config G (X.up m)) from rfl,cant_one] at hk
  exact neg_neg (gradientA G (X.up m) a) ▸ hk.neg

lemma optimize (s : X.Stable (m:=m) 1 1) (z : BaseSites G m) :
    X.thick 1 1 *ᵥ cash (helmets _ _ _) ((0,z):Vault G m (X.up m)) +
    X.spat 1 1 *ᵥ (-gradientA G m z) = 0 := by
  have hh : X.Fronds (fun w : BaseSites G m => (0,w))
      (fun w => moveField (w,0)) 1 1 := by
    have ht : ContDiffAt ℝ ω (fun w:BaseSites G m=> (w,(0:Link G m))) 0 := contDiffAt_id.prodMk contDiffAt_const
    refine ⟨contDiffAt_const.prodMk contDiffAt_id,rfl, moveField_analytic.contDiffAt.comp (f:=fun w=> (w,0)) (0:BaseSites G m) ht,
      moveField_zero, ?_⟩
    filter_upwards [ht.continuousAt.tendsto.eventually moveField_germ] with w hw
    simp only [mul_one,hw]
    have he : Stationary.extend ((0,w):Vault G m (X.up m)) = wages (X.S m) 1 (switchSite w) 1 := by
      ext <;> simp [Stationary.extend,wages,gauge_one]
    rw [he, shiftLinks,input_zero]
    exact Shell.wage X.branches E.paths s 1 _
  have hx := X.fronds_bend X.sitting_zero hh z; dsimp only at hx
  have hi : HasFDerivAt (fun w=>moveField (w,0)) _ (0:BaseSites G m) := 
    ((moveField_analytic (G:=G)).differentiableAt.hasFDerivAt.comp (f:=fun w=>(w,0)) _
      ((hasFDerivAt_id _).prodMk (hasFDerivAt_const ..)))
  have hr : HasFDerivAt (fun w=>((0,w):Vault G m (X.up m))) _ (0:BaseSites G m) :=
    (hasFDerivAt_const ..).prodMk (hasFDerivAt_id (𝕜:=ℝ) _)
  rw [hr.fderiv,hi.fderiv,ContinuousLinearMap.comp_apply, moveField_rate] at hx
  simpa using hx

theorem thrust (s : X.Stable (m:=m) 1 1) (p : IsUnit (X.high (m:=m) 1 1).det)
    (hh : X.ZSafe m r)
    (x : BaseSites G m) (h : (ridge r).repeats x)
    (y : Vault G m (X.up m)) (hy : (X.back r).repeats y.1)
    (ht : X.thick 1 1 *ᵥ cash (helmets _ _ _) y + X.spat 1 1 *ᵥ gradientA G m x=0) :
    Vanishes (X.zEnergy r) (gradientA G m x,y) := by
  have hu : X.thick 1 1 *ᵥ cash (helmets _ _ _) (y+(0,x))=0 := by
    have hv := X.optimize s x
    rw [mulVec_neg, ← sub_eq_add_neg, sub_eq_zero] at hv
    rw [map_add,mulVec_add,hv,ht]
  obtain ⟨a,ha,hg⟩ := X.every_body (r:=r) s p hu (by simpa using hy)
  convert! Vanishes.sub (X.z_fine hh ha) (X.z_coarse hh h)
  all_goals rw [←hg]; simp

end BlockTie
end ExactRunning
