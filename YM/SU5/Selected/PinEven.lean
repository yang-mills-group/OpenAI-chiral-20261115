import YM.SU5.Selected.Addition

/-! Pin signs comparing the involutions. For even marks with projected
adjoints. Tiny Vos argument paying the actual period `More`, before using
resolution transfer. `swaps_pin` and the Fock sign proof similar to the local
arguments on the different GridM in `Buffered/Flips`. -/
set_option autoImplicit false
set_option synthInstance.maxSize 30000
set_option maxRecDepth 6000
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.PhaseChoice
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark Vacancy SatinVerification
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
  (V:Universal Y H i k I E)
  (G:GroundExtension (i:=i) (k:=k) (E:=E) Y H)
variable (j : Axis) (strict : Bool) (C : Arena Y H G.history.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H G.history.circuit j 0 strict C
local notation "Fₛ" i:max=>Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s G.history.circuit j 0 strict C
local notation "ω"=>floorV Y H G.history.circuit j 0 strict C
local notation "Γ"=>Aurora Y H V G.history j strict C
local notation "Ω"=>seat0 Y H V G.history j strict C
local notation "ι₀"=> (Γ).subtypeL
local notation "π"=> (Γ).orthogonalProjectionOnto
local notation "B" s:max f:max h:max=>boxOp Y H V s G.history G.clipped j strict C _ f h
local notation "P" s:max=>cap Y H V s G.history G.clipped j strict C
open Tenant Mir.Trip Branch
section
variable (d : Axis)
private lemma swaps_pin (p:j≠d) : pin j*pin d = -(pin d*pin j) := by
  unfold pin; simp only [←mul_assoc]
  rw [mul_assoc (gammaOp j), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap j d p, neg_mul,
    neg_mul,neg_neg, mul_assoc (gammaOp d) grading, gradingSwap, mul_neg, neg_mul, neg_neg, mul_assoc]
  simp only [mul_assoc]

private lemma planes : joinX (plane j 0) (plane d 0)=joinX (plane d 0) (plane j 0) := by
  unfold joinX plane; dsimp only; simp only [zero_smul, add_zero]
  congr 1
  · exact Signed.ext rfl (by funext i; simp [Signed.mirror,Bool.xor_comm] <;> rfl)
  funext i; simp [Signed.act]

private lemma packs_swap (n : Side) (p:j≠d) :
    (carR j 0 n).val * (carR d 0 n).val = -((carR d 0 n).val * (carR j 0 n).val) := by
  have ht : (pinLift j * pinLift d).val = (-1:ℂ) • (pinLift d * pinLift j).val := by
    rw [neg_one_smul]; exact swaps_pin j d p
  change (carR j 0 n * carR d 0 n).val = -(carR d 0 n * carR j 0 n).val
  unfold carR; rw [kio,kio,planes d j,Ygs _ _ _ ht,neg_one_smul]

private lemma pin_sign (p:j≠d) {n:Side} {S:Finset (Single n)}{b:Bool}{x:FC (Single n)}(v:Sector S b x) :
    theta (carR j 0 n) (theta (carR d 0 n) x) =
    (if b then (-1:ℂ) else 1) • theta (carR d 0 n) (theta (carR j 0 n) x) := by
  have he(a b:Axis)(x:Ket (Single n)): theta (carR a 0 n) (theta (carR b 0 n) (create x))=
      -create (acts ((carR a 0 n).val*(carR b 0 n).val) x):= by
    rw [theta_upV,theta_smul,theta_downV,←act_mul]; simp [smul_smul]
  induction v with
  | zero=> simp only [theta_zero,smul_zero]
  | one=> rw [theta_one,theta_one,theta_one]; simp
  | up k _=> rw [←create_put,he,he,packs_swap j d n p,act_neg,map_neg]; simp
  | down k _=> rw [takeF,theta_star,theta_star,theta_star,theta_star,←create_put,he,he,packs_swap j d n p,act_neg,map_neg]; simp
  | add _ _ h i=> rw [theta_add,theta_add,theta_add,theta_add,h,i,smul_add]
  | scale _ z p=>rw [theta_smul,theta_smul,theta_smul,theta_smul,star_star,p,smul_comm]
  | @mul a b _ _ x y h p=> rw [theta_mul,theta_mul,theta_mul,theta_mul,h,p]; cases a <;> cases b <;> simp

private lemma flings (n:Side)(x:Pane n): fling j 0 n (fling d 0 n x) = fling d 0 n (fling j 0 n x) := by
  unfold fling; rw [← kor,←kor,planes d j]

lemma mirror_switch (Z:Calibration) {f:Family Z}(h:TestFamily Z true f) :
    mirror Z j 0 (mirror Z d 0 f) = mirror Z d 0 (mirror Z j 0 f) := by
  by_cases p:j=d
  · rw [p]
  funext n x
  change theta _ (theta _ (f n (fling d 0 _ (fling j 0 _ _),fling d 0 _ (fling j 0 _ _)))) =
    theta _ (theta _ (f n (fling j 0 _ (fling d 0 _ _),fling j 0 _ (fling d 0 _ _))))
  rw [flings j d,flings j d, pin_sign j d p (((h.paid.choose_spec.support n).allV _).sector), if_neg (by decide), one_smul]
end

-- Make the subtractions explicitly within cap domains.
section
variable {J: Calibration} (X Y' : observable J strict)
noncomputable def twiceNeg : observable J strict := ⟨(-1:ℂ) • X.val, X.property.1.scale _,
    fun h => covariant_scale _ (X.property.2 h) _⟩
noncomputable def subtractMark : observable J strict := ⟨X.val+ (twiceNeg strict Y').val,
    X.property.1.add (twiceNeg strict Y').property.1, fun h =>
      (covariant_parts _ (X.property.2 h) ((twiceNeg strict Y').property.2 h)).1⟩
lemma subtractMark_val : (subtractMark strict X Y').val = X.val-Y'.val := by
  rw [sub_eq_add_neg,←neg_one_smul ℂ Y'.val]; rfl
end

variable (d : Axis) (C' : Arena Y H G.history.circuit d 0 strict)
local notation "P'" t:max=> cap Y H V t G.history G.clipped d strict C'
local notation "Ω'"=> seat0 Y H V G.history d strict C'
local notation "D'"=>dual Y H d strict
local notation "D"=>dual Y H j strict

lemma cap_subtract (s:ℕ) (x y:observable K strict) :
    (P s) (subtractMark strict x y)=(P s) x-(P s) y := by
  rw [cap_add Y H V G j strict C s _ x (twiceNeg strict y) rfl,
      cap_scale Y H V G j strict C s (twiceNeg strict y) y (-1) rfl,neg_one_smul ℂ ((P s) y)]
  exact (sub_eq_add_neg ..).symm

include C' in
lemma oppositeStar (s:ℕ) (x:observable K strict) : (P s) (D' x)=(P s) (D x) := by
  by_cases p:j=d
  · cases p; rfl
  let y := subtractMark strict (D' x) (D x)
  have hy : (D' y).val = (-1:ℂ) • (D y).val := by
    change mirror K d 0 y.val = (-1:ℂ) • mirror K j 0 y.val
    unfold y subtractMark twiceNeg; dsimp only
    rw [mirror_plus,mirror_scale,mirror_plus,mirror_scale]
    change mirror K d 0 (mirror K d 0 x.val) + _ • mirror K d 0 (mirror K j 0 x.val) =
      (-1:ℂ) • (mirror K j 0 (mirror K d 0 x.val) + _ • mirror K j 0 (mirror K j 0 x.val))
    rw [mirror_switch d j K x.property.1,mirror_invert K d 0 x.property.1,mirror_invert K j 0 x.property.1]
    -- simplify negative
    simp [add_comm]
  let T := (P s) y; let T' := (P' s) y
  let v := T Ω; let v' := T' Ω'
  have h0 := between_axes Y H V G.history G.clipped j strict C ![(s,D y),(s,y)] d C' p [0,1] [0,1] (by decide) (.refl ..)
  change inner ℂ Ω (((P s) (D y)) v) = inner ℂ Ω' (((P' s) (D y)) v') at h0
  have hp:(P' s) (D y) = -ContinuousLinearMap.adjoint T' := by
    unfold T'
    rw [mirror_cap, cap_scale Y H V G d strict C' s _ _ (-1) hy,neg_one_smul ℂ ((P' s) (D y)),neg_neg]
  rw [← mirror_cap,hp,ContinuousLinearMap.adjoint_inner_right] at h0
  change inner ℂ v v = inner ℂ Ω' (-(T'.adjoint v')) at h0
  rw [inner_neg_right,ContinuousLinearMap.adjoint_inner_right] at h0
  have h₁ : v=0 := (re_inner_self_nonpos (𝕜:=ℂ)).mp (by
    change (inner ℂ v v).re ≤ 0; rw [h0]; exact neg_nonpos.mpr (show 0 ≤ (inner ℂ v' v').re from inner_self_nonneg (𝕜:=ℂ)))
  apply sub_eq_zero.mp
  rw [←cap_subtract]
  exact faithful_of_commute Y H V G j strict C T (fun v=> commutes Y H V G j strict C (s,y) v) h₁

end YM.CF.Buffered.Afterglow.Tower.PhaseChoice
#print axioms YM.CF.Buffered.Afterglow.Tower.PhaseChoice.oppositeStar
