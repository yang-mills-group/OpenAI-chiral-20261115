import YM.SU5.Selected.Cancellation.Algebra
/-!
# Even test reflections in distinct axes commute
Including at the registered planes of all observing rungs. Just opening the axis at the common
origin should suffice in using the cap algebra, but supply all shifts here. Signs crucial from
Gram completion on the even chiral CAR marks. This calculation does not equate θ with the star
of a bosonic lattice function (nor ignore the second-field arguments); we compare two θ's!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
open Mir.Trip
variable (i j : Axis) (p : i ≠ j) (x y : ℤ)

include p
private theorem keeps_step (k : ℤ) : (Signed.mirror i).act (k • step j : Cover) = k • step j := by
  funext a; by_cases h : a=i
  · subst a; simp [Signed.mirror,Signed.act,p]
  simp [Signed.mirror,Signed.act,h,Ne.symm h]
private theorem shape_cross : joinX (plane i x) (plane j y) = joinX (plane j y) (plane i x) := by
  unfold joinX plane
  have he : Signed.mirror i * Signed.mirror j = Signed.mirror j * Signed.mirror i := by
    refine Signed.ext rfl ?_; ext1 k; simp [Signed.mirror,Bool.xor_comm]; rfl
  dsimp only; rw [he, keeps_step i j p, keeps_step j i p.symm,add_comm]

private lemma fling_cross (n : Side) (t) : fling i x n (fling j y n t) = fling j y n (fling i x n t) := by
  unfold fling; rw [←kor,←kor,shape_cross i j p]

private lemma car_cross (n : Side) :
    (carR i x n).val * (carR j y n).val = -((carR j y n).val * (carR i x n).val) := by
  have hp : pin i * pin j = -(pin j * pin i) := by
    unfold pin; simp only [←mul_assoc]
    rw [mul_assoc (gammaOp i), gradingSwap, mul_neg, ←mul_assoc, neg_mul, gammaSwap i j p,
        neg_mul, neg_mul,neg_neg, mul_assoc (gammaOp j) grading, gradingSwap, mul_neg, neg_mul,
        neg_neg, mul_assoc]; simp only [mul_assoc]
  change (carR i x n * carR j y n).val = -(carR j y n * carR i x n).val
  unfold carR; rw [kio,kio,shape_cross i j p]
  have hz : (pinLift i * pinLift j).val = (-1:ℂ) • (pinLift j * pinLift i).val := by rw [neg_one_smul]; exact hp
  rw [Ygs _ _ _ hz, neg_one_smul]

-- like anti_mark in Buffered.Region but with the actual two-period test Theta.
omit p in
private lemma theta_order {κ : Type} [Fintype κ] [LinearOrder κ]
    (A B : UNI κ) (e : A.val*B.val = -(B.val*A.val))
    {b : Bool} {S : Finset κ} {x : FC κ} (v : Sector S b x) :
    theta A (theta B x) = (if b then (-1:ℂ) else 1) • theta B (theta A x) := by
  have he (A B : UNI κ) (x : Ket κ) : theta A (theta B (create x)) = -create (acts A.val (acts B.val x)) := by
    rw [theta_upV, theta_smul, theta_downV]; simp [smul_smul]
  have hu (x : Ket κ) : acts A.val (acts B.val x) = -acts B.val (acts A.val x) := by rw [←act_mul,←act_mul,e,act_neg]
  induction v with
  | zero=> simp only [theta_zero,smul_zero]
  | one=> rw [theta_one,theta_one,theta_one]; simp
  | up k _=> rw [←create_put,he,he,hu,map_neg]; simp
  | down k _=> rw [takeF,theta_star,theta_star,theta_star,theta_star,← create_put,he,he,hu,map_neg]; simp
  | add _ _ a b=> rw [theta_add,theta_add,theta_add,theta_add,a,b,smul_add]
  | scale _ z a=> rw [theta_smul,theta_smul,theta_smul,theta_smul,star_star,a,smul_comm]
  | @mul a b _ _ x y h p=> rw [theta_mul,theta_mul,theta_mul,theta_mul,h,p]; cases a <;> cases b <;> simp

theorem mirrors_commute {Z : Calibration} (F : Family Z) (h : TestFamily Z true F) :
    mirror Z i x (mirror Z j y F) = mirror Z j y (mirror Z i x F) := by
  funext n w
  let P := reflFields i x (reflFields j y w)
  have ht : reflFields j y (reflFields i x w)=P := Prod.ext ((fling_cross i j p x y _ w.1).symm) ((fling_cross i j p x y _ w.2).symm)
  change theta (carR i x _) (theta (carR j y _) (F n (reflFields j y _))) = theta _ (theta _ (F n P))
  obtain ⟨S,t⟩ := h.paid
  rw [ht, theta_order _ _ (car_cross i j p x y _) ((t.support n).allV P).sector, if_neg (by decide), one_smul]
end YM.CF.Buffered.Afterglow.Tower.Selection
