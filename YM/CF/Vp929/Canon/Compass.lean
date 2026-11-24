import YM.CF.Vp929.Canon.Reel
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.flexible false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Taxi RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
namespace Test
open Push Exterior
set_option quotPrecheck false
variable {n L:Side}{q:ℝ} (h:Frequency L n q)
local notation "Bμ" => (More n).val
local notation "V'"=> Skye.Seat n
include h
lemma sinStep (x:V')(d:ℝ) : Real.sin (rtape q (x+Lattice.step 0)+d)= Real.sin (rtape q x+q+d):=by
 let k:Site (More n):= x+Lattice.step 0; have he:wrap (More n) (lift k)=wrap (More n) (lift x+Lattice.step 0):=by simp [k]
 convert sin_relay h (lift k) (lift x+Lattice.step 0) he d using 2; unfold rtape; simp [mul_add]
lemma cosStep (x:V')(d:ℝ) : Real.cos (rtape q (x+Lattice.step 0)+d)=Real.cos (rtape q x+q+d):=by
 have hv:=sinStep h x (d+Real.pi/2); rwa [←add_assoc,Real.sin_add_pi_div_two,←add_assoc (rtape q x+q),Real.sin_add_pi_div_two] at hv
private lemma tinyQ : q≤1:=h.small.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
private lemma together (x:V')(d:ℝ): Real.cos (2*(rtape q (x+Lattice.step 0)+d))=Real.cos (2*(rtape q x+q+d)):=by simp only [Real.cos_two_mul, cosStep h]
lemma choir_q (d:ℝ): ∑ x:V', Real.cos (2*(rtape q x+d))=0:=by
 let A(z:ℝ)(x:V'):= Real.cos (2*(rtape q x + z)); let f(a:ℝ):=∑ x:V',A a x; have hx(z:ℝ): f z=f (z+q):=by
    refine (show f z=∑ i:V',A z (i+Lattice.step 0) from (Equiv.sum_comp (Equiv.addRight ((Lattice.step 0):V')) (A z)).symm).trans ?_; exact sum_congr rfl (fun i _=> (together h i z).trans (show Real.cos (2*(rtape q i+q+z))=Real.cos (2*(rtape q i+(z+q))) by rw [add_comm z q, add_assoc (rtape q i)]))
 have he:= h.pos; have hq:= tinyQ h; have hg:Real.sin q≠0:= (Real.sin_pos_of_pos_of_lt_pi he (by linarith [Real.pi_gt_three])).ne'; have hc:Real.cos (2*q) ≠ 1:=by rw [Real.cos_two_mul']; intro h; apply hg; nlinarith [Real.sin_sq_add_cos_sq q]
 have ht: f (d+q)+f (d-q)= f d * (2*Real.cos (2*q)):=by
    unfold f; rw [←sum_add_distrib,sum_mul]; refine sum_congr rfl fun i _=>?_ ; unfold A; let a:=rtape q i
    show Real.cos (2*(a+_))+Real.cos (2*(a+_))=_; rw [show 2*(a+(d+q))=2*(a+d)+2*q by ring,show 2*(a+(d-q))=2*(a+d)-2*q by ring,Real.cos_add,Real.cos_sub]; unfold a; ring
 rw [hx (d-q),sub_add_cancel,← hx d] at ht; change f d=0; by_contra h; apply hc; apply mul_left_cancel₀ h; linarith
lemma q_sinh : 1/2 ≤ 2*Real.sin (q/2)/q:=by
 let u:= h.pos; have e:=tinyQ h; have p:=Real.pi_gt_three; have hp := Real.pi_lt_four; have ht:0<q/2:=half_pos u; have hz:=Real.sin_pos_of_pos_of_lt_pi ht (by linarith); have hv:= Real.mul_abs_le_abs_sin (x:=q/2) (by rw [abs_of_pos ht]; linarith); rw [abs_of_pos hz, abs_of_pos ht] at hv; apply (le_div_iff₀ u).2; have H:1/2 ≤ 2/Real.pi:= (le_div_iff₀ Real.pi_pos).2 (by linarith); nlinarith
lemma blade_face (x:V'): blade q (x+Lattice.step 0)-blade q x=2*Real.sin (q/2)/q*Real.cos (rtape q x+q/2):=by
 obtain hv:= sinStep h x 0; simp only [add_zero] at hv; unfold blade; rw [hv,←sub_div, Real.sin_sub_sin]; let d:= rtape q x; change _= _*Real.cos (d+q/2);
 unfold d; ring_nf
lemma cosineQ :∑ x:V', Real.cos (rtape q x+q/2)^2=sites n/2:=by
 have ht:= choir_q h (q/2); simp_rw [Real.cos_two_mul] at ht; rw [sum_sub_distrib,←mul_sum, sum_const, card_univ,nsmul_eq_mul,site_card,mul_one,Nat.cast_pow] at ht; unfold sites; linarith
end Test
end YM.CF.Py.Rate
