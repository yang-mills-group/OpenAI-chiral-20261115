import YM.CF.Ups.Tot
import YM.CF.Continuum.Uniform
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade.Earn
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
open Next.Rank
variable {c f:Side}(S:StepData c f)(J:ChartRatio SU.group)
local notation "G5"=>SU.group
local notation "ζ"=> Fintype.card
local notation "dG"=> SU.group.lieDim
local notation "βt"=> Window.strengthLog
abbrev roomSite (N:Side) : ℝ:= Fintype.card (Site N)
private lemma countTreasures(F:Tree.Forest S.ratio): ζ F.Free=3* ζ (Site f)+ ζ (Site c):=by
 have ht:= SectorNext.Vacuum.FlatTree.count_clear F; rw [Fintype.card_prod _ Axis] at ht; have hp:ζ Axis=4:=rfl; rw [hp] at ht; omega
include S in
lemma builtLe : roomSite c≤roomSite f:=by
 apply Nat.cast_le.mpr; rw [site_card,site_card]; gcongr; rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property
private def largePot (O:HaarBudget SU.group)(K:KernelChoices):= Real.exp K.penalty * O.big*(2 / K.penalty)^SU.group.lieDim
lemma largePot_pos (O:HaarBudget G5)(K:KernelChoices) :0<largePot O K:=by unfold largePot; have hp:= K.penalty_pos; have ht:=zero_lt_one.trans_le O.big_ge; positivity
private lemma unit_noise (O:HaarBudget G5)(y β:ℝ)(v:0<y)(h:y/2 ≤ β): S.penaltyZ β G5 ≤ largePot O S.kernel*(coupling y)^SU.group.lieDim:=by
 let p:= S.kernel.penalty; have hp : 0<p:= S.kernel.penalty_pos; let C:=Real.sqrt y; let t:=(2/p)*coupling y; have he:0<C:=Real.sqrt_pos.mpr v; have hh:0<t:=mul_pos (by positivity) (coupling_pos v); let W(x:SU.group.El):= Real.exp p*Real.exp (-(SU.group.chord x/t)); have hx:Continuous W:= by unfold W; fun_prop
 apply le_trans (b:=∫ x, W x ∂ SU.group.probHaar); swap
 · rw [integral_const_mul]; exact (mul_le_mul_of_nonneg_left (O.high t hh) (Real.exp_pos _).le).trans_eq (by unfold t largePot p; rw [mul_pow]; ring)
 refine integral_mono ((S.penaltyWeight_cont (G:=G5) β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun u=>?_
 unfold W; rw [←Real.exp_add]; refine Real.exp_monotone ?_; let d:=SU.group.chord u; have he: d/t = p*(C*d)/2:=by unfold t coupling C d; field_simp -- positivity d not needed he
 change -β*p*SU.group.price u≤p+ -(d/t); rw [he,show SU.group.price u=d^2/2 by unfold d; rw [SU.group.chord_price]; ring]; calc
    _ ≤ -(y/2)*p*(d^2/2) := by gcongr
    _ ≤ _ := by rw [show y=C^2 from (Real.sq_sqrt v.le).symm]; nlinarith only [mul_nonneg hp.le (sq_nonneg (C*d-1)), hp]
-- last nlinarith instead rewrite y→C²
private def lowPot(J:ChartRatio G5):= point SU.group 1*(J.scale*(Real.sqrt (2*Real.pi)/2)^SU.group.lieDim)
lemma lowPot_pos(hx:LocalRatio J): 0<lowPot J:=by unfold lowPot; have h':=hx.scale; have ht:0 < point SU.group 1:= point_p (by norm_num); positivity
private lemma unit_forest (hJ:LocalRatio J)(β R y:ℝ)(p:1≤R)(hq:0<y)(q:0<β)(s:β≤2*y): lowPot J*(coupling y)^SU.group.lieDim ≤ shotM J R β :=by
 let d:=Real.sqrt (2*Real.pi); have hx:0<d:= Real.sqrt_pos.mpr (by positivity); let W:=coupling β; have ht:0<W:=coupling_pos q; have hu:coupling y/2 ≤ W:=by
    change (Real.sqrt y)⁻¹/2 ≤ (Real.sqrt β)⁻¹; rw [show (Real.sqrt y)⁻¹/2=(2* Real.sqrt y)⁻¹ by rw [mul_inv_rev]; ring]; refine inv_anti₀ (Real.sqrt_pos.mpr q) (Real.sqrt_le_left (by positivity)|>.mpr ?_); rw [mul_pow,Real.sq_sqrt hq.le]; linarith
 let l:=point G5 1; have hp:l ≤ point G5 R:= ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (closedBall_subset_closedBall p)); have hl:0<l:= point_p (by norm_num); let a:= J.scale; have hJ: 0<a:=hJ.scale
 have hi:spare J β=(d*W)^dG*a:=by unfold spare; rw [Real.sqrt_mul (by positivity),Real.sqrt_sq ht.le]; simp only [Gauge.ColorIndex,Fintype.card_fin]; rfl
 unfold lowPot shotM; rw [hi]; calc
    _ = (d*(coupling y/2))^dG*a*l := by unfold d l a; rw [show Real.sqrt (2*Real.pi)*(coupling y/2)=Real.sqrt (2*Real.pi)/2*coupling y by ring,mul_pow]; ring
    _ ≤ _:=by have he:=coupling_pos hq; gcongr
open Next.Fluctuations.Sector
abbrev pathFees (S K:Side)(T:ℝ)(Z:ℝ):ℝ:=3*(roomSite K-roomSite S)*βt (coupling T) -Z*roomSite K
section receipts
variable {y β:ℝ} (v:0<y)(b:y/2≤β)(q:β≤2*y)
include v b
lemma powerOut (K0:KernelChoices)(O:HaarBudget G5)(h:S.kernel=K0): Real.exp (-(ζ (Bond c):ℝ) * (βt (coupling y)+ Real.log (largePot O K0)))≤ prefactor S G5 β :=by
 let p:= ζ (Bond c); let P:= largePot O K0; have ht:=largePot_pos O K0; have hx:0 < (coupling y):=coupling_pos v
 let w:=P * coupling y^dG; have hl:w=Real.exp (βt (coupling y)+Real.log P):=by
    rw [Window.strengthLog,←Real.log_pow,Real.exp_add,Real.exp_log (pow_pos hx _),Real.exp_log ht]; exact mul_comm ..
 have he: S.penaltyZ β G5≤ w:= by unfold w P; rw [←h]; exact unit_noise S O y β v b
 refine le_trans ?_ (pow_le_pow_left₀ (inv_nonneg.mpr ((S.penaltyZ_pos β).le.trans he)) (inv_anti₀ (S.penaltyZ_pos β) he) p)
 unfold p; rw [hl, inv_pow,←Real.exp_nat_mul, ←Real.exp_neg]; apply le_of_eq; unfold P; congr 1; ring -- tune
include q
lemma powerIn (K:Forest S.ratio)(hJ:LocalRatio J)(H:ℝ)(p:1 ≤ H):
 Real.exp (ζ K.Free*(βt (coupling y)+ Real.log (lowPot J))) ≤ (shotM J H β)^ζ K.Free := by
 let p':= half_pos v; let a:=lowPot J; have hv:a>0:=lowPot_pos J hJ; let w:= a*coupling y^dG; have ht:0 < coupling y:= coupling_pos v
 have hl:w=Real.exp (βt (coupling y)+Real.log a):=by rw [Window.strengthLog,←Real.log_pow,Real.exp_add,Real.exp_log (pow_pos ht _),Real.exp_log hv]; exact mul_comm ..
 refine le_trans ?_ (pow_le_pow_left₀ (show 0 ≤ w from hl.symm ▸ (Real.exp_pos _).le) (unit_forest J hJ _ _ _ p v (p'.trans_le b) q) _)
 rw [hl,←Real.exp_nat_mul]
end receipts
lemma treasury (O:HaarBudget G5)(K0:KernelChoices)(v:LocalRatio J):∃ C:ℝ,0<C ∧ ∀ {c f:Side}(S:StepData c f)(Mk:Monk SU.group S),S.kernel=K0 → ∀ (H y β:ℝ),1≤H→0<y→y/2≤β→β≤2*y → Real.exp (pathFees c f y C) ≤ prefactor S SU.group β * (shotM J H β)^ζ Mk.park.Free:=by
 let u:=Real.log (largePot O K0); let r:= Real.log (lowPot J); let C:=4*|r|+4*|u|+1; refine ⟨C,by unfold C; positivity, ?_⟩; intro c f S k t H y β b s ht hx
 have hp:= powerOut S s ht K0 O t; have hu:=powerIn S J s ht hx k.park v H b; apply le_trans _ (mul_le_mul hp hu (Real.exp_pos _).le ((Real.exp_pos _).le.trans hp))
 rw [←Real.exp_add]; apply Real.exp_monotone; rw [countTreasures S,show ζ (Bond c)=ζ (Site c)*4 from (Fintype.card_prod ..).trans (by rfl)]; push_cast
 let w:= roomSite c; let z:=roomSite f; let x:= βt (coupling y)
 change 3*(z-w)*x-C*z ≤ -(w*4)*(x+u)+(3*z+w)*(x+r)
 have ht:w ≤ z:= builtLe S; have he:0≤ w:=by unfold w roomSite; positivity
 have hs:0≤z:= he.trans ht; unfold C; nlinarith only [hs, mul_le_mul_of_nonneg_left (le_abs_self u) he,mul_le_mul_of_nonneg_left (neg_abs_le r) (show 0 ≤ 3*z+w by positivity), mul_le_mul_of_nonneg_right ht (abs_nonneg r),mul_le_mul_of_nonneg_right ht (abs_nonneg u)]
end YM.CF.Jade.Earn
