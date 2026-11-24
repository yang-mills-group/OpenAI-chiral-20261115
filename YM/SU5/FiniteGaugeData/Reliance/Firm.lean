import YM.CF.Continuum.Beluga
/-! # Counterpart to Jade.Earn.treasury for BudgetLaw ABS log

Prices with site factors and exact Haar exponent. Delivered for assembly ABOVE in Vp929,
P.C(x) can then actually be chosen. This does not change any algorithm or prices of the genuine
regulators, it is an extra budget on the election from those grants. -/
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
-- opened Earn, add just opposite estimates
namespace Reliant
private lemma remaining (F:Tree.Forest S.ratio): Fintype.card F.Free=3* Fintype.card (Site f)+ Fintype.card (Site c):=by
 have ht:= SectorNext.Vacuum.FlatTree.count_clear F; rw [Fintype.card_prod _ Axis] at ht; have hp:Fintype.card Axis=4:=rfl; rw [hp] at ht; omega

private def smallPep (O:HaarBudget SU.group)(K:KernelChoices):ℝ := O.small*Real.exp (-K.penalty)
private lemma pep_positive (O:HaarBudget G5)(K:KernelChoices): 0<smallPep O K:=mul_pos O.positive (Real.exp_pos _)
private lemma coupOne (y : ℝ)(p:1 ≤ y) : coupling y ≤ 1:= inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt p)
private lemma lower_pot (O:HaarBudget G5)(y β:ℝ)(h:1 ≤ y)(p:0 ≤ β)(q:β≤2*y): smallPep O S.kernel * coupling y ^ SU.group.lieDim ≤ S.penaltyZ β G5:=by
 let a : ℝ:=Real.exp (-S.kernel.penalty); let r:=coupling y
 have ht:0<y:= zero_lt_one.trans_le h; have hr:0<r:= coupling_pos ht
 let Z:= SU.group.shell (r/4)
 have hv(x:SU.group.El)(d:x∈Z): a ≤ S.penaltyWeight β x:= by
    apply Real.exp_le_exp.mpr; let c':=SU.group.chord x; let f:= SU.group.price x; let P':=S.kernel.penalty
    change -P' ≤ -β * P'* f; have hp:0<P':= S.kernel.penalty_pos; have hc:0 ≤ c':= SU.group.chord_nonneg x
    have hh:c'≤r:= (show c'≤r/4 from d).trans (by linarith)
    have hy : f=c'^2/2:=by unfold c' f; rw [SU.group.chord_price]; ring
    have hz:0 ≤ f:= (SU.group.price_range x).1; have hR : y*r^2=1:= by unfold r coupling; rw [inv_pow,Real.sq_sqrt ht.le,mul_inv_cancel₀ ht.ne']
    have hf: β*f ≤ 1:= (mul_le_mul q (show f≤r^2/2 from hy.le.trans (by gcongr)) hz (by positivity : 0 ≤ 2*y)).trans_eq (by
       change 2*y*(r^2/2)= (1:ℝ); linarith) -- annotate intermediate
    nlinarith only [mul_le_mul_of_nonneg_left hf hp.le]
 have H (u : SU.group.El): Z.indicator (fun _ => a) u ≤ S.penaltyWeight β u := by
    by_cases g:u∈Z
    · exact le_of_eq (Set.indicator_of_mem g _) |>.trans (hv u g)
    rw [Set.indicator_of_notMem g]; exact (Real.exp_pos _).le
 calc _ = O.small * r^SU.group.lieDim * a:=by unfold smallPep r a; ring
      _ ≤ SU.group.probHaar.real Z * a:= mul_le_mul_of_nonneg_right (O.low r hr (coupOne y h)) (Real.exp_pos _).le
      _ ≤ _:= by
        let t := SU.group.shell_meas (r/4); simpa [StepData.penaltyZ, Z, integral_indicator t, setIntegral_const] using
          (integral_mono (μ:=SU.group.probHaar) ((integrable_const a).indicator t) ((S.penaltyWeight_cont (G:=G5) β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) H)

private def growPot (J:ChartRatio G5):= J.scale*(Real.sqrt (2*Real.pi)*2)^SU.group.lieDim
private lemma grow_pos (hx:LocalRatio J):0 < growPot J:= by unfold growPot; have p:=hx.scale; positivity
private lemma high_grain (v:ℝ): point G5 v ≤ 1:= by
 unfold Appel.point grainS; calc _ ≤ (Appel.rice SU.group Set.univ).toReal:= ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
                                 _ = 1 := by simp
private lemma height_one (hJ:LocalRatio J)(H y β:ℝ)(hi:0<H)(p:1≤y)(q:y/2 ≤ β):
    0 ≤ shotM J H β ∧ shotM J H β ≤ growPot J * coupling y ^ SU.group.lieDim :=by
 have hp:= zero_lt_one.trans_le p; have hb:0 < β:= (half_pos hp).trans_le q
 let A:=Real.sqrt (2*Real.pi); have hA:0<A:= Real.sqrt_pos.mpr (by positivity)
 let W:=coupling β; have ht:0<W:=coupling_pos hb
 have hv:W≤2*coupling y:=by
    have he:Real.sqrt y/2 ≤ Real.sqrt β:=by nlinarith only [q,Real.sq_sqrt hb.le,Real.sq_sqrt hp.le,Real.sqrt_pos.mpr hp,Real.sqrt_pos.mpr hb]
    refine (inv_anti₀ (by positivity : 0 < Real.sqrt y/2) he).trans_eq ?_; unfold coupling; simp [div_eq_mul_inv]
 have hi':spare J β=(A*W)^SU.group.lieDim*J.scale:=by unfold spare; rw [Real.sqrt_mul (by positivity),Real.sqrt_sq ht.le]; simp only [Gauge.ColorIndex,Fintype.card_fin]; rfl
 have hg:0<J.scale:= hJ.scale; have hh:=point_p (G:=G5) hi
 unfold shotM; rw [hi']; refine ⟨by positivity,(mul_le_of_le_one_right (by positivity) (high_grain H)).trans ?_⟩
 apply le_trans (b:= (A*(2*coupling y))^SU.group.lieDim*J.scale) (by gcongr); unfold growPot A; exact le_of_eq (by rw [←mul_assoc _ 2,mul_pow]; ring)
open Next.Fluctuations.Sector
variable (O:HaarBudget G5)(K0:KernelChoices)(v:LocalRatio J)
private lemma out_cap (t:S.kernel=K0)(y β:ℝ)(h:1≤y)(p:0 ≤ β)(q:β ≤ 2*y):
    prefactor S G5 β ≤ Real.exp (-(ζ (Bond c):ℝ) * (βt (coupling y)+ Real.log (smallPep O K0))) :=by
 let L:= smallPep O K0; have ht:= pep_positive O K0; have hs:0<coupling y:=coupling_pos (zero_lt_one.trans_le h)
 let w:=L*coupling y^dG; have hi: 0<w:= mul_pos ht (pow_pos hs _)
 have hl:w=Real.exp (βt (coupling y)+Real.log L):=by
    rw [Window.strengthLog,←Real.log_pow,Real.exp_add,Real.exp_log (pow_pos hs _),Real.exp_log ht]; exact mul_comm ..
 have hw:w ≤ S.penaltyZ β G5:= by unfold w L; rw [←t]; exact lower_pot S O y β h p q
 refine le_trans (pow_le_pow_left₀ (inv_pos.mpr (S.penaltyZ_pos ..)).le (inv_anti₀ hi hw) (ζ (Bond c))) ?_
 rw [hl, inv_pow,←Real.exp_nat_mul, ←Real.exp_neg]; apply le_of_eq; unfold L; congr 1; ring
include v
private lemma in_cap (K:Tree.Forest S.ratio)(H y β:ℝ)(p:1≤H)(d:1≤y)(q:y/2≤β):
    (shotM J H β)^ζ K.Free ≤ Real.exp (ζ K.Free*(βt (coupling y)+ Real.log (growPot J))) :=by
 let w:=growPot J*coupling y ^SU.group.lieDim; have ht:= grow_pos J v; have hs:0<coupling y:= coupling_pos (zero_lt_one.trans_le d)
 have hl:w=Real.exp (βt (coupling y)+Real.log (growPot J)):=by rw [Window.strengthLog,←Real.log_pow,Real.exp_add,Real.exp_log (pow_pos hs _),Real.exp_log ht]; exact mul_comm ..
 obtain ⟨h,z⟩:= height_one J v H y β (zero_lt_one.trans_le p) d q
 have he:w≥shotM J H β:= z; exact (pow_le_pow_left₀ h he _).trans_eq (by rw [hl,←Real.exp_nat_mul])

include O K0
/-- Not just upper bounded by inverse of leading power; matching absolute budget. -/
theorem estimate : ∃ C:ℝ,0<C ∧ ∀ {c f:Side}(S:StepData c f)(Mk:Monk SU.group S),S.kernel=K0 → ∀ (H y β:ℝ),1≤H→1≤y→y/2≤β→β≤2*y → prefactor S SU.group β * (shotM J H β)^ζ Mk.park.Free ≤ Real.exp (pathFees c f y (-C)):=by
 let u:=Real.log (smallPep O K0); let r:= Real.log (growPot J); let C:=4*|r|+4*|u|+1; refine ⟨C,by unfold C; positivity, ?_⟩; intro c f S k t H y β b s ht hx
 have hp:= out_cap S O K0 t y β s (le_trans (half_pos (zero_lt_one.trans_le s)).le ht) hx; have hu:= in_cap S J v k.park H y β b s ht
 refine (mul_le_mul (le_refl (prefactor S G5 β)) hu (show 0≤(shotM J H β)^_ from pow_nonneg (height_one J v H y β (zero_lt_one.trans_le b) s ht).1 _) (prefactor_pos ..).le).trans ((mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans ?_)
 rw [←Real.exp_add]; apply Real.exp_monotone; rw [remaining S,show ζ (Bond c)=ζ (Site c)*4 from (Fintype.card_prod ..).trans (by rfl)]; push_cast
 let w:= roomSite c; let z:=roomSite f; let x:= βt (coupling y)
 change -(w*4)*(x+u)+(3*z+w)*(x+r) ≤ 3*(z-w)*x-(-C)*z
 have ht:w ≤ z:= builtLe S; have he:0≤ w:=by unfold w roomSite; positivity
 have hs:0≤z:= he.trans ht; unfold C; nlinarith only [hs, mul_le_mul_of_nonneg_left (neg_abs_le u) he,mul_le_mul_of_nonneg_left (le_abs_self r) (show 0 ≤ 3*z+w by positivity), mul_le_mul_of_nonneg_right ht (abs_nonneg r),mul_le_mul_of_nonneg_right ht (abs_nonneg u)]
end Reliant
end YM.CF.Jade.Earn
#print axioms YM.CF.Jade.Earn.Reliant.estimate
