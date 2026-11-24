import SatinThinCourt
import SatinThinSkyward
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Gleam.Tempest SectorNext.Remainder.Scales
variable {t:ℝ}
local notation "g5"=>SU.group
local notation "yℓ" L x:max=> Scales.y g5 L x
open BProof (coin)
open Pressure.Worth
private lemma pays_m (R:Patch) : Worth.Pays (-(1/4)) 0 0 (merit R.L):=by
 let L':=R.L
 have he(x:ℝ): x≤ Scales.y SU.group L' x:=le_add_of_nonneg_right (mul_nonneg (Work.E07.slope_nonneg _) (Real.log_nonneg (by exact_mod_cast L'.property)))
 apply Worth.Pays.by_floor (C:=1); filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx; rw [abs_of_pos (merit_pos _ (hx.trans_le (he x))),one_mul]; let η:= coin x (-(1/4)) 0 0; have hv:0≤η:= (BProof.coin_pos ..).le; apply le_of_pow_le_pow_left₀ (n:=4) (by norm_num) hv;
 have hG:0<Scales.g SU.group R.L x:= Scales.gauge _ _ (hx.trans_le (he x)); have h:(Scales.y g5 R.L x)*(merit R.L x)^4=1:=by
    rw [←Scales.yg2 g5 L' (hx.trans_le (he x))]; unfold Scales.merit; rw [show Real.sqrt _ ^ 4=(Real.sqrt (_:ℝ)^2)^2 from (pow_mul (Real.sqrt (Scales.g g5 R.L x)) 2 2), Real.sq_sqrt hG.le] -- rw? orientation
 change merit _ _ ^ 4 ≤ η^4; rw [show η^4=x⁻¹ from (?_), show merit R.L x ^ 4 =(Scales.y g5 R.L x)⁻¹ from eq_inv_of_mul_eq_one_right h]; · exact inv_anti₀ hx (he x)
 unfold η; nth_rw 2 [←BProof.coinY hx]; rw [BProof.coin_pow,BProof.coin_inv]; norm_num
lemma cap_meter (R:Patch) : ∀ᶠ x:ℝ in atTop, 
     merit R.L x ≤ meterC x ∧ dleaf R.L x ≤ meterC x∧ 0< allotΨ R.L x ∧ allotΨ R.L x ≤ meterC x ∧ meterC x ≤1 :=by
 have hg := merit_size R.L 1 zero_lt_one _ ((dev_R R).1.low (k:=1) (by omega)); have ht:= merit_size R.L 1 zero_lt_one _ ((size_ψ R.L).low (k:=1) (by omega));
 filter_upwards [hg, ht, (Scales.year g5 R.L).eventually_gt_atTop 0, Worth.Pays.leap (p:=0) (q:=0) (pays_m R) (Or.inl (by norm_num [r_meter] : -(1/4:ℝ)<r_meter)), ((BProof.coin_purchases (b:=0) (c:=0) (Or.inl (by norm_num [r_meter]:r_meter<0))) : Tendsto meterC atTop (𝓝 0)).eventually (ge_mem_nhds zero_lt_one)] with x hy u h q w
 rw [one_mul] at u hy; exact ⟨q,(le_abs_self _).trans (hy.trans q),pow_pos (Scales.gauge _ _ h) _,(le_abs_self _).trans (u.trans q),w⟩
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.cap_meter
