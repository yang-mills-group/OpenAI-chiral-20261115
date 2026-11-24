import YM.CF.DPress.Yarn.Log
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
namespace Cap
open Moen.Space
-- reusable parameter family. use c on Fin n even when only a portion used, fill dummy. quant.
local notation "St"=>StarPS n
local instance : Nonempty (StarPS n):=⟨⟨0,by rw [norm_zero]; exact zero_le_one⟩⟩
variable (u z:ℕ→ℝ)
def wake (c:StarPS n)(i:ℕ):ℝ:= if h:i<n then u i*(c.val ⟨i,h⟩).1 else 0
def tune (c:StarPS n)(i:ℕ):Haro.SpaceM:= if h:i<n then z i • (c.val ⟨i,h⟩).2 else 0
lemma wakeC : Continuous fun c:StarPS n=>wake u c i:=by unfold wake; by_cases h:i<n; simp_rw [dif_pos h]; exact continuous_const.mul (continuous_fst.comp ((continuous_apply _).comp continuous_subtype_val)); simp_rw [dif_neg h]; exact continuous_const
lemma tuneC : Continuous fun c:StarPS n=>tune z c i:=by unfold tune; by_cases h:i<n; simp_rw [dif_pos h]; have hv:Continuous fun z:StarPS n=>z.val (⟨i,h⟩:Fin n):=(continuous_apply _).comp continuous_subtype_val; exact (continuous_snd.comp hv).const_smul (z i); simp_rw [dif_neg h]; exact continuous_const
lemma wakeB(c:StarPS n)(e:0 ≤ u i) : |wake u c i|≤u i:=by
 unfold wake; split; swap; · exact abs_zero.trans_le e
 next h => rw [abs_mul,abs_of_nonneg e]; exact (mul_le_mul_of_nonneg_left (show _ ≤ _ from (by change ‖(c.val (⟨i,h⟩:Fin n)).1‖≤1; exact (norm_fst_le _).trans ((norm_le_pi_norm ..).trans c.property))) e).trans_eq (mul_one ..)
lemma tuneB(c:StarPS n)(e:0 ≤ z i): ‖tune z c i‖≤ z i:=by
 unfold tune; split; next h=> rw [norm_smul,Real.norm_of_nonneg e]; exact (mul_le_mul_of_nonneg_left ((norm_snd_le _).trans ((norm_le_pi_norm c.val ⟨i,h⟩).trans c.property)) e).trans_eq (mul_one ..)
 exact norm_zero.trans_le e
-- fp scoped.n true.+ rank only compare.
variable {Q:ℕ→Prop}(d:StarPS n→ℕ→ℝ)(r:StarPS n→ℕ→Haro.SpaceM)
structure Clk (d:StarPS n→ℕ→ℝ)(r:StarPS n→ℕ→Haro.SpaceM)(Q:ℕ→Prop):Prop where
 fee(i:ℕ): i<n→ Q i→ 0<u i ∧ Continuous (fun c=> d c i) ∧ ∀ c,|d c i|≤ u i
 earn(i:ℕ):i<n→ Q i→0<z i ∧Continuous (fun c=>r c i)∧∀ c, ‖r c i‖≤ z i
lemma sit (p:Clk u z d r Q): ∃ v:StarPS n, ∀ i,Q i→ i<n → wake u v i=d v i∧ tune z v i=r v i:=by
 let f(v:St)(i:Fin n):ℝ×Haro.SpaceM:=if Q i.val then (d v i/(u i),(z i)⁻¹ • r v i) else 0
 have hv(v:St):‖f v‖≤1:=by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; unfold f; split; swap; · exact norm_zero.trans_le zero_le_one
    next t=>
       obtain ⟨b,c,w⟩:=p.earn i i.isLt t; obtain ⟨g,e,h⟩:=p.fee i i.isLt t; rw [Prod.norm_def]; refine max_le ?_ ?_; · exact le_of_eq_of_le (by rw [norm_div, Real.norm_of_nonneg g.le]; rfl : ‖(d v i/u i)‖=|d v i|/u i) ((div_le_one g).2 (h v))
       rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left (w v) (by positivity)).trans_eq (inv_mul_cancel₀ b.ne')
 let G(v:St):St:= ⟨f v,hv v⟩; have ht:Continuous G:=by
    apply Continuous.subtype_mk; apply continuous_pi; intro i; unfold f; split; next u' => exact ((p.fee i i.isLt u').2.1.div_const (u i)).prodMk ((p.earn i i.isLt u').2.1.const_smul (z i)⁻¹)
    exact continuous_const
 obtain ⟨v,t⟩:= Moen.Space.bow zero_lt_one G ht; refine ⟨v,?_⟩; intro i r' h; let j: Fin n:=⟨i,h⟩; have he:f v j=v.val j:= congrFun (congrArg Subtype.val t) j; unfold f at he; rw [if_pos r'] at he; unfold wake tune; rw [dif_pos h,dif_pos h]; change u i * (v.val j).1=d v i∧ z i • (v.val j).2=r v i; rw [←he]; exact ⟨by change u i*(d v i/u i)=_; rw [mul_comm,div_mul_cancel₀ _ (p.fee i h r').1.ne'],smul_inv_smul₀ (p.earn i h r').1.ne' (r v i)⟩
end Cap
end Crib
end FitD
end YM.CF.Py.Kay
