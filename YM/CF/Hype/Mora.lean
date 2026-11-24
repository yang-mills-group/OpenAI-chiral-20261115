import YM.CF.Hype.Rome
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
-- certify.WAGES off all granted tasks
variable {u Hh pK qK a γ vS dS kL w:ℝ}{r p i:ℕ}{X: GramM (mid N B)}{Y: GramM (mid P B)}{U:Grasp V.U B d}
open Oath Feu Feu.Corset Haro Nor Siete PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Prism Haro Tap Oath
abbrev φnom (k p:ℕ)(C:ℝ):= stakeH k * (flavor * (C*((4:ℝ)^p*((2:ℝ)^p*16))))
lemma ample_η (R:Patch)(k p:ℕ)(C w α h:ℝ)(hv:1 ≤ h)(ht: 0 < α): ∀ᶠ x:ℝ in atTop,∀ (b:ℝ),0≤b → |way_Q R k p x b w α C h| ≤ (|φnom k p C|+1) * (R.L.val:ℝ)⁻¹ * b:=by
 let d:= (R.L.val:ℝ)⁻¹; let V(x):= way_Q R k p x 1 w α C h; have hh:= lt_of_lt_of_le zero_lt_one hv; have hl:0 <d:=by unfold d; positivity
 let Hc(x):=mintY p (a:=α) (C:=w) (radiusB x); let h1(x:ℝ):= -(radiusB x:ℝ)*α; let P'(x:ℝ):=Real.exp (h1 x)
 have hp:Tendsto Hc atTop (𝓝 0):=by
    have he: Tendsto h1 atTop atBot:=by unfold h1; simp_rw [neg_mul]; apply tendsto_neg_atBot_iff.mpr; exact Tendsto.atTop_mul_const ht (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
    let X:= ((Real.exp α)* polV p α) * lurch α*w; have ht': Tendsto P' atTop (𝓝 0):= Real.tendsto_exp_atBot.comp he
    have hk(i): Hc i=P' i* X:=by unfold Hc mintY Haro.frost X P' h1; ring
    simp_rw [funext hk]; simpa using (ht'.mul_const X)
 let A:= (φnom k p C)*d; have he: Tendsto V atTop (𝓝 A):=by
    let L:ℝ:= 2^p*((16:ℝ)*1)/h^2; let U:=(2:ℝ)^p*(L*mintY p (a:=α) (C:=w) 0); let T':ℝ:= C*(4^p*L)/(R.L.val:ℝ); let Ve:=fun x=> stakeH k * h^2*(flavor*((2*Hc x*U)+T'))
    have k0: Tendsto Ve atTop (𝓝 (stakeH k*h^2*(flavor*((2*0*U)+T')))):= (Tendsto.const_mul _ (Tendsto.const_mul _ (Tendsto.add ((Tendsto.const_mul 2 hp).mul_const U) tendsto_const_nhds))) -- namespace
    have hA: stakeH k*h^2*(flavor*((2*0*U)+T'))=A:=by unfold T' L A φnom d; field_simp; ring
    rw [hA] at k0; exact k0
 have hQ:Tendsto (fun x=>|V x|) atTop (𝓝 |A|):= he.abs; have hx:|A| < (|φnom k p C|+1)*d:=by unfold A; rw [abs_mul,abs_of_pos hl]; exact (mul_lt_mul_iff_of_pos_right hl).mpr (by linarith)
 filter_upwards [hQ.eventually (ge_mem_nhds hx)] with x p' b hb; rw [show way_Q R k p x b w α C h= V x*b from by unfold V way_Q; ring_nf,abs_mul,abs_of_nonneg hb]; exact mul_le_mul_of_nonneg_right p' hb
end YM.CF.Py
