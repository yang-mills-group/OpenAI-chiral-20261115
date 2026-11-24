import YM.CF.Pith.Pole
import YM.CF.Pith.Wage
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
open Vow Bake Lilt Nor SupportP
open Vow Bake Larch
abbrev wit_K (R:Patch)(k n:ℕ)(x c:ℝ):= grain_q (radiusB x) k n 1 c 0
abbrev rol_K(R:Patch)(k n:ℕ)(x c f:ℝ):= tilt_Q (radiusB x) k n 1 c (rainX R 2 x) (rainX R 1 x) + f
abbrev pop_K(R:Patch)(k n:ℕ)(x c f:ℝ):= wit_K R k n x c + rainX R 1 x*(rol_K R k n x c f + (rainX R 1 x)⁻¹* wit_K R k n x c)
local notation "Gk" i:max=> (rainX R 1 i)
local notation "Vk" i:max=> (rainX R 2 i)
abbrev wit_H(R:Patch)(k n:ℕ)(x c f:ℝ):=|pop_K R k n x c f|+c
abbrev ink_P(U:ℝ→ℝ)(x:ℝ):= degreePrice (radiusB x) (U x) 1
lemma rate_f(R: Patch)(f:ℝ→ℝ)(p:sizeK R.L 1 f)(u:∀ᶠ x in atTop,ink_P f x≤1/2)(m:ℕ):sizeK R.L (m+1) (fun x => f x * ink_P f x^m*(1-ink_P f x)⁻¹):=by
 let g:=fun x=>degreePrice (radiusB x) (f x) 1; have he:sizeK R.L m (fun x=>g x^m):= by simpa only [one_mul,g] using (apollo_d 1 p).square m
 let U':= fun x=>(1-g x)⁻¹; have hk:sizeK R.L 0 U':=(sizeK.mild R.L 2).cost_d (by
    filter_upwards [u] with x v; have hz:1/2≤1-g x:=by change g x ≤ 1/2 at v; linarith only [v]
    have hp:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hz; unfold U'; rw [abs_of_pos (inv_pos.mpr hp), inv_le_iff_one_le_mul₀ hp,abs_of_pos (by norm_num : 0 < (2:ℝ))]; linarith)
 exact (((p.tint he).tint hk).low (by omega))
variable {c g:ℝ→ℝ}(t:c=c)
abbrev warmK(V:ℝ→ℝ):Prop:=∀ᶠ x:ℝ in atTop,0<V x∧ink_P V x≤1/2
lemma grow_f(R:Patch)(k n:ℕ)(c g:ℝ→ℝ)(p:sizeK R.L 1 c)(w:Litt R 2 g)(q: warmK c):let h(x):= wit_H R k n x (c x) (g x); sizeK R.L 1 h ∧ warmK h∧(∀ᶠ x in atTop,pop_K R k n x (c x) (g x)≤h x)∧sizeK R.L 1 (fun x=>h x+h x*(ink_P h x)^0*(1-ink_P h x)⁻¹) ∧ Litt R 2 (fun x=> Caph (rainX R 1 x) (rol_K R k n x (c x) (g x)) (ink_P h x) (h x)) ∧sizeK R.L 3 (fun x=>(rainX R 2 x)⁻¹*wit_K R k n x (c x)):=by
 intro H
 let u(x):= pop_K R k n x (c x) (g x); let K:=rain_l R 1; let V:= fun x=> grain_q (radiusB x) k n 1 (c x) 0; have hv:= ample_b q p k n 0 1; let G(x):=rol_K R k n x (c x) (g x); have hz:Litt R 2 G:= Litt.add_e (Litt.gain (lean_q q p k n 1)) w -- explicit q is abbrev R? warmK uses no R; yes
 have hk:sizeK R.L 1 u:= hv.accrue (rockP 1 (hz.height_r.accrue (K.tint hv))) -- ABI
 have he:sizeK R.L 1 H:= (iFX hk).accrue p
 have hp:∀ᶠ x in atTop,ink_P H x≤1/2:= (apollo_d 1 he).spine.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2))
 refine ⟨he,(hp.and q).mono (fun i v=> ⟨add_pos_of_nonneg_of_pos (abs_nonneg _) v.2.1,v.1⟩), q.mono fun x v=>(le_abs_self _).trans (le_add_of_nonneg_right v.1.le),he.accrue (rate_f _ _ he hp 0),?_ ,(rain_l R _).tint hv⟩
 exact Litt.add_e (Litt.add_e hz (Litt.gain ((K.scale 2).tint (rate_f _ _ he hp 1)))) (Litt.gain (rate_f _ _ he hp 2))
end YM.CF.Jade
