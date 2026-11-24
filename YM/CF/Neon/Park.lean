import YM.CF.Neon.Spring
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Neon
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
variable{N P B:Side}{S_O:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S_O}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
open Moto Hove Tap Tune Taxi Nor Oath Larch
open Fief Lor Oise
variable (L0:Side) (X p0:BudgetPoint)(k p l j:ℕ)(uκ:0=0)(Ω:Hove.Grant j p)
lemma capD (f:ℝ→ℝ)(pA:Tendsto f atTop (𝓝 0)) (A:ℝ) (u:0 ≤ A):∀ᶠ x in atTop,CapZ X (f x) A:=by
 let G(x):= hrζ X x 1+Moto.trotΦ X (hrζ X x 1) A
 let V(x:ℝ):= G (f x); have he : Tendsto V atTop (𝓝 0):=by
    have h:Continuous G:=by unfold G hrζ Moto.trotΦ Taxi.tollV; fun_prop
    have hx:G 0=0:=by unfold G hrζ Moto.trotΦ Taxi.tollV; simp
    exact hx ▸ (show Tendsto V atTop (𝓝 (G 0)) from h.continuousAt.tendsto.comp pA)
 let a:=((X.order:ℝ)+1); have h1:Tendsto (fun x=>a*V x) atTop (𝓝 0):=by simpa only [mul_zero] using he.const_mul a
 let P(x):= rotζ X (V x); have hh:Tendsto P atTop (𝓝 0):=by simpa only [mul_zero] using h1.const_mul (2*(X.order.factorial:ℝ))
 filter_upwards [h1.eventually (ge_mem_nhds (show 0<(1/4:ℝ) by norm_num)),hh.eventually (ge_mem_nhds (show 0<(1:ℝ) by norm_num))] with x h k
 exact ⟨h,k⟩
lemma capC (Fχ A:ℝ)(p:p0.order=X.order)(v:p0.power=X.power)(g:CapZ X Fχ A):CapZ p0 Fχ A:=by
 unfold CapZ; simp only; rw [vU_c X p0 p v, tV_c X p0 p v]; unfold rotζ; rw [p]; exact g -- tune hg
local notation "k1"=> K.j
variable(Uκ:ℝ→ℝ)(Fχ a s:ℝ)(hK: Hove.Grant j p)(ha:0<a)
open Haro
structure Warm_K (P:BudgetPoint)(d:ℝ)(x:ℝ)(V:ℝ):Prop where
 fuse: CapZ P d V
 moat: (1+(L0.val^2:ℕ):ℝ)⁻¹ ≤ (L0.val:ℝ)⁻¹^2
 burn: Gala p k 100 x 3
 pact: Gala p k (16*(l+300)) x 3
 mast: mast_ζ L0 p j Ω a x s≤ (Ω.A+2)*(L0.val:ℝ)⁻¹^5
#check Warm_K
open Lor
-- unilateral.app after-L forecast independent.Root height.D.shutter.
include ha
lemma loomK (F:ℝ→ℝ)(kτ:ℝ)(pσ:0 ≤ kτ)(u:sizeK L0 2 F):∀ᶠ x in atTop,Warm_K L0 k p l j Ω a s X (F x) x kτ:=by
 filter_upwards [capD X F ((u.low (by omega)).spine) kτ pσ, Oath.progP p k 100, Oath.progP p k (16*(l+300)), frost_Q L0 p j Ω a ha s, Work.E01.radiusB_tendsto.eventually_ge_atTop (2*L0.val^2)] with x q u v ht hu
 exact ⟨q,nought_X ..,@u,@v,ht⟩
end YM.CF.Neon
