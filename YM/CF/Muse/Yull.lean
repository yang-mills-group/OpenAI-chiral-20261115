import YM.CF.Muse.Athos
 
 
set_option autoImplicit false
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
open Oath Feu Haro Nor
private lemma beaconF(P:Patch)(I:Stake.Isle)(w:Decor I)(h A a:ℝ)(k l:ℕ)(p:0 ≤ h)(q:0<A):1 ≤ tollL P I h A a k l:=by
 have he:= w.g0; unfold tollL Coin_; have ht:= richP (k+2); have hi:0 ≤ population:=sq_nonneg _; have hy:0 ≤ followV [] P.L:=by unfold followV; positivity
 apply le_add_of_nonneg_right; positivity
lemma riseV(P:Patch)(I:Stake.Isle)(w:Decor I)(h A a:ℝ)(k l:ℕ)(p:0 ≤ h)(q:0<A):1 ≤ tollL P I h A a k l:=beaconF P I w h A a k l p q
lemma scope_a(w A:ℝ)(u:0<w)(k' j:ℕ):∃ N:ℕ,∀ P:Patch,N≤P.L.val →scope_v w k' P ∧∀ I:Stake.Isle,∀ᶠ H:ℝ in atTop,tollL P I H A (tollE w) j k' ≤ H:=by
 have hx:0 < tollE w:=by unfold tollE; linarith
 obtain ⟨m,f⟩:=scale_b A 1 1 (tollE w) j k' zero_lt_one
 obtain ⟨q,v⟩:=standing w (tollE w) (w/4) hx.le (by positivity) (k'+90+5) (by linarith)
 refine ⟨max m q,fun P p=> ⟨fun x y r h=>?_ ,fun I=>by simpa using f P ((le_max_left ..).trans p) I⟩⟩
 exact v r (by rw [h]; exact le_trans (le_max_right ..) p)
lemma broadB(P:Pilot):∀ᶠ x:ℝ in atTop,1≤ P.hat R x :=by
 let Y(x:ℝ):= P.hat R x; have h:= P.high; have hv: Tendsto Y atTop atTop:= (SectorNext.Remainder.Scales.peak SU.group R.L).const_mul_atTop h -- name check
 exact hv.eventually_ge_atTop _
end YM.CF.Py
