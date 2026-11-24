import YM.CF.Feu.Sand
import YM.CF.Jade.Prune
import YM.CF.Jade.Sense
set_option autoImplicit false
set_option maxHeartbeats 400000
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
variable {d e η t z A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable {E F J:Type}[MeasurableSpace E][MeasurableSpace F][Finite F][MeasurableSingletonClass F]
open Nor Girt
open Prism Feu
local notation "HG"=> Finset (Dwell (mid N B))
local notation "CV"=> Cipher (mid N B)
local notation "θ"=> (mid N B)
local notation "Zq"=> (fun i :Finset (Dwell (mid N B))=>prismL i)
variable {V0:ℝ} (Yp:BudgetPoint) (X:Support (Domain N B))
variable (W0:E→Pane (mid N B)→Cipher (mid N B))(T':F→Raid (Dwell (mid N B)))(κ:E→ F)(h:0 ≤ T')(p:Measurable κ)(hp:∀ i,Sym_ (N:=N) (B:=B) Yp k (W0 i) X ∅ (T' (κ i)))
variable (μ:Measure E)[IsProbabilityMeasure μ](Q: Set E)(u:MeasurableSet Q)(A₀ A₁:Raid (Dwell (mid N B)))(v₀:0 ≤ A₀)(v₁:0 ≤ A₁)
local notation "Ψp"=> Rue.litres Yp.threshold X ∅
variable (WF:Pane (mid N B)→Cipher (mid N B))(fw:∀ U∈Rue.litres Yp.threshold X ∅, StronglyMeasurable (fun i=> W0 i U))
-- Q marks tail (NOT small).
local notation "Bq"=> (fun i:HG=>∫ x':E, Q.indicator (fun y : E=> Nor.linkY Yp X (T' (κ y)) k i) x' ∂μ)
variable (o:Site (Domain N B))(ho:o∈ X)(p₁:∀ U∈ Rue.litres Yp.threshold X ∅,∀ i (y:E), y∉ Q→ Signs Yp o (fun v=>crumb ((W0 y (increment U v))-(WF (increment U v))).val i) (A₁ i)) (p₀:∀ U∈Rue.litres Yp.threshold X ∅,∀ i,Signs Yp o (fun v=>crumb (WF (increment U v)).val i) (A₀ i))
local notation "Zt"=> (unrest (n:=mid N B) ∅ Yp.B) -- tune
private lemma pay_v{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](Z Y:E→ℂ)(x:E){v:ℝ}(h:Allows k Z x V0)(p:Allows k Y x v):Allows k (fun x=>Z x-Y x) x (V0+v):=by
 refine ⟨h.smooth.sub p.smooth,fun i e=> ?_⟩; change ‖iteratedFDeriv ℝ i (Z-Y) x‖ ≤_; rw [iteratedFDeriv_sub_apply (h.smooth.of_le (Nat.cast_le.mpr e)) (p.smooth.of_le (Nat.cast_le.mpr e))] -- tune signature
 exact (norm_sub_le ..).trans (add_le_add (h.norm_le i e) (p.norm_le i e))
include h hp p v₀ v₁ u p₁ p₀ fw ho
lemma warL (U:Pane (mid N B))(hx:U∈ Rue.litres Yp.threshold X ∅)(i:Finset (Dwell (mid N B))): Signs Yp o (fun v=>crumb ((∫ j, W0 j (increment U v) ∂μ)-WF (increment U v)).val i) ((A₁ + (μ.real Q) • A₀ + Bq) i):=by
 let FX(i':E)(y:Pane (mid N B)):= W0 i' y-WF y; let V(i:E)(A:Pane (mid N B)):= FX i A
 let v(i':E)(z:Pane (mid N B)):= prismL i (FX i' z)
 let L:E→ℝ:= Q.indicator (fun y=> Nor.linkY Yp X (T' (κ y)) k i); let H(x:E):ℝ:= A₁ i + Q.indicator (fun _=> A₀ i) x+L x
 have hs(x:Pane (mid N B))(g:x∈ Ψp): Integrable (fun i=>W0 i x) μ:=digJ Yp X ∅ W0 T' h μ κ p hp o ho (empty_subset _) fw _ g
 let Z:= unrest (∅:Support (Domain N B)) Yp.B; have hI(z:Pane θ): Forge.gyrate Z z= increment z:=funext fun i=>non_r ..
 have ht(y: Pane (mid N B))(g:y∈Ψp)(a:E): Signs Yp o (v a ∘ Forge.gyrate Z y) (H a):=by
    rw [hI]
    by_cases t:a∉Q; · unfold H L; rw [Set.indicator_of_notMem t,Set.indicator_of_notMem t,add_zero,add_zero]; exact p₁ y g _ a t
    unfold H L; rw [Set.indicator_of_mem (not_not.mp t),Set.indicator_of_mem (not_not.mp t)]; have he:= hp a (empty_subset _) y g o ho i; rw [show Forge.gyrate (unrest ∅ Yp.B) y=increment y from hI y] at he
    let V(t:tangD (mid N B)):= prismL i (W0 a (increment y t)); let c(t:tangD (mid N B)):= prismL i (WF (increment y t)); have hx:v a ∘ increment y=V-c:=funext fun t=> (prismL i).map_sub _ _
    rw [hx]; have hV: Signs Yp o (V-c) (Nor.linkY Yp X (T' (κ a)) k i+A₀ i):=by
       apply Prism.skills; exact pay_v _ _ _ (Prism.skin he) (Prism.skin (p₀ y g i))
    apply Prism.high hV
    linarith only [show 0 ≤ A₁ i from v₁ i]
 obtain ⟨P,hO,hK⟩:= fin_r (fun x:F=> Nor.linkY Yp X (T' x) k i) (Set.finite_range _); let M := A₁ i+A₀ i+P; have hm0:0 ≤ M:=add_nonneg (add_nonneg (v₁ i) (v₀ i)) hO; have hz(a:E): H a≤M:=by unfold H M L; by_cases p:a ∈ Q; rw [Set.indicator_of_mem p, Set.indicator_of_mem p]; exact add_le_add_right ((Real.le_norm_self _).trans (hK _)) _; rw [Set.indicator_of_notMem p,Set.indicator_of_notMem p,add_zero,add_zero]; exact ((le_add_of_nonneg_right (show 0 ≤ A₀ i from v₀ i)).trans (le_add_of_nonneg_right hO))
 have htL:Integrable L μ:=(frill κ p (fun x:F=> Nor.linkY Yp X (T' x) k i) μ).indicator u; have hF:= (integrable_const (A₁ i)|>.add ((integrable_const (A₀ i)).indicator u)).add htL
 have hv: Signs Yp o (fun x=>∫ j,v j (increment U x) ∂μ) (∫ x,H x ∂μ):=by
    have hp:=Rue.balance_l (Sat:=Ψp) (Rue.open_l ..) (f:=v) (fun x e t=>Prism.high (ht x e t) (hz t)) (fun z x=>(prismL i).continuous.comp_stronglyMeasurable ((fw z x).sub stronglyMeasurable_const)) hm0 μ _ hx H hF (ht U hx)
    rw [hI U] at hp; exact hp
 have hk:(∫ x,H x ∂μ)= (A₁+ μ.real Q • A₀ + Bq) i:=by unfold H; rw [integral_add (show Integrable (fun x=> A₁ i + Q.indicator (fun _=> A₀ i) x) μ from (integrable_const (A₁ i)).add ((integrable_const (A₀ i)).indicator u)) htL,integral_add (integrable_const (A₁ i)) ((integrable_const _).indicator u),integral_indicator u]; simp; rfl -- tune
 rw [hk] at hv; refine Prism.mint hv ?_
 filter_upwards [(show ∀ᶠ i in 𝓝 0, increment U i∈ Ψp from (show Continuous (increment U) from (hI U) ▸ (stickU Z U)).continuousAt.eventually ((Rue.open_l ..).mem_nhds (show increment U 0∈ Ψp from by simp [hx])))] with x hx'
 let z:=increment U x; have h0 : (∫ i,FX i z∂μ)=(∫ i,W0 i z∂μ)-WF z:=by unfold FX; rw [integral_sub (hs z hx') (integrable_const _)]; simp
 exact (Pastry.hinge (prismL i) ((hs z hx').sub (integrable_const (WF z)))).trans (congrArg (prismL i) h0) -- tune
end YM.CF.Jade
