import YM.CF.Muse.Bill
import YM.CF.Tune.Woe
import YM.CF.Jade.Prune
import YM.CF.Jade.Sense
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tune
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
open Jade
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
-- local curvature value including entire exceptional Gaussian set.P.Path. factor correction.
local notation "VΛ"=> ↥(Cipher (mid N B))
local notation "IV"=> increment (1:Pane (mid N B))
variable (o:Site (Domain N B))(hx:o∈X)
open Moto
local notation "EH"=> (tangD (mid N B))
variable (I J₀:PlaqAxes)(Za:ℂ)(σ:ℝ)(hz:0 ≤ σ)(hq:∀ i:E,i∉ Q→ ‖Moto.tooth o Yp (W0 i) I J₀-Za‖≤ σ)
include hx h p hp u fw hz hq
local notation "FΣ"=> (fun U:Pane θ=>∫ j,W0 j U∂μ)
lemma κtax : ‖tooth o Yp FΣ I J₀ -Za‖ ≤ σ + μ.real Q*‖Za‖+ (Bq) (∅: HG):=by
 let T:= prismL (N:=mid N B) ∅; let G(i:E)(U:Pane (mid N B)):= T (W0 i U)
 have hs(x:Pane (mid N B))(g:x∈ Ψp): Integrable (fun i=>W0 i x) μ:=digJ Yp X ∅ W0 T' h μ κ p hp o hx (empty_subset _) fw _ g
 let Z:= unrest (∅:Support (Domain N B)) Yp.B; have hI(z:Pane θ): Forge.gyrate Z z= increment z:=funext fun i=>Feu.non_r ..
 let K(b:F):= Nor.linkY Yp X (T' b) k (∅: HG); have ht(y: Pane (mid N B))(g:y∈Ψp)(a:E): Signs Yp o (G a ∘ Forge.gyrate Z y) (K (κ a)):= hp a (empty_subset _) y g o hx ∅
 obtain ⟨P',hO,hK⟩:= fin_r K (Set.finite_range _); let U:Pane (mid N B):=1; have hP:U∈Ψp:=⟨by simpa using (ping_f Yp X),by simp⟩
 let H1:= Forge.gyrate Z U; have he: (fun t:EH => ∫ i,G i (H1 t)∂μ)=ᶠ[𝓝 0] Taxi.lifeH FΣ ∘ increment U:=by filter_upwards [(stickU Z U|>.continuousAt|>.eventually ((Rue.open_l ..).mem_nhds ((Forge.born Z U).symm ▸ hP)))] with t v; have hp:= Pastry.hinge T (φ:=fun i=>W0 i (H1 t)) (hs (H1 t) v); rw [show H1=increment U from hI U] at hp ⊢; exact hp
 let F_:=(fun x=> ∫ i,G i (increment U x)∂μ); let A:=![Tale.clipT Yp o I,Tale.clipT Yp o J₀]; let L':=ContinuousMultilinearMap.apply ℝ (fun _:Fin 2=>tangD (mid N B)) ℂ A
 let V(i:E):= iteratedFDeriv ℝ 2 (G i ∘ H1) 0; obtain ⟨hp,ho⟩:= (Rue.rank_pi (Sat:=Ψp) (Rue.open_l ..) (f:=G) (fun x p t=>Prism.high (ht x p t) ((Real.le_norm_self _).trans (hK _))) (fun z x=> T.continuous.comp_stronglyMeasurable (fw z x)) hO μ U hP).2 2 ((by decide:2≤6).trans Yp.order_ge)
 let Cz(i:E):ℂ:= L' (V i); have hC: Integrable Cz μ:= L'.integrable_comp (φ:=V) hp; have hT : tooth o Yp FΣ I J₀= (∫ i,Cz i ∂μ):=by
    change L' (iteratedFDeriv ℝ 2 (Taxi.lifeH _ ∘ increment U) 0)= _; rw [← (he.iteratedFDeriv (𝕜:=ℝ) 2).self_of_nhds,show iteratedFDeriv ℝ 2 (fun x=>∫ i,G i (H1 x)∂μ) 0=_ from ho]; exact (L'.integral_comp_comm (φ:=V) (by exact hp)).symm -- arg φ tender
 let L:= Q.indicator (fun y=> K (κ y)); let W:= Q.indicator (fun _:E=> ‖Za‖); have hv:Integrable L μ:=(frill κ p K μ).indicator u; have hw:Integrable W μ:= (integrable_const _).indicator u
 have hd(i:E): ‖Cz i-Za‖≤ (σ + W i) + L i:=by
    have hs:Cz i=tooth o Yp (W0 i) I J₀:= by unfold Cz V; rw [show H1= increment U from hI U]; rfl
    by_cases p:i∉ Q
    · unfold W L; rw [hs, Set.indicator_of_notMem p,Set.indicator_of_notMem p,add_zero,add_zero]; exact hq i p
    unfold W L; rw [Set.indicator_of_mem (not_not.mp p), Set.indicator_of_mem (not_not.mp p)]; let T':= Tale.fore_l Yp o I
    have hp: ‖Cz i‖ ≤ K (κ i):= (ht U hP i).token 2 ((by norm_num:2≤6).trans Yp.order_ge) _ (fun k' => by fin_cases k'; exact T'; exact Tale.fore_l Yp o J₀)
    refine (norm_sub_le (Cz i) Za).trans ((add_le_add hp (le_refl _)).trans ?_); linarith
 have hh:= (norm_integral_le_integral_norm  (fun i:E=> Cz i-Za)).trans (integral_mono ((hC.sub (integrable_const _)).norm) (((integrable_const σ).add hw).add hv) hd)
 change ‖(∫ i,Cz i-Za ∂μ)‖≤ (∫ i,(σ + W i) + L i∂μ) at hh
 rw [integral_sub hC (integrable_const _), integral_add (show Integrable (fun i=>σ+W i) μ from (integrable_const _).add hw) hv, integral_add (integrable_const σ) hw] at hh; unfold W at hh; rw [integral_indicator u] at hh; rw [hT]; simpa using hh -- or Bq macro mismatch
end YM.CF.Tune
