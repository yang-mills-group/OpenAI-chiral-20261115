import YM.CF.Taxi.Yacht
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations AnalyticBridge.VerifiedReset RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Vow
open Geo Trees Rue Collection Push.BetaTransport
variable (R:PathData SU.group){q:Clip}(T: RegBudget n)(P:BudgetPoint)(Γ:ℝ){σ C Λ:ℝ}{U':Scree.Hub n→ℝ}
variable (p: Pant T)(g:∀ X, PressB P X (T X) h (U' X))(hw:0 ≤ h) (G:DayT P.order Γ)(ht:0 ≤Γ)(k:60 <(More n).val)(H:R.Bounds q σ C Λ)(c0:Decent q P)(u:Geo.Width P q σ)
local notation "tP"=> P.threshold
variable (U₁: Orbit n)(uF:FleetS P.threshold U₁.1)(Zt:Ids n)
local notation "Ω"=>flags P.threshold U₁.1
local notation "δ"=> lureC (realH T)
def dropG(T:RegBudget n)(V:Orbit n)(b:ℝ)(D:PathData SU.group)(p:BudgetPoint)(A:Clip):= moldV n (D.inChannels A p b V.1 -D.inChannels A p (b- lureC (realH T)) V.1)
def canto(T:RegBudget n) : Cipher n:= ∑ i: Scree.Hub n, porch T i 1
include p g hw G ht k H c0 u uF
lemma pitchL(β:ℝ):
 (∑ x:Scree.Hub n,Vow.march P (pur x) (oV (T x)) U₁) = (canto T+dropG T U₁ β R P q) +
 (((∑ i:Scree.Hub n,CoatL T P U₁ i) +∑' x: Lane n, Vow.march P (χx P R x) (oV (ham x P q R δ)) U₁)+∑' i:Reign n, Vow.march P (ωx P R i) (oV (gustH i P q R δ)) U₁)+
 ((∑ X:Scree.Hub n,fuelV P (pamE T X) U₁) - ∑' i:Lane n,fuelV P (regV Zt P R q δ i) U₁) :=by
 let W:Scree.Hub n→Pane n→ℝ:=realH T
 let C:=moldV n
 have H₁(ε:ℝ) : HasSum (fun x:Lane n=> Vow.march P (χx P R x) (oV (ham x P q R ε)) U₁) (moldV n (layer (fade R q P ε) U₁.1)):=by
    simp_rw [psips P R U₁ c0 _ ε uF]; apply C.hasSum; have he:= fade_sum (n:=More n) H P ε; rw [layer_total _ _ he]; exact (stack_series _ _ he).hasSum
 have H₂(ε:ℝ): HasSum (fun x:Reign n=> Vow.march P (ωx P R x) (oV (gustH x P q R ε)) U₁) (C (layer (upperFade R P 0 ε) U₁.1)):=by
    simp_rw [pTime P R H U₁ c0 _ ε uF]; apply C.hasSum; let he:= high_fade_sum (n:=More n) H P 0 ε; rw [layer_total _ _ he]; exact (stack_series _ _ he).hasSum
 rw [outflow T p g hw G ht k U₁ uF,(H₁ δ).tsum_eq,(H₂ δ).tsum_eq,(Taxi.toast P R H U₁ Zt ht G c0 u δ).tsum_eq]
 simp_rw [sum_add_distrib];
 rw [dropG,channels_split U₁.1 β,channels_split U₁.1 (β-δ),show (β:ℝ)* _ + _ - _= δ*kinetic R q P U₁.1 from ?_] -- tune
 swap; · ring
 have H₃:= path_split H u c0 0 δ U₁.1; simp only [zero_add, zero_mul] at H₃
 rw [show lureC (realH T)*(∑ i:Site (More n), AnalyticBridge.VerifiedReset.heads P i U₁.1)= _ from (eq_sub_of_add_eq H₃.symm)]
 unfold C canto; simp_rw [map_sub,map_add]; abel
-- financial.H. use enough $Δ`. gives anchored ANY p and buoy h24. even. hinge at output.K.Measure.
omit uF p g hw G ht k
lemma reg_p (v:ℝ)(A:ℝ)(hF:0 ≤ A) : Quotes.anchored (n:=More n) P (Quotes.lowEntry SU.group R P) (fun i=> p0 i P q R v A) ((A*AnalyticBridge.VerifiedReset.Collection.turnFee P*|AnalyticBridge.VerifiedReset.factor*v| * P.threshold^2) * Quotes.lowBase SU.group q P σ C) ∧ Quotes.anchored (n:=More n) P (Quotes.highEntry SU.group R) (fun i=>p2 i P q R v A) ((A*AnalyticBridge.VerifiedReset.Collection.turnFee P*|0+AnalyticBridge.VerifiedReset.factor*v| * P.threshold^3) * Quotes.highBase SU.group P σ C):=by
 let θ₀ :=A*AnalyticBridge.VerifiedReset.Collection.turnFee P*|AnalyticBridge.VerifiedReset.factor*v| *P.threshold^2; let θ₁:= A*AnalyticBridge.VerifiedReset.Collection.turnFee P*|0+AnalyticBridge.VerifiedReset.factor*v| *P.threshold^3; have hx:=turnFee_pos P; obtain ⟨g,p,w⟩:=Quotes.rows (n:=More n) SU.group R q P H u; have hu:= P.threshold_pos
 let vQ:=Quotes.anchored_scale (show 0≤ θ₀ by unfold θ₀; positivity) g; let z:=Quotes.anchored_scale (show 0≤ θ₁ by unfold θ₁; positivity) p
 rw [show (fun i:Lane n=>p0 i P q R v A)= (fun i=> θ₀*(|i.2.mark R q| * lowCost SU.group P (i.2.length R))) from funext (fun i=> by unfold θ₀ p0 AnalyticBridge.VerifiedReset.Collection.turnFee; ring),show (fun i:Reign n=>p2 i P q R v A)= (fun i=> θ₁* i.2.price R P) from funext (fun i=> by unfold θ₁ p2 AnalyticBridge.VerifiedReset.Collection.turnFee; ring)]; exact ⟨vQ,z⟩
end YM.CF.Taxi
