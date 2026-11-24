import GaugeFieldConstruction.AcrossTemper
import GaugeFieldConstruction.AcrossElect
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Altitude Tapestry.Exhibition
open TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
open Heat Buffered Dial Tapestry.Fashion Py.Rate.Branch Haro
local notation "Κ" i:max=> P.run.voyage i
local notation "Τ" k:max=> P.run.uv k
local notation "Πβ" i:max k:max => Actual (Y).meter (Κ i).funds (Κ i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) (Τ k)
local notation "ΤT" i:max k:max s:max => (totalTickets P i k s)

variable (R:P.Register){ε:ℕ→ℝ}(Z:TemperListSt P v R n ε)
local notation "κ" => P.tapeₖ
local notation "μ" => P.tapeᵢ
local notation "ph" => P.foreCallSt v R Z
local notation "θ" => P.run
local notation "gF" => (fun i k s=> roadFareSt P i k s (P.stampOfferSt v Z.calendar i k))
local notation "Τf" => R.val.2.2
local notation "hiF" => R.val.2.2.1
local notation "loF" => R.val.2.2.2
local notation "aB" => (fun i k s=> lobbyTape (i:=i) P k (P.stampOfferSt v Z.calendar i k) s)

-- trajectory of canonically paid β & wave reaches the SAME Tapestry tariffs. Actual and update can both use this character's spectra, not making a new time choice.
lemma termTripSt {i k:ℕ}(h:P.shoulderTape n ε v i k) : Pay Y 0 i k ∧ dist (((aB) i k 0).beta) P.par.x ≤ ε (Τ k):=by
 obtain ⟨q,e⟩:=P.stampGoSt v Z.calendar h
 refine ⟨⟨h.1.2,Nat.zero_le _⟩,?_⟩; change dist (lobbyTape (i:=i) P k _ 0).beta _ ≤ _; rw [Real.dist_eq,e.wallet.trueMark.2.1]; simpa using e.near -- notation e ... unfold binder?
include Z
lemma termPaysSt {I:Type*}{l:Filter I}(i k:I→ℕ)(p:Tendsto k l atTop)(z:∀ᶠ r in l,P.shoulderTape n ε v (i r) (k r)): Tendsto (fun r=> ((aB (i r) (k r) 0)).beta) l (𝓝 P.par.x):=by
 rw [Metric.tendsto_nhds]; intro δ h
 filter_upwards [(Z.calendar.charged.comp (P.run.uv_grows.tendsto_atTop.comp p)).eventually (gt_mem_nhds h),z] with r hr u; exact (P.termTripSt v R Z u).2.trans_lt hr
lemma rampPaysSt {I:Type*}{l:Filter I}(i k:I→ℕ)(p:Tendsto k l atTop)(z:∀ᶠ r in l,P.shoulderTape n ε v (i r) (k r))(s:ℕ){y:Tariff}(h:Tendsto (fun r=> rawTariff Y s (i r) (k r)) l (𝓝 y)): Tendsto (fun r=> gF (i r) (k r) s) l (𝓝 y):=by
 rw [Metric.tendsto_nhds]; intro δ e; let hT:=P.run.uv_grows.tendsto_atTop.comp p; let u:=half_pos e
 filter_upwards [hT.eventually_gt_atTop s, (Z.calendar.charged.comp hT).eventually (gt_mem_nhds u),z,Metric.tendsto_nhds.mp h (δ/2) u] with r t₁ t₂ p u
 obtain ⟨gF0,hg⟩:=stampGoSt P v Z.calendar p; exact lt_of_le_of_lt (dist_triangle _ (rawTariff Y s (i r) (k r)) _) (lt_of_lt_of_le (add_lt_add ((P.walletRateSt v hg.wallet s t₁ (Z.calendar.pay _).1.le).trans_lt t₂) u) (add_halves _).le)
-- `Environs` at all scopes. Tariff orientation.
private lemma secondRoadSt {I:Type*}{l:Filter I}(i:I→ℕ)(v':I→ℕ)(p:Tendsto i l atTop)(z:∀ᶠ r in l, legacy Y (P.period (i r)) (P.cutoff (v' r)))(s:ℕ): Tendsto (fun r=> rawTariff Y s (P.period (i r)) (P.cutoff (v' r))) l (𝓝 ((loF) s)):=by
 rw [Metric.tendsto_nhds]; intro ε h; filter_upwards [z,(propeller_fades.comp p).eventually (gt_mem_nhds h),p.eventually (R.exhibition.scroll s)] with r z t v; exact (v _ (((P.talks R).status ..).1 z)).2.trans_lt t
structure CanonAmenitiesSt : Prop where
 fare (s:ℕ): ((loF) s) ∈ inbounds P.par s∧ Sound.Couplet P.period id (fun i w=> gF i (P.circuitDepth i w) s) (fun i=> hiF s i) (loF s) (fun z=> ∀ᶠ i in atTop, legacy Y (P.period i) (P.circuitDepth (P.period i) (z i))) ∧ Tendsto (fun r:ℕ=> gF (μ (2*r)) (κ (2*r)) s) atTop (𝓝 ((loF) s))
 forecast (s:ℕ)(A:P.Effect)(p:A∈ shorter P.Test s): Sound.Couplet P.period id (fun i t=>ph i (P.circuitDepth i t) A) (fun i=>rowTake Y B i R.exhibition A) (vistaTake Y B (P.talks R) A)
           (fun z=> ∀ᶠ i in atTop, legacy Y (P.period i) (P.circuitDepth (P.period i) (z i)))∧
    Tendsto (fun t:ℕ=>ph (P.tapeᵢ (2*t)) (P.tapeₖ (2*t)) A) atTop (𝓝 (vistaTake Y B (P.talks R) A))
 terminal (i k:ℕ→ℕ)(p:Tendsto k atTop atTop)(z:∀ᶠ r in atTop,P.shoulderTape n ε v (i r) (k r)): Tendsto (fun r=> ((aB (i r) (k r) 0)).beta) atTop (𝓝 P.par.x)
 -- invariant/AuthSt proof independent of i here
lemma outerReachesSt: CanonAmenitiesSt P v R Z:=by
 let g:= R.exhibition
 refine ⟨fun s=>⟨ g.IRPrices Y B s,⟨fun i=>?_,g.ribbon s,?_⟩,?_ ⟩,fun s A p=>P.roadsPaySt v R Z A p,fun i k=>P.termPaysSt v R Z i k⟩
 · have he: StrictMono (circuitColumn i):= by intro _ _ h; unfold circuitColumn; exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (Nat.pair_lt_pair_right _ h) (by decide)) 1
   exact P.rampPaysSt v R Z (fun _=>i) (P.circuitDepth i) (P.independentRead i).1 (P.columnPay v Z.calendar i) s ((g.stripe s i).comp (P.history.growsB.comp he).tendsto_atTop)
 · intro u p; obtain ⟨t,p'⟩:=P.jointPays v Z.calendar p; exact P.rampPaysSt v R Z P.period _ t p' s (P.secondRoadSt v R Z id (fun r=> P.columnPlan (P.period r) (u r)) tendsto_id p s)
 let q:Tendsto (fun r:ℕ=>2*r) atTop atTop:= (show StrictMono (fun i:ℕ=>2*i) from (by intro _ _ h; exact Nat.mul_lt_mul_of_pos_left h (by decide))).tendsto_atTop
 exact P.rampPaysSt v R Z (fun r=>μ (2*r)) (fun r=>κ (2*r)) (P.paidₖ.tendsto_atTop.comp q) (P.thinPays v Z.calendar) s (P.secondRoadSt v R Z _ _ (P.history.growsA.tendsto_atTop.comp q) (Eventually.of_forall fun i:ℕ=>P.history.gate (2*i)) s)
-- The observer's events. `CampaignSt` still with other approach: P/Amplik.X gauge labels & apertures; not claiming those support bounds and geometry
-- already ported to `Temper` beyond the bound book `Prompts`. But all such ordered Menu values (through `Effect`) converge, including the election.
-- For this supplementary estimator one can cost using a wallet before horizon s any S including bounding
-- the WHOLE product (no multiplicativity claimed here between canon charges), #print
variable {j:Axis}{c:P.Poll j}{x:P.Spectrum0 j}(V:P.Selects R j x c)
local notation "pH" => P.pollTicket j c
abbrev canyonRatioSt (a i k:ℕ) (A:P.Effect):= P.foreCallSt v R Z i k (A*P.pollTicket j c a)/ P.foreCallSt v R Z i k (P.pollTicket j c a)
structure PronouncesSt {j:Axis}(c:P.Poll j)(x:P.Spectrum0 j) : Prop where
  announce (s:ℕ)(f:P.Effect)(p:f∈ shorter P.Test s): Tendsto (fun a=>P.RatioOn R j c a f) atTop (𝓝 (P.spirits R j x f)) ∧
    (∀ᶠ a:ℕ in atTop,s ≤ (c a).t ∧
    ((∀ᶠ i:ℕ in atTop,1/2< ‖ph (P.tapeᵢ (2*i)) (P.tapeₖ (2*i)) (P.pollTicket j c a)‖) ∧ Tendsto (fun i:ℕ=> P.canyonRatioSt v R Z (c:=c) a (P.tapeᵢ (2*i)) (P.tapeₖ (2*i)) f) atTop (𝓝 (P.RatioOn R j c a f)))∧∀ (u:ℕ→ℕ), (∀ᶠ i:ℕ in atTop,legacy Y (P.period i) (P.circuitDepth (P.period i) (u i))) →
    (∀ᶠ i:ℕ in atTop,1/2< ‖ph (P.period i) (P.circuitDepth (P.period i) (u i)) (P.pollTicket j c a)‖) ∧ Tendsto (fun i:ℕ=> P.canyonRatioSt v R Z (c:=c) a (P.period i) (P.circuitDepth (P.period i) (u i)) f) atTop (𝓝 (P.RatioOn R j c a f)))

include V
lemma campChoosesSt : PronouncesSt P v R Z c x := by
 constructor; intro s f p; refine ⟨(V.poll f _ p).1,?_⟩
 filter_upwards [V.denominator_tends.norm.eventually (lt_mem_nhds (by norm_num : 1/2<(‖(1:ℂ)‖))),(V.poll f s p).2] with a h h₁
 let Yp:= c a
 have ht:(pH) a∈ shorter P.Test (c a).t:=short_pinhole _ _
 let T:= P.roadsPaySt v R Z _ ht
 let X:= P.roadsPaySt v R Z _ ((shorter P.Test (c a).t).mul_mem ((climbs P.Test h₁.1) p) ht)
 exact ⟨h₁.1,⟨T.2.norm.eventually (lt_mem_nhds h), X.2.div T.2 h₁.2.1⟩,fun j p=>⟨(T.1.paths j p).norm.eventually (lt_mem_nhds h),(X.1.paths j p).div (T.1.paths j p) h₁.2.1⟩⟩
#print axioms campChoosesSt
#print axioms outerReachesSt
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
