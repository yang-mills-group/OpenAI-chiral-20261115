import GaugeFieldConstruction.AcrossThyme
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

variable (R:P.Register){ε:ℕ→ℝ}(E:IntervalsSchedule P n v ε)
local notation "κ" => P.tapeₖ
local notation "μ" => P.tapeᵢ

-- On the three travelling paths. Can forecast via Tapestry, or actual canonically-updated path.
-- No uniformity in budget index s,k *away from the referenced appointments*.
abbrev portholeSt(i k:ℕ) :Prop:= ∃ w:ℕ,P.salesTape w=i ∧ P.tapeₖ w=k
lemma mainWindSt(w:ℕ) : P.portholeSt (P.tapeᵢ (2*w)) (P.tapeₖ (2*w)):= ⟨2*w,P.circleMain w,rfl⟩
lemma alongWindSt(i k:ℕ) : P.portholeSt i (P.circuitDepth i k):= ⟨circuitColumn i k,P.columnIssued i k,rfl⟩
noncomputable def duskSt (k:ℕ):ℝ:=1/(k+1)
lemma duskWakeSt (k:ℕ) : 0<duskSt k:=by unfold duskSt; positivity
lemma duskMovesSt : Tendsto duskSt atTop (𝓝 0):=by
 exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

structure TemperListSt (n:ℕ)(ε:ℕ→ℝ) : Prop extends RibbonCalendarSt P R v ε n where
 highway (i k:ℕ)(t:ℝ)(r:Bet (Τ k))(e:P.shoulderTape n ε v i k)(p:P.portholeSt i k)
       (W:P.WalletDebtSt v (ε:=ε) i k t r) (s:ℕ)(a:s≤ Τ k)(S:BillOfWork)(b:ℝ)(A:P.Effect)(h:Pocket P.calibration S s b A) :
          ‖P.canyonPriceSt i k s r A-taking Y B i k A‖ ≤ duskSt (P.run.uv k)*(cloudSpan s S*b) ∧ (∀ hU,s ≤ hU → hU ≤ Τ k→ P.canyonPriceSt i k hU r A=P.canyonPriceSt i k s r A) ∧
           let F(d:ℕ):= attire (P.roadScriptSt i k d r A); P.PromptsTape (i:=i) r (F s) (frameBudget S P.par P.width s) F (fun d=>(followBox («Λ»:=P.par) («l»:=P.width))^[d-s] (frameBudget S P.par P.width s)) ∧ let T:Mark (side Y i ((Y).uv k)):= F ((Y).uv k); let a(v:Pane (side Y i ((Y).uv k))):=T (v,v); Envelope a ∧ (P.canyonTopSt i k r A)= AcrossLands.position (mesh ((Y).ir i) (Γ).R.L ((Y).uv k)) (Γ).U ((Y).meter.a ((Y).uv k)) (v ((Y).uv k)) a
-- burn exponent preliminary
lemma freezeListSt{N:ℕ→ℝ}(Z:∀ k,0<N k) : ∃ n ε v, RibbonCalendarSt P R v ε n∧ ∀ k, ε k< N k:=by
 obtain ⟨n,h⟩:= territories P.par.J P.par.direct
 let u:= Py.Rate.Branch.Rx P.par.x
 have he:0<u:= Py.Rate.Branch.Rx_pos P.run.oneP
 let ε:=fun k:ℕ=> min (u / (k+2)) (min (duskSt k) (N k/2))
 have hp(k:ℕ):0 < ε k ∧ ε k < u ∧ ε k < N k∧ ε k ≤ duskSt k:=by
    refine ⟨lt_min (by positivity) (lt_min (duskWakeSt k) (half_pos (Z k))), (min_le_left ..).trans_lt (div_lt_self he (by linarith [Nat.cast_nonneg (α:=ℝ) k])), ((min_le_right ..).trans (min_le_right ..)).trans_lt (half_lt_self (Z k)),(min_le_right ..).trans (min_le_left ..)⟩
 obtain ⟨v,E⟩:= P.compileSchedule h (fun k=>⟨(hp k).1,(hp k).2.1⟩) (squeeze_zero (fun k=>(hp k).1.le) (fun k=>(hp k).2.2.2) duskMovesSt)
 refine ⟨n,ε,v,?_,fun k=>(hp k).2.2.1⟩; refine ⟨E,fun m k x=> P.independentCash v E k m x, fun c z h=> P.openVolumes v E z c h, fun _ _ p=>P.passesSTELLA v E p, P.spareTape v E,fun i=>(cadence Y _ (P.circuitMono i) i).and (columnPay P v E _),fun _ p=>P.jointPays v E p, P.thinPays v E, fun i=> ⟨P.circuitMono _,(P.independentRead i).2⟩,?_,fun _ p q=>P.supportsRead v R E p q⟩
 filter_upwards [P.thinPays v E] with i hi; have he:= E.tape _ ((P.circleMain i).symm ▸ hi.1); rw [P.circleMain] at he; exact he.1
lemma spendTemperSt : ∃ n ε v, TemperListSt P v R n ε:=by
 let I:= P.salesTape; let K':= (κ)
 choose D W h using fun w:ℕ=>P.primeMeterSt (I w) (K' w) _ (duskWakeSt (Τ (K' w)))
 let V (k:ℕ):= ∃ t,P.tapeDepth t=k
 let N (k:ℕ):= if v:V k then D v.choose else 1
 have he(k:ℕ):0<N k:= by
       unfold N; split
       next w=> exact W _
       next x=> exact zero_lt_one -- indentation
 obtain ⟨n,ε,v,F,Z⟩:= P.freezeListSt R he
 refine ⟨n,ε,v,F,?_⟩
 intro i k u r x p Yt s a S b A g
 obtain ⟨c,rfl,rfl⟩:= p
 have hg(V₀:ℕ) : N (Τ (K' V₀))=D V₀:=by
      have he:V (Τ (K' V₀)):=⟨V₀,rfl⟩; unfold N; rw [dif_pos he]; exact congrArg D (P.tape_stairs.injective (show P.tapeDepth he.choose=P.tapeDepth V₀ from he.choose_spec))
 have hh : P.run.uv (K' c)= P.tapeDepth c:=rfl
 have d:= P.bookSt_license v Yt x.1 S b A g a
 refine ⟨h c _ _ ⟨(F.calendar.pay _).1,(hg c ▸ Z (Τ (K' c)))⟩ _ _ _ x.1.2 Yt a _ _ _ g,fun s' h g'=>?_, d⟩
 exact (d.1.owned s' h g').2

-- Couplet etc for assigned Bets unlike unfolding through `shoulderTape` syntax.
variable (Z:TemperListSt P v R n ε)
local notation "φ_" j:max h:max => P.portholeSt j h ∧ P.shoulderTape n ε v j h
open Tapestry.Fashion
noncomputable def stampOfferSt (i k:ℕ) : Bet (Τ k):= if W:P.shoulderTape n ε v i k then (P.passesSTELLA v E W).choose_spec.choose else 0
include E
lemma stampGoSt (W:P.shoulderTape n ε v i k) : ∃ t:ℝ, P.PassOutlinesSt (i:=i) (k:=k) (ε:=ε) v t (P.stampOfferSt v E i k):=by
 unfold stampOfferSt; rw [dif_pos W]; exact ⟨_,(P.passesSTELLA v E W).choose_spec.choose_spec⟩
omit E
-- rawCost literal canon view; not bequeathing budgets at any extra tape, only these or `porthole ∧ shoulder`
local notation "tape" j:max h:max=> P.stampOfferSt v Z.calendar j h
abbrev foreCallSt(i k:ℕ)(A:P.Effect):= P.canyonTopSt i k (P.stampOfferSt v Z.calendar i k) A

include Z
lemma purchaserSt (w :P.portholeSt i k)(t:P.shoulderTape n ε v i k)(u:s≤ Τ k)(S:BillOfWork)(b:ℝ)(A:P.Effect)(h:Pocket P.calibration S s b A): ‖P.foreCallSt v R Z i k A-taking P.run P.large i k A‖ ≤ duskSt (Τ k)*(cloudSpan s S*b):=by
 obtain ⟨a,Q⟩:= P.stampGoSt v Z.calendar t; let e:=Z.highway i k a _ t w Q.wallet s u S b A h; unfold foreCallSt canyonTopSt; rw [e.2.1 _ u le_rfl]; exact e.1

lemma forePaysSt {X:Type*}{l:Filter X}(I K':X→ℕ)(g:Tendsto K' l atTop)(h:∀ᶠ r in l, P.portholeSt (I r) (K' r) ∧ P.shoulderTape n ε v (I r) (K' r))(A:P.Effect)(q:A∈ shorter P.Test s){x:ℂ} : Tendsto (fun r=>taking Y B (I r) (K' r) A) l (𝓝 x) → Tendsto (fun r=>foreCallSt P v R Z (I r) (K' r) A) l (𝓝 x):=by
 intro u; let T':=fun r=> taking Y B (I r) (K' r) A; obtain ⟨S,hp⟩:= anyWords P.calibration s A q; obtain ⟨b,w⟩:= issued.mp hp
 let H r:=P.foreCallSt v R Z (I r) (K' r) A - T' r
 let y:= cloudSpan s S*b; have he:= (Y).uv_grows.tendsto_atTop.comp g; have hk:Tendsto H l (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; let d:=fun r=>Τ (K' r)
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ (by simpa only [zero_mul,Function.comp_def] using ((duskMovesSt.comp (show Tendsto d l atTop from he)).mul_const y))
    filter_upwards [h,he.eventually_ge_atTop s] with r z a; exact P.purchaserSt v R Z z.1 z.2 a S b A w
 have hp:=hk.add u; rw[zero_add] at hp; exact hp.congr (fun _=> sub_add_cancel ..)

lemma roadsPaySt (A:P.Effect)(p:A∈ shorter P.Test s): Sound.Couplet P.period id (fun i t=>foreCallSt P v R Z i (P.circuitDepth i t) A) (fun i=>rowTake Y B i R.exhibition A) (vistaTake Y B (P.talks R) A)
           (fun z=> ∀ᶠ i in atTop, legacy Y (P.period i) (P.circuitDepth (P.period i) (z i)))∧
    Tendsto (fun t:ℕ=>foreCallSt P v R Z (P.tapeᵢ (2*t)) (P.tapeₖ (2*t)) A) atTop (𝓝 (vistaTake Y B (P.talks R) A)) :=by
 let z:= Fashion.heightCoupon Y B R.exhibition s p
 constructor
 · refine ⟨fun i=>?_ , z.periods,fun u h=>?_⟩
   · have ht: StrictMono (circuitColumn i):=by intro s v h; unfold circuitColumn; exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (Nat.pair_lt_pair_right _ h) (by decide)) 1
     let d:= P.history.growsB; exact P.forePaysSt v R Z (fun _=>i) (fun t=> P.circuitDepth i (id t)) (P.independentRead i).1 ((Eventually.of_forall fun t:ℕ=>P.alongWindSt i t).and (P.columnPay v Z.calendar i)) _ p ((z.inner i).comp (d.comp ht).tendsto_atTop)
   obtain ⟨a,hp⟩:=P.jointPays v Z.calendar h
   exact P.forePaysSt v R Z P.period _ a ((Eventually.of_forall fun i:ℕ=> P.alongWindSt (P.period i) (u i)).and hp) A p (z.paths (fun k=> P.columnPlan (P.period k) (u k)) h)
 have pu:Tendsto (fun r:ℕ=>2*r) atTop atTop:= (show StrictMono (fun i:ℕ=>2*i) from by intro _ _ h; exact Nat.mul_lt_mul_of_pos_left h (by decide:0<2)).tendsto_atTop
 have hy:Tendsto (fun t=>taking Y B (μ t) (κ t) A) atTop (𝓝 (vistaTake Y B (P.talks R) A)):=
    by rw [← P.spirit_price R 3 (f:=A) (curve.mpr ⟨s,p⟩)]; exact P.spirits_limit R 3 A (curve.mpr ⟨s,p⟩)
 exact P.forePaysSt v R Z (fun r=> μ (2*r)) (fun r=> κ (2*r)) (P.paidₖ.tendsto_atTop.comp pu) ((Eventually.of_forall fun i:ℕ=> P.mainWindSt i).and (P.thinPays v Z.calendar)) A p (hy.comp pu)

#print axioms spendTemperSt
#print axioms roadsPaySt
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
