import GaugeFieldConstruction.AcrossProgram
import YM.SU5.FiniteGaugeData.Tapestry.Concatenation
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
local notation "D" => P.tapeDepth
local notation "C" => P.tapeᵢ
local notation "K" => P.tapeₖ
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
-- uniform quote margin buys transfer through the entire limit, all fixed-resolution
-- effect observables together, including election via any post-Register Poll.
section
variable (R:P.Register){ε:ℕ→ℝ}
variable (E:IntervalsSchedule P n v ε)
include E
open Tapestry.Fashion
abbrev columnPlan (i t:ℕ):ℕ:= P.projection.columns (circuitColumn i t)
abbrev circuitDepth (i t:ℕ):ℕ:= K (circuitColumn i t)

lemma carriedScript (q:P.shoulderTape n ε v i k): P.run.eligible i (P.run.uv k) (v (P.run.uv k)) (ε (P.run.uv k)):=by
 let t:=P.run.uv k; exact (Y).ready_mask i t _ _ (E.pay t).1 (E.pay t).2 q.2.1.1 ((Y).marketOpen _ _ q.1.1 (E.norms t)).2
lemma uniformMargin (A:P.Effect) (h:A∈shorter P.Test s) (S:BillOfWork) (b:ℝ)(H₀:Pocket P.calibration S s b A) :
    ∀ i k,P.shoulderTape n ε v i k→ s≤ (Y).uv k → ‖torqueBare P v A i k-taking Y B i k A‖≤ ε ((Y).uv k)*(cloudSpan s S*b):=by
 intro i k a u; let b':= cloudSpan s S*b; have p:0≤b':=mul_nonneg (cloudSpan_pos ..) H₀.priced; let hp:= P.at_top_limit S s _ _ H₀ i k u
 obtain ⟨z,hx⟩:=P.budgetReserve a.1.2
 unfold torqueBare; rw [← P.correct_price A h (show Pay Y s i k from ⟨a.1.2,u⟩)]; apply le_trans (AcrossLands.compare (mesh _ _ _) P.par.U _ _ (chronicleCap P i k A) (P.prim_pay A ..) z _ _ a.2.1.2 _ (hp))
 let L:= P.totalTickets i k ((Y).uv k)
 have hg: 0<L:=zero_lt_one.trans_le (P.tickets_hi ..); have hf:=E.pay ((Y).uv k); change ε ((Y).uv k)/(1+L)*(L*b')≤_
 field_simp
 nlinarith [mul_nonneg hf.1.le p]
lemma boundedMargin (A:P.Effect) (h:A∈shorter P.Test s) :
    ∃ b≥(0:ℝ), ∀ i k,P.shoulderTape n ε v i k→ s≤ (Y).uv k → ‖torqueBare P v A i k-taking Y B i k A‖≤ ε ((Y).uv k)*b:=by
 obtain ⟨S,p⟩:=anyWords P.calibration s A h; obtain ⟨b,t⟩:=issued.mp p; exact ⟨_,mul_nonneg (cloudSpan_pos ..) t.priced,uniformMargin P v E A h S b t⟩
lemma torquePrice {X:Type*}{l:Filter X}(i k:X→ℕ)(t:Tendsto k l atTop) (p:∀ᶠ n' in l,P.shoulderTape n ε v (i n') (k n'))(A:P.Effect) (h:A∈shorter P.Test s) {c:ℂ}
   (u:Tendsto (fun r=> taking Y B (i r) (k r) A) l (𝓝 c)) : Tendsto (fun r=>torqueBare P v A (i r) (k r)) l (𝓝 c):=by
 let Z:=fun r=> taking Y B (i r) (k r) A
 let g r:= torqueBare P v A (i r) (k r)-Z r
 have ht:Tendsto g l (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]; obtain ⟨b,c,hb⟩:= P.boundedMargin v E A h
    have tk:= (Y).uv_grows.tendsto_atTop.comp t; have he: Tendsto (fun i=> ε ((Y).uv (k i))*b) l (𝓝 0):= by simpa only [zero_mul, Function.comp_apply] using ((E.charged.comp tk).mul_const b)
    refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ he
    filter_upwards [p,tk.eventually_ge_atTop s] with i q d; exact hb _ _ q d
 have hp:= ht.add u; rw [zero_add] at hp; refine hp.congr (fun b=>?_); exact sub_add_cancel ..

omit E
lemma circuitMono (i:ℕ): StrictMono (P.circuitDepth i):= P.paidₖ.comp (fun _ _ h=>by
 exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (Nat.pair_lt_pair_right _ h) (by decide:0<2)) 1) 
lemma circuitSeparate (i j t s:ℕ)(h:P.circuitDepth i t=P.circuitDepth j s): i=j ∧ t=s:= Nat.pair_eq_pair.mp (by
 have p:= P.paidₖ.injective h; unfold circuitColumn at p; omega) 
lemma independentRead (i:ℕ): Tendsto (P.circuitDepth i) atTop atTop ∧ StrictMono (fun j=> P.run.uv (P.circuitDepth i j)):= ⟨(P.circuitMono i).tendsto_atTop,(Y).uv_grows.comp (P.circuitMono i)⟩
lemma budgetCircuit (q:n≤ (Y).uv k)(h:(P.run.voyage i).kick ≤ k): ReserveTape (P:=P) n i k:= ⟨(Y).givenLand ((Y).uv k) q _,h⟩
include E
lemma columnPay (i:ℕ) : ∀ᶠ k in atTop,P.shoulderTape n ε v i (P.circuitDepth i k):=by
 have p: Tendsto (P.circuitDepth i) atTop atTop:= (P.circuitMono i).tendsto_atTop
 filter_upwards [p.eventually_ge_atTop ((Y).voyage i).kick,((Y).uv_grows.tendsto_atTop.comp p).eventually_ge_atTop n] with k h e
 have t:ReserveTape (P:=P) n i (P.circuitDepth i k):= P.budgetCircuit e h; refine ⟨t,?_⟩
 have he:= P.columnIssued i k
 have hp:= (E.tape (circuitColumn i k) (he.symm ▸ t)).2; rw [he] at hp; exact hp
-- joint paths everywhere on the chosen P sequences with any columns paying old legacy.
lemma jointPays {t:ℕ→ℕ} (p:∀ᶠ i in atTop,legacy Y (P.period i) (P.circuitDepth (P.period i) (t i))) :
   let u(i:ℕ) := circuitDepth P (P.period i) (t i)
   Tendsto u atTop atTop ∧ ∀ᶠ i in atTop,P.shoulderTape n ε v (P.period i) (u i):=by
 intro u
 let g(i):= P.projection.columns (circuitColumn (P.period i) (t i)); have he:Tendsto u atTop atTop:= P.law.pick.walks (z:=g) Y B p
 refine ⟨he,?_⟩
 filter_upwards [((Y).uv_grows.tendsto_atTop.comp he).eventually_ge_atTop n,p] with i e p
 have hx:ReserveTape (P:=P) n (P.period i) (u i):= P.budgetCircuit e (P.law.pick.ticket i (g i) p);
 let c:=circuitColumn (P.period i) (t i)
 have hc:P.salesTape c=P.period i:= columnIssued ..; have ht := E.tape c (hc.symm ▸ hx); rw [hc] at ht; exact ⟨hx,ht.2⟩
lemma thinPays : ∀ᶠ r in atTop,P.shoulderTape n ε v (C (2*r)) (K (2*r)):=by
 have p:Tendsto (fun i:ℕ=>2*i) atTop atTop:= (show StrictMono (fun i:ℕ=>2*i) from by exact fun i t h=>Nat.mul_lt_mul_of_pos_left h (by decide)).tendsto_atTop
 filter_upwards [p.eventually (P.circuitPaysAt 0),(P.tape_stairs.tendsto_atTop.comp p).eventually_ge_atTop n] with r q v
 have he: ReserveTape (P:=P) n (C (2*r)) (K (2*r)):= P.budgetCircuit v q.1
 have ht:= E.tape (2*r) ((P.circleMain r).symm ▸ he); rw [P.circleMain] at ht; exact ⟨he,ht.2⟩
lemma transition_exact (i k:ℕ)(t:P.shoulderTape n ε v i k): Envelope (P.run.capFunds i (P.run.uv k) (v (P.run.uv k))) ∧ P.run.capPayment i (P.run.uv k) (v (P.run.uv k))≠0 ∧
  P.run.eligible i (P.run.uv k) (v (P.run.uv k)) (ε (P.run.uv k)):=by
 obtain ⟨p,h⟩:= P.run.marketOpen _ _ t.1.1 (E.norms _); exact ⟨p,h,P.carriedScript v E t⟩

include R
-- POLL ratio.NEW.RowTake limits follow+
lemma supportsRead (A:P.Effect) (h:A∈shorter P.Test s) :
    Sound.Couplet P.period id (fun i t=>torqueBare P v A i (P.circuitDepth i t)) (fun i=>rowTake Y B i R.exhibition A) (vistaTake Y B (P.talks R) A)
           (fun z=> ∀ᶠ i in atTop, legacy Y (P.period i) (P.circuitDepth (P.period i) (z i)))∧
    Tendsto (fun t=>torqueBare P v A (P.tapeᵢ (2*t)) (P.tapeₖ (2*t))) atTop (𝓝 (vistaTake Y B (P.talks R) A)) :=by
 let z:= Fashion.heightCoupon Y B R.exhibition s h
 constructor
 · refine ⟨fun i=>?_ , z.periods,fun u p=>?_⟩
   · have ht: StrictMono (circuitColumn i):=by intro s v h; unfold circuitColumn; exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left (Nat.pair_lt_pair_right _ h) (by decide)) 1
     let p:= P.history.growsB; exact P.torquePrice v E (fun _=>i) (fun t=> P.circuitDepth i (id t)) (P.independentRead i).1 (P.columnPay v E i) _ h ((z.inner i).comp (p.comp ht).tendsto_atTop)
   obtain ⟨a,hp⟩:=P.jointPays v E p
   exact P.torquePrice v E P.period (fun i=>P.circuitDepth (P.period i) (u i)) a hp A h (z.paths (fun k=> P.columnPlan (P.period k) (u k)) p)
 have pu:Tendsto (fun r:ℕ=>2*r) atTop atTop:= (show StrictMono (fun i:ℕ=>2*i) from by intro _ _ h; exact Nat.mul_lt_mul_of_pos_left h (by decide:0<2)).tendsto_atTop
 have hy:Tendsto (fun t=>taking Y B (C t) (K t) A) atTop (𝓝 (vistaTake Y B (P.talks R) A)):=
    by rw [← P.spirit_price R 3 (f:=A) (curve.mpr ⟨s,h⟩)]; exact P.spirits_limit R 3 A (curve.mpr ⟨s,h⟩)
 exact P.torquePrice v E (fun r=> C (2*r)) (fun r=> K (2*r)) (P.paidₖ.tendsto_atTop.comp pu) (P.thinPays v E) A h (hy.comp pu)
-- regulator expression always integrated for every participant, not just those whose limits we can transfer
omit R
lemma commerceRead (i k:ℕ)(t:P.run.permitLand i (P.run.uv k) n)(A:P.Effect) :
    let z:=P.run.uv k
    let m:= mesh ((Y).ir i) (Γ).R.L z
    let A':= chronicleCap P i k A
    let p:= P.run.meter.a z
    Integrable (inkMark (m:=mesh (P.run.ir i) P.par.R.L (P.run.uv k)) (P.run.meter.a (P.run.uv k)) (v (P.run.uv k)) P.par.U A') (city (side P.run i z)) ∧
     P.run.capPayment i z (v z)≠0 ∧ P.torqueBare v A i k = AcrossLands.position m (Γ).U p (v z) A':=by
   intro z m A' p; obtain ⟨g,h⟩:= (Y).marketOpen i z t (E.norms _); exact ⟨ink_T _ _ _ _ _ (P.prim_pay A i k) g,h,rfl⟩
#print axioms supportsRead
#print axioms jointPays
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
