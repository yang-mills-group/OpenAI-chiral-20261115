import SatinThinHalo
import SatinThinRow

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
/-! # Fix ranks independently of layout and period. Extract for every *fixed* v from very same P (no law mutation). -/
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
variable {A C U:ℝ}
/-! # Calibration may be simultaneous for every ordered pair of past stations, PLUS retain bounded price from another starting height. -/
-- bound **in orientation that buys a(r0) times any cost**.
lemma capital_bound (θ: ℕ→ ℝ)(p:∀ r:ℕ,f ≤ r → r < v → |θ r| ≤ zoomC P.par.R.L*|θ (r+1)|)(y:f ≤ r)(a:r ≤ s)(u:s≤v): |θ r| ≤ zoomC P.par.R.L^(s-r)*|θ s| :=by
 induction a with
 | refl=> simp
 | @step m hm ih=> change r ≤ m at hm; refine (ih (le_trans (Nat.le_succ _) u)).trans ?_; rw [show m+1-r=(m-r)+1 from by omega,pow_succ,mul_assoc]; exact mul_le_mul_of_nonneg_left (p m (y.trans hm) u) (pow_nonneg (zero_le_one.trans (zoomC_p _)) _) -- hm u: m<v defeq
lemma ratio_bound {x y a b k:ℝ}(p: |x-1|≤1/4)(q: |y-1|≤1/4)(h:0≤k)(t:|a| ≤ k * |b|) : |x*a| ≤ 4*k*|y*b|:=by
 rw [abs_mul,abs_mul]; obtain ⟨e,w⟩:=abs_le.mp p; obtain ⟨u,v⟩:=abs_le.mp q; have hv: |x|≤2:=abs_le.mpr ⟨by linarith only [e],by linarith only [w]⟩; have he:1/2 ≤ |y|:=le_trans (by linarith only [u]) (le_abs_self y); apply (mul_le_mul hv t (abs_nonneg _) (by norm_num)).trans; calc
   _ = 4*k*((1/2)*|b|) := by ring
   _ ≤ _ := by gcongr
/-- tab ALL eligible at every request (countable, compact convergence actual a posteriori). -/
structure chargeSpan (f v:ℕ)(p:ℕ×ℕ):Prop where
 after : f≤p.1
 before : p.1 < p.2
 during : p.2 ≤ v
local notation "Tier"=>ℕ × ℕ
local notation "Wt" z:max p:max q:max => zoomC z ^((q:Tier).2 - (p:Tier).2)
structure Workforce (A C:ℝ)(f v:ℕ)(P:Spine)(c:ℕ→Tier→ℝ)(a:Tier→ℝ)(l:ℕ→ℕ):Prop where
 plans(p:Tier)(h:chargeSpan f v p) : lender A C p.1 p.2 v (fun i=> c i p) (a p) l P
 career (p q: Tier)(h:chargeSpan f v p)(u:chargeSpan f v q)(y:p.2 ≤ q.2): |a p| ≤ 4*(zoomC P.par.R.L)^ (q.2-p.2)*|a q|
def wageRow (i:ℕ)(q:Tier→ℝ)(f v:ℕ)(P:Spine)(A:ℝ): Prop:= (∀ p:Tier,∀ y:chargeSpan f v p,P.cradle p.2 v (q p) ∧ P.fundsDay (A:=A) y.before.le y.during i (q p)) ∧
   (∀ p d:Tier,chargeSpan f v p→chargeSpan f v d→ p.2 ≤ d.2 → |q p| ≤ 4* Wt P.par.R.L p d *|q d|) ∧ ∀ p:Tier, |q p| ≤ 2*fareMax P.par.R.L (v-p.2)
local notation "g(i)"=>P.run
lemma wage_earn (t:Credentials P.run (P.nomadic i) (P.engine i) A f v) : ∃ q:Tier→ℝ, wageRow i q f v P A:=by
 obtain ⟨b,h,t₂⟩:= capital_theta P.run (P.nomadic i) (P.engine i) t.scope t
 let q₀(x:Tier)(z:ℝ):= |z-1|≤1/4∧ ∀ y:chargeSpan f v x, ∃ b₁:ℝ, ReadDensity P.run (P.nomadic i) (P.engine i) A y.before.le y.during (b x.2) z b₁
 have he(x:Tier):∃ z,q₀ x z:=by
   by_cases p:chargeSpan f v x; swap; · exact ⟨1,by norm_num,fun t=>(p t).elim⟩
   let u:= t.part P.run (P.nomadic i) (P.engine i) p.after (p.before.le.trans p.during) le_rfl; let V:= h x.2 (p.after.trans p.before.le) p.during
   obtain ⟨z,d,a⟩:= full_clock _ _ _ p.during V p.before.le u; exact ⟨z,eddy_small _ _ a.amplitude,fun _=>⟨d,density_earn _ _ _ _ _ _ _ p.before u a⟩⟩
 choose a e using he
 let c (x:Tier):=a x * b x.2
 classical
 let q(x:Tier):= if chargeSpan f v x then c x else 0
 have hc{x:Tier}(p:chargeSpan f v x): q x=c x:= if_pos p -- if _ Prop classical used by notation above local
 have hp(x:Tier)(p:chargeSpan f v x): P.cradle x.2 v (c x):= P.crests_mark (h _ ((show chargeSpan f v x from p).after.trans p.before.le) p.during).aims (e x).1
 refine ⟨q,fun p y=>?_ , fun x z y v k=>?_, fun p=>?_⟩
 · obtain ⟨w,g⟩:= (e p).2 y; rw [hc y]; exact ⟨hp p y,b p.2,a p,w,(e p).1,g,rfl⟩
 · rw [hc y,hc v]; exact ratio_bound (e x).1 (e z).1 (pow_nonneg (zero_le_one.trans (zoomC_p _)) _) (P.capital_bound b t₂ (y.after.trans y.before.le) k v.during)
 by_cases h:chargeSpan f v p; · rw [hc h]; exact (hp p h).1
 have hv:q p=0:= if_neg h; rw [hv,abs_zero]; unfold fareMax; exact mul_nonneg (by norm_num) (pow_nonneg (zero_le_one.trans (zoomC_p _)) _)
lemma wardBank (_u:f ≤ v) (W₀:∀ r:ℕ,∀ z:ℕ,f ≤ r → r < z → z ≤ v → treasury A C P r z v)(G:∀ᶠ i:ℕ in atTop, Credentials P.run (P.nomadic i) (P.engine i) A f v):
    ∃ (c:ℕ→Tier→ℝ) (a:Tier→ℝ) (l:ℕ→ℕ), Workforce A C f v P c a l:=by
 classical
 let c(i:ℕ):=if p:Credentials P.run (P.nomadic i) (P.engine i) A f v then Exists.choose (P.wage_earn p) else (0: Tier→ℝ); have U:∀ᶠ i:ℕ in atTop,wageRow i (c i) f v P A:=by
    filter_upwards [G] with i h; unfold c; rw [dif_pos h]; exact Exists.choose_spec (P.wage_earn h)
 let d(p:Tier):= 2*fareMax L (v-p.2)
 obtain ⟨a,t,l,v0,he⟩:= (isCompact_pi_infinite (ι:=Tier) (X:=fun _=>ℝ) (fun p=> isCompact_Icc (a:=-d p) (b:=d p))).isSeqCompact.subseq_of_frequently_in ((U.mono fun z i=> (show ∀ p:Tier,c z p∈Set.Icc _ _ from fun p=> abs_le.mp (i.2.2 p))).frequently) -- tune argument membership coercion
 have h(p:Tier): Tendsto (fun i=>c (l i) p) atTop (𝓝 (a p)):= tendsto_pi_nhds.mp he p; have hv:= (v0.tendsto_atTop.eventually U)
 refine ⟨c,a,l,fun p y=>⟨W₀ _ _ y.after y.before y.during, ⟨abs_le.mpr (t p),ge_of_tendsto ((h p).abs.const_mul _) (hv.mono fun _ t=>(t.1 p y).1.2)⟩,v0,U.mono fun z i=>i.1 p y,h p⟩ ,fun p q y v₀ θ=>?_⟩ -- parent comma group structural
 exact le_of_tendsto_of_tendsto ((h p).abs) ((h q).abs.const_mul _) (hv.mono fun _ t=>t.2.1 p q y v₀ θ)
lemma auditsCalendar (Y0:∀ᶠ f:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ, (P.run.voyage i).kick ≤ k→f ≤ P.run.uv k→ShelterCost C P.run f i k)(Y1:Chronicle P.run A):
 ∀ᶠ f:ℕ in atTop,∀ v:ℕ, f≤v →∃ c a l, Workforce A C f v P c a l:=by
 filter_upwards [eventually_forall_ge_atTop.mpr (P.treasury_plot A C Y0 Y1), elected_everywhere P.run Y1] with f h t v u
 refine P.wardBank u (fun r s y w k=> h r y s w v k) ?_; filter_upwards [P.history.finance v,P.stockGo.eventually (t v u)] with i h p; exact p _ h.depth h.enters
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.auditsCalendar
