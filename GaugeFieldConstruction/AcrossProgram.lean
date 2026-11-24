import GaugeFieldConstruction.AcrossProjection
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
open Dial
variable {n:ℕ}
local notation "Q"=> (Γ).J
-- `k` here is still a cutoff INDEX. (Y).uv k is a bare depth.
abbrev ReserveTape {P:Spine} (n i k:ℕ):Prop:= P.run.permitLand i (P.run.uv k) n ∧ (P.run.voyage i).kick ≤ k
abbrev salesTape (r:ℕ):= if r%2=0 then P.tapeᵢ r else (Nat.unpair (r/2)).1

def circuitColumn (i r:ℕ):= 2*Nat.pair i r+1
lemma columnIssued (t j:ℕ) : salesTape P (circuitColumn t j)=t:=by
  let p:= Nat.pair t j; have v:¬circuitColumn t j%2=0:=by unfold circuitColumn; omega
  have ht : circuitColumn t j/2=p:=by unfold circuitColumn p; omega
  rw [salesTape,if_neg v,ht,Nat.unpair_pair]
lemma circleMain (r:ℕ): salesTape P (2*r)=P.tapeᵢ (2*r):=by unfold salesTape; rw [if_pos (by omega)]

noncomputable abbrev currencyRow (i k:ℕ)(u:ℝ):Orbit (side P.run i (P.run.uv k))→Phys (side P.run i (P.run.uv k)):= normalized (mesh ((Y).ir i) (Γ).R.L ((Y).uv k)) (Γ).U ((Y).meter.a ((Y).uv k)) u

def quoteCap (ε:ℕ→ℝ) (u:ℝ) (i k:ℕ) : Prop :=
    |u-P.run.headIn i (P.run.uv k)| ≤ ε (P.run.uv k)/2 ∧
    ∀ x:Orbit (side P.run i (P.run.uv k)), ‖P.currencyRow i k u x - P.currencyRow i k (P.run.headIn i (P.run.uv k)) x‖ ≤ ε (P.run.uv k)/(1+P.totalTickets i k (P.run.uv k))

abbrev quoteMargin (ε:ℕ→ℝ)(u:ℝ)(i k:ℕ): Prop:= P.quoteCap ε u i k∧ P.run.owedTape i (P.run.uv k) u (ε (P.run.uv k)) (ε (P.run.uv k)/(1+P.totalTickets i k (P.run.uv k)))
-- Still only *one measurement* period for each cutoff index where the new prescription
-- must pay Transfer. On all periods, normalization. On each fixed period there is now its own
-- genuine UV subpath, paying the entire family. Distinct i have disjoint subpaths. No claim
-- of physical measurement limits over every large k at fixed volume, nor over every large m
-- at fixed cutoff. Where we've proved genuinely many periods with approximate *physical*
-- terminal at once at the same depth, those periods aren't required to be in the legacy cone
-- and we have not paid the limiting ratios out there.

abbrev shoulderTape (n:ℕ)(ε v:ℕ→ℝ)(i k:ℕ):Prop:= ReserveTape (P:=P) n i k ∧ quoteMargin P ε (v (P.run.uv k)) i k
structure IntervalsSchedule (P:Spine) (n:ℕ) (v:ℕ→ℝ) (ε:ℕ→ℝ):Prop where
 land : Territory P.par.K P.par.J n
 positive_p : 0<P.par.x
 gk(k:ℕ): 0<v k
 interior_all(k:ℕ): Py.Rate.entersReal (Vale.hat P.par.R.L P.par.x k) (v k)
 norms(k:ℕ): CompleteMask (p:=P.run.meter.a k) P.par.J n (v k)
 tape(r:ℕ)(s:ReserveTape (P:=P) n (P.salesTape r) (P.tapeₖ r)):
    P.run.headIn (P.salesTape r) (P.tapeDepth r) < v (P.tapeDepth r) ∧
    quoteMargin P ε (v (P.tapeDepth r)) (P.salesTape r) (P.tapeₖ r)
 pay (r:ℕ): 0<ε r ∧ ε r < Py.Rate.Branch.Rx P.par.x
 charged : Tendsto ε atTop (𝓝 0)
 frequent_empty : ∃ᶠ k:ℕ in atTop, ¬ ∃ r, P.tapeDepth r=k
 spares (k:ℕ)(h:¬∃ r, P.tapeDepth r=k) : ∃ᶠ i in atTop,P.run.eligible i k (v k) (ε k)

abbrev torqueBare (A:P.Effect)(i k:ℕ):ℂ:= consultPrice P A i k (v ((Y).uv k))
section
variable (Λ:Territory P.par.K P.par.J n)
lemma budgetReserve (h:((Y).voyage i).kick≤k) :
   Envelope ((Y).capFunds i ((Y).uv k) ((Y).headIn i ((Y).uv k))) ∧
   (Y).capPayment i ((Y).uv k) ((Y).headIn i ((Y).uv k))≠0 :=by
 constructor
 · have he:= ((Y).history i k).hot (Γ).V _ (Γ).J Chi.canonical (Γ).h (Γ).direct; obtain ⟨T,h⟩:=he; rw [funext h] at T; exact T
 have hw:= Tapestry.funds (f:=1) Y ((Y).uv k) i k (AtSupport.oneM (n:=side P.run _ _) ∅).env h le_rfl; have he:=hw.2.1; rw [partitionZ,funext ((Y).whole i k)] at he; exact he
lemma paid_interior {u ε₀:ℝ} (E:P.run.eligible i k u ε₀) : Py.Rate.entersReal (hat P.par.R.L P.par.x k) u:=by
 obtain ⟨b,h,⟨t,ht⟩⟩:=E
 obtain ⟨-,_,c,_,Hu⟩:= ht; rw [←c]; exact (Hu k le_rfl).1

include Λ
variable {ε:ℕ→ℝ}
lemma perfume (i k:ℕ)(he:ReserveTape (P:=P) n i k)(hp:∀ k,0< ε k∧ ε k<Py.Rate.Branch.Rx P.par.x):
    ∃ u, (Y).headIn i ((Y).uv k)<u ∧ CompleteMask (p:=(Y).meter.a ((Y).uv k)) P.par.J n u ∧ quoteMargin P ε u i k ∧ (Y).eligible i ((Y).uv k) u (ε ((Y).uv k)):=by
 obtain ⟨g,h⟩:=P.budgetReserve he.2
 let b:= (Y).headIn i ((Y).uv k); let z:=(Y).uv k; have ht:= hp z; let V:= P.totalTickets i k z
 have hs:0 < ε z /(1+V):=by have he:0<V:= zero_lt_one.trans_le (tickets_hi P ..); exact div_pos ht.1 (by positivity)
 have ht':∀ᶠ u:ℝ in 𝓝 b, quoteCap P ε u i k:=by
    filter_upwards [Icc_mem_nhds (by linarith [ht.1] : b-ε z/2<b) (by linarith [ht.1] : b < b+ε z/2),stable_price (mesh ((Y).ir i) (Γ).R.L z) (Γ).U _ _ g h _ hs] with u e w
    refine ⟨?_,fun x=> (w x).le⟩; change |u-b|≤ε z/2; exact abs_le.mpr ⟨by linarith [e.1],by linarith [e.2]⟩
 obtain ⟨u,U,e'⟩:=Metric.mem_nhds_iff.mp ht'
 obtain ⟨δ,v,hV⟩:= (Y).readyTrunk i z _ _ ht.1 hs h
 let Dℓ:=min δ u; have hv:0<Dℓ:= lt_min v U
 obtain ⟨t,p,q,s⟩:= choose_paying P.par.direct Λ ((Y).meter.a z) ((((Y).voyage i).paths z).paid.can.pole z) (lt_add_of_pos_right b hv)
 have hδ0:|t-(Y).headIn i z|< Dℓ:=by apply abs_lt.mpr; constructor<;> linarith
 have hx:quoteCap P ε t i k:= e' (Metric.mem_ball.mpr (by rw [Real.dist_eq]; exact lt_of_lt_of_le hδ0 (min_le_right ..)))
 have hg:= (Y).marketOpen i z he.1 s
 exact ⟨t,p,s,⟨hx,hV _ (le_trans hδ0.le (min_le_left ..)) hg.2⟩,(Y).ready_mask i z _ _ ht.1 ht.2 hx.1 hg.2⟩

omit Λ
lemma coinsInfinite : ∃ᶠ k:ℕ in atTop, ¬∃ r, P.tapeDepth r=k := by
 have h:∀ r, P.tapeDepth (r+1) ≥ P.tapeDepth r + 2:= by
   intro r; let f:=fun r=> (Y).ivory (K r); have hf:f r<f (r+1):= ((Y).UV.comp (P.paidₖ)) (by omega)
   change (f r)^4+f r+1+P.par.b+2≤ (f (r+1))^4+f (r+1)+1+P.par.b; have hv: (f r)^4<(f (r+1))^4:= Nat.pow_lt_pow_left hf (by omega); omega
 apply frequently_atTop.mpr; intro t; obtain ⟨r,e⟩:= (P.tape_stairs.tendsto_atTop.eventually_ge_atTop t).exists; refine ⟨D r+1,by omega,?_⟩; rintro ⟨s,p⟩; have e:=P.tape_stairs.lt_iff_lt.mp (show D r < D s by omega); have he:= (h r).trans (P.tape_stairs.monotone (Nat.succ_le_iff.mpr e)); omega

include Λ
local notation "q" r:max => P.salesTape r
lemma compileSchedule (p:∀ k,0< ε k∧ ε k<Py.Rate.Branch.Rx P.par.x)(h:Tendsto ε atTop (𝓝 0)): ∃ v, IntervalsSchedule P n v ε:=by
 let Rne:= ReserveTape (P:=P) n
 have Hβ (k:ℕ):∃ t>0,
             entersReal (hat P.par.R.L P.par.x k) t ∧
             CompleteMask (p:=(Y).meter.a k) P.par.J n t ∧
             (∀ r,D r=k→Rne (q r) (K r)→ (Y).headIn (q r) (D r)<t ∧ quoteMargin P ε t (q r) (K r)) ∧
             ((¬∃ r,D r=k) → ∃ᶠ i in atTop,(Y).eligible i k t (ε k)):=by
   by_cases e: ∃ r,D r=k ∧ Rne (q r) (K r)
   · obtain ⟨r,rfl,v⟩:=e; obtain ⟨u,hc,p,w,ω⟩:=P.perfume Λ (q r) (K r) v p; exact ⟨u,((Y).headCost ..).trans hc,P.paid_interior ω,p, fun t X e=> P.tape_stairs.injective X ▸ ⟨hc,w⟩,fun e=>False.elim (e ⟨r,rfl⟩)⟩
   obtain ⟨u,h,t,f⟩:= (Y).common_places k Λ _ (p _).1 (p _).2; obtain ⟨i,y⟩:=f.exists; exact ⟨u,h,P.paid_interior y,t,fun r v w=> False.elim (e ⟨r,v,w⟩),fun _=> f⟩
 choose V hV hp H T hv using Hβ; exact ⟨V,Λ, (zero_lt_one.trans_le P.run.oneP),hV,hp,H,fun r p=>T (D r) r rfl p,p,h,coinsInfinite P, hv⟩
lemma lowering : ∃ ε v, IntervalsSchedule P n v ε:=by
 let t:=Py.Rate.Branch.Rx P.par.x; have h:0<t:= Py.Rate.Branch.Rx_pos P.run.oneP; let ε:=fun k:ℕ=> t / (k+2)
 refine ⟨ε, P.compileSchedule Λ (ε:=ε) (fun k=>?_ ) ?_⟩
 · unfold ε; constructor
   · positivity
   exact div_lt_self h (by linarith [Nat.cast_nonneg (α:=ℝ) k])
 exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
#print axioms paid_interior
#print axioms perfume
#print axioms lowering
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
