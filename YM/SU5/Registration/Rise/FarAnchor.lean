import YM.SU5.Registration.Rise.Flying
import YM.SU5.Registration.Rise.StowAt
import YM.SU5.Registration.Rise.GranuleSpace
import YM.SU5.Registration.Rise.Rally
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
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
open Worth Pays CF.BProof

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)

/-! # Operator at ANY heated presentation

Maps from fields at a fixed anchor into a taller stage (ruler-overlap fixed) are
in H and are contractive; can pass to ALL matter-free clock leaves in one
norm estimate. When the allowance is spent at both ends the opening line is
operator-norm priced; the screenings at nonaligned points depend on mesh, but
transfer out of mesh on MANY-F via its spatial continuity. Then get Strong Star Cauchy
on the sequence of managed granules.
-/
open Germ Alliance
open _root_.YM.SatinRegistration
variable (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x j
local notation "X'"=> P.ColorHil j ξ
local notation "G"=> P.ManyF j ξ
local notation "U"=> P.truck j ξ
local notation "E"=> (P.physicalEnergy j ξ).E
local notation "S"=> P.seasons j ξ
local notation "E'" => (S).E
local notation "T'"=>timeMesh P.par
local notation "α" s:max n:max => whenly (timeMesh P.par) s n
local notation "π" => P.toStageG j ξ
variable (g h:ℕ)(l:List Axis) (a:ℕ→(ℕ×ℕ)→ℝ)(v':ℕ→ℕ)
local notation "s!"=> P.rootSpace g f l
local notation "p!" n:max=> P.quoteSpot g f l n
local notation "O" f:max=>P.rowClock j g f l
local notation "π'" n:max=> P.basePlay x g n
local notation "D" n:max=> (P.basePlay x g n).pivot P l
local notation "c₀"=>ℕ -- remove
local notation "z₀" v:max=> (Z f v (O f))
local notation "Z'" v:max=> P.bedCase j (P.rootSpace g f l) x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) v
local notation "Cκ" v:max=> (Z' v).charges ξ (P.calendarZ v f (O f) (Nat.succ_pos _))
local notation "κ" => P.cartage j ξ
local notation "ℓ₁" v:max=> ((p! v) j).toNat -- parser ℓ! not p! max!!
local notation "λκ" v:max=> (p! v)
private lemma flying_cart {X:ℕ→Vantage}{Y':Vantage}(e:Tendsto X atTop (𝓝 Y')) : Flying (H:=G) (fun i:ℕ=>κ (X i)) (κ Y'):=by
 intro u; simp_rw [P.cart_reverses]; exact ⟨((P.cart_cont ..).tendsto _).comp e, ((P.cart_cont ..).tendsto _).comp e.neg⟩

private def throughCab (L':Hilbert)(A B C D':L'.Op): L'.Op→L[ℂ] L'.Op:=
 (ContinuousLinearMap.compL ℂ L' L' L' (A*B)).comp ((ContinuousLinearMap.compL ℂ L' L' L').flip (C*D')) -- L'.space vs L'

-- avoids norm continuity of inner map. continuation at raised level argument before
-- spending projections in `Some`.
noncomputable def pitCab (f s:ℕ)(t:ℝ≥0) : (X').Op →L[ℂ] (X').Op:=
 let p:= P.quoteSpot g f l s
 let Δ:= whenly (timeMesh P.par) s ((p j).toNat)
 throughCab X' (P.truck j ξ (-(P.vtile s p))) ((P.physicalEnergy j ξ).E (t-Δ)) ((P.physicalEnergy j ξ).E (t+Δ- (whenly (timeMesh P.par) f (P.rowClock j g f l)))) (P.truck j ξ (P.vtile s p))

local notation "J" s:max t:max=> P.pitCab j x g l f s t
lemma pit_reads (t:ℝ≥0)(A:(P.ColorHil j (P.advocate 3 x j)).Op): (J v t) A=P.charter j ξ (-(P.vtile v (p! v))) (E (t-(α v (ℓ₁ v))) * A * E (t+(α v (ℓ₁ v))-(α f (O f)))):=by
 let w₀:=P.vtile v (p! v); let D₀:= E (t-(α v (ℓ₁ v))); let D':= E (t+(α v (ℓ₁ v))-(α f (O f))); unfold charter; rw [neg_neg]
 change ((U (-w₀)) * D₀) * (A * (D' * (U w₀))) = (U (-w₀))* ((D₀ * A * D')* (U w₀))
 simp only [mul_assoc]
lemma pit_pay (t:ℝ≥0)(A:(P.ColorHil j (P.advocate 3 x j)).Op): ‖P.pitCab j x g l f v t A‖ ≤ ‖A‖:=by rw [P.pit_reads]; exact (P.charter_pay ..).trans (P.heater_norm ..)

variable (Y₀:P.NightCop) (L':Odd P.par.R.L.val) (D₀:Earnings P A C g h v' a)
local notation "T" v:max=> (a v (g,h):ℂ)
local notation "b!" v:max=> (a v (f,r):ℂ)
noncomputable def subsidizedH (t:ℝ≥0)(v:ℕ): (P.ColorHil j (P.advocate 3 x j)).Op:=
 ((a v (g,h):ℝ):ℂ) • P.stageH j ξ ((P.basePlay x g (v' v)).pivot P l) t t

local notation "Ξ" r:max v:max t:max=> (J (v' v) t) (Cκ r)
local notation "λ₀" f:max r:max v:max=> subsidy g h f r v a
noncomputable def approxCab (f r:ℕ)(t:ℝ≥0)(v:ℕ) := ((subsidy g h f r v a:ℝ) :ℂ) • P.pitCab j x g l f (v' v) t ((P.bedCase j (P.rootSpace g f l) x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) r).charges ξ (P.calendarZ r f (O f) (Nat.succ_pos _))) -- check hygiene shadow f note O f macro f argument passed OK
local notation "pC" r:max t:max i:max=> P.approxCab j x g h l a v' f r t i
local notation "Z₀" t:max i:max=> P.subsidizedH j x g h l a v' t i
local notation "D'" f:max=>6*tiltBase P.par A f
noncomputable abbrev skyLoss (P:Spine)(A:ℝ)(f r h:ℕ): ℝ := avail P.par.R.L h r * (2*(6*tiltBase P.par A f/(zoomM P.par.R.L ^(r-f))))
variable (p:h≤ f)(b0:f<r)
private lemma subsidy_money (X:Hilbert)(A B:X.Op)(k μ' c:ℝ)(h:k*μ'=c)(f:X.Op→L[ℂ]X.Op)(Y':X.Op)(u:Y'=f A): (c:ℂ) • Y' - (k:ℂ) • f B=(k:ℂ) • f ((μ':ℂ) • A - B):=by rw [u,map_sub,map_smul,smul_sub,smul_smul,←Complex.ofReal_mul,h]
include p b0 Y₀ L' D₀
lemma relative_pit 
    (Yκ:P.ColumnBill (P.rowClock j g f l) f) (t:ℝ≥0)(gF:α f (O f)≤ t) : ∀ᶠ i:ℕ in atTop, ‖(Z₀ t i)-(pC r t i)‖ ≤ skyLoss P A f r h:=by
 let hG:= D₀.earlier.le.trans p; let K:= D₀.fast.tendsto_atTop
 filter_upwards [K.eventually_ge_atTop r,K.eventually (P.quote_fits j x g l hG L')] with i y w
 let v:= v' i; let t':= P.bedCase j (P.rootSpace g f l) x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1)
 let g':= P.calendarZ r f (O f) (Nat.succ_pos _); let δ:= a i (f,r); let A':= Cκ r; let B:= Cκ v; let C':= P.pitCab j x g l f v t; let k:= subsidy g h f r i a; obtain ⟨u',π0⟩:= D₀.gift hG b0 p y
 obtain ⟨g₁,v₁,h₁⟩:= D₀.pick hG b0 y
 have he:‖(δ:ℂ) • B-A'‖ ≤ 2*(6*tiltBase P.par A f/(zoomM P.par.R.L^(r-f))):= P.gap_center j (P.rootSpace g f l) x (O f) (P.rent_honors j g f l) (Nat.le_add_right _ 1) (Nat.succ_pos _) h₁ Yκ Y₀ b0.le y
 have hz: P.stageH j ξ (D v) t t=C' B:= by
    let e: f≤v:=b0.le.trans y; rw [P.stowed j 0 x g 0 l _ t w (P.quote_spot_agrees g l hG L' e) gF e]; exact (P.pit_reads ..).symm
 have hV: (Z₀ t i)-(pC r t i)= (k:ℂ) • (C' ((δ:ℂ) • B - A')):=subsidy_money X' B A' k δ (a i (g,h)) π0 C' _ hz
 rw [hV,norm_smul,Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul u' ((P.pit_pay ..).trans he) (norm_nonneg _) ((abs_nonneg k).trans u')
omit Y₀
-- `pitFlies` after projection. No gap income here.
lemma approxFlies (p0:PaidSubsidy g h a) (t:ℝ≥0) : Travels (H:=G) (fun i=> P.toStageG j ξ (pC r t i)):=by
 obtain ⟨k,y⟩:= cauchySeq_tendsto_of_complete (p0 f r (D₀.earlier.le.trans p) p b0); let v:= (Cκ r)
 have hz:Tendsto (fun i=> (↑(subsidy g h f r i a):ℂ)) atTop (𝓝 (k:ℂ)):= Complex.continuous_ofReal.continuousAt.tendsto.comp y
 let w:= α f (O f); let α₀(i:ℕ):= α (v' i) (( (P.quoteSpot g f l (v' i)) j).toNat); let α':= (P.pinTime j g f l).toNNReal
 have hp:Tendsto α₀ atTop (𝓝 α'):= (P.quote_time_val j x g l (D₀.earlier.le.trans p) L').comp D₀.fast.tendsto_atTop
 let g₀(i:ℕ):=P.laysM (P.vtile (v' i) (λκ (v' i))); let u:Vantage:= fun j=>P.pinTime j g f l
 have he:Tendsto g₀ atTop (𝓝 u):=(P.quote_moving g l (D₀.earlier.le.trans p) L').comp D₀.fast.tendsto_atTop
 let Yz:= κ (-u) * (E' (t-α') * (π v) * E' (t+α'-w))*κ u; let z:= (k:ℂ) • Yz;
 have hh: Flying (H:=P.ManyF j (P.advocate 3 x j)) (fun i=>P.toStageG j ξ (pC r t i)) z:=by
    let A' := Flying.still (π v)
    have p:Earnings P A C g h v' a:=D₀
    have hy:= (Flying.heat (S) ((tendsto_const_nhds (x:=t)).sub hp)).multiply A'; have hu:= hy.multiply (Flying.heat (S) (((tendsto_const_nhds (x:=t)).add hp).sub (tendsto_const_nhds (x:=w))))
    refine Flying.late (Flying.scaled hz (((P.flying_cart j x he.neg).multiply hu).multiply (P.flying_cart j x he))) (Eventually.of_forall fun i=>?_)
    let W₀:= λκ (v' i); let P₀:=P.vtile (v' i) W₀
    change ((λ₀ f r i):ℂ) • (κ (-(g₀ i))* (E' (t-α₀ i)*(π v)* E' (t+α₀ i-w)) * κ (g₀ i))=π (((λ₀ f r i):ℂ) • Ξ r i t); rw [map_smul,P.pit_reads,P.charter_toG,neg_neg,P.lays_neg,P.bank_both]; try rfl
 exact hh.Cauchy
omit D₀ L' p b0 in
lemma sky_zero (A:ℝ)(p:h≤f): Tendsto (fun n:ℕ=> skyLoss P A f (f+(n+1)) h) atTop (𝓝 0):=by
 let k:= zoomC P.par.R.L; let K:= zoomM P.par.R.L; have hK:0<K:=zoomM_p _; have hk:0<k:= zero_lt_one.trans_le (zoomC_p _)
 have hkK:k<K:=by have ht:= P.par.R.L.property; unfold k K zoomC zoomM; nlinarith only [show 0<((L).val:ℝ)^4 by positivity]
 let d:= zoomC P.par.R.L/zoomM P.par.R.L; have hp : Tendsto (fun n:ℕ=> d^(n+1)) atTop (𝓝 0):= (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hk hK|>.le) ((div_lt_one hK).mpr hkK)).comp (tendsto_add_atTop_nat 1)
 let B:= tiltBase P.par A f; let t:=4*k^(f-h)*(2*(6*B)); have he:= hp.const_mul t; rw [mul_zero] at he; refine he.congr fun i=> ?_
 unfold skyLoss avail; rw [show f+(i+1)-h=f-h+(i+1) from by omega,Nat.add_sub_cancel_left,pow_add (zoomC P.par.R.L) (f-h)]; unfold d t; change 4*k^(f-h)*(2*(6*B))*(k/K)^(i+1)=4*(k^(f-h)*k^(i+1))*(2*(6*B/K^(i+1))); rw [div_pow]; ring
-- remove ledger treasury here. apply
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.relative_pit
#print axioms Spine.approxFlies
#print axioms Spine.sky_zero
