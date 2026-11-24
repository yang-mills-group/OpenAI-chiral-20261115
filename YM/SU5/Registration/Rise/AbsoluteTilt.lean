import YM.SU5.Registration.Rise.Appraise
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
local notation "H"=>P.large
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

/-! # Absolute (not connected) clover prices. For polynomial cap bound need only
r=f+1. Use grant for `PaysTilt` with r=r, i.e. use `Premier` estimates in
that clock. Lender returns income only on the Gap cost. DO NOT get from just
his `fundsDay`. -/
local notation "U₁" s:max=> P.visitOne s (P.clockPlate f s X)
local notation "n₀" s:max=>frameOne (P.clockPlate f s X)
local notation "G₀" => plusAgain P.par.block (P.labW f)
local notation "qΦ"=> 3*tiltBase P.par A f
local notation "Bβ"=> (fareMin (L) (v-f))
variable (w:ℕ) (p:Plans j X f P)(hw:0<w)(c0:twiceT X j ≤ w)
variable (T':treasury A C P f v v)(vCap:P.ColumnBill w f)(PZ:P.NightCop)
include p hw c0 vCap PZ T'
lemma books_raw : ClockBooking.Issues Y H v j (Z f v w) id P.history (fun _=> (U₁ v).val) (3*tiltBase P.par A f *fareMin (L) (v-f)):=by
 let W':= (U₁ v).val; let q:=(qΦ); have ht:0<q:= mul_pos (by norm_num) (P.tilt_pos T')
 have he:TestFamily W true W':=aux_test P.basesT
 let f':= T'.price.le
 obtain ⟨D,hD⟩:= Journey.valuation Y H (show InTest W true (n₀ v) false W' from P.basesT)
 have h0:0≤D:= Tower.pay_nonneg (F:=W') hD -- F notation!? escape
 let D':= fareMax P.par.R.L (v-f)*D
 have hp:Tendsto (fun i:ℕ=> ((Journey.side P.run (P.nomadic i) v).val:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp (P.amount_go v)
 filter_upwards [P.history.finance v,T'.room,(P.amount_go f).eventually_ge_atTop G₀,hp.eventually_ge_atTop (D'*(16/(tiltBase P.par A f))),PZ v] with i hv m' cΩ hA bΩ n a t V Hf
 let k:=P.engine i; let u:= P.nomadic i; let X':= wrap (side Y u f) X; let Z':= RootBook Y u k f
 obtain ⟨b,z,q',x,y,x0,hx,_⟩:=m'.1.reading -- order
 let U:= earlyLeaf Y u k b q' f'
 let η:= q'*b
 have hb: Premier L 0 b:= (show v-v=0 from Nat.sub_self _) ▸ y.aims
 have hq: Premier L (v-f) q':= x0.breath
 have hη : η≠0:= mul_ne_zero hq.nz hb.nz
 have hU: distribute Y H v u ((η:ℂ) • W')=U X':=by
    unfold η U earlyLeaf Yoke.principal; rw [Complex.ofReal_mul,mul_smul,(distribute_arith Y H v u _ 0 (q':ℂ)).2.2.1]; exact congrArg ((q':ℂ) • ·) (show distribute Y H v u ((b:ℂ) • W')=_ from P.eerieT (i:=i) (P.high_root f' X).symm hv.enters b)
 have hF:pay ((η:ℂ) • W') D':=by
    have ha : |b| ≤ 1:=by simpa [fareMax] using hb.big
    have hq: |η|≤ fareMax (L) (v-f):=(abs_mul ..).trans_le ((mul_le_of_le_one_right (abs_nonneg _) ha).trans hq.big)
    intro s x; refine (pay_scale (show pay W' D from hD) (η:ℂ) s x).trans ?_; rw [Complex.norm_real,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right hq h0
 have hW:repeatD Λ P.width Z'.p.B=P.labW f:=congrArg (repeatD Λ P.width) (congrArg BudgetPoint.B (Papal.prices_plot P.run f u k (le_trans f' hv.enters)).1)
 obtain ⟨y',t'⟩:= P.lands_at f' (i:=u) (m:=n) V Hf
 have hf:= long_line_issues (P.run) u k j H hv f' m'.2 (f:=f) (w:=w) (A:=A) (by rw [hW]; exact vCap) (by rw [hW]; exact cΩ) U bΩ (D:=D') hA (fun l=> jewel_envelope Y u k l f') (graceful_jewel Y u k H hv f' Z'.p.B) (fun l w=> jewel_ticket Y u k f' (r:=v) (v:=v) le_rfl m'.2 hx l w) X (by rw [hW]; exact p.seat) (by rw [hW]; exact (P.clock_fit j X p c0).1) _ (he.scale _) hU hF t hw y' t' a
 let ω:ℤ:= ((L).val:ℤ)^(v-f)*w; let ω':ℤ:= ω*a; let r:=4*n
 let Z0:= SlabMark.banner j ω ω' n W'
 let σ(y:Family W):= Journey.sharp Y H v u k y
 rw [← mul_assoc (↑(L).val^(v-f):ℤ), ClockBooking.banner_real, Tower.sharp_scale,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs] at hf
 change |η|^r * ‖σ Z0‖≤ q^r at hf
 change ‖σ (SlabMark.banner j (Z f v w) ((↑(Z f v w):ℤ)*a) n W')‖ ≤ (q*_)^ _; rw [show (↑(Z f v w):ℤ)=ω from by unfold ω; push_cast; rfl]
 change ‖σ Z0‖ ≤ (q*(fareMin (L) (v-f)))^r
 have hb' : |b⁻¹|≤1:= by simpa [fareMin] using hb.small
 have he' : |η⁻¹|≤ fareMin (L) (v-f):= by unfold η; rw [mul_inv_rev,abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) hb').trans hq.small
 apply le_trans (calc
   _ = |η⁻¹|^r*(|η|^r * ‖σ Z0‖):= by rw [← mul_assoc, abs_inv,inv_pow, inv_mul_cancel₀ (pow_ne_zero r (abs_pos.mpr hη).ne'),one_mul] -- inv_pow orientation?
   _ ≤ |η⁻¹|^r*q^r:= mul_le_mul_of_nonneg_left hf (by positivity))
 rw [mul_pow q (fareMin P.par.R.L (v-f)) r, mul_comm (q^r)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) he' _) (by positivity)
lemma absolute_clock (x:P.Spectrum0 j) : ‖(P.bought_frame j X w p c0 v).charges x (P.calendarZ v f w hw)‖ ≤ 2*(3*tiltBase P.par A f *fareMin (L) (v-f)):=
 let V₁:= P.bought_frame j X w p c0 v
 let H':=P.calendarZ v f w hw
 (V₁.cap x H').trans (ClockBooking.earned Y H P.law v P.history P.projection.clipped j (Z f v w) (n₀ v) (P.visits_queue X v) ((P.clock_fit j X p c0).2 _) id tendsto_id H' (by have ht:=P.tilt_pos T'; unfold fareMin; positivity) (P.books_raw j X w p hw c0 T' vCap PZ) (f₀:=V₁.card) (congrArg Subtype.val V₁.entry) (P.room j))
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.absolute_clock
