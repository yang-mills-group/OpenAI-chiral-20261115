import YM.SU5.Registration.Rise.Appraise
import YM.SU5.Same.TemperWarrant
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

/-!
# Quoting the earlier slab clock. Adapts `TemperWarrant.pin_toll_earns`, for the
entire slab, not just the transposed time. Can afford common ruler clearance here at
polynomial price to 0-width: small log costs of root spacings do not exceed buying this
with *double* the height of the `step k`-width. This one lemma buys the pressure
permission too; not assuming a `Preparation.Geometry` for the earlier mesh when making
long estimates.
-/
local notation "T" f:max s:max l:max=> P.rootSpace f s l
local notation "kℝ" => (P.par.R.L.val:ℝ)
local notation "μ'" s:max=> P.macroStep s
abbrev rowClock (j:Axis)(g f:ℕ)(l:List Axis) := twiceT (P.rootSpace g f l) j + 1
local notation "O" f:max s:max l:max => P.rowClock j f s l

lemma row_paid : ∀ᶠ s:ℕ in atTop, ∀ (f:ℕ)(l:List Axis),P.ColumnBill (P.rowClock j f s l) s:=by
 let k:= 16*P.par.block.val; let c:ℝ:=(k:ℝ); let d(x:ℝ):= c*(Nat.ceil (trailℓ 1 x)+ (1:ℝ))
 have hd: Worth.Pays 0 1 0 d:=Pays.scale _ (Pays.plus (helmBound 1 zero_lt_one) (Worth.Pays.merit (constant _) (Or.inr (Or.inl ⟨rfl,zero_lt_one⟩))))
 filter_upwards [(turnover P.par).eventually (leap (w:=0) (p:=2) (q:=0) hd (Or.inr (Or.inl ⟨rfl,by norm_num⟩))), P.earns_newsprint j 1 zero_lt_one, P.weather_bill 2 (by norm_num)] with i h t v f l
 let x:= F i; let u:= O f i l; let b:= k*u; let A:= Yoke.scout Λ 2 i; let D:= plusAgain P.par.block (P.labW i)
 have he: k*(Yoke.scout P.par 1 i+1) ≤ A:= Nat.cast_le (α:=ℝ)|>.mp (by push_cast; exact (show d x≤trailℓ 2 x from h).trans (Nat.le_ceil _))
 have hs: b ≤ A:= (Nat.mul_le_mul_left k (Nat.succ_le_succ (t f l))).trans he
 let V:= Worth.meterC x; have hV: 0 ≤ 14*V:=mul_nonneg (by norm_num) (coin_pos ..).le
 change 14*V*(↑((4*D)^3*(2*b):ℕ):ℝ) ≤1
 refine v.trans' (mul_le_mul_of_nonneg_left ?_ hV)
 change ((↑((4*D)^3*(2*b):ℕ)):ℝ) ≤ ((↑(4*(A+D):ℕ)):ℝ)^4; norm_cast; rw [pow_succ (4*(A+D):ℕ) 3]; exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (by omega)

-- Clock quota in true physical units.
local notation "C₀" j:max=> 2*frameRadius j+2*P.sidesPerTick
lemma row_beat {a:ℝ}(h₀:0<a): ∀ᶠ k:ℕ in atTop, ∀ (f:ℕ)(l:List Axis),(P.rowClock j f (k+k) l:ℝ) * P.macroStep (k+k) < a* P.macroStep k:=by
 let A := P.par.x; let B:= billX P.par.R.L; let c:ℝ:=(C₀ j : ℕ)
 have he : 1 < kℝ := by exact_mod_cast (timeMesh P.par).Llarge
 let h(k:ℕ):ℝ:= (2*(F (k+k)+c)+1)/kℝ^k
 have ht:Tendsto h atTop (𝓝 0):=by
    have h0:= tendsto_pow_const_div_const_pow_of_one_lt 1 he
    have h1:= tendsto_pow_const_div_const_pow_of_one_lt 0 he
    suffices w:Tendsto (fun k:ℕ=> (2*(A+c)+1)*(1/kℝ^k)+4*B*((k:ℝ)/kℝ^k)) atTop (𝓝 0) by
        refine w.congr fun k=>?_ ; unfold A B h hat; push_cast; ring
    simpa only [mul_zero,add_zero,pow_zero,pow_one] using (h1.const_mul (2*(A+c)+1)).add (h0.const_mul (4*B))
 have g0: ∀ᶠ i:ℕ in atTop,(P.baseK i:ℝ) ≤ F i:=by
    filter_upwards [P.pays_root_mile,(turnover Λ).eventually (coin_budget (a:=0) (b:=1) (c:=0) (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 1 1 zero_lt_one)] with i u v
    rw [coinY (P.f_here i), one_mul,one_mul] at v; exact u.trans v.le
 filter_upwards [ht.eventually (gt_mem_nhds h₀), tendsto_double_page.eventually g0] with k p q f l
 let s:= k+k; let u:= μ' s; let d:= kℝ^k; let y:= nodeC (T f s l) j
 have hz: (y:ℝ)≤(P.baseK s:ℝ)+c:=by
   have he':=(Int.cast_le (R:=ℝ)).mpr (P.node_ceiling j s f l)
   push_cast only [Int.cast_add, Int.cast_natCast] at he'; exact he'
 have hU : (↑(O f s l):ℝ)≤2*( F s + c)+1:=by
    rw [show (↑(O f s l):ℝ) = (2:ℝ)*(y:ℝ)+1 from ?_]; have hx: (y:ℝ)≤ (F s) + c := hz.trans (add_le_add q le_rfl); linarith only [hx]
    have he': (O f s l:ℤ)= 2*y+1:=by unfold rowClock twiceT; have ht:0≤y:=(P.point_bought j ..).le; change _= _; unfold y at *; omega
    exact_mod_cast he'
 rw [P.page_step k,← mul_assoc]; refine mul_lt_mul_of_pos_right (hU.trans_lt ((div_lt_iff₀ (pow_pos (zero_lt_one.trans he) _)).1 (show (2*( F s +c)+1)/kℝ^k<a from p))) (P.macroStep_pos s)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.row_paid
#print axioms Spine.row_beat
