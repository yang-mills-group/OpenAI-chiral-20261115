import SatinThinCentury

/-! ## Quantitative consultation time. -/
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
open Papal Regis.Head Gleam
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
variable (P:Spine) (j:Axis)
local notation "kθ" => hat P.par.R.L P.par.x
open Real

lemma baseK_fee : ∀ᶠ i:ℕ in atTop,(P.baseK i:ℝ) ≤ kθ i:=by
 filter_upwards [P.pays_root_mile,(turnover P.par).eventually (coin_budget (a:=0) (b:=1) (c:=0) (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 1 1 zero_lt_one)] with i h j
 rw [coinY (P.f_here i),one_mul,one_mul] at j; exact h.trans j.le

private lemma doubled_tick_bound (d:ℝ) : ∀ᶠ i:ℕ in atTop,kθ (2*i)+d< (P.par.R.L.val:ℝ)^i:=by
 let z:ℝ:= P.par.R.L.val; have hz:1<z:=by unfold z; exact_mod_cast (timeMesh P.par).Llarge
 have hp(i:ℕ):0<z^i:=pow_pos (by linarith only [hz]) _
 have he:Tendsto (fun i:ℕ=>(i:ℝ)/z^i) atTop (𝓝 0):=by simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1 hz
 let r:=Vale.billX P.par.R.L
 have ht0:=tendsto_pow_atTop_atTop_of_one_lt hz
 have ht:Tendsto (fun i:ℕ=>(P.par.x+d)*(z^i)⁻¹ + 2*r*((i:ℝ)/z^i)) atTop (𝓝 0):= by
   have ht:=tendsto_inv_atTop_zero.comp ht0
   simpa only [mul_zero,add_zero,Function.comp_apply] using (ht.const_mul (P.par.x+d)).add (he.const_mul (2*r))
 filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with i v
 change _<z^i; apply (div_lt_one (hp i)).mp
 have h:= (show _< (1:ℝ) from v); refine lt_of_eq_of_lt ?_ h
 unfold hat; push_cast; change (_+_*r+d)/_=(P.par.x+d)*_+_; ring

/-- A pad quote with realization no later than `2*i` pays uniformly even across *all*
   mark involution requests (l). -/
lemma pin_budget : ∀ᶠ i:ℕ in atTop,∀ f:ℕ,∀ l:List Axis,P.pinTime j f (2*i) l < P.macroStep i:=by
 let d:= 2*frameRadius j+2*P.sidesPerTick
 have ht:= (show StrictMono (fun i:ℕ=>2*i) from fun x y g=> by change 2*x<2*y; omega).tendsto_atTop
 filter_upwards [ht.eventually P.baseK_fee,P.doubled_tick_bound (d:ℝ)] with i k hx f l
 let b:= 2*i
 change (P.baseK b:ℝ) ≤ kθ b at k
 have he : (nodeC (P.rootSpace f b l) j:ℝ) < (P.par.R.L.val:ℝ)^i:= by
   have h: (nodeC (P.rootSpace f b l) j:ℝ) ≤ (P.baseK b:ℝ)+(d:ℝ):=by
     have h:= (Int.cast_le (R:=ℝ)).mpr (P.node_ceiling j b f l)
     push_cast only [Int.cast_add,Int.cast_natCast] at h; exact h
   exact (h.trans (add_le_add_left k _)).trans_lt hx
 change _*_ / _ < _; apply (div_lt_iff₀ (show 0<(P.sidesPerTick:ℝ) from Nat.cast_pos.mpr P.sides_pos)).mpr
 have hn : i ≤ b:=by unfold b; omega
 have hp:b-i=i:=by unfold b; omega
 have hc:=P.daysF b i hn; rw [hp] at hc
 exact ((mul_lt_mul_of_pos_right he (P.macroStep_pos b)).trans_eq hc).trans_le (le_mul_of_one_le_right (P.macroStep_pos _|>.le) (by exact_mod_cast P.sides_pos))

lemma soon_quote (f r:ℕ): ∀ᶠ i:ℕ in atTop, ∀ l:List Axis,∃ V:ForecastCard P f r j l (P.macroStep i),V.stage=2*i:=by
 let ht:= (show StrictMono (fun i:ℕ=>2*i) from fun x y g=> by change 2*x<2*y; omega).tendsto_atTop
 filter_upwards [P.pin_budget j,ht.eventually (eventually_ge_atTop f),ht.eventually (eventually_ge_atTop r),ht.eventually (P.offers_plans j 1 zero_lt_one),ht.eventually (P.earns_newsprint j 1 zero_lt_one),ht.eventually P.size_honors] with i a b c d e h l
 exact ⟨⟨2*i,b,c,a f l,d.1 _ (e f l),h.1⟩,rfl⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
