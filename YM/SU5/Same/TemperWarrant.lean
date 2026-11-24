import SU5SatinVerifiedNovember6
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
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
/-! # Regular account estimate toward unpadded fields

Reduce payments to actual Century calibration. M3p: see `the construction notes`.
All cash in CP18 H on the single character family. Choose character *once*
when launching the Scouts, carrying additional almost-everywhere purchases.
-/
local notation "θ" => hat P.par.R.L P.par.x
local notation "Lᵣ" => (P.par.R.L.val:ℝ)
local notation "Δs" => P.sidesPerTick
-- bounds on tolls at that tick
lemma slot_le_unit : ∀ᶠ s:ℕ in atTop, slotFee P.par s ≤ 1:= by
 filter_upwards [(turnover Λ).eventually (cap_meter P.par.R)] with s p
 exact p.2.2.2.1.trans p.2.2.2.2
lemma has_units : Tendsto (fun s:ℕ=> scaleY (hat P.par.R.L P.par.x s)) atTop atTop:=
    (summitT 1 zero_lt_one).comp (turnover P.par)
lemma tall_units : ∀ᶠ s:ℕ in atTop, P.tallWorth s ≤ 1:=by
 filter_upwards [P.slot_le_unit, P.has_units.eventually_ge_atTop 1] with s p q
 have he: (1:ℝ)≤ scaleY (θ s)^2:= one_le_pow₀ q
 rw [P.tariff_law]; exact (div_le_one (zero_lt_one.trans_le he)).2 (p.trans he)

-- pin time qualification. Use real units of the reference CP18 (Motion.lean)
-- and compare to *center* times for polynomial of `Radiates.choir`.
lemma page_step (k:ℕ): P.macroStep k = Lᵣ ^ k * P.macroStep (k+k):=by
 simpa only [Nat.add_sub_cancel_left] using (P.daysF (k+k) k (Nat.le_add_right ..)).symm -- simp orientation
lemma tendsto_double_page : Tendsto (fun i:ℕ=> i+i) atTop atTop:=
 tendsto_atTop_mono (fun i : ℕ=> Nat.le_add_right i i) tendsto_id
local notation "C₀" j:max=> 2*frameRadius j+2*P.sidesPerTick
lemma pin_toll_earns : ∀ᶠ k:ℕ in atTop, ∀ (f:ℕ)(l:List Axis),P.pinTime j f (k+k) l < P.macroStep k:=by
 let A := P.par.x
 let T := billX P.par.R.L
 let c:ℝ:=(C₀ j : ℕ)
 have he: 1 < Lᵣ := by exact_mod_cast (timeMesh P.par).Llarge
 let h(k:ℕ):ℝ:= (θ (k+k)+c)/Lᵣ^k
 have ht:Tendsto h atTop (𝓝 0):=by
    have h0:= tendsto_pow_const_div_const_pow_of_one_lt 1 he
    have h1:= tendsto_pow_const_div_const_pow_of_one_lt 0 he
    suffices w:Tendsto (fun k:ℕ=> (A+c)*(1/Lᵣ^k)+2*T*((k:ℝ)/Lᵣ^k)) atTop (𝓝 0) by
        refine w.congr fun k=>?_ ; unfold A T h hat; push_cast; ring
    simpa only [mul_zero,add_zero,pow_zero,pow_one] using (h1.const_mul (A+c)).add (h0.const_mul (2*T))
 have hp: 0<(Δs:ℝ) := Nat.cast_pos.mpr P.sides_pos
 have g0: ∀ᶠ i:ℕ in atTop,(P.baseK i:ℝ) ≤ θ i:=by
    filter_upwards [P.pays_root_mile,(turnover Λ).eventually (coin_budget (a:=0) (b:=1) (c:=0) (d:=1) (e:=0) (f:=0) (Or.inl zero_lt_one) 1 1 zero_lt_one)] with i u v
    rw [coinY (P.f_here i), one_mul,one_mul] at v; exact u.trans v.le
 filter_upwards [ht.eventually (gt_mem_nhds hp),tendsto_double_page.eventually g0] with k p q f l
 let Z:=nodeC (P.rootSpace f (k+k) l) j; let m:= P.macroStep (k+k); let d:= Lᵣ^k
 have hs:(Z:ℝ) ≤ θ (k+k)+c:=by
    have hz: (Z:ℝ)≤(P.baseK (k+k):ℝ)+c:=by
      have he':=(Int.cast_le (R:=ℝ)).mpr (P.node_ceiling j (k+k) f l)
      push_cast only [Int.cast_add,Int.cast_natCast] at he'; exact he'
    exact hz.trans (add_le_add q le_rfl)
 rw [P.page_step k] -- target right
 have hw: (θ (k+k)+c)/d < Δs:=p
 refine (div_lt_iff₀ hp).2 ?_; change (Z:ℝ)*m< d * m * ↑Δs; rw [mul_right_comm d,mul_comm d]; exact mul_lt_mul_of_pos_right (hs.trans_lt ((div_lt_iff₀ (pow_pos (zero_lt_one.trans he) k)).1 hw)) (P.macroStep_pos (k+k))

/-- Can always choose the forecast table with these stage rules **at** the little heat heights. -/
lemma table_at (f r:ℕ)(l:List Axis) : ∃ F:∀ k, ForecastCard P f r j l (P.macroStep k), ∀ᶠ k:ℕ in atTop, (F k).stage=k+k:=by
 let CardsAt (k:ℕ):=ForecastCard P f r j l (P.macroStep k)
 let p(k:ℕ):Prop := ∃ G:CardsAt k,G.stage=k+k
 let F(k:ℕ):CardsAt k:= if t:p k then Classical.choose t else Classical.choice (P.forever_quote _ _ _ _ _ (P.macroStep_pos k))
 have he(k:ℕ)(h:p k): (F k).stage=k+k:= by rw [show F k=h.choose from (dif_pos h)]; exact h.choose_spec
 refine ⟨F,?_⟩; let D:= tendsto_double_page
 filter_upwards [D.eventually_ge_atTop f,D.eventually_ge_atTop r,P.pin_toll_earns j,D.eventually (P.offers_plans j 1 zero_lt_one),D.eventually (P.earns_newsprint j 1 zero_lt_one), D.eventually P.size_honors] with k u v t b c d
 exact he k ⟨⟨k+k,u,v,t f l,b.1 _ (c f l), d.1⟩,rfl⟩

-- geometric bound on size of the corner. *All* coordinates at once, before trip estimate
abbrev windowCenter (s f:ℕ)(l:List Axis): Cover:= P.clockPlate s (s+1) (P.rootSpace f s l)
lemma center_coord (s f:ℕ)(l:List Axis) : P.windowCenter s f l j = P.par.R.L.val * nodeC (P.rootSpace f s l) j:=by
 unfold windowCenter clockPlate; rw [show s+1-s=1 from by omega, pow_one, Pi.smul_apply,nsmul_eq_mul]
lemma center_payable : ∀ᶠ s:ℕ in atTop,∀ (j:Axis)(f:ℕ)(l:List Axis),(P.windowCenter s f l j).natAbs ≤ scout P.par 2 (s+1):=by
 apply Filter.eventually_all.mpr; intro j
 let v(n:ℕ):= scaleY (θ n)
 have h:Tendsto (fun i:ℕ=> Real.log (θ i)) atTop atTop:= Real.tendsto_log_atTop.comp (turnover Λ)
 let T:= hat P.par.R.L P.par.x
 let c:ℝ:=(C₀ j :ℕ)
 let he := ((turnover Λ).eventually (coin_budget (a:=0) (b:=1) (c:=0) (d:=0) (e:=2) (f:=0) (Or.inr (Or.inl ⟨rfl,by norm_num⟩)) (Lᵣ * 2) 1 zero_lt_one))
 have h1: Tendsto (fun n:ℕ=> n+1) atTop atTop:= tendsto_add_atTop_nat 1
 have h2: ∀ᶠ s:ℕ in atTop,v s ≤ v (s+1):=by
   filter_upwards [h.eventually_ge_atTop 1] with i p; unfold v; rw [coin_scale,coin_scale]; refine Real.exp_monotone (pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ log (T i) from p)) (Real.log_le_log (zero_lt_one.trans_le (show 1 ≤ log (T i) from p)) (Real.log_le_log (P.f_here i) (P.base_height (Nat.le_succ i)))) _)
 filter_upwards [h2,P.pays_root_mile,P.has_units.eventually_ge_atTop c,h1.eventually he] with s p q d t f l
 let Z:=nodeC (P.rootSpace f s l) j
 let U:= P.windowCenter s f l j
 have hu:= P.point_bought j s f l
 have e: (U.natAbs:ℝ) = Lᵣ * (Z:ℝ):=by
    have hl:0 ≤ U:=by rw [show U= _ from P.center_coord j s f l]; exact mul_nonneg (Nat.cast_nonneg _) hu.le
    rw [show (U.natAbs:ℝ)= ((↑U.natAbs:ℤ):ℝ) from ?_,Int.natCast_natAbs,abs_of_nonneg hl, show U= _ from P.center_coord j s f l, Int.cast_mul, Int.cast_natCast]
    exact Eq.symm (Int.cast_natCast _)
 apply Nat.cast_le (α:=ℝ)|>.mp; change (U.natAbs:ℝ) ≤ _; rw [e]; apply le_trans (b:= trailℓ 2 (θ (s+1))) _ (Nat.le_ceil _)
 refine le_trans (mul_le_mul_of_nonneg_left (show (Z:ℝ) ≤ 2 * v (s+1) from ?_) (Nat.cast_nonneg _)) ?_
 · have hv:= (Int.cast_le (R:=ℝ)).mpr (P.node_ceiling j s f l); push_cast only [Int.cast_add,Int.cast_natCast] at hv; change (Z:ℝ) ≤ (P.baseK s:ℝ)+c at hv; change (P.baseK s:ℝ)≤v s at q; have ht:c ≤ v s:= d; linarith only [p,hv,q,ht]
 rw [← mul_assoc]; rw [one_mul] at t; exact t.le
lemma covered_window (f:ℕ)(l:List Axis): ∀ᶠ s:ℕ in atTop,CoversT (twinTrip (opposeQ j (P.windowCenter s f l)) (P.windowCenter s f l)) (scout P.par 2 (s+1)):=by
 filter_upwards [P.center_payable] with s p
 intro i k; cases i
 · exact p k f l
 change (opposeQ j (P.windowCenter s f l) k).natAbs ≤ _; by_cases h:k=j <;> simpa [opposeQ,mirrorΩ,h] using p k f l
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.center_payable
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.table_at
