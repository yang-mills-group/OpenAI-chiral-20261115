import SatinThinPeacock
import SatinThinPilgrim

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
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
abbrev recoilF (k a b:ℕ): Cover := opposeQ 3 (P.focusF k a b)
-- Treasury of all positions. Footprint at SAME positive base. two-label distances
noncomputable abbrev travelF (r:ℕ)(a b:ℕ):ℝ:= ((a+b:ℕ):ℝ)*(P.plannedK r:ℝ)
local notation "δγ" => (3:Axis)
local notation "Kv" r:max=>P.plannedK r
local notation "ZC"=> (P.sidesPerTick:ℤ)
lemma recoil3 (r:ℕ) (x y:ℕ): P.recoilF r x y δγ= - P.focusF r x y δγ:= if_pos rfl
lemma recoilH(k:ℕ)(x y:ℕ){a:Axis}(h:a≠3): P.recoilF k x y a=P.focusF k x y a:= if_neg h
lemma distance_P (r i a:ℕ)(q:0 < i+a) : 0<P.travelF r i a:= mul_pos (Nat.cast_pos.mpr q) (Nat.cast_pos.mpr (P.pointK_pos ..))
lemma distance_go {i a:ℕ}(q:0 < i+a): Tendsto (fun r=> P.travelF r i a) atTop atTop:= Filter.Tendsto.const_mul_atTop (show 0< (↑(i+a):ℝ) from Nat.cast_pos.mpr q) P.planned_grows
lemma tiny_one_ledger (_r:ℕ)(x:ℤ) : 0 ≤ (P.persistN x:ℝ) ∧ (P.persistN x:ℝ) ≤ P.echoFoot:= ⟨by exact_mod_cast (Int.natCast_nonneg _).trans (P.lodge x).1, by exact_mod_cast (P.lodge x).2.1⟩
lemma pointer_E (b:ℕ) {i a:ℕ}(q:0 < i+a): Tendsto (fun r=> Onyx.riseX (P.travelF r i a) (P.focusF (P.plannedK r) i 0 - P.recoilF (P.plannedK r) a b)) atTop (𝓝 (YM.basis 3)):=by
 let S r:= P.travelF r i a; let R0 (r:ℕ):=(fun k:Axis=>(↑((P.focusF (Kv r) i 0 - P.recoilF (Kv r) a b) k):ℝ)/ (S r)); refine (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (f:=R0) (tendsto_pi_nhds.mpr ?_); intro c
 change Tendsto (fun r=> R0 r c) atTop (𝓝 ((YM.basis 3) c)); by_cases h:c=3
 · subst c; have ht(r):0<S r:= P.distance_P r i a q; let u(r):= (P.persistN (Kv r):ℝ)/S r; let k₀:ℝ:=2-i-a
   have h0: Tendsto u atTop (𝓝 0):= squeeze_zero (fun r=>div_nonneg (P.tiny_one_ledger r _|>.1) (ht r).le) (fun r=>div_le_div_of_nonneg_right (P.tiny_one_ledger r _|>.2) (ht r).le) (tendsto_const_nhds.div_atTop (a:=(P.echoFoot:ℝ)) (P.distance_go q)); have h1 := tendsto_const_nhds (x:=(1:ℝ))|>.add (h0.const_mul k₀); rw [mul_zero,add_zero] at h1; rw [show YM.basis 3 3=1 from (by simp [basis_eq])]; refine h1.congr fun r=>?_
   let z:= Kv r; let θ:ℝ:= S r; let k:=P.persistN z; unfold R0 u
   have hz:θ=((i:ℝ)+a)*(z:ℝ):=by change (↑(i+a):ℝ)*(z:ℝ)=_;rw [Nat.cast_add];
   rw [Pi.sub_apply,P.recoil3,P.focus_axis,P.focus_axis]; change 1+ k₀*((k:ℝ)/θ)= ↑(((i:ℤ)*z+(1-(i:ℤ))*k) - -( (a:ℤ)*z+(1-(a:ℤ))*k))/θ; simp only [Int.cast_sub,Int.cast_natCast,Int.cast_mul,Int.cast_add,Int.cast_neg,Int.cast_one] -- may push k? simp no simp
   set c:= k₀; rw [show _ - -(↑a*(z:ℝ)+(1-(a:ℝ))*(k:ℝ))= θ+c*(k:ℝ) from (by rw [hz]; unfold c k₀; ring), add_div, div_self (show θ≠0 from (ht r).ne'),mul_div_assoc]
 rw [show YM.basis 3 c=0 from (by simp [basis_eq,h])]; let B:ℝ:= (P.sidesPerTick:ℝ)*b; have he:= tendsto_const_nhds.div_atTop (f:=fun (_:ℕ) => B) (a:=B) (P.distance_go q); refine he.congr fun r=>?_ ; unfold R0 S; rw [Pi.sub_apply,P.recoilH _ _ _ h,P.focus_canvas _ _ 0 c h,P.focus_canvas _ _ b c h,Int.cast_sub]; unfold B; apply congrArg (·/ _); simp only [Int.cast_sub,Int.cast_natCast,Int.cast_mul,Nat.cast_zero,Int.cast_zero]; ring

private lemma detailed_request {a b:ℝ}(h:a<b)(t:0<a)(A B:ℝ): ∀ᶠ s:ℕ in atTop,A*trailℓ a (F s)+B ≤ trailℓ b (F s) :=by -- need b>0 and a≥0 for pays
 exact (turnover P.par).eventually (leap (p:=b) (w:=0) (q:=0) (plus (Pays.scale A (Pays.whole 0 a 0)) (Worth.Pays.merit (constant B) (Or.inr (Or.inl ⟨rfl,t⟩)))) (Or.inr (Or.inl ⟨rfl,h⟩)))
private lemma battalion (n u b:ℕ)(t:Axis): (P.focusF n u b t).natAbs ≤ u*n+n+(1+u)*P.echoFoot+P.sidesPerTick*b:=by
 have hx:(P.persistN n).natAbs ≤ P.echoFoot:=by obtain ⟨h,k,_⟩:= P.lodge n; omega
 by_cases h:t=(3:Axis)
 · subst t; rw [P.focus_axis]; refine (Int.natAbs_add_le ..).trans ?_; have ht:(1-(u:ℤ)).natAbs ≤ 1+u:=by omega
   rw [Int.natAbs_mul,Int.natAbs_mul]; refine le_trans (b:=u*n+(1+u)*P.echoFoot) ?_ (by omega); exact Nat.add_le_add_left (Nat.mul_le_mul ht hx) _ -- maybe cast order wrong
 rw [P.focus_canvas _ _ _ _ h]; refine (Int.natAbs_sub_le ..).trans ?_; rw [Int.natAbs_mul]; change n+P.sidesPerTick*b≤_; omega
private lemma hand_r {a:ℝ} (h:P.depthCap<a)(A B:ℕ) : ∀ᶠ s:ℕ in atTop, A*P.plannedK s+B ≤ scout P.par a s:=by
 filter_upwards [P.detailed_request h P.depthCap_pos ((A:ℝ)*P.par.R.L.val) (B:ℝ),P.planned_ceiling] with s p v; have hc:(A:ℝ)*(P.plannedK s:ℝ) + B ≤ (scout P.par a s:ℝ) := le_trans (add_le_add_left ((mul_le_mul_of_nonneg_left v (Nat.cast_nonneg A)).trans_eq (mul_assoc _ _ _).symm) _) (p.trans (Nat.le_ceil _)); exact_mod_cast hc
lemma military_size {a:ℝ} (h:P.depthCap<a)(u b:ℕ): ∀ᶠ s:ℕ in atTop, ∀ t:Axis, ((P.focusF (P.plannedK s) u b t).natAbs ≤ scout P.par a s) ∧(P.recoilF (P.plannedK s) u b t).natAbs ≤ scout P.par a s:=by
 filter_upwards [P.hand_r h (1+u) ((1+u)*P.echoFoot+P.sidesPerTick*b)] with s p t; let n:=Kv s; have he:=P.battalion n u b t; change (1+u)*n+_ ≤ _ at p; rw [add_mul,one_mul] at p; have hv:(P.focusF n u b t).natAbs ≤ scout P.par a s:=by omega
 refine ⟨hv,(show (P.recoilF n u b t).natAbs=(P.focusF n u b t).natAbs from ?_)|>.trans_le hv⟩; by_cases h:t=(3:Axis); subst t; rw [P.recoil3,Int.natAbs_neg]; rw [P.recoilH _ _ _ h]

lemma planning_size_go (i a:ℕ)(h:0 < i+a)(p:ℝ)(v:8*P.depthCap < p): Tendsto (fun r=> (P.travelF r i a)^8/trailℓ p (F r)) atTop (𝓝 0):=by
 let y(x:ℝ):= ((↑(i+a):ℝ)*((↑(L).val:ℝ)*trailℓ P.depthCap x))^8*trailℓ (-p) x; have hv:Tendsto (fun s:ℕ=> y (F s)) atTop (𝓝 0):= (Pays.limit (Pays.times (pot (Pays.scale ((↑(i+a)):ℝ) (Pays.scale ((↑(L).val:ℝ)) (Pays.whole 0 P.depthCap 0))) 8) (Pays.whole 0 (-p) 0)) (by right; left; constructor; norm_num; push_cast; linarith only [v])).comp (turnover Λ)
 have hg:=P.pointK_pos
 apply squeeze_zero' _ _ hv
 · filter_upwards with r; exact div_nonneg (pow_nonneg (P.distance_P r i a h).le _) (trainℓ ..|>.le)
 filter_upwards [P.planned_ceiling] with s t; unfold y; rw [div_eq_mul_inv,show (trailℓ p (F s))⁻¹= trailℓ (-p) (F s) by unfold trailℓ; rw [coin_inv,neg_zero]]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (P.distance_P s i a h|>.le) (mul_le_mul_of_nonneg_left t (Nat.cast_nonneg _)) _) (trainℓ .. |>.le)
open Regis.Circuit
local notation "z'"=> Yoke.witnessZ
private lemma CoversT_pairP {x y:Cover}{n:ℕ} (f:∀ t:Axis,(x t).natAbs≤ n)(g:∀ t:Axis,(y t).natAbs≤ n): CoversT (twinTrip x y) n:=by intro l k; cases l with|true=> exact f k|false=> exact g k
abbrev glareF (P:Spine)(f r a b c:ℕ) (x:P.Spectrum0 3):ℝ:= let k:=P.megaK f r; P.mistake 3 z' r (((a+b:ℕ):ℝ)*k) (P.focusF k a 0) (P.recoilF k b c) (YM.basis 3) x
lemma glare_go (i a b:ℕ)(h:0 < i+a){C:ℝ}(Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → ShelterCost C P.run s i k) : Tendsto (fun s=>∫ x,P.glareF (P.pointEra s) s i a b x∂(P.pillars 3)) atTop (𝓝 0):=by
 let p:=8*P.depthCap+1; have hp:=P.depthCap_pos; let A:=14+2*p; let v:= P.depthCap+6*A+2*p+1; have hV:P.depthCap < v:=by unfold v A p; linarith
 let R0:=fun s=> P.travelF s i a
 let x:=fun s=> P.focusF (P.plannedK s) i 0
 let y:=fun s=>P.recoilF (P.plannedK s) a b
 have hw:∀ᶠ j:ℕ in atTop,CoversT (twinTrip (x j) (y j)) (scout P.par v j):=by
    filter_upwards [P.military_size hV i 0,P.military_size hV a b] with s t v; exact CoversT_pairP (fun k=>(t k).1) (fun k=>(v k).2)
 have hpu:0<p:=by unfold p; linarith only [hp]
 -- beware notation `z` autoImp
 have he:= P.mistake_go 3 z' A p v Z (ρ:=R0) (x:=x) (y:=y) (Z:=YM.basis 3) (fun s=> P.distance_P s i a h) (P.distance_go h) (P.pointer_E b h) (by intro e; simpa using congrArg norm e) hw (P.planning_size_go i a h p (by unfold p; linarith)) (by unfold A; linarith) hpu (by unfold v; linarith only [hp])
 exact he
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.glare_go
