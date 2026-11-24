import YM.SU5.Relativistic.Grotty
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.Mosaic
open Function Finset Filter MeasureTheory Lattice Wilson Fixed.Pivots GaugeFlux
open scoped Matrix BigOperators
variable {N C: Side}(L:Ratio C N)
local notation "W_"=> L.count
local notation "T_"=> Site C
local notation "F_"=> Site N
local notation "P_"=> Site L.count
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace
open RG RG.PathData Work.F03 Pharos
local notation "J"=> Link N
local notation "O"=> Face (Per N)
local notation "V"=> Site C
variable (G: Gauge)(p:Clip){σ a b:ℝ}(B:PathData G)
open scoped Classical
local notation "S"=> Config G N
open Pressure (temp radiusB)
open Precision Next.SectorChange
-- choose all budgets. quantified explicit. Permit ANY tessellation width
lemma decor (ε:ℝ)(v:0<ε):∃ r> (0:ℝ), r<1/4 ∧ oppo G r≤ ε:=by
 have ht: ContinuousAt (oppo G) 0:=by unfold oppo; apply ContinuousAt.mul continuousAt_const; apply ContinuousAt.sub <;> apply ContinuousAt.log <;> first|fun_prop|norm_num
 have he:= ht.continuousWithinAt (s:=Set.Ioi (0:ℝ)) |>.tendsto.eventually (ge_mem_nhds (show oppo G 0<ε by simpa [oppo] using v)); exact (((show ∀ᶠ i in 𝓝[Set.Ioi (0:ℝ)] 0, 0 < i from self_mem_nhdsWithin).and ((show ∀ᶠ i in 𝓝[Set.Ioi (0:ℝ)] 0,i<1/4 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))).and he))).exists

theorem lumin(Λ:ChartRatio G)(ht:LocalRatio Λ)(K:Clip)(σ a b f z:ℝ)(φ:0≤f)(hp:1≤ K.relaxation*σ)(hs:0<σ)(u:0≤a)(e:0≤b)(hz:0<z) :
 ∀ᶠ n:ℕ in atTop, ∀ W:Side,n≤ W.val → ∀ᶠ x:ℝ in atTop, ∀ β∈ Set.Icc (x/2) (2*x),∀ (p':BudgetPoint),p'.threshold=temp x→ ∀ {N C:Side}(L:Ratio C N),2≤ N.val→ 2≤ C.val → L.count=W→ ∀(B:PathData G),B.Bounds K σ a b → ∀ {r s:ℝ}(H:Bed), Floor H K N r s → Attached H B →
    (∫ U:Config G N, grain G B K p' β f U∂prior G N)≤ Real.exp (z*(N.val:ℝ)^4+oppZ G N H Λ β) :=by
 let Z:=z/4; have hZ:0<Z:=by unfold Z; positivity
 obtain ⟨r,v,w,s⟩:= decor G Z hZ; let c:=r*K.linear/2; have hv:= K.tail_pos; have hx:0<c:=div_pos (mul_pos v hv) zero_lt_two
 obtain ⟨A,hf,hx'⟩:= husk_int G c hx Λ ht
 have he:K.linear ≤ K.direct:=by have hf:=K.kink; linarith
 obtain ⟨D,q⟩:= ((late σ a hs|>.const_mul (1+1/r)).eventually (ge_mem_nhds (show (1+1/r)*0<r*K.linear from (mul_zero ..|>.trans_lt (mul_pos v hv))))).exists
 obtain ⟨M,h⟩:= eventually_atTop.mp (puffSoon G D Z hZ K a A r v)
 filter_upwards [eventually_ge_atTop M] with n hn W hw
 filter_upwards [firstM G K D Λ ht W σ a b f c A r Z hx v φ w u e hf hp q le_rfl hx' hZ, eventually_gt_atTop (0:ℝ)] with x F o β t p' wu N C L i j g B X a' b' H H0 V0
 have hc:= F _ t p' wu L i j g B X; have hy:0<β:=lt_of_lt_of_le (half_pos o) t.1
 apply hc.trans
 have ht':0<pubB L G K B D Λ X A β r:=by
    have he:=feePos G K B D Λ X _ _ ht (by linarith :0<1-4*r) hy L.count; have hh:=spare_pos _ ht hy; unfold pubB; positivity
 have hP:=ticketPrice L G K B D Λ X H H0 V0 r β A hf v w hy ht i j (q.trans (mul_le_mul_of_nonneg_left he v.le))
 rw [← Real.exp_log ht',← Real.exp_add]; apply Real.exp_monotone
 have hv: (N.val:ℝ)^4=(C.val:ℝ)^4*(L.count.val:ℝ)^4:=by rw [L.exact_size]; push_cast; ring
 have he: pound G D K a A r L.count.val ≤ Z*(L.count.val:ℝ)^4:=by rw [g]; exact h W.val (le_trans hn hw)
 let y:ℝ:= N.val; have hy': (C.val:ℝ)^4*pound G D K a A r L.count.val ≤ Z*y^4:= le_trans (mul_le_mul_of_nonneg_left he (by positivity :0≤(C.val:ℝ)^4)) (le_of_eq (by unfold y; rw [hv]; ring)); unfold Z y at *; linarith only [hP,hy',mul_le_mul_of_nonneg_right s (show (0:ℝ) ≤ (N.val:ℝ)^4 by positivity),mul_nonneg hz.le (show (0:ℝ)≤(N.val:ℝ)^4 by positivity)] -- tune rewrite exp_log also exp x
end YM.CF.Papyrus.Mosaic
#print axioms YM.CF.Papyrus.Mosaic.lumin
