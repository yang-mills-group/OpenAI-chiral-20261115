import YM.SU5.Same.AllSeasons
/-!
# Keep purchase evidence for the representations. work in RealSheet.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.SatinEdge.RealSheet
open Function Set Filter Metric Finset MeasureTheory Measure Spectral Analysis Boundary Probe Complex
open OS Semigroup
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace BigOperators Classical ComplexConjugate
open Multiplier Roy SatinJets
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
local notation "P" => S.ℚmeasure
lemma attendee : ∃ f:ℕ→ Test4, ∀ x:H,Tendsto (fun i=> collect S (f i) x) atTop (𝓝 x):=by
 -- idem SNAG/Escape: pull a test from half. here oracle actual boundary
 let B : ContDiffBump (0 : E4) := ⟨1,2,by norm_num,by norm_num⟩
 let f : Probe E4 := (B.hasCompactSupport.comp_left (show ofReal 0=0 from rfl)).toSchwartzMap
    (ofRealCLM.contDiff.comp B.contDiff)
 have h : f 0=1 := by
    change (B 0:ℂ)=1; rw [B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)];rfl
 refine ⟨fun i=> SNAG.cut (SNAG.wide f i),fun x=>?_⟩; simp_rw [collect,onward_cut]; exact SNAG.zooms S.unit f h x

variable {ι:Type}[Fintype ι][DecidableEq ι] (X:ι→ℝ→ H)
variable (v:∀ i,TemperedAtEdge H (X i))
variable (u:∀ i,Positive S (X i))
-- kernel test (need only clean det of match)
lemma clean_reads (X:ι→H)(Z:H.Op)(h:Six.Clean (Matrix.of fun i j:ι=> inner ℂ (X i) (Z (X j)))) : LinearIndependent ℂ X:=by
 rw [Fintype.linearIndependent_iff]; intro f t i
 let M:= Matrix.of fun i j:ι=> inner ℂ (X i) (Z (X j))
 apply congrFun (f:=f) (g:= (0:ι→ℂ)) _ i; refine Matrix.eq_zero_of_mulVec_eq_zero (M:=M) h.1 ?_ -- signature
 funext k
 have hz:(∑ i:ι,f i • Z (X i))=0:=by
    rw [←show Z (∑ i:ι,f i • X i)=(∑ i:ι,f i • Z (X i)) from ?_,t, map_zero]; simp_rw [_root_.map_sum,map_smul]
 have ht:inner ℂ (X k) (∑ i:ι, f i • (Z (X i)))=0:=by rw [hz,inner_zero_right];
 change ∑ j:ι,(M k j * f j)=0; simp_rw [inner_sum,inner_smul_right] at ht; rw [sum_congr rfl (g:=fun j:ι=>f j * (M k j)) (fun j _=> mul_comm ..)]; exact ht -- syntax change after?

lemma narrow_clean (Z:H.Op): IsOpen {x:ι→ H|Six.Clean (Matrix.of fun i k=> inner ℂ (x i) (Z (x k)))}:= by
 apply Six.clean_open; exact continuous_matrix fun i k=> (continuous_apply i).inner (Z.continuous.comp (continuous_apply k))
include u
lemma colored_rank (t:ℝ)(τ:0<t)(Z:H.Op)(w:Six.Clean (Matrix.of fun i k:ι=> inner ℂ (X i t) (Z (X k t)))) : ∃ f: Test4, LinearIndependent ℂ (fun i:ι=> awake S (X i) (v i) f):=by
 obtain ⟨g,p⟩:= attendee S; let Y(n:ℕ):=fun i=> collect S (g n) (X i t); have he:Tendsto Y atTop (𝓝 (fun i :ι=> X i t)):= tendsto_pi_nhds.mpr fun i :ι=> p (X i t)
 let s: Set (ι→H):={x| Six.Clean (Matrix.of fun i k=> inner ℂ (x i) (Z (x k)))}
 obtain ⟨n,hx⟩:= (he.eventually (IsOpen.mem_nhds (show IsOpen s from narrow_clean Z) w)).exists
 let K:= S.E t.toNNReal
 let A(i):= awake S (X i) (v i) (g n)
 have h : LinearIndependent ℂ (Y n) := clean_reads (Y n) Z hx
 have ht(i): Y n i= K (A i):=by
    unfold Y K A; rw [awake_on_axis S (X i) (v i) (u i) t.toNNReal (Real.toNNReal_pos.mpr τ),Real.coe_toNNReal _ τ.le]
 rw [show Y n= K.toLinearMap ∘ A from funext ht] at h
 exact ⟨g n,LinearIndependent.of_comp K.toLinearMap h⟩ -- Lean ?
end YM.SatinEdge.RealSheet
open YM.SatinEdge.RealSheet
#print axioms colored_rank
