import SatinFixedContrastNovember4
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Convex.Combination

/-!
# CP12 Maze: one price constitution

Bright individual lamps in EVERY concert are paid via one ordinary (not ultraweak)
limit schedule. Estimate uses nested convex sublevels in Hilbert (a version of Mazur).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SatinNucleus
open Filter Metric Set NormedSpace
open scoped Topology NNReal ENNReal lp Classical BigOperators Pointwise
open Finset (sum)
-- note hull of *tail(i+j)* convenient
structure Coalition where
  voters : Finset ℕ
  w : ℕ → ℝ
  pledges : voters.sum w = 1
  signed : ∀ j ∈ voters, 0 ≤ w j

section
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
private lemma inner_convex_collection (v:ℕ→ E) (C:ℝ) (h:∀ i, ‖v i‖≤C) : ∃ u:E,∀ i:ℕ, u∈ closure (convexHull ℝ (Set.range (fun j:ℕ=> v (i+j)))):=by
 let K(i:ℕ): Set E:= closure (convexHull ℝ (Set.range (fun j:ℕ=> v (i+j))))
 have he(i:ℕ): v i ∈ K i:= subset_closure (subset_convexHull ℝ _ ⟨0,rfl⟩)
 have H:∀ i,Convex ℝ (K i):= fun i=> (convex_convexHull ℝ _).closure
 have anti:Antitone K:= by
   intro j k p; refine closure_mono ((convexHull ℝ).monotone ?_)
   rintro _ ⟨r,rfl⟩; exact ⟨k-j+r, by dsimp only; simp only [← Nat.add_assoc]; congr; omega⟩
 have t(i:ℕ):∃ x∈ K i, ∀ y∈ K i, ‖x‖ ≤ ‖y‖:= by
   obtain ⟨x,e,Z⟩:= exists_norm_eq_iInf_of_complete_convex (K:=K i) ⟨_,he i⟩ isClosed_closure.isComplete (H i) 0
   refine ⟨x,e,fun y u=>?_⟩; simp_rw [zero_sub,norm_neg] at Z; rw [Z]
   exact ciInf_le_of_le ⟨0, Set.forall_mem_range.mpr fun _=>norm_nonneg _⟩ ⟨y,u⟩ le_rfl
 choose f g w using t
 let d(i:ℕ):ℝ := ‖f i‖^2
 have lo: Monotone d:=fun i j p=> (pow_le_pow_left₀ (norm_nonneg (f i)) (w i _ (anti p (g j))) 2)
 have hb:BddAbove (Set.range d):= ⟨C^2,Set.forall_mem_range.mpr fun i=>pow_le_pow_left₀ (norm_nonneg _) ((w i _ (he i)).trans (h i)) _⟩
 let D:=iSup d
 have hz:Tendsto d atTop (𝓝 D):= tendsto_atTop_ciSup lo hb
 have hc:CauchySeq f:=by
    refine Metric.cauchySeq_iff'.2 fun ε hε=>?_ -- single other idx
    obtain ⟨k,hk⟩:= (hz.eventually (lt_mem_nhds (show D-ε^2 /4 < D from (by linarith only [pow_pos hε 2])))).exists
    refine ⟨k,fun n h=>?_⟩
    have hu:= (w k ((1/2:ℝ) • (f k+f n)) (by
       rw [smul_add]; exact H k (g k) (anti h (g n)) (by norm_num) (by norm_num) (by norm_num)))
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))] at hu
    rw [dist_eq_norm]
    have hv:= parallelogram_law_with_norm_mul ℝ (f n) (f k); rw [add_comm (f n)] at hv
    have hl: d n ≤ D:=le_ciSup hb n
    change _ < d k at hk; unfold d at hk hl
    -- orient
    nlinarith only [hk, hu, pow_le_pow_left₀ (norm_nonneg _) hu 2, hε, hl, hv, norm_nonneg (f n-f k)]
 obtain ⟨u,r⟩:= cauchySeq_tendsto_of_complete hc; exact ⟨u,fun i=>isClosed_closure.mem_of_tendsto r ((eventually_ge_atTop i).mono fun n y=> anti y (g n))⟩

lemma inner_coalition (v:ℕ→ E) (C:ℝ) (h:∀ i, ‖v i‖≤C) :
 ∃ (A:ℕ→ Coalition) (u:E), Tendsto (fun i=>∑ j∈ (A i).voters,(A i).w j • v (i+j)) atTop (𝓝 u):=by
 classical
 obtain ⟨u,H⟩:= inner_convex_collection v C h
 have he(i:ℕ):∃ t:Coalition, dist (∑ j∈ t.voters,t.w j • v (i+j)) u < 1/(i+1:ℝ):=by
   obtain ⟨x,hx,q⟩:= Metric.mem_closure_iff.mp (H i) (1/(i+1:ℝ)) (by positivity)
   rw [convexHull_range_eq_exists_affineCombination] at hx; obtain ⟨s,w,t,e,rfl⟩:=hx; rw [Finset.affineCombination_eq_linear_combination _ _ _ e,dist_comm] at q; exact ⟨⟨s,w,e,t⟩,q⟩
 choose s H using he
 refine ⟨s,u, Metric.tendsto_nhds.mpr fun ε hε =>?_⟩; filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)] with i q; exact (H i).trans q
end
section lp
variable {E:ℕ→Type} [∀ i, NormedAddCommGroup (E i)] [∀ i,InnerProductSpace ℝ (E i)] [∀ i,CompleteSpace (E i)]
lemma charter (v:∀ i:ℕ,ℕ→E i)(B:ℕ→ℝ)(p:∀ i k, ‖v i k‖ ≤ B i): ∃ A:ℕ→ Coalition, ∀ i,∃ u:E i,Tendsto (fun n=> ∑ j∈(A n).voters,(A n).w j • v i (n+j)) atTop (𝓝 u):=by
 let f(i:ℕ):=(1/2:ℝ)^i
 let c(i:ℕ):=f i /(B i + 1)
 have hc(i:ℕ):0<c i:=div_pos (pow_pos one_half_pos i) (by linarith only [norm_nonneg (v i 0), p i 0])
 let x(k:ℕ)(i:ℕ):= c i • v i k
 have hz(k i:ℕ): ‖x k i‖≤ f i:=by
   unfold x; rw [norm_smul, Real.norm_of_nonneg (hc i).le]; refine (mul_le_mul_of_nonneg_left ((p i k).trans (show B i ≤ B i + 1 by linarith)) (hc i).le).trans (le_of_eq ?_); exact div_mul_cancel₀ _ (by linarith only [norm_nonneg (v i 0), p i 0])
 have hl(k:ℕ)(s:Finset ℕ): ∑ i∈ s, ‖x k i‖ ^ (2:ℝ≥0∞).toReal ≤ (2:ℝ) ^ (2:ℝ≥0∞).toReal :=by
    have hj: (2:ℝ≥0∞).toReal=(↑(2:ℕ):ℝ):=by norm_num
    rw [hj]; simp_rw [Real.rpow_natCast]
    have hx: (∑ i∈ s,f i) ≤ (1-(1/2:ℝ))⁻¹:= sum_le_hasSum s (fun i _=> by dsimp only [f]; positivity) (hasSum_geometric_of_lt_one (r:=1/2) (by norm_num) (by norm_num))
    refine (Finset.sum_le_sum (g:= (fun i=> f i)) ?_).trans (hx.trans ?_)
    · intro i _; have he:f i ≤ 1:= pow_le_one₀ (by norm_num) (by norm_num); nlinarith [p i k, norm_nonneg (x k i), hz k i]
    norm_num
 let w(k:ℕ):lp E 2:=⟨x k,memℓp_gen' (hl k)⟩
 obtain ⟨A,u,t⟩:= inner_coalition w 2 (fun i=> lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2:ℝ≥0∞).toReal) (by norm_num) (hl i))
 refine ⟨A,fun i=>?_⟩; let p':lp E 2 →L[ℝ] E i:= lp.evalCLM ℝ E 2 i
 let I:= (c i)⁻¹; let T:= I • p'
 refine ⟨T u, Tendsto.congr' ?_ ((T.continuous.tendsto u).comp t)⟩
 refine Eventually.of_forall fun j =>?_; dsimp only [Function.comp_apply]; rw [map_sum]; refine Finset.sum_congr rfl fun k h=>?_; rw [map_smul]; apply congrArg ((A j).w k • ·); exact inv_smul_smul₀ (hc i).ne' (v i (j+k))
end lp
lemma Coalitions (H: ℕ→Hilbert)(v:∀ i:ℕ,ℕ→ H i)(T:∀ i, ∃ B:ℝ, ∀ᶠ k:ℕ in atTop, ‖v i k‖ ≤ B): ∃ A:ℕ→ Coalition, ∀ i,∃ u:H i,Tendsto (fun n=> ∑ j∈(A n).voters,((A n).w j:ℂ) • v i (n+j)) atTop (𝓝 u):=by
 letI(i:ℕ): InnerProductSpace ℝ (H i):= InnerProductSpace.rclikeToReal ℂ _
 have hb(i:ℕ):∃ B:ℝ,∀ k:ℕ, ‖v i k‖≤B:= by
    obtain ⟨C,h⟩:= T i; obtain ⟨n,t⟩:=eventually_atTop.mp h; let L:= ∑ j∈ Finset.range n, ‖v i j‖; refine ⟨max C L, fun k=>?_⟩; by_cases p:n≤ k; exact le_max_of_le_left (t k p)
    exact le_max_of_le_right (Finset.single_le_sum (fun j _=> norm_nonneg _) (Finset.mem_range.mpr (by omega)))
 choose B q using hb
 exact charter (E:=fun i=>(H i).space) v B q
end YM.SatinNucleus
#print axioms YM.SatinNucleus.Coalitions
