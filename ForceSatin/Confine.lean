import ForceSatin.Wash
import ForceSatin.Coupon
-- orthogonal fee & mean-test kit. No representing different q on different spins.
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.Gleam.Luster.Risa.Gentle
open Function Filter MeasureTheory Metric Finset RG Lattice Wilson Tree Precision Pressure Exterior Next.Rank.Spindle Work.F03 Fineness Regis ProbabilityTheory Module
open scoped Topology ContDiff BigOperators Classical ENNReal
variable {c n:Side}{r:Ratio c n}{G:Gauge}{p:BudgetPoint}{v:Config G n}{S:Support n}
open WithLp
variable {J:Type*}[DecidableEq J]
def lot (S:Support n):Finset (Cell n × Bool × G.ColorIndex):=univ.filter fun i=> i.1.1∈ S
noncomputable abbrev traceNorm (S:Support n)(x:Altar G n):ℝ:= Real.sqrt (∑ i ∈ lot (G:=G) S,(x i)^2)
lemma traceNorm_p (X:Altar G n)(S:Support n):0≤traceNorm S X:=Real.sqrt_nonneg _
lemma traceNorm_sq (X:Altar G n)(S:Support n):traceNorm S X^2=∑ i ∈ lot (G:=G) S,(X i)^2:=Real.sq_sqrt (Finset.sum_nonneg (fun i _=>sq_nonneg _))
lemma traceNorm_mono {X:Altar G n}{S T:Support n}(p:S⊆T):traceNorm S X≤ traceNorm T X:=Real.sqrt_le_sqrt (sum_le_sum_of_subset_of_nonneg (fun i v=> mem_filter.mpr ⟨mem_univ _,p (mem_filter.mp v).2⟩) (fun i _ _=> sq_nonneg _))
lemma norm_gains {X:Altar G n}(S:Support n):traceNorm S X ≤ ‖X‖:=by
 apply (sq_le_sq₀ (traceNorm_p ..) (norm_nonneg _)).mp; rw [traceNorm_sq,EuclideanSpace.real_norm_sq_eq]; exact sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ..) (fun i _ _=> sq_nonneg _)
theorem orthogonal_fee (L:Finset J)(S:J→Support n)(p:Set.PairwiseDisjoint (L:Set J) S)(X:Altar G n): ∑ i∈L,traceNorm (S i) X≤Real.sqrt L.card*‖X‖:=by
 apply (sq_le_sq₀ (sum_nonneg (fun i _=>traceNorm_p ..)) (by positivity)).mp
 apply (show (∑ i∈L,traceNorm (S i) X)^2≤ ↑L.card* (∑ i∈L,traceNorm (S i) X^2) from by simpa using (sum_mul_sq_le_sq_mul_sq L (fun _=> (1:ℝ)) (fun i=>traceNorm (S i) X))).trans
 rw [mul_pow,Real.sq_sqrt (by positivity), EuclideanSpace.real_norm_sq_eq]
 simp_rw [traceNorm_sq]; apply mul_le_mul_of_nonneg_left _ (by positivity)
 rw [← Finset.sum_biUnion (t:=fun i=>lot (G:=G) (S i)) ?_]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> sq_nonneg _)
 intro i v j t k; apply disjoint_left.mpr; intro x h w; exact disjoint_left.mp (p v t k) (mem_filter.mp h).2 (mem_filter.mp w).2
noncomputable abbrev fullLease (A:Support c)(D:Finset (Cell n))(S:Support n)(r:Ratio c n)(m:ℕ):Prop:=∀ i∈S, stint r m A D i
theorem fullLease_p (m:ℕ)(A:Support c)(D:Finset (Cell n))(r:Ratio c n)(j:Odd r.count.val) (wH:hallBill m≤r.count.val/2)(L:Finset J)(S:J→Support n)(p:Set.PairwiseDisjoint (L:Set J) S) :
 (∑ i∈L,if fullLease A D (S i) r m then (0:ℝ) else 4)≤ snags r m A D:=by
 let W:= L.filter (fun i=>¬fullLease A D (S i) r m)
 let F:=snagS r A D m (id:Site n→Site n)
 have he(i:W): ∃ v∈S i.val,v∈F:=by
    have v:= (mem_filter.mp (show i.val∈L.filter _ from i.property)).2; change ¬ (∀ u∈ S i.val,stint r m A D u) at v; push Not at v; obtain ⟨x,t,q⟩:=v; exact ⟨x,t,(by simp only [F,snagS,mem_filter, mem_univ, id_eq, q]; tauto)⟩
 choose f h w using he; let g(i:W):F:=⟨f i,w i⟩
 have hk:f.Injective:=fun i j e=>Subtype.ext (by by_contra v; exact disjoint_left.mp (p (mem_filter.mp i.property).1 (mem_filter.mp j.property).1 v) (h i) (e.symm ▸ h j))
 rw [Finset.sum_ite,sum_const_zero,sum_const,nsmul_eq_mul,zero_add,mul_comm]; apply le_trans _ (snag_cover (r:=r) j wH (id:Site n→Site n) injective_id A D)
 change (4:ℝ)*W.card ≤ _; apply mul_le_mul_of_nonneg_left _ (by norm_num); exact Nat.cast_le.mpr (by change W.card ≤ F.card; rw [← Fintype.card_coe W,← Fintype.card_coe F]; exact Fintype.card_le_of_injective g (fun i j e=> hk (congrArg Subtype.val e)))
variable {A:Support c}{D:Finset (Cell n)}{Z:PathData G}{H:Bed}{Y:Altar G n→ℝ}{q:Clip}{κ β C K l u ℓ a ψ Υ s v' x:ℝ}{T:Forest r}{m:ℕ}{Φ:Config G n→ℝ}
variable (B:Z.Bounds q a C K)(P:Attached H Z)
-- κ=near-cut fraction; ψ step cost (dosed), u amplitude through turnout, ℓ local Lip allowance. U expectation budget incl when approving exact flat of Wick. s trust logs fee, v' sax. 
structure Stamp (B:Z.Bounds q a C K)(P:Attached H Z)(p:BudgetPoint)(T:Forest r)(A:Support c)(D:Finset (Cell n))(S:Support n)
    (m:ℕ)(κ β ψ u ℓ Υ s v':ℝ)(f:Config G n→ℝ)(Y:Altar G n→ℝ) : Prop where
 regular : ContDiff ℝ 1 Y
 wallet(t) : |Y t|≤ u
 along(t y): |Y t-Y y|≤ ℓ*traceNorm S (t-y)
 stamp : TreeLease B P p T m κ β s (ψ+ if fullLease A D S r m then 0 else 4) v' A D f Y
 mean_p : plumeCost B P Y 1 ≤ Υ
namespace Stamp
-- integrate top even across failures, using ℓ only, no need support norm in party's Y part. Dp each term key ∈ L.
theorem high_day (L:Finset J)(S:J→Support n)(F:J→ Config G n→ℝ)(Y:J→Altar G n→ℝ)(hg:0≤ℓ)
    (v:Set.PairwiseDisjoint (L:Set J) S)(p':∀ j∈L,Stamp B P p T A D (S j) m κ β ψ u ℓ Υ s v' (F j) (Y j))
    (hj:Odd r.count.val)(x: hallBill m ≤ r.count.val/2) : let G₀(t:Altar G n):= ∑ i∈L,Y i t
       ContDiff ℝ 1 G₀ ∧ (∀ t,|G₀ t|≤ L.card*u) ∧
       (∀ t,‖fderiv ℝ G₀ t‖≤ ℓ*Real.sqrt (L.card:ℝ)) ∧
        TreeLease B P p T m κ β s (L.card*ψ+snags r m A D) v' A D (fun V=> ∑ i∈L,F i V) G₀ ∧ plumeCost B P G₀ 1 ≤ L.card * Υ:=by
 intro W; let H:NNReal:=⟨ℓ*Real.sqrt (L.card:ℝ),mul_nonneg hg (Real.sqrt_nonneg _)⟩
 refine ⟨ContDiff.sum (fun i h=> (p' i h).regular),fun t=>?_ ,fun u=>?_ ,?_,?_⟩
 · exact (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>u) fun i h=>(p' i h).wallet t).trans_eq (by rw [sum_const,nsmul_eq_mul]))
 · refine norm_fderiv_le_of_lipschitz ℝ (C:=H) (LipschitzWith.of_dist_le_mul fun U V=>?_) -- norm
   rw [dist_eq_norm,dist_eq_norm,Real.norm_eq_abs]; unfold W; rw [←sum_sub_distrib]
   refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun i=> ℓ*traceNorm (S i) (U-V)) fun i h=> (p' i h).along ..).trans ?_)
   rw [←mul_sum]; exact (mul_le_mul_of_nonneg_left (orthogonal_fee L S v _) hg).trans_eq (mul_assoc ..).symm
 · intro V U t y i j l h; dsimp only; apply (sum_le_sum (g:=fun i=>Y i (starFee B P r A D m y β t)+(ψ+if fullLease A D (S i) r m then 0 else 4)) fun x hx=>(p' x hx).stamp V t y i j l h).trans
   rw [sum_add_distrib,sum_add_distrib,sum_const,nsmul_eq_mul]; gcongr; exact fullLease_p _ _ _ _ hj x L S v -- tune
 unfold plumeCost W; rw [one_mul,integral_finsetSum]; swap; · intro i hi; let p:= p' i hi; let U:=stdGaussian (Altar G n)
                                                              apply Envelope.integrable (Envelope.mk _ ⟨u,fun x=>p.wallet _⟩) U; exact p.regular.continuous.measurable.comp (ContinuousLinearMap.continuous _|>.measurable)
 apply (sum_le_sum (g:=fun _=> Υ) fun i hi=>?_).trans_eq (by rw [sum_const,nsmul_eq_mul]); simpa only [plumeCost,one_mul] using (p' i hi).mean_p
#print axioms _root_.YM.Gleam.Luster.Risa.Gentle.fullLease_p
#print axioms high_day
end Stamp
end YM.Gleam.Luster.Risa.Gentle
