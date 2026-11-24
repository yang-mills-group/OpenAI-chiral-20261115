import YM.SU5.WakeInvestment.MarginShelf
import SatinThinIncense
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Gleam.Wake
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric Exterior Precision Next.Rank.Spindle Pressure Work.F03 Next.SectorChange Next.SectorChange.Gaussian
open Fineness Matrix Module Regis Regis.Head clocks
open scoped Matrix BigOperators Classical ContDiff Topology MatrixOrder ENNReal Kronecker Matrix.Norms.Frobenius NNReal
variable {c n : Side}{r:Ratio c n}{T:Forest r}{G:Gauge}{p:BudgetPoint}{q:Clip}{v t η C S w δ β κ ξ Λ:ℝ}{U:Config G n}{A:Support c}{o x z:Site n}{f m:ℕ} {X:T.Slice G}{Y:LinkArray G (Blip T (univ : Finset T.Free))} {R:Rules G} {Z:PathData G}{b:Cell n}{H:Bed}{F:Finset T.Free}{J:ChartRatio G}
variable (B:Z.Bounds q η C S) (P:Attached H Z)(L_:Floor H q n δ w)(D:LocalRatio J)
/-! # Hodge of leading polynomial
 Terminology: Φ is **real** signed projection. `Forecast` expects qualifier on its smooth
 cost-accounting interpolation on full `Altar`; not saying function Φ itself is smooth even after good.
 Usually buy this for each chosen tag via constructing masked leading polynomial with path transport.
 As usual Ψ_t prices ``actually θ-rotated`` one, smallness of `clouds` bought from reading
 its finite-torus Wick purchase, compare full unclipped mean paying tail, before accepting this tag.
 All these orientations can be asked **even when** the gathering. -/

-- spatial variance room
abbrev Watershed (G:Gauge)(n:Side):= Cell n × Bool × G.ColorIndex
def vase (G:Gauge)(n:Side)(S:Support n) : Altar G n→ₗ[ℝ] Altar G n where
 toFun x:= WithLp.toLp 2 (fun i:Watershed G n=> if i.1.1∈S then x i else 0)
 map_add' x y:=by ext i; change (if i.1.1∈S then x i+y i else 0)= (if i.1.1∈S then x i else 0)+(if i.1.1∈ S then y i else 0); split; rfl; rw [add_zero]
 map_smul' x y:=by ext i; change (if i.1.1∈S then x*(y i) else 0)= x*(if i.1.1∈S then y i else 0); split; rfl; rw [mul_zero]
variable {I:Type*}[Fintype I]
lemma vase_lend (σ:I→Support n)(p:Set.PairwiseDisjoint Set.univ σ)(x:Altar G n): ∑ i:I, ‖vase G n (σ i) x‖^2 ≤ ‖x‖^2:=by
 let W(i:Watershed G n)(j:I):= vase G n (σ j) x i; simp_rw [EuclideanSpace.real_norm_sq_eq]; rw [sum_comm]; apply sum_le_sum; intro i _; change (∑ j, W i j ^2) ≤ _;
 by_cases h:∃j, i.1.1∈σ j
 · obtain ⟨j,u⟩:=h; rw [sum_eq_single j]; · exact (le_of_eq (by rw [show W i j=x i from if_pos u]))
   · intro k _ w; rw [show W i k=0 from if_neg (fun h=> disjoint_left.mp (p (Set.mem_univ k) (Set.mem_univ _) w) h u),zero_pow (by decide:(2:ℕ)≠0)]
   simp
 push Not at h; rw [sum_eq_zero fun j (_:j∈univ)=>by rw [show W i j=0 from if_neg (h j),zero_pow (by decide:(2:ℕ)≠0)]]; exact sq_nonneg _
lemma vase_close (S:Support n)(x:Altar G n) : ‖vase G n S x‖ ≤ ‖x‖:= by
 let V:= vase_lend (fun j:Unit=>S) (fun i _ j _ z=>False.elim (z (Subsingleton.elim i j))) x; apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (norm_nonneg _); simpa using V

lemma vista_spill (σ:I→Support n)(p:Set.PairwiseDisjoint Set.univ σ)(t:Signed)(b:Site n) : Set.PairwiseDisjoint Set.univ (fun i=> (σ i).image (affine t b)):=fun i h j l v=> Finset.disjoint_left.mpr (fun u m r=>by
 obtain ⟨a,f,rfl⟩:=mem_image.mp m; obtain ⟨bb,v',g⟩:=mem_image.mp r; exact Finset.disjoint_left.mp (p h l v) f ((t.act_injective (add_right_cancel g)) ▸ v'))
-- gathered scenery. all rates real
structure Forecast (B:Z.Bounds q η C S)(P:Attached H Z)(C:ℝ)(p:BudgetPoint)(r:Ratio c n)(m:ℕ)(α β s k a t:ℝ) (T:Support n)(φ:Config G n →ℝ) : Prop where
 env: Envelope φ
 price_: ∀ i, |φ i|≤ C
 inv: GaugeInvariant φ
 lead: ∀ v:Signed,∀ x:Site n, let U:= T.image (affine v x); ∃ W:Altar G n→ℝ, ContDiff ℝ 1 W ∧ (∀ i,|W i|≤ C) ∧ (∀ z w, |W z-W w| ≤ C*‖vase G n U (z-w)‖) ∧ |clouds B P W|≤ t ∧ ∀ A:Support c,∀ Y0:Finset (Cell n),∀ (V: Config G n)(D Y:fieldDir G n 1), A=broken r k V → Y0=misdemean (α*p.threshold) V → ProbeBox (D+Y) (2*s) → TrustLogs (D+Y) V r A s → (∀ i∈ U, withinCore r A (face_anchors Y0) (hallBill m) i) → |φ (pull v x V) - W (starFeed B P r A (face_anchors Y0) m Y β D)| ≤ a

lemma lacking (σ:I→Support n)(p:Set.PairwiseDisjoint Set.univ σ)(U:Support n) : (univ.filter fun i=> ¬σ i ⊆ U).card ≤ Uᶜ.card:=by
 let T:= univ.filter fun i=> ¬σ i⊆ U; have hv (i: ↥T):∃ j : Site n, j∈ σ i.val ∧ j ∈ Uᶜ:=by
    obtain ⟨z,t,v⟩:= not_subset.mp (mem_filter.mp i.property).2; exact ⟨z,t,mem_compl.mpr v⟩
 choose g h he using hv; let X (i:↥T): ↥(Uᶜ):= ⟨g i, he i⟩; refine card_le_card_of_injective (f:=X) (fun i j v=> Subtype.ext ?_); by_contra e; apply disjoint_left.mp (p (Set.mem_univ i.val) (Set.mem_univ j.val) e) (h i); rw [show g i=g j from congrArg Subtype.val v]; exact h j

def spectacles (φ:I → Config G n→ℝ)(U:Config G n):ℝ:=∑ i, φ i U
variable {σ:I→Support n}{φ:I → Config G n→ℝ}{Ca s α k a :ℝ}
lemma scenery (p':Set.PairwiseDisjoint Set.univ σ) (h:∀ i, Forecast B P Ca p r m α β s k a t (σ i) (φ i))(v:Signed)(x:Site n)(hR:Odd r.count.val)(hT:hallBill m ≤ r.count.val/2)(hC:0≤Ca)(ha:0≤a)(z:ℝ)(v0:2*Ca≤4*z) : ∃ W:Altar G n→ℝ, ContDiff ℝ 1 W ∧ (∀ i,|W i| ≤ Ca*↑(Fintype.card I)) ∧ (∀ i, ‖fderiv ℝ W i‖ ≤ Ca*Real.sqrt (↑(Fintype.card I))) ∧ plumeCost B P W 1 ≤ (Fintype.card I:ℝ)* t ∧ ∀ A:Support c, ∀ D:Finset (Cell n), nearScene B P p r m β s k (α*p.threshold) ((Fintype.card I:ℝ)*a+ z*(trap r m A+trap_s m D)) A D 1 ((spectacles φ) ∘ pull v x) W:=by
 choose W hW hp hl hc hf using (fun i=>(h i).lead v x); let τ(i:I):= (σ i).image (affine v x); let H':= fun x=> ∑ i:I,W i x; let S:= Real.sqrt (Fintype.card I); have ht:= vista_spill σ p' v x
 have he: ContDiff ℝ 1 H':=ContDiff.sum (fun i _=> hW i); refine ⟨H',he,fun x=>?_,fun i=>?_,?_,?_⟩
 · exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=>hp i x)).trans_eq (by simp; ring))
 · let D:ℝ≥0:=⟨Ca*S,mul_nonneg hC (Real.sqrt_nonneg _)⟩; apply norm_fderiv_le_of_lipschitz ℝ (C:=D); refine LipschitzWith.of_dist_le_mul (fun x y=>?_)
   unfold H'; let V i:= ‖vase G n (τ i) (x-y)‖; rw [dist_eq_norm, Real.norm_eq_abs, ←sum_sub_distrib,dist_eq_norm]; apply (abs_sum_le_sum_abs ..).trans; apply le_trans (sum_le_sum (fun i _=> hl i x y)); rw [←mul_sum]; change Ca* (∑ i:I,V i)≤Ca*S*_; rw [mul_assoc]
   have h:Real.sqrt (∑ i:I,V i^2)≤ ‖x-y‖ := by apply (Real.sqrt_le_sqrt (vase_lend τ ht (x-y))).trans_eq; exact Real.sqrt_sq (norm_nonneg _)
   have ht1:=Real.sum_mul_le_sqrt_mul_sqrt univ (fun i:I=>1) V; simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one] at ht1
   exact mul_le_mul_of_nonneg_left (ht1.trans (mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _))) hC
 · rw [plumeCost,one_mul,cloud_turn B P _ he.continuous]; unfold H' clouds; rw [integral_finsetSum]; swap; · exact fun i _=> Regis.bree _ _ (((hW i).continuous.comp continuous_subtype_val).measurable) fun j=>hp i _
   exact (sum_le_sum (fun i _=> (le_abs_self (clouds B P (W i))).trans (hc i))).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])
 intro A E U D Y hd g ug lg; let T:= univ.filter (withinCore r A (face_anchors E) (hallBill m)); let R:= univ.filter fun i=> ¬ τ i ⊆ T; let Y':=starFeed B P r A (face_anchors E) m Y β D
 have hx (i:I): φ i (pull v x U) - W i Y' ≤ a + if i∈ R then 2*Ca else 0:=by
    split; swap
    · rename_i H; rw [add_zero]; apply (le_abs_self _).trans; refine hf i A E _ D Y hd g ug lg fun i k=>?_ ; exact (mem_filter.mp ((of_not_not (fun h=> H (mem_filter.mpr ⟨mem_univ _,h⟩))) k)).2
    apply le_trans _ (le_add_of_nonneg_left ha); linarith only [le_abs_self (φ i (pull v x U)),(h i).price_ (pull v x U),neg_le_abs (W i Y'),hp i Y']
 have htR: (R.card:ℝ)*(2*Ca) ≤ z*(trap r m A+trap_s m E):=by
    have hw:R.card≤Fintype.card (Site c)*largerBill r.count.val (hallBill m)+ A.card * r.count.val^4+ E.card*coldBill (hallBill m):= (lacking τ ht T).trans (by rw [show Tᶜ= _ from (show Tᶜ=univ.filter (fun i=> ¬ withinCore r A (face_anchors E) (hallBill m) i) by ext; simp [T])]; exact land_fee A E hR hT)
    let μ:ℝ:=Fintype.card (Site c)* (largerBill r.count.val (hallBill m):ℕ)+ A.card*(r.count.val:ℝ)^4+E.card*(coldBill (hallBill m):ℕ); have hv : (R.card:ℝ) ≤ μ:= by unfold μ; exact_mod_cast hw
    rw [show trap r m A+trap_s m E=4*μ from by unfold trap trap_s μ; ring]; nlinarith only [mul_le_mul_of_nonneg_left v0 (show 0 ≤ μ by unfold μ; positivity),mul_le_mul_of_nonneg_right hv hC]
 have he:= sum_le_sum (s:=univ) (fun i _=> hx i); rw [sum_sub_distrib,sum_add_distrib,←sum_filter] at he; simp only [filter_mem_eq_inter,univ_inter,sum_const,card_univ,nsmul_eq_mul] at he
 simp only [Function.comp_apply,one_mul]; unfold spectacles H'; linarith only [he,htR]
#print axioms scenery
end YM.Gleam.Wake
