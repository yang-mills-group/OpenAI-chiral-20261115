import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib
/-!
# DiffOn even at blank interior seam as soon as continuous

 horizontal-split proof included. Used on actual reconstruction to propagate vanishing of
 translated-real-word distributions after Lorentz-boosting them (only in WickP space-time after
 Eu estimates). Continuous on boundary; won't appeal to all vectors analyt.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
open Complex Filter Function Set MeasureTheory Metric
open scoped Topology Interval
variable {E : Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
variable (U:Set ℂ)(f:ℂ→ E)(h:ContinuousOn f U)(D:∀ z∈U,z.re ≠0→ DifferentiableAt ℂ f z)
variable (z w:ℂ)(p: Rectangle z w ⊆ U)
include h D p
set_option maxHeartbeats 400000
lemma simpleBound (r:z.re≤w.re) (s:0 ≤ z.re ∨ w.re ≤0): wedgeIntegral z w f = -(wedgeIntegral w z f):=by
 rw [← add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq]
 refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w (h.mono p) ?_
 rintro x ⟨⟨v,k⟩,⟨e,u⟩⟩; refine (D x (p ⟨⟨le_of_lt v,le_of_lt k⟩,⟨e.le,u.le⟩⟩) ?_).differentiableWithinAt
 exact s.elim (fun t=> ((t.trans_eq (min_eq_left r).symm).trans_lt v).ne') (fun t=> ((lt_of_lt_of_le k ((max_eq_right r).le.trans t))).ne)
lemma joinedBound (r:z.re≤w.re): wedgeIntegral z w f=-(wedgeIntegral w z f):=by
 rcases le_total 0 z.re with v|u; · exact simpleBound U f h D z w p r (Or.inl v)
 rcases le_total w.re 0 with v|e; · exact simpleBound U f h D z w p r (Or.inr v)
 let c:ℂ:=⟨0,z.im⟩; let c':ℂ:=⟨0,w.im⟩
 have hs: Rectangle z c' ⊆ Rectangle z w:=by unfold Rectangle; apply inter_subset_inter _ (_root_.subset_refl _); apply preimage_mono; change [[z.re, (0:ℝ)]] ⊆ [[z.re,w.re]]; rw [uIcc_of_le u, uIcc_of_le r]; exact Icc_subset_Icc_right e
 have ht: Rectangle c w ⊆ Rectangle z w:=by unfold Rectangle; apply inter_subset_inter _ (_root_.subset_refl _); apply preimage_mono; change [[(0:ℝ),w.re]] ⊆ [[z.re,w.re]]; rw [uIcc_of_le e,uIcc_of_le r]; exact Icc_subset_Icc_left u
 have he:=simpleBound U f h D z c' (hs.trans p) u (Or.inr le_rfl); have hv:=simpleBound U f h D c w (ht.trans p) e (Or.inl le_rfl)
 rw [← add_eq_zero_iff_eq_neg,wedgeIntegral_add_wedgeIntegral_eq] at *
 dsimp only [c,c'] at he hv
 have HI(y:ℝ)(b:y∈ [[z.im,w.im]]): (∫ x:ℝ in z.re..(0:ℝ), f (x+y*I))+(∫ x:ℝ in 0..w.re, f (x+y*I))=(∫ x:ℝ in z.re..w.re,f (x+y*I)):=by
    apply intervalIntegral.integral_add_adjacent_intervals
    · apply ContinuousOn.intervalIntegrable; apply h.comp (f:=fun x:ℝ=> (x:ℂ)+y*I) (by fun_prop); intro a ha; refine p (hs ⟨?_,?_⟩);
      · simpa using ha
      simpa [c'] using b
    apply ContinuousOn.intervalIntegrable; apply h.comp (f:=fun x:ℝ=> (x:ℂ)+y*I) (by fun_prop); intro a ha; refine p (ht ⟨?_,?_⟩)
    · simpa [c] using ha
    simpa [c] using b
 rw [← HI z.im left_mem_uIcc,← HI w.im right_mem_uIcc]
 -- regroup additive abraded
 linear_combination (norm := abel) he+hv
omit p in
lemma shear (v:IsOpen U) : DifferentiableOn ℂ f U:= by
 
 apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn v).mp; refine ⟨fun z w p=> ?_,h⟩; rcases le_total z.re w.re with r|r; · exact joinedBound U f h D z w p r
 have e: Rectangle w z=Rectangle z w:=by unfold Rectangle; rw [uIcc_comm w.re,uIcc_comm w.im];
 rw [joinedBound U f h D w z (e ▸ p) r,neg_neg]
#print axioms simpleBound
#print axioms shear
omit p h D
set_option quotPrecheck false
local notation "P"=> ({z:ℂ|0≤ z.re})
local notation "Y"=> ({z:ℂ|0< z.re})
local notation "J"=> ({z:ℂ| z.re<0})
lemma crease (t:ℝ) (v: Continuous f) (h:DifferentiableOn ℂ f Y) (T:∀ᶠ r:ℝ in 𝓝 t, f ⟨0,r⟩=0) : EqOn f (fun _=>0) P:=by
 classical
 -- Use open strip ℝ ×ℂ ball(t,r) rather than ball. no open estimates beyond. Convex.
 obtain ⟨r,hr,k⟩:= Metric.eventually_nhds_iff_ball.mp T
 let U:=(Complex.im ⁻¹' Ioo (t-r) (t+r)); let G:= (P).piecewise f (fun _=>0)
 have HV: IsOpen U:= isOpen_Ioo.preimage continuous_im; have Hp:IsClosed P:=isClosed_le continuous_const continuous_re; have Hj:IsOpen J:=isOpen_lt continuous_re continuous_const; have Hy:IsOpen Y:=isOpen_lt continuous_const continuous_re; have Hd: Y⊆P:= fun z p=> show 0≤ z.re from le_of_lt p
 have fire:ContinuousOn G U:=by
    apply ContinuousOn.piecewise _ v.continuousOn continuousOn_const
    rintro z ⟨p,r'⟩
    have hb:z.re=0:= by
       have q:= frontier_subset_iff_isClosed.mpr Hp r'
       exact eq_of_le_of_not_lt (le_of_not_gt (fun e=> r'.2 ( interior_maximal Hd Hy e))) (not_lt.mpr (show 0≤ z.re from q))
    have he: f ⟨0,z.im⟩=0:= k _ (by rw [mem_ball, Real.dist_eq,abs_lt]; change t - r < z.im ∧ z.im < t + r at p; constructor<;> linarith [p.1,p.2]); change f z=0; exact (congrArg f (show z=⟨0,z.im⟩ from Complex.ext hb rfl)).trans he
 have hg(z:ℂ)(h:z∈J): G =ᶠ[𝓝 z] (fun _=>0):=by filter_upwards [Hj.mem_nhds h] with z h; exact piecewise_eq_of_notMem _ _ _ (not_le.mpr (show z.re<0 from h))
 have hf(z:ℂ)(h:z∈Y): G=ᶠ[𝓝 z] f:= by filter_upwards [Hy.mem_nhds h] with z h; exact piecewise_eq_of_mem _ _ _ (Hd h)
 have HE: AnalyticOnNhd ℂ G U:= by
    apply DifferentiableOn.analyticOnNhd _ HV; apply shear U G fire _ HV; intro z p d; rcases lt_or_gt_of_ne d with e|e; · exact (differentiableAt_const ..).congr_of_eventuallyEq (hg z e)
    exact (h.differentiableAt (Hy.mem_nhds e)).congr_of_eventuallyEq (hf z e)
 have HU(x:ℝ):( (⟨x,t⟩:ℂ))∈ U:= show t∈ Ioo (t-r) (t+r) from ⟨by linarith,by linarith⟩
 have hc:Convex ℝ U:= (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap
 have hu:EqOn G (fun _=>0) U:= HE.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc.isPreconnected (HU (-1)) (hg _ (show (-1:ℝ)<0 from neg_lt_zero.mpr zero_lt_one))
 let s:ℂ:=⟨1,t⟩; have hs:s∈Y:= (zero_lt_one : (0:ℝ)<1)
 have how:EqOn f (fun _=>0) Y:= (h.analyticOnNhd Hy).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const (convex_halfSpace_re_gt 0).isPreconnected hs ((hf s hs).symm.trans ((show ∀ᶠ u in 𝓝 s,u∈ U from HV.mem_nhds (HU 1)).mono fun z h=> hu h)) -- HP mono
 intro z e
 let S(x:ℝ):= z+(x:ℂ); have hm:Continuous S:= continuous_const.add continuous_ofReal
 change f z=0; apply Eq.trans (_ : f z=(f ∘ S) 0); swap; · simp [S];
 apply tendsto_nhds_unique_of_eventuallyEq ((v.comp hm).continuousAt.continuousWithinAt (x:=(0:ℝ))) (tendsto_const_nhds (x:=(0:E)) (f:=𝓝[>] (0:ℝ))) ?_
 filter_upwards [self_mem_nhdsWithin] with x h; exact how (show (S x) ∈ Y from add_pos_of_nonneg_of_pos (show 0≤ z.re from e) (show 0<x from h))
#print axioms crease
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
