import YM.SU5.Relativistic.Glisten
/-! # Quantitative signs and oblique rates for finite-cost kernel. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I

variable {U:Set Behind}(H:IsCompact U)(h:U ⊆ sunshine)
local notation "V"=> U ×ˢ Set.Icc (-π) π
local notation "L"=>Set.Icc (-π) π
variable {s:Finset ℤ}{c:Behind→ℤ→ℝ}
variable {a:ℝ}
structure Cuest (s:Finset ℤ)(c:Behind→ℤ→ℝ)(a:ℝ) : Prop where
 cont : ∀ j,Continuous fun k=> c k j
 stays : ∀ k∈sunshine,∀ b:Bool,(∀ j,0≤ speaker s c k j b)∧(∃ j,0<speaker s c k j b)∧∀ j,amp k j<a→speaker s c k j b=0
namespace Cuest
variable (C: Cuest s c a)
def outlined (i:Axis)(s:Finset ℤ)(c:Behind→ℤ→ℝ)(k:Behind)(t:ℝ) := swell s c k t * heatLine k t i
def etched (s:Finset ℤ)(c:Behind→ℤ→ℝ)(k:Behind)(t:ℝ) := swell s c k t * faceR k t
include C H h
lemma swirling : Continuous (fun x:Behind × ℝ=> swell s c x.1 x.2):= (continuous_finsetSum _ fun i _=> (Complex.continuous_ofReal.comp ((C.cont i).comp continuous_fst)).mul (surge_cont.comp (continuous_const.prodMk continuous_snd))) -- maybe remove inclusion
lemma outline_c (i:Axis): ContinuousOn (uncurry (outlined i s c)) V:= ((swirling H h C).continuousOn).mul (heat_cont H h i)
lemma etch_c : ContinuousOn (uncurry (etched s c)) V:= ((swirling H h C).continuousOn).mul ((heat_cont H h _).sub (continuousOn_const.mul (heat_cont H h TA)))
omit H h
variable (b:Bool)(n:ℤ)(hL:∀ u∈s, (4:ℝ) ≤ sg b*(n+u:ℤ)) {k: Behind}(p:k∈sunshine)
include b n hL p
lemma outlined_price (i:Axis): HasSum (fun j=> (speaker s c k j b:ℂ)*axialB k j b i n) (pluse n (outlined i s c k)):=by
 let f(t:ℝ):=heatLine k t i
 apply bounds b p s c f (continuous_cut (U:={k}) (fun x t=> heatLine x t i) (heat_cont (U:={k}) isCompact_singleton (Set.singleton_subset_iff.mpr p) i) (Set.mem_singleton _)) _
 intro j v; simp_rw [←axial_advance]; exact bladeV p b (n+j) i (hL j v)
lemma outlineVertical : HasSum (fun j=>‖(speaker s c k j b:ℂ)*axialB k j b TA n‖) ((-(↑(sg b):ℂ)*I * pluse n (outlined TA s c k)).re):=by
 have he:= Complex.hasSum_re ((outlined_price C b n hL p TA).mul_left (-(↑(sg b):ℂ)*I))
 refine he.congr_fun ?_ -- hasSum.congr_fun?
 intro j
 rw [mul_left_comm,axial_vertical p b n, ←Complex.ofReal_mul,Complex.ofReal_re,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((C.stays k p b).1 j)] -- tune
lemma pressing : 0<sg b*(pluse n (etched s c k)).re:=by
 let Y:Set Behind:= {k}; let f:ℝ→ℂ:=faceR k
 have hc:IntegrableOn f screen:= continuous_cut faceR (U:=Y) (ContinuousOn.sub (heat_cont (U:=Y) isCompact_singleton (Set.singleton_subset_iff.mpr p) _) (continuousOn_const.mul (heat_cont (U:=Y) isCompact_singleton (Set.singleton_subset_iff.mpr p) TA))) (Set.mem_singleton _)
 let r(j:WalkA):= tears k j * pulseCost k b j * nodes b k j n
 have hp:HasSum (fun j=> (speaker s c k j b:ℂ)*(r j:ℂ)) (pluse n (etched s c k)) :=by
    apply bounds b p s c f hc
    intro j u; have hv:= signedV p b (n+j) (hL j u); rw [show pluse (n+j) f= pluse (n+j) (faceR k) from rfl]
    simp_rw [nodes,Int.cast_add,mul_add,Real.exp_add, ←mul_assoc,Complex.ofReal_mul] at hv; simp only [r,Complex.ofReal_mul,nodes,←mul_assoc]; exact hv
 let q(j:WalkA):=speaker s c k j b*(sg b*r j)
 have hq:HasSum q (sg b*(pluse n (etched s c k)).re):=by
    have hv:=(Complex.hasSum_re hp).mul_left (sg b); simp_rw [← Complex.ofReal_mul,Complex.ofReal_re] at hv; simp only [q,mul_left_comm (speaker s c k _ b)]; exact hv -- tune
 rw [←hq.tsum_eq]; have he(j):0<sg b*r j:=by unfold r; rw [←mul_assoc, mul_left_comm, ←mul_assoc]; -- rw tuning
                                              rw [mul_assoc (tears ..)]; exact mul_pos (mul_pos (tear_pos p _) (strictV p b j)) (Real.exp_pos _)

 obtain ⟨j,g⟩:= (C.stays k p b).2.1
 exact hq.summable.tsum_pos (fun i=>mul_nonneg ((C.stays k p b).1 i) (he i).le) j (mul_pos g (he j)) -- inference

include H h n
omit p
-- all points after n to one side relativistic. budget above x already pre-axis rates.
lemma budgetStep : ∃ B:ℝ,0<B ∧ ∀ k∈U,∀ q:ℤ, 0 ≤ sg b*q → ∀ i:Axis, ‖pluse (n+q) (outlined i s c k)‖ ≤ B*Real.exp (-a*(sg b*(q:ℝ))):=by
 let f(k):= (-(↑(sg b):ℂ)*I*pluse n (outlined TA s c k)).re; have hf:ContinuousOn f U:= (Complex.continuous_re).comp_continuousOn (continuousOn_const.mul (circle_continuous _ _ (outline_c H h C TA) H))
 obtain ⟨B,E⟩:= H.exists_bound_of_continuousOn hf; refine ⟨|B|+1, (by positivity), fun k p q v i=>?_⟩
 have hh:=h p
 have ht:∀ j∈s,4≤ sg b*(n+q+j:ℤ) :=by intro j v'; push_cast; have he:=hL j v'; push_cast at he; nlinarith
 let Z:=(speaker s c k · b)
 let W:=Real.exp (-a*(sg b*(q:ℝ)))
 have hw:=outlined_price C b (n+q) ht hh i
 have hp:= outlineVertical C b n hL hh
 rw [← hw.tsum_eq]
 apply (norm_tsum_le_tsum_norm (hw.summable.norm)).trans
 let r(j):=‖(Z j:ℂ)*axialB k j b TA n‖
 refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_trans (((le_abs_self (f k)).trans (E k p)).trans (le_abs_self _)) (le_add_of_nonneg_right zero_le_one)) (Real.exp_pos _).le) -- wrong name
 calc
    _ ≤ ∑' j:WalkA,r j*W := Summable.tsum_le_tsum (fun j=>?_ ) hw.summable.norm (hp.summable.mul_right W)
    _ = f k*W := (hp.mul_right W).tsum_eq
 by_cases hx : amp k j<a; · rw [show speaker s c k j b=0 from (C.stays k hh b).2.2 j hx]; simp only [Complex.ofReal_zero, zero_mul,norm_zero]; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
 rw [axial_advance b n]; unfold r Z; simp only [norm_mul,nodes,Complex.norm_real]; rw [Real.norm_of_nonneg ((C.stays k hh b).1 j),Real.norm_of_nonneg (Real.exp_pos _).le,mul_assoc]; apply mul_le_mul_of_nonneg_left _ ((C.stays k hh b).1 j); refine mul_le_mul (axial_length hh b n j i) ?_ (by positivity) (norm_nonneg _); exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith : -amp k j ≤ -a) v)
end Cuest
end YM.CF.Crest.Sleet
