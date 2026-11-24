import YM.SU5.Selected.Rail.Lys
/-! # Sampling even when turbulent x tends root. $hammer$ slope coordinate signed real p≥4.
Multiple moments. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
open Finset
local notation "A"=> Aop
variable {k:ℕ}(p:3≤k){x:Facet3}(h:x∈Cliff)
local notation "D"=> Set.Icc (-π) π
lemma embark_m (x:Facet3)(t:x∈hill)(s:ℝ)(z:s∈ D): Ε x s ∈ stemGuard:=by
 apply stemG.mpr; apply (pi_norm_le_iff_of_nonneg pi_pos.le).mpr; intro i; cases i using Fin.lastCases <;> first|exact (node₃ x s).symm ▸ (abs_le.mpr z)|rw [nodeV]; exact abs_le.mpr (hillv t _)
lemma hook (x:Facet3 ×ℝ)(p:x∈hill ×ˢ D): joinBin x∈stemGuard:= embark_m _ p.1 _ p.2 -- syntax
lemma deck_integrable_of_c {U:Type*}[NormedAddCommGroup U]{f:ℝ→ U}(p:ContinuousOn f (D)) : Integrable f (volume.restrict deck):=(p.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
def aroma (k:ℕ)(n:ℕ)(x:Facet3)(t:ℝ):ℂ:= surge n t*beat k (Ε x t) 2 0
def hammer(k:ℕ)(n:ℕ)(x:Facet3):ℂ:=∫ t in deck, aroma k n x t
private lemma keep {X:Type*}[PseudoMetricSpace X]{K:Set X}(p:IsCompact K){V: X×ℝ→ℂ}(h:ContinuousOn V (K ×ˢ Set.Icc (-π) π)) : ContinuousOn (fun (x:X)=> ∫ s in deck,V (x,s)) K:=by
 intro x hx; obtain ⟨u,k⟩:= (p.prod (isCompact_Icc)).bddAbove_image h.norm; let μ:= volume.restrict deck; haveI:IsFiniteMeasure μ:= inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioc (-π) π))); apply tendsto_integral_filter_of_dominated_convergence (μ:=μ) (fun i=>u) ?_ ?_ (integrable_const _) ((ae_restrict_mem measurableSet_Ioc).mono (fun i w => ?_))
 · filter_upwards [eventually_mem_nhdsWithin] with x l; exact ((h.comp (by fun_prop) (show Set.MapsTo (fun i:ℝ=>(x,i)) deck (K ×ˢ _) from fun _ e=>⟨l, e.1.le,e.2⟩))).aestronglyMeasurable measurableSet_Ioc -- use metric separable
 · filter_upwards [eventually_mem_nhdsWithin] with x l; filter_upwards [ae_restrict_mem measurableSet_Ioc] with y i; exact k ⟨(x,y),⟨l,i.1.le,i.2⟩,rfl⟩
 exact (h.comp (by fun_prop) (show Set.MapsTo (fun x:X=>(x,i)) K _ from fun _ e=>⟨e,w.1.le,w.2⟩) _ hx) -- tune
lemma hill_compact : IsCompact hill:= isCompact_closedBall ..
include p
lemma aroma_c(n:ℕ): ContinuousOn (Function.uncurry (aroma k n)) (hill ×ˢ D):=by
 let T:= hill ×ˢ D; let U(x:Op SpinIdx):= x 2 0; have he:Continuous U:= (continuous_apply _).comp (continuous_apply 2); let Y:Facet3×ℝ→ Op SpinIdx:= beat k ∘ joinBin; have h: ContinuousOn Y T:=(beating p).comp join_cont.continuousOn (fun x p=>hook x p)
 exact ((surge_cont.comp (continuous_const.prodMk continuous_snd)).continuousOn).mul (he.continuousOn.comp h (Set.mapsTo_univ _ _)) -- matrix topology reducible
lemma hammer_c (n:ℕ): ContinuousOn (hammer k n) hill:= keep hill_compact (aroma_c p n)
omit p
include h
lemma aroma_spec (n:ℕ): ContinuousOn (aroma k n x) (D):=by
 let f:=fun t:ℝ=> Ε x t; have he:Continuous f:= join_cont.comp (continuous_const.prodMk continuous_id)
 let T:= stemGuard; have h'(i:Axis):ContinuousOn (fun s=> tough (f s) i) (D):= by
    intro y u; exact (timbre i (embark_m x h.1 _ u) (powerV h y)).comp (he.continuousOn _ u) (fun t u=> embark_m _ h.1 _ u)
 unfold aroma; simp_rw [artP,arc_lo]; apply ContinuousOn.mul (surge_cont.comp (continuous_const.prodMk continuous_id)).continuousOn; refine ContinuousOn.mul ((fleece_c k).comp he).continuousOn ?_; exact (h' 2).add (continuousOn_const.mul (h' 3)) -- tune
lemma progression (n:ℕ): hammer (k+1) n x= hammer k n x-hammer k (n+1) x:=by
 unfold hammer; rw [←integral_sub (deck_integrable_of_c (aroma_spec h _)) (deck_integrable_of_c (aroma_spec h _))]; congr 1; funext i; unfold aroma; simp_rw [artP,fleece,node₃]; rw [pow_succ,fade, Nat.cast_add,Nat.cast_one,surge_left]; ring
-- hammers summation positivity
local notation "E"=> tempoE
local notation "u" x:max v:max=> dollar x v
def stake(k:ℕ)(n:ℕ)(x:Facet3)(v:FaceL):ℝ:= (1-u x v)^k* summer true n x v
lemma stake_pos (k n:ℕ)(v:FaceL):0 ≤ stake k n x v:= mul_nonneg (pow_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (born_e v h).le))) _) (pret v h n)
omit h in
lemma script_add (k n c:ℕ)(v:FaceL):stake k (n+c) x v=stake k n x v*(u x v)^c:=by rw [stake,step_b,←mul_assoc];rfl
lemma counts_t {n:ℕ}(e:4≤n): HasSum (fun v=> (stake k n x v:ℂ)) (hammer k n x):=by
 induction k generalizing n with
 | zero=> simpa only [hammer,aroma,artP,fleece,pow_zero,stake,one_mul, Int.cast_natCast, thru] using haunts h n e
 | succ k ih=>
    rw [progression h]; apply (show HasSum _ _ from (ih e).sub (ih (by omega :4 ≤ n+1))).congr_fun -- target might fail
    intro v; rw [← Complex.ofReal_sub,script_add]; unfold stake; rw [pow_succ,pow_one]; congr 1; ring
-- tune
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms counts_t
#print axioms stake_pos
#print axioms progression
#print axioms hammer_c
#print axioms aroma_c
