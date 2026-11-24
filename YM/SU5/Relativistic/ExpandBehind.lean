import YM.SU5.Relativistic.TurnedBill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Fock Lat UnitAddTorus
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
-- attribute typo for screen_fin local instance
attribute [local instance] screen_fin

def atlas(k:Behind):Rim (Fin 3) := dress (Fin 3) fun i=> k i/(2*π)
lemma atlas_c:Continuous atlas:= by refine (dressed _).continuous.comp (continuous_pi ?_); exact fun i=> (continuous_apply i).div_const _
lemma atlas_onto : IsQuotientMap fun k:↥backPane=> atlas k.val:=by
 haveI:CompactSpace ↥backPane:= isCompact_iff_compactSpace.mp (isCompact_univ_pi fun i=> isCompact_Icc)
 apply IsQuotientMap.of_surjective_continuous _ (atlas_c.comp continuous_subtype_val)
 intro x; let e:= AddCircle.equivIco 1 (-(1/2:ℝ)); let k: Behind:=fun i=> φ*(e (x i)).val
 have hu:k∈ backPane:=by
    intro i _; let w:ℝ:=(e (x i)).val; have he:-(1/2:ℝ) ≤ w:= (e _).property.1; have ht:w≤1/2:=by linarith only [(show w< -(1/2:ℝ)+1 from (e _).property.2)]
    change _ ≤ φ*w ∧ _; constructor
    · nlinarith only [pi_pos,he]
    change φ*w≤π; nlinarith only [ht,pi_pos]
 refine ⟨⟨k,hu⟩,?_⟩; funext i; change ((φ*(e (x i)).val /(2*π):ℝ):UnitAddCircle)=x i; rw [mul_div_cancel_left₀ _ (by positivity)]; exact AddCircle.coe_equivIco
lemma afloat (k:Behind): k∈backPane ↔ ∀ i, k i∈Set.Icc (-π) π:=by simp only [backPane, Set.mem_univ_pi]
-- equality when f measured nonzero only in interior
lemma identify {x y:Behind}(p:x∈sunshine)(q:y∈backPane)(g:atlas x=atlas y):x=y:=by
 funext i; have he: ((x i/(2*π):ℝ):UnitAddCircle)= ((y i/(2*π):ℝ):UnitAddCircle):= congrFun g i
 obtain ⟨j,hj⟩:= AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp he)
 simp only [zsmul_eq_mul,mul_one] at hj; have hp:=p i (Set.mem_univ _); have hq:=(afloat _).1 q i
 have ht: φ>0:=by positivity
 have hv : φ*(j:ℝ)=x i-y i:=by rw [hj]; field_simp
 by_cases hx:j ≤ -1
 · have hl:(j:ℝ)≤-1:=by exact_mod_cast hx
   exfalso; linarith only [hv,hp.1,hp.2,hq.1,hq.2,(show φ*(j:ℝ) ≤ φ*(-1) from mul_le_mul_of_nonneg_left hl (by positivity))]
 by_cases hy:1≤j; · have hl:1≤(j:ℝ):=by exact_mod_cast hy; -- issue focus
                    exfalso; linarith only [hv,hp.1,hp.2,hq.1,hq.2,(show φ ≤ φ*j from le_mul_of_one_le_right (by positivity) hl)]
 rw [show j=0 by omega] at hv; exact (sub_eq_zero.mp (by simpa using hv.symm : x i-y i=0))
lemma atlasMode (n:WalkA)(k:Behind): UnitAddTorus.mFourier n (atlas k)=spax n k:=by
 unfold atlas; rw [wears]; unfold mode spax walk surge; rw [Finset.mul_sum,Complex.exp_sum]; apply prod_congr rfl; intro i _; congr 1; push_cast; have he:(Real.pi:ℂ)≠0:=by exact_mod_cast Real.pi_pos.ne'
 field_simp

lemma spanIt {F:C(Rim (Fin 3),ℂ)}(h:F∈Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d:=Fin 3)))) :
 ∃ A: WalkA →₀ ℂ,F= A.sum fun i z=> z • UnitAddTorus.mFourier (d:=Fin 3) i:=by
 rw [← Finsupp.range_linearCombination] at h; obtain ⟨a,rfl⟩:=h; exact ⟨a,by rw [Finsupp.linearCombination_apply]⟩
lemma summit (f:Behind→ℂ)(p:ContinuousOn f backPane)(h: ∀ k∉sunshine,f k=0) (ε:ℝ)(v:0<ε):
 ∃ a:WalkA →₀ ℂ,∀ k∈backPane,‖(a.sum fun i z=> z *spax (-i) k)-f k‖≤ ε :=by
 let g(k: Rim (Fin 3)):= atlas_onto.surjective k|>.choose; let G(k:Rim (Fin 3)):=f (g k).val
 have hu (x:Behind)(p:x∈backPane):G (atlas x)=f x:=by
    let y:=g (atlas x); have hp:y.val∈backPane:=y.property; have hz:atlas y.val=atlas x:= (atlas_onto.surjective _).choose_spec
    change f y.val=f x; by_cases e:y.val∈ sunshine; · exact congrArg f (identify e p hz)
    by_cases q:x∈sunshine; · exact congrArg f (identify q hp hz.symm).symm
    rw [h _ e,h _ q]
 have ht:Continuous G:= atlas_onto.continuous_iff.mpr (by rw [show _= _ from (show (G ∘ fun i:↥backPane=>atlas i.val)=Set.restrict _ f from funext fun i=>hu i.val i.property)]; exact continuousOn_iff_continuous_restrict.mp p) -- function comp
 let A: C(Rim (Fin 3),ℂ):=⟨G,ht⟩; have hw:A∈(Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d:=Fin 3)))).topologicalClosure:=by rw [UnitAddTorus.span_mFourier_closure_eq_top]; trivial
 obtain ⟨a,z,e⟩:=Metric.mem_closure_iff.mp hw ε v
 obtain ⟨u,hx⟩:= spanIt z; let a':WalkA→₀ℂ:= u.embDomain (Equiv.neg WalkA).toEmbedding; refine ⟨a',fun k p=>?_⟩
 rw [dist_comm,dist_eq_norm] at e; rw [hx] at e
 apply le_trans ?_ e.le
 let J:=atlas k; let X:=u.sum (fun i v=> v • UnitAddTorus.mFourier (d:=Fin 3) i); rw [show (a'.sum fun i z=>z*spax (-i) k)-f k=(X-A) J from ?_]; exact ContinuousMap.norm_coe_le_norm (X-A) J
 change a'.sum _ - f k= X J- A J
 rw [show A J=f k from hu k p]; congr 1; unfold a' X; -- rewrite move
 rw [Finsupp.sum_embDomain]; unfold Finsupp.sum; rw [ContinuousMap.sum_apply]; refine sum_congr rfl fun i _=>?_ ; dsimp only; simp only [Equiv.toEmbedding_apply,Equiv.neg_apply,neg_neg]; change u i*_= u i • UnitAddTorus.mFourier i (atlas k); rw [smul_eq_mul,atlasMode]
end YM.CF.Crest.Sleet
