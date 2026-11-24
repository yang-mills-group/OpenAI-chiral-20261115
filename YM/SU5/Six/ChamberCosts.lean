import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace YM.DoorCost
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace
open Function Set Filter Metric MeasureTheory MeasureTheory.Measure
abbrev Chamber (n:ℕ):= Fin n→ℝ
-- Pi version for successor/axes (nothing implicit about direction)
variable (n:ℕ)(f: ℝ→ ℂ)
abbrev merge: ℝ × Chamber n≃ᵐ Chamber (n+1):= (MeasurableEquiv.piFinSuccAbove (fun _:Fin (n+1)=>ℝ) (Fin.last n)).symm
theorem merge_cost : MeasurePreserving (merge n):= MeasurePreserving.symm _ (volume_preserving_piFinSuccAbove (fun _=>ℝ) (Fin.last n)) -- direction
lemma lastAt (p:ℝ× Chamber n): merge n p (Fin.last n)=p.1:= Fin.insertNth_apply_same (α:=fun _=>ℝ) (Fin.last n) p.1 p.2
lemma firstAt (p:ℝ× Chamber n)(i:Fin n): merge n p i.castSucc=p.2 i := by
 rw [← congrFun Fin.succAbove_last i]; exact Fin.insertNth_apply_succAbove (α:=fun _=>ℝ) (Fin.last n) p.1 p.2 _
@[fun_prop] theorem merge_cont : Continuous (merge n):= by apply continuous_pi; intro i; induction i using Fin.lastCases with | last =>simp_rw [lastAt]; exact continuous_fst| cast i=> simp_rw [firstAt]; exact (continuous_apply _).comp continuous_snd
lemma merge_zero : merge n 0=0:= by funext i; induction i using Fin.lastCases with | last=>exact lastAt _ _ | cast i=>exact firstAt ..

-- zero-set slicing: avoid assuming 4-momentum a.c. at any stage.
lemma zeros_ae (h:AnalyticOnNhd ℝ f Set.univ)(p:f 0 ≠0) : ∀ᵐ x:ℝ,f x≠0:= by
 let A: Set ℝ:= f ⁻¹' ({0}:Set ℂ)
 have e:IsClosed A:= isClosed_singleton.preimage (continuousOn_univ.mp h.continuousOn)
 have t:IsDiscrete A:=isDiscrete_iff_nhdsNE.mpr (fun i _=>by
   by_contra v
   have hz : ∃ᶠ t in 𝓝[≠] i,f t=0:= frequently_iff_neBot.mpr (⟨v⟩ : NeBot ((𝓝[≠] i)⊓ Filter.principal A))
   exact p (h.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ trivial hz trivial))
 exact (e.isLindelof.countable_of_isDiscrete t).ae_notMem _
lemma slices_live (F:Chamber n→ℂ)(u:Continuous F)(h:F 0≠0)(e:∀ (p:Chamber n)(i:Fin n), AnalyticOnNhd ℝ (fun t:ℝ=>F (update p i t)) Set.univ):∀ᵐ x:Chamber n, F x≠ 0:= by
 induction n with
 | zero => exact ae_of_all _ (fun x=>by rw [Subsingleton.elim x]; exact h)
 | succ n ih=>
  let f(z:Chamber n):= F (merge n (0,z))
  let μ':=merge n
  have hh: Continuous f:= u.comp ((merge_cont n).comp (continuous_const.prodMk continuous_id))
  have hp:f 0 ≠0:= (congrArg F (merge_zero n)).trans_ne h
  have he:= ih f hh hp (fun p i=>?_)
  · rw [← (merge_cost n).map_eq]
    let V : Set (Chamber (n+1)):= {x|F x≠0}
    have hv:MeasurableSet V:= ((isOpen_ne (x:=(0:ℂ))).preimage u).measurableSet
    have H':MeasurableSet (μ' ⁻¹' V):= μ'.measurable hv
    refine (ae_map_iff μ'.measurable.aemeasurable hv).2 ((Measure.ae_prod_iff_ae_ae H').2 ((Measure.ae_ae_comm (p:=fun p z=> merge n (p,z)∈ V) H').2 ?_))
    filter_upwards [he] with z g
    let X:=merge n (0,z); let k:=Fin.last n; apply zeros_ae (fun a=>F (merge n (a,z))) _ g
    rw [show (fun a=>F (merge n (a,z)))=(fun a:ℝ=>F (update X k a)) from funext (fun a=>congrArg F (funext fun i => by
       induction i using Fin.lastCases with
       | last=> rw [lastAt]; exact (update_self (α:=Fin (n+1)) (β:=fun _=>ℝ) k a X).symm
       | cast j=> rw [firstAt,update_of_ne (Fin.castSucc_lt_last j|>.ne)]; exact (firstAt n (0,z) j).symm))]
    exact e X k
  · rw [show (fun t:ℝ=> f (update p i t))= (fun t:ℝ=>F (update (merge n (0,p)) i.castSucc t)) from funext (fun t=>congrArg F (funext fun j=>by
        induction j using Fin.lastCases with
        | last=> rw [lastAt,update_of_ne (Fin.castSucc_lt_last _|>.ne'),lastAt]
        | cast j=> rw [firstAt]; by_cases h:j=i
                   · subst j; exact (update_self ..).trans (update_self (β:=fun _=>ℝ) i.castSucc t (merge n (0,p))).symm
                   exact (update_of_ne h ..).trans ((firstAt n (0,p) j).symm.trans (update_of_ne (fun e=> h (Fin.castSucc_injective n e)) ..).symm)))]
    exact e _ _
section
-- radians. analytic cost from a real compactly supported test density
variable (u:Chamber n→ℝ) (p:Continuous u) (h:HasCompactSupport u)
def stars (k y:Chamber n):ℂ := Complex.exp (↑(∑ i:Fin n,k i * y i)* Complex.I)
def starbill (k:Chamber n):ℂ:=∫ x,(u x:ℂ) * stars n k x
@[fun_prop] lemma stars_cont : Continuous (Function.uncurry (stars n)) :=by unfold stars Function.uncurry; fun_prop
include p h
@[fun_prop] lemma sums_slip : Continuous (starbill n u):=by
 let f(k x:Chamber n):= (u x:ℂ) * stars n k x
 have he(k): Continuous (f k):= (Complex.continuous_ofReal.comp p).mul ((stars_cont n).comp (continuous_const.prodMk continuous_id))
 refine continuous_of_dominated (F:=f) (fun i=> (he i).aestronglyMeasurable) (bound:=fun p=> ‖u p‖) (fun k=> ae_of_all _ ?_) (p.integrable_of_hasCompactSupport (μ:=volume) h|>.norm) (ae_of_all _ ?_)
 · intro i; unfold f stars; rw [norm_mul,Complex.norm_real,Complex.norm_exp_ofReal_mul_I,mul_one]
 intro i; exact continuous_const.mul ((stars_cont n).comp (continuous_id.prodMk continuous_const))
lemma star_analytic (v:Chamber n)(i:Fin n): AnalyticOnNhd ℝ (fun z:ℝ=>starbill n u (update v i z)) Set.univ:= by
 let X:= tsupport u
 let C (p:Chamber n):ℂ:= (u p:ℂ)*stars n (Function.update v i (0:ℝ)) p
 let g(p:Chamber n):ℂ:= (p i:ℂ)*Complex.I
 have e : Continuous C:=(Complex.continuous_ofReal.comp p).mul ((stars_cont n).comp (continuous_const.prodMk continuous_id))
 have hx(p:Chamber n)(z:p∉X): C p=0:=by unfold C; rw [image_eq_zero_of_notMem_tsupport z]; simp
 have hg:Continuous g:= by unfold g; fun_prop
 let M(z:ℂ)(p:Chamber n):ℂ:= C p * Complex.exp (z*g p)
 let T (z:ℂ):= ∫ p,M z p
 have hm(x:ℝ): T (x:ℂ)= starbill n u (update v i x):= by
    refine integral_congr_ae (Eventually.of_forall fun p=> ?_)
    change C p * Complex.exp _=_
    unfold C g stars; rw [mul_assoc,← Complex.exp_add]; congr 2
    have he(z:ℝ): ∑ a:Fin n, Function.update v i z a * p a=z*p i+ ∑ a∈ Finset.univ.erase i, v a*p a:= by
       -- sum split
       rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]; congr 1
       exact Finset.sum_congr rfl (fun a h=>by rw [Function.update_of_ne (Finset.ne_of_mem_erase h)])
    rw [he,he]; push_cast; ring
 let D(z:ℂ)(p):ℂ:= C p*(Complex.exp (z*g p)*g p)
 have ht: Differentiable ℂ T:= by
    intro z; let Y:= Metric.closedBall z 1
    have hK(x:ℂ): Continuous (M x):=by unfold M; fun_prop
    have hD:Continuous D.uncurry:=by unfold D Function.uncurry; fun_prop
    have hz: IsCompact X:= h; obtain ⟨r,hp,A⟩:= ((isCompact_closedBall z 1|>.prod hz).image hD).isBounded.exists_pos_norm_le
    let b:= X.indicator (fun _=>r)
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=M) (F':=D) (closedBall_mem_nhds _ zero_lt_one) (Eventually.of_forall fun p=>(hK p).aestronglyMeasurable) ((hK _).integrable_of_hasCompactSupport ?_) (((hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)) (bound:=b) (ae_of_all _ ?_) ((integrable_indicator_iff hz.measurableSet).2 (integrableOn_const hz.measure_ne_top)) (ae_of_all _ ?_) |>.2.differentiableAt) -- syntax tune
    · refine exists_compact_iff_hasCompactSupport.mp ?_ -- verify iff
      exact ⟨X,hz,fun x u=>by unfold M; rw [hx x u, zero_mul]⟩
    · intro x i v; by_cases h:x∈ X
      · rw [show b x=r from indicator_of_mem h _]; exact A _ ⟨(i,x),⟨v,h⟩,rfl⟩
      rw [show b x=0 from indicator_of_notMem h _]; simp [D,hx x h]
    intro x y _
    simpa only [one_mul, D] using ((hasDerivAt_id' y|>.mul_const (g x)).cexp.const_mul (C x))
 intro x _
 rw [show (fun t:ℝ=>starbill n u (update v i t))=T ∘ Complex.ofRealCLM from funext (fun t=>(hm t).symm)]
 exact (ht.analyticAt _).restrictScalars.comp (Complex.ofRealCLM.analyticAt _)
lemma starbill_live (a:∫ x,u x=1): ∀ᵐ x:Chamber n,starbill n u x≠0:=by
 refine slices_live n (starbill n u) (sums_slip n u p h) ?_ (star_analytic n u p h)
 unfold starbill stars; simp [integral_complex_ofReal,a]
end
end YM.DoorCost
