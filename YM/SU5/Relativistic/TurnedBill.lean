import YM.SU5.Relativistic.StagingCloud
/-! # purchase on every transverse coordinate of this price. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Sleet
open Function Set Filter Topology NormedSpace MeasureTheory Metric Real Finset Lattice Next.Free
open Laurent Bloch Fir Jill Ember Shore Cuest Fock Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
local notation "φ"=>2*Real.pi
local notation "Φ"=> Set.Icc (-π) π
attribute [local instance] screen_fin
section abstract
variable {U:Set Behind}{a:ℝ}
lemma snatchS {A:Type*} (s:Finset A)(f:A→Behind→ℤ→ℂ) (h:∀ i∈s, TollS a U (f i)): TollS a U (fun k n=> ∑ i∈s,f i k n):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact ⟨1,one_pos,fun i p t=> (norm_zero).trans_le (mul_nonneg zero_le_one (spangle_pos ..).le)⟩
 | @insert i s hp ih => simp_rw [sum_insert hp]; exact (h _ (mem_insert_self ..)).addX (ih (fun i g=> h i (mem_insert_of_mem g)))
lemma wrapPulseSum {A:Type*}(s:Finset A)(n:ℤ)(f:A→ℝ→ℂ)(h:∀ i∈s,IntegrableOn (f i) screen): pluse n (fun t=>∑ i∈s, f i t)=∑ i∈s,pluse n (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp [pluse]
 | @insert i s hp ih=> simp_rw [sum_insert hp]; have he i (g:i∈s):IntegrableOn (f i) screen:=h i (mem_insert_of_mem g); rw [pluse_add n (h i (mem_insert_self ..)) (integrable_finsetSum _ he), ih he]
lemma wrapPulse_sum{A:Type*}(s:Finset A)(n:ℤ)(f:A→ℝ→ℂ)(h:∀ i∈s,IntegrableOn (f i) screen): wrapT n (fun t=>∑ i∈s, f i t)=∑ i∈s,wrapT n (f i):=by
 unfold wrapT; rw [wrapPulseSum _ _ _ h,mul_sum]
lemma wrapPulse_scale(n:ℤ)(x:ℂ)(f:ℝ→ℂ): wrapT n (fun t=>x*f t)=x*wrapT n f:=by unfold wrapT; rw [pluse_const,mul_left_comm]
lemma wrapPulse_add(n:ℤ)(f g:ℝ→ℂ)(p:IntegrableOn f screen)(q:IntegrableOn g screen): wrapT n (fun t=>f t+g t)=wrapT n f+wrapT n g:=by unfold wrapT; rw [pluse_add _ p q,mul_add]
end abstract
variable {d:ℕ}{s:Finset ℤ}{c:ℤ→Behind→ℂ}{a r:ℝ}
namespace UpStart
variable (P:UpStart d s c r a)
local notation "Ω"=>target s c
local notation "Z"=>turned s c
local notation "U"=>launch d r
local notation "V"=> (launch d r) ×ˢ Set.Icc (-π) π
include P
-- for staff with common letters outside stencil.
lemma registered (i n:ℤ)(k:Behind): wrapT n (pledge s c k)= if n∈s then c n k else 0:=by
 rw [show pledge s c k=fun t=>∑ j∈s,c j k*soundT j t from rfl]; rw [wrapPulse_sum (f:=fun j t=>c j k*soundT j t)]; swap; · intro i v; exact (((continuous_const.mul (sound_con i)).continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self
 simp_rw [wrapPulse_scale,sound_wrap]; by_cases g:n∈s; rw [sum_eq_single n (fun i u h=> by simp [Ne.symm h]) (fun v=>(v g).elim), if_pos rfl, mul_one,if_pos g]; rw [if_neg g]; exact sum_eq_zero fun i h=> by simp [show n≠i from fun v=>g (v.symm ▸ h)]
lemma landing {i:SpinIdx}(h:i∈plusHalf) (k:Behind)(n:ℤ) (p:n∉s): wrapT n (Z i k)=0:=by
 rw [show Z i k=fun t=> (if i=0 then (1:ℂ) else 0) * pledge s c k t from funext fun t=>by rw [tariffed,fell_upper h,add_zero,mul_comm], wrapPulse_scale, P.registered 0, if_neg p,mul_zero]
lemma projectedReceipt (i:SpinIdx): TollS a U (fun k j=> wrapT j (Z i k)):=by
 let h:=P.pledge_c; let V₁:=pledge s c
 let ht:= launch_compact d r
 let f(i:Axis)(k:Behind)(t:ℝ):= V₁ k t*heatLine k t i
 have hc(i):ContinuousOn (Function.uncurry (f i)) V:= h.continuousOn.mul (heat_cont ht (launch_sun P.wage P.tail) i)
 let x(l:Axis):=(- Complex.I) *gammaOp l i 0
 let p:ℂ := if i=0 then 1 else 0
 let V₂(i': ℤ)(k:Behind)(t:ℝ):=(p*c i' k)*soundT i' t
 have hq(j k):IntegrableOn (V₂ j k) screen:= ((continuous_const.mul (sound_con j)|>.continuousOn).integrableOn_Icc).mono_set Ioc_subset_Icc_self
 have he(k:Behind): Z i k=fun y=> (p*V₁ k y)+(∑ l:Axis,x l * f l k y):=by
    funext y; rw [tariffed]; unfold x f fell zen V₁; simp_rw [Matrix.sum_apply,Matrix.smul_apply, smul_eq_mul] -- unnecessary
    rw [mul_add,mul_comm _ (if i=0 then 1 else 0),mul_neg,mul_sum,←sum_neg_distrib]; congr 1; refine sum_congr rfl fun l _=>by ring
 have hT:TollS a (launch d r) (fun k n=>p*wrapT n (V₁ k)):=by
    let g(k:Behind)(n:ℤ):= if n∈s then p*c n k else (0:ℂ)
    suffices h: TollS a U g by
       have he(k n):p* wrapT n (V₁ k)=g k n:=by unfold g V₁; rw [P.registered 0]; split<;>simp [*]
       simp_rw [he]; exact h
    have hf(i:ℤ) : Continuous (fun k=> g k i):=by unfold g; split; exact continuous_const.mul (P.cont i); exact continuous_const
    exact fewS (a:=a) ht s _ (fun i x=> (hf i).continuousOn) (fun _ x i=>if_neg x)
 let Y (k:Behind)(n:ℤ):= ∑ j:Axis,x j * wrapT n (f j k)
 have hw:TollS a (launch d r) Y:=by
    apply snatchS Finset.univ (f:=fun i (k:Behind) (n:ℤ)=> x i*wrapT n (f i k)); intro i u
    exact ((P.expense i).scaleU ht (fun _=>(↑(φ:ℝ):ℂ)⁻¹) continuousOn_const).scaleU ht (fun _=> x i) continuousOn_const
 obtain ⟨B,b,g⟩:=hT.addX hw; refine ⟨B,b,fun k ht n=>?_⟩
 have Hx(k): IntegrableOn (V₁ k) screen:= ((h.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self
 have v(l):IntegrableOn (fun t=> x l * f l k t) screen:=(continuous_cut (f l) (hc l) ht).const_mul _
 change ‖wrapT n (Z i k)‖ ≤ _; rw [he, wrapPulse_add n _ _ ((Hx _).const_mul _) (integrable_finsetSum _ (fun i _=> v i)),wrapPulse_sum (f:=fun l t=> x l*f l k t) _ _ (fun l _=>v l)]; simp_rw [wrapPulse_scale]; exact g k ht n
where fewS {a:ℝ}{U₀:Set Behind}(hU:IsCompact U₀)(s:Finset ℤ)(f:Behind→ℤ→ℂ)(h:∀ i∈s,ContinuousOn (fun k=> f k i) U₀)(e:∀ x∉s,∀ i,f i x=0): TollS a U₀ f:=by
        suffices g:∃ B:ℝ,0<B∧∀ k∈U₀,∀ i∈s,‖f k i‖ ≤ B*spangle a i by obtain ⟨B,p,u⟩:=g; refine ⟨B,p,fun k q i=>?_⟩; by_cases t:i∈s; exact u _ q _ t; rw [e i t,norm_zero]; exact (mul_pos p (spangle_pos ..)).le
        clear e
        induction s using Finset.induction_on with
        | empty=> exact ⟨1,zero_lt_one,by simp⟩
        | @insert i s hi ih=>
           obtain ⟨A,u⟩:=hU.exists_bound_of_continuousOn (h i (mem_insert_self ..)); obtain ⟨B,t,p⟩:=ih (fun k q=>h k (mem_insert_of_mem q)); let b:= |A|/spangle a i; have hp:0≤b:= div_nonneg (abs_nonneg _) (spangle_pos ..).le
           refine ⟨B+b,add_pos_of_pos_of_nonneg t hp,fun k l j q=>?_⟩; rw [add_mul]; rcases mem_insert.mp q with z|z; subst j; unfold b; rw [div_mul_cancel₀ _ (spangle_pos ..).ne']; exact ((u _ l).trans (le_abs_self _)).trans (le_add_of_nonneg_left (mul_nonneg t.le (spangle_pos ..).le)); exact (p k l j z).trans (le_add_of_nonneg_right (mul_nonneg hp (spangle_pos ..).le))
end UpStart
end YM.CF.Crest.Sleet
