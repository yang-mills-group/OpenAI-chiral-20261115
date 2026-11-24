import YM.SU5.Registration.LineUp.Pocket
import YM.Work.C18
/-!
 # Moment analytical condition across spin tickets, local -> global arc budget

 From finite-pocket costs of Courts at real points. Per *boost line*. Needn't put
 a topology on epaulets. This is analytic only and not asserting an acted 
 representation on fields (next file). Does work for a zero portrait.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Function Filter Set Boundary Mink Metric Module Submodule
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Courts
lemma boost_annual (R:Courts V)(e:Ray)(v:V) : ∀ t:ℝ, GearContinuity (fun x=> R.mi (e.boost x) v) t:=by
 intro t; obtain ⟨k,g,c,h,p⟩:= R.miC v (e.boost t); exact ⟨k,g,fun i=> c i ∘ e.boost, fun i=> (h i).comp e.continuousBoost.continuousAt, (e.continuousBoost.tendsto _).eventually p⟩
-- module one-parameter arc `u`; along 0 for each vector suffice (request all here).
variable (u: ℝ → V →ₗ[ℂ] V) (h0:∀ v,u 0 v=v) (hp:∀ a b v, u (a+b) v=u a (u b v)) (hg:∀ v t, GearContinuity (fun r=> u r v) t)
include h0 hp hg
lemma year_price (v:V) : ∃ Q:Submodule ℂ V, FiniteDimensional ℂ Q ∧ v∈Q ∧ ∀ t, ∀ v∈Q, u t v∈Q:=by
 classical
 let A(r:ℝ) := Submodule.span ℂ ((fun t:ℝ=> u t v) '' ball 0 r); have h m s (p:m≤s) : A m ≤ A s:= Submodule.span_mono (Set.image_mono (ball_subset_ball p)); have sub {U U':Submodule ℂ V}[FiniteDimensional ℂ U'] (p:U≤U'): FiniteDimensional ℂ U := FiniteDimensional.of_injective (Submodule.inclusion p) (Submodule.inclusion_injective p)
 obtain ⟨k,g,c,q,a⟩:=hg v 0; let Z:= Submodule.span ℂ (Set.range g); obtain ⟨r,hr,e⟩:=Metric.mem_nhds_iff.mp a; haveI : FiniteDimensional ℂ Z:= Module.Finite.span_of_finite ℂ (Set.finite_range g)
 haveI : FiniteDimensional ℂ (A r):= sub (show A r ≤ Z from Submodule.span_le.mpr (by
    rintro x ⟨t,i,rfl⟩; change u t v∈Z; rw [show u t v=_ from e i]; exact sum_mem fun i _=> Z.smul_mem _ (subset_span (Set.mem_range_self _))))
 let P (i:ℕ):Prop:= ∃ t:ℝ, t∈ Ioc 0 r ∧ finrank ℂ (A t)=i; let N:∃ i,P i:= ⟨_,r,⟨hr,le_rfl⟩,rfl⟩; obtain ⟨s, ⟨m,p⟩, hs⟩:= Nat.find_spec N
 let r':=s/2
 have mm:0<r':=by unfold r'; positivity
 have he:r'+r'=s:= by unfold r'; ring
 let Q:= A s
 have hs': r' ≤ s:=by linarith
 haveI hp' : FiniteDimensional ℂ Q:= sub (h _ _ p)
 have uQ:A r'=Q:= Submodule.eq_of_le_of_finrank_le (h r' s hs') (by change finrank ℂ (A s)≤_; rw [hs]; exact Nat.find_min' N ⟨r', ⟨mm,hs'.trans p⟩,rfl⟩)
 have fund (t:ℝ)(p': |t|<r') (x:V)(h:x∈Q) : u t x∈Q:=by
    change x∈ Q.comap (u t); apply le_trans (show Q=A r' from uQ.symm).le (Submodule.span_le.mpr ?_) h
    rintro x ⟨b,g,rfl⟩; have g₁: |b|<r':= by simpa [Real.dist_eq] using g
    change u t (u b v)∈Q; rw [← hp]; refine Submodule.subset_span ⟨t+b,?_,rfl⟩; simp only [ball, Set.mem_setOf_eq,Real.dist_eq,sub_zero]; exact (abs_add_le ..).trans_lt (by linarith)
 have uF (t:ℝ) (p':|t|<r') (x:V)(h:x∈Q) (k:ℕ): u ((k:ℝ)*t) x∈Q:=by
   induction k with
   | zero => simpa only [Nat.cast_zero,zero_mul,h0] using h
   | succ n ih => push_cast; rw [add_mul,one_mul,add_comm, hp]; exact fund _ p' _ ih
 refine ⟨Q,hp',Submodule.subset_span ⟨0,?_,h0 v⟩,?_⟩
 · exact Metric.mem_ball_self m
 intro t x p
 obtain ⟨K,pK⟩:= exists_nat_gt (|t|/r'+1); have hk:(0:ℝ)< K:=lt_trans (by positivity) pK; have he':|t| / r'< K:=by linarith
 rw [← show (K:ℝ)*(t/K)=t from by field_simp]
 refine uF _ ?_ _ p _; rw [abs_div,abs_of_pos hk,div_lt_iff₀ hk,mul_comm]; exact (div_lt_iff₀ mm).mp he'
lemma stock_time (v:V) : ∃ (k:ℕ) (B: Fin k→V) (c:Fin k→ ℂ→ℂ), (∀ i, AnalyticOnNhd ℂ (c i) univ) ∧ ∀ t:ℝ, ∑ i,c i t • B i=u t v:=by
 obtain ⟨Q,hfd,hv,hP⟩:= year_price u h0 hp hg v; haveI : FiniteDimensional ℂ Q:=hfd
 let k:=finrank ℂ Q; let B:=finBasis ℂ Q; let X(t:ℝ) := (u t).restrict (p:=Q) (q:=Q) (hP t); let F:= Fin k → ℂ; let E: Q≃ₗ[ℂ] F:= B.equivFun; let Λ(t:ℝ): F→ₗ[ℂ]F := E.toLinearMap.comp ((X t).comp E.symm.toLinearMap); let P(t:ℝ): F→L[ℂ]F:= LinearMap.toContinuousLinearMap (Λ t)
 have φ(t:ℝ)(q:Q): (X t q).val =u t q.val:= rfl
 have e(t:ℝ)(x:F) : P t x=E (X t (E.symm x)):=rfl
 have hl: Continuous P:= by
   obtain ⟨W,hW⟩:= Q.subtype.exists_leftInverse_of_injective Q.ker_subtype
   refine continuous_clm_apply.mpr fun f=> continuous_iff_continuousAt.mpr fun t=>?_
   let x:=E.symm f; let T := E.toLinearMap.comp W; obtain ⟨k',B',c,h,m⟩:= hg x.val t
   have he (t':ℝ): P t' f=T (u t' x.val):=by
     rw [e,LinearMap.comp_apply,← φ]; exact congrArg E ((LinearMap.congr_fun hW (X t' x)).symm)
   apply ContinuousAt.congr_of_eventuallyEq (show ContinuousAt (fun t=> ∑ i,c i t • T (B' i)) t from (tendsto_finsetSum _ fun i _=> (h i).tendsto.smul tendsto_const_nhds)); filter_upwards [m] with t p; simp only [he, show u t _=_ from p, map_sum, map_smul]
 have hh: P 0=1:= by
   ext1 i; rw [e,show X 0 _=E.symm i from Subtype.ext (h0 _), E.apply_symm_apply]; rfl
 have hU(x y:ℝ): P (x+y)=P x*P y:=by
   ext1 v; change P (x+y) v=P x (P y v); rw [e,e,e,E.symm_apply_apply]; exact congrArg E (Subtype.ext (hp ..))
 obtain ⟨U,h,hT⟩:= Work.C18.entire P hl hh hU; let q:Q:= ⟨v,hv⟩; let i:= E q; let D:ℂ→F:= fun z=> U z i; refine ⟨k,fun j=> Q.subtype (B j),fun j z=> D z j,fun j z _=>?_, fun t=>?_⟩
 · exact ((ContinuousLinearMap.proj (R:=ℂ) j).analyticAt _).comp (((ContinuousLinearMap.apply ℂ F i).analyticAt _).comp (h z (mem_univ _)))
 rw [show u t v=Q.subtype (X t q) from rfl]; simp_rw[← map_smul, ← map_sum]; congr 1
 simp_rw [D,hT,e,i,E.symm_apply_apply]; exact B.sum_equivFun _
omit h0 hp hg
lemma weight_slot (R:Courts V)(v:V)(e:Ray): ∃ (k:ℕ)(B:Fin k→V)(c:Fin k→ℂ→ℂ), (∀ i,AnalyticOnNhd ℂ (c i) univ) ∧ ∀ t:ℝ, ∑ i,c i t • B i= R.mi (e.boost t) v:=by
 refine stock_time (fun t=>R.mi (e.boost t)) (fun i=>?_) (fun a b x=>?_) (boost_annual R e) v
 · rw [e.boost_start]; exact R.mi1 i
 rw [e.boost_add,R.miMul]
end Courts
end YM.SatinWFixed
open YM.SatinWFixed
#print axioms Courts.year_price
#print axioms Courts.weight_slot
