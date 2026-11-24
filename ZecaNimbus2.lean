import ZecaSky
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section

namespace YM.ZecaSky
open Function Metric Filter Asymptotics Set
open scoped ComplexOrder InnerProductSpace BigOperators Topology


variable {ι:Type*} {d:ι→ℝ}{p u:ℝ} {s:Set ℂ}

structure Weather (s:Set ℂ)(d:ι→ℝ) : Prop where
 opens:IsOpen s
 days: ∀ i,(d i:ℂ)∈s
 lapse: ∃ t:Set ℝ, IsPreconnected t ∧ MapsTo ((↑):ℝ→ℂ) t s ∧
   0∈t ∧ ∃ r∈t,∃ᶠ z in 𝓝[≠] r,z∈ Set.range d

lemma settled_real (h:Weather s d):
 ev s 0 ∈ (Submodule.span ℝ (Set.range fun i=>ev s (d i))).topologicalClosure:=by
 let J:=Submodule.span ℝ (Set.range fun i=>ev s (d i))
 let W:=J.topologicalClosure
 let a:=W.mkQL
 haveI:IsClosed (W:Set (Cost s)):=J.isClosed_topologicalClosure
 obtain ⟨t,connected,inc,w,r,v,e⟩:=h.lapse
 have k:AnalyticOnNhd ℝ (ev s) s:= (ev_magic h.opens).restrictScalars
 have b:AnalyticOnNhd ℝ (a ∘ (ev s ∘ (↑))) t:=
   (a.analyticOnNhd Set.univ).comp
    (k.comp (Complex.ofRealCLM.analyticOnNhd t) inc) (mapsTo_univ ..)
 have y:=b.eqOn_zero_of_preconnected_of_frequently_eq_zero connected v
     (e.mono (fun z ⟨i,p⟩=>
          (Submodule.Quotient.mk_eq_zero W).mpr
             (J.le_topologicalClosure (
                 Submodule.subset_span ⟨i, congrArg (fun x:ℝ=>ev s x) p⟩))))

 rw [← Complex.ofReal_zero]
 exact (Submodule.Quotient.mk_eq_zero W).mp (y w)
open BoundedContinuousFunction
#check BoundedContinuousFunction.evalCLM
#check BoundedContinuousFunction.sum_apply

lemma reached_one (h:Weather s d)(p:0<u):
 ∃ (F:Finset ι)(a:ι→ℝ),∀ g:Str s,‖g.f 0- ∑ i∈F,a i • g.f (d i)‖≤u:=by
 obtain ⟨x,y,t⟩:=Metric.mem_closure_iff.mp (settled_real h) _ p
 obtain ⟨a,v⟩:=
    Finsupp.mem_span_range_iff_exists_finsupp.mp y
 -- use pointwise eval
 rw [dist_eq_norm,←v] at t
 unfold Finsupp.sum at t
 refine ⟨a.support,a,fun g=>le_trans ?_ t.le⟩
 have q:=norm_coe_le_norm (ev s 0- ∑ i∈a.support,a i • ev s (d i)) g
 simp only [BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.sum_apply,BoundedContinuousFunction.smul_apply,ev_here] at q
 exact q
#print axioms reached_one

lemma reached (h:Weather s d) (p:0<u):
 ∃ (F:Finset ι)(a:ι→ℝ),∀ {D:ℝ},0<D→∀ f:ℂ→ℂ,
   DifferentiableOn ℂ f s → (∀z∈s,‖f z‖≤D)→
        ‖f 0- ∑ i∈F,(a i:ℂ)* f (d i)‖≤D*u:=by
 classical
 obtain ⟨F,a,t⟩:=reached_one h p
 refine ⟨F,a,fun {D} b f x g=>?_⟩
 have ds:DifferentiableOn ℂ (fun z=>f z/(D:ℂ)) s:=x.div_const (D:ℂ)
 let l:Str s:=
   ⟨s.indicator (fun z=>f z/(D:ℂ)), fun z=>by
          by_cases j:z∈s
          · rw [Set.indicator_of_mem j,norm_div,Complex.norm_real,Real.norm_of_nonneg b.le,div_le_one b]
            exact g z j
          rw [Set.indicator_of_notMem j,norm_zero]; exact zero_le_one,
          ds.congr fun z hz=>Set.indicator_of_mem hz _⟩
 have z0:(0:ℂ)∈s:= by
    obtain ⟨t,_,a,b,_⟩:=h.lapse
    simpa using a b
 have j: l.f 0- ∑ i∈F,a i • l.f (d i)=
          (f 0- ∑ i∈F,(a i:ℂ)* f (d i))/(D:ℂ):=by
   change Set.indicator s (fun z=>f z/(D:ℂ)) 0- ∑ i∈F,a i • Set.indicator s (fun z=>f z/(D:ℂ)) (d i:ℂ)= _
   rw [Set.indicator_of_mem z0 _,sub_div,Finset.sum_div]
   exact congrArg (_- · ) (Finset.sum_congr rfl fun i _=>by rw [indicator_of_mem (h.days i), Complex.real_smul, mul_div_assoc])
 specialize t l
 rwa [j,norm_div, Complex.norm_real, Real.norm_of_nonneg b.le, div_le_iff₀ b, mul_comm u] at t
#print axioms reached
