import YM.SU5.Reconstruction.Quartz.Tunnel
set_option autoImplicit false
noncomputable section
namespace YM.Quartz
open Function Set Filter MeasureTheory Spectral Analysis Metric Topology
open scoped Topology NNReal ENNReal Complex ComplexOrder InnerProductSpace Classical
open Multiplier CrossedFrame Clasp Complex HadamardThreeLines BridgeClub Anvil TopologicalSpace ContinuousLinearMap
variable {K H D:Hilbert}(C:Clasp K H D) (X:H.Op)(Y:D.Op)
variable {ι:Type*}{A:ι→H.Op}{B:ι→D.Op}{x:H.Op}{y:D.Op}{v:Filter ι}
lemma passMon [v.NeBot] (p:Limited v A x)(q:Limited v B y)(e:∀ᶠ i in v,C.Pass (A i) (B i)): C.Pass x y:=by
 intro z; rw[C.latch_dual]
 let u(i:ι) := C.l.adjoint (A i (C.l z))+ C.r.adjoint (B i (C.r z)); let k:= C.l.adjoint (x (C.l z))+ C.r.adjoint (y (C.r z))
 have hv(m:K): Tendsto (fun i=> inner ℂ m (u i)) v (𝓝 (inner ℂ m k)):=by simp_rw [u,k,inner_add_right,adjoint_inner_right]; exact (p.confirms ..).add (q.confirms ..)
 refine ⟨ext_inner_left ℂ (fun a=>?_),ext_inner_left ℂ (fun a=>?_)⟩
 · rw [← adjoint_inner_left]; exact tendsto_nhds_unique_of_eventuallyEq (hv _) (p.confirms ..) (e.mono (fun i h=> by change inner ℂ (C.l.adjoint a) (u i)=_; rw [adjoint_inner_left,(latch_dual .. |>.1 (h z)).1] )) -- `u` reducible
 rw [← adjoint_inner_left]; exact tendsto_nhds_unique_of_eventuallyEq (hv _) (q.confirms ..) (e.mono (fun i h=> by change inner ℂ (C.r.adjoint a) (u i)=_; rw [adjoint_inner_left,(latch_dual .. |>.1 (h z)).2] ))
lemma eitherUnique {t:D.Op}(p:C.Pass x t)(q:C.Pass x y):t=y:=by
 ext1 z; apply congrFun (a:=z) (C.q.equalizer t.continuous y.continuous ?_); funext u; obtain ⟨i,a,b⟩:=p u; obtain ⟨j,d,h⟩:= q u; exact b.symm.trans ((congrArg _ (C.j (a.trans d.symm))).trans h)
lemma limitedSub {ι':Type*}{L:Filter ι'}{a:ι'→ι}(p:Limited v A x)(t:Tendsto a L v) : Limited L (A∘a) x:=by obtain ⟨⟨r,t',b⟩,s⟩:=p; exact ⟨⟨r,t',t.eventually b⟩,fun _ _=>(s _ _).comp t⟩
lemma pearlSub {ι':Type*}{L:Filter ι'}{a:ι'→ι}(p:Pearl v B y)(t:Tendsto a L v) : Pearl L (B∘a) y:=by obtain ⟨⟨r,t',b⟩,s,d⟩:=p; exact ⟨⟨r,t',t.eventually b⟩,fun _=>(s _).comp t,fun _=>(d _).comp t⟩
lemma shouldFly (i:Axis) (S:OS.Semigroup D i) (v:ι→E4) (L:Filter ι)(x:E4)(p:Tendsto v L (𝓝 x)): Pearl L (fun u=> Picket.trans S (v u)) (Picket.trans S x):= by
 refine ⟨⟨1,zero_le_one,Eventually.of_forall fun r=> flammable _ (Picket.mobile ..)⟩,fun t=> ((S.unit.moves t).tendsto _).comp p,fun t=>?_⟩
 change Tendsto (fun u=> star (Picket.trans S (v u)) t) L (𝓝 (star (Picket.trans S x) t))
 simp_rw [Picket.trans_star]; exact ((S.unit.moves t).tendsto _).comp p.neg
open TopologicalSpace in
lemma scene [SeparableSpace D.space] {c:ℝ}(F:ℕ→H.Op) (Z T:ℕ→D.Op) (p:Limited atTop F X)(s:Pearl atTop T 1)(d:0≤c)(e:∀i,‖Z i‖≤ c)(h:∀i,C.Pass (F i) (Z i*T i)) : ∃ B:D.Op, C.Pass X B∧Limited atTop Z B:=by
 obtain ⟨ψ,g,u,-,k⟩:=Limited.extract Z d e
 have v(ns:ℕ→ℕ)(w:Tendsto ns atTop atTop){y:D.Op}(p':Limited atTop (Z∘ns) y): C.Pass X y:= by
    let t:= passMon C (limitedSub p w) (p'.toRight (pearlSub s w)) (Eventually.of_forall (fun i=>h (ns i)))
    rwa [mul_one] at t -- let prop rewriting binder?
 have hu : C.Pass X u:=v ψ g.tendsto_atTop k
 refine ⟨u,hu,⟨c,d,Eventually.of_forall e⟩,?_⟩
 intro x y; apply tendsto_of_subseq_tendsto; intro ns hns; obtain ⟨η,hT,v',-,e'⟩:= Limited.extract (Z∘ns) d (fun i=> e _)
 refine ⟨η,?_⟩
 rw [eitherUnique C hu (v (ns ∘ η) (hns.comp hT.tendsto_atTop) e')]; exact e'.confirms ..
end YM.Quartz
