import ZecaNibber
import YM.SU5.FiniteGaugeData.Seld.NewMoon
set_option autoImplicit false
set_option maxHeartbeats 270000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Zeca
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder


namespace Moment
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)
open Boundary Probe
variable (D:Moment H) (x y:Bench S)
lemma approachable:Tendsto (fun t:ℝ≥0=> inner ℂ x.val ((D.cost S t t) y.val))
       (𝓝[>] 0) (𝓝 (D.form S 0 x y)):=by
 let A:= D.op
 let X:=hall S D.n x;let Y:=hall S D.n y
 unfold form lucent;rw [vroot]
 have r: Tendsto (fun t=>inner ℂ (S.E t X) (A (S.E t Y))) (𝓝[>] 0)
            (𝓝 (inner ℂ X (A Y))):=by
    have p(x:H): Tendsto (fun t=>S.E t x) (𝓝[>] 0) (𝓝 x):=
       ((S.continuousE x).tendsto' 0 x (DFunLike.congr_fun S.eZero x)).mono_left nhdsWithin_le_nhds
    exact (p X).inner (A.continuous.continuousAt.tendsto.comp (p Y))
 refine r.congr' ?_
 filter_upwards [self_mem_nhdsWithin] with t p
 have h:0<t:=mem_Ioi.mp p
 have g(x:Bench S):parabola S D.n (duration t) x.val=S.E t (hall S D.n x):=by
    refine Eq.trans ?_ (DFunLike.congr_fun (parabolaE S D.n _ h) _)

    change parabola S D.n _ x.val=parabola S D.n _ (Cache S _ _); rw [releases]
 rw [← show parabola S _ _ x.val=S.E t X from g x,
     ← show parabola S _ _ y.val=S.E t Y from g y,←ContinuousLinearMap.adjoint_inner_right,
     para_adj S D.n _ h];rfl
lemma formZero(p:E4):D.form S p x y=D.form S 0 (usher S (-p) x) (usher S (-p) y):=by
  rw [form,Lucent,form,lucent,vroot,ush_pre,ush_pre]

variable {ι:Type}(U:Finset ι)(c:ι→ℂ)(B:ι→Moment H)
  (g:∀ t:ℝ≥0,0<t→D.cost S t t=∑ i∈U,c i • (B i).cost S t t)
include g in
lemma exhibit (p:E4):D.form S p x y =∑ i∈U, c i * (B i).form S p x y:=by
 suffices ∀x y:Bench S, D.form S 0 x y=∑ i∈U,c i * (B i).form S 0 x y from by
    simp_rw [formZero S _ x y];exact this ..
 intro x y; apply tendsto_nhds_unique (approachable S D x y)
 refine Tendsto.congr' ?_ (tendsto_finset_sum U fun i _=> tendsto_const_nhds (x:=c i) |>.mul (approachable S (B i) x y))
 filter_upwards [self_mem_nhdsWithin] with t h
 rw [g t (mem_Ioi.mp h), ContinuousLinearMap.sum_apply,inner_sum]
 simp only [ContinuousLinearMap.smul_apply,inner_smul_right]

include g
lemma area (f:Test4):
 inner ℂ x.val (D.field S f y).val=∑ i∈U, c i * inner ℂ x.val ((B i).field S f y).val:=by
 have h(p:E4): f p * D.form S p x y=∑ i∈U,c i * (f p*(B i).form S p x y):=by
    rw [exhibit S D x y U c B g p,Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=>mul_left_comm ..
 simp_rw [(realStamp S).scalar,h]
 rw [integral_finset_sum _ (fun i _=>(sell S _ _ (B i).op f).const_mul (c i))] -- replace
 exact Finset.sum_congr rfl fun _ _=>integral_const_mul ..
lemma display (f:Test4):
 D.field S f=∑ i∈U,c i • (B i).field S f:=by

 -- tune unresolved implicit
 ext1 y; apply Subtype.ext
 apply (show DenseRange (Subtype.val:Bench S→H) from by rw [DenseRange,Subtype.range_val]; exact bench_warm S).eq_of_inner_right ℂ;intro x
 rw [area S D x y U c B g f,LinearMap.sum_apply,Submodule.coe_sum,inner_sum]
 apply Finset.sum_congr rfl; intro i _
 exact (inner_smul_right x.val ((B i).field S f y).val (c i)).symm

omit g
abbrev Copy (C:Moment H) := ∀f:Test4,∃ k:Test4, tsupport k ⊆ tsupport f ∧ D.field S f=C.field S k
lemma tickS (a:Axis)(f:Test4):tsupport ⇑(newTick a f) ⊆ tsupport f:=
   (tsupport_comp_subset (g:=fun z:ℂ=> -(I*z)) (by simp) _).trans (show tsupport (shade (basis a) f: E4→ℂ)⊆_ from tsupport_fderiv_apply_subset ℝ _)
lemma notchCopy(C:Moment H)(p:D.Copy S C): (notch S D).Copy S C:=by
 intro f;obtain ⟨k,v,w⟩:=p (newTick a f)
 exact ⟨k,v.trans (tickS ..),(visible S D f).trans w⟩
lemma selfCopy: D.Copy S D:=fun f=>⟨f,_root_.subset_refl _,rfl⟩

lemma ts_smul (z:ℂ)(f:Test4):tsupport ⇑(z • f)⊆tsupport f:=tsupport_comp_subset (g:=fun x:ℂ=>z*x) (by simp) _
lemma ts_add (f g:Test4):
 tsupport ⇑(f+g)⊆tsupport f ∪ tsupport g:= by
 rw [tsupport, tsupport, tsupport,←closure_union]; apply closure_mono
 intro p t
 by_contra! r
 change f p+g p≠0 at t
 have :p∉support ⇑f∧p∉support ⇑g:=⟨fun h=>r (.inl h),fun h=>r (.inr h)⟩ -- r possibly pushed
 simp at this; exact t (by rw [this.1,this.2,add_zero])

lemma ts_sum (t:ι→Test4)(V:Set E4)(v:∀i,tsupport (t i)⊆V):
    tsupport (⇑(∑i∈U,c i • t i:Test4))⊆V:=by
  classical
  induction U using Finset.induction_on with
  | empty=> rw [Finset.sum_empty]; change tsupport (0:E4→ℂ)⊆V; simp -- 
  | insert j w p ih=>
     rw [Finset.sum_insert p]
     exact (ts_add ..).trans (union_subset ((ts_smul ..).trans (v j)) ih)

include g in lemma copy (C:Moment H)(t:∀ i,(B i).Copy S C): D.Copy S C:=by
 intro f
 choose k v h using (fun i=> t i f)
 refine ⟨_,ts_sum U c k _ v,?_⟩
 simp_rw [display S D U c B g f,h,map_sum,map_smul]

-- dagger.
lemma barS(f:Test4):tsupport ⇑(bar f)⊆tsupport f:=
 tsupport_comp_subset (g:=starRingEnd ℂ) (map_zero _) _

lemma twinCopy(C:Moment H)(p:D.Copy S C):D.dagger.Copy S C.dagger:=by
 intro f
 obtain ⟨k,v,t⟩:=p (bar f)
 refine ⟨bar k,(barS k).trans (v.trans (barS f)),?_⟩
 ext1 x;apply Subtype.ext
 apply (show DenseRange (Subtype.val:Bench S→H) from by rw [DenseRange,Subtype.range_val]; exact bench_warm S).eq_of_inner_right ℂ
 intro y; rw [←bar_twice f,← (realStamp S).adj,← (realStamp S).adj,t]
#print axioms copy
