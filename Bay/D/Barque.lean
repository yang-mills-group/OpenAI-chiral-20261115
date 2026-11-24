import Mathlib
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.D
open Filter Metric Finset Classical
open scoped Topology

def Fleet{X:Type*}(f:ℕ→X→ℂ):Prop:=
 (∃C:ℝ,∀n x,‖f n x‖≤ C)∧∀ε:ℝ,0<ε→∃v:Finset X,∀x,
   (∀n,f n x=0) ∨ ∃y∈v,∀n,dist (f n x) (f n y)≤ ε

lemma shipFleet{X Y:Type*}[PseudoMetricSpace Y]{D:Set X}
   (g:X→Y)(h:TotallyBounded (Set.range g))(F:ℕ→X→ℂ)
   (b:∃C:ℝ,∀n x,‖F n x‖≤ C)
   (l:∃c:ℝ,0<c∧∀x∈D,∀y∈D,∀n,dist (F n x) (F n y) ≤ c*dist (g x) (g y))
   (off:∀n x,x∉D→ F n x=0):Fleet F:=by
 refine ⟨b,fun ε he=>?_⟩
 obtain ⟨c,hc,u⟩:=l
 obtain ⟨y,Y,m,H⟩:= Metric.finite_approx_of_totallyBounded
   (h.subset (Set.image_subset_range g D)) (ε/c) (by positivity)
 choose s U V using fun i:y=>Y i.property
 haveI:Finite y:=m
 refine ⟨(Set.finite_range s).toFinset,fun x=>?_⟩
 by_cases w:x∈D
 swap; · left; exact fun _=>off _ _ w
 right
 have t:=H (Set.mem_image_of_mem g w)
 obtain ⟨a,t⟩:=Set.mem_iUnion.mp t
 obtain ⟨r,T⟩:=Set.mem_iUnion.mp t

 let i:y:=⟨a,r⟩
 have v:g (s i)=a:=V _
 refine ⟨s i,by simpa using Set.mem_range_self (f:=s) i,fun n=>?_⟩
 refine le_trans (u x w _ (U i) _) ?_
 rw [v,mul_comm]
 exact (le_div_iff₀ hc).mp (show dist _ _ < _ from T).le

lemma Fleet.launch {X:Type*} {F:ℕ→X→ℂ} (h:Fleet F):
 ∃ φ:ℕ→ℕ,StrictMono φ∧∃f,TendstoUniformly (F∘φ) f atTop:=by
 obtain ⟨⟨C,a⟩,b⟩:=h
 choose v h using fun n:ℕ=> b (1/(n+1)) (by positivity)
 let p:= Σ n:ℕ,↥(v n)
 haveI:Countable p:= by unfold p;infer_instance
 have ht(j:p):IsCompact (closedBall (0:ℂ) C):=isCompact_closedBall ..
 obtain ⟨k,_,φ,w,u⟩:= (isCompact_univ_pi ht).tendsto_subseq (x:=fun n j=>F n j.2.val)
    (fun n j _=>mem_closedBall.mpr (by rw [dist_zero_right];exact a ..))
 have c:=tendsto_pi_nhds.mp u
 -- temp
 let G:= F∘φ
 have W(ε:ℝ)(t:0<ε): ∃ M,∀m≥ M,∀n≥ M,∀x,
     dist (G m x) (G n x)<ε:= by
    have e:0 < ε/4:=by positivity
    obtain ⟨l,L⟩:=exists_nat_one_div_lt e
    obtain ⟨M,d⟩:=eventually_atTop.mp (eventually_all.mpr fun j:↥(v l)=>
      Metric.tendsto_nhds.mp (c ⟨l,j⟩) _ e)
    refine ⟨M,fun m hm n hn x=>?_⟩
    rcases h l x with y|H
    · rw [show G m x=0 from y _,show G n x=0 from y _,dist_self];exact t
    obtain ⟨y,hy,r⟩:=H
    have a(s:ℕ)(hs:M≤ s): dist (G s x) (k ⟨l,⟨y,hy⟩⟩)<ε/2:=by
      apply lt_of_le_of_lt (dist_triangle _ (G s y) _)
      have u:dist (G s x) (G s y)<ε/4:=(r (φ s)).trans_lt L
      have v:dist (G s y) (k ⟨l,⟨y,hy⟩⟩)<ε/4:=d s hs ⟨y,hy⟩
      linarith
    exact lt_of_le_of_lt (dist_triangle _ (k ⟨l,⟨y,hy⟩⟩) _)
      (lt_of_lt_of_le (add_lt_add (a _ hm) ((dist_comm ..).symm.trans_lt (a _ hn))) (by linarith))

 choose g J using fun x:X=>cauchySeq_tendsto_of_complete
    (u:=fun n=>G n x) (Metric.cauchySeq_iff.mpr (fun ε h=>
       (W ε h).imp fun _ t=>fun i hi j hj=> t i hi j hj x))
 refine ⟨φ,w,g,Metric.tendstoUniformly_iff.mpr (fun ε h=>?_ )⟩
 obtain ⟨N,t⟩:=W (ε/2) (by positivity)
 filter_upwards [eventually_ge_atTop N] with i u x
 apply lt_of_le_of_lt _ (half_lt_self h)
 apply le_of_tendsto ((J x).dist tendsto_const_nhds)
 exact (eventually_ge_atTop N).mono fun n q=>(t _ q _ u x).le
