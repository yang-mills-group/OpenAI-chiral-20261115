import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option autoImplicit false
namespace YM.CF.Merino.Plume
open Function Filter Topology Set Metric
variable {X:Type*}{W:Type*}{I:Type*} [PseudoMetricSpace W][Finite I]
variable {L:ℝ}{z:X→W}{q:X→I}


private theorem pill {f:ℕ→X→ℂ}{g:X→ℂ}{F:Filter ℕ}[F.NeBot]
 (t:TotallyBounded (range z))
 (hL:0 ≤ L)
 (p:∀n x y,q x=q y→ dist (f n x) (f n y)≤L*dist (z x) (z y))
 (u:∀ x,Tendsto (fun n=>f n x) F (𝓝 (g x)))
 {ε:ℝ}(v:0<ε) : ∀ᶠ n in F,∀ x,dist (f n x) (g x)≤ε:=by
 refine (eventually_all.mpr ?_ : ∀ᶠ n in F, ∀ i:I, ∀x,q x=i→dist (f n x) (g x)≤ε).mono fun n w x=>w (q x) x rfl
 intro i
 let s:={x | q x=i}
 let R:=z '' s
 have e: R⊆range z:= by rintro _ ⟨x,_,rfl⟩;exact ⟨x,rfl⟩
 let d:=ε/(4*(L+1))
 obtain ⟨T,H,D,G⟩:= finite_approx_of_totallyBounded (t.subset e) d
    (show 0<d by unfold d; positivity)
 let pick (i:↥T):X:=Classical.choose (H i.property)
 have b:∀ᶠ n in F, ∀y:↥T, dist (f n (pick y)) (g (pick y))<ε/2:=by
   haveI:= D.fintype
   exact eventually_all.mpr fun w=>Metric.tendsto_nhds.mp (u _) _ (half_pos v)

 filter_upwards [b] with n hn x hx
 obtain ⟨y,m⟩:=Set.mem_iUnion.mp (G ⟨x,hx,rfl⟩)
 obtain ⟨hy,m⟩:=Set.mem_iUnion.mp m
 let j:↥T:=⟨y,hy⟩
 let a:=pick j
 have w:q a=i∧z a=y:=Classical.choose_spec (H j.property)
 have dx:L*dist (z x) (z a)≤ε/4:=by
    rw [w.2]
    refine (mul_le_mul_of_nonneg_left (Metric.mem_ball.mp m).le hL).trans ?_
    have l:d*(4*(L+1))=ε:=div_mul_cancel₀ _ (by positivity)
    have h:0<d:=by unfold d;positivity
    linarith
 refine (dist_triangle (f n x) (f n a) _).trans ?_
 have h1:(∀m,dist (f m x) (f m a) ≤ ε/4):=fun m=>
   (p m _ _ (hx.trans w.1.symm)).trans dx
 have h2:=le_of_tendsto' ((u x).dist (u a)) h1
 have h3:dist (f n a) (g a)<ε/2:=hn j
 rw [dist_comm] at h2
 linarith [h1 n,dist_triangle (f n a) (g a) (g x)]


def spray (f:ℕ→X→ℂ) (g:X→ℂ):Prop:=
    ∀ε:ℝ,0<ε→∀ᶠ n in atTop,∀x,dist (f n x) (g x)≤ε
lemma spray.rise {f:ℕ→X→ℂ}{g:X→ℂ}(v:spray f g)(x:X):
    Tendsto (fun n=>f n x) atTop (𝓝 (g x)):=by
 refine Metric.tendsto_nhds.mpr fun e h=>?_ 
 exact (v (e/2) (half_pos h)).mono fun _ h0=>lt_of_le_of_lt (h0 x) (half_lt_self h)
/-- Finite code discontinuity + totally bounded coordinate. -/
theorem feather {f:ℕ→X→ℂ}
 (t:TotallyBounded (range z))
 (hL:0 ≤ L)
 (p:∀n x y,q x=q y→ dist (f n x) (f n y)≤L*dist (z x) (z y))
 (M:ℝ)(H:∀n x,‖f n x‖≤M) :
 ∃ (σ:ℕ→ℕ) (g:X→ℂ),StrictMono σ∧ spray (f∘σ) g:=by
 let F:=Ultrafilter.of (atTop:Filter ℕ)
 let S:={f:X→ℂ|∀x,f x∈closedBall 0 M}
 have hS:IsCompact S:=isCompact_pi_infinite (by exact fun _=>isCompact_closedBall _ _) -- adjust


 have v:(Ultrafilter.map f F:Filter (X→ℂ))≤𝓟 S:=by
    rw [Ultrafilter.coe_map,le_principal_iff,Filter.mem_map]
    exact Eventually.of_forall fun n x=> by simp [H]
 obtain ⟨g,_,a⟩:=hS.ultrafilter_le_nhds _ v
 rw [Ultrafilter.coe_map] at a
 obtain ⟨y,_,b,c⟩:=exists_seq_strictAnti_tendsto (0:ℝ)
 obtain ⟨σ,r,l⟩:=extraction_forall_of_frequently fun i=>
    (pill t hL p (tendsto_pi_nhds.mp a) (b i)).frequently.filter_mono
       (Ultrafilter.of_le _)
 refine ⟨σ,g,r,fun e h=>(c.eventually_lt_const h).mono ?_⟩
 intro n j x
 exact (l n x).trans j.le

abbrev veil : Filter ℕ:=↑(Ultrafilter.of (atTop:Filter ℕ))
def blizzard (f:ℕ→X→ℂ)(g:X→ℂ):Prop:=
    ∀ε:ℝ,0<ε→∀ᶠ n in veil,∀x,dist (f n x) (g x)≤ε
lemma mantle {f:ℕ→X→ℂ}
 (t:TotallyBounded (range z))
 (hL:0 ≤ L)
 (p:∀n x y,q x=q y→ dist (f n x) (f n y)≤L*dist (z x) (z y))
 (M:ℝ)(H:∀n x,‖f n x‖≤M) :
 ∃g, blizzard f g:=by
 let S:={f:X→ℂ|∀x,f x∈closedBall 0 M}
 have hS:IsCompact S:=isCompact_pi_infinite fun _=>isCompact_closedBall _ _
 have v:(Ultrafilter.map f (Ultrafilter.of atTop):Filter (X→ℂ))≤𝓟 S:=by
    rw [Ultrafilter.coe_map,le_principal_iff,Filter.mem_map]
    exact Eventually.of_forall fun n x=> by simp [H]
 obtain ⟨g,_,a⟩:=hS.ultrafilter_le_nhds _ v
 rw [Ultrafilter.coe_map] at a
 exact ⟨g,fun _=>pill t hL p (tendsto_pi_nhds.mp a)⟩


lemma parked {Z : ℕ→Type*} {f : ∀ s:ℕ, ℕ→Z s→ℂ}
    {g: ∀ s:ℕ, Z s→ℂ} (h:∀s,blizzard (f s) (g s)):
    ∃r:ℕ→ℕ, StrictMono r ∧ ∀s,spray (f s∘r) (g s):=by
 obtain ⟨y,_,b,c⟩:=exists_seq_strictAnti_tendsto (0:ℝ)
 have t(i:ℕ):∃ᶠ n in atTop,∀s:Fin (i+1),∀x,dist (f s.val n x) (g s.val x)≤y i:=
   Filter.Frequently.filter_mono
     (Eventually.frequently (eventually_all.mpr (fun s=>h s.val _ (b i))) )
     (Ultrafilter.of_le atTop)
 obtain ⟨r,u,v⟩:=extraction_forall_of_frequently t
 refine ⟨r,u,fun s e d=>?_⟩
 filter_upwards [eventually_ge_atTop s,c.eventually_lt_const d] with i z l x
 exact (v i ⟨s,Nat.lt_succ_iff.mpr z⟩ x).trans l.le
end YM.CF.Merino.Plume
