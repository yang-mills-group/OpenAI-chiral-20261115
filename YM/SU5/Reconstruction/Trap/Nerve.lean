import YM.SU5.Reconstruction.Trap.Dried
import Mathlib.Analysis.InnerProductSpace.ProdL2
/-!
# The trap from two graphs. Generic. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {H D:Hilbert} {X Y:Type} [AddCommGroup X] [Module ℂ X] (l:X→ₗ[ℂ] H) (r:X→ₗ[ℂ]D) (U:Y→H)(V:Y→D)
local notation "W₀"=> WithLp 2 (H.space×D.space)
noncomputable def graph (l:X→ₗ[ℂ]H)(r:X→ₗ[ℂ]D): Submodule ℂ (WithLp 2 (H.space × D.space)) := LinearMap.range ((WithLp.linearEquiv 2 ℂ (H.space × D.space)).symm.toLinearMap.comp (l.prod r)) |>.topologicalClosure
instance : CompleteSpace ↥(graph l r):=(LinearMap.range ((WithLp.linearEquiv 2 ℂ (H.space × D.space)).symm.toLinearMap.comp (l.prod r))).isClosed_topologicalClosure.completeSpace_coe
noncomputable def Crew (l:X→ₗ[ℂ]H)(r:X→ₗ[ℂ]D): Hilbert:={space:=↥(graph l r)}
local notation "Zh"=> Crew l r
noncomputable def pinl (l:X→ₗ[ℂ]H)(r:X→ₗ[ℂ] D): Crew l r →L[ℂ] H:= (WithLp.fstL 2 ℂ H D).comp (graph l r).subtypeL
noncomputable def pinr (l:X→ₗ[ℂ]H)(r:X→ₗ[ℂ] D): Crew l r →L[ℂ] D:= (WithLp.sndL 2 ℂ H D).comp (graph l r).subtypeL
noncomputable def buildGraph (x:X): Crew l r:= (⟨WithLp.toLp 2 (l x,r x), ((Submodule.le_topologicalClosure _) (⟨x,rfl⟩))⟩:graph l r)
local notation "P"=> pinl l r
local notation "Q"=> pinr l r
lemma tap_build (x:X) : P (buildGraph l r x)=l x ∧ Q (buildGraph l r x)=r x:= ⟨rfl,rfl⟩
lemma toy (x:Zh): WithLp.toLp 2 (P x,Q x)= (x:graph l r).val:= rfl
lemma lens_dense : DenseRange (buildGraph l r):=by
 let f x:= WithLp.toLp 2 (l x,r x); have h': (graph l r:Set (WithLp 2 (H.space×D.space)))= closure (Set.range f):= rfl
 intro v; change (v:graph l r)∈ _; rw [show closure (range (buildGraph l r))=((graph l r).subtype) ⁻¹' closure (Subtype.val '' range (buildGraph l r)) from ?_]; -- tune
 swap
 · exact (Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image (range (buildGraph l r)))
 have he: Subtype.val '' (Set.range (buildGraph l r)) = Set.range f:= by rw [← Set.range_comp]; rfl
 rw [he,←h']; exact (v:graph l r).property
variable (x:DenseRange l)(y:DenseRange r) (p:DenseRange U)(q:DenseRange V) (v:∀ i j, inner ℂ (U i) (l j)= inner ℂ (V i) (r j))
include v
lemma low_step (a:Y)(i:Zh): inner ℂ (U a) (P i)= inner ℂ (V a) (Q i):=by
 apply congrFun (a:=i) ((lens_dense l r).equalizer (((innerSL ℂ (U a)).comp P).continuous) (((innerSL ℂ (V a)).comp Q).continuous) (funext fun j=> v a j)); -- tune
include x y p q
def pier : Clasp (Crew l r) H D where
 l:=P
 r:=Q
 p:=by apply x.mono; rintro t ⟨j,rfl⟩; exact ⟨buildGraph l r j,rfl⟩
 q:=by apply y.mono; rintro t ⟨j,rfl⟩; exact ⟨buildGraph l r j,rfl⟩
 j i j t:=by
   have he: Q i=Q j:= q.eq_of_inner_right ℂ (fun y=>?_); -- tune
   · apply Subtype.ext; rw [←toy,←toy,t,he]
   rw [←low_step l r U V v,←low_step l r U V v,t]
 k i j t:=by
   have he: P i=P j:= p.eq_of_inner_right ℂ (fun y=>?_)
   · apply Subtype.ext; rw [←toy,←toy,t,he]
   rw [low_step l r U V v,low_step l r U V v,t]
 frame:= by
   ext1 a; apply ext_inner_left ℂ; intro b; simp [inner_add_right,ContinuousLinearMap.adjoint_inner_right]; rfl -- LP product tune
-- uses x y p q v in def `include`?
local notation "C₀"=> pier l r U V x y p q v
-- use Prop defs for application avoids trans dependent constructor
structure Faces (l:X→ₗ[ℂ] H) (r:X→ₗ[ℂ] D) (U:Y→H)(V:Y→D)(K:Hilbert)(C:Clasp K H D):Prop where
 sees (i:X): C.Latch (l i) (r i)
 meets (a:Y)(x:K): inner ℂ (U a) (C.l x)= inner ℂ (V a) (C.r x)
 full : Dense {x:K | ∃ i,C.l x=l i ∧ C.r x=r i}
 pass (M:H.Op)(N:D.Op): (∀ i:X, C.Latch (M (l i)) (N (r i))) → C.Pass M N
-- should derive pass from Faces full easier later
lemma cert : ∃ (K:Hilbert)(C:Clasp K H D), Faces l r U V K C:= by
 refine ⟨Crew l r,(C₀),?_⟩; let S:= (C₀)
 constructor
 · intro i; exact ⟨buildGraph l r i, rfl, rfl⟩
 · exact low_step l r U V v
 · apply (lens_dense l r).mono; rintro _ ⟨y,rfl⟩; exact ⟨y,rfl,rfl⟩
 intro A B f x; let s0:= A.comp S.l; let t0:= B.comp S.r; change S.Latch (s0 x) (t0 x)
 obtain ⟨p,b,e⟩:= mem_closure_iff_seq_limit.mp (lens_dense l r x); apply S.latch_limit atTop ((s0.continuous.tendsto _).comp e) ((t0.continuous.tendsto _).comp e); apply Eventually.of_forall; intro i; obtain ⟨j,t⟩:= b i; change S.Latch (s0 (p i)) (t0 (p i)); rw [← t]; exact f j
end YM.CrossedFrame
