import YM.CF.BProof.Veil.Reads
/-! Costed Borel kernels off price domains. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Veil
open Function Filter NormedSpace Finset MeasureTheory RecN
open Cube Lattice Tenant
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Classical
variable {s: Side}{I Y D E:Type}[MeasurableSpace D][MeasurableSpace E]
-- supports in `Part` may stand still if pay=0; will take care in arrays to ensure chosen anchor
structure Part (b:RecN s D) (S:Support s)(c:ℝ) where
 val:D→ℂ
 tag: TagF b (T:=S) val c
 ward : b.fixed val
variable {b:RecN s D}{q: RecN s E}{S: Support s}{c:ℝ}(p:Part b S c)
lemma paint_e (v:D→ℂ)(h:TagF b (T:=S) v c) : ∃ p:Part b S c,p.val=b.varnish v:=⟨⟨_,b.even S h, b.evenFix⟩,rfl⟩
theorem edited [StandardBorelSpace D][StandardBorelSpace E] {f:E→D}(u:Measurable f)(k:∀ g:geo s,∀ x:E,∃ y, f y=b.act g (f x)){v:E→ℂ}(D: Measurable v)(hp:0≤c) (w:∀ i, ‖v i‖≤ c)(h:∀ i j,b.agree S (f i) (f j) → v i=v j)(q:∀ g i j, f j=b.act g (f i)→v j=v i) : ∃ p:Part b S c,∀ i,p.val (f i)=v i:=by
 obtain ⟨T,h,e⟩:=b.wid hp S _ u _ D w h; refine ⟨⟨b.varnish T,b.even S h,b.evenFix⟩,fun i=>?_⟩; show b.varnish T (f i)=_; rw [b.evenFree S h,e]; intro g; obtain ⟨y,k⟩:=k g i; rw [← k,e,e,q g i y k]
namespace Part
@[fun_prop] lemma meas : Measurable p.val:= p.tag.borel
lemma cost(i:D): ‖p.val i‖≤ c:= p.tag.pays _
lemma include_b {x y:D}(h:b.agree S x y): p.val x=p.val y:=p.tag.ruled h
def liftC (f:E→ D)(h:Measurable f)(u:∀ g x,f (q.act g x)=b.act g (f x))(e:∀ i j,q.agree S i j→ b.agree S (f i) (f j)): Part q S c:=⟨p.val ∘ f,⟨p.tag.pos,p.tag.borel.comp h,fun i=>p.cost _,@fun i j g=>p.include_b (e i j g)⟩,fun g x=>by simp only [Function.comp_apply,u,p.ward g]⟩
def fstL(q:RecN s E) := p.liftC (q:=b.together q) Prod.fst measurable_fst (fun _ _=>rfl) (fun i j h=> congrArg Prod.fst h)
def sndL(q:RecN s E) := p.liftC (q:=q.together b) Prod.snd measurable_snd (fun _ _=>rfl) (fun i j h=> congrArg Prod.snd h)
-- static assertions used to combine families packed
lemma zero (v:c=0) : p.val = fun _=>0:=by ext1 i; exact norm_le_zero_iff.mp ((p.cost _).trans_eq v)
end Part
end YM.CF.BProof.Veil
