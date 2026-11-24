import YM.CF.BProof.Contour.Tower
import YM.CF.BProof.Mapping.Ledger
import Mathlib.MeasureTheory.Function.FactorsThrough

/- Support extension to full space of Spice/Course. Scope exactly visible Tang and
I regions. Core decisions compared beams exc sets, not pointwise tags unless inside T.
Adapt Borel separation (cf Veil extension) to `reads`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Contour
open Function Filter NormedSpace TopologicalSpace MeasureTheory Relation Finset RG
open Lattice Prox Grid Moment Account Tower
open scoped Topology BigOperators Classical
variable {n:ℕ}(s: Fin n→Side)(r:ℕ) (X:Vertex s→Type*) [∀ i,MeasurableSpace (X i)]
abbrev ℂn:= Comps s r
abbrev Exciting : Type _ := (@Exc n s) -- syntax
namespace Season
-- delete
variable [∀ i,StandardBorelSpace (X i)] [∀ i,Nonempty (X i)]
abbrev Virtue (f:((i : Vertex s) → X i)→Prop):=MeasurableSet {x|f x}
-- factor-without-change beams analytic measurable subset
lemma gather {g:((i : Vertex s) → X i)→ℂ}(h:Measurable g)(T:Sites s)(P:Set ((i : Vertex s) → X i))(p:MeasurableSet P)(k:∀ x∈P,∀ y∈P,(∀ i∈T,x i=y i)→ g x=g y): ∃ f:((i : Vertex s) → X i)→ℂ,reads X f T∧Measurable f∧∀ x∈P,f x=g x:=by
 let v:((i : Vertex s) → X i)→ ((i : Vertex s) → X i):=fun x i=>if i∈ T then x i else Classical.arbitrary _; let D:=↥P; let θ:D→ ((i : Vertex s) → X i) := fun x=> v x.val; let H:D→ℂ:=fun x=>g x.val; letI : StandardBorelSpace D:= p.standardBorel
 have hv:Measurable v:=measurable_pi_lambda _ fun i=>by unfold v; split <;> first|exact measurable_pi_apply _|exact measurable_const
 have ht:Measurable θ:=hv.comp measurable_subtype_coe; let m:= (inferInstance : MeasurableSpace D); let M:= (inferInstance:MeasurableSpace ((i : Vertex s) → X i))
 have he: Measurable[(M.comap θ)] H:=by
    letI := upgradeStandardBorel (((i : Vertex s) → X i)); intro B hB; let S:=H ⁻¹' B; let U:=θ '' S; let V:=θ '' Sᶜ; have hs:MeasurableSet (H ⁻¹' B):=h.comp measurable_subtype_coe hB -- tune ambiguity m instance in goal?
    have hl:Disjoint U V:=by
       rw [Set.disjoint_left]; rintro i ⟨j,p,rfl⟩ ⟨l,g,e⟩; have hf:H l= H j:=by apply k l.val l.property j.val j.property; intro i s; simpa only [θ,v,s,if_true] using congrFun e i
       exact g (show l∈ S from (show H l∈ B from hf.symm ▸ (show H j∈ B from p))) -- tune
    have hk:= (hs.analyticSet_image ht).measurablySeparable (hs.compl.analyticSet_image ht) hl; obtain ⟨Y,l,u,v⟩:= hk
    refine ⟨Y,v,(by ext i; constructor; intro a; by_contra b; exact Set.disjoint_left.mp u (Set.mem_image_of_mem θ (show i∈ Sᶜ from b)) a; exact fun b=> l (Set.mem_image_of_mem θ b))⟩
 obtain ⟨w,c,t⟩:= he.exists_eq_measurable_comp; refine ⟨w ∘ v,?_,c.comp hv,fun x h=> (congrFun t (⟨x,h⟩:D)).symm⟩; intro x y p; apply congrArg w; ext i; by_cases l:i∈T; · simp [v,l,p i l]
 simp [v,l]
lemma keep {g:((i : Vertex s) → X i)→ℂ}(h:Measurable g)(T:Sites s)(P:Set ((i : Vertex s) → X i))(p:MeasurableSet P)(k:∀ x∈P,∀ y∈P,(∀ i∈T,x i=y i)→ g x=g y)(c:((i : Vertex s) → X i)→ℝ)(w:Measurable c)(u: reads X c T)(hx:∀ x,0≤c x)(m:∀ x∈P, ‖g x‖≤ c x): ∃ f:((i : Vertex s) → X i)→ℂ,reads X f T∧Measurable f∧ (∀ x,‖f x‖≤c x) ∧∀ x∈P,f x=g x:=by
 obtain ⟨f,k,l,t⟩:= gather s X h T P p k; let F(x:((i : Vertex s) → X i)):= if ‖f x‖≤c x then f x else 0
 refine ⟨F,fun x y e=>(by unfold F; rw [k x y e,u x y e]),l.ite (measurableSet_le l.norm w) measurable_const,?_,?_⟩
 · intro i; unfold F; split; assumption; rw [norm_zero]; apply hx
 intro i h; unfold F; rw [t i h,if_pos (m i h)]
-- measurable set test for cores. Finset membership as Prop; no need Measurable V elves instance? define locally. Atmos for account. also filtered press coverage
variable {s X} (V:((i : Vertex s) → X i)→ Exc s)
def chooseE(x:((i : Vertex s) → X i)):=Contact s r (V x)
def beams(F:Sites s)(x y:((i : Vertex s) → X i)): Prop := ∀ i∈ F,x i=y i
def esp (S:Sites s)(x y:((i : Vertex s) → X i)): Prop:= see (plan s r) S (chooseE r V x) = see (plan s r) S (chooseE r V y) ∧ beams (X:=X) (comfort (plan s r) S (chooseE r V x)) x y
def Vis(V:((i : Vertex s) → X i)→ Exc s): Prop:=∀ q:Exc s,MeasurableSet {x| V x=q}
lemma vis (v:Vis V)(f: Exc s→Prop): Virtue s X (fun x=>f (V x)) := by -- successful if Virtue takes s X? check
 unfold Virtue; rw [show {x| f (V x)}= ⋃ i:Exc s, if f i then {x|V x=i} else ∅ from ?_]; apply MeasurableSet.iUnion; intro i; split; exact v _; exact MeasurableSet.empty
 ext i; rw [Set.mem_iUnion]; constructor; intro h; exact ⟨V i,by rw [if_pos (show f (V i) from h)]; rfl⟩
 rintro ⟨q,h⟩; split at h; rw [Set.mem_setOf]; rwa [show V i=q from h]; contradiction
variable {J:Type*}[Fintype J][DecidableEq J] {adm:((i : Vertex s) → X i)→Prop} {u:((i : Vertex s) → X i)→ℂ}{α:ℝ}(T:Teller (gridBase s) adm (esp r V) J u 4 α)
include T
lemma candy (v:Vis V)(q:Virtue s X adm) : ∃ R:Spice X (plan s r) J,Toll R.t R.w 4 α ∧ (∀ i,Grid.Conn (R.t i) 1)∧∀ x,adm x→ ∑ j,R.A j (chooseE r V x) x= u x:=by
 let K:=plan s r; let t:= T.starboard; let w:=T.size
 have he(Q:Comps s r)(i:J) : ∃ f:((i : Vertex s) → X i)→ ℂ, reads X f (t i∪ hull K.T Q) ∧ Measurable f ∧ (∀ x,‖f x‖ ≤ w i)∧∀ x,adm x∧ see K (t i) (chooseE r V x)=Q→ f x=T.bill i x:=by
    let S:= {x|adm x∧ see K (t i) (chooseE r V x)=Q}; have hh: MeasurableSet S:= MeasurableSet.inter q (vis V v (fun p=> see K (t i) (Contact s r p)=Q)); refine keep s X (T.meas i) _ S hh (fun x px y py g=> T.private_read i x y ?_ px.1 py.1) _ measurable_const (fun _ _ _=>rfl) (fun _=>T.pay.nonneg _) (fun x p=> T.amount i x p.1)
    have hv:see K (t i) (chooseE r V x)=Q:=px.2; refine ⟨hv.trans (show see K (t i) (chooseE r V y)=Q from py.2).symm,?_⟩; unfold beams comfort; change beams (X:=X) (t i∪ hull K.T (see K (t i) (chooseE r V x))) x y; rw [hv]; exact g
 choose F k hm hw h using he
 let f(i:J)(Q:Comps s r):= F (see K (t i) Q) i; refine ⟨⟨t,fun i=>(T.our i).1,f,w,fun i P Q _ _ h=>congrArg (fun x=> F x i) h,fun i _ _=>k _ _,fun i _ _=> hm _ _,fun i _ _=> hw _ _⟩,T.pay,fun i=>(T.our i).2,fun x q=>?_⟩; rw [T.values x q]; exact sum_congr rfl fun i _=> h _ i x ⟨q,rfl⟩
end Season
end YM.CF.BProof.Contour
