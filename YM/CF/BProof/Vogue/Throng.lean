import YM.CF.BProof.Vogue.Solar
/-! Stacking the parcels of worlds. Uniform coherence extends across all links. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh Shore Finset
open scoped Topology BigOperators NNReal ENNReal Classical
variable {K:Type}{n:Side}{d u:ℝ}{k r L:ℕ}
section Matrix
open Regard Equiv
variable {X Y I Z:Type*}
abbrev RoofB (X I:Type*):=X× (I→X)
private def tap(i:I)(f:X×X→X×X)(x:RoofB X I):RoofB X I:= ((f (x.1,x.2 i)).1,update x.2 i (f (x.1,x.2 i)).2)
private lemma tap_c (i:I)(f g:X× X→ X×X)(h:LeftInverse f g): LeftInverse (tap i f) (tap i g):=by
 intro x; simp only [tap,update_self,Prod.mk.eta,h _]; simp
private def neat(i:I)(E:Perm (X×X)): Perm (RoofB X I):= ⟨tap i E,tap i E.symm,tap_c i E.symm E E.left_inv,tap_c i E E.symm E.right_inv⟩
private lemma patch[DecidableEq Y]{F:X→ Y→Z}(U:I→Finset Y)(h:∀ i (s: Finset I),i∉s→ Pen (s.biUnion U) (U i) F)(s:Finset I):∃ E:Perm (RoofB X I),∀ x, (∀ i∈s, Matches (U i) (F (E x).1) (F (x.2 i))) ∧ ∀ i∉s,(E x).2 i=x.2 i:=by
 induction s using Finset.induction_on with
 | empty=> exact ⟨Equiv.refl _, by simp⟩
 | @insert i s u IH =>
    obtain ⟨E,H⟩:=IH; obtain ⟨P,g⟩:=h i s u; refine ⟨E.trans (neat i P),fun x=> ⟨fun j hj=>?_,fun j he=>?_⟩⟩
    · let y:=P ((E x).1,(E x).2 i); have hv:=fromPen g ((E x).1,(E x).2 i); rcases mem_insert.mp hj with rfl|hj
      · rw [← (H x).2 _ u]; exact hv.2.2.1
      exact (hv.1.reduce (subset_biUnion_of_mem U hj)).endL ((H x).1 j hj)
    change update (E x).2 i _ j=x.2 j; rw [update_of_ne (show j≠i from (fun e=> he (e.symm ▸ mem_insert_self ..)))]; exact (H x).2 _ fun k=> he (mem_insert_of_mem k)
lemma patch_Pen [Fintype I][DecidableEq Y]{F:X→ Y→Z}(U:I→Finset Y)(h:∀ i (s: Finset I),i∉s→ Pen (s.biUnion U) (U i) F):∃ E:Equiv.Perm (RoofB X I),∀ x i, Matches (U i) (F (E x).1) (F (x.2 i)):=by obtain ⟨E,g⟩:=patch U h univ; exact ⟨E,fun x i=> (g x).1 i (mem_univ _)⟩
end Matrix
open Regard
variable (P:Spice n K d u k L)(M:Support (Cube.More n))
def skip(k:ℕ)(v:Fleets M r) :Support (Cube.More n):= Finset.univ.filter fun i=>∃ x:reach n,x.1=i∧ Bubb M k x ∧ soup M r x=v.val
def point (x:reach n)(p:Bubb M r x): Fleets M r:= ⟨_,ft M r p⟩ -- tune order
variable (p:k≤ r)(h:k+1+(k+1)+L≤2*r+20)
include p h
lemma effect_many : ∃ E:Equiv.Perm (RoofB K (Fleets M r)),∀ x i, Matches (skip M k i) (fun l (y:Pane n) (j:Axis)=> P.P (E x).1 y (l,j)) (fun l (y:Pane n) (j:Axis)=>P.P (x.2 i) y (l,j)):=by
 refine patch_Pen (F:=fun i x (U:Pane n) j=>P.P i U (x,j)) (fun i:Fleets M r=>skip M k i) (fun i s q=>?_) -- s variable name conflict
 apply P.gap; intro a ha b hb; obtain ⟨j,u,t⟩:=mem_biUnion.mp ha; obtain ⟨x,rfl,H,G⟩:=(mem_filter.mp t).2; obtain ⟨y,rfl,g,e⟩:= (mem_filter.mp hb).2; exact lives_space h p x y (fun f=> q (Subtype.ext (G.symm.trans (f.trans e)) ▸ u)) H g
-- show soup versions converge on same Pane all flags.One-shot.
lemma epoch : ∃ E: Equiv.Perm (RoofB K (Fleets M r)),∀ U:Pane n, M=RG.flags u U→ ∀ t (x:reach n)(v:Bubb M r x), P.P (E t).1 U x = P.P (t.2 (point M x v)) U x:=by
 obtain ⟨E,hx⟩:= effect_many P M p h; refine ⟨E,fun U pM t i v=>?_⟩; by_cases e:Bubb M k i; · exact congrFun (congrFun (hx t (point M i v) (mem_filter.mpr (show i.1∈univ∧∃ x:reach n,x.1=i.1∧Bubb M k x ∧ soup M r x= (point M i v).val from ⟨mem_univ _,i,rfl,e,rfl⟩))) U) i.2
 rw [(P.ok _).covers U i,(P.ok _).covers U i] <;> rw [← pM] <;> exact not_not.mp (fun v=> e (pieV .. |>.2 v))
-- stronger variant needed E independent U
end YM.CF.BProof.Vogue
