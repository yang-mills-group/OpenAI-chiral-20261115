import GaugeFieldConstruction.Flour
import GaugeFieldConstruction.Depot

/-!
# The cost-lift of (100)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 6000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Empire Fathom Payroll Function Filter Set TopologicalSpace YM.Analysis MeasureTheory Points Bulb Palace Module RawBank Stage Row
open Floor Wick Invoice Gap Sailing
open scoped Topology BigOperators ContDiff
open Phys Flux.One
attribute [local instance] iG iF iX iU iT2 iW2 iV iS

section Nonunital
variable {I : Type*} [Fintype I] [DecidableEq I]
/-- Elementwise indicator. No constant polynomial. -/
lemma pricing (S : Submodule ℂ (I→ℂ)) (p : ∀ x y : S,x.val*y.val∈S) (s : ↥S): (fun k=> if s.val k=0 then (0:ℂ) else 1) ∈ S:= by
  classical
  -- 1 - prod(1 - s[k]^-1*v), over nonzero entries
  let b (i:I) : S:= (s.val i)⁻¹ • s
  let P (i:I):I→ℂ:= 1-(b i).val
  have h (f:Finset I) : ((1:I→ℂ)-∏ i∈f,P i)∈ S:= by
    induction f using Finset.induction_on with
    | empty=> simp
    | @insert i f v w =>
      let a:S:= ⟨1-∏ i∈f,P i,w⟩
      rw [Finset.prod_insert v, show ∏ i∈f,P i=1-a.val from by change _=1-(1-_); simp]
      have H:= S.sub_mem (S.add_mem (b i).property a.property) (p (b i) a)
      rw [show 1-P i*(1-a.val)=(b i).val+a.val-(b i).val*a.val by unfold P; ring]; exact H
  rw [show (fun k=> if s.val k=0 then (0:ℂ) else 1)=1-∏ i:I,P i from funext fun i=>?_]; exact h _
  change (if s.val i=0 then (0:ℂ) else 1)=1-(∏ i:I,P i) _; rw [Finset.prod_apply]; by_cases t:s.val i=0
  · have q j:P j i=1:= by change 1-_ * s.val i=1; rw [t,mul_zero,sub_zero]
    simp only [t,if_true, q,Finset.prod_const_one,sub_self]
  have r:P i i=0:=by change 1-(s.val i)⁻¹ * s.val i=0; rw [inv_mul_cancel₀ t,sub_self]
  rw [if_neg t,Finset.prod_eq_zero (f:=fun k=>P k i) (Finset.mem_univ i) r,sub_zero]
lemma panel (S : Submodule ℂ (I→ℂ)) (p : ∀ x y : S,x.val*y.val∈S) : ∃ u:S,(∀ i,u.val i=0∨u.val i=1) ∧ ∀ v:S,u.val*v.val=v.val := by
  classical
  have h (f: Finset I): ∃ u:S,(∀ i,u.val i=0∨ u.val i=1) ∧ ∀ v:S, ∀ i∈f,u.val i*v.val i=v.val i := by
    induction f using Finset.induction_on with
    | empty=> exact ⟨0, fun _=>Or.inl rfl,by simp⟩
    | @insert i f _ w=>
      obtain ⟨u,g,h⟩:=w
      by_cases he: ∃ r:S,r.val i≠0
      · obtain ⟨r,hr⟩:=he
        let x:S:= ⟨_,pricing S p r⟩
        let z:S:= u + x - ⟨_,p u x⟩
        have hp j:z.val j=u.val j + x.val j-u.val j*x.val j:=rfl
        have hv:x.val i=1:= if_neg hr
        have hu j:x.val j=0 ∨ x.val j=1:= by change (if r.val j=0 then (0:ℂ) else 1)=0 ∨ _; by_cases p : r.val j=0; exact Or.inl (if_pos p); exact Or.inr (if_neg p)
        refine ⟨z, fun j=> ?_,fun v j c=>?_⟩
        · rw [hp]; rcases hu j with a|a <;> rcases g j with b|b <;> rw [a,b] <;> simp
        cases Finset.mem_insert.mp c with
        | inl e=> rw [e,hp,hv]; ring
        | inr e=>
          rw [hp]; have p:= h v j e
          rcases hu j with a|a
          · simpa [a] using! (show (u.val j+x.val j-u.val j*x.val j)*v.val j=v.val j from by rw [a,mul_zero,sub_zero,add_zero,p]) -- simplify
          rw [a]; ring
      push Not at he; refine ⟨u,g,fun v j c=>?_⟩; rcases Finset.mem_insert.mp c with r|r
      · rw [r,he v,mul_zero]
      exact h v j r
  obtain ⟨u,p,w⟩:=h Finset.univ
  exact ⟨u,p,fun v=> funext fun i=> w v i (Finset.mem_univ i)⟩
end Nonunital

def payment (D : District) : Bundle:= (activates D.g,fun i=>activates (D.f i))
def Live (D : District) := D.g=true ∨ ∃ i,D.f i=true
def named : Bundle≃ₗ[ℂ] (Option Bool→ℂ) where
  toFun x i:= match i with | none=>x.1 | some i=>x.2 i
  invFun x:=(x none,fun i=>x (some i))
  left_inv x:= rfl; right_inv x:= funext fun i=>by cases i<;> rfl
  map_add' x y:= funext fun i=>by cases i <;> rfl
  map_smul' r x:=funext fun i=>by cases i <;>rfl
lemma multiplication (a b : Bundle) : named (a*b)=named a*named b := funext fun i=>by cases i <;> rfl
lemma unitS {X : Type*} [AddCommGroup X] [Module ℂ X] [Nontrivial X] (B:X→ₗ[ℂ]Bundle) (v:Injective B) (p : ∀ x y,B x*B y∈ LinearMap.range B):
    ∃ (D:District), Live D ∧ ∃ z:X,B z=payment D ∧ ∀ v:X,B v*B z=B v:= by
  classical
  let Y:=named.toLinearMap ∘ₗ B
  let S:= LinearMap.range Y
  have ht (x y:S) : x.val*y.val∈S:= by
    obtain ⟨a,ha⟩:=x.property; obtain ⟨b,hb⟩:=y.property; obtain ⟨c,hc⟩:=p a b
    rw [← ha,← hb]; refine ⟨c,?_⟩; change named (B c)=_; rw [hc,multiplication]; rfl
  obtain ⟨u,h,hV⟩:=panel S ht
  obtain ⟨z,g⟩:=u.property
  have hp v: B v*B z=B v:= by
    apply named.injective
    rw [multiplication,mul_comm]; change Y z * Y v= Y v; rw [g]; exact hV ⟨Y v,v,rfl⟩
  let D:= District.mk (decide (u.val none=1)) (fun i=>decide (u.val (some i)=1))
  have he j:u.val j=named (payment D) j:= by
    cases j with
    | none=> rcases h none with t|t <;> simp only [t, D,payment] <;> simp [activates,named,t] -- fix t
    | some i=> rcases h (some i) with t|t <;> simp [t,D,payment,activates,named]
  have hz:B z=payment D:= named.injective (g.trans (funext he))
  refine ⟨D,?_,z,hz,hp⟩; unfold Live; by_contra! hw
  have hg :payment D=0:= by
    have h (i):D.f i=false:= by cases p:D.f i; rfl; exact (hw.2 i p).elim
    simp only [payment, hw.1,h,activates]; apply Prod.ext <;> rfl
  obtain ⟨i,hi⟩:=exists_ne (0:X)
  rw [hg] at hz; apply hi; apply v; rw [map_zero]; nth_rw 1 [← hp i]; rw [hz,mul_zero]

end YM.GaugeFieldConstruction.Ember
