import HectorA.Jets
set_option autoImplicit false
noncomputable section
namespace Yoland
open Filter Function Finset Set
open scoped Topology ContDiff BigOperators NNReal InnerProductSpace Classical
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℂ X][CompleteSpace X]
-- real instance use `InnerProductSpace.complexToReal`
#check InnerProductSpace.complexToReal
variable [NormedSpace ℝ X][IsScalarTower ℝ ℂ X][SMulCommClass ℝ ℂ X]
variable (f:ℝ→X)(A:AnalyticOnNhd ℝ f (Set.Ioi 0)) (a: ℝ)
-- translation property on strictly right times
structure Civil (f:ℝ→X) : Prop where
 price : AnalyticOnNhd ℝ f (Ioi 0)
 flow(t:ℝ)(u:0<t): ∃ F:X→L[ℂ]X, ∀x:ℝ,0<x→F (f x)=f (x+t)
local notation "P" => Ioi (0:ℝ)
variable (C:Civil f)
include C
-- localized transform
lemma shifted {F:X→L[ℂ]X}{t u:ℝ}(h:0<u)(p: F ∘ f =ᶠ[𝓝 u] (fun x=> f (x+t)))(n:ℕ): F (iteratedDeriv n f u)=iteratedDeriv n f (u+t):=by
 let L:=F.restrictScalars ℝ
 rw [show F (iteratedDeriv n f u)= L _ from rfl,← transport (C.price u h) L n]; change iteratedDeriv n (F ∘ f) u=_; rw [p.iteratedDeriv_eq, iteratedDeriv_comp_add_const]
-- homogeneous ODE with coeff indexed n≤j (only); derive chain for all n+a and x>u
lemma deflect (k:ℕ)(c:ℕ→ℂ){a:ℝ}(h:0<a)(t:(∑ i∈Finset.range (k+1), c i • iteratedDeriv i f a)=0)(n:ℕ)(r:ℝ)(q:a<r): (∑ i∈Finset.range (k+1), c i • iteratedDeriv (i+n) f r)=0:=by
 have hp:= h.trans q
 induction n generalizing r with
 | zero =>
    obtain ⟨F,e⟩:= C.flow (r-a) (sub_pos.mpr q)
    have hk:F ∘ f=ᶠ[𝓝 a] (fun x=> f (x+(r-a))):= (lt_mem_nhds h).mono (fun x hx=>e x hx)
    have hs(i:ℕ): iteratedDeriv (i+0) f r=F (iteratedDeriv i f a):=by rw [shifted f C h hk,show a+(r-a)=r from by ring,Nat.add_zero]
    simp_rw [hs,← map_smul,← map_sum,t,map_zero]
 | succ n ih=>
    let m(x:ℝ):= ∑ i∈Finset.range (k+1), c i • iteratedDeriv (i+n) f x
    have ht:m =ᶠ[𝓝 r] (fun _=>0):= (show ∀ᶠ y in 𝓝 r,a<y from lt_mem_nhds q).mono fun y (hy:a<y)=> ih y hy (h.trans hy)
    have he:= ht.deriv_eq
    unfold m at he; rw [deriv_fun_sum] at he; swap; · intro i _; exact ( (aoe C.price (i+n) hp).differentiableAt.const_smul (c i))
    simpa only [deriv_fun_const_smul_field, ← iteratedDeriv_succ,Nat.add_assoc,deriv_const] using he
-- highest k with nonzero c imposes all jets at r=a+1 in finite span
lemma liable(k:ℕ)(c:ℕ→ℂ)(hc:c k ≠0)(ha:0<a)(h:(∑ i∈Finset.range (k+1), c i • iteratedDeriv i f a)=0):
 let T:=Submodule.span ℂ ((fun i=>iteratedDeriv i f (a+1)) '' {n:ℕ|n<k});
 ∀ i:ℕ, iteratedDeriv i f (a+1) ∈ T:=by
 intro T i
 induction i using Nat.strong_induction_on with
 | h i ih=>
    by_cases e:i<k
    · exact Submodule.subset_span ⟨i,e,rfl⟩
    let n:=i-k; have t:k+n=i:=Nat.add_sub_of_le (le_of_not_gt e)
    have he:= deflect f C k c ha h n (a+1) (lt_add_one _); rw [Finset.sum_range_succ,t,add_eq_zero_iff_eq_neg] at he
    have hp:(c k) • iteratedDeriv i f (a+1)= -(∑ j∈ Finset.range k,c j • iteratedDeriv (j+n) f (a+1)):= by rw [he, neg_neg] -- tune
    have hl:=T.neg_mem (T.sum_mem (fun j (hj:j∈Finset.range k)=> T.smul_mem (c j) (ih (j+n) (by have hh:=Finset.mem_range.mp hj; omega))))
    rw [←hp] at hl; have hq:=T.smul_mem ((c k)⁻¹) hl
    rwa [smul_smul,inv_mul_cancel₀ hc,one_smul] at hq
#check liable
end Yoland
