import YM.CF.Sample.Air
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact independence, matching marginals via support-only equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase.Sample
open scoped BigOperators Topology
open MeasureTheory Set Finset Function Filter
variable {I T E : Type*} [DecidableEq I] [Fintype I] [MeasurableSpace T] [TopologicalSpace T] [CompactSpace T] [T2Space T] [SecondCountableTopology T] [BorelSpace T] [Nonempty T] {μ : Measure T} [IsProbabilityMeasure μ] (p q : Plan I μ) {s t : Finset I}
-- no null extension on a marginal
lemma widens (h : Bank p s) (x : I→T) (e : sails p s x≠0) : ∃ y, AgreeF s y x ∧ fall p y≠0 := by
  by_contra! k
  have ht : ∀ i:I→T, sails p sᶜ (patchF s x i)=0 := by
    intro i; apply (mul_eq_zero.mp _).resolve_left e; rw [←fuel p h (patch_left s x i)]; exact k _ (patch_left s x i)
  have he := aer_valid p s x; unfold aerate at he; simp only [ht,integral_zero] at he; exact zero_ne_one he
section receipts
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (v f : (I→T)→E)
abbrev bet (v : (I→T)→E) x := fall p x • v x
lemma aer_miss (h : Bank p s) (x : I→T) (e:sails p s x=0) : aerate s μ (bet p v) x=0 := by unfold aerate bet; simp_rw [fuel p h (patch_left s x _),e,zero_mul,zero_smul]; simp
lemma aer_side {x} (h : Bank p s) (k : ∀ y, AgreeF s y x → fall p y≠0 → v y=v x) : aerate s μ (bet p v) x=sails p s x • v x := by
  have he (y) : bet p v (patchF s x y)=(sails p s x*sails p sᶜ (patchF s x y)) • v x := by
    rw [←fuel p h (patch_left s x y), bet]; by_cases u : fall p (patchF s x y)=0
    · rw [u,zero_smul, zero_smul]
    rw [k _ (patch_left s x y) u]
  unfold aerate; simp_rw [he]; rw [integral_smul_const, integral_const_mul,show (∫ w, sails p sᶜ _ ∂fares I μ)=1 from aer_valid p s x,mul_one] -- tune
/-- only cross-plan equality on jointly active data. -/
lemma banks_like (h : Bank p s) (g : Bank q s) (l : ∀ z,sails p s z=sails q s z) (r : ∀ x y, AgreeF s x y→ fall p x≠0→ fall q y≠0→ v x=f y) (he : Continuous (bet p v)) (hg : Continuous (bet q f)) :
    (∫ y, bet p v y ∂fares I μ)=∫ y, bet q f y ∂fares I μ := by
  rw [←split_air (μ:=μ) s he,←split_air (μ:=μ) s hg]; apply integral_congr_ae; apply Eventually.of_forall; intro x
  by_cases e:sails p s x=0
  · rw [aer_miss p v h x e,aer_miss q f g x (by rw [←l,e])]
  obtain ⟨y,H,K⟩ := widens p h x e; obtain ⟨z,u,t⟩ := widens q g x (fun h=>e ((l x).trans h))
  have hz : AgreeF s y z := fun i hi=> (H _ hi).trans (u _ hi).symm
  have hp := r _ _ hz K t
  rw [←aerate_agree _ H, ←aerate_agree _ u,aer_side p v h,aer_side q f g,l,banked q g hz,hp]
  · intro j hj he; rw [← r y j _ K he, hp]; exact fun i hi=>(hz _ hi).trans (hj _ hi).symm
  intro i hi he; rw [hp]; exact r _ _ (fun j e=>(hi j e).trans (hz j e)) he t
end receipts

variable [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E] (v f : (I→T)→E)
lemma patch_ind (h : Disjoint s t) (k : ∀ x y, AgreeF s x y→ f x=f y) (l : ∀ x y, AgreeF t x y→v x=v y) (g : Continuous f) (e : Continuous v) :
    (∫ x,f x*v x ∂fares I μ)=(∫ x,f x ∂fares I μ)*(∫ x,v x ∂fares I μ) := by
  let M := ∫ x,v x ∂fares I μ
  rw [←split_air (μ:=μ) s (f:=fun x=> f x*v x) (g.mul e)]
  have he x : aerate s μ (fun x=>f x*v x) x=f x*M := by
    unfold aerate; have hQ (z) : AgreeF t (patchF s x z) z := fun i l₁=> if_neg (fun j=> disjoint_left.mp h j l₁)
    simp_rw [k _ x (patch_left s x _),l _ _ (hQ _)]
    let p := ContinuousLinearMap.mul ℝ E (f x); exact (p.integral_comp_comm (net_compact e)) -- tune
  change (∫ y,aerate s μ (fun x=>f x*v x) y ∂fares I μ)=_*M
  simp_rw [he]
  let p := (ContinuousLinearMap.mul ℝ E).flip M
  exact (p.integral_comp_comm (net_compact g))
lemma independent (h : Bank p s) (g : Bank p t) (L : ∀ x y, AgreeF s x y→fall p x≠0→fall p y≠0→ f x=f y) (K : ∀ x y, AgreeF t x y→fall p x≠0→fall p y≠0→ v x=v y) (l : Disjoint s t) (he : Continuous (bet p f)) (hv : Continuous (bet p v)) (u : Continuous (bet p (fun x=>f x*v x))) :
    (∫ y, bet p (fun x=>f x*v x) y ∂fares I μ) = (∫ y, bet p f y ∂fares I μ)*(∫ y, bet p v y ∂fares I μ) := by
  let S := s∪t; let F := fun x=>f x*v x
  let a := aerate S μ (bet p F); let b := aerate s μ (bet p f); let w := aerate t μ (bet p v)
  have hp x : sails p S x=sails p s x*sails p t x := prod_union l
  have hk := h.union g
  have hh (z : I→T) : a z=b z * w z := by
    by_cases ht:sails p S z=0
    · rw [show a z=0 from aer_miss p F hk z ht]; rw [hp] at ht
      rcases mul_eq_zero.mp ht with e|e <;> first | rw [show b z=0 from aer_miss p f h z e,zero_mul] | rw [show w z=0 from aer_miss p v g z e,mul_zero]
    obtain ⟨x,P,A⟩ := widens p hk z ht
    have hl := P.less Finset.subset_union_left; have hr := P.less Finset.subset_union_right
    unfold a b w; rw [←aerate_agree _ P,←aerate_agree (bet p f) hl, ←aerate_agree _ hr,aer_side p F hk,aer_side p f h,aer_side p v g,hp, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul] -- tune
    · intro y k v; exact K _ _ k v A
    · intro y k v; exact L _ _ k v A
    intro j u p; unfold F; rw [L j x (u.less Finset.subset_union_left) p A, K j x (u.less Finset.subset_union_right) p A]
  rw [←split_air (μ:=μ) S u,←split_air (μ:=μ) s he, ←split_air (μ:=μ) t hv]; change (∫ y,a y ∂fares I μ)=(∫ y,b y ∂fares I μ)*(∫ y,w y ∂fares I μ)
  simp_rw [hh]; exact patch_ind (μ:=μ) w b l (fun _ _=>aerate_agree _) (fun _ _=>aerate_agree _) (aerate_cont _ _ he) (aerate_cont _ _ hv) -- tune
end YM.CF.Phase.Sample
