import YM.CF.Vp929.Analysis.Combo
import YM.CF.Vp929.Analysis.Stencil
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Stencil theorem on local jets of pure real-slope exponential pencils. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeRate
open Set Function Filter Topology Metric Complex
section
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
private def Tonal (t:Finset ℝ)(f:ℂ→F) : Prop:=∃ w:ℝ→F,∀ z:ℂ,f z=∑ r∈t,exp ((r:ℂ)*z) • w r
def Pencilled (n:ℕ)(f:ℂ→F):Prop:=∃ t:Finset ℝ, t.card ≤ n ∧ Tonal t f
variable {f g:ℂ→F} {s t:Finset ℝ} {n m:ℕ}
private lemma Tonal.mono (h:Tonal t f) (e:t⊆s):Tonal s f:=by
 classical
 obtain ⟨w,H⟩:=h; refine ⟨fun r=> if r∈t then w r else 0,fun z=>?_⟩
 rw [H]; symm; rw [←Finset.sum_subset e (fun r p q=>by simp [q])]; exact Finset.sum_congr rfl (fun r p=>by simp [p])
namespace Pencilled
lemma one (x:ℝ)(F:F) : Pencilled 1 (fun z=> exp ((x:ℂ)*z) • F):=by classical exact ⟨{x},by simp, (fun _=> F), by simp⟩
lemma const (F:F):Pencilled 1 (fun _=>F):= by simpa using one 0 F
lemma add (h:Pencilled n f)(e:Pencilled m g):Pencilled (n+m) (fun x=>f x+g x):=by
 classical
 obtain ⟨s,p,h⟩:=h; obtain ⟨t,q,e⟩:=e
 refine ⟨s∪t, (Finset.card_union_le ..).trans (add_le_add p q),?_⟩; obtain ⟨w,H⟩:= h.mono (Finset.subset_union_left (s₂:=t)); obtain ⟨v,E⟩:= e.mono (Finset.subset_union_right (s₁:=s)); exact ⟨w+v, by simp [H,E,smul_add,Finset.sum_add_distrib]⟩
lemma map [NormedAddCommGroup G] [NormedSpace ℂ G] (h:Pencilled n f)(L:F→ₗ[ℂ]G):Pencilled n (fun z=> L (f z)):=by
 obtain ⟨s,p,w,H⟩:=h; exact ⟨s,p,fun i=> L (w i),by simp [H,map_sum]⟩
lemma complex_cost (r:ℂ)(h:Pencilled n f) : Pencilled n (fun x=>r•f x):= h.map (r • LinearMap.id)
private lemma scalar (r:ℝ)(h:Pencilled n f) : Pencilled n (fun x=> r • f x):= by simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact h.complex_cost (r:ℂ)
lemma mono (e:n≤m)(h:Pencilled n f): Pencilled m f:= by obtain ⟨s,p,h⟩:=h; exact ⟨s,p.trans e,h⟩
lemma entire (h:Pencilled n f): Differentiable ℂ f:= by obtain ⟨s,p,w,H⟩:=h; rw [show f=_ from funext H]; fun_prop
end Pencilled
variable {c w:ℝ} {z:ℂ} {s:Set E} {C:ℝ} {x:E}
local notation "z@" => ((c:ℂ)+z*w)
local notation "t0" i => ((wooden n c w i:ℝ):ℂ)
local notation "Σ_" n => panel n
/-- Stencil coefficient grant. Use separate from stencil estimates to specialize before knowing its nodes. -/
def Appears (n:ℕ)(C:ℝ): Prop:= ∀ c w:ℝ, ∀ z:ℂ, ‖z‖ ≤ 2 → ∀ s: Finset ℝ, s.card ≤ n → ∃ p:ℕ→ℂ, (∑ i∈panel n, ‖p i‖) ≤ C ∧ ∀ x∈s, exp ((x:ℂ)*((c:ℂ)+z*w)) = ∑ i∈panel n, p i * exp ((x:ℂ)* (wooden n c w i : ℂ))

variable (A:Appears n C) (hz:‖z‖≤2) (h:0<C) {Fv:E→ℂ→F}
include A hz
lemma Pencilled.span (h:Pencilled n f) : ∃ p:ℕ→ℂ,(∑ i∈panel n, ‖p i‖) ≤ C ∧ f z@=∑ i∈panel n, p i • f (t0 i):= by
 classical
 obtain ⟨s,e,x,H⟩:=h; obtain ⟨p,hu,P⟩:=A c w z hz s e; refine ⟨p,hu,?_⟩
 rw [H]; simp_rw [H,Finset.smul_sum]; rw [Finset.sum_comm (s:=panel n)]; refine Finset.sum_congr rfl ?_; intro r v; simp_rw [P r v,Finset.sum_smul,mul_smul]
lemma Pencilled.stencil (h:Pencilled n f) : ‖f z@‖ ≤ C * ‖fun i:panel n=> f (t0 i)‖:= by
 obtain ⟨p,hP,P⟩:= h.span (c:=c) (w:=w) A hz; rw [P]; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum fun i e=> ?_) (le_trans (le_of_eq (Finset.sum_mul _ _ _).symm) (mul_le_mul_of_nonneg_right hP (norm_nonneg _))))
 rw [norm_smul]; exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i : panel n => f (t0 i)) ⟨i,e⟩) (norm_nonneg _)
lemma Pencilled.block (k:ℕ)(hv:2^k*m≤n) (P:∀ x∈ s, Pencilled m (Fv x)):Blocks C k s (fun x=>Fv x z@) (fun x (i:panel n)=>Fv x (t0 i)):= by
 classical
 let S:= (fun x=>(Fv x z@,fun i: panel n=> Fv x (t0 i))) '' s
 have Q (k:ℕ): ∀ p∈combos S k, ∃ f:ℂ→F, Pencilled (2^k*m) f ∧ p=(f z@,fun i: panel n=> f (t0 i)):= by
   clear hv; induction k with
   | zero=> rintro p ⟨_,⟨x,h,rfl⟩,r,rfl⟩; exact ⟨_, (by rw [pow_zero,one_mul]; exact (P _ h).scalar r),rfl⟩
   | succ k ih=>
      rintro p ⟨u,v,a,e,rfl⟩; obtain ⟨f,hf,rfl⟩:= ih u v; obtain ⟨g,hg,rfl⟩:= ih a e; exact ⟨fun x=> f x+g x,(by rw [pow_succ]; exact (by ring : 2^k*m+2^k*m=2^k*2*m) ▸ hf.add hg),rfl⟩
 refine Blocks.from_raw fun p q=>?_ ; obtain ⟨f,hf,rfl⟩:= Q k p q; exact (hf.mono hv).stencil A hz
include h
lemma Pencilled.transfer (k:ℕ)(hv:2^(k+2)*m≤n) (P:∀ x,Pencilled m (Fv x)) (Q:∀ i∈panel n, ContDiffAt ℝ k (fun x=> Fv x (t0 i)) x):
    ContDiffAt ℝ k (fun x=> Fv x z@) x ∧
    ∀ j:ℕ,j≤k→ ‖iteratedFDeriv ℝ j (fun x=> Fv x z@) x‖ ≤ C * ∑ i∈panel n, ‖iteratedFDeriv ℝ j (fun x=> Fv x (t0 i)) x‖:= by
 classical
 let Fu (x:E)(i:panel n):= Fv x (t0 i)
 have H:ContDiffAt ℝ k Fu x:= contDiffAt_pi.mpr fun i=> Q _ i.prop
 obtain ⟨t,ht,V⟩:= H.contDiffOn le_rfl (by simp)
 obtain ⟨s,o,Hs,xm⟩:= _root_.mem_nhds_iff.mp ht; have p:= Hs.mem_nhds xm
 have y:=Pencilled.block (Fv:=Fv) (c:=c) (w:=w) A hz (k+2) hv fun x (_ : x∈s)=> P x; obtain ⟨W,G⟩:= y.pay (k:=k) h Hs (V.mono o)
 refine ⟨W.contDiffAt p, fun j hj=>(G _ hj _ xm).trans (mul_le_mul_of_nonneg_left ?_ h.le)⟩
 refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v=>?_
 change ‖iteratedFDeriv ℝ j Fu x v‖ ≤ _; refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>?_
 let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:panel n=> F) i
 have hu : iteratedFDeriv ℝ j Fu x v i= _ := congrArg (fun L: E [×j]→L[ℝ] _ => L v) (L.iteratedFDeriv_comp_left H (by exact_mod_cast hj)).symm
 rw [hu]; refine ((iteratedFDeriv ℝ j (fun x=> Fv x (t0 i)) x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun i=>‖iteratedFDeriv ℝ j (fun x=> Fv x (t0 i)) x‖) (fun i _=>norm_nonneg _) i.prop) (by positivity))
end
end YM.CF.VolumeRate
