import YM.SU5.Relativistic.Quintile
set_option autoImplicit false
noncomputable section
namespace YM.Signs
open Filter Function MeasureTheory Metric Set InnerProductSpace
open scoped Topology NNReal InnerProductSpace ComplexOrder
open CF.Buffered.Afterglow.Tower.Vacancy
variable {a:Axis}{H:Hilbert}(P:OS.Semigroup H a)(B:Rolls H)
variable (c:∀ t m, (B.wind t) * (P.E m) = (P.E m)*(B.wind t))
local notation "π"=>P.orth
local notation "σ"=>B.calm
noncomputable def finalProject:H.Op:= P.orth * B.calm
local notation "Rp"=> finalProject P B
include c
lemma equal_s(t:ℤ): B.wind t*π=π*B.wind t:=by
 ext1 v
 have hp:= P.emerges (B.wind t v); simp only [show ∀ s,P.E s (B.wind t v)=B.wind t (P.E s v) from fun s=>Eq.symm (congrArg (fun x:H.Op=> x v) (c t s))] at hp
 exact tendsto_nhds_unique ((B.wind t).continuous.continuousAt.tendsto.comp (P.emerges v)) hp
lemma meet (x:H):Rp x =σ (π x):= Eq.symm (congrArg (fun t:H.Op=> t x) (B.calm_commutes (fun i=> (equal_s P B c i).symm)).symm) -- tune
lemma final_fix(u:H): (Rp u)=u ↔ (∀ t,P.E t u=u)∧ (∀ m,B.wind m u=u):=by
 constructor
 · intro h; refine ⟨(P.fixed _).1 ?_, (B.calm_mem _).mp ?_⟩
   · rw [←h]; exact Submodule.starProjection_apply_mem ..
   rw [←h,meet P B c, B.calm_mem]; exact fun x=> B.projected ..
 rintro ⟨p,q⟩; rw [meet P B c,show P.orth u=u from Submodule.starProjection_eq_self_iff.mpr ((P.fixed _).2 p)]
 exact (B.calm_mem u).2 q
lemma paid(x y:H): inner ℂ (π x) (σ y)=inner ℂ (Rp x) (Rp y):=by
 -- ⟪πx,σy⟫=⟪πx,Rpy⟫. then etc
 have h:inner ℂ (π x) (σ y-π (σ y))=0:=by rw [←inner_conj_symm,Submodule.starProjection_inner_eq_zero _ _ (Submodule.starProjection_apply_mem _ _), map_zero]
 rw [inner_sub_right, sub_eq_zero] at h
 rw [h]; change inner ℂ (π x) (Rp y)= inner ℂ (Rp x) (Rp y); rw [meet P B c,meet P B c]
 apply sub_eq_zero.mp; rw [←inner_sub_left]; unfold Rolls.calm; apply Submodule.starProjection_inner_eq_zero; apply Submodule.starProjection_apply_mem
lemma final_self(x y:H): inner ℂ (Rp x) y=inner ℂ x (Rp y) :=by
 -- h_w access
 change inner ℂ ((π) (σ x)) y=inner ℂ x (Rp y); rw [meet P B c]; unfold OS.Semigroup.orth Rolls.calm
 -- self via known symmetric
 rw [Submodule.inner_starProjection_left_eq_right,Submodule.inner_starProjection_left_eq_right] -- tune
end YM.Signs
#print axioms YM.Signs.paid
