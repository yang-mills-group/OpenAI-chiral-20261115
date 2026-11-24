import YM.SU5.Reconstruction.AnglePath.Orbit
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

open Multiplier Chirp OS Semigroup Boundary Probe Picket
variable {a b:Axis} (C:Clasp K H H)(F:H≃ₗᵢ[ℂ] D)
local notation "P"=> F.toContinuousLinearEquiv.toContinuousLinearMap
private lemma accounts : ((P).comp C.r).adjoint.comp ((P).comp C.r) = C.r.adjoint.comp C.r:=by ext1 x; apply ext_inner_left ℂ; intro y; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]; exact LinearIsometryEquiv.inner_map_map ..
noncomputable def Shank: Clasp K H D where
 l:=C.l
 r:= (P).comp C.r
 j:=C.j
 k:= F.injective.comp C.k
 p:= C.p
 q:= F.surjective.denseRange.comp C.q F.continuous
 frame:= by rw[accounts]; exact C.frame
local notation "W" => Shank C F
lemma saves (u:H)(v:D): (W).Latch u v ↔ C.Latch u (F.symm v):=by
 constructor
 · rintro ⟨x,p,q⟩; refine ⟨x,p,?_⟩; rw [← q]; exact (F.symm_apply_apply _).symm
 rintro ⟨x,v,q⟩; exact ⟨x,v,F.eq_symm_apply.mp q⟩
lemma sustainX (X:H.Op)(Y:D.Op): (W).Pass X Y ↔ C.Pass X (F.symm.conjStarAlgEquiv Y):= by
 unfold Pass; apply forall_congr'; intro x; rw [saves C F, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; rfl
-- $W.$ notation field captured? tune
variable (r:b≠a)(S:OS.Semigroup H a)(Q:OS.Semigroup D b)(p:Paces b S)(q:Paces a Q) (h:∀ x:E4,F.conjStarAlgEquiv (Picket.trans S x)=Picket.trans Q (quarter a b x))
local notation "V₀" => Picket.trans S
local notation "U₀" => Picket.trans Q
include r h
private lemma ahead (x:E4) : (P).comp (V₀ x)=(Picket.trans Q (quarter a b x)).comp P:=by rw [←h]; ext1 y; simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; change F ((V₀ x) y)= F (V₀ x (F.symm (F y))); rw [LinearIsometryEquiv.symm_apply_apply]
private lemma ties_leads (A:H.Op)(B:D.Op)(v:(P).comp A=B.comp P):F.symm.conjStarAlgEquiv B=A:=by ext1 x; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]; change F.symm (B (F x))=_; apply F.injective; rw[LinearIsometryEquiv.apply_symm_apply]; exact DFunLike.congr_fun v.symm x -- unused r,h
lemma backGrants(ξ:Picket.Behind S Q W) (x:E4)(v:x a=0)(w:x b=0): C.Pass (Picket.trans S x) (Picket.trans S x):=by
 have p:quarter a b x=x:=by
    obtain ⟨p,e,f⟩:=quarter_gear r x; ext1 i; by_cases q:i=a; · subst i; rw [e,v,w,neg_zero]
    by_cases h:i=b; · subst i; rw[p,v,w]
    exact f i q h
 have h' := ahead _ r S Q h x; rw [p] at h'; have hx:=(sustainX C F (V₀ x) (U₀ x)).1 (ξ x v w); rwa [ties_leads F r S Q h _ _ h'] at hx -- tune include
omit h in
private lemma quarterHead(t e:ℝ) : Picket.quarter a b (t • head a b e)=t • head b a (-e):= by
 ext1 i; obtain ⟨p,v,t'⟩:= quarter_gear r (t • _); by_cases h:i=a; · subst i; rw [v]; simp [head,r,r.symm] -- simp `head`
 by_cases p1:i=b; · subst i; rw [p]; simp [head,r,r.symm]
 rw [t' i h p1]; simp [head,h,p1]
include p q
lemma photons (β:Picket.Beam r S Q W)(e:ℝ)(g:e=1∨e=-1): Tide C (ticket a b e) (ticket a b e) e S.ℚmeasure S.ℚmeasure:=by
 let L:=ticket a b e; let M:=ticket b a (-e)
 let T:=S.ℚmeasure; let V:=Q.ℚmeasure; let ζ:=sail (-e)
 have A(f:ℝ→ℂ)(z:Tag f):(P).comp (order T (f ∘ L))=(order V (f ∘ M)).comp P:= by
    refine ballot _ _ _ _ _ (ticket_cont ..|>.measurable) (ticket_cont ..|>.measurable) ?_ f z
    intro i; unfold T V; rw [shift b e _ S p g,shift a (-e) _ Q q (by rcases g with g|g <;> simp [g])]; rw [ahead F r S Q h,quarterHead r i e] -- tune
 intro x y; let f (u:ℝ):= Complex.exp (-ζ*x*(max (0:ℝ) u:ℝ))
 have hp: Tag f:= by
    refine ⟨by unfold f; fun_prop,1,zero_le_one,fun t=>?_⟩; unfold f ζ; rw [Complex.norm_exp,Real.exp_le_one_iff]; simp only [Complex.mul_re,Complex.neg_re, Complex.ofReal_im,mul_zero,sub_zero,Complex.ofReal_re]; unfold sail; simp; exact mul_nonneg y.le (le_max_left ..)
 let Z:=order V (slopeRay ζ M x); have T':(W).Pass (order T (slopeRay (sail e) L x)) Z:= crosses_at r _ _ W _ g p q β x y
 have X':(P).comp (order T (slopeRay ζ L x))= Z.comp P:=by
    rw [show slopeRay ζ L x = f ∘ L from (by funext i; unfold comp slopeRay f; rw [max_eq_right (Picket.positive b e i)])]; unfold Z; rw [show slopeRay ζ M x= f∘M from (by funext i; unfold comp slopeRay f; rw [max_eq_right (Picket.positive a (-e) i)])]; exact A f hp
 have u:=(sustainX C F _ Z).1 T'; rwa [ties_leads F r S Q h _ _ X'] at u
end YM.CrossedFrame.Cardio
