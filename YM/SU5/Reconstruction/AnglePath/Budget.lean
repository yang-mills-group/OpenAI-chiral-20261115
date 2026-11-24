import YM.SU5.Reconstruction.AnglePath.Spectrum
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

namespace Organ
variable [AddCommGroup X][Module ℂ X](A:Organ X H D)(G:Clasp K H H)(p:A.Pre G)(C:Clasp J H D)(q:A.Core C)
open Complex Multiplier Chirp
local notation "S"=> peel C.l
local notation "R"=> peel C.r
noncomputable def bill (f:X):J:= C.Left.symm (A.L f)+ C.Left.symm (A.R f)
local notation "B"=> A.bill C
include q in
lemma prepayments(f:X): C.Left.symm (A.L f)=peel C.l (A.budget C f) ∧ C.Right.symm (A.d f)=peel C.r (A.budget C f):= by
 obtain ⟨v,p⟩:=A.core_funding C q f; let z:= A.budget C f; rw [←v,←p,←left_done,←right_done,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.symm_apply_apply]; exact ⟨rfl,rfl⟩
include q in
lemma workout(f:X): C.angle (A.bill C f)=C.Left.symm (A.L f) ∧ (1-C.angle) (A.bill C f)= C.Left.symm (A.R f) ∧ (peel C.l * peel C.r) (A.bill C f)= C.Right.symm (A.d f):=by
 obtain ⟨a,b⟩:= prepayments A C q f
 let x:=B f; let v:=C.Left.symm (A.L f); let w:= C.Left.symm (A.R f); let z:=C.Right.symm (A.d f); let u:= A.budget C f
 have h1:S u=v:= a.symm; have h2:R u=z:= b.symm
 have e(x:J):R (S x)=S (R x):=DFunLike.congr_fun (peels C).eq.symm x
 have h3:S w=R z:= by
    apply ext_inner_right ℂ; intro x
    have p₀:= (show Faces A.L A.d A.R A.d J C from q).meets f x
    have hx : inner ℂ w (C.Left.symm (C.l x))=inner ℂ z (C.Right.symm (C.r x)):=by unfold w z; rw [LinearIsometryEquiv.inner_map_map,LinearIsometryEquiv.inner_map_map]; exact p₀
    have hv:S=(S).adjoint :=(IsSelfAdjoint.of_nonneg (positive_peel C.l)).symm; have hw:R=(R).adjoint:=(IsSelfAdjoint.of_nonneg (positive_peel C.r)).symm
    rw [hv,hw,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_inner_left]; rw[←left_done,←right_done,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.symm_apply_apply] at hx; exact hx
 have p1(x:J): S (S x)+R (R x)=x:= DFunLike.congr_fun C.registered x
 have hx:S x=u:=by unfold x bill; rw [map_add]; change S v+S w=u; rw [←h1,h3,←h2,p1]
 have p0:C.angle (B f)=v:=by change (C.l.adjoint.comp C.l) x = v; rw [←peel_sq]; change S (S x)=v; rw [hx,h1]
 refine ⟨p0,?_,?_⟩
 · change B f-C.angle (B f)=w; rw [p0]; unfold bill; change v+w-v=w; abel
 change S (R x)=z; rw [←e,hx,h2]
noncomputable def bond (z:ℂ)(f:X):H:= C.Left (spool C z (A.bill C f))
local notation "X₀"=> A.bond C
lemma bond_bound (z:ℂ)(p':z∈scroll)(f:X): ‖X₀ z f‖≤‖A.bill C f‖:=by rw [bond,LinearIsometryEquiv.norm_map]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((book C z p').fare zero_le_one (fun x=> oracle_cost p' _ (C.price x))))
lemma bond_full(f:X):ContinuousOn (fun z:ℂ=> bond A C z f) scroll:= LinearIsometryEquiv.continuous C.Left|>.comp_continuousOn (pathway_w C _)
lemma bond_inner(f:X): AnalyticOnNhd ℂ (fun z:ℂ=> bond A C z f) income:=fun x h=> C.Left.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _ |>.comp (f:=fun z=> spool C z (B f)) ((ContinuousLinearMap.apply ℂ J (B f)).analyticAt (spool C x) |>.comp (pathway C x h))
private lemma spool_on(z t:ℝ)(h:t∈ Ioo (0:ℝ) 1): oracle ((z:ℂ)*I) t= river z t * oracle 0 t:=by unfold oracle river sing; rw [←exp_add,Real.log_div (sub_pos.mpr h.2).ne' h.1.ne']; push_cast; ring_nf
private lemma spool_funds(z:ℝ): spool C ((z:ℂ)*I)=(C.Cabin z)* spool C 0:=by
 have h:=book C ((z:ℂ)*I) (by simp [scroll]); apply h.single; exact ((C.Cabin_reads z).times (book C 0 (by simp [scroll]))).agrees h.price (fun w=> (C.inOpen w).mono fun y hy=> (spool_on z _ hy).symm)
include q in
lemma bond_train(f:X): bond A C 0 f=A.L f ∧ bond A C (1/2) f=C.look.symm (A.d f) ∧ bond A C 1 f=A.R f ∧ ∀ z:ℝ,bond A C ((z:ℂ)*I) f=C.cLeft z (A.L f):=by
 obtain ⟨a,u,p⟩:= A.workout C q f; have he: bond A C 0 f=A.L f:=by unfold bond; rw [spool_first,a,LinearIsometryEquiv.apply_symm_apply];
 refine ⟨he,?_,?_,?_⟩
 · unfold bond look; rw [spool_mid,p]; rfl
 · unfold bond; rw [spool_last,u,LinearIsometryEquiv.apply_symm_apply]
 intro z; rw [←he]; unfold bond cLeft; rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,spool_funds]; rfl
end Organ
end YM.CrossedFrame.Cardio
