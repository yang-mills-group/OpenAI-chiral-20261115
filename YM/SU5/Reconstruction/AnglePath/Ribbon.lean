import YM.SU5.Reconstruction.AnglePath.Lights
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
variable {P U:H.Op} {c s:ℝ}
local notation "Z"=> A.spread G p
local notation "K₀"=>G.bring P P
local notation "W"=>G.bring U (U*Mint P c)
include p
lemma procure {X₀:H.Op}{Y:K.Op}{D':D.Op}(a:G.l.comp Y=X₀.comp G.l)(b:(Z).comp Y=D'.comp Z) (q:Core A C): C.Pass X₀ D':= by
 apply (show Faces _ _ _ _ J C from q).pass; intro i; let v:= A.revenue G i; have he:= A.spread_ready G p C q (Y v); rw [show G.l (Y v)=X₀ (G.l v) from DFunLike.congr_fun a v,show Z (Y v)=D' (Z v) from DFunLike.congr_fun b v] at he; unfold v at he; rw [(A.revenue_funding G p i).1,A.spread_at] at he; exact he
lemma extends_projection (h:IsStarProjection P)(e:G.Pass P P): ∃ D':D.Op, IsStarProjection D' ∧ (D').comp Z=(Z).comp (G.bring P P):= by
 let L:=G.l; let R:=G.r; let u:=G.bring P P
 have hl(x:K): L (u x)=P (L x):= DFunLike.congr_fun ((G.sustain ..).1 e).1 x
 have hr(x:K): R (u x)=P (R x):= DFunLike.congr_fun ((G.sustain ..).1 e).2 x
 have hp(x:K): u (u x)=u x:= DFunLike.congr_fun (G.groupProj h h e).1.eq x
 have v(x y:K): inner ℂ (Z x) (Z (u y))=inner ℂ (Z (u x)) (Z y):=by
    simp only [A.spread_inner]; change inner ℂ (L x) (R (u y))= inner ℂ (L (u x)) (R y); rw [hl,hr,show P (L x)=P.adjoint (L x) from DFunLike.congr_fun h.2.star_eq.symm _,ContinuousLinearMap.adjoint_inner_left]
 have b(x:K):‖Z (u x)‖≤‖Z x‖:=by
    by_cases h:‖Z (u x)‖=0
    · rw [h]; exact norm_nonneg _
    apply le_of_mul_le_mul_left (a:=‖Z (u x)‖) _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
    calc
      _= ‖inner ℂ (Z (u x)) (Z (u x))‖ :=by rw [inner_self_eq_norm_sq_to_K,norm_pow]; change _=‖((‖Z (u x)‖:ℝ):ℂ)‖^2; simp [pow_two]
      _≤_ := by rw [←v,hp]; rw [mul_comm]; exact norm_inner_le_norm ..
 let Y:=((Z).comp u).toLinearMap.extendOfNorm ((Z).toLinearMap); have he(x:K):Y (Z x)=Z (u x):= LinearMap.extendOfNorm_eq (A.spread_dense G p) (⟨(1:ℝ), fun x=> show ‖Z (u x)‖≤1 * ‖Z x‖ from by rw [one_mul]; exact b x⟩) x
 refine ⟨Y, ⟨?_,?_⟩, ContinuousLinearMap.ext he⟩
 · change Y*Y=Y; apply dense_cancel Z (A.spread_dense G p); ext1 x; change Y (Y (Z x))= Y (Z x); rw [he,he,hp]
 change Y.adjoint=Y; apply dense_cancel Z (A.spread_dense G p); ext1 x; apply (A.spread_dense G p).eq_of_inner_right ℂ; intro m; change inner ℂ (Z m) (Y.adjoint (Z x))=inner ℂ (Z m) (Y (Z x)); rw [ContinuousLinearMap.adjoint_inner_right,he,he]; exact (v ..).symm
omit p
variable (h:ScalePass G P P U U c)(x:0<s)(y:s*s=c)
include p q h x y
lemma fundRibbon: ∃ (P':D.Op)(V:D.Op), C.ScalePass P P' U V s:=by
 obtain ⟨R,b,e⟩:= A.extends_projection G p h.lap h.dialog
 have hu: C.Pass P R:= A.procure G p C ((G.sustain ..).1 h.dialog).1 e.symm q
 let N:= Mint R s; let NI:= Mint R s⁻¹
 have sInv : NI*N=1 ∧ N*NI=1:=by unfold NI N; rw [Mint.fuse _ _ b,Mint.fuse _ _ b, mul_inv_cancel₀ x.ne',inv_mul_cancel₀ x.ne']; simp
 -- define v by extending Z via NI ZW or Z (W Mint(sinv)). want V comp N -> ... More direct NI ZW, prove commutation
 have z1(i:K): G.l (W i)= U (G.l i):=DFunLike.congr_fun ((G.sustain ..).1 h.given).1 i
 have z2(i:K): G.r (W i)= U ((Mint P c) (G.r i)):=DFunLike.congr_fun ((G.sustain ..).1 h.given).2 i
 have z3(i:K)(r:ℝ): Mint P r (G.r i)= G.r (Mint (G.bring P P) r i):=DFunLike.congr_fun (Mint.across ((G.sustain ..).1 h.dialog).2 r).symm i
 have z4(i:K)(r:ℝ): Z (Mint K₀ r i)= Mint R r (Z i):=DFunLike.congr_fun (Mint.across e.symm r) i
 let α₁:= Mint K₀ s; let α':=Mint K₀ s⁻¹
 have aInv : α'*α₁=1 ∧ α₁*α'=1:=by unfold α' α₁; rw [Mint.fuse _ _ (G.groupProj h.lap h.lap h.dialog), Mint.fuse _ _ (G.groupProj h.lap h.lap h.dialog), mul_inv_cancel₀ x.ne', inv_mul_cancel₀ x.ne']; simp
 let Y:=W*α'; have h1(i:K):Z (α₁ i)=N (Z i):=z4 i s
 have HN(i j:K):inner ℂ (Z (W i)) (Z (W j))=inner ℂ (Z i) (Z (Mint K₀ c j)):=by
    simp only [A.spread_inner,z1,z2,h.leftU.ordinary,z3]
 have hx(i j:K):inner ℂ (Z (W i)) (Z (W j))=inner ℂ (N (Z i)) (N (Z j)):=by
    rw [HN,z4,show Mint R c=N*N from ( (Mint.fuse _ _ b).trans (congrArg (Mint R) y)).symm]
    change inner ℂ _ (N (N (Z j)))=_; nth_rw 3 [← (show N.adjoint=N from Mint.star_rate _ b)]; rw [ContinuousLinearMap.adjoint_inner_left]; -- tune
 have iv(i j:K): inner ℂ (Z (Y i)) (Z (Y j))= inner ℂ (Z i) (Z j):= by
    change inner ℂ (Z (W (α' i))) (Z (W (α' j)))=_; rw [hx, ←h1,←h1,show α₁ (α' i)=i from DFunLike.congr_fun aInv.2 i, show α₁ (α' j)=j from DFunLike.congr_fun aInv.2 j]
 let V: D.Op:= ((Z).comp Y).toLinearMap.extendOfNorm ((Z).toLinearMap); have eq(i:K): V (Z i)=Z (Y i):= LinearMap.extendOfNorm_eq (A.spread_dense G p) (⟨(1:ℝ), fun i=> le_of_eq (show ‖Z (Y i)‖=1*‖Z i‖ from (by rw [one_mul,@norm_eq_sqrt_re_inner ℂ,@norm_eq_sqrt_re_inner ℂ,iv]))⟩) _
 have pv: star V*V=1:=by
    apply dense_cancel Z (A.spread_dense G p); ext1 i; apply (A.spread_dense G p).eq_of_inner_right ℂ; intro j; change inner ℂ (Z j) (V.adjoint (V (Z i)))=inner ℂ (Z j) (Z i); rw [ContinuousLinearMap.adjoint_inner_right,eq,eq,iv]
 have yComm:Commute Y K₀ := by
    unfold Y; exact ((G.lanes_comm h).symm).mul_left (Mint.mints _)
 have a1:Commute V R:= by
    change V*R=R*V; apply dense_cancel Z (A.spread_dense G p); ext1 i; have hr(i:K): R (Z i)=Z (K₀ i):= DFunLike.congr_fun e i; change V (R (Z i))= R (V (Z i)); rw [hr,eq,eq,hr]; exact congrArg Z (DFunLike.congr_fun yComm.eq i)
 have ys: Surjective Y:= fun i=> by obtain ⟨j,v⟩:= (G.routeU h).2 i; exact ⟨α₁ j, by change W (α' (α₁ j))=i; rw [show α' (α₁ j)=j from DFunLike.congr_fun aInv.1 j]; exact v⟩
 have H_V:Pays V:= ⟨pv,dense_cancel V ( (A.spread_dense G p).mono (by rintro t ⟨i,rfl⟩; obtain ⟨i,rfl⟩:=ys i; exact ⟨Z i,eq i⟩)) (show V*star V*V=1*V from by rw [mul_assoc,pv,mul_one,one_mul])⟩
 have vp:(V*N).comp Z=(Z).comp W:= by
    ext1 i; change V (N (Z i))=Z (W i); rw [←h1,eq]; change Z (W (α' (α₁ _)))=_; rw [show α' (α₁ i)=i from DFunLike.congr_fun aInv.1 i]
 refine ⟨R,V,h.lap,b,hu,x,h.leftU,H_V,h.lc,a1, A.procure G p C ((G.sustain ..).1 h.given).1 vp.symm q,?_⟩
 refine A.procure G p C ((G.sustain ..).1 h.wants).1 ?_ q
 -- v inverse at (Mint ...). need mate W^-
 let W':=G.bring (star U) (Mint P c⁻¹*star U); have wInv:W*W'=1:=by
    unfold W'; rw [← G.gather_mul h.given h.wants, mul_assoc,← mul_assoc _ (Mint P c⁻¹),Mint.fuse _ _ h.rap,mul_inv_cancel₀ h.pos.ne',Mint.at_base,one_mul,h.leftU.2,G.gather_one]
 ext1 i; have h: (NI * star V) * (V*N)=1:= by rw [←mul_assoc, mul_assoc NI,pv,mul_one,sInv.1]
 change Z (W' i)= (NI*star V) (Z i); calc
 _ = (NI*star V) ((V*N) (Z (W' i))):= DFunLike.congr_fun h.symm _ -- Tune one
 _ = _ := by rw [show (V*N) (Z (W' i))= Z (W (W' i)) from DFunLike.congr_fun vp (W' i),show W (W' i)=i from DFunLike.congr_fun wInv i]
end Organ
end YM.CrossedFrame.Cardio
