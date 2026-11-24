import YM.SU5.Reconstruction.Trap.Mint
/-!
# Halfway calculation
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K H D:Hilbert}
lemma Pays.ordinary {U:K.Op}(p:Pays U)(x y:K) : inner ℂ (U x) (U y)=inner ℂ x y:= ContinuousLinearMap.inner_map_map_of_mem_unitary p x y -- tune namespace
lemma Pays.usingEquiv (s:K≃ₗᵢ[ℂ]K): Pays s.toContinuousLinearEquiv.toContinuousLinearMap:= by
  let U:=s.toContinuousLinearEquiv.toContinuousLinearMap; change Pays U
  have ht(x:K): star U x=s.symm x := DFunLike.congr_fun (LinearIsometryEquiv.adjoint_eq_symm s) x
  constructor
  · ext1 x; change star U (s x)=x; rw [ht,s.symm_apply_apply]
  ext1 x; change s (star U x)=x; rw [ht,s.apply_symm_apply]
namespace Mint
variable {l : K→L[ℂ]H} {P : H.Op}{Q:K.Op} (e:l.comp Q=P.comp l)
include e
lemma across (x:ℝ) : l.comp (Mint Q x)=(Mint P x).comp l:= by
 unfold Mint; rw [ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul,e,ContinuousLinearMap.add_comp,ContinuousLinearMap.sub_comp,ContinuousLinearMap.smul_comp]; ext1; rfl
end Mint
section square
variable {W Y A B:K.Op}(p:Pays Y)(v:0≤A)(b:0≤ B)
include p v in
private lemma pulled_sqrt : CFC.sqrt (star Y*A*Y)=star Y*CFC.sqrt A*Y:= by
 rw [CFC.sqrt_unique _ (star_left_conjugate_nonneg (CFC.sqrt_nonneg A) _)] -- order
 simp_rw [mul_assoc]
 rw [← mul_assoc Y, p.2,one_mul,←mul_assoc (CFC.sqrt A), CFC.sqrt_mul_sqrt_self A v]
-- e=text: if star W A W=B, W^*W commutes B, cancel peel W to get relation on unsquared A via Y
include v b p in
lemma torque (i:Injective W)(u:W=Y*peel W)(e:star W*A*W=B)(h: Commute B (W.adjoint.comp W)) : Commute (star Y*A*Y) (peel W) ∧ CFC.sqrt A * W=Y*CFC.sqrt B:= by
 let x:=CFC.sqrt A; let a:=star Y*A*Y; let S:=CFC.sqrt a; let r:= peel W
 have hh: Commute B r := (rootComm h.symm).symm
 have hz: star r = r:= IsSelfAdjoint.of_nonneg (positive_peel _)
 have hu: r*a*r=B:= by
   rw [u,star_mul,hz] at e
   simpa only [r,a,mul_assoc] using e
 have w : Commute r a:= by
   have ht : r*(r*a)*r=r*(a*r)*r:=calc
     _ = r*(r*a*r) := by simp only [mul_assoc]
     _ = (r*a*r)*r := by nth_rw 1 [hu]; rw [hh.eq.symm, hu]
     _ = _ := by simp only [mul_assoc]
   exact strict_cancel r (peel_inj W i) (dense_cancel r (peel_dense W i) ht) -- tune comp r occurrences
 -- separate
 have k: Commute S r:= rootComm w.symm
 have hs: CFC.sqrt B=S*r:=CFC.sqrt_unique (by
    nth_rw 1 [k.eq]; rw [mul_assoc, ←mul_assoc S, show S*S=a from CFC.sqrt_mul_sqrt_self a (star_left_conjugate_nonneg v Y), ←mul_assoc]; -- tune
    exact hu) (Commute.mul_nonneg (CFC.sqrt_nonneg a) (positive_peel _) k)
 refine ⟨w.symm,?_⟩; unfold S a at hs; rw [hs,pulled_sqrt p v]
 nth_rw 1 [u]; simp_rw [mul_assoc]; rw [← mul_assoc Y,p.2,one_mul]
end square
namespace Clasp
variable (C:Clasp K H D)
variable {P:H.Op}{Q:D.Op}{U:H.Op}{V:D.Op}{c:ℝ}
local notation "W"=> C.bring U (V*Mint Q c)
local notation "A" => C.angle
local notation "S"=> (peel W)
local notation "Z"=> C.bring P Q
local notation "Y"=> (Mint (C.bring P Q) c)
local notation "D'" => (1-C.angle)
local notation "L" => C.Left.toContinuousLinearEquiv.toContinuousLinearMap
local notation "R" => C.Right.toContinuousLinearEquiv.toContinuousLinearMap
variable (h:ScalePass C P Q U V c)
noncomputable def halfway (h:ScalePass C P Q U V c) : K.Op:=
  (get_polar _ (C.routeU h).1 (C.routeU h).2.denseRange).choose.toContinuousLinearEquiv.toContinuousLinearMap
local notation "Y₀" => halfway C h
local notation "r" => peel C.l
local notation "s" => peel C.r
include h
lemma mark_half : C.bring U (V* Mint Q c)=halfway C h * peel (C.bring U (V* Mint Q c)) := ContinuousLinearMap.ext (fun x=> ((get_polar _ (C.routeU h).1 (C.routeU h).2.denseRange).choose_spec x).symm)
lemma paysHalf : Pays (halfway C h):= Pays.usingEquiv _
-- weights of W exact both projections
lemma hold_left : star W * A * W=A:= by
 let U₀ : K→L[ℂ]K:=W; have hp(x:K): C.l (W x)=U (C.l x):= DFunLike.congr_fun ((C.sustain ..).1 h.given).1 x
 ext1 x; apply ext_inner_left ℂ; intro u; change inner ℂ u (U₀.adjoint (C.l.adjoint (C.l (W x))))= inner ℂ u (C.l.adjoint (C.l x)); unfold U₀; simp_rw [ContinuousLinearMap.adjoint_inner_right,hp,h.leftU.ordinary]
lemma meet_right : star W * D' * W=Y*D'*Y:= by
 have k : C.r.comp Y=(Mint Q c).comp C.r:= Mint.across ((C.sustain ..).1 h.dialog).2 c
 have hp(x:K): C.r (W x)=V (C.r (Y x)):= by
   rw [show C.r (Y x) = Mint Q c (C.r x) from DFunLike.congr_fun k x]; exact DFunLike.congr_fun ((C.sustain ..).1 h.given).2 x
 rw [← C.complement]; nth_rw 1 [← Mint.star_rate c (C.groupProj h.lap h.rap h.dialog)] -- choose Y
 ext1 x; apply ext_inner_left ℂ; intro u; change inner ℂ u ((W).adjoint (C.r.adjoint (C.r (W x)))) = inner ℂ u ((Y).adjoint (C.r.adjoint (C.r (Y x))))
 simp_rw [ContinuousLinearMap.adjoint_inner_right,hp,h.rightU.ordinary]
lemma W_square : (W).adjoint.comp W=A+Y*D'* Y:= by
 change star W * W= _
 calc
   _ = star W * A * W + star W * D' * W := by noncomm_ring
   _ = _ := by rw [hold_left C h,meet_right C h]
lemma WZ_comm : Commute (C.bring P Q) (peel W):= by
 apply Commute.symm; apply rootComm; rw [W_square C h]; have ha: Commute A Z:= (capProj C h.lap h.rap h.dialog).1
 apply ha.add_left; exact (((Mint.mints c).mul_left ((Commute.one_left Z).sub_left ha)).mul_left (Mint.mints c))
lemma yrate : Commute Y A:= Mint.full (capProj C h.lap h.rap h.dialog).1.symm _
lemma Wr_comm : Commute C.angle ((W).adjoint.comp W) :=by
 rw [W_square C h]; exact Commute.symm ((Commute.refl _).add_left (((C.yrate h).mul_left ((Commute.one_left _).sub_left (Commute.refl _))).mul_left (C.yrate h)))
lemma unit_arc : Commute (C.bring P Q) (halfway C h):=by
 refine dense_cancel S (peel_dense W (C.routeU h).1) (f:=Z*Y₀) (g:=Y₀*Z) ?_
 change Z*Y₀*S=Y₀*Z*S; rw [mul_assoc,←C.mark_half h,(C.lanes_comm h).eq, mul_assoc, (C.WZ_comm h).eq,← mul_assoc,←C.mark_half h]
lemma pointing : star (halfway C h)* C.angle * halfway C h * ((W).adjoint.comp W) = C.angle:= by
 let T:= star Y₀*A*Y₀
 have ht: Commute (star Y₀*A*Y₀) (peel W):=(torque (C.paysHalf h) C.angle_pos C.angle_pos (C.routeU h).1 (C.mark_half h) (C.hold_left h) (C.Wr_comm h)).1
 change T * (_)=_
 rw [show (W).adjoint.comp W = S*S from (peel_sq ..).symm, ← mul_assoc,ht.eq]
 nth_rw 1 [← (show star S=S from IsSelfAdjoint.of_nonneg (positive_peel _))]
 rw [←mul_assoc, ←mul_assoc, ←star_mul,← C.mark_half h, mul_assoc _ Y₀ _,←C.mark_half h]; exact C.hold_left h
lemma halftime : (L).comp Y₀=U.comp L ∧ (R).comp Y₀= V.comp R:=by
 have hu: r*W=Y₀*r:=(torque (C.paysHalf h) C.angle_pos C.angle_pos (C.routeU h).1 (C.mark_half h) (C.hold_left h) (C.Wr_comm h)).2
 have he:= (C.sustain ..).1 h.given
 constructor
 · apply dense_cancel r (peel_dense C.l C.j)
   ext1 x; change C.Left (Y₀ (r x))=U (C.Left (r x)); rw [show Y₀ (r x)=r (W x) from DFunLike.congr_fun hu.symm x,C.left_done, C.left_done]; exact DFunLike.congr_fun he.1 x
 have hm: 0≤ Y:= Mint.award (C.groupProj h.lap h.rap h.dialog) _ h.pos.le -- tune order
 have hd:0≤ D':= sub_nonneg.mpr C.angle_le
 have hs':0≤ Y*D'*Y:= by nth_rw 1 [←(show star Y=Y from IsSelfAdjoint.of_nonneg hm)]; exact star_left_conjugate_nonneg hd _
 have hk: Commute (Y*D'*Y) ((W).adjoint.comp W):= by
   rw [W_square C h]; exact (((C.yrate h|>.mul_left ((Commute.one_left _).sub_left (Commute.refl _))).mul_left (C.yrate h)).add_right (Commute.refl _))
 have hv:= (torque (C.paysHalf h) hd hs' (C.routeU h).1 (C.mark_half h) (C.meet_right h) hk).2
 have hs: CFC.sqrt D'=s:=C.complement.symm ▸ rfl -- tune orientation
 have hp: s*s= D':= (peel_sq C.r).trans C.complement
 have ha: Commute s Y := by rw [←hs]; apply rootComm; exact (Commute.one_left _).sub_left (C.yrate h).symm
 have hb: CFC.sqrt (Y*D'*Y)=s*Y:= CFC.sqrt_unique (by nth_rw 1 [ha.eq]; rw [mul_assoc,←mul_assoc s,hp,mul_assoc]) (Commute.mul_nonneg (positive_peel _) hm ha)
 rw [hs,hb] at hv
 have key(x:K): (R) (Y₀ (s (Y x)))= V ((R) (s (Y x))):= by
   have hp (x:K) : C.r (Y x)= Mint Q c (C.r x) := DFunLike.congr_fun (Mint.across ((C.sustain P Q).1 h.dialog).2 c) x
   change C.Right (Y₀ (s (Y x)))= V (C.Right (s (Y x)))
   rw [show Y₀ (s (Y x))=s (W x) from DFunLike.congr_fun hv.symm x, C.right_done,C.right_done,hp]; exact DFunLike.congr_fun he.2 x
 have t:Surjective Y:= fun x=>
   ⟨Mint Z c⁻¹ x, DFunLike.congr_fun (show Y*Mint Z c⁻¹=1 by rw [Mint.fuse _ _ (C.groupProj h.lap h.rap h.dialog),mul_inv_cancel₀ h.pos.ne', Mint.at_base]) x⟩
 apply dense_cancel s (peel_dense C.r C.k); ext1 x; obtain ⟨x,rfl⟩:= t x; exact key _
end Clasp
end YM.CrossedFrame
