import YM.SU5.May.LunarPin
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
attribute [local instance] opCStarAlgebra
variable (N:Side)(P:Ramp)(p q:E4)(i:Title P)(x y:E4) (b:ℝ) (v w:Ket SpinIdx)
local notation "𝕀" => Complex.I
local notation "θ"=> tilted P
noncomputable def visor (p:E4):= ‖p‖⁻¹ • p
lemma vis_neg (p:E4) : visor (-p)= -visor p:=by unfold visor; rw [norm_neg,smul_neg]
lemma vis_one (w:p≠0): ‖visor p‖=1:=by unfold visor; rw [norm_smul, Real.norm_of_nonneg (by positivity),inv_mul_cancel₀ (norm_ne_zero_iff.mpr w)] -- tune
lemma vis_smul (b:ℝ)(t:0<b): visor (b • p)= visor p:=by unfold visor; rw [norm_smul,Real.norm_of_nonneg t.le,smul_smul]; field_simp
lemma visor_earn (w:p≠0) : ‖p‖ • visor p=p:=by unfold visor; rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr w), one_smul]
noncomputable def seamA(P:Ramp)(p:E4): Peb:= 𝕀 • (cliff (tilted P)*cliff (visor p))
lemma seam_neg : seamA P (-p) = -seamA P p:=by unfold seamA; rw [vis_neg,cliff_neg,mul_neg,smul_neg]
lemma seam_d(b:ℝ)(h:0<b): seamA P (b • p)= seamA P p:=by rw [seamA,vis_smul _ _ h]; rfl
local notation "Z"=>cliff (tilted P)
local notation "U"=>cliff (visor p)
local notation "H" => seamA P p
variable (μ:inner ℝ (tilted P) p=0)(h:p≠0)
include μ
lemma seam_adj : star (seamA P p)=seamA P p:=by unfold seamA; rw [star_smul,star_mul,cliff_adj,cliff_adj,anticomm (visor p) (tilted P) (by rw [real_inner_comm,visor,real_inner_smul_right,μ,mul_zero]),show star 𝕀= -𝕀 from Complex.conj_I]; simp
include h
lemma seam_sq : (seamA P p)*(seamA P p)=1:=by
 have hp : U*U=1:=by rw [cliff_sq, vis_one p h]; simp
 unfold seamA; rw [Matrix.smul_mul, Matrix.mul_smul, mul_assoc,←mul_assoc (cliff (visor p)),anticomm (visor p) (tilted P) (by rw [real_inner_comm,visor,real_inner_smul_right,μ,mul_zero]),neg_mul,mul_assoc Z _ _,hp,mul_one,mul_neg,tiltQ, smul_smul]; simp
noncomputable def hymnP(P:Ramp)(p:E4): Op SpinIdx:= 1+seamA P p
local notation "Q" => hymnP P p
lemma hymn_adj : star (hymnP P p)= hymnP P p:=by unfold hymnP; rw [star_add,star_one,seam_adj P p μ]
lemma range_cert : star (hymnP P p)*hymnP P p=(2:ℂ) • hymnP P p:=by rw [hymn_adj P p μ h]; unfold hymnP; rw [add_mul,one_mul,mul_add,mul_one,seam_sq P p μ h]; module
lemma hunt : ‖acts (hymnP P p) v‖≤2*‖v‖:=by
 let V:UNI SpinIdx:=⟨H,⟨(by rw [seam_adj P p μ,seam_sq P p μ h]),(by rw [seam_adj P p μ,seam_sq P p μ h])⟩⟩; -- order check
 unfold hymnP; rw [act_add,act_one]; exact (norm_add_le ..).trans_eq (by rw [show ‖acts (H) v‖= _ from act_unit_norm V v]; ring)
lemma horizon : inner ℂ v (acts (hymnP P p) w)=(1/2:ℂ)*inner ℂ (acts (hymnP P p) v) (acts (hymnP P p) w):=by
 -- orientation locale
 nth_rw 2 [← hymn_adj P p μ h]; rw [act_inner (Q) v]
 have he:= range_cert P p μ h; rw [hymn_adj P p μ h] at he; rw [←act_mul, he,act_smul, inner_smul_right]; ring
omit μ
open Hygrometry
lemma earlier : (‖p‖:ℂ) • hymnP P p=(‖p‖:ℂ) • (1: Peb)+ 𝕀 • ((Z)*cliff p):=by
 unfold hymnP seamA; rw [smul_add]; congr 1; rw [smul_comm (_:ℂ),← Matrix.mul_smul,←cliff_smul,visor_earn p h] -- tune
lemma latter : -(‖p‖:ℂ) • (1:Peb)+𝕀 • ((Z)*cliff p)= -(‖p‖:ℂ) • hymnP P (-p):=by rw [neg_smul _ (hymnP P (-p))]; nth_rw 2 [←norm_neg p]; rw [earlier P (-p) (neg_ne_zero.mpr h),norm_neg,cliff_neg]; rw [mul_neg]; module -- simp mul
-- pay b general. define pier τ tank for up and down.Swap. Spin left ray coefficients. Support $k`
def warp (b:Bool)(p:E4):=if b then -p else p
lemma warp_size (B:Bool): ‖warp B p‖= ‖p‖:=by cases B <;> simp [warp]
include μ
lemma warp_cross (B:Bool): inner ℝ (tilted P) (warp B p)=0:=by cases B <;> simp [warp,μ]
lemma warp_hired(B:Bool): warp B p≠ 0:= by cases B <;> simp [warp,h]
def chargeAxis(P:Ramp)(b:Bool)(S:Peb): Peb:= if b then S*P.imageP else -(star P.imageP*S)
lemma chargeCost (B:Bool): chargeAxis P B (lash (shaft p (tilted P) b))=((b:ℂ) • (1:Peb)+𝕀 • ((Z)*cliff (warp B p))) * (if B then minA else Aop):=by
 cases B; exact upward P p b; exact downward P p b μ
lemma ocean_p (B:Bool) : chargeAxis P B (lash (shaft p (tilted P) ‖p‖)) = ((‖p‖:ℂ) • (hymnP P (warp B p))) * (if B then minA else Aop):=by rw [chargeCost P p _ μ h,←warp_size p h B,earlier P _ (warp_hired P p μ h B)] -- tune arguments
lemma ocean_n (B:Bool) : chargeAxis P B (lash (shaft p (tilted P) (-‖p‖))) = (-(‖p‖:ℂ) • hymnP P (-warp B p))* (if B then minA else Aop):=by rw [chargeCost P p _ μ h,ofReal_neg,←warp_size p h B, latter P _ (warp_hired P p μ h B)]
omit μ h
lemma charge_s (B:Bool)(c:ℂ)(A:Peb): chargeAxis P B (c • A)=c • chargeAxis P B A:=by cases B <;> simp only [chargeAxis,Bool.false_eq_true,if_false,if_true,Matrix.mul_smul,Matrix.smul_mul,smul_neg]
lemma charge_q (B:Bool)(A A':Peb): chargeAxis P B (A+A')=chargeAxis P B A + chargeAxis P B A':=by cases B <;> simp [chargeAxis,mul_add,add_mul] <;> abel
noncomputable def asker (P:Ramp)(B:Bool): Momentum→L[ℂ] Peb:=LinearMap.toContinuousLinearMap ⟨⟨chargeAxis P B ∘ lash,fun _ _=> by unfold Function.comp; rw [lash_a,charge_q]⟩,fun _ _=> by dsimp only [Function.comp, RingHom.id_apply]; rw [lash_s, charge_s]⟩ -- rfl tune
#print axioms ocean_p
#print axioms horizon
end YM.CF.May.Lunar
