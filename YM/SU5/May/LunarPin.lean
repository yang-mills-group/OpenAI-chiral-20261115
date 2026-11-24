import YM.SU5.May.LunarEntry
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
-- L(k)=-i minA Γ k. frame
noncomputable def cliff (x:E4):Peb:= -𝕀 • zen (brushQ x)
lemma cliff_adj : star (cliff x)=cliff x:=by
 unfold cliff; rw [star_smul,zenStar]; simp [Complex.conj_I]; unfold physical; funext j; simp [brushQ,Fir.tmap] -- tune
lemma cliff_Γ : zen (brushQ x)=𝕀 • cliff x:=by unfold cliff; simp [smul_smul]
lemma cliff_add : cliff (x+y)=cliff x+cliff y:=by
 have he:brushQ (x+y)= _:= funext (show ∀ i:Axis, brushQ (x+y) i=(brushQ x+brushQ y) i from fun i=> by simp [brushQ,Fir.tmap]); unfold cliff; rw [he,zenP,smul_add]
lemma cliff_smul : cliff (b • x)= (b:ℂ) • cliff x:=by rw [cliff,cliff]; rw [show brushQ (b • x)=(b:ℂ) • brushQ x from funext (fun i=> by simp [brushQ,Fir.tmap]),zenS]; exact smul_comm ..
lemma cliff_neg : cliff (-x)= -cliff x:=by rw [← neg_one_smul ℝ x,cliff_smul,ofReal_neg,ofReal_one, neg_one_smul]
lemma cliff_sq : cliff x*cliff x=(‖x‖^2:ℝ) • (1:Op SpinIdx):=by
 have he:prodM (brushQ x) (brushQ x)= pass (brushQ x):=by simp [Window.Largo.pass,prodM,sq]; -- tune
 unfold cliff; rw [Matrix.smul_mul,Matrix.mul_smul,zenSq,he,spendQ]; simp only [smul_smul]; rw [← BZ.ofReal_action]; ring_nf; simp -- tune
lemma across : grading*cliff x= -(cliff x*grading):=by unfold cliff; rw [Matrix.mul_smul, Matrix.smul_mul, zenG, smul_neg]
lemma cliffA : Aop*cliff x=cliff x*minA:=by unfold cliff; rw [Matrix.mul_smul,Matrix.smul_mul,zenA]
lemma cliffB : minA*cliff x=cliff x*Aop:=by unfold cliff; rw [Matrix.mul_smul,Matrix.smul_mul, zenAA]
lemma anticomm (v:inner ℝ x y=0): cliff x*cliff y= -(cliff y*cliff x):=by
 let A:=cliff x; let B:=cliff y; have he:=cliff_sq (x+y); rw [cliff_add,norm_add_sq_real, v,mul_zero,add_zero,add_smul,mul_add,add_mul,add_mul,cliff_sq,cliff_sq] at he
 rw [show ‖x‖^2 • (1:Op SpinIdx)+_ + (_+_)= (‖x‖^2 • (1:Op SpinIdx)+‖y‖^2 • (1:Op SpinIdx))+(cliff x*cliff y+cliff y*cliff x) from (by abel)] at he; exact eq_neg_of_add_eq_zero_left ((add_eq_left.mp he)) -- names tune
lemma cliff_basis (k:Axis): cliff (YM.basis k)=gammaOp k:=by
 unfold cliff zen; rw [Finset.sum_eq_single k]; · simp [brushQ,Fir.tmap,YM.basis_inner,YM.basis_eq,smul_smul]
 · intro i hx h; simp [brushQ,Fir.tmap,YM.basis_eq,h];
 simp
open Mir Hygrometry
local notation "U"=> cliff (tilted P)
lemma tiltQ : cliff (tilted P)*cliff (tilted P)=1:=by rw [cliff_sq (tilted P),rulerL]; simp
lemma reel_eq : P.imageP = cliff (tilted P)*grading:=by
 unfold tilted; rw [cliff_smul, cliff_add, cliff_basis,cliff_basis, Matrix.smul_mul,add_mul,BZ.ofReal_action]; rfl
lemma rising (u: remains false v) : acts grading v=v:=by
 rw [ordA,act_sub,act_smul,show acts Aop v=v from u,act_one]; module
lemma sinking (u: remains true v): acts grading v=-v:=by rw [ordA,act_sub,act_smul,show acts Aop v=0 from u,act_one]; simp
lemma purse_u (u: remains false v) : remains true (acts (cliff x) v):=by rw [remains,← act_mul,cliffA,act_mul, minA,act_sub,act_one, show acts Aop v=v from u,sub_self,map_zero]; rfl -- tune
lemma purse_d (u: remains true v): remains false (acts (cliff x) v):=by rw [remains,← act_mul,cliffA,act_mul,minA,act_sub,act_one,show acts Aop v=0 from u, sub_zero]; rfl
-- statements avoid full? let's use matrices. lashUPP, lashDN
lemma lash_alt(z:E4): zen (shaft x z b)= 𝕀 • cliff x + (b:ℂ) • cliff z:=by
 unfold shaft; simp only [sub_eq_add_neg, ←neg_smul, zenP, zenS,cliff_Γ]; simp [smul_smul,mul_comm 𝕀]; ring_nf; simp -- tune
local notation "H+" K:max z:max=> ((z:ℂ) • (1:Op SpinIdx)+ 𝕀 • ((U)*cliff K))
private lemma A_grade : grading*Aop=Aop:=by rw [ordA,sub_mul,Matrix.smul_mul,one_mul,AOne]; module
private lemma grade_A : Aop*grading=Aop:=by rw [ordA,mul_sub,Matrix.mul_smul,mul_one,AOne]; module
private lemma grade_B : minA*grading= -minA:=by unfold minA; rw [sub_mul,one_mul,grade_A,ordA]; module
lemma upward : -(star P.imageP * lash (shaft p (tilted P) b))=(H+ p b)*Aop:=by
 let X:= tilted P; unfold lash; rw [reel_eq,star_mul,gradingAdj.star_eq,cliff_adj,mul_neg,neg_neg,mul_assoc grading,← mul_assoc (cliff _),←cliffA]; rw [←mul_assoc grading,← mul_assoc grading,A_grade]; -- tune
 rw [lash_alt]; rw [mul_add,Matrix.mul_smul,Matrix.mul_smul]; rw [mul_assoc Aop, mul_assoc Aop, tiltQ,mul_one]; rw [add_mul,Matrix.smul_mul,Matrix.smul_mul]; rw [one_mul]; rw [←mul_assoc, cliffA,mul_assoc _ minA,cliffB,←mul_assoc]; exact add_comm ..; -- likely this part wrong
lemma downward (u:inner ℝ (tilted P) p=0): lash (shaft p (tilted P) b)*P.imageP=(H+ (-p) b)*minA:=by
 rw [lash,reel_eq,neg_mul,lash_alt,← mul_assoc (_*_) (cliff _),mul_add,add_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul]; -- inspect
 rw [mul_assoc minA (cliff _), mul_assoc minA (cliff _), anticomm p (tilted P) (by rwa [real_inner_comm]), tiltQ]; -- order
 rw [mul_neg,mul_one, ←mul_assoc,cliffB,mul_assoc _ Aop,cliffA,← mul_assoc, add_mul]; simp only [Matrix.smul_mul,smul_neg,neg_mul,mul_assoc, grade_B, cliff_neg,mul_neg,add_mul,one_mul,neg_neg]; module
#print axioms reel_eq
end YM.CF.May.Lunar
