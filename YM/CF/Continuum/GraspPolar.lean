import YM.CF.Continuum.Needle
import YM.CF.Flare.Pyre

/-! # control near and away singular holonomies, uniform Male. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {B m N:Side}{j:ℕ}{x r:ℝ}{P:Op SpinIdx}{d:Candle}
lemma projector_norm_fact : ‖Aop‖=1:=by
 have he:= norm_entry (A:=Aop) 0 0; have hp:Aop (0:SpinIdx) (0:SpinIdx)=1:=by rw [Adef,←raising,cutM,Matrix.diagonal_apply_eq,if_pos (by decide)] -- tune
 exact (IsStarProjection.norm_le _ A_id).antisymm (by simpa [hp] using he)

def polarLift (P:Op SpinIdx)(d:ℝ) := d⁻¹ • (P*Aop)
def polarWork (P:Op SpinIdx)(d:ℝ):=laneP Aop 1 (polarLift P d)
local notation "W"=> polarLift P x
local notation "Qpay"=> polarWork P x

lemma polarClad (h:IsStarProjection P)(e:P.trace=Aop.trace)(p:Aop*P*Aop=x • Aop)(k:0<x): Clad P Aop 1 1 (polarLift P x) := by
 apply Flare.volta h A_id e.symm (by simp)
 · rw [polarLift,Matrix.mul_smul,←mul_assoc,h.1]
 · unfold polarLift; simp only [star_mul,star_smul,Matrix.smul_mul,Aadj,h.isSelfAdjoint.star_eq,star_trivial,mul_one,mul_assoc]
 · rw [polarLift,Matrix.smul_mul,mul_assoc,AOne]
 rw [mul_one,polarLift,Matrix.mul_smul,←mul_assoc,mul_assoc _ P P,h.1,p,inv_smul_smul₀ k.ne']
lemma polarSector (_p:Aop*P*Aop=x • Aop)(_k:0<x): Aop * Qpay=0 ∧ Qpay*Aop=Qpay := by
 unfold polarWork laneP polarLift; rw [mul_one]; constructor
 · rw [←mul_assoc,Porth A_id,zero_mul]
 rw [mul_assoc,Matrix.smul_mul,mul_assoc,AOne]
lemma polarMetric (h:IsStarProjection P)(p:Aop*P*Aop=x • Aop)(k:0<x): ‖Qpay‖^2+1=x⁻¹:=by
 have hu:Aop*W=Aop:=by unfold polarLift; rw [Matrix.mul_smul, ← mul_assoc,p,inv_smul_smul₀ k.ne']
 have he:Qpay=W-Aop:=by unfold polarWork laneP; rw [mul_one,sub_mul,one_mul,hu]
 have hp:star W * W= x⁻¹ • Aop:=by unfold polarLift; rw [star_smul,star_trivial,Matrix.smul_mul,star_mul,Aadj,h.2,Matrix.mul_smul, ←mul_assoc,mul_assoc _ P P, h.1,p, inv_smul_smul₀ k.ne']
 have hx: star Qpay* Qpay= (x⁻¹-1) • Aop:=by
    have he':star W * Aop=Aop:=by simpa only [star_mul,Aadj] using congrArg star hu
    rw [he,star_sub,Aadj, mul_sub,sub_mul, sub_mul,he',AOne,sub_self,hp,hu,sub_zero,sub_smul,one_smul]
 have hv:x≤1:=by
   have ht:‖P‖≤1:= IsStarProjection.norm_le _ h; have hh:= (norm_mul_le (Aop*P) Aop); rw [p,norm_smul, projector_norm_fact,Real.norm_of_nonneg k.le, mul_one,mul_one] at hh; apply hh.trans; exact (norm_mul_le ..).trans (by rw [projector_norm_fact,one_mul]; exact ht)
 have hh:‖Qpay‖^2= ‖star Qpay*Qpay‖:= by rw [sq]; exact (CStarRing.norm_star_mul_self ..).symm
 rw [hh,hx,norm_smul,projector_norm_fact,mul_one,Real.norm_of_nonneg (sub_nonneg.mpr ((one_le_inv₀ k).2 hv))]; ring

variable (M:Jill.Male)
local notation "F"=> field (needlesView N) j M
local notation "x" i:max => Kea.angle (needlesView N) i
local notation "L" p:max=> disk j M p
def tiltCharge(N:Side)(j:ℕ)(M:Jill.Male)(i:Stag N) := polarWork (field (needlesView N) j M i) (disk j M (Kea.angle (needlesView N) i))
lemma tiltLower(j:ℕ)(h:1 ≤ j): ∃ c C :ℝ,0<c ∧ 0<C ∧ ∀ (N:Side),Even N.val →∀ (M:Jill.Male)(s:Stag N),
    let w:= disk j M (Kea.angle (needlesView N) s); c*(N.val:ℝ)^(-18:ℤ)≤w ∧
    (s=tinyMode N s.2.1→ w ≤ C*(N.val:ℝ)^(-18:ℤ)) ∧(s≠tinyMode N s.2.1→ c*(N.val:ℝ)^(-2:ℤ)≤w):=by
  obtain ⟨c,C,p,h,Z⟩:=Jill.zip h; refine ⟨(c*Real.pi^2/16),(C*Real.pi^2),by positivity,by positivity,fun N g M s=>?_⟩; intro w; let X:= Kea.angle (needlesView N) s
  obtain ⟨u,v⟩:= Z M X (up_p (needlesView N) g s); refine ⟨le_trans ?_ u, fun z=> v.trans ?_, fun z=> le_trans ?_ u⟩; rotate_left -- small
  · unfold X; nth_rw 1 [z]; rw [tiny_value,jitter,pinch]; rw [show (-18:ℤ)=- (18:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast]; apply le_of_eq; field_simp -- simplify
  · have he:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤pinch N/4 from div_nonneg (pinch_pos _).le (by positivity)) (other_mode z) 2) p.le
    apply le_trans _ he; unfold pinch; rw [show (-2:ℤ)=-(2:ℕ) from rfl,_root_.zpow_neg, _root_.zpow_natCast]; apply le_of_eq; field_simp; ring
  have hv:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0≤pinch N*jitter N/4 by have he:=pinch_pos N; have hj:=(jitter_prop N).1; positivity) (every_mode s) 2) p.le; apply le_trans _ hv; unfold pinch jitter; rw [show (-18:ℤ)=- (18:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast]; apply le_of_eq; field_simp; ring
lemma tiltGap {k:Stag N}(p: 1 ≤ j)(e:Even N.val): 0< L (x k):=by obtain ⟨c,C,hc,h,X⟩:=tiltLower j p; exact lt_of_lt_of_le (by positivity) (X N e M k).1
lemma tiltClad (h:1 ≤ j)(e:Even N.val)(k:Stag N) : Clad (F k) Aop 1 1 (polarLift (F k) (L (x k))) := by obtain ⟨p,t,c,_⟩:= crestQ j M (needlesView N) e k; exact polarClad p t c (tiltGap M h e)

-- numeric uniform size estimates (all framed eras)
lemma tiltPulse(j:ℕ)(h:1≤j):∃ c C:ℝ,0<c∧0<C∧∀ N:Side,Even N.val →∀ (M:Jill.Male)(s:Stag N), ‖tiltCharge N j M s‖≤ C*N.val^9 ∧ (s≠tinyMode N s.2.1→ ‖tiltCharge N j M s‖≤C*N.val) ∧ (s=tinyMode N s.2.1→ c*N.val^9≤ ‖tiltCharge N j M s‖ +1):=by
 obtain ⟨c,C,hc,hC,X⟩:=tiltLower j h; refine ⟨(Real.sqrt (1/C)),Real.sqrt (1/c),by positivity,by positivity,fun N g M s=>?_⟩; let Q:= tiltCharge N j M s; let k:ℝ:=N.val; let w:=high_d M (needlesView N) s j; have hk:0<k:=nPos _; have hx:= X N g M s; have hp: 0<w:=tiltGap M h g; have he:= crestQ j M (needlesView N) g s; have hv: ‖Q‖^2+1=w⁻¹:= polarMetric he.1 he.2.2.1 hp
 let B:=Real.sqrt (1/c); have hh (v:ℝ)(p:0<v) (l: c * (v^2)⁻¹ ≤ w): ‖Q‖≤ B*v:=by
     refine (sq_le_sq₀ (norm_nonneg _) (by unfold B; positivity)).mp ?_; have he:= inv_le_inv₀ hp (show 0<c*(v^2)⁻¹ by positivity)|>.mpr l; rw [show (c*(v^2)⁻¹)⁻¹=(B*v)^2 from (by unfold B; rw [mul_pow,Real.sq_sqrt (by positivity)]; field_simp)] at he; linarith
 refine ⟨hh (k^9) (by positivity) ?_,fun p=>hh k hk ?_,?_⟩; rotate_left 2
 · intro p; have he: (C*(k^9)^ (-(2:ℤ)))⁻¹ ≤ w⁻¹:=inv_le_inv₀ (by positivity) hp |>.mpr (by rw [show (- (2:ℤ))=-(2:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast,←pow_mul]; have h:=hx.2.1 p; simp only [show (-18:ℤ)=-(18:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast] at h; exact h)
   change Real.sqrt (1/C)*k^9≤‖Q‖+1; refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
   rw [mul_pow,Real.sq_sqrt (by positivity)]; refine le_trans (le_trans (le_of_eq ?_) he) ?_; rw [show (- (2:ℤ))=-(2:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast]; field_simp
   nlinarith [norm_nonneg Q]
 · rw [←pow_mul]; have h:=hx.1; rw [show (-18:ℤ)=-(18:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast] at h; exact h
 have h:= hx.2.2 p; rw [show (-2:ℤ)=-(2:ℕ) from rfl,_root_.zpow_neg,_root_.zpow_natCast] at h; exact h
end YM.CF.Window
