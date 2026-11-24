import Crape.Sewn
import Crape.Adjust
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Py.Dyad Keeping
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X] (L0:Side)(C D:ℕ→ℕ→ℝ)(F j:ℕ)(t:F ≤ j)(p:∀ s,F ≤ s → Bills F (s+1) s L0 (C s) (D s))
local notation "H"=>gainCost L0
local notation "Q"=>ThinGauge.boost (Xη L0)
variable(x:ℕ→X)(Y:ℝ)(tY:0<Y)
-- preC norm positive.
include p t tY
lemma coatLemma(K₀:∀ᶠ s:ℕ in atTop, ‖((C s s*(Q^(s-j)*revenue L0 (C s) (D s) s j):ℝ):ℂ) • x (s+1)+ ((-(Q^(s-j)):ℝ):ℂ) • x s‖ ≤ 2^s*Y) :
 CauchySeq (fun i=> ((basket L0 C D F i:ℝ):ℂ) • x i):=by
 let D0:= (2*H)^(j-F)*2^j
 let Y':=2*D0*Y*16^j+64^j
 have ht:=gainCost_pos L0
 apply excur _ Y' (by unfold Y' D0; positivity)
 filter_upwards [eventually_ge_atTop j,K₀] with i q g
 let b:= C i i; let a:= revenue L0 (C i) (D i) i F; let a':= revenue L0 (C i) (D i) i j; let d:= i-j; let B:=basket L0 C D F i
 have h:= boundsT L0 C D F p le_rfl (t.trans q); have h':=boundsT L0 C D F p t q
 change 3/4≤a ∧ a≤ 5/4 at h; change 3/4 ≤a'∧ a'≤5/4 at h'
 have hp:0<a':=by linarith
 have hp':0<a:=by linarith
 have hb:0<Q^d:=pow_pos (boostP _) _
 have hi:‖ ((b*a':ℝ):ℂ) • x (i+1)-x i‖≤ 2^i*Y/(Q^d):=by
    rw [le_div_iff₀ hb]; calc
     _ = ‖((Q^d:ℝ):ℂ) • ((((b*a':ℝ):ℂ) • x (i+1))-x i)‖:= (by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb,mul_comm])
     _ ≤ _:=by rw [smul_sub,←mul_smul,QmulEq,sub_eq_add_neg,←neg_smul,←Complex.ofReal_neg]; exact g
 have hl':‖((a/a':ℝ):ℂ)‖≤2:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hp' hp),div_le_iff₀ hp]; linarith
 obtain ⟨hm,e⟩:=basket_price L0 C D F p (t.trans q)
 let k:=2*H
 have hS:‖((a/a'-1:ℝ):ℂ)‖ ≤64⁻¹^d:=by
    have e₂:=revenue_vac (C i) (D i) L0 t q (fun n h v=>(p i (t.trans q)).2 _ h v)
    let δ:=(64:ℝ)⁻¹^d
    change |a-a'| ≤ (1/4:ℝ)*δ - _ at e₂
    have hr': |a-a'| ≤ (1/4:ℝ)*δ:=e₂.trans (sub_le_self _ (by positivity))
    rw [Complex.norm_real,Real.norm_eq_abs,show a/a'-1=(a-a')/a' from (by field),abs_div,abs_of_pos hp, div_le_iff₀ hp]; change _≤δ*a'; exact hr'.trans ((le_of_eq (mul_comm ..)).trans (mul_le_mul_of_nonneg_left (by linarith) (by unfold δ; positivity)))
 change ‖((basket L0 C D F (i+1):ℝ):ℂ) • x (i+1)- (B:ℂ) • x i‖ ≤ _+(Y'*16⁻¹^i)*_
 rw [outlay _ _ _ _ i (t.trans q)]; unfold starts
 refine (bill_rel (a:=a) (g:=k^(i-F)) hp hi hl' hm (by positivity)).trans ?_
 have h1:2*k^(i-F)*(2^i*Y/(Q^d))≤ Y'*16⁻¹^i:=by
    have he:k*2 ≤ Q*(16:ℝ)⁻¹:=by linarith only [hC64 L0]
    have e₃:(k*2)^d /Q^d ≤(16:ℝ)⁻¹^d:=by rw [div_le_iff₀ hb,← mul_pow]; refine pow_le_pow_left₀ (by unfold k; positivity) ?_ _; rwa [mul_comm Q] at he
    calc _=2*D0*Y*((k*2)^d/Q^d):=by
           unfold D0; rw [show i-F=j-F+d by unfold d; omega,pow_add,show (2:ℝ)^i=2^j*2^d from (by rw [←pow_add,show j+d=i from by unfold d; omega]),mul_pow k]; change 2*(k^(j-F)*k^d)*(2^j*2^d*Y/(Q^d))=2*(k^(j-F)*2^j)*Y*((k^d*2^d)/Q^d); exact stencil_eq _ _ _ _ _ _
         _ ≤ 2*D0*Y*((16:ℝ)⁻¹^d):=mul_le_mul_of_nonneg_left e₃ (by unfold D0; positivity)
         _ ≤ Y'*_:=by unfold d; rw [bankNote (show 0<(16:ℝ) by norm_num) q]; unfold Y'; rw [add_mul]; refine le_trans (le_of_eq (show _=2*D0*Y*16^j*(16⁻¹:ℝ)^i by ac_rfl)) (le_add_of_nonneg_right (by positivity))
 have h2 :(64:ℝ)⁻¹^d ≤ Y'* (16⁻¹:ℝ)^i:=by
    unfold d; rw [bankNote (show 0<(64:ℝ) by norm_num) q]; apply mul_le_mul (le_add_of_nonneg_left (by unfold D0; positivity)) (pow_le_pow_left₀ (by norm_num) (by norm_num) _) (by positivity) (by unfold D0; positivity)
 exact add_le_add h1 (mul_le_mul_of_nonneg_right (hS.trans h2) (norm_nonneg _))
where
 stencil_eq (a b c d e g:ℝ):2*(a*b)*(c*d*e/g)=2*(a*c)*e*(b*d/g):=by ring
 QmulEq(h c a:ℝ): (h:ℂ)* ↑(c*a) = (↑(c*(h*a)):ℂ):=by push_cast; ring
 bankNote {s j:ℕ}{a:ℝ}(h:0<a)(q:j≤ s): a⁻¹^(s-j)= a^j*a⁻¹^s:=by nth_rw 2 [show s=s-j+j from by omega]; rw [pow_add, mul_comm (a^j),mul_assoc,←mul_pow, inv_mul_cancel₀ h.ne',one_pow,mul_one]
#print axioms coatLemma
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
