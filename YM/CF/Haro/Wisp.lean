import YM.CF.Haro.Color
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{n:ℕ}{K u v w A' B' C':ℝ}
abbrev Risk(n:ℕ)(F:E→ Op Slot)(B: Op Slot)(p:E)(R a:ℝ):Prop:=‖B‖ ≤ a∧ Allows n (fun v=>F v-B) p (a*R)
abbrev horn:ℝ:= max 1 ‖(Nacre.coordL (k:=Slot)).symm.toContinuousLinearMap‖
abbrev pole :ℝ:=max 1 ‖(starL' ℝ (A:=Op Slot)).toContinuousLinearMap‖
lemma p0: 1 ≤ horn:=le_max_left ..
lemma p1 : 1 ≤ pole:=le_max_left ..
lemma soft(R:ℝ)(B:Op Slot)(h:0 ≤ v)(t:∀ i j, ‖B i j‖ ≤ v): ‖B‖ ≤ horn*v:=by
 let f:= (coordL (k:=Slot)); rw [←f.symm_apply_apply B]; refine (f.symm.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul (le_max_right ..) ?_ (norm_nonneg _) (zero_le_one.trans p0)); apply (pi_norm_le_iff_of_nonneg h).mpr; intro i; exact (pi_norm_le_iff_of_nonneg h).mpr (t _)
lemma softL(F:E→Op Slot)(h:0 ≤ v)(B: Op Slot)(p:∀ i j, Allows n (fun k=>F k i j-B i j) z v): Allows n (fun k=>F k-B) z (horn*v):=by
 let X(k:E)(i j:Slot):=F k i j-B i j; have hv: Allows n X z v:=allows_pi h fun i=>allows_pi h (p i); exact hv.linear (coordL (k:=Slot)).symm.toContinuousLinearMap (le_max_right ..)
lemma reS(F:E→Op Slot)(B:Op Slot)(p: Risk n F B z u v): Risk n (star ∘ F) (star B) z u (pole*v):=by
 have hv:0 ≤ v:=(norm_nonneg _).trans p.1; refine ⟨by rw [norm_star]; exact p.1.trans (le_mul_of_one_le_left hv p1), ?_⟩
 have he:(fun v=> (star ∘ F) v-star B)= ((starL' ℝ (A:=Op Slot)).toContinuousLinearMap) ∘ (fun v=>F v-B):=funext fun v=> Eq.symm (star_sub ..); rw [he,mul_assoc]; exact p.2.linear _ (le_max_right ..)
lemma risk_m(F:E→Op Slot)(B:Op Slot)(p: Risk n F B z u v)(h: u ≤ w): Risk n F B z w v:= ⟨p.1,p.2.mono (mul_le_mul_of_nonneg_left h ((norm_nonneg _).trans p.1))⟩
def wheel_l (n:ℕ):= max 1 (2^n*‖ContinuousLinearMap.mul ℝ (Op Slot)‖)
lemma wheels_p : 1 ≤ wheel_l n:=le_max_left ..
lemma leaf_h (F T:E→Op Slot)(h:Allows n F z u)(p:Allows n T z v): Allows n (F*T) z (wheel_l n *u*v):=by
 refine (h.bilinear (ContinuousLinearMap.mul ℝ (Op Slot)) p le_rfl).mono ?_; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) h.nonneg) p.nonneg -- tune
lemma roam_p(F T:E→Op Slot)(A B:Op Slot)(p:Risk n F A z w u)(h:Risk n T B z w v)(ht: w ≤ 1): Risk n (F*T) (A*B) z w (3*wheel_l n*u*v):=by
 have hu:0≤u:=(norm_nonneg _).trans p.1; have hv:0 ≤v:=(norm_nonneg _).trans h.1
 refine ⟨(norm_mul_le ..).trans ((mul_le_mul p.1 h.1 (norm_nonneg _) hu).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hu (by linarith only [wheels_p (n:=n)])) hv)),?_⟩
 let U:E→Op Slot:=fun _=>A; let V:E→Op Slot:=fun _=>B; let Q:E→Op Slot:=F-U; let C:=T-V
 have he:Allows n T z (2*v):=by rw [show T=C+V from (sub_add_cancel T V).symm]; exact (h.2.add (allows_const _ h.1)).mono (by linarith only [mul_le_mul_of_nonneg_left ht hv])
 rw [show (fun x=>(F*T) x-A*B)=Q*T+U*C from ?_]; exact ((leaf_h Q T p.2 he).add (leaf_h U C (allows_const _ p.1) h.2)).mono (le_of_eq (by ring))
 ext1 v; change _=(F v-A)*T v+A*(T v-B); rw [sub_mul, mul_sub]; change F v*T v -A*B=_; abel
lemma ship_x(D Y: Op Slot)(h: D∈ unitary (Op Slot))(p:Y ∈ unitary (Op Slot))(F:E→Op Slot)(hp:Allows n F z u): Allows n (fun y=> star D * F y * Y) z u:=by
 let L:= (show Op Slot →ₗ[ℝ] Op Slot from ⟨⟨fun x=> star D * x * Y,fun x y=>by rw [mul_add,add_mul]⟩,fun r x=>by change star D*(r • x)*Y=r • _; rw [Matrix.mul_smul, Matrix.smul_mul]⟩).toContinuousLinearMap
 have hv:‖L‖≤1:=ContinuousLinearMap.opNorm_le_bound L zero_le_one fun x=> by
    rw [one_mul]; change ‖star D * x * Y‖≤_; let U:UNI Slot:=⟨_,p⟩; let V:UNI Slot:=⟨_,h⟩; change ‖((star V).val*x)*U.val‖≤ _; rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
 exact (hp.linear L hv).mono (by linarith : 1*u≤u)
lemma cape_l(F:E→ Op Slot)(p:Allows n F z u)(i j:Slot): Allows n (fun x=>F x i j) z u:=by
 let L:Op Slot→ₗ[ℝ]ℂ:= ⟨⟨fun x=> x i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩; let K:=L.toContinuousLinearMap; apply (p.linear K ?_).mono (le_of_eq (one_mul u)); apply ContinuousLinearMap.opNorm_le_bound K zero_le_one; intro x; exact (norm_entry ..).trans (one_mul _).symm.le
end YM.CF.Haro
