import YM.CF.BPress.Pf.Ratio
import YM.CF.BPress.Pf.Mileage
import YM.CF.BPress.Pf.Helm
import YM.CF.BPress.Spin.Tilt
/-! The complex amplitude formula at thm prop:B-bra. Hum as a Spire value to isolate away, enters ONLY here for pinning: orient from existing `change_v`. `ℓ` and its estimates are independent of that value. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter Finset Fock Spin NormedSpace MeasureTheory Branch Spin.Pledge Spin.Cellar Spin.Cellar.Pass Bridge Mileage Helm Thera
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q:Finset I}{A T K:Op I}{C C': ℝ → Op I}{r ε w:ℝ}

abbrev shun (I:Type)[Fintype I][LinearOrder I] (P Q:Finset I):Op I:=1-(cutM P+cutM Q)
private lemma zero01 : (0:ℝ)∈ Set.Icc 0 1:= ⟨le_rfl,zero_le_one⟩
private lemma one01 : (1:ℝ)∈ Set.Icc 0 1:= ⟨zero_le_one,le_rfl⟩
lemma tiny_t {v:ℝ}(h:v∈Set.Icc (0:ℝ) 1): ‖v‖≤1:=by rw [Real.norm_of_nonneg h.1]; exact h.2
section Flight
def craft (A T:Op I)(y: Wave I)(u:ℝ):= acts (quant (zom T u)) y
def mood (A T:Op I):= tilt A T 1
def traceM (P Q: Finset I)(A T:Op I):=smoothP (cutM P) (cutM Q) (shun I P Q) (mood A T)
def cabin (P Q:Finset I)(A T:Op I):=slide (cutM P) (cutM Q) (shun I P Q) (mood A T)
def cue (P Q: Finset I)(A T:Op I)(v:ℝ):= Basement.slip (cutM P) (cutM Q) (shun I P Q) (mood A T) v* Trans.pinv (mood A T) (cabin P Q A T v)
structure Issued (P Q:Finset I)(A T:Op I)(C C':ℝ→Op I)(r ε:ℝ):Prop where
 proj:IsStarProjection A
 she:TagG A T
 near:‖T‖≤1
 rails:Pass (cutM P) (cutM Q) (shun I P Q) (mood A T) ε
 apart: Disjoint P Q
 skit: PairBoard (cutM P) (cutM Q) (shun I P Q) (C 2)
 cont:ContinuousOn C' (Set.Icc 0 2)
 diff:∀ x∈Set.Icc (0:ℝ) 2, HasDerivAt C (C' x) x
 front:∀ t∈Set.Icc (0:ℝ) 1,Bore (tilt A T t) (C 0) r
 center:∀ t∈Set.Icc (0:ℝ) 1,Bore (mood A T) (C t) r
 warp:∀ t∈Set.Icc (0:ℝ) 1, Bore (traceM P Q A T t) (C 1) r
 back:∀ t∈Set.Icc (1:ℝ) 2,Bore (traceM P Q A T 0) (C t) r
-- path value increments, strong matrix support traces
def firstD(A T:Op I)(U:Op I)(v:ℝ): Op I:= seedM (tilt A T v) T U
def prepD(A T U U':Op I): Op I:= dinoM (mood A T) U' U
def starD(P Q:Finset I)(A T:Op I)(U:Op I)(v:ℝ):=seedM (traceM P Q A T v) (cue P Q A T v) U
def passD(P Q:Finset I)(A T U U':Op I):=dinoM (traceM P Q A T 0) U' U

def sweepR (P Q:Finset I)(A T:Op I)(C C':ℝ→Op I):ℂ :=
 (∫ v in (0:ℝ)..1,(firstD A T (C 0) v).trace)+(∫ v in (0:ℝ)..1,(prepD A T (C v) (C' v)).trace) -
 (∫ v in (0:ℝ)..1,(starD P Q A T (C 1) v).trace)+(∫ v in (1:ℝ)..2,(passD P Q A T (C v) (C' v)).trace)

def loss (P C:Op I) := pencil (-lost P C)
def uPivot (A C:Op I):= (loss A C).trace.re/4

variable (H:Issued P Q A T C C' r ε){x:Wave I} (p:Top A x)
namespace Issued
include H
local notation "aX"=> cutM P
local notation "bX"=> cutM Q
local notation "U"=>mood A T
local notation "L"=> shun I P Q

lemma birth:Bore A (C 0) r:= by have he:=H.front _ zero01; rwa [Spin.zeroT H.proj] at he
lemma endF:Bore (cutM P + ramp L aX U) (C 2) r:= by have he:=H.back 2 ⟨by norm_num,le_rfl⟩; rwa [traceM,H.rails.mark_exit] at he
include p
lemma craft_with (v:ℝ): acts (quant (scraw A T v)) x=craft A T x v:=by rw [switch_s H.she,←together p]; rfl
lemma rising (v:ℝ): Top (tilt A T v) (craft A T x v):=by rw [←H.craft_with p]; exact p.spread (tiltR H.proj H.she v)
lemma ω_glide : inner ℂ (pairWave (C 0)) (craft A T x 1)= inner ℂ (pairWave (C 0)) x * Complex.exp (∫ v in (0:ℝ)..1, (firstD A T (C 0) v).trace):=by
 have he:= crossing (show (0:ℝ)≤1 by norm_num) _ _ (show ContinuousOn (fun _:ℝ=>T) _ from continuousOn_const) _ H.front (fun x _=>H.rising p x) (fun u _=> Rotate.d_shear T H.she.nil x u); rw [show craft A T x 0=x by simp [craft,zom,quant_one]] at he; exact he
lemma ω_rot : inner ℂ (pairWave (C 1)) (craft A T x 1) = inner ℂ (pairWave (C 0)) (craft A T x 1) *Complex.exp (∫ v in (0:ℝ)..1,(prepD A T (C v) (C' v)).trace):= passing (by norm_num) U (H.rising p 1) C C' (H.cont.mono (Set.Icc_subset_Icc_right (by norm_num))) (fun x p=> H.diff x (Set.Icc_subset_Icc_right (by norm_num : (1:ℝ) ≤ 2) p)) H.center
abbrev transportK (x:Wave I) (P Q: Finset I) (A T:Op I) (u:ℝ):= acts (quant (cabin P Q A T u)) (craft A T x 1)
lemma slips (v:ℝ)(Hx:v∈ Set.Icc (0:ℝ) 1) : Top (traceM P Q A T v) (transportK x P Q A T v):=(H.rising p 1).spread (H.rails.enjoy _ (tiny_t Hx)) -- header tune
lemma transport_shape : inner ℂ (pairWave (C 1)) (craft A T x 1) = inner ℂ (pairWave (C 1)) (transportK x P Q A T 0) *Complex.exp (∫ v in (0:ℝ)..1,(starD P Q A T (C 1) v).trace):=by
 let Y:=cue P Q A T; let D:=cabin P Q A T; have he: Continuous D:=by unfold D cabin slide coeff0 coeff1; fun_prop
 have ht:ContinuousOn Y (Set.Icc (0:ℝ) 1):=by
    intro i hi; let Z(v:ℝ):= Trans.gram U (D v); have hV:Continuous Z:=by unfold Z Trans.gram; fun_prop
    have hx : ContinuousAt (fun x=> (Z x)⁻¹) i:= (InvC_cont ((H.rails.enjoy i (tiny_t hi)).live_G)).comp (f:=Z) hV.continuousAt
    have hz: Continuous (Basement.slip aX bX L U):=by unfold Basement.slip Basement.slopeP1; fun_prop
    exact (hz.continuousAt.mul (hx.mul (he.star.continuousAt))).continuousWithinAt
 have hx:= crossing (show (0:ℝ)≤1 by norm_num) Y _ ht _ H.warp (H.slips p) (fun x y=>Rotate.d_real _ x H.rails (tiny_t y)); rw [show transportK x P Q A T 1= craft A T x 1 from ?_] at hx; exact hx
 rw [transportK, cabin, H.rails.approves]; exact (H.rising p 1).occupies
lemma exit : inner ℂ (braC P Q (C 2)) (craft A T x 1) = inner ℂ (pairWave (C 1)) (transportK x P Q A T 0) * Complex.exp (∫ v in (1:ℝ)..2,(passD P Q A T (C v) (C' v)).trace):=by
 rw [bra_ref (H.rising p 1) H.rails H.apart]; exact passing (by norm_num) (traceM P Q A T 0) (H.slips p _ zero01) C C' (H.cont.mono (Set.Icc_subset_Icc_left (by norm_num))) (fun x p=>H.diff _ (Set.Icc_subset_Icc_left zero_le_one p)) H.back
omit H p in
lemma normL {A B:Op I}(h:Bore A B r): ‖lost A B‖<1:=h.costs.trans_lt (sub_pos.mp h.δ_pos)
omit H p in
lemma pivot_cost {A B:Op I}(h:Bore A B r): Real.exp (uPivot A B)= ‖filled A B‖:=by
 apply pow_left_inj₀ (Real.exp_pos _).le (norm_nonneg _) (show (4:ℕ) ≠ 0 by norm_num) |>.1; rw [h.pivot,←Real.exp_nat_mul]; unfold uPivot; rw [show (↑(4:ℕ):ℝ) * _= (loss A B).trace.re by push_cast; ring,loss,bill_p (by rw [norm_neg]; exact normL h)]; simp [sub_eq_add_neg]
omit H p in
-- Eq:B-hum orientation pin (given charge z e.g. zen(hum))
lemma pins {T Q:Op I}{x:Wave I}(H:Bore T Q r)(z:ℂ)(h: Complex.exp ((uPivot T Q:ℂ)+z) • x=filled T Q) : inner ℂ (pairWave Q) x =Complex.exp ((uPivot T Q:ℂ)-z):=by
 let A:=uPivot T Q; let V:=lineOp T; let k:=pairWave Q; let S:=filled T Q; let t:=H.p; have hx: inner ℂ k S= (‖S‖:ℂ)^2:=by
    unfold S filled; nth_rw 1 [← (line_proj t).isIdempotentElem.eq]; rw [act_mul,←act_inner,(line_proj t).isSelfAdjoint]; exact inner_self_eq_norm_sq_to_K (𝕜:=ℂ) S -- tune
 have hp := congrArg (inner ℂ k) h; rw [inner_smul_right,hx] at hp; rw [← pivot_cost H,Complex.ofReal_exp,pow_two] at hp -- WRONG coerc exp
 exact mul_left_cancel₀ (Complex.exp_ne_zero _) (hp.trans (by rw [← Complex.exp_add,←Complex.exp_add]; congr 1; abel))
 -- edit
include H p
lemma liftLog (z:ℂ)(r0:Complex.exp ((uPivot A (C 0):ℂ)+z) • x=filled A (C 0)) : inner ℂ (braC P Q (C 2)) (craft A T x 1) = Complex.exp ((uPivot A (C 0):ℂ)-z+sweepR P Q A T C C'):=by
 have ht:= H.ω_glide p; rw [pins H.birth z r0] at ht; have hp:= H.transport_shape p; rw [H.ω_rot p,ht] at hp; rw [H.exit p]; let u:= C 2; let r:=∫ v in (0:ℝ)..1,(starD P Q A T (C 1) v).trace; unfold sweepR; rw [Complex.exp_add,Complex.exp_add, Complex.exp_sub _ r,Complex.exp_add]; field_simp; exact hp.symm
end Issued
end Flight
end YM.CF.BPress.Pf
