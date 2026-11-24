import YM.SU5.May.LunarHeat
import YM.SU5.May.LunarTaylor
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
open SU Tulip Hygrometry Personality Rush Dial Cube Kea Emu Tilted May.Floe
attribute [local instance] opCStarAlgebra
open Rink
variable (N:Side)(P:Ramp)(p q:E4)(i:Title P)(x:Cover)(b:Bool) (v:Ket SpinIdx) (x':ℝ)
variable {D j k:ℕ} (J:Fin D)(a:ℝ)
local notation "T"=>rimB N
local notation "G" => chord N P i
local notation "ε" => ‖chord N P i‖
-- orientation & rates D independent regulators
noncomputable def flash (D:ℕ)(J:Fin D):ℕ:= D^2+J.val+1
lemma wage_cash: 0 < flash D J := by unfold flash; omega
def aimD (D:ℕ)(J:Fin D)(j:ℕ):ℕ:= flash D J*j^4
abbrev rateD (J:Fin D)(j:ℕ):ℝ:= ferryD ((flash D J:ℕ):ℝ) j
lemma rate_aim : rateD J j = 2*(aimD D J j:ℝ)-1:=by unfold rateD ferryD aimD; push_cast; ring
lemma wage {D:ℕ}(J:Fin D){j:ℕ}(p:j∈fling D):0 < aimD D J j:= mul_pos (wage_cash _) (pow_pos ((fling_up _).1 p).1 _)
-- scaling by -u, u=2*n-1
noncomputable def casted (t:ℕ):Title P:= ⟨fun k=> if k=P.a then 0 else if k=P.b then (1-2*(t:ℤ))*i.val k else (1-2*(t:ℤ))*i.val k -t,by simp⟩
lemma cast_chord (t:ℕ): chord N P (casted P i t)= (1-2*(t:ℝ)) • chord N P i:=by
 unfold chord; rw [smul_comm]; apply congrArg (_ • ·); apply PiLp.ext; intro l; rw [PiLp.smul_apply]; by_cases b:l=P.a; · subst l; simp [canon, casted,P.cross]; ring
 by_cases c:l=P.b; · subst l; simp [canon,casted,P.cross]; ring
 rw [z_loc _ _ _ b c,z_loc _ _ _ b c]; simp [casted,b,c]; ring
lemma cast_inj : Injective (casted P i):=by
 intro j k e; have hm: 1-2*(j:ℝ)=1-2*k:= smul_left_injective ℝ (hired 1 P i) (by dsimp only; rw [←cast_chord,←cast_chord,e]); exact Nat.cast_injective (R:=ℝ) (by linarith only [hm]) -- parameter incl N? didn't include
lemma rate_profit (f:j∈fling D) : 1 ≤ rateD J j:=by
 rw [rate_aim]; have hv:1 ≤ (aimD D J j:ℝ) := by exact_mod_cast (show 1 ≤ aimD D J j from wage J f); -- punctuation
 linarith only [hv]
lemma aim_up {D:ℕ}(J K:Fin D){j k:ℕ}(p:j<k)(f:j∈fling D): aimD D J j < aimD D K k := by
 obtain ⟨hj,pj⟩: 0 < j∧ j≤D:= (fling_up _).1 f; let Y:= D^2; have hp:(flash D K) > D^2:=by unfold flash; omega
 have ht: flash D J ≤ D^2+D:=by unfold flash; omega
 apply lt_of_le_of_lt (Nat.mul_le_mul_right (j^4) ht); refine lt_of_le_of_lt ?_ (Nat.mul_lt_mul_of_pos_right hp (pow_pos (hj.trans p) _)); apply le_trans _ (Nat.mul_le_mul_left (D^2) (pow_le_pow_left' (show j+1 ≤ k from p) 4))
 have hx: D*j≤ D^2:=by rw [sq]; exact Nat.mul_le_mul_left _ pj
 have hm : (D^2+D)*j ≤ D^2*(j+1):=by nlinarith only [hx]
 rw [pow_succ' j,←mul_assoc]; refine (Nat.mul_le_mul_right (j^3) hm).trans ?_; rw [mul_assoc, pow_succ' (j+1)]; gcongr; omega -- tune
lemma aimed {D:ℕ}(x:Fin D→ℕ)(p:∀ i,x i∈ fling D): Injective fun i=>aimD D i (x i) := by
 intro i j h; dsimp only at h; rcases lt_trichotomy (x i) (x j) with t|t|t
 · exact (lt_irrefl _ (h ▸ aim_up i j t (p i))).elim -- motive inference trouble
 · rw [t] at h; unfold aimD at h; have he: flash D i=flash D j:=mul_right_cancel₀ (pow_ne_zero _ ((fling_up _).1 (p j)).1.ne') h; apply Fin.ext; unfold flash at he; omega
 exact (lt_irrefl _ (h ▸ aim_up j i t (p j))).elim
-- budget exterior sampling
lemma rate_ceiling (J:Fin D)(u:j∈fling D): rateD J j ≤ 4*(D:ℝ)^6:=by
 have hD:1 ≤ D:=by have e:= J.isLt; omega
 have he: D≤D^2:=by nlinarith
 have hp : flash D J ≤ 2*D^2:=by unfold flash; omega
 have hq: aimD D J j ≤ 2*D^6:= (show _ ≤ (2*D^2)*D^4 from Nat.mul_le_mul hp (pow_le_pow_left' ((fling_up _).1 u).2 4)).trans_eq (by ring)
 rw [rate_aim]; have hl:(aimD D J j:ℝ) ≤↑(2*D^6:ℕ):= by exact_mod_cast hq
 push_cast at hl; linarith only [hl]
variable (h: (D:ℝ)^10 ≤ rimB N) (g:grain P i ≤ (D:ℝ)) (x0:6 ≤ D)
noncomputable def arenaI (P:Ramp)(i:Title P)(J:Fin D)(j:ℕ):= casted P i (aimD D J j)
local notation "R" j:max=> arenaI P i J j
lemma askSale : chord N P (R j)= rateD J j • -(chord N P i) :=by rw [arenaI, cast_chord, rate_aim,smul_neg, ←neg_smul, neg_sub]; -- tune
lemma scaleH (f:j∈fling D): ‖chord N P (R j)‖=rateD J j*‖chord N P i‖ :=by rw [askSale,norm_smul,Real.norm_of_nonneg (zero_le_one.trans (rate_profit J f)), norm_neg]
include x0 g
lemma temperatureA (f:j∈fling D): (rateD J j) * (2*‖chord N P i‖*hazySize D N) ≤1:= by
 let Q:ℝ:=D; let E:= (ε); let M:= (T); have hm: E*M≤ D:=by rw [show E*M=(grain P i) from therm ..]; exact g
 have hu:6≤Q:=by unfold Q; exact_mod_cast x0
 have hp:0<Q:=lt_of_lt_of_le (by norm_num) hu
 change _ * (2*E*(M/Q^10)) ≤ _; rw [← mul_div_assoc,← mul_div_assoc, div_le_one (pow_pos hp _)]; rw [mul_assoc (2:ℝ)]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by norm_num:(0:ℝ) ≤2)) (show 0≤rateD J j from zero_le_one.trans (rate_profit J f))).trans; apply (mul_le_mul_of_nonneg_right (rate_ceiling _ f) (show (0:ℝ)≤2*Q from (by positivity))).trans; change 4*Q^6*(2*Q) ≤ _; rw [show 4*Q^6*(2*Q)=Q^7*8 from (by ring), show Q^10= Q^7*Q^3 from (by ring)]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact le_trans (le_of_lt (show (8:ℝ)<6^3 by norm_num)) (pow_le_pow_left₀ (by norm_num) hu _)
include h
lemma tune_head (f:j∈fling D):‖chord N P (R j)‖ ≤1/(D:ℝ) := by
 rw [scaleH N P _ J f]; let Q:ℝ:= D; have hx:6≤ Q:=by unfold Q; exact_mod_cast x0
 have hp:0<Q:=by linarith
 let A:= ‖chord N P i‖; have he:=therm N P i; apply (mul_le_mul (rate_ceiling _ f) (show A ≤ Q/(Q^10) from ?_) (norm_nonneg _) (by positivity)).trans ?_
 · apply (le_div_iff₀ (pow_pos hp _)).2; rw [← he] at g; exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans g
 change 4*Q^6*(Q/Q^10)≤1/Q; field_simp; nlinarith only [hp,hx] -- inspect
variable (f:j∈fling D)
#print axioms rate_profit
#print axioms temperatureA
end YM.CF.May.Lunar
