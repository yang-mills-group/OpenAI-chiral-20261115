import CellQ.Day
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
open Py.Rate.Pitching.Focus
variable (P:Spine) {U:P.Roster}(M:Morn P.par.K)
open Py.Dyad Keeping
section ratio
variable {F:ℕ}{C D:ℕ→ℕ→ℝ}(L:Side)(p:∀ s,F ≤ s→ Bills F (s+1) s L (C s) (D s))
local notation "W" i:max x:max=> revenue L (C i) (D i) i x
include p in
lemma fainter_ratio (j s:ℕ)(u:F ≤ j)(v:j ≤ s): |(W s j)/(W s F)-1|≤ (64:ℝ)⁻¹^(s-j):=by
 have h:= boundsT L C D F p le_rfl (u.trans v); have h':=boundsT L C D F p u v
 let a:= W s F; let a':= W s j; let d:=s-j
 change 3/4≤a ∧ a≤ 5/4 at h; change 3/4 ≤a'∧ a'≤5/4 at h'
 have hp:0<a':=by linarith
 have hp':0<a:=by linarith
 have e₂:=revenue_vac (C s) (D s) L u v (fun k h w=>(p s (u.trans v)).2 _ h w)
 let δ:=(64:ℝ)⁻¹^d
 change |a-a'| ≤ (1/4:ℝ)*δ - _ at e₂
 have hr': |a'-a| ≤ (1/4:ℝ)*δ:=by rw [abs_sub_comm]; exact e₂.trans (sub_le_self _ (by positivity))
 rw [show (W s j)/(W s F)-1=(a'-a)/a from (by change a'/a-1=_; field),abs_div,abs_of_pos hp', div_le_iff₀ hp']; change _≤δ*a; exact hr'.trans ((le_of_eq (mul_comm ..)).trans (mul_le_mul_of_nonneg_left (by linarith) (by unfold δ; positivity)))
variable (C D)
def eraK(j s:ℕ):ℝ:= C s s * (W s j)
-- marker from s+k
abbrev stepsK(j s:ℕ):ℕ→ℝ
 | 0=>1
 | k+1=> stepsK j s k * eraK C D L j (j+s+k)
lemma stepsK_succ(j s k):stepsK C D L j s (k+1)=stepsK C D L j s k*eraK C D L j (j+s+k):= by rw [stepsK]
#check @eraK
#check @stepsK
include p
lemma feeK (i j:ℕ)(h:F ≤ j)(u:j ≤ i): |eraK C D L j i|≤2*gainCost L ∧ eraK C D L j i ≠ 0:=by
 have ht:=boundsT L C D F p h u
 have hk:0< W i j:=by linarith; -- semicolon
 have hr:= (p i (h.trans u)).1 i (h.trans u) (Nat.lt_succ_self _)
 unfold eraK; rw [abs_mul,abs_of_pos hk]; exact ⟨(mul_le_mul hr.amp (ht.2.trans (by norm_num)) hk.le (gainCost_pos _).le).trans_eq (mul_comm ..),mul_ne_zero hr.non hk.ne'⟩
local notation "η"=> 2*gainCost L
lemma stepsK_bound (j s:ℕ)(h:F ≤ j)(n:ℕ): |stepsK C D L j s n| ≤ (η)^n ∧ stepsK C D L j s n ≠0:=by
 induction n with
 | zero=> simp [stepsK]
 | succ n ih=>
    rw [stepsK_succ,pow_succ,abs_mul]; obtain ⟨v,c⟩:=feeK C D L p (j+s+n) j h (by omega)
    exact ⟨mul_le_mul ih.1 v (abs_nonneg _) (pow_nonneg (mul_nonneg zero_le_two (gainCost_pos _).le) _),mul_ne_zero ih.2 c⟩
-- argument order: p uses C D implicit before.Sin.

#check stepsK_bound
lemma ford_bound (j s:ℕ)(h:F ≤ j)(n:ℕ): let t:=j+s; let u:=t+n
   |stepsK C D L j s n/basket L C D F u| ≤ Real.exp (∑ k∈Finset.range n, (64:ℝ)⁻¹^k) * |(basket L C D F (j+s))⁻¹|:=by
 induction n with
 | zero=> simp only [stepsK, Nat.add_zero, Finset.range_zero,Finset.sum_empty,Real.exp_zero, one_div,one_mul,le_refl]
 | succ n ih=>
   dsimp only at ih ⊢; let i:=j+s+n; let R:=W i j; let T:= W i F; let b:= C i i
   have hv:F ≤ i:=by unfold i; omega
   have hp:j ≤ i:=by unfold i; omega
   have hu:b ≠ 0:=(p i hv).1 _ hv (by omega)|>.non
   -- ratio exact, no assumption denom not zero except b for cancellation.
   rw [Finset.sum_range_succ,Real.exp_add,stepsK_succ,show j+s+(n+1)=i+1 by unfold i; omega,outlay _ _ _ _ i hv]
   let Q:= basket L C D F i; let q:= stepsK C D L j s n; let E:=Real.exp (∑ k∈Finset.range n,(64:ℝ)⁻¹^k); let d:=(64:ℝ)⁻¹^n
   have hz: |R/T| ≤ Real.exp d:=by
      have ht:= fainter_ratio L p j i h hp
      have h':0<R/T:=div_pos (by have he:=boundsT L C D F p h hp; change 3/4≤R∧_ at he; linarith only [he.1]) (by have he:=boundsT L C D F p le_rfl hv; change 3/4≤T∧_ at he; linarith only [he.1])
      have hl: (64:ℝ)⁻¹^(i-j)≤d:=pow_le_pow_of_le_one (by norm_num) (by norm_num) (by unfold i; omega)
      rw [abs_of_pos h']; exact le_trans (b:=d+1) (by linarith only [(le_abs_self (R/T-1)).trans ht,hl]) (Real.add_one_le_exp _)
   have hI: |q/Q|≤E*|(basket L C D F (j+s))⁻¹|:=ih
   change |q*(b*R)/(Q*(b*T))|≤ E*Real.exp d*_
   rw [show q*(b*R)/(Q*(b*T))=q/Q*(R/T) from (by rw [mul_div_mul_comm,mul_div_mul_left _ _ hu]),abs_mul]; exact (mul_le_mul hI hz (abs_nonneg _) ((abs_nonneg _).trans hI)).trans_eq (by ring)
end ratio
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
