import Crape.Cutwork
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
-- Qualifying per reference height. Markov on price.Basic threshold ~2^s sqrt(Wx). all suffice vs boost.S
local notation "K"=>P.calibration
lemma ester{C D:ℕ→ℕ→ℝ}(F j n:ℕ)(o:Cover)(b:Bool)(t:F ≤ j)(p:∀ s, j ≤ s → Accordance P M F s (C s) (D s))(f₁:(P.calibration.ℓ:ℤ) + Calico.amount P j ≤ nodeC o (3:Axis))(f₂:nodeC o (3:Axis) ≤ n)(h:(K).ℓ+22 ≤ nodeC o (3:Axis)):
 ∀ᵐ x ∂P.pillars 3,∀ᶠ s:ℕ in atTop, ‖P.viewF 3 x (s+1) (birthDress P s j o b (C s) (D s) h)‖≤2^s * max 1 (wafer P M j (Calico.amount P j) n):=by
 let w:= wafer P M j (Calico.amount P j) n; let d:=max 1 w; have hd:1≤ d:=le_max_left ..; have ht:0<d:=zero_lt_one.trans_le hd
 let i(k:ℕ):= k+j; let z(k:ℕ):= dress P (i k) j o b (C (i k)) (D (i k))
 have he (k:ℕ): (∫ x, readingSq P (i k+1) (z k) x ∂P.pillars 3) ≤ d:=by
    rw [paid_mean]
    have h': (P.E (i k+1) (P.reflectTest 3 (z k)*z k).val).re ≤ ‖P.E (i k+1) (mirror K 3 0 (Calico.invoice P (i k) j o b (C (i k)) (D (i k)))*Calico.invoice P (i k) j o b (C (i k)) (D (i k)))‖:=by
      apply le_trans (Complex.re_le_norm _); unfold z; change ‖P.E (i k+1) (mirror K 3 0 (dress P (i k) j o b (C (i k)) (D (i k))).val*(dress P (i k) j o b (C (i k)) (D (i k))).val)‖≤_; rw [dress_val]
    refine h'.trans (((p (i k) (Nat.le_add_left ..)).2 j t (Nat.le_add_left ..) 3 o b n f₁ f₂).trans (le_max_right ..))
 have hv(k:ℕ):0 < 2^k*d:=mul_pos (pow_pos zero_lt_two _) ht
 let A(k:ℕ)(_: Unit)(x:P.Spectrum0 3):= readingSq P (i k+1) (z k) x
 have hg(k:ℕ)(x:P.Spectrum0 3):A k () x= ‖P.viewF 3 x (i k+1) (birthDress P (i k) j o b _ _ h)‖^2:=as_paid ..
 have hm:=prognosis A (fun _=>d) (fun _ _=> paid_cont ..) (fun k ⟨⟩ x=> by rw [hg]; exact sq_nonneg _) _ hv (fun k _=>he k) (fun k=>?_)
 · filter_upwards [hm] with x p'; obtain ⟨a,ha⟩:= Filter.eventually_atTop.mp p'; filter_upwards [Filter.eventually_ge_atTop (a+j)] with s l; let k:=s-j; have e:s=i k:=by unfold k i; omega
   have hx:= ha k (by unfold k; omega) (); have H':(2:ℝ)^k ≤2^s:=pow_le_pow_right₀ one_le_two (Nat.sub_le ..)
   rw [hg] at hx; exact e ▸ ((pow_lt_pow_iff_left₀ (norm_nonneg _) (hv k).le (by decide:2 ≠ 0)).mp hx).le.trans (mul_le_mul_of_nonneg_right (e ▸ H') ht.le)
 · unfold discount; rw [Fintype.card_unique,Nat.cast_one,one_mul]
   have e:((2:ℝ)⁻¹)^k=(2^k)⁻¹:=inv_pow ..
   rw [sq,mul_mul_mul_comm,e]; have k':0<(2:ℝ)^k:=pow_pos zero_lt_two _
   field_simp; have l:1≤ (2:ℝ)^k:=one_le_pow₀ one_le_two; nlinarith
#check prognosis
#check inv_pow
#print axioms ester
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
