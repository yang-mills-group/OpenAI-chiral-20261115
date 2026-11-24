import MarchC.Admission
import Crape.Creature
import Preen.Fitted
import SatinLocalChron
import Preen.Travel
import GlazeS.Incline
import GlazeS.Room
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
namespace Mido
open Calico Py.Rate.Pitching.Focus
variable (P:Spine)(M:Morn P.par.K){C D:ℕ→ℕ→ℝ}
local notation "K"=>P.calibration
lemma mintAE (F j n:ℕ)(a:Axis)(o:Cover)(t:F ≤ j)(p:∀ s, j ≤ s → Accordance P M F s (C s) (D s))(f₁:(P.calibration.ℓ:ℤ) + Calico.amount P j ≤ nodeC o a)(f₂:nodeC o a ≤ n)(h:(K).ℓ+22 ≤ nodeC o a):
 ∀ᵐ x ∂P.pillars 3,∀ᶠ s:ℕ in atTop, ‖P.viewF a (P.otherSpectrum 3 a x) (s+1) (bonDress P a s j o (C s) (D s) h)‖≤2^s * max 1 (wafer P M j (Calico.amount P j) n):=by
 let w:= wafer P M j (Calico.amount P j) n; let d:=max 1 w; have hd:1≤ d:=le_max_left ..; have ht:0<d:=zero_lt_one.trans_le hd
 let i(k:ℕ):= k+j; let z(k:ℕ):= dress P (i k) j o true (C (i k)) (D (i k)); let A(k:ℕ)(_:Unit)(x:P.Spectrum0 3):=(P.singleState a (i k+1) (P.otherSpectrum 3 a x) (P.reflectTest a (z k)*z k)).re
 have he (k:ℕ): (∫ x,A k () x ∂P.pillars 3) ≤ d:=by
    have h': (P.E (i k+1) (P.reflectTest a (z k)*z k).val).re ≤ ‖P.E (i k+1) (mirror K a 0 (Calico.invoice P (i k) j o true (C (i k)) (D (i k)))*Calico.invoice P (i k) j o true (C (i k)) (D (i k)))‖:=by
      apply le_trans (Complex.re_le_norm _); unfold z; change ‖P.E (i k+1) (mirror K a 0 (dress P (i k) j o true (C (i k)) (D (i k))).val*(dress P (i k) j o true (C (i k)) (D (i k))).val)‖≤_; rw [dress_val]
    refine (mn_earn P a (i k+1) (z k)).le.trans (h'.trans (((p (i k) (Nat.le_add_left ..)).2 j t (Nat.le_add_left ..) a o true n f₁ f₂).trans (le_max_right ..)))
 have hv(k:ℕ):0 < 2^k*d:=mul_pos (pow_pos zero_lt_two _) ht
 have hg(k:ℕ)(x:P.Spectrum0 3):A k () x= ‖P.viewF a (P.otherSpectrum 3 a x) (i k+1) (bonDress P a (i k) j o _ _ h)‖^2:=as_mn ..
 have hm:=prognosis A (fun _=>d) (fun k _=> mn_cont P a ..) (fun k ⟨⟩ x=> by rw [hg]; exact sq_nonneg _) _ hv (fun k _=>he k) (fun k=>?_)
 · filter_upwards [hm] with x p'; obtain ⟨v,hv'⟩:= Filter.eventually_atTop.mp p'; filter_upwards [Filter.eventually_ge_atTop (v+j)] with s l; let k:=s-j; have e:s=i k:=by unfold k i; omega
   have hx:= hv' k (by unfold k; omega) (); have H':(2:ℝ)^k ≤2^s:=pow_le_pow_right₀ one_le_two (Nat.sub_le ..)
   rw [hg] at hx; exact e ▸ ((pow_lt_pow_iff_left₀ (norm_nonneg _) (hv k).le (by decide:2 ≠ 0)).mp hx).le.trans (mul_le_mul_of_nonneg_right (e ▸ H') ht.le)
 · unfold discount; rw [Fintype.card_unique,Nat.cast_one,one_mul]
   have e:((2:ℝ)⁻¹)^k=(2^k)⁻¹:=inv_pow ..
   rw [sq,mul_mul_mul_comm,e]; have k':0<(2:ℝ)^k:=pow_pos zero_lt_two _
   field_simp; have l:1≤ (2:ℝ)^k:=one_le_pow₀ one_le_two; nlinarith
local notation "u" a:max x:max=>P.otherSpectrum 3 a x
open Py.Dyad Keeping
noncomputable def tether(F:ℕ)(C D:ℕ→ℕ→ℝ)(j s:ℕ)(o:Cover)(a:Axis)(ζ:P.Spectrum0 a)(h:(K).ℓ+22 ≤ nodeC o a):P.ManyF a ζ:=
 P.wealth a ζ (((basket P.par.R.L C D F s:ℝ):ℂ) • P.viewF a ζ s (rooty P a s j o h))
/- Rovers yes x with every P and heading offered.
Using the same recovery axiom-free from payment on z.W.T.
-/
def Rovers(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3):Prop:= ∀ j,F ≤ j→∀ a o,(minB P j:ℤ) ≤ nodeC o a → ∀ h:(K).ℓ+22 ≤ nodeC o a, CauchySeq (fun s=> tether P F C D j s o a (u a x) h)
set_option maxHeartbeats 1150000 in
lemma rover_all(F:ℕ)(p:∀s,F ≤ s → Accordance P M F s (C s) (D s)): ∀ᵐ x ∂P.pillars 3, Rovers P F C D x:=by
 have he(j:ℕ)(a:Axis)(o:Cover):∀ᵐ x∂P.pillars 3,F ≤ j→ (minB P j:ℤ)≤nodeC o a → ∀ h:(K).ℓ+22 ≤ nodeC o a,CauchySeq (fun s=>tether P F C D j s o a (u a x) h):=by
    by_cases q:F ≤ j; swap; · exact Eventually.of_forall fun _ b=>(q b).elim
    by_cases g:(minB P j:ℤ) ≤ nodeC o a; swap; · exact Eventually.of_forall fun _ _ b=>(g b).elim
    have h' : ((K).ℓ:ℤ)+Calico.amount P j ≤ nodeC o a:=by unfold minB at g; push_cast at g; exact g
    have h:(K).ℓ+22 ≤ nodeC o a:=by have hz:22 ≤Calico.amount P j:=Nat.le_add_right ..; omega
    let d:=(nodeC o a).toNat
    filter_upwards [mintAE P M F j d a o q (fun s v=>p s (q.trans v)) h' ((Int.toNat_of_nonneg (by omega)).symm.le) h] with x p'
    intro _ _ _
    let f(s:ℕ):=P.viewF a (u a x) s (rooty P a s j o h)
    let Lx:=P.par.R.L
    let w:=max 1 (wafer P M j (Calico.amount P j) d)
    have hx:CauchySeq (fun s=> ((basket Lx C D F s:ℝ):ℂ) • f s):=by
       refine coatLemma Lx C D F j q (fun s e=>p s e|>.1) f w (zero_lt_one.trans_le (le_max_left ..)) ?_
       filter_upwards [p'] with s hv
       rw [mn_dress _ _ _ _ _ _ _ _ h] at hv
       unfold tokenA tokenB denom at hv
       let Q:=ThinGauge.boost (Xη Lx)
       have hZ: hGain (C s) (s+1) s=C s s:=by rw [gain_step _ _ _ (Nat.lt_succ_self _),gain_here,mul_one]
       change ‖((hGain (C s) (s+1) s*(Q^(s-j)*revenue Lx (C s) (D s) s j):ℝ):ℂ) • f (s+1)+ ((-(Q^(s-j)):ℝ):ℂ) • f s‖ ≤ 2^s*w at hv
       refine le_trans (le_of_eq ?_) hv; exact congrArg (fun (w:ℝ)=> ‖((w*(Q^(s-j)*revenue Lx (C s) (D s) s j):ℝ):ℂ) • f (s+1)+ ((-(Q^(s-j)):ℝ):ℂ) • f s‖) hZ.symm -- target in coat sub? check coat: +. yes

    obtain ⟨y,b⟩:=cauchySeq_tendsto_of_complete hx
    exact (show Tendsto (fun s=> tether P F C D j s o a (u a x) h) atTop (𝓝 (P.wealth a (u a x) y)) from (P.wealth a (u a x)).continuous.continuousAt.tendsto.comp b).cauchySeq
 exact (ae_all_iff.mpr (fun j=>ae_all_iff.mpr (fun a=>ae_all_iff.mpr (fun o=>he j a o)))).mono (fun x h j t a o=>h j a o t)
#print axioms rover_all
end Mido
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
