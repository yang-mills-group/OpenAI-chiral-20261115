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
open Py.Dyad Keeping
open Py.Rate.Pitching.Focus (Morn)
/- board the state costs and all matching proofs. abstract height recession, mix. no claim fixed-time Lozenge! -/
structure RobeRoad(P:Spine)(s:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3):Prop where
 e : ∀ j,s≤ j→∃ y:ℝ,0 < y ∧ ∀ᶠ i:ℕ in atTop,
     ‖P.viewF 3 x (i+1) (birthDress P i j (cellar P s j) true (C i) (D i) (fresh P s j))‖ ≤ 2^i*y

variable (P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(x:P.Spectrum0 3)(M:Morn P.par.K)(p:∀ s,F ≤ s → Accordance P M F s (C s) (D s))
include p
lemma redemption : ∀ᵐ x∂P.pillars 3,RobeRoad P F C D x:= by
 have he(j:ℕ): ∀ᵐ x∂P.pillars 3,F ≤ j → ∃ y:ℝ,0 < y ∧ ∀ᶠ i:ℕ in atTop,
     ‖P.viewF 3 x (i+1) (birthDress P i j (cellar P F j) true (C i) (D i) (fresh P F j))‖ ≤ 2^i*y:=by
    by_cases a:F ≤ j
    · obtain ⟨h,b⟩:=recess P F j
      have he:(P.calibration.ℓ:ℤ)+Calico.amount P j≤ nodeC (cellar P F j) (3:Axis):= by unfold minB at h; push_cast at h; unfold Calico.amount; push_cast; exact h -- hb contains amount pow raw?
      exact (ester P M F j (reachQ P j) _ true a (C:=C) (D:=D) (fun i g=>p i (a.trans g)) he b (fresh P F j)).mono fun _ q _=> ⟨_,zero_lt_one.trans_le (le_max_left ..),q⟩
    exact Eventually.of_forall fun _ b=>(a b).elim
 exact (ae_all_iff.mpr he).mono fun _ v=>⟨v⟩
variable (T:RobeRoad P F C D x)
include T
local notation "Lx"=>P.par.R.L
lemma advances {j:ℕ}(q:F ≤ j) : CauchySeq (fun i=> recoup P F C D x i j):=by
 let g(s:ℕ):=P.viewF 3 x s (certificate P F s j)
 obtain ⟨y,t,l⟩:=T.e _ q
 refine coatLemma Lx C D F j q (fun s e=>p s e|>.1) g y t ?_; filter_upwards [l] with s h
 rw [billDress _ _ _ _ _ _ _ (fresh P F j)] at h
 unfold tokenA tokenB denom at h -- simp? simp via direct equality
 let Q:=ThinGauge.boost (Xη Lx)
 have hZ: hGain (C s) (s+1) s=C s s:=by rw [gain_step _ _ _ (Nat.lt_succ_self _),gain_here,mul_one]
 change ‖((hGain (C s) (s+1) s*(Q^(s-j)*revenue Lx (C s) (D s) s j):ℝ):ℂ) • g (s+1)+ ((-(Q^(s-j)):ℝ):ℂ) • g s‖ ≤ _ at h
 rwa [hZ] at h
#print axioms advances
#print axioms redemption
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
