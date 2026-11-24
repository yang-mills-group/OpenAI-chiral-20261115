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
-- accountant. offsets. t_j:=node representative smallest x≥ℓ+D via ruler advancement. z_j:= physical pose times →0 by rise polylog. no coupling changes. can then act all T>0.
variable(P:Spine)(F:ℕ)
local notation "K"=>P.calibration
local notation "R"=>ruler P.par.block
local notation "L0"=>P.par.R.L
abbrev subject(s:ℕ):Cover:=orbitB P.par.R.L (0:Cover) (s-F) -- physical anchor fixed. choose 0 epi. 
def kioskT (s:ℕ):ℤ:= nodeC (subject P F s) (3:Axis)
noncomputable abbrev minB (s:ℕ):ℕ:=P.calibration.ℓ+Calico.amount P s
noncomputable abbrev setback (s:ℕ):ℤ:= - ((kioskT P F s - minB P s) / ruler P.calibration.B)
noncomputable abbrev cellar (s:ℕ):Cover:=slid P.calibration 3 (setback P F s) (subject P F s)
noncomputable def reachQ(s:ℕ):ℕ:=minB P s +16*P.calibration.B.val
variable (s:ℕ)
lemma pages : (reachQ P s:ℤ)=(minB P s:ℤ)+R:=by rfl -- coe def? Int.castAdd
lemma recess : ((minB P s:ℕ):ℤ)≤nodeC (cellar P F s) (3:Axis) ∧ nodeC (cellar P F s) (3:Axis)≤reachQ P s:=by
 rw [cellar,bellV,if_pos rfl,pages]; let n:=kioskT P F s; let t:ℤ:= minB P s; have u:=ruler_gene P.par.block
 change t ≤ n+ (R)*(- ((n-t)/R)) ∧ n+ (R)*(- ((n-t)/R))≤t+R
 have h:= Int.emod_add_mul_ediv (n-t) (R); have e:=Int.emod_lt_of_pos (n-t) u; have q:=Int.emod_nonneg (n-t) u.ne'; change _+ (R)* _= _ at h
 rw [mul_neg]; omega
lemma precinct (L:Side)(t:Odd L.val)(w:ℕ)(G:Calibration)(u:Cover)(c:ℤ) : orbitB L (slid G 3 c u) w = slid G 3 ((L.val:ℤ)^w*c) (orbitB L u w) :=by
 apply node_dC; ext i; rw [bellV,dutyT _ _ t,dutyT _ _ t]; simp only [Pi.smul_apply,nsmul_eq_mul]; rw [bellV]; split_ifs <;> push_cast <;> ring
lemma upwards {j:ℕ}(t:F≤ j)(u:j ≤ s): orbitB P.par.R.L (subject P F j) (s-j)=subject P F s:=by
 unfold subject orbitB
 rw [←Function.iterate_add_apply,show s-j+(j-F)=s-F from by omega]
lemma er(s j:ℕ)(t:F ≤ j)(u:j ≤ s): etui P s j (cellar P F j)=P.shifts 3 (castor (timeMesh P.par) j s (setback P F j)) (wp P s (subject P F s)):=by
 unfold etui; rw [cellar,precinct _ P.par.R.odd_side, upwards P F s t u,wp_shift]; rfl
lemma fresh(j:ℕ):((K).ℓ:ℤ)+22 ≤ nodeC (cellar P F j) (3:Axis):= (recess P F j).1.trans' (by have he:22 ≤Calico.amount P j:=Nat.le_add_right ..; unfold minB; omega)
lemma certificate (s j:ℕ) : P.birthF 3 s (etui P s j (cellar P F j)):=prince P s j (cellar P F j) (fresh P F j)
#check castor
#print axioms er
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
