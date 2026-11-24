import Crape.Mean
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
variable (P:Spine)
local notation "K"=> P.calibration
-- as Test
abbrev wp (s:ℕ)(o:Cover): P.Test:= P.art (watch P s o) (aux_test (lining_test ..))
lemma color_wp(s:ℕ)(o:Cover) : wp P s o ∈ enclave K:= (enclave_spec P.calibration).mpr (lining_cov P.calibration o (P.run.meter.a s) (payday P s))
lemma birthWP {s:ℕ}(o:Cover)(h:(K).ℓ+22 ≤ nodeC o (3:Axis)):P.birthF 3 s (wp P s o):=by
 have p:wp P s o∈bay K (bands o 22) true:= lining_test ..
 refine P.criteria 3 s p ?_ (color_wp P s o); intro z q; have u:=bands_spec o q 3; rw [zero_add]; omega
lemma wp_val(s:ℕ)(o:Cover) : (wp P s o).val=watch P s o:=rfl
lemma wp_shift(s:ℕ)(o:Cover)(w:ℤ): P.shifts 3 w (wp P s o)=wp P s (slid P.calibration 3 w o):=Subtype.ext (coilT ..)
local notation "Lx"=>P.par.R.L
variable (s j:ℕ)(o:Cover)(b:Bool)(C D:ℕ→ℝ)
abbrev etui (P:Spine)(s j:ℕ)(o:Cover):= wp P s (orbitB P.par.R.L o (s-j))
lemma prince(o:Cover)(h:(K).ℓ+22 ≤ nodeC o (3:Axis)): P.birthF 3 s (etui P s j o):=by
 apply birthWP; rw [dutyT _ _ P.par.R.odd_side]; simp only [Pi.smul_apply,nsmul_eq_mul]
 apply h.trans
 apply le_mul_of_one_le_left (by omega)
 exact_mod_cast (show 1≤ P.par.R.L.val^(s-j) from Nat.one_le_of_lt (pow_pos P.par.R.L.property _))

abbrev dress (P:Spine)(s j:ℕ)(o:Cover)(b:Bool)(C D:ℕ→ℝ):P.Test:= tokenA P (s:=s) (j:=j) b C D • etui P (s+1) j o + tokenB P (s:=s) (j:=j) b • P.conveying s (s+1-s) (etui P s j o)
lemma dress_val: (dress P s j o b C D).val=invoice P s j o b C D:=by rw [dress,show s+1-s=1 by omega]; rfl
variable (h:(P.calibration).ℓ+22 ≤ nodeC o (3:Axis))
include h
lemma birthDress: P.birthF 3 (s+1) (dress P s j o b C D):= P.birthAdd _ (P.birthScale _ _ (prince P (s+1) j o h)) (P.birthScale _ _ (P.rig 3 s (s+1) (prince P s j o h) (Nat.le_succ _)))
lemma billDress(x:P.Spectrum0 3): P.viewF 3 x (s+1) (birthDress P s j o b C D h)= tokenA P (s:=s) (j:=j) b C D • P.viewF 3 x (s+1) (prince P (s+1) j o h) + tokenB P (s:=s) (j:=j) b • P.viewF 3 x s (prince P s j o h):=by
 change P.viewF 3 x (s+1) (P.birthAdd _ (P.birthScale _ _ (prince P (s+1) j o h)) (P.birthScale _ _ (P.rig 3 s (s+1) (prince P s j o h) (Nat.le_succ _))))=_
 let l:= prince P (s+1) j o h; let k:= prince P s j o h; let f:=P.rig 3 s (s+1) k (Nat.le_succ _)
 exact (P.view_plus x (s+1) (P.birthScale _ (tokenA P (s:=s) (j:=j) b C D) l) (P.birthScale _ (tokenB P (j:=j) (s:=s) b) f)).trans (congrArg₂ (·+·) (P.sixWard_view_scale x (s+1) _ l) ((P.sixWard_view_scale x (s+1) (tokenB P (s:=s) (j:=j) b) f).trans (congrArg (fun w:P.ColorHil 3 x=>tokenB P (s:=s) (j:=j) b • w) (P.view_rig 3 x s (s+1) k (Nat.le_succ _)))))
#check prince
#print axioms billDress
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
