import YM.SU5.SatinWard.Resolution.FuelZ
import YM.SU5.SatinWard.Resolution.Recital
import YM.CF.Lattice.Covariant
import YM.CF.Operator.Commute
set_option autoImplicit false
set_option maxHeartbeats 420000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Mezzo
open Function NormedSpace Lattice Laurent Finset Cube Lat Fock Tulip Peaks Drapes SU Ember
open Rush Scroll Paige Spire Fir Bloch Next.Free Dial Tap
open scoped Topology Matrix MatrixOrder Kronecker Classical BigOperators InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {g:UNI SU.Slot}{N:Side}
local notation "U'"=> singlet N g
local notation "D"=> duet N g
lemma twirls_frame (k:Registrar g)(x:Bkg N)(b:Site N):
 twist D (frame SU.matter x b).H=(frame SU.matter x b).H:=by
 let F :=frame SU.matter x b; let G:=twist D
 have hi (A:Op SpinIdx): G (spin N Slot A)=spin N Slot A:=by
    have hx:= roseHead N g A 1; rw [map_one] at hx; apply still_U.mpr
    have hk:=(still_U.mp hx).eq; rw [← love_coat] at hk; exact (love N).injective (show love N _=love N _ from Eq.trans (map_mul ..) (hk.trans (map_mul ..).symm)) -- p.comm
 have ht(i:Axis): G (F.T i)= F.T i:=by
    apply Mir.twist_comm; change ((1:Op (Site N))⊗ₖ (pal g).val)* Lat.shift SU.matter _ _ _= _*_; unfold Lat.shift; change ((1:Op (Site N))⊗ₖ (pal g).val)*jump _ _= jump (advance i) (Lat.hop _ x b i)*((1:Op (Site N))⊗ₖ (pal g).val); rw [←jump_replicate,jump_mul,jump_mul,Equiv.refl_trans,Equiv.trans_refl]
    congr 1; ext1 y; apply Commute.smul_right; apply still_U.mp
    change twist (across SpinIdx g) ( _ ⊗ₖ _) = _; rw [twistLook,k _]; rfl -- tune
 have hg (i:Axis): G (F.inc i)= F.inc i:=by simp only [WilsonFrame.inc,WilsonFrame.lap,WilsonFrame.diff,map_add,map_sub,map_neg,map_one,map_smul,map_mul,map_star,ht]; rw [show G (F.gamma i)= F.gamma i from hi _]
 unfold WilsonFrame.H; change G (F.chir*F.H0)=_; rw [map_mul,show G F.chir=F.chir from hi _]; simp only [WilsonFrame.H0,map_sum,map_add,map_neg,map_one,hg]; rfl
lemma twirls_projector (x:Bkg N)(b:Site N)(k:Registrar g)(u:Safe (frame matter x b).H): twist U' (portW (helix N).symm (projector (frame matter x b).H))= portW (helix N).symm (projector (frame matter x b).H):=by
 let F:= (frame matter x b).H; change twist _ (love N (projector F)) = _; rw [twist_formula,←love_coat,← map_star (love N),←map_mul, ← map_mul, ← twist_formula, projector_twist u,twirls_frame k]; rfl
end YM.CF.Mezzo
