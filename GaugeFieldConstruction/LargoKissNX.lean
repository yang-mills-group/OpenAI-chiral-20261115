import GaugeFieldConstruction.ScoutPinNX
import GaugeFieldConstruction.WaltsQuotaNX
-- regulator reflection flips species's two generations with exact Spin cost. Body sizes unchanged.
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3600
set_option linter.unusedSectionVars false
set_option maxHeartbeats 70000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker InnerProductSpace Topology Classical
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}
open YM.CF.Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal (Weaver household)
open Kea
open Flare
namespace Lead
variable (A:Lead R)(k:VFlavorNX)(j w:Fin 2)
abbrev reverseRackNX(k:VFlavorNX):VFlavorNX:=(k.1,k.2.2,k.2.1)
lemma rotColorNX : bookColorNX (reverseRackNX k)=star (bookColorNX k):=by
 ext x y
 rw [Matrix.star_apply, bookColorNX, bookColorNX,YM.GaugeFieldConstruction.Flavor.wear,YM.GaugeFieldConstruction.Flavor.wear]
 by_cases h:x.2=y.2
 · rw [if_pos h,if_pos h.symm,h]
   rcases k with ⟨f,u,v⟩; simp [Pi.single_apply,reverseRackNX, and_comm] -- tune
 rw [if_neg h,if_neg (Ne.symm h),star_zero]
lemma rakeNX(U:SU.E) : VLeadNX (reverseRackNX k) U⁻¹ = star (VLeadNX k U):=by
 have h: (matter U).val * bookColorNX k= _:= YM.GaugeFieldConstruction.Matter.coeff_ok (Pi.single k 1) U; rw [VLeadNX,VLeadNX, map_inv,rotColorNX,←h,star_mul]; rfl
abbrev rotorCostNX (i:Axis)(j w:Fin 2):ℂ:= -(bkNX_scaledn i w*star (bkNX_scaleup i j))
lemma orbitingNX (N:Side)(i:Axis)(s:ℤ)(p q:SU.Slot) : let X:=A.mirror i s; theta (carR i s N) (Fock.remove (A.lowlightNX w N q)*create (A.highlightNX j N p))= rotorCostNX i j w • (Fock.remove (X.lowlightNX (shuffle i j) N p)* create (X.highlightNX (shuffle i w) N q)):=by
 intro X
 let F:= carR i s N; have hl:acts F.val (A.highlightNX j N p)= bkNX_scaleup i j • X.lowlightNX (shuffle i j) N p:=by
    unfold highlightNX lowlightNX F; rw [acted_basisC]; simp_rw [(bkNX_pinned i _ _).1, ite_smul, zero_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]; rfl
 have hv: acts F.val (A.lowlightNX w N q)= bkNX_scaledn i w • X.highlightNX (shuffle i w) N q:=by
    unfold highlightNX lowlightNX F; rw [acted_basisC]; simp_rw [(bkNX_pinned i _ _).2, ite_smul, zero_smul]; rw [sum_ite_eq',if_pos (mem_univ _)]; rfl
 rw [theta_mul,theta_upV,theta_downV]; change (Complex.I • create _) * (-Complex.I • Fock.remove _)=_
 rw [show acts _ (A.lowlightNX w N q)=_ from hv,show acts _ (A.highlightNX j N p)=_ from hl,map_smul,show ∀ (v:Ket (Single N))(z:ℂ), Fock.remove (z • v)=star z • Fock.remove v from (by intro v z; simp [Fock.remove]),smul_smul,smul_smul,Matrix.smul_mul, Matrix.mul_smul]
 rw [Afterglow.Tower.VacuumSelection.Spine.flipsPNX]; rw [smul_smul,smul_neg,← neg_smul,rotorCostNX,show Complex.I * _ * (-Complex.I * _) = bkNX_scaledn i w*star (bkNX_scaleup i j) by linear_combination (norm:=ring_nf) -(bkNX_scaledn i w*star (bkNX_scaleup i j))*Complex.I_mul_I] -- order tune
lemma spectralRollNX (i:Axis)(s:ℤ) : reflMark i s (A.rollNX k j w N) = rotorCostNX i j w • (A.mirror i s).rollNX (reverseRackNX k) (shuffle i w) (shuffle i j) N:=by
 let Q:= rotorCostNX i j w; let X:= A.mirror i s; funext U; let V:=fling i s N U.1
 change theta _ (∑ i:SU.Slot,∑ p:SU.Slot,VLeadNX k (A.laps V) i p • _) = Q • _
 unfold rollNX
 simp_rw[theta_sum]; rw [sum_comm,smul_sum]; apply sum_congr rfl; intro p h
 rw [smul_sum]; apply sum_congr rfl; intro q u
 rw [theta_smul]; rw [Afterglow.Tower.VacuumSelection.Spine.flipsPNX,Afterglow.Tower.VacuumSelection.Spine.flipsPNX]
 have hn(v:FC (Single N)): theta (carR i s N) (-v)= -theta (carR i s N) v:=by unfold theta; simp
 rw[hn, orbitingNX]
 rw [show VLeadNX (reverseRackNX k) _ p q=star (VLeadNX k (A.laps V) q p) from (by rw [mirror_laps,rakeNX]; rfl)]
 rw[smul_neg,smul_neg,smul_neg,smul_comm]
#print axioms spectralRollNX
end Lead
end YM.CF.Buffered.Ballad
end
