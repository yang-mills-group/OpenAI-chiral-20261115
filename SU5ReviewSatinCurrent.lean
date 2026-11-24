import Quarry.Receipt
import Finch.Sector
import YM.SU5.LitCurrent.Candle

/-! The marked regulator estimates from Quarry, Finch and Candles on a
single preparation, register and selected character. The finite estimates
retain the respective insertion and denominator in each formulation. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


theorem markedCurrentOnOneElection (Mc : ℕ) :
    ∃ (P : Spine) (K : P.Register) (x : P.Spectrum0 3),
      JointTuple.{uΩ} P K x ∧ Rocky P K Mc ∧ CathedralQ P ∧
      SingleRootFinance P ∧ LitFuture P Mc ∧ P.UnderLease P.jump128 0 := by
  obtain ⟨n,h⟩ := exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
  have hz : 0 ≤ strive_E 6:=by unfold strive_E Jet.composeCost; positivity
  obtain ⟨P,K,q,r,H,⟨T,t⟩,mY,_,hv,hy,_,⟨C,_,_,p⟩,A,k⟩ :=
    bookedS n (le_trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ)≤2+Mc) hz) h.le)
      (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m⟩:= T.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  have hr : Rocky P K Mc := ⟨q,r,H,hy,ht,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,
    visa_onPath P.run r.prepared t,mY,⟨Pay,kC,Γ,Tξ,n,
    bandRadius P.run ((RateCover.includes _ _ _ m).staysOn
      (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2 Mc
       ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared⟩,
    A,C,k,p⟩
  have evenLevel : Even P.par.K.j := by rw [P.par.kJ]; exact ⟨2, rfl⟩
  have cover := RateCover.includes _ _ _ m
  have jet := _root_.Zephyr.Chern.SprigFee.paid P
  have hl : LitFuture P Mc :=
    ⟨hr.tile, hr.ro, t, hr.stepR, Preparation.postpaid P.run cover r.prepared, jet, hr.slot,
      Preparation.warmDust P.run (cover.fuels evenLevel P.par.kJ.ge u v Z s p1 p2) r.prepared⟩
  obtain ⟨x, _, htuple⟩ := hr.select (fun _ => True) (Eventually.of_forall fun _ => trivial)
  exact ⟨P, K, x, htuple, hr, cathedral_buy hr,
    singleRootSupported P hr.ro hr.stepR hr.visa jet, hl,
    P.scheduleLease hl.roster hl.payment hl.season hl.rate _ P.jump_pos 0⟩

#print axioms markedCurrentOnOneElection
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
