import SU5SatinProgressNovember7B
import ForceSatin.Normalize

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


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

/-- Prefix, not the full Lux estimate conjunction. When constructing Lux one must
retain these numerical approvals before choosing any P, as in ElectionA. -/
structure BornGrants (Λ:Preparation) (b C:ℝ) : Prop where
  projection : ∃ δ a, Λ.d ≤ δ ∧ 0<δ ∧ 0<a ∧ ∀ᶠ k:ℕ in atTop,∀ N:Side,k≤N.val → Sow 4 N a C δ
  positive : 0 < C
  shearPos : 0 < b
  mail : CF.Papyrus.Franc.postage 4 b
  credit : mixedMatrixFee b*(1+C) ≤ Λ.h

lemma BornGrants.earns {b C:ℝ}{P:Spine}(q : BornGrants P.par b C) (u:Meritorious P.par):
      ∀ᶠ s in atTop,∀ i k:ℕ,(P.run.voyage i).kick ≤ k → s≤P.run.uv k → TiltWorld P.run s i k b C := by
  obtain ⟨δ,a,b₀,p,h,H⟩:=q.projection
  exact tilt_unmarked P.run u (earnsTilt P.run b₀ p q.positive q.shearPos h H q.mail q.credit)

/-- Checkpoint. Reissue markedCurrentOnOneElection on the same preparation & Spine being
used to purchase the tilt. Price is on the chiral functional, on each finite history as in
EB.4. All preparation requirements needed so far by the argument are met **on this one
object**. P is not uniquely determined—we prove a prefix of EA timeline, and the work may
need re-issuing with further numerical thresholds as more of Lux is proved. Character selection
ready for additional conull criteria. -/
theorem sameBornElection (M L : ℕ) (d h' βmin : ℝ) (hd : 0 < d) :
    ∃ (P : Spine) (K : P.Register) (n:ℕ) (b C : ℝ),
      2*strive_E 6 < (n:ℝ) ∧ L ≤ P.par.R.L.val ∧ P.par.R.L.val%16=1 ∧ 15 ∣ P.par.R.L.val ∧
      TintCommercial n (crayon (fun _ _ _ _ _ _=>0)) P.par ∧ Solstitial P.par ∧
      Rocky P K M ∧ CathedralQ P ∧ SingleRootFinance P ∧ LitFuture P M ∧
      P.UnderLease P.jump128 0 ∧ h' ≤ P.par.h ∧ P.par.d ≤ d ∧ βmin < P.par.x ∧
      BornGrants P.par b C ∧
      (∀ᶠ s in atTop,∀ i k:ℕ,(P.run.voyage i).kick ≤ k → s≤P.run.uv k → TiltWorld P.run s i k b C) ∧
      ∀ good:P.Spectrum0 3→Prop, (∀ᵐ x ∂P.pillars 3,good x) → ∃ x, good x ∧ JointTuple.{uΩ} P K x := by
  -- Re-issuance. New permit: h and d chosen as in F/WA, before physical trajectory.
  obtain ⟨δ,a,C,hδ,ha,hC,E⟩:= Checkers.warm 4 (by decide)
  obtain ⟨b,hb,F⟩:= CF.Papyrus.Franc.grantH 4 (by decide)
  let μ:Supplier:=fun _ _ _ _ _ _ _ _ _ _ _ _=> max (mixedMatrixFee b*(1+C)) h'
  obtain ⟨n,h⟩ := exists_nat_gt ((2+(M:ℝ))*strive_E 6)
  have hz : 0 ≤ strive_E 6:=by unfold strive_E Jet.composeCost; positivity
  have hj : (2:ℝ)*strive_E 6 < n := (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ)≤2+M) hz).trans_lt h
  let X:TintDemand := fun _ _ _ _ _ _=>L
  obtain ⟨P,K,q,r,H,⟨T,t⟩,mY,hk,hv,hy,_,⟨C',_,_,p⟩,A,k⟩ :=
    bookedS n hj.le X μ (max βmin 1) (min d (min δ 1)) (lt_min hd (lt_min hδ zero_lt_one))
  obtain ⟨qz,vz,r₀,z₁,z₂,g,f,gx⟩:=q.1.paper
  have he':P.par.d ≤ min δ 1:= q.1.walls.trans (min_le_right ..)
  have α : mixedMatrixFee b*(1+C) ≤ P.par.h:=(le_max_left ..).trans gx
  have hV : uniform P K blankSupplier 1 1 := ⟨{ q.1 with meets := (le_max_right ..).trans_lt q.1.meets,
                                                             walls := he'.trans (min_le_right ..),
                                                             paper := ⟨_,_,_,_,_,g,f,zero_le_one.trans P.par.height⟩ }, q.2⟩
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m⟩:= T.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  have hr : Rocky P K M := ⟨hV,r,H,hy,ht,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,
    visa_onPath P.run r.prepared t,mY,⟨Pay,kC,Γ,Tξ,n,
    bandRadius P.run ((RateCover.includes _ _ _ m).staysOn
      (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2 M
       ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared⟩,
    A,C',k,p⟩
  have evenLevel : Even P.par.K.j := by rw [P.par.kJ]; exact ⟨2, rfl⟩
  have cover := RateCover.includes _ _ _ m
  have jet := _root_.Zephyr.Chern.SprigFee.paid P
  have hl : LitFuture P M :=
    ⟨hr.tile, hr.ro, t, hr.stepR, Preparation.postpaid P.run cover r.prepared, jet, hr.slot,
      Preparation.warmDust P.run (cover.fuels evenLevel P.par.kJ.ge u v Z s p1 p2) r.prepared⟩
  have hB : BornGrants P.par b C:= ⟨⟨δ,a,he'.trans (min_le_left ..),hδ,ha,E⟩,hC,hb,F,α⟩
  refine ⟨P,K,n,b,C,hj,(le_max_left ..).trans y,hv,hk,⟨Pay,kC,Γ,Tξ,u,v,s,Z,?_,p1,p2,πx,cover⟩,t,
          hr,cathedral_buy hr,singleRootSupported P hr.ro hr.stepR hr.visa jet,hl,P.scheduleLease hl.roster hl.payment hl.season hl.rate _ P.jump_pos 0,
          (le_max_right ..).trans gx,q.1.walls.trans (min_le_left ..),(le_max_left ..).trans_lt q.1.meets,hB,hB.earns mY,fun good hg=> hr.select good hg⟩
  unfold crayon; dsimp only; exact (max_le (Nat.zero_le _) ((le_max_right ..).trans y))

end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
