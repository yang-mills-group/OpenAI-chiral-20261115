import Merino.Audience
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus

open QuadClock Preparation.Yoke

namespace Spine
universe u
-- For fixed finite number Mc of root-types available at each seat,
-- issue the OrbitPulse economics together with Reg.
open Ione Vow
open _root_.Zephyr.Chern YM.CF.Merino

/-- Election retains the meter, NightCop and Force credit inputs. -/
structure RibbonCourts (P:Spine)(K:P.Register)(x:P.Spectrum0 3)(Mc:ℕ):Prop where
   gala : Gala.{u} P K x Mc
   chilled : P.NightCop
   fire : ∃ C:ℝ, Yoke.Drawbill P.par C ∧ ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ k:ℕ,
                (P.run.voyage i).kick ≤ k→s≤P.run.uv k → Yoke.ShelterCost C P.run s i k
   thaw : ∃ A:ℝ, Chronicle P.run A

theorem courts (Mc:ℕ) :
   ∃ P K x,RibbonCourts.{u} P K x Mc:=by

  obtain ⟨n,h⟩:= exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
  have hz:0 ≤ strive_E 6:=by
      unfold strive_E Jet.composeCost; positivity
  obtain ⟨P,K,q,r,H,⟨T,t⟩,_,_,hv,hy,_,⟨C,_,J,p⟩,a,k⟩:=
    bookedS n (le_trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _):(2:ℝ) ≤ 2+Mc) hz) h.le) (fun _ _ _ _ _ _=>0) blankSupplier 1 1 zero_lt_one
  obtain ⟨Pay,kC,Γ,Tξ,u,v,s,Z,y,p1,p2,πx,m⟩:= T.fromCrew
  have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩
  obtain ⟨x,_,E⟩:= reside.{u} P K q r H ht k p (fun _=>True)
    (Eventually.of_forall fun _=>True.intro)
  exact ⟨P,K,x,⟨⟨E,hy,r,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,visa_onPath P.run r.prepared t, SprigFee.paid P,⟨Pay,kC,Γ,Tξ,n,
    bandRadius P.run ((RateCover.includes _ _ _ m).staysOn (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v Z s p1 p2 Mc ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le)) r.prepared⟩⟩,H,⟨C,J,p⟩,a,k⟩⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

