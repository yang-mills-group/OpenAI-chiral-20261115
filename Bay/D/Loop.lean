import Bay.D.Oriole
import Bay.Estate
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine


open Buffered.Afterglow.Tower
open Buffered.Afterglow.Tower.VacuumSelection.Spine Pitching.Focus
open Push.SectorMeasure
open QuadClock Preparation.Yoke Ione
namespace D
universe u

lemma flotilla (Mc:ℕ)(X:TintDemand):
  ∃ (P:VΩ)(K:P.Register), DryDock P.par ∧ Hammer P Mc X ∧
    ∀ (good : P.Spectrum0 3 → Prop),
      (∀ᵐ x ∂ P.pillars 3, good x) →
      ∃ x,good x ∧ JointTuple.{u} P K x:=by
 obtain ⟨n,h⟩:=exists_nat_gt ((2+(Mc:ℝ))*strive_E 6)
 have hz :0≤ strive_E 6:= by unfold strive_E Jet.composeCost; positivity
 obtain ⟨P,K,q,r,H,⟨⟨⟨⟨⟨T,t⟩,j,y,hv,hy⟩,W⟩,N,L⟩,D⟩⟩ := installPoll (Yoke.dispatch_commission (Yoke.draw_grants (commission (ministerSeasons (crayon X) n)))) blankSupplier 1 1 zero_lt_one
 obtain ⟨Pay,kC,Γ,Tξ,v₀,v,s,Z,w,p1,p2,πx,m⟩:= T.fromCrew
 have ht : Odd P.par.R.L.val:= ⟨P.par.R.L.val/2,by omega⟩

 have ink:= RateCover.includes _ _ _ m
 have tc:TintCommercial n (crayon X) P.par:=⟨Pay,kC,Γ,Tξ,v₀,v,s,Z,w,p1,p2,πx,ink⟩
 have wn : (2:ℝ)*strive_E 6 ≤ (n:ℝ) :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg _)) hz).trans h.le
 obtain ⟨A',k⟩:= crisps P.run Pay kC Γ Tξ w
    (sky_Line P.run (ink.marble (by rw [P.par.kJ]; exact ⟨2,rfl⟩)
        P.par.kJ.ge v₀ v Z s p1 p2 2 (by simpa using wn)) r.prepared)
    Z s πx r.prepared
 have p:= Yoke.costs P.run j D L
    (show 0≤N by obtain ⟨a,b,N,e,f,Ra,Rb,t⟩:=L.bought; rw [Ra]; positivity)
 exact ⟨P,K,⟨j,W⟩,⟨r.prepared,EarningsRate.atMask P.run (RateCover.stepRate m) r.prepared,
          visa_onPath P.run r.prepared t,
          ⟨r,⟨n,_,tc⟩,H,y,hv,j,D⟩,
          hy,n,Pay,kC,Γ,Tξ,h,v₀,v,s,Z,w,p1,p2,πx,m,
          bandRadius P.run (ink.staysOn (by rw [P.par.kJ]; exact ⟨2,rfl⟩)
          P.par.kJ.ge v₀ v Z s p1 p2 Mc
          ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by norm_num)) hz).trans h.le))
          r.prepared⟩,
      Buffered.Afterglow.Tower.VacuumSelection.Spine.reside.{u} P K q r H ht k p⟩


#print axioms flotilla
end D
end YM.CF.Bay
