import SatinFixedContrastNovember4
import YM.SU5.Six.Provider
import Thin.Attic
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
/-- `Tailor.installation`, preserving the other certificates on the run. -/
theorem install_for_SixTh (wp:Pledge) (X:Supplier)(e u:ℝ)(p:0<u) :
    ∃ (P:Spine) (R:P.Register), uniform P R X e u ∧ Stairs P.par wp ∧ P.Roster :=by
  obtain ⟨x,c,q⟩:= Papal.audit_weather 4 (by decide)
  obtain ⟨Λ,l,Z,v,pL,S,Q,A0,ST,K,H,Y,U,Pr,Lo,k,d,w,C,t,a,k',I,E,L,B,T',t',W,A⟩:=
      Papal.elite_atticTh wp e (min x u) (lt_min c p) X
  let V:= W.univ_; obtain ⟨G⟩:= extend_ground Y H V
  let P:Spine:=⟨Λ,l,Y,H,a,k',I,E,V,G⟩
  obtain ⟨x',v₀⟩:=q Λ.d Λ.dpos.le (pL.trans (min_le_left ..))
  exact ⟨P,⟨(L,B,T',t'),W⟩,⟨⟨K,v,pL.trans (min_le_right ..),A, ⟨k,d,w,Z,C,t,Q,S⟩,
        x', (Λ.kJ.symm ▸ v₀: Procurement Λ.K.j x' Λ.d)⟩, A0⟩,
ST,⟨U,Pr,Lo⟩⟩


open Regis.Head Regis.Head.Brecht Spine
open Aria Casting Six Ballad
lemma experiment_stairs (wp:Pledge) (L M:ℝ)(p:0<M)(Y:Supplier)(z:ℕ→ℕ) :
    ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ Stairs P.par wp ∧ P.Roster ∧
      ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3), z≤r ∧ ∃ J:P.Ellis 3 x, Experiment P K c r x J ∧ Transmission P x c r:=by
  obtain ⟨P,K,h,A,Tk⟩:=install_for_SixTh wp Y L M p
  obtain ⟨r,e,c,B,q,y,m',α,t,a,b,g,R,w⟩:= Prototype.summit_on P K h 1 one_pos z
  obtain ⟨n,x,H,U,V,T,G,J,A0,E,F⟩:= w.exists
  have ex:Experiment P K c r x J:=⟨B,T,H,A0,E⟩
  exact ⟨P,K,h,A,Tk,c,r,x,e,J,ex,trans6 ex⟩

#print axioms experiment_stairs
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
