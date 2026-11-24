import YM.SU5.Assay.Admission
import YM.SU5.Assay.FlashGain
import YM.SU5.Six.Provider
import YM.SU5.Six.Trans6
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

/-- Installation retaining all data for the six. Cf. Six/Provider. -/
theorem install_admitted {Lux:Preparation →Prop}(V':Admission Lux)(X:Supplier)(e u:ℝ)(p:0<u):∃ (P:Spine) (R:P.Register), uniform P R X e u ∧ P.Roster ∧ Lux P.par:=by
  obtain ⟨x,c,q⟩:= Papal.audit_weather 4 (by decide)
  obtain ⟨Λ,l,Z,x0,v,pL,S,Q,A0,K,H,Y,U,Pr,Lo,k,d,w,C,t,a,k',I,E,L,B,T',t',W,A⟩:=
      Papal.elite_admission V' e (min x u) (lt_min c p) X
  let V:= W.univ_; obtain ⟨G⟩:= extend_ground Y H V
  let P:Spine:=⟨Λ,l,Y,H,a,k',I,E,V,G⟩
  obtain ⟨x',v₀⟩:=q Λ.d Λ.dpos.le (pL.trans (min_le_left ..))
  exact ⟨P,⟨(L,B,T',t'),W⟩,⟨⟨K,v,pL.trans (min_le_right ..),A, ⟨k,d,w,Z,C,t,Q,S⟩,
        x', (Λ.kJ.symm ▸ v₀: Procurement Λ.K.j x' Λ.d)⟩, A0⟩,
      ⟨U,Pr,Lo⟩,x0⟩

open CF.Papyrus.Franc
open Spine
lemma money_taste : DoorMoney Tasting.Paid:=by
 obtain ⟨u,t,n,v⟩:=winter 4 (by decide)
 obtain ⟨d,g,w,F⟩:= Meshy.vanguard
 obtain ⟨C,c,p⟩:= grantH 4 (by decide)
 refine ⟨min u d, lt_min t g,fun _ _ _ _ _ _ _ _ _ _ _ _=> CF.Papyrus.Franc.charge C,?_⟩
 intro P l Z h θ Y
 obtain ⟨θ,σ⟩:=le_min_iff.mp θ
 refine ⟨h,⟨C,P.kJ.symm ▸ p,c.le,Y⟩,⟨u,θ,?_⟩, (eventually_ge_atTop w).mono fun i h n b=> F _ P.dpos.le σ _ (h.trans b)⟩
 rw [P.kJ]; exact ⟨_,v⟩

lemma macro_on {P:Spine}{K:P.Register}{L M:ℝ}{Y:Supplier} (h:uniform P K Y L M)(z:ℕ→ℕ):
   ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3),z≤r ∧ ∃ J:P.Ellis 3 x, Experiment P K c r x J ∧ Transmission P x c r:= by
 obtain ⟨r,t,c,x,v⟩:=elect_for_Six P K h z
 have B:Experiment P K c r x v.ellis:=⟨v.launch,v.ready,v.choose,v.deck,v.summit⟩
 exact ⟨c,r,x,t,v.ellis,B,trans6 B⟩

theorem macro_with {Lux:Preparation →Prop}(v:Admission Lux)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ):
    ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ Lux P.par ∧ Tasting.Paid P.par ∧
      ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3),z≤r ∧ ∃ J:P.Ellis 3 x, Experiment P K c r x J ∧ Transmission P x c r:= by
 obtain ⟨P,K,h,s,g,W⟩:=install_admitted (v.fund money_taste) Y L M p
 exact ⟨P,K,h,s,g,W,macro_on h z⟩
#print axioms macro_with
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
