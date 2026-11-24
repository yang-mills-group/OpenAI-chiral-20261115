import SatinFixedContrastNovember4
import SatinThinPlant
import SatinThinFeather
import YM.SU5.Six.Provider

-- installVector: supplement to install_for_Six (body uses elite_vector)
import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Voyager.Canyon

/-!
# Binding the Satin supply for the Six

* `install_for_Six` (version of `installation` retaining physical
  hypotheses on the SAME `P.run`).
* `summit_on` (version of `Prototype.summit` accepting the supplied
  `uniform` `P`).
* `Spine.SixElection` (only phase and UV hypotheses needed, no probe
  specific decisions); `elect_for_Six`.

No strengthening of the coupling-existence quantifier to a prescribed
value of `P.par.x`. Run, register and character are fixed, not e.g.
re-picked at each probe scale.
-/
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
theorem installVector {RΘ:Preparation→Prop}(FΘ: CommissionVector RΘ) (X:Supplier)(e u:ℝ)(p:0<u) :
    ∃ (P:Spine) (R:P.Register), uniform P R X e u ∧ P.Roster ∧ RΘ P.par :=by
  obtain ⟨x,c,q⟩:= Papal.audit_weather 4 (by decide)
  obtain ⟨Λ,l,Z,v,pL,S,Q,A0,Xφ,K,H,Y,U,Pr,Lo,k,d,w,C,t,a,k',I,E,L,B,T',t',W,A⟩:=
      Papal.elite_vector FΘ e (min x u) (lt_min c p) X
  let V:= W.univ_; obtain ⟨G⟩:= extend_ground Y H V
  let P:Spine:=⟨Λ,l,Y,H,a,k',I,E,V,G⟩
  obtain ⟨x',v₀⟩:=q Λ.d Λ.dpos.le (pL.trans (min_le_left ..))
  exact ⟨P,⟨(L,B,T',t'),W⟩,⟨⟨K,v,pL.trans (min_le_right ..),A, ⟨k,d,w,Z,C,t,Q,S⟩,
        x', (Λ.kJ.symm ▸ v₀: Procurement Λ.K.j x' Λ.d)⟩, A0⟩,
      ⟨U,Pr,Lo⟩, Xφ⟩

/-- For passing also further purchases through the election. -/
theorem transactVector {RΘ:Preparation→Prop}(F:CommissionVector RΘ)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ):
 ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ RΘ P.par ∧∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3),z≤r ∧ ∃ J:P.Ellis 3 x, P.Experiment K c r x J ∧ P.Transmission x c r := by
 obtain ⟨P,K,T,x,T'⟩:= installVector F Y L M p
 obtain ⟨r,e,c,B,q,y,m',α,t,a,b,g,R,w⟩:= Prototype.summit_on P K T 1 one_pos z
 obtain ⟨n,x₀,H,U,V,T₀,G,J,A,E,F⟩ := w.exists
 let Φ:Spine.Experiment P K c r x₀ J:=⟨B,T₀,H,A,E⟩
 exact ⟨P,K,T,x,T',c,r,x₀,e,J,Φ,Spine.trans6 Φ⟩

open Spine Pitching.Focus
/-- Earn the near-step impulse estimate *on the course supplied also with the
 separated full-rank fixed-width measurement* (world, transmission, elected
 character even the same). See `TintCommercial` & `Feather.pays`.
 -/
theorem mayoral (X:TintDemand)(n_ :ℕ)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ) :
    ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ TintCommercial n_ X P.par ∧
     (∃ (Pay kC Γ:ℝ)(Tξ:Hove.Grant P.par.K.j 2), 0≤Pay∧0≤kC∧0≤Γ∧Taxi.DayT 6 Γ∧X P.par.K P.par.L Pay kC Γ Tξ ≤ P.par.R.L.val∧ InkCover P.par.J Chi.canonical P.par.h P.par.N0 Pay kC Γ Tξ n_ P.par.P∧ Feather P.par.J Chi.canonical P.par.h P.par.N0 Pay kC Γ Tξ n_ P.par.P) ∧
    ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3),z≤r ∧ ∃ J:P.Ellis 3 x, Spine.Experiment P K c r x J ∧ P.Transmission x c r ∧
        ∀ (U V : Doorway) (order : Orders), U.Later V order 0 → ∀ᶠ i : ℕ in atTop,
          ∃ (a : ℝ) (F G : SampleDose), F.Normalized ∧ G.Normalized ∧
            tsupport F.val ⊆ U.invites ∧ tsupport G.val ⊆ V.invites ∧
            P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G := by
  obtain ⟨P,K,h,hs,A,c,r,x,hv,J,w,Xt⟩ := transactVector (mayor X n_) Y L M p z
  refine ⟨P,K,h,hs,A,?_,c,r,x,hv,J,w,Xt,?_⟩
  · obtain ⟨Pay,kC,Γ,Tξ,u,v,s,q,y,p1,p2,πx,m⟩:= A.fromCrew
    exact ⟨Pay,kC,Γ,Tξ,u,v,s,q,y,m,m.vends (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v q s p1 p2⟩
  intro U V order sep
  let b : Fin 3 → Bool := fun _ => false
  obtain ⟨p, e, _he, _inside, hcost⟩ := authorize b
  filter_upwards [packs_within_rectangles Xt (Metric.ball p e) b hcost U V order sep] with i hi
  obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2
  exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩
#check mayoral
#print axioms mayoral
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
