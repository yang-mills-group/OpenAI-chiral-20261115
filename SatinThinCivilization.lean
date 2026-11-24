import SatinFixedContrastNovember4
import SatinThinCourt
import SatinThinWarp

/-! # Estimates on the CONTINUOUS cost ambitions for the *excited comparison*.
       Public checkpoint before using it to lower-compare. See Warp.layout_receipt. -/
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
/-! Continuing the interaction-direction work: first projections earned. -/
theorem progressive (X: TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ) :
    ∃ n_:ℕ, ((2:ℝ)*Ione.strive_E 6 ≤ (n_:ℝ)) ∧ ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ (∀ᶠ s:ℕ in atTop,∀ i k:ℕ,(P.run.voyage i).kick ≤ k→s≤P.run.uv k→VLine P.run s i k (SectorNext.Remainder.Scales.merit P.par.R.L (hat P.par.R.L P.par.x s))) ∧
      Yoke.Dispatchers P.par ∧
     (∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     (∃ A:ℝ, Chronicle P.run A ∧ ∀ᶠ f:ℕ in atTop,∀ r:ℕ, f < r→ ∀ v:ℕ,r ≤ v → ∀ᶠ i:ℕ in atTop, ∀ k:ℕ,(P.run.voyage i).kick ≤ k → v≤ P.run.uv k→ Yoke.PaysTilt P.run i k f r v A) ∧
    ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3),z≤r ∧ ∃ J:P.Ellis 3 x, Spine.Experiment P K c r x J ∧ P.Transmission x c r ∧
        ∀ (U V : Doorway) (order : Orders), U.Later V order 0 → ∀ᶠ i : ℕ in atTop,
          ∃ (a : ℝ) (F G : SampleDose), F.Normalized ∧ G.Normalized ∧
            tsupport F.val ⊆ U.invites ∧ tsupport G.val ⊆ V.invites ∧
            P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G := by
  obtain ⟨n_,wn⟩:= exists_nat_gt ((2:ℝ)*Ione.strive_E 6)
  obtain ⟨P,K,h,hs,⟨⟨⟨A,M₀,g0,h0⟩,X',Y'⟩,Dh⟩,c,r,x,hv,J,w,Xt⟩ := transactVector (Yoke.dispatch_commission (Yoke.draw_grants (minister (crayon X) n_))) Y L M p z
  refine ⟨n_,wn.le,P,K,h,hs,A,M₀,g0,h0, ?_,Dh,?_,?_, c,r,x,hv,J,w,Xt,?_⟩
  · simpa only [one_mul] using line_merit P.run 1 zero_lt_one M₀
  · have ht:1 ≤ X':=by obtain ⟨a,b,N,e,f,Ra,Rb,t⟩:=Y'.bought; rw [Ra]; nlinarith only [sq_nonneg (45*(1+b)),sq_nonneg (1+b)]
    exact ⟨X',ht,Y',Yoke.costs P.run M₀ Dh Y' (zero_le_one.trans ht)⟩
  · obtain ⟨Pay,kC,Γ,Tξ,u,v,s,q,y,p1,p2,πx,m⟩:= A.fromCrew; obtain ⟨A',t⟩:= crisps P.run Pay kC Γ Tξ y (sky_Line P.run (m.marble (by rw [P.par.kJ]; exact ⟨2,rfl⟩) P.par.kJ.ge u v q s p1 p2 2 (by simpa using wn.le)) hs.prepared) q s πx hs.prepared; exact ⟨A',t,Yoke.purchase_series P.run t⟩
  intro U V order sep
  let b : Fin 3 → Bool := fun _ => false
  obtain ⟨p, e, _he, _inside, hcost⟩ := authorize b
  filter_upwards [packs_within_rectangles Xt (Metric.ball p e) b hcost U V order sep] with i hi
  obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2
  exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast K x _ _ a F G hR⟩
#check progressive
#print axioms progressive
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
