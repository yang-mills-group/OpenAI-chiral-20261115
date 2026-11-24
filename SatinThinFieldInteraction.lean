import SatinFixedContrastNovember4
import SatinThinQuizMargin
/-!
# Physically supplied six-channel experiment on the shrinking-footprint fields

We have full rank in the actual minus canonical raw factorization test,
with both one-point answers ZERO. With the earlier width-retaining test of
SatinFixedContrastNovember4 directly re-elected here-- on the same
Spine, course, trajectory (same coupling normalization, etc.), fixed i, wall 0, all
six Clan labels, positions, smearing weights. The new `FullPrismLab` prices
are for THIN fields in this Euclidean problem: strong one-field vectors
at each of the chosen smears on the vacuum (earlier from the oppositely posed test),
x's actual character readings and the kernel throughout positive time order,
response agrees with limit of actual-state-to-raw-comparison difference on the two ordered smears thereof.
`-QuizMargin, -QuizPair` give details and `-QuizLevel` the general estimate.
No claim of *isolated, irreducible matter species propagation* beyond `ReturnsSix`-type
data: each probe label is preserved in exactly its gauge-**matter** `thinMat Z`
constituent (same with `kiss`) and each inquiry is strictly separated in both
physical time and all spatial axes. The gauge-sector scaffold enters
our joint estimate, and the limiting profiles use **different finite derivatives and/or
combinations of derivatives of a COMMON profile up to Clan-dependent scalars**.
The full-rank discrepancy on independent centered smears is meant in the program's
raw factorization criterion and true rank sense of this test. Not claiming Minkowski theory,
not asserting inference about component modes of matter alone: for an obstacle TEST and
further context/limits see the later estimates.
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
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six
-- arbitrary position Pair boxes as long as all axis positive and straddle our wall strictly by paid positive amount.
lemma elected_thin_interaction (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(d:ℝ)(w:0<d)(z:ℕ→ℕ):
 ∃ (n_:ℕ)(P:Spine)(K:P.Register), uniform P K Y L M ∧ P.Roster ∧ P.NightCop ∧ TintCommercial n_ (crayon X) P.par ∧
     Meritorious P.par ∧15 ∣ P.par.R.L.val∧ P.par.R.L.val %16 =1 ∧ Yoke.Dispatchers P.par ∧
     ∃ C≥(1:ℝ), Yoke.Drawbill P.par C ∧ (∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ, (P.run.voyage i).kick ≤ k→s≤P.run.uv k→Yoke.ShelterCost C P.run s i k)∧
     ∃ A:ℝ, Chronicle P.run A ∧ (∀ᶠ f:ℕ in atTop,∀ r:ℕ,∀ (e:f<r), ∀ v:ℕ, ∀ (u:r≤v), EarnedClockPlot P C A f r v e u) ∧
     ∃ c r:ℕ→ℕ, z≤r ∧ ∃ b> (0:ℝ), ∀ᶠ s:ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x),F x ∧ CruisePreparation P A C b K c r (P.pointEra s) s x R ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧ ∃ (u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x (P.pointEra s) s v a q u) n), (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x (P.pointEra s) s v a q u) c r n p X V (P.pointEra s) s) ∧
          ∀ (U W: Doorway), U.Later W thinAlongOrder 0 → ∀ μ:ℝ,0<μ→ U.upper 3 ≤ -μ → μ ≤ W.lower 3 →
            ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x (P.pointEra s) s v a q u) c r n p V (P.pointEra s) s X μ F G U W (c i) (r i) K :=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_armada X Y L M p d w z
 refine ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ.mono fun i p=> ⟨p.1,fun F h=>?_⟩⟩; obtain ⟨x,R,h,t,v,a,V,u,Q,X,N,d,u',b'⟩:= p.2 F h
 refine ⟨x,R,h,t,v,a,V,u,Q,X,N,d,u',fun F F' e m m' l i' =>?_⟩
 filter_upwards [b' F F' e m m' l i'] with j h; obtain ⟨D₁,D₂,w',H⟩:= h; exact ⟨D₁,D₂,w',P.honorLab x _ _ _ _ _ _ _ _ _ (u' w') R _ _ _ _ _ _ _ _ e l i' H⟩

-- in particular the concrete boxes. arbitrary supplier data in this theorem.
lemma interaction_review (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ): ∃(P:Spine)(K:P.Register), uniform P K Y L M ∧ ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), z ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n), (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x f s v a q u) c r n p X V f s) ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i) (r i) K:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_thin_interaction X Y L M p 1 zero_lt_one z
 obtain ⟨i,_,s⟩:= ρ.exists
 obtain ⟨x,R,_,t,v,a,V,u,Q,X,N,d,T,f⟩:= s (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 exact ⟨P,K,e,x,R,c,r,h,t.setup, P.pointEra i,i,v,a,u,Q,X,N,d,T, f reviewEarlierBox reviewLaterBox thinEarlier _ zero_lt_one (le_refl _) (le_refl _)⟩ -- uniform check
-- NO hypotheses. The choice of geometry is allowed after the x selection. The smears, anchor,
-- and mark mask p can be chosen at any late fixed i, in reviewEarlierBox and reviewLaterBox
-- (ordinary unit boxes with separation at least 2; -Front.thin_separation).
lemma actual_separated_thin_field_interaction :
    let Y:Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Y 1 1 ∧
    ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), id ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n), (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x f s v a q u) c r n p X V f s) ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i) (r i) K:= interaction_review (fun _ _ _ _ _ _=> 0) _ _ _ zero_lt_one id

#check @actual_separated_thin_field_interaction
#check @elected_thin_interaction
#check @interaction_review
#print axioms actual_separated_thin_field_interaction
#print axioms elected_thin_interaction
#print axioms interaction_review
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
