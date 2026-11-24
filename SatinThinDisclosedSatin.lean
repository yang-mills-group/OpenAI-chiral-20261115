import SatinFixedContrastNovember4
import SatinThinDisclosedMixed

/-!
# One exact experiment on this law. Disclose the limit and the comparison.

Read `-QuizMargin` FullPrismLab, `-QuizPair` AuthorizedPair, etc. for the main
assertions (Lean notation as in this project). For obstruction test use UsesReproof.

Provides one `reviewTwoFixedProbes` witness, also with the general availability
`P.Transmission` and *universally* re-bought reviewElectedFixedContrast
(as in the public theorem but on THIS same P,K,c,r,x). Work on the
project's physical course:
- e.g. use `Spine.bare_chiral`, `six_families` from `YM/SU5/Six/Elected` on this P;
- `Spine.input_formula`, `input_order`, `common_reading` also there,
  for regulator context of this state (the path limits there are for the
  unselected E probes; doesn't replace the character computation);
- choose templates for same clan labels as that `Spine.Experiment`, and at
  measure again compare to `Spine.thinSplit`, the uniquely determined `Six.Comparison`,
  also at each later level. Maintain physically budgeted implementation and
  reinterpretation on that dictionary, NOT factorization on before-motion components.
Note `SatinThinFieldInteraction` and `SatinThinReproofEnd` for the corresponding
key applications, also with probes selected *eventually* at fixed experiment
heights (select one such here). This last strengthening `-Disclosed*` shows
both probes of comparison actually have NEITHER raw-pure type at fine enough
resolution (for the very smear's prepared polynomial), and gives the marginal
cost algorithms termwise via presentations.

Does not assert a *joint smeared-operator limit* on a domain -- it's convergence
to smeared fields on the vacuum in the Euclidean separated 1- and 2-point sense.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

private lemma fixed_ready (P:Spine)(K:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3)(T:P.Transmission x c r): ∀ (U V:Doorway)(o:Orders),U.Later V o 0 →∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites∧
    P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G:=by
 intro U V o p; obtain ⟨v,e,_,_,h⟩:= Spine.authorize (fun _=>false); filter_upwards [Spine.packs_within_rectangles T _ _ h U V o p] with i w
 obtain ⟨a,F,G,l,q,s,r,t,_⟩ := w.2
 exact ⟨a,F,G,l,q,r,t,s,P.reviewWardContrast K x _ _ _ _ _ s⟩

open Regis.Head Regis.Head.Brecht
-- No hypotheses; remember all mathematical terms in THIS question are in the
-- supplied normalized program. In particular no claim about physical readings
-- outside this operational definition.
theorem disclosed_satin_witness :
    let Ω':Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Ω' 1 1 ∧
    (∀ i k:ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta=P.par.x) ∧
    ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3)(R:P.Ellis 3 x), id ≤ r ∧ Experiment P K c r x R ∧
    P.Transmission x c r ∧
    (∀ (U V:Doorway)(order:Orders),U.Later V order 0 →∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites ∧
        P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G) ∧
    ∃ (i₀:ℕ)(F G:SampleDose), F.Normalized∧G.Normalized ∧ tsupport F.val⊆ reviewEarlierBox.invites ∧ tsupport G.val⊆ reviewLaterBox.invites ∧
        P.ReturnsSix x (c i₀) (r i₀) 0 F G ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F G ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n) (p:Lead.Clan→ SatinJets.Prism),
       P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K ∧
       (∃ A'∈reviewEarlierBox.invites, ∃ B'∈ reviewLaterBox.invites,P.UsesReproof x (P.cinema x f s v a q u) c r n p V f s X F G (c i₀) (r i₀) K A' B') ∧
       ∀ᶠ i:ℕ in atTop,∀ t:ℕ, c (n i) ≤ t→ P.SimultaneousDisclosure x (P.cinema x f s v a q u) c r n p F G i t:= by
 intro Ω'
 obtain ⟨P,K,e,x,R,c,r,h,D,f,s,v,a,u,q,V,n,X,p,w⟩:= thin_field_tested
 let Y:= trans6 D
 obtain ⟨i,F,G,z,A',f',B',h',T⟩:= w.exists
 let U:= T.toFullPrismLab
 exact ⟨P,K,e,P.terminalBeta K e,c,r,x,R,h,D,Y,fixed_ready P K c r x Y,i,F,G,T.keeps.normalized.1,T.keeps.normalized.2,T.keeps.earlier,T.keeps.laterProbe,T.keeps.fixed.1,T.keeps.fixed.2,f,s,v,a,u,q,V,n,X,z,U,⟨A',f',B',h',T⟩,P.plan_issued x _ c r n z V _ _ _ F G U⟩

#print axioms disclosed_satin_witness
#check @disclosed_satin_witness
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
