import YM.SatinExist.Marina
import YM.SatinExist.Warsaw
import YM.SatinExist.Votes
import YM.SatinExist.Lazul
import YM.SatinExist.Prices
import YM.SatinExist.Polynomial
import YM.SatinExist.ThermalJet
import SatinProbeCompatibilityNovember6
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 680000
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

private lemma fixed_readyAPS (P:Spine)(K:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3)(T:P.Transmission x c r): ∀ (U V:Doorway)(o:Orders),U.Later V o 0 →∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites∧
    P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G:=by
 intro U V o p; obtain ⟨v,e,_,_,h⟩:= Spine.authorize (fun _=>false); filter_upwards [Spine.packs_within_rectangles T _ _ h U V o p] with i w
 obtain ⟨a,F,G,l,q,s,r,t,_⟩ := w.2
 exact ⟨a,F,G,l,q,r,t,s,P.reviewWardContrast K x _ _ _ _ _ s⟩

open Regis.Head Regis.Head.Brecht
open SatinJets
theorem diva_pricedSnap :
    let Ω':Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Ω' 1 1 ∧ EpochPair P ∧ Defer P.par ∧ P.Roster ∧
    (∀ i k:ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta=P.par.x) ∧
    ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3)(R:P.Ellis 3 x), id ≤ r ∧ Spine.LargeM P c r ∧ Experiment P K c r x R ∧
    P.Transmission x c r ∧
    (∀ (U V:Doorway)(order:Orders),U.Later V order 0 →∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites ∧
        P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G) ∧
    ∃ (i₀:ℕ)(F G:SampleDose), F.Normalized∧G.Normalized ∧ tsupport F.val⊆ reviewEarlierBox.invites ∧ tsupport G.val⊆ reviewLaterBox.invites ∧
        P.ReturnsSix x (c i₀) (r i₀) 0 F G ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F G ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n) (p:Lead.Clan→ SatinJets.Prism),
       Spine.Snapdragon P x c r (P.cinema x f s v a q u) n ∧
       P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K ∧
       (∃ A'∈reviewEarlierBox.invites, ∃ B'∈ reviewLaterBox.invites,P.UsesReproof x (P.cinema x f s v a q u) c r n p V f s X F G (c i₀) (r i₀) K A' B') ∧
       P.PolynomialControl p (V:=V) ∧ P.ThermalBid x f s v a ∧
       (∀ j l,∃ M,Spine.ActualScarab P x (P.cinema x f s v a q u) j l M) ∧
       ∀ᶠ i:ℕ in atTop,∀ t:ℕ, c (n i) ≤ t→ P.SimultaneousDisclosure x (P.cinema x f s v a q u) c r n p F G i t:= by
 intro Ω'
 obtain ⟨ν,P,K,e,hR,N,Lt,_,_,_,hw,_,C,_,_,_,A,_,_,c,r,h,Ht,b,hb,ρ⟩:= sectional_galaxyXL (fun _ _ _ _ _ _=>0) Ω' 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨s,_,hs⟩:=ρ.exists
 obtain ⟨x,R,_,k,v,a,V,Bid,τ,u,Q,V',p⟩:= hs (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 let f:= P.pointEra s; let D:= P.cinema x f s v a Q u
 obtain ⟨n,T'⟩:= P.hovered x c r D Ht k.setup; have T:=T'.allow
 obtain ⟨i,F,G,w,z⟩:=(P.ordersPrism x f s V' 1 p R K _ _ thinEarlier (le_refl _) (le_refl _) k.setup zero_lt_one).exists
 let Y':=P.get_armada x D c r n w T V' _ _ p (P.makeFleet x c r D n k.setup T p.heat (fun j=>P.cinema_pure x f s v a Q u j))
 have U:= P.honorLab x _ _ _ _ _ _ _ _ _ Y' R _ _ _ _ _ _ _ _ thinEarlier (le_refl _) (le_refl _) z
 let Y:= trans6 k.setup
 exact ⟨P,K,e,Lt.1,Lt.2,hR,P.terminalBeta K e,c,r,x,R,h,Ht,k.setup,Y,fixed_readyAPS P K c r x Y,i,F,G,U.keeps.normalized.1,U.keeps.normalized.2,U.keeps.earlier,U.keeps.laterProbe,U.keeps.fixed.1,U.keeps.fixed.2,f,s,v,a,u,Q,V',n,T,w,T',U,P.probe_rejected x D c r n w V' f s T F G (c i) (r i) K R U,P.prices_caught f s v a w u Q Y' Bid,Bid,fun j l=> P.culmination j N x A C b v a V k.station.2.1 l (⟨P.par.R.L.val/2,by omega⟩) τ u Q,P.plan_issued x _ c r n w V' _ _ _ F G U⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection


#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.diva_pricedSnap
