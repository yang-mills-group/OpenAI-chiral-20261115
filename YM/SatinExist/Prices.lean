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

private lemma fixed_ready (P:Spine)(K:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3)(T:P.Transmission x c r): ∀ (U V:Doorway)(o:Orders),U.Later V o 0 →∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites∧
    P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G:=by
 intro U V o p; obtain ⟨v,e,_,_,h⟩:= Spine.authorize (fun _=>false); filter_upwards [Spine.packs_within_rectangles T _ _ h U V o p] with i w
 obtain ⟨a,F,G,l,q,s,r,t,_⟩ := w.2
 exact ⟨a,F,G,l,q,r,t,s,P.reviewWardContrast K x _ _ _ _ _ s⟩

open Regis.Head Regis.Head.Brecht
open SatinJets
namespace Spine
variable (P:Spine){x:P.Spectrum0 3}(f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ){c r n:ℕ→ℕ}{X:P.Spectrum0 3}
variable {Y:ℕ→P.Apron}(w:Lead.Clan→Prism)(i:Lead.Clan)
variable {V:∀ j:Axis,List Axis → ℝ →P.ColorHil j (P.advocate 3 x j)}
lemma profiles_agree {T:P.HandleWith x c r Y n}(D:P.ThinArmada x Y c r n w T V f s)(t:ℝ)(hp:0 < t): P.wealth 3 (P.advocate 3 x 3) (P.profilesH x w i V t)=P.profilesZ x V w i t:=by
 obtain ⟨p,u⟩:= D.heated_points i t hp; apply tendsto_nhds_unique _ u
 exact (((P.wealth 3 (P.advocate 3 x 3)).continuous.tendsto _).comp p).congr fun n=> (P.cradle_bank ..).symm

structure PolynomialControl : Prop where
 temp (j:Axis) (l:List Axis) : VacuumPower (M:=P.ColorHil j (P.advocate 3 x j)) (V j l)
 channels (i:Lead.Clan) : VacuumPower (M:=P.ColorHil 3 (P.advocate 3 x 3)) (P.profilesH x w i V) ∧ VacuumPower (M:=P.ManyF 3 (P.advocate 3 x 3)) (P.profilesZ x V w i)
variable (u:StrictMono v)(Q:ℕ→ Coalition)

lemma prices_caught {T:P.HandleWith x c r (P.cinema x f s v a Q u) n}(D:P.ThinArmada x (P.cinema x f s v a Q u) c r n w T V f s)(p:P.ThermalBid x f s v a): P.PolynomialControl w (V:=V):=by
 have hU :∀ j l, VacuumPower (M:=P.ColorHil j (P.advocate 3 x j)) (V j l):= fun j l=> D.cinema.heat.price u p j l
 refine ⟨hU,fun i=>?_⟩
 have ht: VacuumPower (M:=P.ColorHil 3 (P.advocate 3 x 3)) (P.route_before i x V):= (hU 3 []).line _
 have h:VacuumPower (M:=P.ColorHil 3 (P.advocate 3 x 3)) (P.profilesH x w i V):= ht.ticket (D.fusion.profile i) _
 refine ⟨h,?_⟩
 obtain ⟨K,u,m,t⟩:= h; refine ⟨K,u,m,?_⟩
 filter_upwards [self_mem_nhdsWithin,t] with t b d; rw [← P.profiles_agree f s w i D t b]; exact (P.bank_cost ..).trans d
end Spine
theorem estimated_disclosed :
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
       P.PolynomialControl p (V:=V) ∧ P.ThermalBid x f s v a ∧
       ∀ᶠ i:ℕ in atTop,∀ t:ℕ, c (n i) ≤ t→ P.SimultaneousDisclosure x (P.cinema x f s v a q u) c r n p F G i t:= by
 intro Ω'
 obtain ⟨ν,P,K,e,_,_,_,_,_,_,_,C,_,_,_,A,_,_,c,r,h,b,hb,ρ⟩:= estimated_galaxy (fun _ _ _ _ _ _=>0) Ω' 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨s,_,hs⟩:=ρ.exists
 obtain ⟨x,R,_,k,v,a,V,Bid,u,Q,V',p⟩:= hs (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 let f:= P.pointEra s; let D:= P.cinema x f s v a Q u
 obtain ⟨n,T⟩:= P.panel_sales x c r D k.setup
 obtain ⟨i,F,G,w,z⟩:=(P.ordersPrism x f s V' 1 p R K _ _ thinEarlier (le_refl _) (le_refl _) k.setup zero_lt_one).exists
 let Y':=P.get_armada x D c r n w T V' _ _ p (P.makeFleet x c r D n k.setup T p.heat (fun j=>P.cinema_pure x f s v a Q u j))
 have U:= P.honorLab x _ _ _ _ _ _ _ _ _ Y' R _ _ _ _ _ _ _ _ thinEarlier (le_refl _) (le_refl _) z
 let Y:= trans6 k.setup
 exact ⟨P,K,e,P.terminalBeta K e,c,r,x,R,h,k.setup,Y,fixed_ready P K c r x Y,i,F,G,U.keeps.normalized.1,U.keeps.normalized.2,U.keeps.earlier,U.keeps.laterProbe,U.keeps.fixed.1,U.keeps.fixed.2,f,s,v,a,u,Q,V',n,T,w,U,P.probe_rejected x D c r n w V' f s T F G (c i) (r i) K R U,P.prices_caught f s v a w u Q Y' Bid,Bid,P.plan_issued x _ c r n w V' _ _ _ F G U⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
