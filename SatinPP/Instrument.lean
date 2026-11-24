import SU5SatinVerifiedNovember6
import SatinPP.CanvasBudget

/-!
Instrument the proof of `Spine.exists_disclosed_satin_native_contrast`
(see #check). Run it once. Need two things that are true of its actual
choices but dropped from its existential type (scouting data and elections'
weather). They enable the PP purchase. Don't, e.g., take Classical.choose of
an *independent* public ∃ and expect it to agree. Here drop nothing we need:
pass forward the `Attested` flag IN the same proof.
Diff from CP18: pass extra flag, rename lemmas, some scoping changes (combine
in one file), verify result forgets to the exact type. See below.
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

-- all flags written as a single predicate for easy diff
def Attested (P:Spine)(x:P.Spectrum0 3)(t s:ℕ)(Y:ℕ→P.Apron):Prop:=
    t<s ∧ ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ→ Coalition),
    Y=P.cinema x t s v a q u ∧
    ∃ (A C b:ℝ),P.Climate C ∧ ScoutAnthem P x A C t s b v a

lemma attested_price {P:Spine}{x:P.Spectrum0 3}{t s:ℕ}{Y:ℕ→P.Apron}
  (R:P.Register)(z:Attested P x t s Y):∃ B,LocketFifth P x Y B:=by
 obtain ⟨w,v,a,u,q,rfl,A,C,b,h,k⟩:=z
 exact fifth_cinema P R x s t v a u h w k q

open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Pitching.Focus
section
lemma interaction_review_instrument (X:TintDemand)(Y:Supplier)(L M:ℝ)(p:0<M)(z:ℕ→ℕ): ∃(P:Spine)(K:P.Register), uniform P K Y L M ∧ ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), z ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n), Attested P x f s (P.cinema x f s v a q u) ∧ (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x f s v a q u) c r n p X V f s) ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i) (r i) K:=by
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A,a,season,c,r,h,b,β,ρ⟩:= elected_thin_interaction X Y L M p 1 zero_lt_one z
 obtain ⟨i,_,s⟩:= ρ.exists
 obtain ⟨x,R,_,t,v,a,V,u,Q,X,N,d,T,f⟩:= s (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 exact ⟨P,K,e,x,R,c,r,h,t.setup, P.pointEra i,i,v,a,u,Q,X,N,d,⟨t.station.2.1,v,a,u,Q,rfl,_,_,_,⟨h0,H,h3,h4⟩,V⟩,T, f reviewEarlierBox reviewLaterBox thinEarlier _ zero_lt_one (le_refl _) (le_refl _)⟩ -- uniform check
-- NO hypotheses. The choice of geometry is allowed after the x selection. The smears, anchor,
-- and mark mask p can be chosen at any late fixed i, in reviewEarlierBox and reviewLaterBox
-- (ordinary unit boxes with separation at least 2; -Front.thin_separation).
lemma actual_separated_thin_field_interaction_instrument :
    let Y:Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Y 1 1 ∧
    ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), id ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n), Attested P x f s (P.cinema x f s v a q u) ∧ (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x f s v a q u) c r n p X V f s) ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i) (r i) K:= interaction_review_instrument (fun _ _ _ _ _ _=> 0) _ _ _ zero_lt_one id


lemma thin_field_tested_instrument :
    let Ω':Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Ω' 1 1 ∧
    ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), id ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n), Attested P x f s (P.cinema x f s v a q u) ∧ (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x f s v a q u) c r n p X V f s) ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), ∃ A'∈reviewEarlierBox.invites, ∃ B'∈ reviewLaterBox.invites,P.UsesReproof x (P.cinema x f s v a q u) c r n p V f s X F G (c i) (r i) K A' B' := by
 intro u
 obtain ⟨P,K,e,x,R,c,r,h,u,v,a,f,o,w,q,V,n,X,flag,p,l⟩:= actual_separated_thin_field_interaction_instrument
 exact ⟨P,K,e,x,R,c,r,h,u,v,a,f,o,w,q,V,n,X,flag,p,l.mono fun i x' =>by
    obtain ⟨Z,M,p,t⟩:=x'
    exact ⟨Z,M,p,P.probe_rejected x _ c r n _ V _ _ _ _ _ _ _ K R t⟩⟩
theorem disclosed_satin_witness_instrument :
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
       Attested P x f s (P.cinema x f s v a q u) ∧ P.FullPrismLab x (P.cinema x f s v a q u) c r n p V f s X 1 F G reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K ∧
       (∃ A'∈reviewEarlierBox.invites, ∃ B'∈ reviewLaterBox.invites,P.UsesReproof x (P.cinema x f s v a q u) c r n p V f s X F G (c i₀) (r i₀) K A' B') ∧
       ∀ᶠ i:ℕ in atTop,∀ t:ℕ, c (n i) ≤ t→ P.SimultaneousDisclosure x (P.cinema x f s v a q u) c r n p F G i t:= by
 intro Ω'
 obtain ⟨P,K,e,x,R,c,r,h,D,f,s,v,a,u,q,V,n,X,flag,p,w⟩:= thin_field_tested_instrument
 let Y:= trans6 D
 obtain ⟨i,F,G,z,A',f',B',h',T⟩:= w.exists
 let U:= T.toFullPrismLab
 exact ⟨P,K,e,P.terminalBeta K e,c,r,x,R,h,D,Y,fixed_ready P K c r x Y,i,F,G,T.keeps.normalized.1,T.keeps.normalized.2,T.keeps.earlier,T.keeps.laterProbe,T.keeps.fixed.1,T.keeps.fixed.2,f,s,v,a,u,q,V,n,X,z,flag,U,⟨A',f',B',h',T⟩,P.plan_issued x _ c r n z V _ _ _ F G U⟩

end
namespace Spine
open SatinJets
open _root_.YM.CF.Buffered.Afterglow.Hierarchy _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
theorem exists_disclosed_satin_native_contrast_instrument :
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
      (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
      Experiment P K c r x R ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
      tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
      P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U ∧
      ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
        (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
        (g h : ℕ) (X : P.HandleWith x c r A n),
        Attested P x g h A ∧ P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox
          (c i₀) (r i₀) K ∧
        (∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d) ∧
        ((∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
          (𝓝 (P.thinJournal x A c r n w X F U i))) ∧
          Tendsto (P.thinJournal x A c r n w X F U) atTop (𝓝 (P.readPrism x V w 1 F U))) ∧
        ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
          ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
            (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
            (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val := by
  obtain ⟨P, K, _, beta, c, r, x, R, _, experiment, transmission, _, i₀,
    F, U, normF, normU, boxF, boxU, six, fixedRead, g, h, v, a, hv, q, V,
    n, X, w, flag, lab, _, _⟩ := disclosed_satin_witness_instrument
  let A := P.cinema x g h v a q hv
  exact ⟨P, K, c, r, x, R, i₀, F, U, beta, experiment, transmission, normF,
    normU, boxF, boxU, six, fixedRead, A, n, w, V, g, h, X, flag, lab,
    P.fullPrism_azure_margin x A c r n w V g h X F U lab,
    P.fullPrism_azure_limits x A c r n w V g h X F U lab,
    P.fullPrism_excludes_azure_gauge x A c r n w V g h X F U lab⟩

abbrev Invoice := ∀(P:Spine) (_:P.Register)(c r : ℕ → ℕ)
   (x : P.Spectrum0 3) (_:P.Ellis 3 x),
   ℕ → SampleDose → SampleDose →
   ∀(A:ℕ→ P.Apron) (n: ℕ→ℕ), (Lead.Clan → Prism) →
   (∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) →
   ℕ → ℕ → P.HandleWith x c r A n → Prop

def InStock:Invoice:=fun P _ _ _ x _ _ _ _ A _ _ _ g h _ => Attested P x g h A
def Affirmed (I:Invoice):Prop:=

    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
      (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
      Experiment P K c r x R ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
      tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
      P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U ∧
      ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
        (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
        (g h : ℕ) (X : P.HandleWith x c r A n),
        I P K c r x R i₀ F U A n w V g h X ∧ P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox
          (c i₀) (r i₀) K ∧
        (∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d) ∧
        ((∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
          (𝓝 (P.thinJournal x A c r n w X F U i))) ∧
          Tendsto (P.thinJournal x A c r n w X F U) atTop (𝓝 (P.readPrism x V w 1 F U))) ∧
        ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
          ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
            (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
            (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val

lemma one_manifest : Affirmed InStock := exists_disclosed_satin_native_contrast_instrument

abbrev Public : Prop := 
    ∃ (P : Spine) (K : P.Register) (c r : ℕ → ℕ) (x : P.Spectrum0 3)
      (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose),
      (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
      Experiment P K c r x R ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
      tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
      P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U ∧
      ∃ (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
        (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
        (g h : ℕ) (X : P.HandleWith x c r A n),
        P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox
          (c i₀) (r i₀) K ∧
        (∃ d : ℝ, 0 < d ∧ LoudMargin (P.readPrism x V w 1 F U) d ∧
          ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → LoudMargin (P.azurePrism x A c r n w F U i t) d) ∧
        ((∀ᶠ i in atTop, Tendsto (fun t => P.azurePrism x A c r n w F U i t) atTop
          (𝓝 (P.thinJournal x A c r n w X F U i))) ∧
          Tendsto (P.thinJournal x A c r n w X F U) atTop (𝓝 (P.readPrism x V w 1 F U))) ∧
        ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a : Lead.Clan,
          ∀ u : Charm.W P.calibration, Verne.GNative P.calibration u →
            (P.prepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F).val ≠ u.val ∧
            (P.prepared t ((P.soldTrumpet A c r n w) a i) U).val ≠ u.val 
lemma re_export_public (I:Invoice)(h:Affirmed I):Public:=by
 obtain ⟨P,K,c,r,x,R,i₀,F,U,beta,e,y,nf,nu,bf,bu,s,t,A,n,w,V,g,h,X,flag,p,b,j,a⟩:=h
 exact ⟨P,K,c,r,x,R,i₀,F,U,beta,e,y,nf,nu,bf,bu,s,t,A,n,w,V,g,h,X,p,b,j,a⟩
-- type check
example : Public := Spine.exists_disclosed_satin_native_contrast

#print axioms exists_disclosed_satin_native_contrast_instrument
#print axioms attested_price

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

