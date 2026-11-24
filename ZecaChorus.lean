import ZecaCloud
import SU5SatinVerifiedNovember6
set_option autoImplicit false
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 350000
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
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight

namespace Spine

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set


variable (P : Spine) (K : P.Register) (c r : ℕ → ℕ)
   (x : P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A : ℕ → P.Apron) (n : ℕ → ℕ) (w : Lead.Clan → Prism)
   (V : ∀ j : Axis, List Axis → ℝ → P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n)

def CP18Inner: Prop:=
      (∀ i k : ℕ, (((P.run.voyage i).X (P.run.uv k)).gram 0).beta = P.par.x) ∧
      Experiment P K c r x R ∧ P.Transmission x c r ∧ F.Normalized ∧ U.Normalized ∧
      tsupport F.val ⊆ reviewEarlierBox.invites ∧ tsupport U.val ⊆ reviewLaterBox.invites ∧
      P.ReturnsSix x (c i₀) (r i₀) 0 F U ∧ P.FixedSatinReadings K x (c i₀) (r i₀) 0 F U ∧
     
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

/-- Native calls compare directly to both programs (factorized raw test, Glasshouse display)
and footprints stay strictly within disclosed boxes. -/
def CP18Cost: Prop :=
 (∀ i t, P.glasshousePrism x A c r n w F U i t = P.azurePrism x A c r n w F U i t) ∧
 (∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t →
    P.azurePrism x A c r n w F U i t =
        P.reportPrism A c r n w F U i t (P.singleState 3 t x) -
        P.reportPrism A c r n w F U i t (P.thinSplit x t)) ∧
 ∀ᶠ i in atTop, ∀ t : ℕ, c (n i) ≤ t → ∀ a b : Lead.Clan,
      ∃ S Q : Finset Cover,
        Charm.Locator P.calibration (P.azurePrepared t (((P.soldTrumpet A c r n w) a i).kiss P 3) F) S ∧
        Charm.Locator P.calibration (P.azurePrepared t ((P.soldTrumpet A c r n w) b i) U) Q ∧
        P.pinFoot t S ⊆ reviewEarlierBox.invites ∧ P.pinFoot t Q ⊆ reviewLaterBox.invites

open Preparation.Yoke Yoke.Travel SatinNucleus Six Regis.Head Regis.Head.Brecht
open CF.Velvet CF.Pannier.Chancel
/-- Also keep disclosure and history of purchases.
(Not every commission possible at jointly chosen v is announced here, use
elected_thin_cloud for the co-station main theorem.)
-/
def Incense: Prop:=
  let Ω':Supplier:= fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
  uniform P K Ω' 1 1 ∧
  (id : ℕ → ℕ) ≤ r ∧
  (∀ (U V:Doorway)(order:Orders),U.Later V order 0 →
     ∀ᶠ i:ℕ in atTop,∃ (a:ℝ)(F G:SampleDose),F.Normalized∧G.Normalized ∧ tsupport F.val⊆ U.invites ∧ tsupport G.val⊆ V.invites ∧
        P.ReturnsSix x (c i) (r i) a F G ∧ P.FixedSatinReadings K x (c i) (r i) a F G) ∧
  (∃ p∈reviewEarlierBox.invites, ∃ q∈ reviewLaterBox.invites, P.UsesReproof x A c r n w V g h X F U (c i₀) (r i₀) K p q) ∧
  (∀ᶠ i:ℕ in atTop,∀ t:ℕ, c (n i) ≤ t→ P.SimultaneousDisclosure x A c r n w F U i t) ∧
  P.Roster ∧ P.NightCop ∧
  (∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition), A=P.cinema x g h v a q u) ∧
  (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x A c r n p X V g h)

structure Scores (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n): Prop where
 native: P.CP18Inner K c r x R i₀ F U A n w V g h X
 costs: P.CP18Cost c r x F U A n w
 incense: P.Incense K c r x i₀ F U A n w V g h X
 operators: P.Aureole x A c r n

-- use inner
lemma sing_scores
 (hu: uniform P K (fun _ _ _ _ _ _ _ _ _ _ _ _ => 0) 1 1)
 (ir:id ≤ r)
 (ex:Experiment P K c r x R)
 (t: P.Roster)(s:P.NightCop)
 (ee: ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition), A=P.cinema x g h v a q u)
 (D:∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x A c r n p X V g h)
 (Z:P.FullPrismLab x A c r n w V g h X 1 F U reviewEarlierBox reviewLaterBox (c i₀) (r i₀) K)
 (l:P.Aureole x A c r n):
 Scores P K c r x R i₀ F U A n w V g h X :=by
 have y:=trans6 ex
 refine ⟨⟨P.terminalBeta K hu,ex,y,Z.keeps.normalized.1,Z.keeps.normalized.2,Z.keeps.earlier,
        Z.keeps.laterProbe,Z.keeps.fixed.1,Z.keeps.fixed.2,Z,
        P.fullPrism_azure_margin x A c r n w V g h X F U Z,
        P.fullPrism_azure_limits x A c r n w V g h X F U Z,
        P.fullPrism_excludes_azure_gauge x A c r n w V g h X F U Z⟩,
        ⟨P.glasshousePrism_eq_azure x A c r n w F U,
         P.fullPrism_azure_comparison x A c r n w V g h X F U Z,
         P.fullPrism_azure_boxes x A c r n w V g h X F U Z⟩,
        ⟨hu,ir,?_, P.probe_rejected x A c r n w V g h X F U _ _ K R Z,
        P.plan_issued x A c r n w V _ _ _ F U Z,t,s,ee,D⟩,
       l⟩
 intro U V o p; obtain ⟨v,e,_,_,hf⟩:= Spine.authorize (fun _=>false); filter_upwards [Spine.packs_within_rectangles y _ _ hf U V o p] with i w
 obtain ⟨a,F,G,l,q,s,r,t,_⟩ := w.2
 exact ⟨a,F,G,l,q,r,t,s,P.reviewWardContrast K x _ _ _ _ _ s⟩

/--
This strengthens `exists_disclosed_satin_native_contrast`, concurrently with its proof.
Select ALL witnesses once; keep every conclusion (Scores.native) AND the operator
prices Scores.operators. Uses imports down to election where the existential witnesses
are made, retaining extra data and choosing qualifying launches and purchases, not
claiming these extra qualifications for arbitrary witnesses of the compatibility theorem.
-/
theorem exists_disclosed_satin_native_operators :
 ∃ (P:Spine) (K:P.Register) (c r:ℕ→ℕ)
   (x:P.Spectrum0 3) (R : P.Ellis 3 x) (i₀ : ℕ) (F U : SampleDose)
   (A:ℕ→P.Apron) (n:ℕ→ℕ) (w:Lead.Clan→Prism)
   (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))
   (g h : ℕ) (X : P.HandleWith x c r A n), P.Scores K c r x R i₀ F U A n w V g h X:=by
 let Ω':Supplier:= fun _ _ _ _ _ _ _ _ _ _ _ _=>0
 obtain ⟨n,P,K,e,π₀,h0,h1,h2,h3,h4,G,C,ec,q,H,A₀,a,season,c,r,h,snow,b,β,ρ⟩:=
   elected_thin_cloud (fun _ _ _ _ _ _=> 0) Ω' 1 1 zero_lt_one 1 zero_lt_one id
 obtain ⟨i,_,s⟩:= ρ.exists
 obtain ⟨x,R,_,t,v,a',V_,u,Q,V,N,d,z,l,T,f⟩:= s (fun _=>True) (Eventually.of_forall (fun _=>True.intro))
 obtain ⟨i₀,F,U,w,J⟩:=(f reviewEarlierBox reviewLaterBox thinEarlier _ zero_lt_one (le_refl _) (le_refl _)).exists
 exact ⟨P,K,c,r,x,R,i₀,F,U,_,N,w,V,_,i,d,
    P.sing_scores K c r x R i₀ F U _ N w V _ _ d e h t.setup π₀ h0 ⟨_,_,_,_,rfl⟩ T J l⟩

#print axioms exists_disclosed_satin_native_operators
#check @exists_disclosed_satin_native_operators
