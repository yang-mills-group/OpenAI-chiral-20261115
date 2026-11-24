import GaugeFieldConstruction.ContinuumTheory
import GaugeFieldConstruction.CraftEpochPV
import GaugeFieldConstruction.BifoldPV
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace
namespace ContinuumConstruction
-- Data telescope. Naming concordance through the flagship API (QFT: E to Story,
-- L & G to continuity, calendars to labels and paths).
variable
  {nLeaf : ℕ}
  {process : Spine}
  {scale : process.Register}
  {production : YardμN process CostUpVU PolRun PriceArtVU nLeaf}
  {growth : InterR}
  {roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU}
  {axes : Axis → GaugeFieldConstruction.Empire.Across}
  {comparison : Sheds roles.Crew_N axes}
  {approvals : Supplies comparison}
  {stress : Ticket roles.Gamma_N approvals}
  {vacuum : process.Spectrum0 3}
  {costAnalysis : process.Ellis 3 vacuum}
  {c : ℕ → ℕ}
  {collars : ℕ→ℕ}
  {layers : NSF.Boundary.Waves (roles.RadianceVU stress)}
  {response : NSF.Boundary.Surface (roles.RadianceVU stress)}
  {continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL}
  {model : roles.GlowVU stress vacuum (le_refl _) layers response}
  {screens : process.Poll 3}
variable (Certificate : Assembled (scale:=scale) (costAnalysis:=costAnalysis) (c:=c) (collars:=collars)
   (continued:=continued) (model:=model) (screens:=screens))
open Reconstruction Tapestry.Altitude Tapestry.Exhibition PhaseChoice
open Vale Reed Dial Pastry
/- **Physical prescription**. Use the primary Spine (six families at
that SU coupling) exactly. These are the reads, at EVERY height in this
production. See also Corpus/M-frames for continuum chiral signatures.
-/
section
open Complex in
abbrev SixFamiliesAtEveryLink : Prop :=
   ∀ (g:SU.E) (j:Fin 3),
    (SU.matter g).val=(1:Op (Fin 3)) ⊗ₖ Join.both (ExTwo.wedgeOp (SU.fund g)) (cc (SU.fund g)) ∧
    Fintype.card Lead.Clan=6 ∧
    (∀ i:SU.Ten, Window.family (j,Sum.inl i)=(j,true)) ∧
    (∀ i:SU.F, Window.family (j,Sum.inr i)=(j,false)) ∧
    (Window.colors (j,true)).card=10 ∧ (Window.colors (j,false)).card=5
/- 'Generation' at the continuum fields API remains these Fin 3 indices. -/
lemma representation : SixFamiliesAtEveryLink:= MultiSpeciesVU

variable (P:Spine) (k:ℕ)
local notation "ᴺᴷ" => P.NboltPV k

abbrev TopUsesSameBare : Prop:= ∀ z: Orbit (P.NboltPV k),
     denZ (((P.run.voyage (P.diagonalᵢ k)).X (P.diagonalDepth k)).gram (P.diagonalDepth k)) P.par.U
        ((P.run.voyage (P.diagonalᵢ k)).CapeT (P.diagonalDepth k)) z=
     Vale.capP (K:=P.par.K) P.par.U (P.barePrescription (P.diagonalDepth k))
       (P.run.meter.a (P.diagonalDepth k)) z.1

abbrev WilsonProjectionAndPhase : Prop:= ∀ (u:Pane ᴺᴷ), P.AcclimatedPV k u →
    Safe (P.AtlasPV k u).H ∧ P.DboltPV k u=portW (Tulip.helix _).symm (projector (P.AtlasPV k u).H) ∧
    Sea (P.DboltPV k u) (P.ΦboltPV k u) ∧
    portW (Tulip.helix _).symm (P.AtlasPV k u).overlap * P.DboltPV k u=cutM (Tset ᴺᴷ) * P.DboltPV k u ∧
    (∀ (x:Site ᴺᴷ) (a:SpinIdx) (g:Fin 3) (t:SU.Ten ⊕ SU.F), (Reed.think (Tset ᴺᴷ)).term ((x,a),g,t)=
        if a∈plusHalf then Fock.put ((x,a),g,t) else -Fock.takeF ((x,a),g,t))∧
    (∃ v L,(P.AtlasPV k u).H=spectral v L ∧ P.DboltPV k u=portW (Tulip.helix _).symm (spectral v (occ L)))∧
    (∃ (v:UNI (Single ᴺᴷ))(S:Finset (Single ᴺᴷ)), P.DboltPV k u=twist v (cutM S) ∧
     ∃ c:ℂ, ‖c‖=1 ∧ ∀ x:FC (Single ᴺᴷ), Reed.Plain x →
       c*Reed.spell (Reed.syms (Tset ᴺᴷ)) v.val (Tset ᴺᴷ) S x= inner ℂ (mateK ᴺᴷ) (acts ((Reed.think (Tset ᴺᴷ)).eval x) (P.ΦboltPV k u)))

lemma bareLaw : WilsonProjectionAndPhase P k:=by
 intro u p; obtain ⟨e,f,g,h,H⟩:= LivePhaseVU k u p
 exact ⟨e,f,g,h,H,(P.RaiseProjectPV k u p).2.2,P.GrassRepresentationPV k u p⟩

abbrev IntegralReadOnTorus (L:BillsSumVU P):ℂ:=
 let A:=witnessCutVU P (P.diagonalᵢ k) (P.diagonalₖ k) L
 let μ:= prior SU.group (More (P.NboltPV k))
 (∫ U,P.bareViewPV k A U ∂μ)/(∫ U,P.bareViewPV k 1 U ∂μ)
lemma reads (L:BillsSumVU P): AskingPriceVU P k L=IntegralReadOnTorus P k L:=by unfold AskingPriceVU IntegralReadOnTorus; simp_rw [P.βwrittenPV]; rfl
end

structure BareMeasurementsOnOnePath :Prop where
 period : Tendsto (fun k=> (process.run.ir (process.diagonalᵢ k)).val) atTop atTop
 depth : StrictMono process.diagonalDepth
 -- coupling (Beta variable convention)
 fixed_physical : 0<process.par.x
 uses_same : ∀ k:ℕ,
    (((process.run.voyage (process.diagonalᵢ k)).X (process.diagonalDepth k)).gram 0).beta=process.par.x ∧
    process.FiniteScheduleVU k=(((process.run.voyage (process.diagonalᵢ k)).X (process.diagonalDepth k)).gram (process.diagonalDepth k)).beta
 prescription : ∀ k:ℕ, TopUsesSameBare process k
 chiral : ∀ k:ℕ, WilsonProjectionAndPhase process k
 families : SixFamiliesAtEveryLink
 selects : process.Selects scale 3 vacuum screens
 before_elect : ∀ (s:ℕ) (l:List (MeterQueryVU process)),
    (∀ i∈l,i.1∈ treasuryVU s i.2)→ l.Pairwise (fun a b=>Disjoint a.2 b.2) →
    ∃ K:MeterQueryVU process →Set Vantage,
     (∀ i∈l,K i⊆ i.2 ∧ IsCompact (K i) ∧ process.asked_at s i.1 (K i)) ∧
     let W:= TopCurrencyVU process s (l.map (fun x=>(x.1,K x)))
     (∀ᶠ k in atTop,TenderΘVU s (process.diagonalᵢ k) (process.diagonalₖ k) W) ∧
     Tendsto (fun i=>IntegralReadOnTorus process i W) atTop (𝓝 (process.E s (((l.map Prod.fst).prod).val)))
 -- permits arbitrary height menus after election on this same path, without
 -- the χ, K, (i,k) changing except indicated, i.e. can realize each estimate
 -- in the actual bare law. Read TenderΘVU inside SummitInvoiceVU for supports,
 -- fits and nonzero/integrable conditions.
 on_elected : ∀ {J:Type} (L:Finset J) (S:J→ℕ)(l:J→List (MeterQueryVU process)) ε, 0<ε →
   (∀ i∈L, (∀ u∈l i, u.1∈treasuryVU (S i) u.2 ∧ IsCompact u.2) ∧
       (l i).Pairwise (fun a b=>Disjoint a.2 b.2))→
   ∀ᶠ i in atTop,∀ᶠ k:ℕ in atTop,∀ j∈L,
     let A:=l j
     let W:= TopCurrencyVU process (S j) A
     let Y:= PollavuVU process 3 screens i
     SummitInvoiceVU (R:=scale) (x:=vacuum) (s:=S j) (c:=screens) i k W ε ∧
      (1/2<‖IntegralReadOnTorus process k Y‖) ∧
      dist (IntegralReadOnTorus process k (W++Y) / IntegralReadOnTorus process k Y)
       (process.singleState 3 (S j) vacuum ((A.map Prod.fst).prod))<ε

include Certificate
lemma charged_bare : BareMeasurementsOnOnePath (scale:=scale) (vacuum:=vacuum) (screens:=screens):=by
 let X:= Certificate.path
 obtain ⟨p,h,e,v⟩:= process.InstrumentVU scale X.admissible
 refine ⟨p,h,e,v,PeggedVU,bareLaw process,representation,X.trajectory.1,?_,?_⟩
 · intro s l q t; simp_rw [←reads]; exact cratePV q t
 intro J L S l ε e q
 filter_upwards [X.trajectory.2 L S l ε e (fun i w=> ⟨fun a b=> ⟨((q i w).1 a b).1.1, ((q i w).1 a b).1.2, ((q i w).1 a b).2⟩,(q i w).2⟩)] with i p
 filter_upwards [p] with k hp j hj
 dsimp only
 refine ⟨hp _ hj,?_⟩; rw [← reads,← reads]
 exact (askVU (hp _ hj)).symm
#print axioms charged_bare
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
