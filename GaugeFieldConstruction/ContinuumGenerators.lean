import GaugeFieldConstruction.ContinuumTheory
import GaugeFieldConstruction.SapphireRT
import GaugeFieldConstruction.RidgeBornRP
import GaugeFieldConstruction.TensionPerilPV
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
open ConsoleθN
open NSF.Boundary (Wightman Fields Letter Symmetries)
open YM.Boundary (Test4 Joint Distn)
open NSF.Boundary
open PortRT
open Stage Stage.Cell
/-! # The system on the vacuum. Claims made in TERMS of the Wightman
  functions of this system. `MeridianΛL` additionally uses clocks computed
  by analytic continuation of the same distributions (and spectra), via
  `Surface.Aurora`.

  We prove a translation **Ward identity**, not via stress charges.
  See `StressGeneratesTranslationsHere.retarded` below: statement wholly
  on real distributions. There is no time-ordered extension prescription at
  coincident Eu points. In this Mink statement the contour is an arbitrary
  hatch, cut away from the contact at 0 on the support of the insertion
  commutator. No products of step functions with distributions in the identity.
-/

local notation "Rim"=> roles.PerD_VU stress (le_refl _)
local notation "Alphabet"=> roles.RadianceVU stress
noncomputable abbrev indexFields : Calibration.UV four ≃ₗ[ℂ] (roles.RadianceVU stress).Union:=
 (roles.PerD_VU stress (le_refl _)).TinCanL
noncomputable abbrev TensorInTheory (i j:Axis) := roles.MLabelsVU stress (le_refl _) i j
noncomputable abbrev TensorField (i j:Axis) (f:Test4) := model.system.operators.field (TensorInTheory (stress:=stress) i j) f
local notation "Indexκ" => indexFields (stress:=stress)
local notation "ℒq" => TensorInTheory (stress:=stress)
local notation "Tq" => TensorField (model:=model)
local notation "Xq"=> model.system
local notation "Oq"=> model.system.operators
local notation "Vq"=> model.system.action

structure ReconstructedFieldSystem : Prop where
 -- explicitly W-fields; 4 translation generators in radian units.
 fields : model.system.operators.Total
 not_lost : model.system.operators.notLost
 positive : response.wordsPositive model.system.J
 costs : model.system.operators.realizes response
 really (x:(Alphabet).Union) (f:Test4) :
    (Oq).denselyDefined ((Xq).J x) (YM.Boundary.Probe.bar f) ≤ ((Oq).denselyDefined x f).adjoint
 cover : NSF.Boundary.Symmetries (Xq).spin Vq
 spectrum : (Vq).orbit.Spectrum (Xq).momentum
 future : (Xq).momentum.region Mink.coneᶜ = 0
 unique (v : (Oq).H) : (∀ x, (Vq).orbit.translation x v=v) → ∃ z:ℂ, z • (Oq).vacuum=v
 commute : (Oq).commutes
 local_algebras : ∀ (U V:Set E4), (∀ x∈U,∀ y∈V, x-y∈ Mink.spacelike)→∀ (A:LockerΛL Xq U)(B:LockerΛL Xq V),
     A.val*B.val=B.val*A.val
 act (U:Set E4)(A : LockerΛL Xq U): ∃! B:LockerΛL Xq U, ActorVerΛL Xq A.val B.val
 inside (U:Set E4) : IsOpen U → U.Nonempty →
     (PolyBornRP Xq U).topologicalClosure = ⊤ ∧ Dense (Set.range (LockerBornRP Xq U)) ∧
      ∀ (V:Set E4), (∀ x∈V,∀ y∈U, x-y∈Mink.spacelike) → Injective (LockerBornRP Xq V)
 sector_geometry : layers.Region (SurfRimL (roles.χVX stress vacuum))
    -- real actual direct system on time axis also in `PredictionL`, not result on
    -- hypothetical adoption; spectra in all believers see ContinuumPayments.
 continuations : continued.FullBody layers
 observed : ObservingVU (K:=scale) (p:=stress) (x:=vacuum) (R:=response) screens

include Certificate
lemma realized : ReconstructedFieldSystem (continued:=continued) (model:=model) (scale:=scale) (screens:=screens) := by
 let H:= model.course
 have U:= Certificate.field_theory
 have e:= Certificate.path
 refine ⟨H.total,H.faithful, Fields.sees _ _ H.meets _ H.adj,H.meets,Fields.really _ _ H.total H.adj,H.covariance,
   H.spectral,H.forward,H.unique,H.localPairs,U.2.localPo,U.2.lock,
   roles.TalentBornRP stress vacuum _ e.phase_costs layers response continued model U e.ward_oracle,
   model.inlet.heat,U.1,bloomsObserveSC screens e.trajectory e.phase_costs e.ward_oracle U⟩

omit Certificate
noncomputable abbrev tensorCommutator (n:ℕ)(V:Fin n→UV four)(k:Fin n)(a i:Axis) : Distn (Points (n+1)) := CommΘRt stress (roles.PerD_VU stress (le_refl _)) (Y:=response) V k a i
-- inputs before k unaffected; before F at k, insert T^{i a}
noncomputable def placesStress (n:ℕ)(V:Fin n→UV four)(k:Fin n) (a i:Axis)
    (g:Fin (n+1)→Test4) (j:Fin (n+1)) : Letter (roles.RadianceVU stress) :=
 (addXRT k (indexFields (stress:=stress) ∘ V) (TensorInTheory (stress:=stress) i a) j,g j)
structure StressGeneratesTranslationsHere : Prop where
 stress_label (a b:Axis) : ℒq a b=CoffΜΛ Rim stress a b
 symmetry(a b:Axis) : ℒq a b=ℒq b a
 stars(a b:Axis) : (Xq).J (ℒq a b)=ℒq a b
 nontrivial : ∃ a b f,Tq a b f ≠ 0
 covariant(p:Mink.Poincare)(a b:Axis)(f:Test4): DragΛL Xq model.course p (Tq a b f)=
          ∑ i:Axis,∑ j:Axis,(costΛ p.Λ⁻¹ a i*costΛ p.Λ⁻¹ b j) • Tq i j (YM.Boundary.Joint.push p f)
 conserve(a:Axis)(f:Test4): (∑ i:Axis,Tq i a (ΦshiftΛ (basis i) f))=0
 -- derivative as distributions of the inserted W, test on Schwartz
 conservation_as_W : ConsWΛL response ℒq
 -- d(Uτ O(F) Uτ⁻¹)/dτ evaluated on the common word domain (all fields) at 0
 motion(a:Axis)(x:UV four)(f:Test4)(v:(Oq).domain): HasDerivAt (fun t:ℝ=>
     (DragΛL Xq model.course (Mink.Poincare.translation (t • basis a)) ((Oq).field (Indexκ x) f) v).val)
       (((Oq).field (Indexκ x) (-(ΦshiftΛ (basis a) f)) v).val) 0
 -- no reliance on some other Ward arrays. Commutator distribution uniquely
 -- priced by insertions of OUR T field, arbitrary spectators. τNearRT swaps this slot with next
 commutator(n:ℕ)(V:Fin n→UV four)(k:Fin n)(a i:Axis)(W:Distn (Points (n+1))):
    W=tensorCommutator (response:=response) n V k a i ↔
      ∀ f:Fin (n+1)→Test4,W (YM.Boundary.Joint.materialize (n+1) f) =
        CostXtRt Xq (List.ofFn (placesStress (stress:=stress) n V k a i f))-
        CostXtRt Xq (List.ofFn ((placesStress (stress:=stress) n V k a i f) ∘ (τNearRT k).s))
 caps : ∀ (U:Set E4), U∈𝓝 0 → ∃ b:Test4,∃ h:Axis→Test4,HatchRT b h ∧ tsupport b⊆U ∧ ∀ i:Axis, tsupport (h i) ⊆ U
 retarded (n:ℕ)(V:Fin n→UV four)(k:Fin n)(a:Axis)(b:Test4)(h:Axis→Test4)(f:Fin n→ Test4): HatchRT b h →
       CostXtRt Xq (List.ofFn fun i=> ((Indexκ (V i)), Function.update f k (-(ΦshiftΛ (basis a) (f k))) i))=
         -(Complex.I * (MinkΛM a:ℂ)) * ∑ i:Axis, tensorCommutator (response:=response) n V k a i
                                (χTestRT k (h i) (YM.Boundary.Joint.materialize n f))
 ward : LocalWardRT stress Rim response Xq
 -- includes independent analytic translation Ward. Normalization directly
 -- from U1--U5. Contours Breather; Wickγ notation. No charges.
 complex_clock : EssentialWardVU (G:=model) (T:=continued)

include Certificate
lemma generates : StressGeneratesTranslationsHere (continued:=continued) (model:=model) := by
 let H:= model.course
 have Q:= Certificate.path
 have A:= Q.phase_costs; have t:=Q.ward_oracle
 have U:= Certificate.field_theory
 let M:=U.2
 let K:=roles.ΛFutureRealCoreRT stress vacuum _ A layers response continued model U t
 have p:TensorInTheory (stress:=stress)= CoffΜΛ (roles.PerD_VU stress le_rfl) stress:=
      funext fun a=>funext fun b=>roles.pricesVU stress vacuum _ A a b
 refine ⟨fun a b=>congr_fun (congr_fun p a) b,fun i j=>?_,fun i j=>?_, ?_, ?_,roles.KruppVU stress vacuum _ A _ _ _ _ U,?_,M.rotates,?_,K.caps,K.generates,K,blossomsVU A t U⟩
 · rw [p]; exact M.symm ..
 · rw [p]; exact M.adj ..
 · obtain ⟨a,b,g⟩:= stress.nonzero
   have he: TensorInTheory (stress:=stress) a b≠0:= by
      rw [TensorInTheory,MLabelsVU]
      apply (LinearEquiv.map_ne_zero_iff _).2
      change ((((Wickγ _)⁻¹*(Wickγ _)⁻¹):ℂ) • stress.J _ _) ≠ 0
      refine smul_ne_zero ?_ g
      unfold Wickγ; split_ifs <;> simp
   obtain ⟨f,q⟩:=H.faithful _ he; exact ⟨a,b,f,q⟩
 · intro g a b f; unfold TensorField; rw [p]; exact M.field ..
 · rw [p]; exact M.conserve
 intro n V k a i W
 refine (K.knows n V k a i W).symm.trans ?_; unfold ReflectionWardRT; unfold placesStress; rw [p]
 rfl
#print axioms realized
#print axioms generates
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
