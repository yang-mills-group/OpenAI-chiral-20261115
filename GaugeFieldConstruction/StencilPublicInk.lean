import GaugeFieldConstruction.StencilHalos
import GaugeFieldConstruction.FancyLightL
import GaugeFieldConstruction.ChasmLightYL
import GaugeFieldConstruction.StencilCarton
import GaugeFieldConstruction.StencilPublicCore
import SatinThinReproofClock
import GaugeFieldConstruction.AuldΘJ
/-!
# Carton on those actual SAT labels, over the neutral-timeslice space
-/
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
namespace Discipline
open RosterJ BoonsθJ Shower SelectionAnalysis
open OS.Semigroup MacroGrid
open NSF.Boundary
open Complex Mink SignetS YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric
open _root_.YM.SatinWFixed _root_.YM.SatinRegistration
variable (P:Spine) (x:P.Spectrum0 3)
local notation "ν" => P.advocate 3 x (3:Axis)
local notation "H"=> P.ColorHil 3 ν
local notation "B"=> P.ManyF 3 ν
local notation "J"=> P.gnsIn 3 ν
local notation "C"=> P.privateH x 3
local notation "D"=> (C).DegreeHab
local notation "S"=> P.seasons 3 ν
local notation "T"=> (C).BrightHab
local notation "Κ"=> (C).canopy.track
local notation "μ"=> marks (timeMesh P.par)
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable (R:ΧiMars→ₗ[ℂ] ScreensJ P)(A:AllocatedL P)(X:CloudsL){F:CloudsL}(W:SurfCheckL F)
variable (h:CheckΩL R) (g:∀ (v:ΧiMars) (j:Axis) (σ τ:PermWallJ P), R v j σ τ ∈ P.neutralSlabs j)
local notation "Qρυθ" => SmallRimL (P.privateH x 3) R A X W
local notation "SY" => (SurfRimL F).Union
local notation "Ζ" => projectLine P 3 x
variable {W':Waves (SurfRimL F)}(p:NSF.Bid.Direct (SmallRimL (P.privateH x 3) R A X W) W')
local notation "Λ" => StampShelf P x R A W
local notation "Ψ" => passFrame P 3 x
include X h g p
noncomputable def library : Carton (S) (SurfRimL F).Union:= {bar:=Λ,coherent:= stamp_coherent P x R A W h g, price:= stamp_enjoy P x R A X W h g p, omega:=P.heaven 3 ν,size:=P.stone_norm .., hot:=fun _=> P.heaven_hot ..,stay:= fun _=> P.roll_static ..} -- `omit X p` in not.P binder tuning
local notation "𝒢"=> library P x R A X W h g p
open SatinRegistration.Grading
omit X h g p in
private lemma asterOp_st (q:ΧiMars): W.AsterBackL (W.TinCanL q)= W.TinCanL (TurnupMars timeAxis q):=by change W.TinCanL ((TurnupMars timeAxis) (W.TinCanL.symm (W.TinCanL q)))= _; rw [W.TinCanL.symm_apply_apply]
set_option maxHeartbeats 1300000 in
omit X p in
private lemma stamp_alive_st (t:ℝ≥0)(v:ΧiMars): Λ t (W.TinCanL (TurnupMars timeAxis v))= ContinuousLinearMap.adjoint (Λ t (W.TinCanL v)):=by
 let V:= TurnupMars timeAxis v; change Λ t (W.TinCanL V)= (Λ t (W.TinCanL v)).adjoint
 rcases eq_zero_or_pos t with rfl|hv
 · change Λ 0 (W.TinCanL V)= ContinuousLinearMap.adjoint (_); have hp(z:SY): Λ 0 z=0:=if_neg (lt_irrefl (0:ℝ≥0)); rw [hp,hp,map_zero]
 let s:=A.pad t; let Zℓ:=R v 3 s s; let X:P.Physical 3:= ⟨Zℓ,g v 3 s s⟩; let T₁:=(t:ℝ)-StallJ P (A.pad t); have he:R V 3 s s=star Zℓ:= h.warmL v timeAxis s
 rw [stamp_part P x R A W t _ hv,stamp_part P x R A W t _ hv,W.TinCanL.symm_apply_apply,W.TinCanL.symm_apply_apply,he]
 change (S).sand (projectPrice P 3 x (Star.star X).val) T₁ T₁= Star.star ((S).sand (projectPrice P 3 x X.val) T₁ T₁); rw [notLoss P 3 x (Star.star X), (S).sand_star,notLoss P 3 x X, map_star, ← P.reprise_star]
lemma library_rem : Remembers (𝒢) W.AsterBackL:=⟨ by
      intro v; obtain ⟨k,rfl⟩:= W.TinCanL.surjective v; rw [asterOp_st W k,asterOp_st,Turn2AxYL], fun t v=> by obtain ⟨v,rfl⟩:=W.TinCanL.surjective v; rw [asterOp_st]; exact stamp_alive_st P x R A W h g t v⟩
lemma library_pres: PreservesSmall (S) (𝒢).bar (𝒢).omega LinearMap.id Ψ (Qρυθ) := preserves_cart P x R A X W h g
#print axioms library
#print axioms library_rem
#print axioms library_pres
end Discipline
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
