import YM.SatinExist.Chelo
import YM.SatinExist.Danish
import YM.SatinExist.Ione
import YM.SatinExist.Luminous
import YM.SatinExist.Twin
/-! # Real fields on these actual labels. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn CF.Py.Rate.LocalLimit.Papal
open CF.Lamour.Bridge.Celeste
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open SatinTails SatinJets Boundary Spectral
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
variable (P:Spine)(x:P.Spectrum0 3)
local notation "X"=>P.ColorHil 3 (P.advocate 3 x 3)
local notation "Y"=>P.ManyF 3 (P.advocate 3 x 3)
local notation "ℰ" => P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "R"=>P.seasons 3 (P.advocate 3 x 3)
local notation "Λ"=>P.kiosk 3 (P.advocate 3 x 3)
local notation "E"=> (ℰ).E
local notation "U"=> (R).E
local notation "V"=>P.advocate 3 x 3
local notation "Ω" =>P.heaven 3 V
local notation "Pτ" F:max a:max b:max=>P.pillar 3 V F (- (a:ℝ)) (b:ℝ) 0
variable (A:ℕ→P.Apron) (k:ℕ)(L:(P.ManyF 3 (P.advocate 3 x 3)).Op)
variable (p:P.Concerto x A k L)
variable (N:P.PowerNames x A)
variable (Z:Lead.Clan)(c r n:ℕ→ℕ)(w:Lead.Clan→Prism)
local notation "Σ"=> N.fields 3
local notation "𝓻"=> N.rate 3
local notation "X'"=>P.weightL x A N Z
variable (S:P.Snapdragon x c r A n)
-- adjudication. exact Rim rendering. countably priced real clocks.
local notation "v₀"=>P.Asp x 3
local notation "ℓ"=> Bench (R)
section
variable (F:Test4) (t:ℝ≥0)
lemma heat_render (u:0<t) : U t (ℑ (R) L F k (v₀)).val= advancing (R) (plated (R) (r:=k) L t Ω) F:=by
 let S:=R; let B:=cache_I S k; let x₀:=plated S (r:=k) L t; let A' := plated S (r:=k) L
 have he: RealMint S k A' L:=fun x h=>by unfold A' plated; rw [Real.toNNReal_coe]
 have hv:stove S t (v₀)=v₀:= Subtype.ext (P.heaven_hot ..)
 have hx: U t (ℑ S L F k (v₀)).val= valise S x₀ F Ω:= by
    have h:= heatigher S k A' L F he t u (v₀); rw [hv] at h; exact (congrArg Subtype.val h.symm)
 rw [hx, advancing_eq,vmap]; congr 1; funext p;
 apply congrArg (fun x:P.ManyF 3 (P.advocate 3 x 3)=> _ • x);
 change M S p (x₀ (M S (-p) Ω))= M S p _; rw [P.transportsK x 3] -- tune
end
-- weighted casts and macros
local notation "J"=> P.heightPA x A N w Z
local notation "A!"=> P.legR x A N Z w
local notation "W!"=> P.soldTrumpet A c r n w Z
variable {V':∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)}
variable {I: P.HandleWith x c r A n}{F U_:SampleDose}
variable {a b t k':ℕ}{K:P.Register}
variable (Q:P.FullPrismLab x A c r n w V' a b I 1 F U_ reviewEarlierBox reviewLaterBox t k' K)
variable {Y':Lead.Clan→ VacuumVector (P.ManyF 3 (P.advocate 3 x 3))}(L':P.E4bridge F U_ x V' w A c r n I Y')
include Q S
lemma profile_at (T:P.LargeM c r)(u:StrictMono c) (s:ℝ≥0)(h:0<s): P.profilesZ x V' w Z (s:ℝ)= plated (R) (r:=J) A! (s:ℝ) Ω:=by
 have he:= P.rotorPrice x A N Z c r n w S T u
 exact tendsto_nhds_unique (Q.armada.heated_points Z s h).2 (Concerto.profile P x W! (J) (A!) he s h (fun i=> P.sold_birth x A c r n w Z i I))
include L'
lemma groundRender (T:P.LargeM c r)(u:StrictMono c) (f:Test4): Y' Z f= (ℑ (R) (A!) f (J) (v₀)).val:=by
 apply sub_eq_zero.mp; apply (R).heat_faithful 1; rw [map_sub,sub_eq_zero]; let p:=(1:ℝ); let v:=(1:ℝ≥0)
 have h:= (L'.costs Z).pays p (by unfold p; positivity) f
 simp only [p, Real.toNNReal_one] at h; rw [h,P.heat_render x _ _ f _ zero_lt_one,← P.profile_at x A N Z c r n w S Q T u 1 zero_lt_one]; congr 3
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
