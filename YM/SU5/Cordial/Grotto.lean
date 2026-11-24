import YM.SU5.Cordial.Horizon
import YM.SU5.Cordial.Spritz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
/-! # Hankel estimates repay marginal continuity inside this UV resolution.
 No passage to different study/vacuum data! Lift through other axes on this observation.
 Strict separation using actual SUPPORT at its stencil; no need diagonal limit to get this. -/
open OS.Semigroup (F)
open OS.Semigroup.Balloon
variable (P:Spine){q:ℕ}(x:P.Spectrum0 3)(Z:Lead.Clan)(k:Street)(s:ℕ)(c r:ℕ→ℕ)
local notation "κ" => P.calibration
local notation "B" => P.par.block
local notation "M" => timeMesh P.par
local notation "Γ" => marks M
local notation "N₀" => notch M
local notation "ε" => YM.basis (3:Axis)
local notation "ι" => k.val
local notation "ℓ" => P.calibration.ℓ
local notation "β" => P.otherSpectrum 3 3 x
local notation "S" => P.physicalEnergy 3 (β)
local notation "V" => P.ColorHil 3 (β)
local notation "χ" => P.otherSpectrum 3 k.val (β)
local notation "W" => P.ColorHil (ι) (χ)
local notation "Λ" => P.physicalEnergy (ι) (χ)
local notation "Ψ" => P.voyageF 3 (β)
local notation "y" s:max i:max=> P.shard x Z s i
local notation "U" => (Ψ).crew k
-- along whole canonical spatial space. ensemble costs hold
local notation "Φ" i:max=> (y (c i) (r i))
local notation "ρ" i:max=> P.dew (c i) (r i)
local notation "π"=> (U).pi_c
local notation "G"=>P.ManyF 3 (β)
local notation "Ψ'"=>P.seasons 3 (β)
local notation "π'"=>P.wealth 3 (β)
local notation "λ'"=>P.enter 3 (β)
local notation "φ" i:max=> P.lucid x Z (c i) (r i)
open FixedProbe Tapestry.Altitude Tapestry.Exhibition CF.Pannier.Chancel
open Signal.Interval (separationCost)
open OS.Semigroup.Balloon
variable (R:P.Register)
-- specialized gauge separation at the actual fixed level. k→∞ elsewhere in proof.
def crownR (q:ℕ): Fin 1 → Cover:= fun _=> (P.flash q).death
lemma risingS(q:ℕ): let f:=P.flash q; dist (addressG P.par s (nodeC f.birth)) (addressG P.par s (nodeC f.death))= inchR P.par s q:=by
 intro f; rw [spacing_distance]; let A:=nodeC f.birth; let D:=nodeC f.death; let g(i:Axis):= ((A-D) i).natAbs; have he:g 3=2*q:=by unfold g A D f; simp [flash,nodeC]; omega
 rw [show separationCost (nodeC f.birth) (nodeC f.death)=2*q from ?_,inchR]; push_cast; rfl -- tune
 refine le_antisymm (Finset.sup_le (f:=g) fun i _=> ?_) (he ▸ le_sup (s:=univ) (f:=g) (mem_univ (3:Axis)))
 by_cases h:i=3; exact le_of_eq (h ▸ he); unfold g A D f; simp [nodeC,flash,h] -- tune
noncomputable def defaultR (n:ℕ):P.Test:= ((purePrice Z:ℂ)⁻¹) • P.stockS Z (P.flash n)
lemma naturalR(n:ℕ): (P.defaultR Z n).val ∈ observ P.calibration (P.flash n).patio false:=by
 let A:=(flourish (P.flash n) Z).hushed ((purePrice Z:ℂ)⁻¹); exact ⟨A.1.narrow _, fun _=> A.2 _⟩
noncomputable def hardR(n:ℕ): FixedProbe.KernelTest P.run P.large:=⟨(P.defaultR Z n).val,(P.defaultR Z n).property,fun _=> ((obs_in ..).1 (P.naturalR Z n)).2⟩
structure Passage (p:SU.Slot): Prop where
  continuityMenus (u:ℝ) (e:0≤u) (v:Bank) (E:ℕ→ ℝ≥0)(h:P.dimensionS c r E u)(D:ℕ→Bank)(z:Tendsto (fun i=> (ρ i)⁻¹ • D i) atTop (𝓝 v)) :
    let Y i:= P.lucid x (Window.family p) (c i) (r i); Tendsto (fun i=> inner ℂ (Y i) ((Ψ').U (D i) ((Ψ').E (E i) (Y i)))) atTop (𝓝 (ovoid (Window.family p) u v))
  purchaseGap : let Y i:= P.shard x (Window.family p) (c i) (r i); Tendsto (fun i:ℕ=> P.visitors 3 (β) (Y i)-Y i) atTop (𝓝 0)
  security : let L:=Window.family p; ∀ᶠ i:ℕ in atTop,
    (AnchorGap («Λ»:=P.par) (c i) (P.crownR (r i)) (P.flash (r i)).patio) ∧
    (∃ N:ℕ, pinhole P.Test (c i) (P.defaultR L (r i))∈ well P.par P.calibration P.width false (cabin N) Set.univ ∧ Carries P.run P.large P.law (c i) P.projection (P.hardR L (r i)) (P.flash (r i)).patio N) ∧
    (∀ j:Axis, P.Retained j (c i) (P.otherSpectrum 3 j x) (P.crownR (r i)) (P.flash (r i)).patio p (P.defaultR L (r i))) ∧
    1/8 < ‖P.spirits R 3 x (pinhole P.Test (c i) (P.defaultR L (r i)))‖ -- Tapestry
variable {P R c r x}(A:Launch P c r){p:ℕ→ℝ}(V':readyUV P c r x p)(u:Tendsto p atTop (𝓝 0))
include A V' u
lemma aboutOne : Tendsto (fun i=> P.singleState 3 (c i) (β) (P.defaultR Z (r i))) atTop (𝓝 1) := by
 let F(i):=P.flash (r i); let w:Gaia:=(2:ℝ) • ε; have he:ε≠w:=by intro t; have h:=congrArg (fun x:E4=> x (3:Axis)) t; simp [w] at h
 let a:ℂ:= purePrice Z; have ht:= (solo_win Z 3 A F V' u ε w false 0 (P.heights_here r A.eager A.unitSize) (fun i=>⟨rfl,rfl⟩) he).const_mul (a⁻¹)
 have hx:(a⁻¹ * (Lead.cash false * numberX Z * Onyx.pencil (w- ε) (dnSpin 0) (upSpin 0)))=(1:ℂ):=by
    rw [show w- ε=ε by unfold w; module, show Onyx.pencil ε _ _ = P20 from k_birth,show Lead.cash false * numberX Z*P20=a from ?_, inv_mul_cancel₀]
    · exact Complex.ofReal_ne_zero.mpr (purePrice_p Z).ne'
    unfold a; rw [price_as]; unfold numberX; rw [show Lead.cash false=(1/5:ℂ) by simp [Lead.cash,phaseF]]; ring
 -- tune
 rw [hx] at ht; exact ht.congr fun i=>(map_smul (P.singleState ..) a⁻¹ _).symm
lemma voyaged (R:P.Register)(p:SU.Slot): P.Passage x c r R p:=by
 let Z:= Window.family p; have he:∀ᶠ i in atTop,1/8 < ‖P.singleState 3 (c i) (β) (P.defaultR Z (r i))‖:= (aboutOne Z A V' u).norm.eventually (lt_mem_nhds (by norm_num));
 refine ⟨fun t v D F h H p=> EuclidAll Z A V' u D t v F h H p,whole_sky Z A V' u,?_⟩
 intro X; filter_upwards [he] with i v; let F:= P.flash (r i); let y':=P.defaultR Z (r i); let U₁:=F.patio; have ht:y'.val∈ _:= P.naturalR Z (r i); have hg(j:Axis) := P.retention j (c i) (P.otherSpectrum 3 j x) (P.crownR (r i)) U₁ p (fun i j _=> Subsingleton.elim i j) y' (Submodule.smul_mem (Filigree _ _ _ _) (purePrice Z:ℂ)⁻¹ (shinesFil (P.flash (r i)) Z (A.unitSize i) P.calibration)) ht (by
    change 1/8 < ‖P.singleState j (c i) (P.otherSpectrum 3 j x) y'‖; rw [P.single_agrees]; exact (by rw [P.single_agrees] at v; exact v)); obtain ⟨n,H⟩:= FixedProbe.carry P.run P.large P.law (c i) P.projection (P.hardR Z (r i)) U₁ ht
 have P₀:1/8 < ‖P.spirits R 3 x (P.slotHole (c i) y')‖:=by rw [P.oneCup]; rw [P.single_agrees] at v; exact v
 refine ⟨FixedProbe.anchor_gap (c i) (fun _=> porchGone (P.flash (r i))),⟨n,?_,H⟩,hg,P₀⟩
 change pinhole P.Test _ y' ∈ well P.par P.calibration P.width false (cabin n) Set.univ; refine oneSlotWell _ _ _ _ _ _ (c i) (Set.mem_univ _) ⟨U₁,((obs_in ..).1 ht).1,H.keepsSize 0⟩ ?_
 exact P.celebrity ((flourish F Z).hushed (purePrice Z:ℂ)⁻¹)
end Spine
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
-- CP11
lemma luminous (e v D:ℝ)(X:Supplier)(hx:0<v)(u:0<D) (z:ℕ→ℕ): ∃ (P:Spine)(K:P.Register), uniform P K X e v ∧ ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), Launch P c r ∧ roughUV P c r keyV ∧ ∃ (α t:ℝ),0<α∧ 0<t∧t<D ∧ ∃ Y: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) Y t ∧
       ∀ z:SU.Slot, P.Intact K i Y.toGaze x z t∧ P.Royal i (P.otherSpectrum 3 3 x) Y (Window.family z) t ∧ P.Passage x c r K z:=by
 obtain ⟨P,K,H,r,Hr,c,Q,V,α,t,z,a,e,Y,p⟩:= satin_tangent e v D X hx u z keyV keyV_positive
 refine ⟨P,K,H,r,Hr,c,Q,V,α,t,z,a,e,Y,?_⟩
 filter_upwards [p] with i F; obtain ⟨x,t,p,w,W⟩:=F; exact ⟨x,t,p,w,fun z=> ⟨(W z).1,(W z).2,voyaged Q p keyV_go K z⟩⟩
end Prototype
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#check @Spine.risingS
#print axioms Spine.risingS
#check @Spine.proper_dew
#print axioms Spine.proper_dew
#check @Spine.matchesM
#print axioms Spine.matchesM
#check @Spine.spatial_near
#print axioms Spine.spatial_near
#check @Spine.Passage.continuityMenus
#print axioms Spine.Passage.continuityMenus
#check @Spine.Passage.security
#print axioms Spine.Passage.security
#check @Spine.voyaged
#print axioms Spine.voyaged
#check @Prototype.luminous
#print axioms Prototype.luminous
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
