import YM.SU5.Reconstruction.Trap.Ballet
import YM.SU5.Reconstruction.Trap.Invariant
import YM.SU5.Reconstruction.Trap.Dusk
/-!
# Picket in the Reconstruction setup. same character.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock ConePrice SelectionAnalysis Germ Chambers
open CrossedFrame
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
local notation "D" => Domain Y H G false
local notation "Ds" => Domain Y H G true
local notation "Gt" => marks (timeMesh Λ)
variable (C : ∀ j, Arena Y H G.history.circuit j 0 false)
variable (a:Axis)
variable (χ : displayAlgebra Y H V G.history G.clipped a false (C a) →⋆ₐ[ℂ] ℂ)
local notation "w" i:max=> displacement Y H V G.history G.clipped a false (C a) χ i (C i)
local notation "J₀" i:max=> indoor Y H V G.history G.clipped i false (C i) (w i)
local notation "C₀" i:max=> saunters Y H V G.history G.clipped i false (C i) (w i)
local notation "G₀" i:max=> fort Y H V G.history G.clipped i false (C i) (w i)
local notation "Ω₀" i:max=> vocation Y H V G.history G.clipped i false (C i) (w i)
local notation "S₀" i:max=> peninsula Y H V G.history G.clipped i false (C i) (w i)
local notation "ℜ" p:max=> Real.toNNReal (p:ℝ)
local notation "Pr" i:max=> bridgeEstate Y H V G i (C i) (w i)
local notation "Vo" i:max=> coreOs Y H V G i (C i) (w i)
local notation "Os" i:max=> compassKet Y H V G i (C i) (w i)
local notation "θ" i:max=> flipMark i (tent Y H)
variable (j j' : Axis) (hv:j'≠j)
local notation "N" i:max => flank i 0
local notation "Globe" => (N j ∩ N j')
local notation "L" i:max=> lowland i 0
local notation "Tea" => (L j ∩ L j')
variable {S:Hilbert} (Z:Clasp S (fort Y H V G.history G.clipped j false (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j))) (fort Y H V G.history G.clipped j' false (C j') (displacement Y H V G.history G.clipped a false (C a) χ j' (C j'))))
variable {r e:ℝ} (p:0≤r)(v:0<e)
-- vacuum & coordinates in both clocks. preserving Ports. no claim Poincare group relations.
lemma comesHome : compassKet Y H V G j (C j) (w j) (⟨1,domain_one ..⟩) = Ω₀ j:= by
 let y:= (⟨1, domain_one ..⟩: Ds (N j))
 unfold compassKet vocation
 have h:= vacuum_ticket Y H V G j (C j) (w j)
 exact congrArg ((C₀ j).orthogonalProjectionOnto) h
lemma backHome (U:Set RSpace)(b: mirrorE j 0 '' U ⊆ N j) : flipLens Y H V G C a χ j U b (⟨1,domain_one ..⟩ : Ds U)= Ω₀ j:= by
 rw [← comesHome Y H V G C a χ j]; exact congrArg (Os j) (Subtype.ext (flipMark_unit ..)) -- tune
local notation "β" i:max=> Ivory Y H V G i (C i) (w i)

/-- The intertwiners are of the chosen sector. For any Clasp passing...
Positive quadr joint tests & dual on same characters even BEFORE Macc. -/
structure Quarter : Prop where
 port: Brigade Y H V G C a χ j j' hv S Z
 tC:Picket.Beam hv (S₀ j) (S₀ j') Z ∧ Picket.Behind (S₀ j) (S₀ j') Z
 vacuum: Z.look (Ω₀ j)= Ω₀ j' ∧ ∀ u:ℝ,Picket.boost Z u (Ω₀ j)=Ω₀ j
 calendar (u:ℝ≥0): Z.look.toContinuousLinearEquiv.toContinuousLinearMap.comp ((S₀ j).E u)=((S₀ j').E u).comp Z.look.toContinuousLinearEquiv.toContinuousLinearMap
 both (x:E4): Z.look.toContinuousLinearEquiv.toContinuousLinearMap.comp ((S₀ j).unit.translation x)= ((S₀ j').unit.translation (Picket.quarter j j' x)).comp Z.look.toContinuousLinearEquiv.toContinuousLinearMap
 spins (u:ℝ): Pays (Picket.boost Z u) ∧ Picket.Boosts (S₀ j) u j' (Picket.boost Z u)
-- continuity & group within this jk `boost` in Picket already
include p v
variable (hb: Ivory Y H V G j (C j) (displacement Y H V G.history G.clipped a false (C a) χ j (C j)) r e)(hc: Ivory Y H V G j' (C j') (displacement Y H V G.history G.clipped a false (C a) χ j' (C j')) r e)
include hb hc
lemma quartered : ∃ (S:Hilbert)(Z:Clasp S (G₀ j) (G₀ j')), Quarter Y H V G C a χ j j' hv Z:= by
 obtain ⟨A,B⟩:= grants Y H V G j (C j) (w j) p v hb; obtain ⟨R,Q⟩:= grants Y H V G j' (C j') (w j') p v hc
 obtain ⟨S,Z,h⟩:= people Y H V G C a χ j j' hv A R (B j' hv) (Q j hv.symm); have b:= onBeam Y H V G C a χ j j' hv Z A R h; have k:= onStreet Y H V G C a χ j j' hv Z A R h
 refine ⟨S,Z,h,⟨b,k⟩,Picket.victory Z _ _ ?_ ?_, Picket.looksHeat hv _ _ Z (B _ hv) (Q _ hv.symm) b, Picket.look_bill hv _ _ Z (B _ hv) (Q _ hv.symm) b k,fun x=> ⟨Picket.boost_pays ..,Picket.boost_bill hv _ _ Z (B _ hv) (Q _ hv.symm) b k x⟩⟩
 · rw [← comesHome Y H V G C a χ j, ←comesHome Y H V G C a χ j']; exact h.sees (⟨1,domain_one ..⟩:Ds Globe)
 intro x; have he:= h.meets (⟨1,domain_one ..⟩ : Ds Tea) x
 rw [←backHome Y H V G C a χ j Tea (top_ready j j' hv), ← backHome Y H V G C a χ j' Tea (low_ready j j' hv)]; exact he
omit hb hc
local notation "Mu"=> saunters Y H V G.history G.clipped
-- panel-to-driver existing separate lift; here actual selected consumer
structure StageT(e r:ℝ) : Prop where
  purchases (j:Axis): (β j) r e
structure BoostBacking : Prop where
  present (j:Axis): C₀ j=⊤
  forward (j:Axis): ConePrice.Forward (S₀ j)
  circles (j j':Axis)(p:j'≠j) : ∃ (S:Hilbert)(Z:Clasp S (G₀ j) (G₀ j')), Quarter Y H V G C a χ j j' p Z
/-- Finally THIS normalization receipts: use only stencil estimate `Ivory` at arbitrary small cutoff, only ONE direction on a pair of observations. Not assuming strengths on slits, parity aliases etc. Equivalence relies on ACTUAL selected law, through this pupil. If obstruction, then to retaining full theory with the physical spectrum under these same clocks. If estimate purchased, then not just temporal E continuity or SNAG but full spatial & even Finer correction (other CP4 receipt when use), full forward cone by iterating the new boosts, and genuine identification across the Hilbert spaces with quarter-frame Wick polar communications (same light-frequencies & all continuous translations/vac, normalized clock even its heat). -/
theorem real_boost_purchase : StageT Y H V G C a χ e r ↔ BoostBacking Y H V G C a χ:= by
 constructor
 · intro h
   have k (j j':Axis)(u:j'≠j): ∃ (S:Hilbert)(Z:Clasp S (G₀ j) (G₀ j')), Quarter Y H V G C a χ j j' u Z := quartered Y H V G C a χ j j' u p v (h.purchases j) (h.purchases j')
   let t(j):= grants Y H V G j (C j) (w j) p v (h.purchases j)
   refine ⟨fun i=>(t i).1,fun i=> Picket.endLight (S₀ i) (fun j j' u=>?_) (t i).2,k⟩
   obtain ⟨S,Z,p⟩:=k i j j'; exact ⟨Picket.boost Z u,p.spins u⟩
 intro h; exact ⟨fun i=> twoShotPays Y H V G i (C i) (w i) ((true_spectrum Y H V G i (C i) (w i) p v).2 ⟨h.present i,h.forward i⟩)⟩
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.LightBudget
