import YM.CF.Yaw.Quartz
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees Rill Atala
attribute [local instance] opCStarAlgebra
local notation "G_"=> SU.group
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B)) (G:Ratio (mid N B) (mid P B))(φ:S.ratio=Rush.ratio G)
local notation "c₁"=> Domain N B
local notation "c₂"=> Domain P B
variable {r l n k k' m:ℕ}(x d e s s' K τ B₀:ℝ)(q h:Chi)
variable{S} (U:Loom (mid N B))(V:Loom (mid P B))(T:Tube SU.group S)
variable {e s s' d x K τ B₀} {t v b b' a β e0 v':ℝ}
local notation "B'"=> radiusB x
local notation "k_"=> ((l+90)*radiusB x)
local notation "bay"=> Stilo.bay
variable (M:Monk SU.group S)(J: List (Kite S r))(p:M.key=cook S J.toFinset)(A:Ride S) 
local notation "F"=> erosion ((l+70)*radiusB x) (bay A)
local notation "Y"=> (((M.V,M.U,β,M.z):HomeL (Domain N B) (Domain P B)))
local notation "D"=> cusp M.key x M.V
variable {J':Teller SU.group}
variable (hp:30*radiusB x ≤ r)(hx:1000≤radiusB x)(vK:∀ i∈ J.toFinset,Lattice.halo ((l+90)*radiusB x) (Eire.frameP S i)⊆Stilo.bay A)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (I:E→L[ℝ] Directions SU.group (Domain N B))
local notation "Z_"=> (fun i=>Rill.TasteZ.hover M.V I i x Y)
local notation "K_"=> (monkD M ∘ Z_)
local notation "Nc"=> ({M with key:=cusp M.key x M.V}:Monk SU.group S)
variable (z':Ids (mid P B))(z:Ids (mid N B)) (U': E→ Rill.Arch G e)
include U V φ p hp hx vK
lemma pure_v(p0:pureK S J.toFinset)(RP:Rill.MarkP M F x s s' Y l n T q d)
 (pu:Roof (mid N B) s t k' U)(pv:Roof (mid P B) s v k V)(p2:k+k'≤radiusB x)(p3:s' <firstRadius SU.group)(hq:0<s')(hV:s≤e0)(w:∀ i,((U' i).val.1∈ {v|JointB G v e0}) ∧ Guard (U' i).val.2 e0)(c:∀ i,Eire.Clan G S (T:=T) φ z z' (K_ i) U V q h l x d s' β (U' i)) : ∀ᶠ i in 𝓝 (0:E),HullK S (20*radiusB x) J.toFinset (U' i).val.1.1 (U' i).val.2 e0:=by
 have he: Continuous Z_:=by unfold TasteZ.hover Vmove increment; fun_prop
 have hz: Z_ 0=Y:=by simp [TasteZ.hover,Vmove]
 filter_upwards [(show ContinuousAt Z_ (0:E) from he.continuousAt).eventually (p:=fun y=>MarkP M F x s s' y l n T q d) (by rw [hz]; exact mead RP p3)] with i ih
 exact watt G S φ A z z' (show Rill.Arch G e0 from ⟨_,w i⟩) (show PaneL (K_ i) F x s s' _ from MarkP.toPaneL ih) (skyC S A) J.toFinset vK p hx hp hV pu pv p2 p3 hq (c i) p0
omit φ p hp U V hx
include vK
lemma query_l (j:Kite S r)(u:j∈J):(halo ((l+90)*radiusB x) (hatY S (j.2.1∪j.2.2)) ⊆ Stilo.bay A):=by refine (chilling le_rfl ?_).trans (vK _ (List.mem_toFinset.mpr u)); unfold Eire.frameP; rw [union_assoc]; exact (image_subset_image subset_union_right).trans subset_union_right
omit vK
open Phase Acorn Spire
lemma pool_m(X:Support (Domain P B))(g:1≤ K)(p:BeamV G e U' n X τ 0)(j:Kite S r)(h:j∈J)(hj:X=j.2.1 ∪ j.2.2)(A':Finset (Hos S r))(u:∀ (V:E→SU.E),Tender V 0 τ n→ Allows n (SU.fund ∘ V) 0 1): let U(i):= printG S (20*radiusB x) (U' i).val.1.1 (U' i).val.2 A' j.1; ∀ b:Bool,∀ i:Bond (Domain P B),Skye.ends i ⊆ X → Allows n (fun v=>SU.fund (U v b i)) 0 1:=by
 intro U b i hp; have hg(Q:Finset (Hos S r)):Allows n (fun y=>SU.fund (valve S (U' y).val.1.1 (U' y).val.2 Q (20*radiusB x) i)) 0 1:=by unfold valve; split; exact u _ (p.1 i hp).2; exact u _ (p.1 i hp).1
 cases b<;>exact hg _
-- Mark from EP.True TSUPPORT studies.V. need pulse.Cost_m on /t∈κ.P. old.
end YM.CF.Yaw
