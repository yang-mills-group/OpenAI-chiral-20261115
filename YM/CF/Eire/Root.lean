import YM.CF.Eire.Wing
import YM.CF.Rill.Sot
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Eire
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(u:S.ratio=Rush.ratio G) (z:Odd G.count.val)(e:ℝ)(g:0<e)(X: Meter TailB G e)(V: Meter Grave G e)
structure ReefT :Prop where
 sail i Y: ∃ C: Toll (Iota G), Suite (badge _) (pinH G e true) (pinH G e false) Y C (X i Y)
 flow i Y: ∃ C:Toll (Iota G),Suite (badge _) (pinH G e true) (pinH G e true) Y C (heal G e V i Y)
local notation "bay"=> Stilo.bay
abbrev Ride(S:StepData (Domain N B) (Domain P B)):=Crowd (Site (Domain N B))
variable (T:Rill.Arch G e)(W:Ride S)
def gleans(k:ℕ)(H:Ride S): Finset (Support (Domain P B)):= univ.filter fun Y=> beamH (halo k (hatY S Y))≤ H
def cala (k:ℕ)(H:Ride S): Weave (Single (mid P B)) (Single (mid N B)):= portX (switchG G).symm (postH G (bring g T) z X V (Subtype.ext (Prod.ext (revI T.val.1) (ice_pr _))) (gleans S k H)) -- names tune
abbrev mint(i:Single (mid P B)):= S.ratio.parent (node i.1.1)
abbrev mintK(H:Ride S):Set (Twig (Single (mid P B))) := hearth (mint S) (bay H) -- Twig namespace?
variable (k:ℕ) (f:ReefT G e X V)
omit z u
lemma till {s t:Bool}{C: Toll (Iota G)}{Y:Support (Domain P B)}{F:cro G e→ Op (Iota G)} (p: Suite (badge _) (pinH G e s) (pinH G e t) Y C F) (x:cro G e)(i j:Iota G) (h:F x i j ≠0):lookM G i∈Y ∧ lookM G j∈Y:=by
 let k:= p.expo i j; exact (k.triggered (ne_of_gt ((norm_pos_iff.mpr h).trans_le (k.bounded x)))).2
local notation "α"=> tinOre (switchG G).symm
abbrev rayB (i:Dwell (mid N B)):= node i.2.1.1
lemma melt (i:Twig (Single (mid P B))): mint S (twigS i).2=S.ratio.parent (lookM G (twigS (α i)).2):=by cases i with| inl i=> change _=S.ratio.parent (node ((switchG G ((switchG G).symm i.2)).1.1)); rw [Equiv.apply_symm_apply]; rfl| inr i=> change _=S.ratio.parent (node ((switchG G ((switchG G).symm i.2)).1.1)); rw [Equiv.apply_symm_apply]; rfl
include z u f
lemma snail (H:Ride S)(i:Twig (Single (mid P B)))(j:Dwell (mid N B))(h:(cala G S z e g X V T k H).seats i j≠0): mint S (twigS i).2 ∈ bay H ∧ rayB j∈ bay H:=by
 change Urn.mount (LenT G e X (bring g T) _) _ j≠0 at h
 let i':=α i; change Urn.mount _ i' j≠0 at h; unfold Urn.mount LenT Radix marge at h; dsimp only at h; split at h; swap; contradiction
 let L:= (tallC i', (twigS i').1); have hu:∑ Y∈gleans S k H,X L Y (bring g T) (twigS i').2 (patchQ G j.2) ≠ 0:=by intro p; apply h; simp only [Matrix.submatrix_apply,id, Matrix.sum_apply]; rw [show ∑ Y∈_,X _ _ _ _ _=0 from p]; simp [Scroll.cSignX]
 obtain ⟨Y,w,d⟩:= exists_ne_zero_of_sum_ne_zero hu; obtain ⟨C,l⟩:= f.sail L Y; obtain ⟨hx,hg⟩:= till G e l (bring g T) _ _ d
 let A':= hatY S Y; have he: A'⊆ bay H:= (halo_subset k A').trans ((Eq.le (bay_beam _).symm).trans (bay_m (mem_filter.mp w).2)); rw [trK G _ z,←u] at hg; refine ⟨?_, he ((show S.ratio.parent (S.ratio.embed (rayB j))= rayB j from Ratio.embed_parent ..) ▸ mem_image_of_mem S.ratio.parent hg)⟩; rw [melt G]; exact he (mem_image_of_mem _ hx)
end YM.CF.Eire
