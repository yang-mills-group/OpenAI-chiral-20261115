import YM.CF.Tye.Life
import YM.CF.Tye.Sheer
import YM.CF.Lich.Spear
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Tye
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "Y"=> clue S s b M
local notation "V"=> shiftZ g M
local notation "F"=> cedar M
variable (h:K.Funds S T)(hp:FreeResolvent.Gap (baseX T x M.key M.park M.k M.V) m)(hv:120 ≤ radiusB x)(hz:0 < m)(hA: Reef.Rare T.up)(hB:Reef.Rare T.down)(ht: LocalRatio A.vita)(hi:0 < A.rota)(hm:4*A.rota < A.vita.radius)(hb:0 < A.beta)
local notation "j"=> A.loft
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "L"=> Stores.till x
variable(i:Site (Domain N B))(O:Stores S)
local notation "n"=> A.post
local notation "q"=> A.trot
local notation "r"=> A.room
local notation "β"=> A.beta
-- rebalanced pluck.
abbrev flockK : ℝ:= ∑ t:Bond d', ansC (S:=S) i t * opus T x A.trot A.room A.post A.beta j t M
local notation "W"=> calendar x M.key M.park
include h hp hz hv
variable (v:Site (Domain N B))
local notation "e'"=> affine s b i
lemma wish_s : Muster.wish A Y i= Muster.wish A M e':=by
 unfold Muster.wish; apply congrArg (-β*·); apply av_a s; intro t; refine sum_equiv (lawn S (Channels.offset s b t)) (fun i'=>?_) (fun v _=> Rink.heat_s T x M q r n β h hp hz hv s t b v)
 simp only [Cay.rush,clue,mem_univ,mem_filter,true_and,dome_map, herZ]; refine and_congr Iff.rfl ?_; rw [←herZ]; exact (StepData.sendSites s b).injective.eq_iff.symm
lemma wish_g:Muster.wish A V i=Muster.wish A M i:=by unfold Muster.wish; simp_rw [Rink.heat_g T x M q r n β h hp hz hv]
include hA hB hb
lemma wish_f: Muster.wish A F i=Muster.wish A M i:=by unfold Muster.wish; simp_rw [←Rink.heat_f T x M q r n β h hp hz hv hA hB hb] -- Heat_f hr?
lemma flock_f: flockK A F i=flockK A M i:=by unfold flockK; simp_rw [Rink.burn_e T x M q r n β h hp hz hv hA hB hb]
omit hA hB
lemma flock_s : flockK A Y i=flockK A M (affine s b i):=by
 unfold flockK; nth_rw 2 [← Equiv.sum_comp (diagram s b S)]; exact sum_congr rfl fun t _=> congrArg₂ (·*·) (ansP s b (S:=S) i t).symm (burn_t T x M q r n β h hp hz hv hb s b j t)
lemma flock_g: flockK A V i=flockK A M i:=by unfold flockK; simp_rw [burn_g T x M q r n β h hp hz hv hb]
omit hb
include ht hm hi
lemma sore_s : soreG A Y (Locations.book s b O)= soreG A M O:=by
 unfold soreG; rw [oak_s T M x q r n β O h hp hv hz]; refine congrArg₂ (·-·) (congrArg₂ (·-·) rfl (av_a s _ _ fun t=>?_)) ?_
 · refine sum_equiv (lawn S (Channels.offset s b t)) ?_ (fun i _=>heat_s T M x q r n β h hp hv hz s b t _ _ _ i); intro i; simp only [strum,mem_filter,mem_univ,true_and,dome_map,herZ]
 unfold gemG; refine sum_equiv (W s b).onKey (fun i=>?_) (fun i _=> Tye.flare_s T M x q r n β h hp hv hz _ _ ht hi hm s b _)
 unfold locals; rw [mem_filter,mem_filter]; simp only [mem_univ,true_and]; exact witnessP O s b ..
lemma sore_g : soreG A V O= soreG A M O:=by
 unfold soreG; rw [oak_g T M x q r n β O h hp hv hz]; refine congrArg₂ (·-·) (congrArg₂ (·-·) rfl (congrArg averaged (funext fun t=>?_))) ?_
 · exact sum_congr rfl fun i z=>heat_g T M x q r n β h hp hv hz t g _ _ _ _
 exact sum_congr rfl fun i z=>flare_g T M x q r n β h hp hv hz _ _ ht hi hm g _
include hA hB
lemma sore_f : soreG A F O= soreG A M O:=by
 unfold soreG; rw [oak_f T M x q r n β O h hA hB hp hv hz]; refine congrArg₂ (·-·) (congrArg₂ (·-·) rfl (congrArg averaged (funext fun t=>?_))) ?_
 · exact sum_congr rfl fun i z=> heat_f T M x q r n β h hA hB hp hv hz t _ _ _ _
 exact sum_congr rfl fun i z=> flare_f T M x q r n β h hA hp hv hz _ _ ht hi hm _
end YM.CF.Tye
