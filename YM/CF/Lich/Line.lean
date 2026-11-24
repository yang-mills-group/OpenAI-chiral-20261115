import YM.CF.Lich.Rank
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lich
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
-- separate path ledger Φ.M.Target.S.P
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x e:ℝ)(T:Tube SU.group S)
variable{r n j d:ℕ}
namespace Muster
variable{G S x e T}
variable(A:Muster G S x e T)
variable(U: Monk SU.group S)(V W:Rent0 G e) -- V true W at ζ=0
local notation "θ"=> A.room
local notation "j"=> A.loft
local notation "β"=> A.beta
local notation "q"=> A.trot
local notation "α"=> A.ang
local notation "γ"=> A.fee
local notation "l"=> A.post
local notation "F"=> U.sent x T q θ l β
local notation "Y"=> (U.park,U.k)
local notation "K"=> U.key.dome (j*radiusB x)
local notation "Q'"=> A.LawQ
local notation "YY"=> A.Beds
-- account per site
-- far components plus interior.Optional momentum.
open Corne
lemma comet {ι Kb E:Type*}[Fintype Kb][DecidableEq Kb][AddCommMonoid E](i:Finset ι)(f:ι→Kb)(u:ι→E): ∑ t:Kb,∑ k∈i with f k=t, u k= ∑ k∈i,u k:= Finset.sum_fiberwise i _ _ -- tune
lemma waving (L:Finset (Hos S r))(Dt:Hos S r→ Signed→ℝ): (∑ i∈L,averaged (Dt i))=averaged (fun s=>∑ i∈L,Dt i s):=by unfold averaged; rw [←mul_sum, sum_comm (f:=Dt)]
lemma paid_r{ι Kt:Type*}[Fintype ι][DecidableEq ι][AddCommMonoid Kt](X:Finset ι)(P Q:ι→Kt): (∑ i,if i∈X then P i else Q i)=(∑ i∈X,P i)+∑ i∈Xᶜ,Q i:=by
 let Dt(i:ι):=if i∈X then P i else Q i; rw [←sum_add_sum_compl X Dt]; refine congrArg₂ (·+·) (sum_congr rfl (fun i p=>?_)) (sum_congr rfl (fun i p=>?_)); exact if_pos p; exact if_neg (mem_compl.mp p)
lemma wisp : ∑ i, wish A U i= -β*averaged (fun s=>∑ i∈ rush x U.key s j,shotB (dense T x q θ l β s i) U):=by unfold wish; simp_rw [←mul_sum]; unfold averaged; rw [← mul_sum,sum_comm]; simp_rw [comet]
-- orientation
abbrev taxT := ∑' k:ℕ,∑ i:Site (Domain N B),penR T x q θ l U (k+3) i
local notation "L"=> blip S U.key r
lemma bandB (p:(j+104)*radiusB x+10≤r): ∑ i∈L,gemG A U i.val=gemG A U U.key:=by
 let b:=(j+104)*radiusB x; let Ew(o:Stores S):= locals U.key o x U.park b
 have hp:Ew U.key=(L).biUnion fun i=>Ew i.val:=by
    have Z(i:Active U.key x U.park)(O:Stores S): i∈ Ew O ↔ tastes S i.val.val (O.dome b):=by simp [Ew,locals,witnesses,tastes]
    ext i; rw [mem_biUnion,Z]; constructor
    · intro k; rcases k with k|k
      · obtain ⟨v,p,t⟩:= (totalX r _).1 k; exact ⟨_,p,(Z i v.val).mpr (Or.inl t)⟩
      obtain ⟨v,p,t⟩:= (totalX r _).1 k; exact ⟨_,p,(Z i v.val).mpr (Or.inr t)⟩
    rintro ⟨v,p,t⟩; exact Or.imp (fun x=>(pack S v p).inside b x) (fun x=>(pack S v p).inside b x) ((Z ..).mp t)
 have htH:b+2≤r:=by unfold b; omega
 have hr : Set.PairwiseDisjoint (L:Set (Hos S r)) fun i=> Ew i.val:= by intro i t k g w; exact Finset.disjoint_left.mpr fun z g' s=>w (split_w S U.key z.val.val _ _ t g (mem_filter.mp g').2 (mem_filter.mp s).2 (by simp [htH]))
 unfold gemG; change _=∑ i∈Ew U.key, _; rw [hp,sum_biUnion hr]
lemma pure_s (p:(j+104)*radiusB x+10 ≤ r): ((gearC T x q θ (α+γ) l U β A.vita A.rota j r A.muK A.mup A.phaseUp A.phaseLow:ℝ):ℂ)= ((arcD T x U+taxT A U+tollG A U+(∑ i∈L,soreG A U i.val):ℝ):ℂ)+∑ i, per A U i:=by
 let U':=∑ i∈L,soreG A U i.val; let Z:=∑ i:Site (Domain N B),(yurn A U i+blunt A U i+artU T x q θ l U i)
 rw [show ∑ i,per A U i=(Z:ℂ) from (Complex.ofReal_sum ..).symm, ←Complex.ofReal_add]; apply congrArg Complex.ofReal
 let Q(s:Signed):=(∑ i,leftV T F s U.key q A.phaseUp x β i)-∑ i,rightV T U.V s U.key A.phaseLow x (α+γ) β i; let X(s:Signed)(z:Hos S r):=∑ i∈strum x s z.val j, heatR T F U.V s U.key q A.phaseUp A.phaseLow x (α+γ) i
 have he: veil T x q θ (α+γ) l U β j r A.phaseUp A.phaseLow=averaged Q+ ∑ i∈L,averaged (fun s=>X s i):=by rw [waving]; unfold Corne.veil; exact av_add .. -- tune
 unfold gearC archQ warmth junk brawn; rw [he]; unfold Z;
 rw [sum_add_distrib,sum_add_distrib]; unfold yurn blunt footS; rw [sum_add_distrib, sum_add_distrib,sum_add_distrib,← mul_sum,wisp,comet _ (fun i:Bond _=>S.ratio.parent i.1),paid_r _ (fun i=>kite T x q θ l U β A.vita A.rota i+qerr T x q θ l U i)]; unfold soreG; rw [sum_sub_distrib, sum_sub_distrib,bandB A U p]
 unfold Q X taxT bus tollG gemG Corne.jewel qerr; simp only [sum_add_distrib,sum_sub_distrib]; ring
lemma grand_g (p:(j+104)*radiusB x+10≤r) : plaza A U V W r= ((arcD T x U+taxT A U+tollG A U+(∑ i∈L,soreG A U i.val):ℝ):ℂ)+ (∑ i,burnS A U V W i)+posy G Q' x V YY:=by unfold plaza; rw [pure_s A U p]; unfold burnS Muster.lore prum; rw [sum_add_distrib,sum_sub_distrib,sum_sub_distrib,paid_r _ (fun i=>fJ G Q' x YY i-fJ G Q' x V i)]; unfold scenic pearQ rockS; abel
end Muster
end YM.CF.Lich
