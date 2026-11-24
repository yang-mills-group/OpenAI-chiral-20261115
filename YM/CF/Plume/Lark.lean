import YM.CF.Plume.Wager

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Plume
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
variable {N P B:Side}(S:StepData (Domain N B) (Domain P B))(x:ℝ)
local notation "G₀"=> SU.group
local notation "n₀"=> (Domain N B)
local notation "m₀"=> (Domain P B)
local notation "Tabs"=>Arena.Tab S
variable{S}
open scoped Classical ENNReal NNReal
open Girt Next.Fluctuations.Sector Dial
open Lich
-- active Modes: for Shape Y plan agreement full on X.
variable{k b l k1 k' o₁ o₂ r r' j:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]
local notation "bay"=> Stilo.bay
variable {X: Support (Domain N B)}{H H':Ride S}
variable{G:Ratio (mid N B) (mid P B)}{e:ℝ}{Q:GramM (mid P B)}
set_option pp.universes false
variable {V V':Orbit (mid N B)}{y y':Cord S}{K K':Ids (mid P B)}
variable {X0:ι→Palot.leaf (Site (Domain N B))}{i:Troupe S r ι}{t:ℝ}
local notation "U₀"=> cort V.1 y
local notation "U'"=> cort V'.1 y'
local notation "AX"=> BranchX S X0 k
local notation "ScopeF"=> Passage S
variable (h:Spark (Stilo.bay H) y y')(p:Palot.fits (BranchX S X0 k) i H)
variable {A₀:Side}{e:ℝ}{j κ n μ:ℕ}{ho:Odd A₀.val}{Y:Pricing j A₀ ho (Thread j)}{P':Grasp Y B e}{M:Male}{I:Aim (mid P B)}{I':Pec.Pride (mid P B)}{v v' g g' t t' w Z α ι₀:ℝ}
variable (A: Dress G S e r k' (cort V.1 y) Q k X0)(B':Dress G S e r k' (cort V'.1 y') Q k X0)
local notation "µ"=>A.wage
local notation "t₀"=>A.coats i
local notation "t₁"=>B'.coats i
variable {q:Chi}{T:Tube SU.group S}
include h p
lemma shades_l (a:Lattice.Agrees (bay H) V.1 V'.1)(o:k=(l+90)*radiusB x)(b:1000≤radiusB x)(k':Ready A.pipe x)(ζ:A.pipe=B'.pipe)(u:A.wage=B'.wage)(e:A.chi=B'.chi)(s:A.cloth=y.2.2)(s':B'.cloth=y'.2.2) : A.bodyL x l i=B'.bodyL x l i:=by
 have hp:= h
 unfold Dress.bodyL Eire.lure; rw [←ζ,←u,←e,s,s']; apply prod_congr rfl; intro j v; refine earnR S x Q _ _ _ _ A.pipe _ _ l (sail h a _) k' b A.copies j ?_ (beardX h p j v); have ht: Lattice.halo k (Eire.port S j)⊆bay H:= lodX S X0 p (Sum.inr (Sum.inl j)) (mem_toRight.mp (mem_toLeft.mp v)) -- v
 exact (chilling (show (l+75)*radiusB x≤k from by rw [o]; simp only [Nat.add_mul]; omega) (Subset.refl _)).trans ht
lemma vestX (u:HullK S k' i.toLeft (t₀).val.1.1 (t₀).val.2 e)(u': HullK S k' i.toLeft (t₁).val.1.1 (t₁).val.2 e)(L:Pec.Pride (mid P B))(v':Vista P' M I A.pens n v g α t')(a:Dyes Z e L n A.dyes t w)(x':A.dyes=B'.dyes)(hw:A.pens=B'.pens)(t:CrownB G S e (t₀) (t₁) k H)(s:A.cloth=y.2.2)(s':B'.cloth=y'.2.2)(hu:A.wager=walksK A.cloth)(hg:B'.wager=walksK B'.cloth) : A.songP i=B'.songP i:=by
 let W:Finset (Kite S r):=i.toLeft; let X:=t₀; let X':=t₁
 have he(Z:List (Hos S r))(F:Finset (Hos S r))(hf:F ⊆ liftK S W)(ι':Kite S r)(hi:ι'∈W): postM S k' A.pens A.dyes X.val.1.1 X.val.2 A.cloth F ι'= postM S k' B'.pens B'.dyes X'.val.1.1 X'.val.2 B'.cloth F ι':= by
    have hY: Eire.liftK S W = liftK S W:=rfl; have hq:ι'.1∈liftK S W:=mem_image_of_mem _ hi
    let D':=ι'.2.1∪ ι'.2.2; have hc:Lattice.halo k (Eire.frameP S ι')⊆bay H:= lodX S X0 p _ (mem_toLeft.mp hi); have ht':hatY S D'⊆Eire.frameP S ι':= by refine Subset.trans (image_subset_image ?_) subset_union_right; rw [union_assoc]; exact subset_union_right
    have hb:=t.hears D' ((chilling le_rfl ht').trans hc)
    unfold postM; rw [dif_pos (pays_l S k' X.val.1.1 X.val.2 _ u F hf ι'.1 hq),dif_pos (pays_l S k' X'.val.1.1 X'.val.2 _ u' F hf ι'.1 hq), ← hw,←x']; apply lit_i S A.pens A.dyes ι' v' L a
    · rw [s,s']; intro j t; exact h.sharesL j ((Dress.moon p _ hi) (mem_union_right _ (mem_image_of_mem S.ratio.parent t)))
    have hh(f:Finset (Hos S r)): Agrees D' (valve S X.val.1.1 X.val.2 f k') (valve S X'.val.1.1 X'.val.2 f k'):=by intro j v' k; unfold valve; split; exact hb.2.2 j v' k; exact hb.1 j v' k
    intro v'; cases v'; exact hh _; exact hh _
 have hz(z:List (Hos S r)): Eire.paint S k' A.pens A.dyes X.val.1.1 X.val.2 A.cloth W z=Eire.paint S k' B'.pens B'.dyes X'.val.1.1 X'.val.2 B'.cloth W z:=by
    induction z with
    | nil=>rfl
    | cons a b ih=> change rankG _ _ _ _ _ _ _ _ _ _*_ = rankG _ _ _ _ _ _ _ _ _ _*_; refine congrArg₂ (fun x y:FC (Single (mid P B))=>x*y) ?_ ih; unfold rankG; split; exact sum_congr rfl fun j v=>he b _ inter_subset_left j (mem_filter.mp v).1; rfl -- W'?
 have ht:A.wager.filter (fun i=>i∈liftK S W)=B'.wager.filter (fun i=>i∈ liftK S W):=by rw [hu,hg,s,s']; refine sail_s _ _ _ (fun j v z' k=> ?_); obtain ⟨j',v',rfl⟩:= mem_image.mp v; exact h.sharesL z' (litG S X0 p j' v' ((mem_filter.mp k).2)) -- tuning indent
 change Eire.paint S k' _ _ _ _ _ W _=Eire.paint S k' _ _ _ _ _ W _; rw [← jug S k' _ _ _ _ _ W A.wager, ←jug S k' _ _ _ _ _ W B'.wager, ht]; exact hz _
end YM.CF.Plume
