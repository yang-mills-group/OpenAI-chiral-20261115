import YM.CF.Eire.Tune
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
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(x:ℝ)(e_:ℝ)(r l k D:ℕ)
local notation "bay"=> Stilo.bay
variable {ι:Type}[Fintype ι][DecidableEq ι](X:ι→ Palot.leaf (Site (Domain N B)))
open Rush Scroll Paige Vault Phase Acorn Spire
-- pack at each table with one metric projection. same thermal components for all leg fibres.
structure Dress (M:Monk SU.group S)(R:GramM (mid P B))(k:ℕ)(X:ι→Palot.leaf (Site (Domain N B))) where
 odds:Odd G.count.val
 axes:S.ratio=ratio G
 pipe: Tube SU.group S
 chi: Chi
 wage:ℝ -- affine-patch guard coeff
 yawB:0<e_
 pens:∀ i:Support (Domain P B),Lend P B e_ i
 dyes: Tints P B e_
 cloth: Ids (mid P B)
 portT : Meter TailB G e_
 portG : Meter Grave G e_
 guardP : ReefT G e_ portT portG
 blocks: ∀ i:Stores S,Rill.Arch G e_
 wager: List (Hos S r)
 rare: Stores S→ Hos S r → Cipher (mid N B)
 coin: Stores S→ι→ Cipher (mid N B)
 rareP i j: Flour (camp (stem S j)) (rare i j).val
 coinP i j: Flour (camp (X j).val) (coin i j).val
 copies: Copies R
 paints: ∀ Y: Finset (Kite S r),∀ H:Ride S,(∀ i∈Y,frameP S i⊆bay H)→ let P:=blocks (cook S Y); Pitch bell (lipF (mintK S H)) 0 (paint S D pens dyes P.val.1.1 P.val.2 cloth Y wager)
namespace Dress
variable {S G D k r l x}
variable (M:Monk SU.group S)(R:GramM (mid P B))
variable {M R X e_}
variable (U:Dress (r:=r) G S e_ D M R k X) -- order inferred?
variable (x:ℝ)(l:ℕ)
abbrev coats(i:Troupe S r ι):= U.blocks (penn S i)
def bodyL(i:Troupe S r ι): Cipher (mid P B):= lure S x R (trot S M (penn S i)) U.cloth U.pipe U.chi U.wage l (i.toRight.toLeft)
def songP(i:Troupe S r ι): FC (Single (mid P B)):= let P:=U.coats i; paint S D U.pens U.dyes P.val.1.1 P.val.2 U.cloth i.toLeft U.wager
def brew(i:Troupe S r ι): Cipher (mid N B):= let P:=penn S i; (∏ j∈liftK S i.toLeft,U.rare P j)* ∏ j∈i.toRight.toRight, U.coin P j
def heatT(i:Troupe S r ι)(Pb:Ride S): Weave (Single (mid P B)) (Single (mid N B)):= cala G S U.odds e_ U.yawB U.portT U.portG (U.coats i) k Pb
variable {U}
lemma beam_i {A: Ride S}{P:Troupe S r ι}(p: cluster (BranchX S X k) P≤ A): Palot.fits (BranchX S X k) P A:= Finset.sup_le_iff.mp p -- ambiguous
lemma moon{i:Troupe S r ι}{P:Ride S}(p: Palot.fits (BranchX S X k) i P)(j)(v:j∈ i.toLeft): frameP S j ⊆ bay P:=(halo_subset k (Eire.frameP S j)).trans (lodX S X p _ (mem_toLeft.mp v))
variable (U)
lemma gown (i:Troupe S r ι)(P:Ride S)(h: Palot.fits (BranchX S X k) i P): Pitch put (lipV (mintK S P)) 0 (U.bodyL x l i).val:=by
 unfold bodyL; apply Pitch.rise (fresh_p (show Flour (camp (Passage S (bay P))) _ from ?_)) ?_; swap
 · intro j p; change mint S j.2∈bay P; exact (mem_filter.mp ((mem_filter.mp (show j∈ camp _ from p)).2)).2
 apply (stretch_ok _).mp; apply Subalgebra.prod_mem; intro j v; apply (stretch_ok _).mpr; exact (witnessH S x R _ U.cloth U.pipe _ _ _ U.copies j).lift (fun i d=> mem_filter.mpr ⟨mem_univ _,litF S X h j v (mem_filter.mp d).2⟩)
lemma breeds (i:Troupe S r ι)(P:Ride S)(h:Palot.fits (BranchX S X k) i P): Pitch put ((rayB)⁻¹' (bay P)) 0 (U.brew i).val:=by
 apply Pitch.rise (fresh_p (show Flour (camp (bay P)) _ from ?_)) ?_; swap; · exact fun j p=> (mem_filter.mp p).2 -- tune
 unfold brew; dsimp only; apply Flour.mul; -- tune implicit subtype
 · apply (stretch_ok _).mp; apply Subalgebra.prod_mem; intro j t; obtain ⟨k,u,rfl⟩:=mem_image.mp t; apply (stretch_ok _).mpr; exact (U.rareP ..).lift (fun y v=> mem_filter.mpr ⟨mem_univ _,litG S X h _ u (mem_filter.mp v).2⟩)
 apply (stretch_ok _).mp; apply Subalgebra.prod_mem; intro j t; apply (stretch_ok _).mpr; exact (U.coinP ..).lift (fun y v=>mem_filter.mpr ⟨mem_univ _,lodX S X h _ (mem_toRight.mp (mem_toRight.mp t)) (mem_filter.mp v).2⟩)
def stageT(i:Troupe S r ι) : ModeW (mint S) rayB (BranchX S X k) i where
 knots:=U.heatT i
 voice:=(U.bodyL x l i).val
 diet _ :=(U.brew i).val
 rhythm _ :=U.songP i
 forP P h:= U.gown x l i P (beam_i h)
 dapP P h:=U.breeds i P (beam_i h)
 capP P h:=U.paints i.toLeft P (moon (beam_i h))
 localP Q _ i' _ j p:= (snail G S U.axes U.odds _ U.yawB _ _ (U.coats i) k U.guardP _ _ _ p).2
end Dress
end YM.CF.Eire
