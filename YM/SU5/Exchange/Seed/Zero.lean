import YM.SU5.Exchange.Seed.Flagon
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Rue
namespace TreasuryFog
open Palot Stilo Push.AbsoluteSums.Graph Gas Ursell

lemma costBright (P:BudgetPoint)(Q:Aura n) : FeeD P 0 Q=0:=by
 funext V; unfold FeeD spinD lasting zenS; split_ifs with v
 · have he(i:ℕ): funge Q (0:Pax n) 0 i V=0:=by
      unfold funge sta; rw [Finset.sum_apply]; apply sum_eq_zero; intro j w; split; next v=>
        unfold guava; rw [prod_eq_zero (mem_univ (none:SongQ _)) rfl,smul_zero]; rfl
      next g=> rfl
   change ∑' i:ℕ,funge Q (0:Pax n) 0 i V=0
   simp only [he,tsum_zero]
 rfl
lemma toneL {T:Finset (Duo (More n))}(q:T.toRight=∅): beatB T=weighH T.toLeft:=by
 unfold beatB rhythm weighH; apply le_antisymm
 · apply Finset.sup_le; intro i u; cases i with
   |inl i=> exact Finset.le_sup (f:=fun i:Aura n=> beamH i.val) (mem_toLeft.mpr u)
   |inr i=> exact False.elim (notMem_empty i (q ▸ Finset.mem_toRight.mpr u))
 apply Finset.sup_le; intro i u
 exact Finset.le_sup (f:=fun i:Duo (More n)=> beamH ((stern ∘ dock) i)) (Finset.mem_toLeft.mp u)
private lemma gatherDots (b:Aura n)(h:D.Nonempty)(u:D⊆b.val) : lumpD {Sum.inl b} D b:=by
 let i:Duo (More n):= Sum.inl b; let X:Finset (Duo (More n)):= {i}; have hp:X.toLeft={b}:=Finset.ext fun y=>by simp [X,i]
 have hq:X.toRight=∅:= Finset.eq_empty_iff_forall_notMem.mpr fun i t=> Sum.inr_ne_inl (mem_singleton.mp (mem_toRight.mp t))
 have hx:beatB X=beamH b.val:=by rw [toneL hq,hp,weighH]; simp
 change lumpD X D b; unfold lumpD Palot.mine; rw [hx,hp,hq,bay_beam]
 have he:flow _ {b}:=fun _ p _ q t=> False.elim (t ((mem_singleton.mp p).trans (mem_singleton.mp q).symm)) -- fix
 refine ⟨rfl,he,fun j v=> ?_ ,fun j p=>by simp at p,?_⟩
 · rw [mem_singleton.mp v]; intro z; obtain ⟨i,t⟩:= h; exact Finset.disjoint_left.mp z (u t) t
 simpa [robe,inter_eq_left.mpr u] using u
lemma brightZero (P:BudgetPoint)(X:Aura n)(h:D.Nonempty)(u:D⊆X.val)(K:Cusp n) : roomV P 0 K 0 X D=K X D:=by
 have hζ:boastV (FeeD P 0) 0=0:=funext fun (i:Aura n)=> funext fun (D:Support (More n)) => funext fun (x:Orbit n)=> by
    unfold boastV; rw [costBright]; change exp (if D.Nonempty then _ else -0)-1=0; split <;> simp -- tune
 unfold roomV; rw [hζ,glowV,if_pos u]; unfold mintF; simp_rw [gear_v]
 let i:Duo (More n):= Sum.inl X; let T:Finset (Duo (More n)):= {i}; rw [sum_eq_single T]; swap
 · intro j v t; split
   next h=> by_cases k:j.toRight.Nonempty; · obtain ⟨x,h⟩:= k; rw [prod_eq_zero h rfl,mul_zero]
            have he: j.toRight=∅:= not_nonempty_iff_eq_empty.mp k
            have hr:j.toLeft={X}:= (emblem (show flow _ j.toLeft from h.2.1)).symm.trans ((congrArg tally ((toneL he).symm.trans h.1)).trans (singHs X)); apply False.elim (t (by rw [← joinP j,he,hr]; ext x :1; unfold T; rcases x with z|z <;> simp [i])) -- tune
   next h=>rfl
 swap; · simp
 have hp:T.toLeft={X}:= Finset.ext fun y=>by simp [T,i]
 have hx:T.toRight=∅:= Finset.eq_empty_iff_forall_notMem.mpr fun _ t=> Sum.inr_ne_inl (mem_singleton.mp (mem_toRight.mp t))
 rw [if_pos (gatherDots X h u),hx,hp,prod_singleton,prod_empty, inter_eq_left.mpr u,mul_one]
end TreasuryFog
end YM.CF.Vow
