import YM.SU5.Interaction.Draught.Taper
import YM.CF.Rive.Rays
import YM.CF.Song.Pads
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
open Rue Trees
-- Origin check for FeeD & Force. ALL Orbit.
open Palot Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Gas
set_option maxHeartbeats 600000
variable (K:Cusp n)(Xq:Aura n)
lemma spark_core_zero : FeeD P (0:Pax n)=0:=by
 funext i x; unfold FeeD spinD lasting zenS; split; swap; · rfl
 rename_i v
 have hx(k:ℕ)(t:Tuple (Aura n) k):sta (0:Pax n) i 0 ⟨k,t⟩=0:=by unfold sta; split; unfold guava; simp; rfl -- nonempty?
 unfold funge; simp_rw [hx]; simp -- scope
lemma glow_boast_z : boastV (0:Pax n) 0=0:=by funext i D x; simp [boastV] -- lite
private lemma tally_needed (T: Finset (Palot.Duo (More n)))(p:lumpD T D Xq)(v:T.toRight=∅) : T.toLeft={Xq}:=by
 have hv:beatB T = weighH T.toLeft:=by
    unfold beatB rhythm weighH; nth_rw 1 [←joinP T]; rw [v]; -- disjSum_empty
    simp; rfl
 have hx:= emblem p.2.1; rw [←hv,p.1, singHs Xq] at hx; exact hx.symm
variable (t:D.Nonempty)(f:D⊆Xq.val)
include t f
lemma glow_R_zero : glowV K 0 Xq D = K Xq D:=by
 let T:Finset (Palot.Duo (More n)):= ({Xq} : hook (Seat n)).disjSum ∅
 have ht(T':Finset (Palot.Duo (More n)))(v:T' ≠ T): gemB D K 0 T' (beamH Xq.val)=0:=by
    rw [gear_v]; split; swap; · rfl
    rename_i q
    by_cases u:T'.toRight=∅
    · have h:= joinP T'; rw [tally_needed Xq T' q u,u] at h; exact (v h.symm).elim
    obtain ⟨x,z⟩:= Finset.nonempty_iff_ne_empty.mpr u; rw [prod_eq_zero z rfl, mul_zero]
 have hb:T={Sum.inl Xq}:=by ext y; cases y<;>simp [T]
 have hq:T.toLeft={Xq}:=Finset.toLeft_disjSum ..; have hk:T.toRight=∅:=Finset.toRight_disjSum ..
 have hx:lumpD T D Xq:=by
    have ht:beatB T= beamH Xq.val:= by unfold beatB rhythm; rw [hb]; simp [dock,Palot.stern]
    refine ⟨ht,?_⟩; unfold Palot.mine; rw [ht,bay_beam, hq,hk]; unfold flow raisedH fuelH robe; simp; obtain ⟨i,v⟩:=t; exact not_disjoint_iff.mpr ⟨i,f v,v⟩
 unfold glowV; rw [if_pos f,mintF,sum_eq_single T (fun i _ v=>ht _ v) (fun v=> (v (mem_univ _)).elim),gear_v,if_pos hx]; simp [hk,hq, inter_eq_left.mpr f]
omit f t
lemma bareLuxe (K:Cusp n)(h:(fun (X:Aura n)=>K X ∅)=0) : budgetR (roomV P (fun X=>K X ∅) K 0)= budgetR K:=by rw [h,roomV,spark_core_zero,glow_boast_z]; funext i; unfold budgetR; rw [glow_R_zero _ _ i.property.1 i.property.2]
end YM.CF.Vow
#print axioms YM.CF.Vow.bareLuxe
