import YM.CF.Siete.Tree
import YM.Push.ABSOLUTE_SUMS.Path
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Reprise
set_option autoImplicit false
noncomputable section
namespace YM.CF.Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Jet Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Skye Scree Cube
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n j l:ℕ}{K C Q v ε x:ℝ}{c f:Side}{L:Side}{S:StepData (More c) (More f)}{F:Forest S.ratio}{A:Stores S}{P B:BudgetPoint}{X X':Support (More f)}{Y:Support (More c)}{I:Type}[Fintype I][DecidableEq I]{p o:Seat f}
local notation "G"=>SU.group
lemma strokeZ {i:Bond (More f)} (h:X ⊆ halo B.B {i.1}): Short S B X:=by
 have he:covers B.B X {i.1}:=⟨h,Corona.ship_halo _ (by intro a ha b hb; rw [mem_singleton.mp ha,mem_singleton.mp hb])⟩
 have hg: coverNumber B.B X ≤1:=by simpa using Corona.list_cost _ he
 apply lt_of_le_of_lt (pow_le_pow_left' hg 3); have ht:=S.patch.coarse; rw [one_pow]; omega
lemma short_s (S:StepData (More c) (More f)) (i:Seat f): Short S B {i}:=strokeZ (i:=(i,0)) (halo_subset ..)
abbrev twoZ (i:Bond (More f)): Support (More f):={i.1,i.1+step i.2}
lemma short_z (S:StepData (More c) (More f))(i:Bond (More f)): Short S B (twoZ i):=by
 apply strokeZ (i:=i); intro j g; rcases mem_insert.mp g with rfl|g
 · exact halo_subset _ _ (mem_singleton_self _)
 apply halo_spec.mpr; refine ⟨i.1,mem_singleton_self _,?_⟩; rw [mem_singleton.mp g,separation_comm,separation,add_sub_cancel_left]; exact (pdist_step i.2).trans B.B_pos
lemma plane_s{X Y:Support f}(h:X⊆Y) : inspected X ⊆ inspected Y := union_subset_union h (by
 intro p hn; obtain ⟨i,b,H⟩:=mem_biUnion.mp hn
 refine mem_biUnion.mpr ⟨i,b,?_⟩; by_cases he:Disjoint X (touched i)
 · simp [he] at H
 rw [if_neg he] at H; exact (if_neg (fun hz=> he (Disjoint.mono_left h hz))).symm ▸ H)
-- derive coherent heir under area PO and hp coverage
section norm
variable (M: Museum F x A X Y I)(p_:X' ⊆ X)
include M p_
lemma cask : ∀ i∈ inspected X', halo (Heir.reach x+4) {S.ratio.parent i} ⊆ Y:=fun i l=>M.asks i (plane_s p_ l)
def fringe (M: Museum F x A X Y I)(p_:X' ⊆ X): Museum F x A X' Y (PlaceZ F X' A x):= museZ X' Y F A x M.away (cask M p_)
lemma fry : coZ (fringe M p_) ⊆ coZ M:=by
 let m:= PlaceZ F X' A x; unfold coZ airP; refine fun i p=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
 apply Corona.halo_mono le_rfl _ (Finset.mem_filter.mp p).2; intro j g; obtain ⟨t,_,rfl⟩:= mem_image.mp g
 obtain ⟨y,b⟩:= M.covers t.val (plane_s p_ t.property.1) (plane_s p_ t.property.2); exact mem_image.mpr ⟨y,mem_univ _,congrArg (fun w: Active A x F=> S.ratio.parent w.val.val.1) b⟩
end norm
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{g: tangD f → E}
lemma rise_i (j:ℕ)(h:∀ v:Fin j→ tangD f, (∀ i,B.dirBound o (v i))→ ‖iteratedFDeriv ℝ j g 0 v‖ ≤ C) (w:Fin j→ tangD f)(p':∀ i,B.dirBound p (w i)): ‖iteratedFDeriv ℝ j g 0 w‖≤ spine B.power o p^j * C:=by
 let t:= spine B.power o p; let y(i:Fin j):= t⁻¹ • w i; have ht:0<t:=spine_pos ..
 have he :w=fun i => t • y i:=funext fun i=> (smul_inv_smul₀ ht.ne' _).symm
 have hy(i):B.dirBound o (y i):= fun m=> by
    change ‖t⁻¹ • (w i m)‖ ≤ Lyre.width B o m; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le, inv_mul_le_iff₀ ht]; apply (p' i m).trans; rw [mul_comm t]; unfold t; change _ ≤ B.threshold * spine _ _ _ * _; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (spine_triangle ..) B.threshold_pos.le
 rw [he,ContinuousMultilinearMap.map_smul_univ,norm_smul,Real.norm_of_nonneg (Finset.prod_nonneg fun _ _=>ht.le),prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left (h _ hy) (by positivity)
end YM.CF.Siete
