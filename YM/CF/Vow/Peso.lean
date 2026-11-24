import YM.CF.Nor.Nas
import YM.CF.Palot.End
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
-- no exponential growth in angular boiler. one common normalized Dir (cost Oₚ(skeleton)^n restored at LAST)
abbrev pressQ(P: BudgetPoint)(D:Support (More n))(V:Pane n)(i:DN):= gyrate (Rill.unrest D P.B) V (P.threshold • i)
abbrev WorthB(P: BudgetPoint)(U:Orbit n)(D:Support (More n))(F:Copy n)(c: Ink n):=Rue.Rigid (fun i:tangD n=>F (pressQ P D U.1 i,U.2)) P.order 0 c
structure ThemeR (X: Support (More n))(F:Copy n):Prop where
 same (V W: Orbit n) : Agrees X V.1 W.1→ Set.EqOn V.2 W.2 X → F V=F W
 lit(V): Flour (camp X) (F V).val
 keeps: Measurable F
 gaugeX(V:Orbit n)(g:Seat n→SU.group.El): F (Lattice.gauge g V.1,threadG g V.2)= Scree.paintR false false (tradew n g) (F V)
structure Medal (P: BudgetPoint)(X D:Support (More n))(F:Copy n)(h C:ℝ):Prop extends ThemeR X F where
 pays : ∃ c: Ink n, 0≤c ∧ (∀ V:Orbit n, pingS P.threshold (X\D) V.1 → ∀ {Y:Support (More n)},D ⊆ Y→ WorthB P V Y F c) ∧ joinV (stake h) c ≤ C
-- protected ports separate
structure Firm (P:BudgetPoint)(X D:Support (More n))(F:Copy n):Prop where
 readV :¬ inspected D⊆X → F=0
 litK(V):F V≠0→D⊆flags P.threshold V.1
lemma deal_L (p:D⊆Y)(i:DN): openG P D (openG P Y i)= openG P Y i:=by
 funext j; unfold openG; split; rfl
 rename_i h; symm; rw [if_neg]; exact fun q=> h (Disjoint.mono_right (Corona.halo_mono le_rfl p) q)
variable {K:Pane n→ℂ} {o:Seat n}
open PhysicalNext.JointLoad Heir
lemma pins (p:D⊆Y)(s:Signs P o (fun i=> K (increment U (openG P D i))) a): Allows P.order (K ∘ pressQ P Y U) 0 (composeCost P.order a 1):=by
 let L:=Rill.unrest Y P.B; let M:DN→L[ℝ]DN:= P.threshold • wakeB L; have ht(i): M i=openG P Y (P.threshold • i):=by rw [padP,map_smul]; rfl
 let V:= (Prism.silo P o).comp M; let G(i:DN):=K (increment U (openG P D i)); let R:= G ∘ Prism.trunk P o; have hr:Allows P.order R (V 0) a:= (map_zero V).symm ▸ Prism.skin s
 have hv: ‖V‖ ≤ 1:=by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i=>?_ ; rw [one_mul]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro j
    change ‖(Lyre.width P o j)⁻¹ • ((M i) j)‖ ≤ _; rw [ht]; unfold openG; split
    · rw [Pi.smul_apply,smul_smul,norm_smul,Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (Lyre.width_pos ..).le) P.threshold_pos.le)]; refine (mul_le_mul (show (Lyre.width P o j)⁻¹ * P.threshold ≤ 1 from (inv_mul_le_iff₀ (Lyre.width_pos ..)).mpr ?_) (norm_le_pi_norm i j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _); rw [mul_one]; exact le_mul_of_one_le_right P.threshold_pos.le (spine_one ..)
    rw [smul_zero,norm_zero]; exact norm_nonneg _
 rw [show K ∘ pressQ P Y U=R ∘ V from ?_]; exact hr.comp (allows_linear hv (by simp))
 funext i; change K _ =K _; symm; unfold V; simp only [ContinuousLinearMap.comp_apply]; rw [trench,ht,deal_L p,padP]; rfl
-- standardize costs born.Repayment
lemma debt_m (s:Signs P o (fun i=> K (increment U i)) a) : Allows P.order (K ∘ pressQ P Y U) 0 (composeCost P.order a 1):=by
 have he (i:tangD n):openG P (∅:Support (More n)) i=i:=by funext j; simp [openG,Lattice.halo]
 apply pins (D:=∅) (empty_subset _); simp_rw [he]; exact s
lemma grow_b (p:Y⊆Z)(w:pingS x Z U):pingS x Y U:=fun i g=> w i fun u=>g (Disjoint.mono_left p u)
lemma loc_y (f:DN→L[ℝ]DN)(hh:f=rodV P o X D)(i:DN): Agrees X (pressQ P D U (f i)) (increment U (openG P D (Prism.trunk P o i))):=by
 subst f; let L:= unrest D P.B; have ht:= P.threshold_pos
 intro j v t; have hq:pinPos j⊆X:= insert_subset v (singleton_subset_iff.mpr t);
 unfold pressQ rodV highlight gyrate
 rw [padP]; unfold RG.increment; simp only [Function.comp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply]; rw [Forge.steadyB]; split_ifs with hp
 · rw [smul_inv_smul₀ ht.ne',ContinuousLinearMap.pi_apply,if_pos hq]; rfl
 rw [Forge.steadyB, if_neg hp]; -- tune namespaces
lemma tomB (p:o ∈ X)(K_:ℕ)(hk:LocalOn X K)(hx:Hake.Pence P.order (fun i:tangD n=> K (pressQ P D U i)) 0 a): Signs P o (fun i:tangD n=>K (increment U (openG P D i))) (Nor.liftR P X K_ a):=by
 let L:=rodV P o X D; let F(i:tangD n):=K (pressQ P D U i); let J(i:tangD n):= K (increment U (openG P D i)); have ht: F ∘ L = J ∘ Prism.trunk P o:=funext fun i=> hk _ _ (loc_y L rfl i)
 let Y:= Nor.surgeL P X K_; have hu:‖L‖≤Y:=lens_x P o X D K_ p; apply Prism.skills (A:=J); rw [←ht]; exact (show Allows P.order F (L 0) (P.order.factorial*a) from (map_zero L).symm ▸ hx.pay).comp (allows_linear hu (by rw [map_zero,norm_zero]; exact (norm_nonneg L).trans hu))
end YM.CF.Vow
