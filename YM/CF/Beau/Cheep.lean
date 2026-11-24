import YM.CF.Beau.Pour
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Trees
variable (H:ℕ→ Aura n)(F:ℕ→Support (More n) → Copy n)(G:ℕ→ℝ)
abbrev μK(i:Aura n)(k:ℕ):= if i=H k then G k else 0
abbrev μV(i:Aura n)(D':Support (More n))(k:ℕ): Copy n:= if i=H k then F k D' else 0
abbrev ΘS(P:BudgetPoint)(X:Aura n)(D:Support (More n)): Copy n:= lasting P X.val D (μV H F X D)
abbrev Thr(K:Cusp n)(v:Aura n→ℝ)(P:BudgetPoint)(h:ℝ):Prop:=∀ i:Aura n,∀ D:Support (More n), Medal P i.val D (K i D) h (v i)
variable (p:∀ i:ℕ,∀ D:Support (More n), Vow.Medal P (H i).val D (F i D) h (G i))(v:1≤h)(u:Ac.Hit (fun i:ℕ=> (H i).val) P.B G (P.supportExponent+1+1) a)
local notation "Θ"=> ΘS H F P
include p v
lemma mail_k(X:Aura n)(k:ℕ)(D':Support (More n)): Vow.Medal P X.val D' (μV H F X D' k) h (μK H G X k):=by unfold μV μK; split; rename_i v; subst X; exact p _ _; exact Vow.Medal.zeroT
include u
lemma milk_P(X:Aura n):Summable (μK H G X):=by
 obtain ⟨Y,t⟩:= X.property; let L:= P.supportExponent+1+1; have hf:= u Y; have hx(i):0 ≤ G i:= (p i ∅).wage (zero_le_one.trans v)
 refine hf.2.1.of_nonneg_of_le (fun i=> (mail_k H F G p v X i ∅).wage (zero_le_one.trans v)) (fun j=>?_ ); unfold μK; split
 next w=> rw [if_pos (show Y∈ (H j).val from w ▸ t)]; apply le_mul_of_one_le_right (hx j); exact Real.one_le_exp (by have h:=P.exponent_pos; positivity)
 exact hf.1 _
abbrev vis(X:Aura n):ℝ:= ∑' i, μK H G X i
lemma sail_F: Thr Θ (vis H G) P h ∧∀ i: Skye.Seat n,tallB (vis H G) P.B (P.supportExponent+1+1) i≤a:=by
 refine ⟨(fun i D=> vaut (fun j=>mail_k H F G p v i j D) (milk_P H F G p v u i) v),fun i=>?_⟩
 unfold tallB vis; simp_rw [←tsum_mul_right]; rw [←Summable.tsum_finsetSum]; swap; · exact fun j _=>(milk_P H F G p v u j).mul_right _
 refine (le_of_eq ?_).trans (u i).2.2; apply tsum_congr; intro j; split
 next y=> rw [sum_eq_single (H j)]; unfold μK; rw [if_pos rfl]; rfl; intro k _ t; unfold μK; rw [if_neg t,zero_mul]; exact fun q=>False.elim (q (mem_filter.mpr ⟨mem_univ _,y⟩))
 next y=> apply sum_eq_zero; intro x v; unfold μK; rw [if_neg (by intro p; dsimp only at y; rw [←p] at y; exact y (mem_filter.mp v).2),zero_mul]
lemma keen_Q (V:Orbit n)(hz:FleetS P.threshold V.1):HasSum (fun i=> fuelV P (chasmR (H i) (F i)) V) (fuelV P Θ V):=by
 let A:= flags P.threshold V.1; let S:=univ.filter fun i:Aura n=> fuelH A i
 let Y(i: Aura n):= A ∩i.val; let L(i:Aura n)(j:ℕ):= μV H F i (Y i) j V
 have hX(i:Aura n)(v:i∈S): visible P i.val (Y i) V.1:=by apply hates; apply (shoreK _ _ hz _).mp; exact Finset.disjoint_left.mpr fun {j} p e=> (mem_sdiff.mp p).2 (mem_inter.mpr ⟨e,(mem_sdiff.mp p).1⟩)
 have ht(i:Aura n)(hv:i∈S): HasSum (L i) (Θ i (Y i) V):=by have he:= lend (fun j=>mail_k H F G p v i j (Y i)) (milk_P H F G p v u i) v V (hX _ hv); rw [ΘS,lasting,zenS,if_pos (hX _ hv)]; exact he.hasSum
 have hP (i:ℕ): fuelV P (chasmR (H i) (F i)) V=∑ j∈S,L j i:=by
    unfold fuelV; refine sum_congr rfl fun j v=>?_ ; unfold L μV chasmR; split
    next x=> subst j; rw [Pi.single_eq_same]
    next h=> rw [Pi.single_eq_of_ne h]; rfl
 simp_rw [hP]; exact hasSum_sum ht
end YM.CF.Beau
