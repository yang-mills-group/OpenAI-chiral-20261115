import SatinThinShelter
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}{P:BudgetPoint}{h A C d Q:ℝ}{L:ℕ}
variable (x: Site (mid N B))
local notation "mQ"=> mid N B
local notation "wq"=>P.supportExponent+1+1
lemma real_E (s:ℝ){E:RegBudget (mid N B)}{X:ArcΦ}(p:Axon L x P E h A X)(h0:0≤h) : Axon L x P (s • E) h (|s| * A) (s • X):=by
 have HP:= charge_ν (↑s:ℂ) L x E X P A h0 p; rwa [Complex.norm_real, Real.norm_eq_abs, Complex.coe_smul,Complex.coe_smul] at HP
lemma realV (s:ℝ){F:Copy (mid N B)}{E:RegBudget (mid N B)}{K:Cusp (mid N B)}{c:ℂ}{X:ArcΦ}(p:Ice L x P h A C d F E K c X)(h0:0≤h) : Ice L x P h (|s| * A) (|s| * C) (|s| * d) (s • F) (s • E) (s • K) (s • c) (s • X):=by
 refine ⟨real_E x s p.axle h0,?_,fun i h'=>?_ ,?_,fun i w=>?_ ⟩
 · rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left p.phase (abs_nonneg _)
 · rw [Pi.smul_apply,p.stout _ h',smul_zero]
 · obtain ⟨v,u,t,l⟩:=p.grant
   refine ⟨‖s‖ • v,⟨fun i=> mul_nonneg (norm_nonneg _) (u.1 _),fun i D v t=> (u.2 i D v t).rum s⟩,fun i=>?_,fun i p=>l i (right_ne_zero_of_mul (show ‖s‖*v i≠0 from p))⟩
   rw [tall_s,Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (t _) (abs_nonneg _)
 rw [←Complex.coe_smul s E, ←Complex.coe_smul s K,voc_E P _ _ i,cul_z P _ _ i]
 rw [Complex.coe_smul,Complex.coe_smul,Pi.smul_apply, p.wear i w, smul_assoc,smul_add,smul_add]
lemma ice_sum {ι:Type*}[DecidableEq ι](S:Finset ι)(v: ι → Copy (mid N B))(u:ι→RegBudget (mid N B))(K:ι→Cusp (mid N B))(c:ι→ℂ)(X:ι→ArcΦ)(a b d:ι→ ℝ)(W:∀ i∈S,Ice L x P h (a i) (b i) (d i) (v i) (u i) (K i) (c i) (X i))(h0:0≤h) : Ice L x P h (∑ i∈S,a i) (∑ i∈S,b i) (∑ i∈S,d i) (∑ i∈S,v i) (∑ i∈S,u i) (∑ i∈S,K i) (∑ i∈S,c i) (∑ i∈S,X i):=by
 induction S using Finset.induction_on with
 | empty=>
   simp only [sum_empty]; refine ⟨nothing_X ..,norm_zero.le,fun _ _=> rfl,⟨0,⟨le_rfl,fun _ _ _ _=> Medal.zeroT⟩,fun i=> by simp [tallB],fun i h=>False.elim (h rfl)⟩,fun i w=>?_ ⟩ -- norm_zero.le
   rw [zero_r P i]; simp [fuelV]
 | insert i S l ih=>
   simp only [sum_insert l]; exact Ice.plan_ADD x L (W i (mem_insert_self ..)) (ih (fun j v=>W j (mem_insert_of_mem v))) h0
lemma ice_nonneg {F:Copy (mid N B)}{E:RegBudget (mid N B)}{V:Cusp (mid N B)}{z:ℂ}{X:ArcΦ}(p:Ice L x P h A C d F E V z X)(h0:0≤h) : 0≤A ∧ 0≤C∧ 0≤d:=by
 obtain ⟨f,h,t⟩:=p.axle.vest.weight; obtain ⟨g,w,a,b⟩:=p.grant
 refine ⟨le_trans ?_ (t (node x)), le_trans ?_ (a (node x)), (norm_nonneg _).trans p.phase⟩
 · exact sum_nonneg fun i _=> by split; exact mul_nonneg (Real.exp_pos _).le (Roots.gradeE _ _ (h i) h0) -- check
                                           ; rfl
 unfold tallB; exact sum_nonneg fun i _=> mul_nonneg (w.1 i) (Real.exp_pos _).le
end YM.CF.QuadClock
