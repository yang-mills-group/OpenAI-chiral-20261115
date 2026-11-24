import YM.CF.Mica.Coup
import YM.CF.Mica.Apex
import YM.CF.Beau.Cheep
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
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
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
variable (R E:RegBudget n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
variable {U:Copy n}
abbrev veil_M(K:Cusp n)(i:Aura n)(D:Support (More n)): Copy n:= blind_E ∘ K i D
abbrev Tox(K:Cusp n)(i:Aura n)(D:Support (More n)): Copy n:= flavor_t (K i D)
def cut_V : Cipher n →L[ℝ] Cipher n:= LinearMap.toContinuousLinearMap {toFun:=blind_E,map_add':=fun A B=>by unfold blind_E; rw [plus_Y]; abel,map_smul':=fun k A=>by unfold blind_E; rw [smul_sub]; refine congrArg _ ?_; refine pimp_Q _ _ fun i=>?_ ; rw [price_X]; split <;> rename_i h; change k • crumb A.val i=k • crumb (wage_Q 0 A).val i; rw [price_X,if_pos h]; change 0=k • crumb (wage_Q 0 A).val i; rw [price_X,if_neg h,smul_zero]} -- tuning
lemma oqua(k:ℂ):blind_E (N:=Dwell n) (Pastry.hollow k)=0:=by
 unfold blind_E; apply sub_eq_zero.mpr; apply pimp_Q; intro i; rw [price_X]; split; rfl
 rename_i h; change (k • (1:FC (Dwell n))) i ∅= _; simp [show i≠∅ from fun p=>h (by subst i; rfl)]
lemma veer_Q (p: Vow.Medal P X D U h a): Vow.Medal P X D (blind_E ∘ U) h a:=by
 obtain ⟨H,A,v,T,k⟩:=p; let Z:=blind_E ∘ U
 refine ⟨⟨fun x y t g=>congrArg blind_E (H.same x y t g),fun x=>?_,cut_V.continuous.measurable.comp H.keeps,fun y G=> Eq.trans (congrArg blind_E (H.gaugeX y G)) (sanct_E ..)⟩,A,v,fun V j Y m=>?_,k⟩ -- cut_V implicit
 · simp only [Function.comp_apply,blind_E,sub_eq_add_neg]; apply (H.lit x).add; change Flour _ (-(wage_Q 0 _).val); rw [←neg_one_smul ℝ ((wage_Q 0 _).val)]; exact (worthS 0 _ _ (H.lit x)).rsmul _
 · refine ⟨Eventually.of_forall (fun i=> (fineShape (Z (pressQ P Y V.1 i,V.2))).allP),fun i=>?_ ⟩; change Pence _ (fun q=> crumb (blind_E (U (pressQ P Y V.1 q,V.2))).val _) _ _; simp_rw [shelter_Q]; split; swap
   · exact (T V j m).haveP _
   refine ⟨contDiffAt_const,(le_trans (show _ ≤ ‖(0:ℂ)‖ from (Pence.const (k:=P.order) (0:DN) 0).earned) ?_)⟩; rw [norm_zero]; exact v i
lemma writ_plus(V G:Cusp n):writ_K (V+G)=writ_K V+writ_K G:=by unfold writ_K; have hp(i:T0): force_V i (V+G)= force_V i V+ force_V i G:= funext fun i=>funext fun D=>funext fun U=>map_add ..; simp_rw [hp,sum_add_distrib,smul_add]
lemma writ_self(G:Cusp n)(g:Sym_M G):writ_K G=G:=by unfold writ_K; simp_rw [g]; exact oath_r n _
lemma yarn_R(A:Cusp n)(s:Aura n→ℝ)(p: Larch.Anuk A s P h)(g:Sym_M (veil_M A))(l:0 ≤ h): Anuk (writ_K A) (s+horse_E P.order s) P h:=by
 have hx: veil_M A+Tox A=A:=funext fun i=>funext fun D=>funext fun x=> sub_add_cancel ..
 nth_rw 1 [←hx]; rw [writ_plus,writ_self _ g]; let Z:= raise_L A s P p l
 exact ⟨add_nonneg p.1 Z.1,fun i D t v=> (veer_Q P (p.2 i D t v)).plus (Z.2 i D t v)⟩
end YM.CF.Ione
