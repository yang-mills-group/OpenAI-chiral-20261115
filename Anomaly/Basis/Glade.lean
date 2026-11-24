import YM.CF.Sour.Fro
import Anomaly.Ward.Reach
/-! Auxiliary unflagged first loader. Pay all directional powers on the Seat proposal. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Rill
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open CF.Forge
open AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Matrix
local notation "G"=>SU.group
open Cube Lat Tulip Peaks Fock Jet Branch Urn Levier Drapes Tenant

variable {N:Side}
set_option synthInstance.maxSize 20000
open Sour Vow
local notation "SS"=> More N
open Pressure
variable {U:Scree.Loom N}{b e a:ℝ}{P:BudgetPoint}{n r:ℕ}{S X D Z:Support (More N)}(hp:0<e)(h:Roof N b e r U)(vb:P.threshold ≤ b)
variable {m:ℝ}(G':HopeT e m a P.order)(x:Orbit N)(Y:Vow.Aura N)(pY:halo (r+10) S ⊆ Y.val)
variable (pz:P.threshold ≤ a)(hD:halo (cipherK r) D ⊆ Y.val)(hs:cipherK r≤5*P.B)(ht:3≤P.B)
local notation "μ"=> (a/P.threshold)
include hD pY hs ht h G' vb
/-- Earn on link increments with dilation at fixed much larger radius `a`. Still off same deletion. -/
lemma earnPlus (p:x.1∈σX P Y D)(t:D⊆Z)(z:Bond SS)(wZ:Skye.ends z⊆S): Tender (fun v:tangD N=> U ((pressQ P Z x.1 (μ • v),x.2):Orbit N) z) 0 m P.order:=by
 let L:= μ • ContinuousLinearMap.id ℝ (tangD N)
 have hy:= (portA h vb hD p S pY t hs ht (show z.1∈S from wZ (by simp))).comp_tendsto (show Tendsto L (𝓝 0) (𝓝 0) from by simpa using L.continuous.tendsto 0) -- adapt from earnR
 let Yq:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Bond SS=>SU.group.Color) z; let B(v:tangD N):=pressQ P Z (U x) (μ • v); let W:tangD N→L[ℝ]SU.group.Color:= a • Yq
 suffices p:Tender (fun v=> B v z) 0 m P.order by exact p.same (hy.symm.mono fun i t=> congrArg SU.group.mat t)
 by_cases g:z∈unrest Z P.B; swap
 · refine Shake.same ((Shake.holds (SU.group.mat ((U x) z))).bag G'.ease.le) (Eventually.of_forall ?_); intro y; change _=SU.group.mat (B y z); unfold B pressQ gyrate Function.comp increment; rw [steadyB,if_neg g]; simp
 have hz:‖Yq‖ ≤ 1:=ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun i'=> (norm_le_pi_norm i' z).trans_eq (one_mul _).symm
 apply Shake.same (G'.until' _ W ((U x) z) ?_)
 · refine Eventually.of_forall fun y=> ?_; change _=SU.group.mat (B y z); unfold B pressQ gyrate Function.comp increment; rw [steadyB,if_pos g, smul_smul, mul_comm _ (a/_),div_mul_cancel₀ _ P.threshold_pos.ne']; rfl
 unfold W; rw [norm_smul,Real.norm_of_nonneg G'.peta.le]; exact mul_le_of_le_one_right G'.peta.le hz
end YM.CF.Rill
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
variable {N:Side}{Y:SOp N}{S:Sa N}{B:BudgetPoint}{a s t d f h q' x₀:ℝ}{k q:ℕ}{K:Scree.Loom N}
local notation "I"=> Single N
local notation "θ"=> More N
variable {P:Raw (Openc (More N) d) (Single N)}{V:Toll (Single N)} (T:Suite (badge _) (bail N d) (bail N d) S V P)
    (p:Roof N t d q K)(g:0<d)(l:a≤ t)(vb:B.threshold≤t)(Z:Vow.Aura N)(u:halo (q+10) S⊆ Z.val)(hs:cipherK q ≤5*B.B)(ht:3≤B.B)(e:HopeT d f x₀ B.order)
local notation "σ"=> (x₀/B.threshold)
local notation "τ"=> (B.threshold / x₀)
local notation "Uπ"=> roller g p
include T p vb u hs ht e
lemma offerPlus (x:Orbit N)(D W:Support (More N))(w:D⊆W)(z:x.1∈ Sour.σX B Z D)(pW:halo (cipherK q) D⊆Z.val) (i j:I): Allows B.order (fun v:tangD N=> P (roller g p (pressQ B W x.1 (σ • v),x.2)) i j) 0 (V i j):=by
 refine e.warm P V T _ _ _ (fun v=> K (pressQ B W x.1 (σ • v),x.2)) (fun _=>rfl) (p.paid _) ?_ i j
 intro y F; exact earnPlus p vb e x Z u pW hs ht z w y F
omit T p vb u hs ht e
-- Consume at B thresholds; degree zero separately small.A.
open Nacre
variable {n:ℕ}{v y:ℝ}
lemma flatGain {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f:E→ ℂ}{w:ℝ}(ht:1 ≤ w)(h:‖f 0‖≤y)(c:Allows n (fun i=> f (w • i)) 0 v) : Allows n f 0 (max y (w⁻¹*v)):=by
 let T:=w⁻¹ • ContinuousLinearMap.id ℝ E
 let M(i:E):=f (w • i)
 have hp: 0<w:=zero_lt_one.trans_le ht
 have hx:M∘T=f:=funext fun i=>congrArg f (smul_inv_smul₀ hp.ne' i)
 have hl:Allows n M (T 0) v:=(map_zero T).symm ▸ c
 refine ⟨hx ▸ hl.smooth.comp 0 T.contDiff.contDiffAt,?_⟩; intro j hj; cases j
 · simpa only [norm_iteratedFDeriv_zero] using le_trans h (le_max_left y (w⁻¹*v))
 next j =>
   rw [← hx, Push.Uniform.iter_lin_at (hl.smooth.of_le (by exact_mod_cast hj))]; apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); refine le_trans (mul_le_mul (hl.norm_le _ hj) ?_ ?_ c.nonneg) ((mul_comm v w⁻¹).le.trans (le_max_right ..))
   · rw [prod_const,card_univ,Fintype.card_fin]; apply (pow_le_pow_left₀ (norm_nonneg _) (Newt.pole0 _ E E (inv_nonneg.mpr hp.le)) _).trans; exact (pow_le_pow_of_le_one (inv_nonneg.mpr hp.le) ((inv_le_one₀ hp).mpr ht) (Nat.succ_pos _)).trans_eq (pow_one _)
   positivity
end YM.CF.Swell.Porticus
