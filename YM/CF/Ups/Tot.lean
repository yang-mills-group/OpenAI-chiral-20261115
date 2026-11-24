import YM.CF.Song.Tree
set_option autoImplicit false
set_option maxHeartbeats 980000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Jade
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
variable (F:Pilot)(Z:Pluck R) (I: Stake.Isle){σ:ℝ}(Q: Tun I Z F σ){H:Muster G S x d T}
variable {U:Grasp V.U B d}{W:GivenX V U}{X: GramM (mid N B)}{Y: GramM (mid P B)}(M: Sheep V U W G Y.J X.J (k+2) n A)(P_:∀ X: Support (Domain P B),Lend P B d X)
variable {r:ℕ}
-- uniform upper determinant; E→ real.Matrix instances paintO constructed Frobenius; result absolute value ok.
open Corne
section
private lemma safeDet(I:Type)[Fintype I][DecidableEq I](C:ℝ)(h:0 ≤ C):∃ M:ℝ,0 ≤ M∧∀ X:Matrix I I ℝ,(∀ i j,|X i j|≤ C) → Real.log X.det ≤ M:=by
 let F(σ:Equiv.Perm I):ℝ:= ‖((Equiv.Perm.sign σ : ℤ):ℝ)‖; let M:ℝ:=∑ σ: Equiv.Perm I,F σ*C^(Fintype.card I)
 have hx:0≤M:=sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) (pow_nonneg h _)
 refine ⟨M,hx,fun X p=>?_⟩; by_cases he:X.det=0; rw [he,Real.log_zero]; exact hx
 have hh:0 < |X.det|:=abs_pos.mpr he; apply (Real.log_abs _ ▸ Real.log_le_sub_one_of_pos hh).trans ((sub_le_self _ zero_le_one).trans ?_); change ‖X.det‖≤_; rw [Matrix.det_apply]; apply (norm_sum_le ..).trans; refine sum_le_sum fun i _=>?_ ; change ‖((Equiv.Perm.sign i):ℤ) • (∏ j:I,X (i j) j)‖ ≤ _; rw [← Int.cast_smul_eq_zsmul ℝ,norm_smul, Real.norm_eq_abs (∏ j:I,X (i j) j),Finset.abs_prod]; refine mul_le_mul_of_nonneg_left ((Finset.prod_le_prod (fun j _=>abs_nonneg _) (fun j _=> p (i j) j)).trans_eq (by simp)) (norm_nonneg _)
end
-- Zs fix x chosen forests
lemma aura_P (L:Patch)(K:Teller SU.group)(p:L.Branches K.bind SU.group):∀ᶠ x:ℝ in atTop,∀{c f:Side}(S:StepData c f)(M:Monk SU.group S), ∃ Z:ℝ,∀ T:Tube SU.group S, Cert L K S T x → Z≤ Corne.arcD T x M:=by
 obtain ⟨m,v,C,hm,hv,hC,h⟩:= Neige.bear K L 2 p; filter_upwards [h] with x h c f S M
 let k:= Corne.kist M; obtain ⟨Kc,hw,hP⟩:=safeDet (Active k.key x k.park × SU.group.ColorIndex) C hC.le; refine ⟨-(1/2)*Kc, fun T t=>?_⟩; have hx:ShardIncome 2 x v C m T k.key k.park k.V k.k:= h S T t _ _ _ (PhysicalNext.JointLoad.Heir.noFlags ..|>.symm) _
 unfold arcD; refine mul_le_mul_of_nonpos_left (hP (baseX T x k.key k.park k.k k.V) (fun i j=>?_)) (by norm_num); have he:= hx.kernel.value; refine (ampO _ _ _).trans ?_; simpa [Function.comp_apply, Vmove] using he
open Next.Fluctuations.Sector
lemma money_V (H:ℝ)(t:0 < H)(hx:LocalRatio L)(Y:ℝ)(v:0<Y)(Mk:Monk SU.group S):∃ F:ℝ,0 < F∧ ∀ y∈Set.Icc (Y/2) (2*Y), F ≤ prefactor S SU.group y * (shotM L H y)^Fintype.card Mk.park.Free:=by
 let Z:=Set.Icc (Y/2) (2*Y); let f(s):= prefactor S SU.group s * (shotM L H s)^Fintype.card Mk.park.Free; have hv(i)(j:i∈Z): 0 < i:= lt_of_lt_of_le (half_pos v) j.1 -- tune syntax
 have he(i)(w:i∈Z):0 < f i:=mul_pos (prefactor_pos _) (pow_pos (mul_pos (spare_pos _ hx (hv i w)) (point_p t)) _)
 have hp:ContinuousOn f Z:=by
    have hu:ContinuousOn coupling Z:= Real.continuous_sqrt.continuousOn.inv₀ (fun i j=> (Real.sqrt_pos.mpr (hv i j)).ne'); apply ContinuousOn.mul
    · unfold prefactor; exact (((Push.BetaTransport.penaltyZ_cont S SU.group).inv₀ (fun i=> (S.penaltyZ_pos ..).ne')).pow _).continuousOn -- order hete
    unfold shotM spare; exact (((Real.continuous_sqrt.comp_continuousOn (continuousOn_const.mul (hu.pow 2))).pow _|>.mul continuousOn_const).mul continuousOn_const|>.pow _)
 obtain ⟨z,g,u⟩:= isCompact_Icc.exists_isMinOn (s:=Z) (f:=f) ⟨Y,⟨by linarith,by linarith⟩⟩ hp; exact ⟨f z,he z g,fun i j=> u j⟩
lemma bank_V (p: (1,1)∈Rent0 G d): ‖shipA G U Y.J.M Y.J.P.den Y.J.I X.J.I (1,1)‖≤ Fintype.card (Seal (Site (Domain P B)))*M.height:=by
 obtain ⟨X,u,v⟩:=M.lake.members; have hz(i:Seal (Site (Domain P B))): X i ≤ M.height:=by
    by_cases h:X i=0; rw [h]; exact M.hh
    obtain ⟨j,g⟩:= populated ((u i).travel h); apply le_trans _ (v j); exact (le_mul_of_one_le_left (u i).pos (rent_one M.hs.le _)).trans (single_le_sum (s:=hit0 j) (f:=fun i=>Branch.rent M.s i*X i) (fun i _=>mul_nonneg (rent_pos ..).le (u i).pos) (mem_filter.mpr ⟨mem_univ _,g⟩))
 rw [M.lake.even _ p]; apply (norm_sum_le ..).trans; apply (sum_le_sum fun i _=> ((u i).sumline _).trans (hz i)).trans_eq; simp
end YM.CF.Jade
