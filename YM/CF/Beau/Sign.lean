import YM.CF.Beau.Shift
import YM.CF.Ione.Pose
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
variable {F:ℕ→InkD n}{u:ℕ→ℝ}{X₀:Scree.Hub n}
variable(p:∀ i:ℕ,PressB P X₀ (F i) h (u i))(hv:1 ≤ h)(g:Summable u)
-- pole scalar. ∀ spin.B.N scar same Pole.value. Metric.Lands.
abbrev pot(x:Finset (Dwell n)):Cipher n→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap {toFun:=fun i=> crumb i.val x, map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
abbrev spark (o:Xo)(U:InkD n):Prop:= pot (n:=n) ∅ (U 1) = 0 ∧∀ (x y: DN),IsAffineDirection o x→IsAffineDirection o y→ iteratedFDeriv ℝ 2 (pot ∅ ∘ U ∘ increment 1) 0 ![x,y]=0
abbrev caj(P:BudgetPoint)(Y:Support (More n))(W:ℕ→ InkD n):InkD n:= fun v=> lasting P Y ∅ (fun i=> oV (W i)) (v,Classical.arbitrary (Ids n))
local notation "sR"=> X₀.val.2
local notation "sO"=> X₀.val.1
local notation "T"=> caj P sR F
local notation "S"=> Hatch P sR
lemma pale_p(x:Pane n)(hx:visible P sR ∅ x): caj P sR F x = ∑' i,F i x:=if_pos hx
include p hv g
lemma pile_q(x: Pane n)(w:visible P sR ∅ x): Summable (fun i=> F i x):= lend (fun i=>rimR (p i) (zero_le_one.trans hv)) (g.mul_left _) hv (x,Classical.arbitrary _) w
lemma fortune(v:S U):HasSum (fun i=> F i U) (T U):=by have ht:visible P sR ∅ U:= hates (by rw [sdiff_empty]; exact v); rw [pale_p U ht]; exact (pile_q p hv g U ht).hasSum
lemma dawn(x:Finset (Dwell n))(V:Pane n)(w:S V): (ray (fun i=> pot x ∘ F i) ∘increment V)=ᶠ[𝓝 0] pot x∘ T ∘increment V:=by
 let M:= Vow.tick (Y:=∅) (X:=sR) (D:=∅) (P:=P) (U:=V) (by simpa only [sdiff_empty] using w)
 let L:= P.threshold⁻¹ • ContinuousLinearMap.id ℝ DN; have hx: Tendsto L (𝓝 0) (𝓝 0):=by simpa only [map_zero] using L.continuous.tendsto 0
 filter_upwards [hx.eventually M] with y t
 let U':= increment V y; have hX: Hatch P sR U':=by change pingS _ (sR\∅) (pressQ P ∅ V _) at t; rwa [sdiff_empty,ploy, show P.threshold • L y= y from smul_inv_smul₀ P.threshold_pos.ne' _] at t
 exact ((pot x).hasSum (fortune p hv g hX)).tsum_eq
lemma tariff_V(i:Finset (Dwell n)):1 ≤ Scree.tariff P sO h i:=by unfold Scree.tariff; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by exact le_add_of_nonneg_right (by positivity))) (one_le_pow₀ hv)
lemma shunt: PressB P X₀ T h (∑' i,u i):=by
 let H:=tsign (fun i=>rimR (p i) (zero_le_one.trans hv)) (g.mul_left _) hv; let Ω:=Classical.arbitrary (Ids n)
 refine ⟨fun x y u=> H.same (x,Ω) (y,Ω) u (fun _ _=>rfl),fun x=> H.lit (x,Ω),H.keeps.comp (f:=fun x:Pane n=>(x,Ω)) (measurable_id.prodMk measurable_const),fun x k=>H.gaugeX (x,Ω) k,?_⟩
 choose C v A K using fun i=>(p i).worth; have ht(j : Finset (Dwell n)):Summable (fun i=>C i j):=g.of_nonneg_of_le (fun i=>v i j) fun i=> ?_
 swap; · have he(k):= tariff_V p hv g k -- includes p. cost
         exact ((le_mul_of_one_le_left (v i j) (he j)).trans (single_le_sum (fun j _=>mul_nonneg (zero_le_one.trans (he j)) (v i j)) (mem_univ _))).trans (K i)
 refine ⟨fun j=>∑' i,C i j,fun i=>tsum_nonneg fun j=>v j i,fun U w j=>Prism.mint (wayF (F:=fun i=> (pot j ∘ F i)) (fun i a Q=> A i a Q j) (ht j) w) (dawn p hv g j _ w),?_⟩
 have he:Summable (fun i=>∑ j:Finset (Dwell n),Scree.tariff P sO h j * C i j):= summable_sum (fun j _=> (ht j).mul_left _) -- tune
 simp_rw [←tsum_mul_left]; rw [←Summable.tsum_finsetSum]; exact he.tsum_le_tsum K g; exact fun j _=>(ht j).mul_left _
include p hv g in
lemma stunt (v:∀ i, spark sO (F i)):spark sO T:=by
 let θ:=pot (∅:Finset (Dwell n)); have hp:= fortune p hv g (ping_f P X₀.val.2 (G:=SU.group)); have hx:= dawn p hv g ∅ _ (ping_f P sR); constructor
 · have h:= θ.hasSum hp; rw [show pot (∅:Finset (Dwell n)) _=_ from h.tsum_eq.symm]; simp_rw [show ∀ j,θ (F j 1)=0 from fun i=> (v i).1]; simp
 intro x y a b; choose C ℓ k l using fun i=> (p i).worth; have ht:Summable (fun i=>C i ∅):=g.of_nonneg_of_le (fun i=>ℓ _ _) fun i=>?_ ; swap; · have he(j):=tariff_V p hv g j; exact ((le_mul_of_one_le_left (ℓ _ _) (he ∅)).trans (single_le_sum (fun j _=>mul_nonneg (zero_le_one.trans (he j)) (ℓ i j)) (mem_univ _))).trans (l i)
 let hg:= ContinuousMultilinearMap.apply ℝ _ ℂ ![x,y]; have hy:= hg.hasSum ((surf (X:=sR) (o:=sO) (F:=fun i=> pot ∅ ∘ F i) (fun i a w=>k i a w ∅) ht (ping_f P sR)).2 2 ((by norm_num: 2≤6).trans P.order_ge)); have hz(i): hg (iteratedFDeriv ℝ 2 ((pot ∅ ∘ F i)∘ increment 1) 0)=0:=(v i).2 x y a b; rw [←(hx.iteratedFDeriv (𝕜:=ℝ) 2).eq_of_nhds]; exact Eq.trans hy.tsum_eq.symm (by simp only [hz]; exact tsum_zero) -- tune
end YM.CF.Beau
