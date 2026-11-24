import YM.CF.Ups.Fresh
import YM.CF.Paxos.Cava
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
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
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
variable {x':ℕ→ℝ}(t:Tendsto x' atTop atTop){L':ℕ→ℕ} (U':∀ i',SpanPS V a p i N0 J q h R0 δ (x' i') (L' i'))
local notation "N_X"=> rimZ V N0 J (x':=x')
variable(X:Month x a i p N0 V W) (H:MeterQ V a p i N0 J q h R0 δ x X)
open Graph
local notation "Mo"=> oYY V N0 J x
local notation "Zo" j:max=>cell Mo B R.L j
variable {ℓ:ℝ}(hp:1≤h)(ht:0 <ℓ)(hx:0 < x)
open Pyx Girt
local notation "hatQ"=> hat R.L x
variable (L0:∀ l:ℕ,SpanPS V a p i N0 J q h R0 δ x l)(R':Cape (oYY V N0 J x) B R.L)(Q:CoilPS V a p i N0 J q h R0 δ X L0 R')
variable {β:ℕ→ℝ}{A:ℕ→Haro.SpaceM}{F:∀ i,InkPS (cell (oYY V N0 J x) B R.L i)}{u:ℕ→ℕ}
local notation "Eρ"=> ν_P V a p i N0 J q h R0 δ L0 R'
variable (dF:ΦS_P V a p i N0 J q h R0 δ L0 R' β A F u)(hpF:K.top.clip.direct ≤1)
def remark{n:Side}(O:Oracle n) (P:InkPS n):ℂ:=∫ y:Orbit n,O y (P y)∂city _
-- Bounded read all at horizon
lemma bodyS{n:Side}(O: Oracle n)(p:BoundedT O): Envelope O:=by
 let E:=Phys n; let I:= Fin (Module.finrank ℝ E); let S:=stdOrthonormalBasis ℝ E
 have hz(y:Orbit n):O y=∑ j,(innerSL ℝ (S j)).smulRight (O y (S j)):=by
    ext1 x; simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply]; simp_rw [← map_smul]; rw [←map_sum]; exact congrArg _ ((S.sum_repr x).symm.trans (Finset.sum_congr rfl fun i _=>congrArg (· • S i) (S.repr_apply_apply _ _)))
 rw [funext hz]; exact Env.total _ (fun i=>Girt.pole_w _ (fun x:ℂ=>(innerSL ℝ (S i)).smulRight x) (by fun_prop) (p _))
include Q dF
local notation "ρ_L" j:max=> InkPS (Zo j)
lemma remark_conv(j:ℕ)(O:Oracle (Zo j))(t:BoundedT O): let f(k:ℕ):= fun x:Orbit (cell (oYY V N0 J x) B R.L j)=> O x (Eρ j (u k) x); Integrable (fun x:Orbit (Zo j)=> O x (F j x)) (city _) ∧ Tendsto (fun i=>∫ y,f i y ∂city _) atTop (𝓝 (remark O (F j))):=by
 intro f; have h:=bodyS O t; obtain ⟨C,w⟩:= Q.stain j; have ht := h.meas; obtain ⟨b,y⟩:= h.cost; let N:=Zo j; let G(x:Orbit N):=O x (F j x); have hT: Integrable G (city N):=Integrable.mono' (((Lp.memLp (F j)).integrable (by norm_num)).norm.const_mul b) (Continuous.comp_aestronglyMeasurable (show Continuous fun z:(Phys N→L[ℝ]ℂ) × Phys N=> z.1 z.2 from continuous_fst.clm_apply continuous_snd) (ht.aestronglyMeasurable.prodMk (Lp.memLp (F j)).1)) (Eventually.of_forall fun x=> ((O x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (y x) (norm_nonneg _)))
 have he:=dF.stay j; have hB:∀ᶠ i in atTop,j ≤ u i:= dF.hz.tendsto_atTop.eventually (eventually_ge_atTop j); refine ⟨hT,tendsto_integral_filter_of_dominated_convergence (fun _=>b*C) ?_ ?_ (integrable_const _) ?_ ⟩
 · exact hB.mono fun i t'=> (Pyx.listen id measurable_id (Q.port _ _ t') t).meas.aestronglyMeasurable
 · exact hB.mono fun i l=> Eventually.of_forall fun x=> ((O x).le_opNorm _).trans (mul_le_mul (y _) (w _ l x) (norm_nonneg _) ((norm_nonneg _).trans (y x)))
 exact he.mono fun i v=> ((O i).continuous.tendsto _).comp v
lemma remark_one(j):remark (fun _:Orbit (Zo j)=> (beamL _).restrictScalars ℝ) (F j)=1:=by
 let O: Oracle (Zo j):= fun _=>(beamL (Zo j)).restrictScalars ℝ; have h:=(remark_conv V a p i N0 J q h R0 δ X L0 R' Q dF j O (fun x=>rite_c _)).2
 apply tendsto_nhds_unique h (Tendsto.congr' _ tendsto_const_nhds); filter_upwards [dF.hz.tendsto_atTop.eventually (eventually_ge_atTop j)] with m w; let c:= ((L0 (u m)).E j); change (1:ℂ)=∫ y,(inner ℂ (mateK _) (Eρ j (u m) y))∂ city _; unfold ν_P ω_den; simp_rw [inner_smul_right,MeasureTheory.integral_const_mul]; exact (inv_mul_cancel₀ (Q.guide _ _ w)).symm
lemma clean_B : β 0=x:=by
 have he(k):((L0 k).E 0).beta=x:= (L0 k).scale.note.color.trans (L0 k).scale.day.unit; exact tendsto_nhds_unique (dF.lampB 0) (tendsto_const_nhds.congr (fun i=> (he (u i)).symm))
lemma UV_head (g:0 <x): Tendsto β atTop atTop :=by
 let v:=Vale.billX R.L; have hz:= billx_T V; have hv:0 < v:= by unfold ν_PS at hz; exact (lt_of_lt_of_le hz (by change Vale.billX _/4 ≤ Vale.billX _; linarith only [hz]))
 have ht:Tendsto (hatQ) atTop atTop:= tendsto_atTop_add_const_left atTop _ (tendsto_natCast_atTop_atTop.atTop_mul_const hv)
 exact tendsto_atTop_mono (fun i=>(dF.plate i).1) (ht.atTop_div_const two_pos)
lemma cardZ(j:ℕ){α:Type*}(Z:Opt (α:=α) (Zo j)) : Tendsto (fun i=>(∫ z,Roe.getF Z ((L0 (u i)).E j) U (R' j) z∂city _)/partitionZ ((L0 (u i)).E j) U (R' j)) atTop (𝓝 (remark (Pyx.plume Z) (F j))):=by
 apply (remark_conv V a p i N0 J q h R0 δ X L0 R' Q dF j _ (hosted Z)).2.congr fun i=>?_; dsimp only; let Vb:=(L0 (u i)).E j; let U0:= partitionZ Vb U (R' j); let f(x:Orbit (Zo j)):Phys (Zo j)→L[ℂ]ℂ:=( (innerSL ℂ (mateK _)).comp (acts (Emu.muni Z.o x.1 Z.R Z.f Z.L))); change (∫ z,f z (U0⁻¹ • denZ Vb U (R' j) z)∂city _)=_; simp_rw [map_smul,integral_smul]; change U0⁻¹ * (_:ℂ)= (∫ z,f z (denZ Vb U (R' j) z)∂ city _) /U0; rw [div_eq_mul_inv, mul_comm]
end YM.CF.Py
