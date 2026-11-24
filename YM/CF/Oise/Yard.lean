import YM.CF.Oise.Duct
import YM.CF.Stake.Loom
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oise
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
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
section
open Scroll Yaw Eire Girt Err
open Lich.Muster Vol AnalyticBridge.SectorAffine Matrix
variable {N P B C:Side} {m k j:ℕ}{ι:Type}[MeasurableSpace ι]
-- measurable left arg-cont-right.
private lemma near_r{X:Type}[TopologicalSpace X][Nonempty X][MeasurableSpace X] [TopologicalSpace.PseudoMetrizableSpace X][OpensMeasurableSpace X][SecondCountableTopology X](U:ι→X)(p:Measurable U):∃ u:ℕ→ι→ℕ,∃ C:ℕ→X,(∀ i,Measurable (u i))∧∀ x,Tendsto (fun i=> C (u i x)) atTop (𝓝 (U x)):=by
 letI := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
 let Y:= TopologicalSpace.denseSeq X; let Z(n:ℕ):ℝ:= (n+1:ℝ)⁻¹; have ht:Tendsto Z atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
 let J(x:ι)(i n:ℕ):= dist (Y n) (U x) < Z i; have hp(x i):∃ n, J x i n:=by obtain ⟨b,⟨n,rfl⟩,t⟩:= Metric.mem_closure_iff.mp (TopologicalSpace.denseRange_denseSeq X (U x)) (Z i) (by unfold Z; positivity); exact ⟨n,(dist_comm ..).trans_lt t⟩
 let u(i:ℕ)(x):= Nat.find (hp x i); have hx(i n):MeasurableSet {x|J x i n}:=p ((isOpen_lt (continuous_const.dist continuous_id) continuous_const).measurableSet)
 refine ⟨u,Y,fun i=>?_ ,fun x=>Metric.tendsto_nhds.mpr (fun ε z=> (ht.eventually (gt_mem_nhds z)).mono (fun i h=> (Nat.find_spec (hp x i) : dist _ _ < _).trans h))⟩
 apply measurable_to_countable; intro j; let z:=u i j
 rw [show u i ⁻¹' ({z}: Set ℕ)={x|J x i z∧ ∀ t<z,¬ J x i t} from Set.ext fun x=>Nat.find_eq_iff (hp x i),Set.setOf_and]; apply MeasurableSet.inter (hx _ _); exact mast_f _ fun j=> imp_m _ (hx i j).compl
lemma cipher_r {X Y:Type} [TopologicalSpace X][Nonempty X][MeasurableSpace X][TopologicalSpace.PseudoMetrizableSpace X][OpensMeasurableSpace X][SecondCountableTopology X][TopologicalSpace Y][MeasurableSpace Y][BorelSpace Y][TopologicalSpace.PseudoMetrizableSpace Y] (U:ι→ X)(P:ι→ X→ Y)(p: Measurable U)(v:∀ i,Continuous (P i))(W:∀ j,Measurable (fun i=> P i j)): Measurable fun i=> P i (U i):=by
 obtain ⟨u,F,hu,p⟩:=near_r U p; exact measurable_of_tendsto_metrizable (fun i:ℕ=>atlas_m (u i) (fun x j=> P x (F j)) (hu i) (fun j=>W _)) (tendsto_pi_nhds.mpr fun i=> (v i|>.continuousAt.tendsto).comp (p i))
local notation "G5"=>SU.group
variable {Z:Type} [NormedAddCommGroup Z][NormedSpace ℝ Z][MeasurableSpace Z][BorelSpace Z][SecondCountableTopology Z]
lemma root_m (U:ι→ Config SU.group N)(P:Config SU.group N→ Z){x:ℝ}(w:0<temp x)(hv:Measurable U)(p:∀ i, ContinuousAt (P ∘ Vmove x (U i)) 0):Measurable (fun i=>P (U i)):=by
 refine pmeas U P (Set.range U) (fun i=>Set.mem_range_self _) hv ?_; rintro _ ⟨i,rfl⟩; obtain ⟨ht,hf,hx⟩:=veil (U i); let L(W:Config SU.group N):=(temp x)⁻¹ • FoldK (U i) W
 have hu:L (U i)=0:=by unfold L; rw [ht,smul_zero]
 apply ((show ContinuousAt _ (L (U i)) from hu.symm ▸ (p i)).comp (f:=L) (hf.const_smul ((temp x)⁻¹))).congr_of_eventuallyEq
 filter_upwards [hx] with j h; dsimp only [L,Function.comp_def,Vmove]; rw [smul_inv_smul₀ w.ne',h]
lemma bend_m {A:Type}[Fintype A](U:ι→ (A→ℝ) →L[ℝ](A→ℝ))(V:ι→ A→ℝ)(p:Measurable V)(h:@Measurable _ _ _ (borel _) U): Measurable fun i=> U i (V i):=by
 let X:= (A→ℝ); letI:MeasurableSpace (X→L[ℝ] X):=borel _; letI :BorelSpace (X→L[ℝ] X):=⟨rfl⟩; have he:Continuous fun i:(X→L[ℝ]X)×X=>i.1 i.2:= Continuous.clm_apply continuous_fst continuous_snd; exact he.measurable.comp ((show Measurable U from h).prodMk p)

variable {S: StepData N P}{T:Tube SU.group S}{K:Teller SU.group}{F:Forest S.ratio}{A: Stores S}{κ:S.Choices}{q:Chi}{β x C u v σ w e:ℝ}
variable (V:ι→ Config SU.group N)(Y:ι→LinkArray SU.group (Frozen A x F))(Pq:ι→LogArray SU.group (Active A x F))
local notation "Dα"=> (LinkArray G5 (Frozen A x F))
local notation "Lα"=> Prices G5 (Active A x F)
-- exposure boarding
variable (pv:∀ i,MossX k j x A F T (V i) κ u e w q)(hv:Measurable V)(hY:Measurable Y)(hw:0<temp x)
include pv hv hY hw
lemma pluto : Measurable fun i=>liftN T x (V i) κ A F q e (Y i) j:=by
 refine cipher_r Y (fun i z=>liftN T x (V i) κ A F q e z j) hY (fun i=> (pv i).moves) (fun z=> root_m V (fun u=> liftN T x u κ A F q e z j) hw hv (fun i=>?_)); obtain ⟨a,b,c⟩:= (pv i).jumps z; exact b.smooth.continuousAt
variable (hf:Measurable Pq)
include hf
lemma cape_m:Measurable fun i=>realP β T F A (V i) κ x j q e (Y i) (Pq i):=by
 let U(v:Config SU.group N):= paintO (credW T A F κ q e x 1 j v); let a(i):= U (V i) (tape.symm (Pq i)); have ht:Measurable a:=by
    letI :MeasurableSpace (Lα→L[ℝ]Lα):=borel _; letI:BorelSpace (Lα→L[ℝ]Lα):=⟨rfl⟩; have he:Measurable (U ∘ V):= root_m V U hw hv (fun i=>by obtain ⟨a,b,z,q,P,d⟩:= (pv i).jumps 1; exact P.smooth.continuousAt)
    exact bend_m (U ∘ V) (fun i=> tape.symm (Pq i)) (tape.symm.measurable.comp hf) he
 have hJ(i): realP β T F A (V i) κ x j q e (Y i) (Pq i)=liftN T x (V i) κ A F q e (Y i) j + coupling β • a i:=by unfold realP spinC; rw [(pv i).still]; rfl
 rw [funext hJ]; exact (pluto V Y pv hv hY hw).add (ht.const_smul (coupling β))
omit hf pv
variable{C':ℝ}{σ' v':ℝ}
include hv
variable (p':T.up.Bounds T.high C' σ' v')(q':0<e)(pH:2*e< firstRadius SU.group)(t':∀ i, wheelAux T q e x A F (V i) v k κ)
include p' q' pH t'
lemma wand_m(W:ι→ Prices SU.group (Active A x F))(h:Measurable W): Measurable (fun i=> wheel A F T x κ q e (Y i) (W i) (V i)):=by
 let P(i:ι)(y:Dα × Lα):= Esti.wheel A F T x κ q e y.1 y.2 (V i); apply cipher_r (fun i:ι=> (Y i,W i)) P (hY.prodMk h)
 · intro i; have ht:Continuous (fun v:Dα × Lα=> Esti.axle A F T x κ q e v.1 v.2 (V i)):=by
      unfold Esti.axle; simp_rw [(t' i).1]; change Continuous (fun v:Dα × Lα=> (Rows.move T x (V i) κ (shots S x) A F) *ᵥ v.2 + Rows.source T x (V i) κ (shots S x) A F q e v.1); refine Continuous.add (f:=fun v:Dα × Lα=> (Rows.move T x (V i) κ (shots S x) A F) *ᵥ v.2) ?_ ((Rows.source_continuous T x (V i) κ (shots S x) A F q e p' q' pH).comp continuous_fst)
      exact ((Rows.move T x (V i) κ (shots S x) A F).mulVecLin.continuous_of_finiteDimensional).comp continuous_snd
   exact ((Next.SectorChange.gaugeCount.continuous).comp ht) -- use gaugeCount.continuous
 intro z; apply root_m V (fun v=> Esti.wheel A F T x κ q e z.1 z.2 v) hw hv; intro i; exact ((t' i).2 z.1 _ ‖z.2‖ (Jet.allows_const (v:=z.2) _ le_rfl)).smooth.continuousAt -- tune Allows name
include pv hf
lemma split_m : Measurable (fun i=> duty T A F (V i) κ q β e x (Y i) j (Pq i))∧ Measurable (fun i=> phere T A F (V i) κ q e x (Y i) j (Pq i)):=by
 let d(i:ι):= fullV T A F κ q e x (Y i) j (V i); let g(i):=tape.symm (Pq i); have hv'(i:ι):Continuous fun y:Dα=>Offset.f0 T x A F κ (V i) q e y:=by rw [show (fun i'=>Offset.f0 T x A F κ (V i) q e i')=Offset.f0 T x A F κ (V i) q e from rfl, (t' i).1]; exact Rows.source_continuous T x _ _ _ _ _ _ _ p' q' pH -- tune names
 have hz(i): Continuous fun y:Dα=> Dira T A F κ q e x y j (V i):=by
    unfold Dira bankG Offset.b; simp_rw [(pv i).still]
    exact ((credW T A F κ q e x 1 j (V i))ᵀ.mulVecLin.continuous_of_finiteDimensional.comp ((((Rows.gram T x (V i) κ (shots S x) A F).mulVecLin.continuous_of_finiteDimensional).comp (pv i).moves).add (((Rows.move T x (V i) κ (shots S x) A F)ᵀ.mulVecLin.continuous_of_finiteDimensional).comp (hv' i)))) -- prol
 let Q(i):= Dira T A F κ q e x (Y i) j (V i); have ht:Measurable Q:= cipher_r Y (fun i y=>Dira T A F κ q e x y j (V i)) hY hz (fun y=> root_m V _ hw hv (fun i=>by obtain ⟨a,b,c,d,r⟩:= (pv i).jumps y; exact d.smooth.continuousAt))
 have hg:Measurable g:=tape.symm.measurable.comp hf; have hm:Measurable (fun i=>d i *ᵥ g i):=by
    unfold d fullV; simp_rw [(pv _).still]
    let U'(x':Config SU.group N):= paintO (fullV T A F κ q e x 1 j x'); apply bend_m (U' ∘ V) g hg -- tune unfolding
    letI:MeasurableSpace (Lα→L[ℝ]Lα):=borel _; letI:BorelSpace (Lα→L[ℝ]Lα):=⟨rfl⟩; exact root_m V U' hw hv (fun i=>by obtain ⟨_,_,_,_,_,t,d⟩:= (pv i).jumps 1; exact t.smooth.continuousAt)
 have he {α : Type} [Fintype α] (f g:ι→α→ℝ) (p:Measurable f)(h:Measurable g):Measurable (fun i=> f i ⬝ᵥ g i):= Finset.measurable_sum _ (fun i _=> ((measurable_pi_apply i).comp p).mul ((measurable_pi_apply _).comp h))
 exact ⟨measurable_const.mul (he Q g ht hg),((he g _ hg hm).neg).div_const _⟩ -- parse neg div
end
end YM.CF.Oise
