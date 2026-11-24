import YM.CF.Salt.Step
import YM.CF.Salt.Tract
import YM.CF.Salt.Stone
import YM.CF.Salt.Piers
import YM.CF.Haro.Tacit
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure Slate Atala
variable {P N B:Side}{G:Ratio (mid N B) (mid P B)}(S:StepData (Domain N B) (Domain P B))(x:ℝ)(t:S.ratio=ratio G)(s:Sweep (mid N B))(A:Stores S)(V:Pane (mid P B))(X:Support (Domain P B))
open Precision Tree Tarn Plume MeasureTheory ProbabilityTheory
open AnalyticBridge.GaussianFieldAlignment Orthogonal Channels
variable (p₀ q:ℝ)(D:Pane (mid N B))(g:Site (Domain N B)→SU.E) (Xv:Cord S)
local notation "Ρ"=> (plummy S q)
local notation "m"=> (mid P B)
local notation "W"=> reSweep G s
variable {F:Type*}[MeasurableSpace F][Countable F][MeasurableSingletonClass F]
local notation "Ξ"=> constantGauge g S.ratio
local notation "Δ"=> (shiftZ g)
abbrev tintL(g:Site (Domain N B)→SU.E):= Tensor.lifting (Gauges.rotating (constantGauge g S.ratio)) (Equiv.refl (Bond (Domain P B)))
abbrev warpD(S:StepData (Domain N B) (Domain P B))(g:Site (Domain N B)→SU.E)(x:Cord S): Cord S:= (x.1, (Lattice.gauge (constantGauge g S.ratio) x.2.1.1, tintL S g x.2.1.2), threadG (constantGauge g S.ratio) x.2.2)
lemma wellT : cort (gauge g D) (warpD S g Xv) = shiftZ g (cort D Xv):=rfl
lemma folk (p:0<q): MeasurePreserving (warpD S g) (plummy S q) (plummy S q):=by
 let μ:=tableG SU.group (Bond (Domain P B)) q; letI:IsProbabilityMeasure (springT S q):= lum_p S p; haveI:IsProbabilityMeasure (suit S):=by unfold suit; infer_instance
 letI:IsProbabilityMeasure μ:= Appel.how SU.group p; letI:IsProbabilityMeasure ((suit S).prod μ):=inferInstance
 exact (MeasurePreserving.id _).prod (((Wilson.prior_gauge (G:=SU.group) (constantGauge g S.ratio)).prod (wearB q (Gauges.rotating Ξ) _ p)).prod (threads Ξ))
-- embeddings. build
abbrev tuftE{N:Side}(f:Sweep N): Ids N ≃ᵐ Ids N where
 toFun:=bun f
 invFun:=bun f⁻¹
 left_inv:=tuftT f
 right_inv x:=by simpa only [inv_inv] using tuftT f⁻¹ x
 measurable_toFun:=(tuft f).measurable
 measurable_invFun:=(tuft f⁻¹).measurable
lemma ga_t {N:Side}(g: Site N→ SU.group.El)(V: Config SU.group N): Lattice.gauge g⁻¹ (Lattice.gauge g V)=V:=by funext i; simp [Lattice.gauge]; group
abbrev flagT{N:Side}(g:Site N→SU.group.El): Config SU.group N ≃ᵐ Config SU.group N where
 toFun:=Lattice.gauge g
 invFun:=Lattice.gauge g⁻¹
 left_inv:=ga_t g
 right_inv x:= by simpa only [inv_inv] using ga_t g⁻¹ x
 measurable_toFun:= (Wilson.prior_gauge (G:=SU.group) g).measurable
 measurable_invFun:= (Wilson.prior_gauge (G:=SU.group) g⁻¹).measurable
abbrev thread_s{N:Side}(g:Seat N→SU.E): Ids N≃ᵐIds N where
 toFun:=threadG g
 invFun:=threadG g⁻¹
 left_inv:=threads_T g
 right_inv x:=by simpa only [inv_inv] using threads_T g⁻¹ x
 measurable_toFun:=(threads g).measurable
 measurable_invFun:=(threads g⁻¹).measurable
lemma knit_a : MeasurableEmbedding (warpD S g):=by
 let Bv:= (tintL S g).toHomeomorph.toMeasurableEquiv; let E:TeamY (mid P B) ≃ᵐ TeamY (mid P B):= MeasurableEquiv.prodCongr (MeasurableEquiv.prodCongr (flagT Ξ) Bv) (thread_s Ξ) -- P shadow
 exact ((MeasurableEquiv.refl (Arena.Tab S)).prodCongr E).measurableEmbedding
lemma codaT{d:Bool} : MeasurableEmbedding (door (P:=P) (B:=B) d):=by
 unfold door; split; next p=> exact (Tensor.lifting (Char.shiftF _) (Equiv.refl (Bond (Domain P B)))).toHomeomorph.measurableEmbedding
 exact MeasurableEmbedding.id
abbrev flashL{N:Side}(s:Sweep N): Pane N≃ᵐ Pane N where
 toFun:=flashA s
 invFun:=flashA s⁻¹
 left_inv :=revB s
 right_inv x:=by simpa only [inv_inv] using revB s⁻¹ x
 measurable_toFun:= (flash_p s).measurable
 measurable_invFun:= (flash_p s⁻¹).measurable
lemma full_t:MeasurableEmbedding (rotor S s G D):=by
 let M:Arena.Tab S≃ᵐ Arena.Tab S:={toEquiv:=Arena.spun S s.s (Facet.pasta s),measurable_toFun:= (specU _).measurable,measurable_invFun:= (specU _).measurable}
 let A:= codaT (P:=P) (B:=B) (d:=s.charge); exact M.measurableEmbedding.prodMap (((flashL W).measurableEmbedding.prodMap (A.comp (boneS S s D).toHomeomorph.measurableEmbedding)).prodMap (tuftE _|>.measurableEmbedding))
lemma warpE{F:Type*}[MeasurableSpace F](μ:Measure F){n:Side}(u r:Bool)(K:UNI (Single n))(Φ:F → Cipher n): (∫ i, paintR u r K (Φ i)∂μ)= paintR u r K (∫ i,Φ i∂μ):=by
 let P:=paintR u r K; let T:=P.toLinearMap
 have hp:Injective T:=by
    intro i j p; apply Subtype.ext; let q:=u.xor r; let R:= quantU (spice K r); have he:twist R (windX q i.val)=twist R (windX q j.val):=congrArg (fun i:Cipher n=> i.val) p; have hx: windX q i.val=windX q j.val:= (twist R).injective he; unfold windX at hx; split at hx; next v=> rw [← cc_cc i.val,hx,cc_cc]
    exact hx
 let S:= (LinearEquiv.ofBijective T ⟨hp,(LinearMap.injective_iff_surjective (f:=T)).mp hp⟩).toContinuousLinearEquiv
 exact ContinuousLinearEquiv.integral_comp_comm (E:=Cipher n) (F:=Cipher n) (𝕜:=ℝ) S Φ -- tune
end YM.CF.Salt
