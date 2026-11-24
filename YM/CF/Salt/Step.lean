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
open scoped ENNReal
lemma meal_k {O:Gauge}{x:ℝ}(A:O.Color→ₗᵢ[ℝ]O.Color):MeasurePreserving A (feast O x) (feast O x):=by
 let F:= A.toLinearIsometryEquiv rfl; let S:=closedBall (0:O.Color) x; have hp:MeasurePreserving F (rice O) (rice O):=⟨F.continuous.measurable,stdGaussian_map ..⟩; have hx:= hp.restrict_preimage (isClosed_closedBall (x:= (0:O.Color)) (ε:=x)).measurableSet ; rw [show F ⁻¹' (closedBall 0 x)=closedBall 0 x from ?_] at hx; swap; · ext i; rw [Set.mem_preimage,mem_closedBall_zero_iff,F.norm_map,mem_closedBall_zero_iff]
 exact hx.smul_measure _ -- coe map defeq? method tune
lemma wearB{ι:Type}[Fintype ι][DecidableEq ι](Q:ColorOrtho SU.group ι)(e:Equiv.Perm ι)(v:0<q): MeasurePreserving (Tensor.lifting Q e) (tableG SU.group ι q) (tableG SU.group ι q):=by
 let μ:= feast SU.group q; letI:IsProbabilityMeasure μ:= feast_nn SU.group v
 exact (measurePreserving_pi (fun _:ι=>μ) (fun _:ι=>μ) (f:=fun i'=>Q i') (fun i=> meal_k _)).comp (Girt.normP μ (e:ι→ι) e.injective)
lemma flash_p{N:Side}(f:Sweep N): MeasurePreserving (flashA f) (Wilson.prior SU.group (More N)) (prior SU.group (More N)):=by
 rw [show flashA f=(fun i:Pane N=>polarT f.charge ∘ i) ∘ Lattice.pull f.s ((assembly N).embed f.b) from funext (revoke f)]; exact (measurePreserving_pi _ _ (f:=fun i:Bond (More N)=> polarT f.charge) (fun i=> Skye.twirl ..)).comp (Wilson.prior_pull ..)
def boneS:= Tensor.lifting (fiber s.s (Facet.pasta s) D S) (diagram s.s (Facet.pasta s) S)

abbrev door(d:Bool)(v:Directions SU.group (Domain P B)):= if d then Tensor.lifting (Char.shiftF _) (Equiv.refl _) v else v
abbrev rotor(s:Sweep (mid N B))(G:Ratio (mid N B) (mid P B))(D:Pane (mid N B))(v:Cord S): Cord S:= (Arena.spun S s.s (Facet.pasta s) v.1, (flashA (reSweep G s) v.2.1.1,door s.charge (boneS S s D v.2.1.2)), bun (reSweep G s) v.2.2)
local notation "Σ'"=> rotor S s G D
lemma maze_s (p:0<q) : MeasurePreserving (rotor S s G D) (plummy S q) (plummy S q):=by
 let Q(z):=door s.charge (boneS S s D z); let μ:=tableG SU.group (Bond (Domain P B)) q; have he:=wearB q (fiber s.s (Facet.pasta s) D S) (diagram s.s (Facet.pasta s) S) p
 have hx:MeasurePreserving Q μ μ:=by unfold Q door; split; exact (wearB q (Char.shiftF _) _ p).comp he; exact he -- tune
 letI:IsProbabilityMeasure (springT S q):=lum_p S p; haveI:IsProbabilityMeasure (suit S):=by unfold suit; infer_instance; -- inline issues
 letI:IsProbabilityMeasure μ:= Appel.how SU.group p; haveI:IsProbabilityMeasure ((suit S).prod μ):=inferInstance
 exact (Skye.specU (Arena.spun S s.s (Facet.pasta s))).prod (((flash_p (reSweep G s)).prod hx).prod (tuft (reSweep G s))) -- tune
include t
lemma tower(v:Cord S): cort (flashA s D) (rotor S s G D v)=rot s (cort D v):=by
 let P:=cort D v; have hg(s):airport s P.key=P.key:=by unfold airport Locations.book; simp [P,cort,AnalyticBridge.LocalGaussianLaws.bareStores]
 have hv := person P s; have ht(U V:Monk SU.group S)(p:V.key=U.key)(h:V.park=U.park)(hk:V.k=U.k)(hx:U.V=V.V)(hv:U.U=V.U)(t:U.z=V.z):U=V:=by cases U; cases V; congr 1; exact p.symm; exact h.symm; exact hk.symm
 change cort _ _=rot s P; apply ht (cort (flashA s D) (rotor S s G D v)) (rot s P) ((thereZ ..).trans (hg s)) hv.1 hv.2 (Tye.pose_t P s).symm (Eq.trans (helve S t s v.2.1.1) (toss_a P s).symm)
 change door s.charge _=_; unfold Tye.rot Tye.dice door; split<;> rfl
end YM.CF.Salt
