import YM.CF.Cloak.Shoal
import YM.Further.ROOTED_INTERACTING_REMAINDER.Vault
import YM.CF.Cloak.Wear
import YM.CF.Cloak.Mint
import YM.CF.Rill.Oboe
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cloak
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
open Forge Reine Rill
open Vol Pressure.Tube
open Vol Cay Slate
variable {l:ℕ}{M:Monk G S}{s':ℝ}
open Further.RootedInteractingRemainder Precision Next.SectorChange
-- normative d-independent W. before width & threshold. Uniform for small Z, afterwards local clamp.
open Atala
section E
variable {I:Type} [NormedAddCommGroup I][NormedSpace ℝ I]{F:I→ Config G f}{V:I→ Config G c}{U:I→SU.group.Color}{C A':ℝ}{i:I}
private lemma opposite(b:Bool)(t:ℝ)(q:Chi)(x:ℝ): 1-testing q t x b=testing q t x (!b):=by cases b <;> unfold testing cliff <;> simp
structure Probe (f:I→ℝ)(i:I)(C:ℝ)(n:ℕ):Prop where
 pays: Allows n f i C
 flat : f i=1→ Allows n (fun x=>1-f x) i 0
lemma probe_d (b:Bool)(q:Chi){f:I→ℝ}{x t:ℝ}(h:Dane G n q x)(p:Allows n f i C): Probe (fun u=>testing q t (f u) b) i (Jet.composeCost n x ((2/t^2)*C)) n:=by
 let F:=h _ _ i _ t b p; refine ⟨F.1,fun v=> ?_⟩; simp_rw [opposite]; apply (h _ _ i _ t (!b) p).2; change testing q t _ (!b)=0; rw [←opposite,v,sub_self] -- tune
lemma probF(p:FuelG I F i n C)(h:Dane G n q A')(b:Cell f): Probe (fun u=> tokenF A q x (F u) b) i (dam G n (fiery G x S.patch.L/4) A' C) n:=by
 let t:=fiery G x S.patch.L/4; let Z(u):=SU.group.price (faceValue (F u) b); let L:=Push.Uniform.priceCost G (Push.Uniform.travelCost G n 4 C)
 have hh := trekP _ F p (square b.2.val.1 b.2.val.2) b.1 4 le_rfl
 have hv:Allows n Z i L:= (fare_a (f:=fun y=>SU.group.mat (faceValue (F y) b)) hh).germ (Eventually.of_forall fun _=> fare_h ..)
 unfold tokenF AnalyticBridge.Annulus1AD.profile Pressure.toll; split <;> rename_i t' -- tune
 · simp_rw [chooseB]; exact probe_d _ _ h hv
 simp_rw [chooseF]; exact probe_d _ _ h hv
lemma probI(z:Bond c)(p:FuelG I F i n C)(t:FuelG I V i n C)(h:Dane G n q A')(hp:Frolic A x F i)(hg:S.patch.Branches S.kernel G)(hS:Volo S n a b C m)(ha:0<a)(hm:1≤ A')(hk:0 ≤ m)(he:1≤ C): Probe (fun u=> tidal A x w a q (F u) (V u) k z) i (trout S.patch x w a C A' m n) n:=by
 let X:= horse S.patch n C a A' m; have hh:=wears hp p h hg hS ha hm hk he z k; have he: Allows n (fun u=>star (Inure A x q k a z (F u))) i X:= pawn hh
 have hz:Allows n (fun u=>SU.group.mat (V u z)*star (Inure A x q k a z (F u))) i (purM G n*C* X):=(t z).bilinear _ he (le_refl ‖ContinuousLinearMap.mul ℝ SU.group.Mat‖); exact probe_d _ _ h (fare_a hz)
lemma probR (t:ℝ)(p: Allows n U i C)(h: Dane G n q A'): Probe (fun u=>broad q t (U u)) i (Jet.composeCost n A' ((2/t^2)*(2^n*C*C))) n:=by
 have hp(a:SU.group.Color): broad q t a=testing q t (‖a‖^2/2) true:=by unfold Next.SectorChange.broad Chi.innerShare testing cliff; rw [div_pow]; simp only [ite_true]; congr 1; ring
 simp_rw [hp]; exact probe_d _ _ h (cow p)
end E
end YM.CF.Cloak
