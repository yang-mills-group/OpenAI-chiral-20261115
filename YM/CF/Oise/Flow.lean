import YM.CF.Oise.Cusp
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
section
variable {ι T:Type}[MeasurableSpace ι]
local instance (I:Type)[Fintype I][DecidableEq I]:MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]:BorelSpace (Op I):=⟨rfl⟩
lemma list_m {F:Type}[MeasurableSpace F][NormedAddCommGroup F][BorelSpace F][SecondCountableTopology F](P:ι→ T → F)(p:∀ i, Measurable (fun x=>P x i))(L:List T):Measurable fun x=> (L.map (P x)).sum:=by induction L with| nil =>exact measurable_const | cons a L ih=> simp_rw [List.map_cons,List.sum_cons]; exact (p a).add ih -- tune
lemma can_p {T:Type}[Nonempty T][Fintype T] (L:List T): L=L:=rfl
variable {Z X:Type}[LinearOrder Z][Fintype Z][LinearOrder X][Fintype X]
lemma ticket_m (D:ι→Weave Z X)(p:Measurable fun i=>(D i).pals)(h:Measurable fun i=>(D i).seats)(n:ℕ)(L:List (Twig Z)):Measurable fun i=> ticketB (lank (D i).seats) (Stilo.price (D i).pals (LeanV X)) n L:=by
 induction n generalizing L with | zero=> exact measurable_const| succ n ih=>
 cases L with
 | nil=> exact measurable_const
 | cons a l=>
  simp only [ticketB]; apply Measurable.add
  · unfold lank; exact (Finset.measurable_sum _ fun j _=> (((measurable_pi_apply j).comp ((measurable_pi_apply a).comp h)).smul measurable_const)).mul (ih l) -- name tune
  apply list_m; intro i; have hf:Measurable fun v:ι=> (D v).pals a i.front:= (measurable_pi_apply _).comp ((measurable_pi_apply _).comp p); unfold Stilo.price; split; exact (hf.smul measurable_const).neg.mul (ih i.back); exact (hf.smul measurable_const).mul (ih i.back)
set_option maxHeartbeats 700000 in
lemma issue_meas (D:ι→Weave Z X)(p:Measurable fun i=>(D i).pals)(h:Measurable fun i=>(D i).seats)(F:ι→ FC (LeanV Z))(W:ι→ FC Z)(R:∀ i, spanP (LeanV Z) (F i))(f:Measurable F)(w:Measurable W): Measurable fun i=> Scion.issue (D i) (F i) (W i):=by
 let T:=Finset (LeanV Z); have he(Y:FC Z):Y=pour ((hope Z).symm Y):=by
    conv_lhs=> rw [← (hope Z).apply_symm_apply Y]
    let H:=(hope Z).symm Y; change wont orchestra H=_; simp [wont,playB,pour,H]
 let Y(i:ι)(a:T):= crumb (F i) a; let X_(i:ι):=(hope Z).symm (W i)
 have hx(i:ι): Scion.issue (D i) (F i) (W i)=∑ j:Finset (LeanV Z),∑ k:Finset Z×Finset Z, Y i j • (X_ i k • Scion.issue (D i) (poke j) (piano k)):=by
    unfold Y X_
    conv_lhs => rw [R i,he (W i)]
    unfold pour; rw [map_sum (issue (D i)),LinearMap.sum_apply]; apply sum_congr rfl; intro i' _; rw [map_smul (issue (D i)),LinearMap.smul_apply,map_sum,smul_sum]; simp_rw [map_smul]
 rw [funext hx]; refine Finset.measurable_sum _ fun j _=> Finset.measurable_sum _ fun k _=>?_ ; have hp :Measurable (fun x=> Y x j):= ((show Continuous (fun x:FC (LeanV Z)=> crumb x j) from (continuous_id.matrix_elem j ∅)).measurable).comp f; obtain ⟨Zp,z⟩:= Urn.duet k; obtain ⟨YP,q⟩:= Urn.along_p j; rw [q,z]; simp_rw [Scion.ring_u]; apply Measurable.smul hp; have ht: Measurable (fun i => X_ i k):= (measurable_pi_apply k).comp (((hope Z).symm.toLinearMap.continuous_of_finiteDimensional.measurable).comp w); exact ht.smul (ticket_m D p h _ _)
open Scroll Yaw Eire
variable{N P B:Side}(S:StepData (Domain N B) (Domain P B))(G:Ratio (mid N B) (mid P B)){z:Odd G.count.val}(e:ℝ)(g:0<e)(R: Meter TailB G e)(V: Meter Grave G e)(p:ReefT G e R V)
include p
lemma cala_m (z':Odd G.count.val)(D:ι→Arch G e)(p':Measurable D)(k:ℕ)(H: Ride S): let L(i:ι):= cala G S z' e g R V (D i) k H; Measurable (fun i=>(L i).pals)∧Measurable (fun i=>(L i).seats):=by
 intro L
 have hf(i:Bool)(j):Measurable (fun y:ι=> (if i then (D y).val.1.1 j else (D y).val.2 j)):=by split; exact (measurable_pi_apply j).comp ((measurable_subtype_coe.comp p').fst.fst); exact (measurable_pi_apply j).comp (measurable_subtype_coe.comp p').snd
 have hg(j):Measurable (fun y:ι=> (D y).val.1.1 j)∧Measurable (fun y:ι=> (D y).val.2 j):=⟨hf true j,hf false j⟩
 have hl(j):Measurable (fun y:ι=> (D y).val.1.2 j):=(measurable_pi_apply j).comp (measurable_subtype_coe.comp p').fst.snd
 have hv(b:Bool)(Y:ι→ℂ)(p:Measurable Y):Measurable (fun x=> cSignX b (Y x)):=by unfold cSignX; split; exact (continuous_star (R:=ℂ)).measurable.comp p; exact p
 constructor
 · apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j; unfold L; simp_rw [cryZ]; apply Measurable.add _ measurable_const; refine Finset.measurable_sum _ fun y _=>?_ ; unfold pairZ Urn.soar; dsimp only; split; exact measurable_const; unfold Levier.oakN; refine hv _ _ ?_ -- tune
   exact bill_k g y _ _ _ _ (Classical.choose_spec (p.flow _ y)) D (fun i _=>hg i) (fun i _=>hl i) _ _
 apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro j; unfold L; simp_rw [Yaw.miles]; refine Finset.measurable_sum _ fun y _=>?_; unfold gash Urn.mount; dsimp only; split; swap; · exact measurable_const
 apply hv; exact bill_k g y _ _ _ _ (Classical.choose_spec (p.sail _ _)) D (fun i _=>hg i) (fun i _=>hl i) _ _
end
end YM.CF.Oise
