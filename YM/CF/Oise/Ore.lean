/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Oise.Yard
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.RoomB
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
open ConnectedActivityE6.Art
open Scroll Eire Girt Err Matrix
open Push Push.AbsoluteSums -- tune
open Lich.Muster Vol AnalyticBridge.SectorAffine
variable {N P B C:Side} {m k j:ℕ}{ι:Type}[MeasurableSpace ι]
local notation "G5"=>SU.group
variable {S: StepData N P}{T:Tube SU.group S}{K:Teller SU.group}{F:Forest S.ratio}{A: Stores S}{κ:S.Choices}{q:Chi}{β x C u v σ w e:ℝ}
variable (V:ι→ Config SU.group N)(U:ι→ Config SU.group P)(P₀:Finset (Cell N))(P₁: Finset (Cell P))(W:ι→ Bond N → SU.group.Mat)
section
local instance mt : MeasurableSpace SU.group.Mat:=borel _
local instance : BorelSpace SU.group.Mat:=⟨rfl⟩
variable (h:Measurable V)(vu:Measurable U)(t:Measurable W)(f:K.Funds S T) (j:ℕ)
open Offset
include h vu t f
lemma coins_m (P P': BudgetPoint): let p:=P.threshold; let p':= P'.threshold; (∀ i, Measurable (fun x=> Esti.kF T j p p' P₁ P₀ (V x) (U x) i)) ∧(∀ i, Measurable (fun x=> Esti.kI T j p' P₀ (V x) (W x) i)) ∧ (∀ i, Measurable (fun x=> Esti.kC T j p' P₀ (V x) i + (Esti.kL T j p' P₀ (V x) (U x) (W x) i+ Esti.kD T j p' P₀ (V x) i)))∧∀ i, Measurable (fun x=>Esti.kN T j p' P₀ (V x) i):=by
 intro t₀ T₁; obtain ⟨α,β,U_,V_⟩:= f.feeds; obtain ⟨B,H,J,-⟩:=f.crosses; rw [← f.low] at V_; rw [← f.high] at U_
 have hV i j' : Continuous (fun x=> T.Φ j x i j') := leap_cont (Bloch.Row.rights _ _ J K.width.le) ..
 have hB i j' : Continuous (fun x=> T.Φ' j x i j') := lane_cont (Bloch.Row.rights _ _ B K.width.le) ..
 have hX i j' : Continuous (fun x=> T.N j x i j') := lane_cont (Bloch.Row.rights _ _ H K.width.le) ..
 let W'(i x):= Esti.wV T j T₁ P₀ (V x) i
 have hh(i):Measurable (W' i):=by
    unfold W' Esti.wV Esti.taken; split; · exact Measurable.ite (pers_m V h _ _ _) ((plotted_cont V_ _ _ i).measurable.comp h) measurable_const
    split; exact (env_thinned V_ _ _ _ P'.threshold_pos.le i).meas.comp h; exact (plotted_cont V_ _ _ i).measurable.comp h
 have hz(i):Measurable fun x=> Esti.zF T j T₁ P₀ (V x) i:= tableB hV h (Y:=fun x i=> W' i x) hh _
 have hy(i):Measurable fun x=> Esti.zI T j T₁ P₀ (V x) i:= tableB hB h (Y:=fun x i=>W' i x) hh _
 have hD(i):Measurable fun x=>Pressure.zip (T.N j (V x)) (Esti.wV T j T₁ P₀ (V x)) i:=tableB hX h (Y:=fun x i=>W' i x) hh _
 have hi(f g:ι→SU.group.Color)(p:Measurable f)(t:Measurable g):Measurable (fun x=> inner ℝ (f x) (g x)):= ((show Continuous (fun i:SU.group.Color×SU.group.Color=>inner ℝ i.1 i.2) by fun_prop).measurable).comp (p.prodMk t)
 have ht(i):Measurable (fun x=> T.Xf j (U x) i):=(plotted_cont U_ _ _ i).measurable.comp vu; have hb(i):Measurable (fun x=> T.Xn j (V x) i):=(plotted_cont V_ _ _ i).measurable.comp h
 have he(i:Bond N):Measurable (fun x=>Esti.kZ (S:=S) (W x) i):= ((((curvatureL G5).continuous.measurable).comp ((measurable_pi_apply i).comp t)).const_smul (Real.sqrt S.kernel.penalty))
 refine ⟨fun i=>?_,fun i=>?_,fun i=>?_,fun i=> ((hD i).norm.pow_const (2:ℕ)).div_const _⟩
 · exact (plot_m U vu P _ P₁ _ U_ j 1 i).add (Finset.measurable_sum _ fun p _=> (((hz (i,p)).norm.pow_const (2:ℕ)).div_const 2).sub (hi _ _ (hz _) (ht _))) -- order tune.
 · unfold kI; refine (measurable_const.mul (show Measurable _ from ?_)).add ((((hy i).norm.pow_const (2:ℕ)).div_const _).sub (hi _ _ (hy i) (he i)))
   exact (show Continuous (fareG G5) from continuous_const.add (Push.Uniform.traceCharge G5).continuous).measurable.comp ((measurable_pi_apply _).comp t)
 -- retab sprinklers.Cole explicit
 have hv0(j'):Measurable (fun x=> Pressure.unzip (T.Φ j (V x)) (T.Xf j (U x)) j'):= retabB hV h ht _
 have ht'(j'):Measurable (fun x=> Pressure.unzip (T.Φ' j (V x)) (Esti.kZ (S:=S) (W x)) j'):= retabB hB h he _
 have hz'(j'):Measurable (fun x=> Pressure.unzip (T.Φ j (V x)) (zF T j T₁ P₀ (V x)) j'):= retabB hV h hz _
 have hi'(j'):Measurable (fun x=> Pressure.unzip (T.Φ' j (V x)) (zI T j T₁ P₀ (V x)) j'):= retabB hB h hy _
 have hl(j'):Measurable (fun x=> Pressure.unzip (T.N j (V x)) (Pressure.zip (T.N j (V x)) (Esti.wV T j T₁ P₀ (V x))) j'):= retabB hX h hD _
 exact ((Finset.measurable_sum _ fun b _=> (hi _ _ (hh (i,b)) (hb (i,b))).sub (((hh (i,b)).norm.pow_const (2:ℕ)).div_const 2)).sub (plot_m V h P' _ P₀ _ V_ _ _ i)).add ((Finset.measurable_sum _ fun b _=> hi _ _ (hh (i,b)) (((hv0 (i,b)).add (ht' _)).sub (hb _))).add (Finset.measurable_sum _ fun b _=> (hi _ _ (hh (i,b)) ((hh (i,b)).sub (((hz' (i,b)).add (hi' _)).add (hl _)))).div_const _))
end
end YM.CF.Oise
