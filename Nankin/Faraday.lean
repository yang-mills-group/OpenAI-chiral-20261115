import Nankin.Beige
import Nankin.Corral
import Nankin.Flood
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
open VacuumSelection.Spine Py.Dyad Keeping YM.CF.Pannier.Chancel Decaf
variable(P:VacuumSelection.Spine)(u:P.Roster)(M:Py.Rate.Pitching.Focus.Morn P.par.K)(Aα:ℝ)(H:P.Foam u M Aα)
local notation "Y"=> P.run
local notation "π" i:max => P.period (P.projection.rows i)
local notation "ζ" i:max => P.cutoff (P.projection.columns i)
local notation "K"=>P.calibration
abbrev Tix' (j i k:ℕ)(o:Cover)(b:Bool): Tix (stageA P i k) j := ((wrap _) o,b)
abbrev Chem (p:ℕ) (a:Axis) (j s i k:ℕ)(C D:ℕ→ℝ)(d:ℕ)(o:Cover)(b:Bool)(w:(P.run.voyage i).kick≤k):ℂ:=
   let f:=pose2 (stageA P i k) j s (Tix' P j i k o b) (s+1) (stageφ P i k) C D; solder P.run i k w (s+1) (reflMark a 0 f * f)
noncomputable def wafer (j t d:ℕ):ℝ:= Real.exp ((cupcost P.par P.run.τ M.Mult P.run.meter.a j+1)*(4*((2*(d+t):ℕ)+(addgap P.calibration):ℝ))^4) -- parsing addition coerces individually ok
noncomputable abbrev amount (P:VacuumSelection.Spine)(j:ℕ):ℕ:=22+2*((P.run.meter.a j).B^3+(P.run.meter.a j).B)
#check P.calibration
private lemma routePlate{n m:Side}(e:n=m)(p:ℕ)(o:Cover): (e ▸ Lattice.halo p {node (wrap n o)}:Support (More m))=Lattice.halo p {node (wrap m o)}:=by subst m; rfl
include H
lemma busE: ∀ᶠ F:ℕ in atTop,∀ s:ℕ,F ≤ s+1→∀ᶠ x:ℕ in atTop,
 let i:=π x;let k:=ζ x; ∃ w:(P.run.voyage i).kick ≤ k,s+1 ≤ P.run.uv k ∧
 ∃ C D, Bills F (s+1) s P.par.R.L C D ∧∀ (j d:ℕ),F ≤ j→ j ≤ s→∀ a:Axis, ∀o:Cover, ∀b:Bool,
    let t:=amount P j; (P.calibration.ℓ:ℤ)+ t ≤ nodeC o a→ nodeC o a ≤ d→ 2*(d+t)+addgap P.calibration≤(Papal.count P.run j i).val→
        ‖Chem P t a j s i k C D d o b w‖ ≤ wafer P M j t d:=by
 have hey (G:Calibration) : G.ℓ ≤ addgap G:=by unfold addgap stepgap; omega
 filter_upwards [H] with F p s e
 filter_upwards [P.history.finance (s+1), ((P.law.pick.grow_k.comp P.history.growsB).tendsto_atTop).eventually (p (s+1) e)] with x w H₀ i k
 obtain ⟨v,h,S⟩:= H₀ (π x) w.depth
 obtain ⟨c,d,E₁,E₂,t⟩:=S
 refine ⟨w.depth,v,c,d s,⟨E₁,fun i e z=>E₂ i s e z (Nat.le_succ _)⟩,fun j n h0 hM a o b=>?_⟩
 intro m' T₀ T₁ T₂
 let t':=amount P j
 have p':22 ≤ t':= Nat.le_add_right ..
 let H:=P.baller u F (s+1) (π x) (ζ x) v c (d s) j s t' h0 hM (Nat.le_succ s) p'
 let X0:= Tix' P j i k o b
 let n0:=P.calibration.c (momentm P.run (π x) j)
 have p1:H.castM a 0=0:=by change _ * 0=0; exact mul_zero _
 have p2:H.place X0=Lattice.halo t' {node (wrap n0 o)}:=routePlate (Journey.terrain P.run P.large (P.run.ir i) j).symm t' o -- args & equality inferred with Eq rec metadata -> use terrain.symm
 have hn:n0=Papal.count P.run j i:= Journey.terrain ..
 have hp(e₀:(K).ℓ ≤ addgap K) : nodeC o a+(t':ℤ)+ (K).ℓ ≤ n0.val:=by rw [hn]; omega -- notation K.ℓ with K keyword syntax P?
 have hB:((stageA P i k).gram j).p.B^3 + ((stageA P i k).gram j).p.B ≤ t'/2:=by rw [show ((stageA P i k).gram j).p = P.run.meter.a j from (Papal.prices_plot P.run j i k ((hM.trans (Nat.le_succ s)).trans v)).1]; unfold t' amount; omega
 obtain ⟨wx,f,g⟩:=livery H X0 o a t' n p1 p2 T₀ (hp (hey _)) T₁
 let L:=[H.mirror a 0 X0,X0]
 have hx: ‖solder P.run i k w.depth (s+1) (H.film L)‖ ≤ wafer P M j t' n:= (t j s h0 hM (Nat.le_succ _)).2 t' p' hB L (2*(n+t')) T₂ f wx
 unfold L at hx; rw [g] at hx; exact hx
#print axioms busE
end Calico
end YM.CF.Buffered.Afterglow.Tower
