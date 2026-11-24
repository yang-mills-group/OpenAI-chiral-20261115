import YM.CF.DPress.Chess.Floor.Aerie
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt Sermon
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough ComplexOrder Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{ℓ d r:ℕ}{β u k:ℝ}{P:Loom n}
namespace Porch
variable {G:Orbit n→ Phys n}{F H: HT n}
def TopTrace(G:Orbit n→Phys n):Prop := ∀ᵐ x∂prior SU.group (More n), ∀ (y z:Ids n)(A:ReOp n), WeightR A (G (x,y))= WeightR A (G (x,z))
lemma rent_C{X:Type*}[MeasurableSpace X]{Y:X→ Phys n}{A:X→ ReOp n}(u:Envelope A)(v:Envelope Y) : Envelope (fun i=> WeightR (A i) (Y i)):= Girt.kitE _ _ (fun (x:ReOp n) (y:Phys n)=> WeightR x y) ((beamL _).continuous.comp (f:=fun x: ReOp n × Phys n=> acts x.1 x.2) ((acts_cont.comp continuous_fst).clm_apply continuous_snd)) u v -- tune
private abbrev tilt (P:Loom n)(F: HT n)(G: Orbit n→ Phys n)(x: Orbit n):ℂ:= WeightR (F (μC P x)) (G x)
private lemma unrue (i: Pane n)(g:Phys n)(u:∀ (y:Ids n)(A:ReOp n), WeightR A (G (i,y))= WeightR A g)(t:Measurable P)(h:Envelope F) : (∫ y, tilt P F G (i,y) ∂depot n)= (∫ y, tilt P (payload (glean P F)) G (i,y) ∂depot n):=by
 let V:= WeightL g; let ν:= Robe.τ P i; let z:= glean P F i; let U(y:Pane n):= F (i,y); let H(y:Ids n):=P (i,y); letI:IsProbabilityMeasure ν:= Robe.prob t i; have ht: Envelope U:= Env.along h (g:=Prod.mk i) measurable_prodMk_left
 have hg(y:Ids n):tilt P (payload (glean P F)) G (i,y)= V z:= u y z; have he(y:Ids n): tilt P F G (i,y)= V (U (H y)):= u y (U (H y)); simp_rw [hg,he,integral_const,probReal_univ,one_smul]
 exact (Transit.expect H (Robe.lever t i) (fun x:Pane n=> V (U x)) (V.continuous.measurable.comp ht.meas)).trans (V.integral_comp_comm (Env.integrableX ht ν))
lemma trace_p (p:TopTrace G)(t: Measurable P)(h:Envelope F)(v:Envelope G): Sermon.gram P G F=Fixed.functional G (glean P F):=by
 let f:Orbit n→ℂ:= fun x=> WeightR (F (μC P x)) (G x); let H:Orbit n→ℂ:=fun x=> WeightR (glean P F x.1) (G x); change (∫ x,f x ∂city n)=∫ y,H y∂city n; have hh: Envelope f:=rent_C (Env.along h (earn t)) v; have he: Envelope H:=rent_C (Env.along (wait_C t h) measurable_fst) v; rw [integral_prod f (Env.integrableX hh (city n)),integral_prod H (Env.integrableX he (city n))]; refine integral_congr_ae (p.mono (fun i u=>?_)); let z:=Classical.arbitrary (Ids n); exact unrue (G:=G) i (G (i,z)) (fun y A=> u y z A) t h
lemma release (p:TopTrace G)(t: Roof n u k d P)(ψv: Firm P u d)(v:Envelope G)(Z:Wall.wage r d ≤ ℓ): ∃ A:HT n→ Fixed.Test n,(∀ F: HT n,Learn W ℓ F→Boss n (W.crop n Wall.rail) (A F)) ∧ ∀ F H, Learn W ℓ F → Learn W ℓ H→ Sermon.gram P G (peer_H W F H)= Fixed.functional G (peer W (A F)* A H):=⟨glean P,fun _ l=> price W l t.bill ψv Z,fun F H vE h=>(trace_p p t.bill (peer_C W vE.envelope h.envelope) v).trans (congrArg _ (stem W vE h t ψv Z).symm)⟩
end Porch
end YM.CF.DPress.Chess
#print axioms YM.CF.DPress.Chess.Porch.release
#print axioms YM.CF.DPress.Chess.Porch.base
