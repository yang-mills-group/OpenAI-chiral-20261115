import YM.CF.Buffered.Probes
/-! # Strengthen clover identification to FIRST Pane only, actual scalar

Even after combining cost representations linearly.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 10000
noncomputable section
namespace YM.CF.Buffered
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG
open Lifted
open Reed (Fine)
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker Classical
attribute [local instance] opCStarAlgebra
abbrev TruthInkSt (K: Calibration)(S:Finset Cover) (p:Buffered.Family K) := ∃ (A:LinksC→ℂ), Coeff true S (A∘Prod.fst)∧ p=scalar K (A∘Prod.fst)∧A 1=0
variable (K:Calibration)(S:Finset Cover)
private lemma plusCoeff {u v': PairsC→ℂ}{S:Finset Cover}(p:Coeff true S u)(q:Coeff true S v'): Coeff true S (u+v'):=by
 refine ⟨fun h=>by contradiction,Girt.kitE u v' (fun x y=> x+y) (continuous_fst.add continuous_snd) p.env q.env,fun x y h w=>?_⟩; exact congrArg₂ (·+·) (p.locus _ _ h w) (q.locus _ _ h w)
private lemma timesCoeff {a:PairsC→ℂ}{S:Finset Cover}(p:Coeff true S a)(c:ℂ):Coeff true S (c • a) :=by
 refine ⟨fun h=>by contradiction,Girt.pole_w _ (c • ·) (Continuous.const_smul continuous_id c) p.env,fun x y h w=>?_⟩; exact congrArg (c • ·) (p.locus _ _ h w)
lemma true_ink_steel (p:Buffered.Family K)(t:p∈ Submodule.span ℂ {F|∃ (A:LinksC→ℂ), Coeff true S (A∘Prod.fst)∧ F=scalar K (A∘Prod.fst)∧A 1=0}):TruthInkSt K S p:=by
 let v:Set (Buffered.Family K) :={f| TruthInkSt K S f}; change TruthInkSt K S p; apply Submodule.span_induction (p:=fun v _=> TruthInkSt K S v) _ _ _ _ t
 · exact fun x h=>h
 · refine ⟨0, Coeff.fromC true S (f:=(0:LinksC→ℂ)) continuous_const (fun _ _ _=> rfl), ?_, rfl⟩; funext n z; change _= (0:ℂ) • _; rw [zero_smul]; rfl
 · rintro x y u v ⟨F,p,rfl,q⟩ ⟨G,k,rfl,z⟩; refine ⟨F+G,plusCoeff p k,funext fun i=> funext fun x=>(add_smul (F ((onC (K.c i)) x.1)) (G ((onC (K.c i)) x.1)) 1).symm,?_⟩; simp [q,z]
 rintro u x p ⟨F,k,rfl,z⟩; exact ⟨u • F,timesCoeff k u,funext fun i=> funext fun x=> ((mul_smul u (F ((onC (K.c i)) x.1)) (1))).symm,by simp [z]⟩
#print axioms true_ink_steel
end YM.CF.Buffered
end
