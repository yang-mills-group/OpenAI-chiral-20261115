import YM.SU5.Hiro.Ladles
import YM.SU5.Aria.Stagehand
import YM.SU5.Aria.Serves
/-!
# Matter-color current comparison with separate gauge readout.
Pure factors herein need not be separately invariant under SU, but unlike Lode
the *matter* is tested using same-site Lie COLOR generators (even bilinears).
Transport sensitivity comes through a locally matched plaquette plus a second such LOCAL, at separated footprint. Does not claim that any Wightman reconstruction
has been proven.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 260000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Hiro Ballad Papal Regis.Head Regis.Head.Brecht
open Twah (DirSpin)
open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn
open CF.Pannier.Chancel
namespace Spine
variable (P: Spine)(L G:DirSpin)(R:ℕ)(F D: PlaqAxes)(x y:Cover){k:ℝ}(p:0<k)(s:ℕ)
local notation "K"=>P.calibration
local notation "A"=>SU.group
local notation "Px"=> platePin F (nodeC x)
local notation "Py"=> platePin D (nodeC y)
-- components are in observable extension, in exactly disjoint sets even on purely gauge test.
noncomputable def condorM : ColorL →ₗ[ℝ] P.Test where
 toFun b:= P.art _ (Tower.aux_test (((holdPass x L R b).narrow (P.calibration)).widen))
 map_add' a b:=Subtype.ext (funext fun m=> funext fun X=> map_add (wrapCurrent x L R ((K).c m)) a b) -- K parser
 map_smul' v a:=Subtype.ext (funext fun m=>funext fun X=> map_smul (wrapCurrent x L R ((K).c m)) v a)
def paletteM (i:prismIndex): P.Test := P.art _ (Tower.aux_test ((InTest.seed («K»:=P.calibration) (sceneryCoeff F x (Papal.museumV (P:=P.par) s) p i)).widen))
#check @condorM
#check @paletteM
private lemma sumFamily (W:ℕ→P.Test) {n:ℕ} : W n=W n:=rfl
noncomputable def scoutCast : P.Test→ₗ[ℂ] Family P.calibration:=⟨⟨fun i=>i.val,fun _ _=>rfl⟩,fun _ _=>rfl⟩
local notation "γ"=> P.jade L R F x p s
local notation "C"=> P.condorM L R x
local notation "D'"=>P.paletteM F x p s
local notation "B'"=>P.condorM G R y
lemma condor_own (d:ColorL): C d∈bay P.calibration {nodeC x} false:= (holdPass x L R d).narrow _
lemma palette_own (i:prismIndex): D' i∈bay P.calibration Px false:= InTest.seed («K»:=P.calibration) (sceneryCoeff _ _ _ p i) -- p issue
include p
lemma proper_own : γ∈bay K Px false∧ γ∈enclave K:=⟨ (currentLabel F x (Papal.museumV (P:=P.par) s) R L p).1.narrow _,P.celebrity _⟩
lemma composedBudget : γ = ∑ i:prismIndex, D' i * C (mug i):=by
 apply Subtype.ext; change _=scoutCast P (∑ i:prismIndex,_); rw [map_sum]; funext n Y; rw [show ((P.jade L R F x p s):Family K) n Y = currentF F x (Papal.museumV (P:=P.par) s) k R L ((K).c n) Y from rfl,scenes]; simp only [Finset.sum_apply]; rfl
omit p
-- traced pure matter factor P~. color vanish using ANY axis and ANY conditioning with same gauge price.
lemma hold_certificate (z:Cover→SU.E) (b:ColorL): pennant K z (C ((SU.group.adjoint (z (nodeC x))) b))= C b:=by
 apply appointed K {nodeC x} z; swap; · exact widerBay K {nodeC x} false (P.condor_own L R x _)
 intro m g h X; let a:=(K).c m; change holdC x L R _ a (Buffered.simultaneous g X)= twist (quantU (tradew _ g)) (holdC _ _ _ b a X); rw [←h (nodeC x) (mem_singleton_self _)]; exact current_cov x L R b X g -- def harmony left Y
variable (E:P.Test→ₗ[ℂ]ℂ)(u:∀ (f:P.Test)(g:GVertex), E (pennant P.calibration g f)= E f)
include u
lemma centroid_empty(q:nodeC x ≠ nodeC y)(b a:ColorL): E ((C b)*(B' a))=0:=by
 let ℒ:= LinearMap.mul ℂ (P.Test); let X:= (((E.comp (ℒ.flip (B' a))).restrictScalars ℝ).comp C).toContinuousLinearMap
 have hp:X=0:= by
    apply Stationary.color_fixed Thera.yet_one; intro g t; let p:= nodeC x; let i:= nodeC y; let ρ:=Function.update (fun _:Cover=> (1:SU.E)) p g; have he:ρ p=g:= update_self ..; have hE:ρ i=1:= update_of_ne q.symm ..
    change E ((C _)* _)= E ((C t) * (B' a)); rw [← u _ ρ,map_mul]; rw [← he,P.hold_certificate L R x ρ t, show pennant K ρ (B' a)=B' a from ?_]; -- defeq syntax
    simpa only [show ρ (nodeC y)=1 from hE,SU.group.adjoint_one] using P.hold_certificate G R y ρ a -- hE i definitional simp?
 exact DFunLike.congr_fun hp b
lemma single_empty (b:ColorL): E (C b)=0:=by
 let X:= (((E.restrictScalars ℝ).comp C).toContinuousLinearMap); have he:X=0:= by
   apply Stationary.color_fixed Thera.yet_one; intro g t; change E (C _)=_; rw [←u _ (fun _=>g),P.hold_certificate L R x (fun _=>g)]; rfl
 exact DFunLike.congr_fun he b
omit u
lemma eInvariant (x:P.Test)(g:GVertex): P.eReadL s (pennant K g x)=P.eReadL s x:=by change P.E s _=P.E s _; rw [← P.occupied 3,←P.occupied 3, ←P.at_label,←P.at_label,P.reading_gauge] -- parser eInvariant
lemma oracleInvariant (j:Axis)(x:P.Spectrum0 3)(s:ℕ)(q:P.Test)(g:GVertex):P.singleState j s (P.otherSpectrum 3 j x) (pennant K g q)=P.singleState j s (P.otherSpectrum 3 j x) q:=by rw [P.single_state, P.single_state,P.reading_gauge]
-- erasure even as compressed
lemma Lie_compression_message(j:Axis)(q:nodeC x≠ nodeC y)(a b:ColorL): P.reading j s ((C a)*(B' b))=0:=by
 apply P.chi_all; intro z; exact P.centroid_empty L G R x y (P.singleState j s z) (fun x ρ=> by rw [P.single_state,P.single_state,P.reading_gauge]) q a b
include p
-- comparison. ***NO comparison of tensor product of separately gauge-INVARIANT elements here.*** Both pure fields may have their adj index free. Product with contracted indices in genuine local algebra of chosen physics. Factors footprint at two polarly disjoint sites. For mixing check, centroid_empty component proof.
def separatesBudget (P:Spine)(L G:DirSpin)(R:ℕ)(F D:PlaqAxes)(x y:Cover){k:ℝ}(p:0<k)(s:ℕ)(E:P.Test→ₗ[ℂ]ℂ):Prop:=
 ∀ b a:prismIndex, let X:= (P.paletteM F x p s b)*(P.paletteM D y p s a); let Y:=P.condorM L R x (mug b)* P.condorM G R y (mug a); E (X*Y)= E X* E Y
-- factors gauge arrays can retain true trajectories at z, still no issue because all matter parts vanish not changed by curvature witness in coefficient
include u
lemma ifSeparating (q:nodeC x≠ nodeC y)(b:P.separatesBudget L G R F D x y p s E): E ((P.jade L R F x p s)*(P.jade G R D y p s))=0:=by
 rw [P.composedBudget,P.composedBudget]; simp_rw [sum_mul,mul_sum,map_sum]; apply sum_eq_zero; intro k _; apply sum_eq_zero; intro i _; specialize b k i; let X:=P.paletteM F x p s k*P.paletteM D y p s i; let Y:=P.condorM L R x (mug k)* P.condorM G R y (mug i); change E (X*Y)=_ at b; rw [show _*_=X*Y from (by unfold X Y; ring),b]; change E X*(E ((C _)*(B' _)))= _; rw [P.centroid_empty L G R x y E u q,mul_zero]
lemma bracketing (q:nodeC x≠ nodeC y)(b:E ((P.jade L R F x p s)*(P.jade G R D y p s))≠0): ¬ P.separatesBudget L G R F D x y p s E:= fun f=> b (P.ifSeparating L G R F D x y p s E u q f)
lemma proper_message (q:nodeC x≠nodeC y)(b:E ((P.jade L R F x p s)*(P.jade G R D y p s))≠0):∃ (v w:prismIndex), let Θ:=(P.condorM L R x (mug v))*(B' (mug w)); let Ψ:=(D' v)*(P.paletteM D y p s w); E Θ=0 ∧ (∀ j:Axis, P.reading j s Θ=0)∧ ‖E (Ψ * Θ)- E Ψ * E Θ‖>0:=by
 let t:= P.bracketing L G R F D x y p s E u q b; unfold separatesBudget at t; -- let t rewrite error
 push Not at t
 obtain ⟨v,w,T⟩:=t
 refine ⟨v,w,?_⟩; intro z Z; exact ⟨P.centroid_empty L G R x y E u q _ _, fun i=>P.Lie_compression_message L G R x y s i q _ _, norm_pos_iff.mpr (sub_ne_zero.mpr T)⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bracketing
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.single_empty
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.proper_message
