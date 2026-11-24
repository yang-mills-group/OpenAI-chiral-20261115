import YM.CF.DPress.Chess.Sermon.Local
import YM.CF.DPress.Chess.Lift.Basic
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Sermon
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire Scree Lift Transit Bough Turn Push.SectorMeasure Tulip
open Fock Finset Girt
open Cube (More assembly node)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough Matrix.Norms.L2Operator YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable (W:Wall) {n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)}{r ℓ d:ℕ}{β u k:ℝ}{P:Loom n}
open Lat Scroll Girt Peaks Paige Vault SU Haro
/-! Accounting for a dual ℝ-linear expectation. Preserve real (not complex!) handling of reflection from `peer_H`, but keep the entire complex-valued integrand. Offset must be included in the stove. -/
abbrev WeightR (A:ReOp n): Phys n →L[ℝ] ℂ:= (beamL n).comp ((acts A).restrictScalars ℝ)
def WeightL (x: Phys n) : ReOp n→L[ℝ]ℂ :=
 { toFun := fun A=> beamZ n (acts A x), map_add':= fun A B=> by rw [act_add,beamZ,inner_add_right] , map_smul':=fun a A=> by -- tune semicolon parse
     change beamL n (acts (a • A) x)=a • beamL n (acts A x); rw [← Complex.coe_smul a,act_smul, Complex.coe_smul,map_smul],
   cont:= by exact continuous_const.inner (acts_cont.clm_apply continuous_const)}
def gram (P:Loom n)(G:Orbit n→Phys n)(U:HT n):= ∫ y, WeightR (U (μC P y)) (G y) ∂city _
section
variable {I C B L:Side}{η0:ℝ}{j:ℕ}{ho: Odd L.val}{Y: Pricing j L ho (Thread j)}{Q:Grasp Y B η0}
-- restate quantities avoiding YΔ inches.CP.
local notation "M0"=> mid I B
local notation "M1"=> mid C B
variable {A:Loom (mid I B)}{A':Loom (mid C B)}{G:Ratio (mid I B) (mid C B)}{T:StepData (More (mid I B)) (More (mid C B))}{R':GramM (mid C B)}
variable {q:Chi}{u:ℝ}{v: SpaceM}
variable (K0:BaseL Q G R' A A' q u)
abbrev starQ (A: HT n):=A -- tune remove
include K0 in
lemma stance0(x:Stage M1)(y:Orbit M0)(F:Forest (ratio G)): JointB G (crop_U G q u (pad A x y F)) η0:=K0.trial F x.2 y
variable {B0:HT (mid I B)}{Ar: Fold G (ReOp (mid C B))}
def Issue (B0:HT (mid I B))(Ar:Fold G (ReOp (mid C B)))(R':GramM (mid C B))(A:Loom (mid I B))(j:ℕ)(q:Chi)(u:ℝ)(v:SpaceM):Prop :=∀ (x:Stage (mid C B))(y:Orbit (mid I B))(F:Forest (ratio G)), let z:=pad A x y F; rise G R'.J.M j v.val (B0 (μC A y)) (crop_U G q u z) (Ar z)
variable [Nonempty (Forest (ratio G))]
include K0
theorem issuer (T:StepData (More (mid I B)) (More (mid C B)))(h:Issue B0 Ar R' A j q u v)(x:Orbit M0)(y:Orbit M1): WeightR (B0 (μC A x)) (Scree.integrated Q A R' A' G T q u v.val x y)= WeightL (denZ R' Q A' y) (loreC A T Ar (μC A' y) R'.beta x) :=by
 let P:= B0 (μC A x); let Y:= denZ R' Q A' y; let l:= WeightR P; let r:= WeightL Y; let q₁:= μC A' y; let f(F:Forest (ratio G)):= pad A q₁ x F; let b:=R'.beta; let d:=T.density (G:=SU.group) b y.1 x.1; have ht(F:Forest (ratio G)):l (carrier Q A R' A' G T q u v.val F x y)= r (d • Ar (f F)):=by
    unfold carrier; rw [l.map_smul, r.map_smul]; apply congrArg (d • · : ℂ→ ℂ); change beamZ M0 (acts (B0 (μC A x)) (pathH G j R'.J.M (crop_U G q u (pad A q₁ x F)) v.val Y))=_; rw [h q₁ x F Y]; exact Lift.beam_M K0.power K0.size K0.pe (stance0 K0 q₁ x F) .. -- tune
 unfold integrated loreC; change l (_ • _)=r (d • ∫ y, Ar (f y)∂St _); rw [cash_mean (fun y=>Ar (f y)), l.map_smul, _root_.map_sum l, sum_congr rfl (fun i _=>ht i), smul_comm d,r.map_smul,smul_sum (r:=d), _root_.map_sum r] -- one `smul_sum`
end
end YM.CF.DPress.Chess.Sermon
