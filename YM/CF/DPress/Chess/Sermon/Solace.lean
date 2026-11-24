import YM.CF.DPress.Chess.Sermon.Dolly
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
section
variable {I C B L:Side}{η0:ℝ}{j:ℕ}{ho: Odd L.val}{Y: Pricing j L ho (Thread j)}{Q:Grasp Y B η0}
-- restate quantities avoiding YΔ inches.CP.
local notation "M0"=> mid I B
local notation "M1"=> mid C B
variable {A:Loom (mid I B)}{A':Loom (mid C B)}{G:Ratio (mid I B) (mid C B)}{T:StepData (More (mid I B)) (More (mid C B))}{R':GramM (mid C B)}
variable {q:Chi}{u:ℝ}{v: SpaceM}
variable (K0:BaseL Q G R' A A' q u)
variable {B0:HT (mid I B)}{Ar: Fold G (ReOp (mid C B))}
variable [Nonempty (Forest (ratio G))]
include K0
lemma wire (p:T.ratio=ratio G)(t:T.patch.Branches T.kernel SU.group)(v0:Measurable A)(h: Envelope B0)(h':Envelope Ar)(hp:Issue B0 Ar R' A j q u v): gram A (Scree.stove Q A R' A' G T q u v.val) B0= gram A' (denZ R' Q A') (guide T R'.beta A Ar):=by
 let ν:= city M0; let μ:= city M1; let g:= Scree.integrated Q A R' A' G T q u v.val; let w:= guide T R'.beta A Ar; let M:= R'.beta; let v(Z:Orbit M0):= WeightR (B0 (μC A Z)); let f(s:Orbit M0× Orbit M1):= v s.1 (g s.1 s.2); let X:=denZ R' Q A'; let Ψ:=uncurry g; have hg : Envelope Ψ:= Girt.buoy K0 T p t _; let E(x:Orbit M0× Orbit M1):= B0 (μC A x.1); have hv:Envelope E:=Env.along h ((earn v0).comp measurable_fst); let J(x: ReOp M0)(y:Phys M0):= WeightR x y; have hJ:Continuous (uncurry J):=(beamL _).continuous.comp (f:=fun x: ReOp M0 × Phys M0=> acts x.1 x.2) ((acts_cont.comp continuous_fst).clm_apply continuous_snd); have he: Integrable f (ν.prod μ):= Env.integrableX (Girt.kitE E Ψ J hJ hv hg) _
 calc
    _=∫ x:Orbit M0,(∫ y,f (x,y) ∂μ)∂ν:=by unfold gram; exact integral_congr_ae (Eventually.of_forall (fun x=> ((v x).integral_comp_comm (Env.integrableX (Env.along hg (g:=Prod.mk x) measurable_prodMk_left) _)).symm))
    _=∫ y:Orbit M1,(∫ x,f (x,y) ∂ν)∂μ:= (integral_prod f he).symm.trans (integral_prod_symm f he)
    _= _:=by
       unfold gram; apply integral_congr_ae; refine Eventually.of_forall fun y=>?_ ; let j:= μC A' y; let V:= WeightL (X y); have hs:= LoreStage.spend A h' v0 t (β:=M) j; change (∫ x,f (x,y) ∂ν) = V (guide T M A Ar j); rw [LoreStage.repurchased A h' v0 t,← V.integral_comp_comm (Env.integrableX hs ν)]; exact integral_congr_ae (Eventually.of_forall fun x=> issuer K0 T hp x y)
omit K0
abbrev lineWeight (z: Pane n →ℝ)(x:Orbit n) := z x.1 * z (W.shine n x.1)
def Go (z: Pane (mid I B)→ℝ)(T: StepData (More (mid I B)) (More (mid C B)))(A0:Orbit (mid I B)→Phys (mid I B))(v:SpaceM) (G:Ratio (mid I B) (mid C B))(Q:Grasp Y B η0)(q:Chi)(k:ℝ)(A:Loom (mid I B))(A':Loom (mid C B))(R':GramM (mid C B)):Prop:=∀ᵐ x: Orbit (mid I B) ∂city _, A0 x=lineWeight W z x • Scree.stove Q A R' A' G T q k v.val x
variable {E: Orbit (mid I B)→Phys (mid I B)} {z:Pane (mid I B)→ℝ}
lemma honor (p: Go (I:=I) W z T E v G Q q u A A' R')(U V:HT M0): gram A E (peer_H W U V)= gram A (Scree.stove Q A R' A' G T q u v.val) (peer_H W (Learn.weight z U) (Learn.weight z V)):=by
 unfold gram; apply integral_congr_ae; refine p.mono fun i h=>?_ ; let y:=μC A i; let Z:=Scree.stove Q A R' A' G T q u v.val i; dsimp only; rw [h,(WeightR _).map_smul,peer_wt]; change _= WeightL Z ((lineWeight W z i) • peer_H W U V y); rw [(WeightL _).map_smul]; rfl
end
end YM.CF.DPress.Chess.Sermon
