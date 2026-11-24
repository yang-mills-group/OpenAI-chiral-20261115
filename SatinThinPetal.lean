import SatinThinSteps
import SatinThinPoles

set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise


/- exact shape and registration charge TRUE or FALSE. Ready for clover-mark reads. -/
open Reef StressFlux AnalyticBridge.VerifiedReset
variable {n N B:Side}
lemma echo_cost (x:Pane n)(o:Skye.Seat n)(b:PlaqAxes): petals (echo x) o b= frolic (petals x o b):=by
 change clover _ _ _ _=_; unfold clover stencil; simp_rw [StressFlux.plate, echo_t,Reef.swing]; change _= frolic ( (4:ℝ)⁻¹ • ((_ - _)-(_-_))); rw [map_smul]; simp_rw [map_sub]; rfl
-- formula in terms of one stencil (side-local, variation follows setup exponentL with flag mask)
def quadScore {n:Side} (a:Site n)(F:Config SU.group n) : ℝ:= (∑ i:PlaqAxes,starWeight i * ‖petals F a i‖^2)/2
lemma petal_core (U:Pane n)(a:Skye.Seat n)(P:BudgetPoint)(q:ℝ): kerP a P (q • mainSlot) U = ((q/P.threshold^2*quadScore a U:ℝ):ℂ):=by
 let K:=P.threshold; have h(i j:PlaqAxes): (q • mainSlot) i j= if i=j then (↑(q*starWeight i):ℂ) else 0:=by
    unfold mainSlot; simp only [Pi.smul_apply]; split; next h=> simp [h, Complex.real_smul]
    next h=> simp
 unfold kerP AnalyticBridge.VerifiedReset.counter AnalyticBridge.VerifiedReset.quad; simp_rw [h]; simp only [apply_ite,Complex.zero_re,Complex.zero_im, Complex.ofReal_im, Complex.ofReal_re,ite_self,zero_div,sum_const_zero,zero_mul,Complex.ofReal_zero, add_zero]; apply congrArg ((↑):ℝ→ ℂ)
 unfold quadScore; rw [←mul_div_assoc,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro i _; rw [sum_eq_single i]; simp only [ite_true,real_inner_self_eq_norm_sq]; ring -- maybe coerc
 · intro j _ v; rw [if_neg v.symm,zero_div,zero_mul]
 simp
lemma quad_move (s:Signed)(p:Quad s)(b a:Skye.Seat n)(F:Pane n): tax s * quadScore a (pull s b F) = quadScore (affine s b a) F:=by
 unfold quadScore; simp_rw [petals_moves,cornerFlux]; rw [←mul_div_assoc,Finset.mul_sum]; congr 1; refine sum_equiv (PlaqAxes.transform s) (fun _=>by simp) fun i _=> ?_; rw [star_thin _ p,norm_smul,Real.norm_eq_abs,scar_abs,one_mul,mul_assoc]
lemma quad_up (s:Sweep n)(p:s∈cycleSweep n)(x y:Site n)(z:Earlier s x y)(F:Pane n): tax s.s * quadScore (node y) (flashA s F)=quadScore (node x) F:=by
 rw [←z,sitA,revoke]; cases s.charge; exact quad_move s.s p _ _ _
 let v:Pane n:=pull s.s ((assembly n).embed s.b) F; have hx(a:Skye.Seat n): quadScore a (echo v)=quadScore a v:=by unfold quadScore; simp_rw [echo_cost,frolic.norm_map];
 exact (congrArg (tax s.s *·) (hx (node y))).trans (quad_move s.s p _ _ _)
lemma plate_core (U: Pane n)(a:Skye.Seat n)(P:BudgetPoint)(q:ℝ): plateZ a P (q • mainSlot) U=(q/P.threshold^2*quadScore a U) • (1: Cipher n):=by
 rw [plateZ,petal_core]; rw [←Complex.coe_smul (q/P.threshold^2*quadScore a U)]; rfl

def cloth_E {n:Side}(P:BudgetPoint)(q:ℝ)(x: Site n):RegBudget n:= Pi.single (Φrap n x 10) (Moto.plateZ (node x) P (q • mainSlot))
lemma cloth_sign (s:Sweep n)(p:s∈cycleSweep n)(x y:Site n)(u:Earlier s x y)(P:BudgetPoint)(q:ℝ) : passingR n s (cloth_E P q x) (bandSign s • cloth_E P q y) :=by
 intro i f; change bandSign s • (cloth_E P q y (moveHub s i) (flashA s f))=_; unfold cloth_E; by_cases v:i=Φrap n x 10
 · subst i; rw [move_bill u 10,Pi.single_eq_same,Pi.single_eq_same,plate_core,plate_core,map_smul,map_one,smul_smul,mul_left_comm _ _ (quadScore _ _),quad_up s p _ _ u f] -- synt assoc issue
 rw [Pi.single_eq_of_ne v,Pi.single_eq_of_ne (show moveHub s i≠Φrap n y 10 from (by rw [←move_bill u 10]; exact (scope_q s).injective.ne v)),Pi.zero_apply,Pi.zero_apply,smul_zero,map_zero]
def cloth_topic (P:BudgetPoint) (q:ℝ):Topic n where
 face x E F:=E=cloth_E P q x ∧ F=0
 color s v x y E W F T p X Y:=by
    rw [X.1,X.2,Y.1,Y.2,smul_zero]; exact ⟨cloth_sign s v x y p P q,fun _ _ _=> (map_zero _).symm⟩
lemma cloth_owns (P:BudgetPoint)(q:ℝ)(x:Site n) : (cloth_topic P q).face x (cloth_E P q x) 0:= ⟨rfl,rfl⟩
end YM.CF.QuadClock
