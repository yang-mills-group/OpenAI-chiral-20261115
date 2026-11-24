import YM.SU5.Hiro.Whisk
import YM.SU5.Hiro.Leaves
import YM.SU5.Circuit.Honey
/-!
 Current * curvature coupled G singlet.
-/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Hiro
open Function Filter Fock Finset Cube Spire Scroll MeasureTheory Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree Gloss Branch RP Reflect Wilson Lat Rush SU Lat Lattice Precision Tree Tenant Push.SectorMeasure Peaks Tulip Buffered Afterglow Lifted Heat Advance Vale Window
open Reed (Fine)
open Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel Regis.Head.Brecht
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder ContDiff
attribute [local instance] opCStarAlgebra
open Ballad Metric
variable {N:Side}(F D: PlaqAxes) (x y:Cover) (ρ k:ℝ)
local notation "Zx"=> nodeC x
local notation "M"=>SU.group
abbrev plaza (u:Cover) (F:PlaqAxes)(A:LinksC): E:= faceValue A (u,F)
def juice (u:Cover)(ρ k:ℝ)(F:PlaqAxes)(A:LinksC): ColorL:= drinkT k (ρ • SU.group.curvature (plaza u F A))
local notation "κ"=> Tower.VacuumSelection.Spine.platePin
lemma juiceNode : nodeC x∈κ F (nodeC x):=by simp [Tower.VacuumSelection.Spine.platePin,Lattice.square,Lattice.visits] -- tune ns
lemma issue (p:0<k)(t:Cover): Continuous (juice t ρ k F):= (taste_smooth (ι:=ColorL) p).continuous.comp ((continuous_const (y:=ρ)).smul (SU.group.continuous_curvature.comp (Wilson.continuous_travel (Lattice.square F.val.1 F.val.2) t))) -- masks closed
lemma proper_juice(t:Cover): LocalOn (κ F t) (juice t ρ k F):=by
 intro V W h; unfold juice; rw [show plaza t F V=plaza t F W from travel_local _ _ _ _ fun _ u v=> h _ (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)]
lemma goGauge (u:Cover) (g: Seat N→ E)(V:Pane N) : juice u ρ k F (onC N (Lattice.gauge g V))= (SU.group.adjoint (g (wrap (More N) u))) (juice u ρ k F (onC N V)):=by
 have he (V:Pane N):plaza u F (onC N V)=faceValue V (wrap (More N) u,F):=by unfold plaza faceValue onC; rw [travel_at]; simp -- tune
 unfold juice; rw [he,he,face_gauge,SU.group.curvature_conjugate, ← map_smul,taste_transform] -- argument order
variable (R:ℕ)(L:Twah.DirSpin)
def currentF : Weaver:= fun N y=> wrapCurrent x L R N (juice (nodeC x) ρ k F (onC N y.1))
lemma currentSpeak : Speak (currentF F x ρ k R L):=by
 intro N g V; unfold currentF; change wrapCurrent _ L R N (juice _ _ _ _ (onC N (gauge g V.1)))= _; rw [goGauge]; exact current_cov x L R (juice (nodeC x) ρ k F (onC N V.1)) V g -- conv
abbrev prismIndex := SU.group.ColorIndex
noncomputable def mug : Module.Basis prismIndex ℝ ColorL := (EuclideanSpace.basisFun prismIndex ℝ).toBasis -- base? check
noncomputable def scenery (i:prismIndex)(U:LinksC):ℂ:= mug.coord i (juice (nodeC x) ρ k F U)
variable {k}
lemma sceneryCoeff (p:0<k)(i:prismIndex): Coeff false (κ F Zx) ((scenery F x ρ k i)∘Prod.fst):=by
 apply Coeff.fromC; exact (Complex.continuous_ofReal.comp ((mug.coord i).continuous_of_finiteDimensional.comp (issue F ρ k p _))) -- issue tune
 intro V W h; unfold scenery; rw [proper_juice F ρ k _ _ _ h]
variable (k)
lemma scenes : currentF F x ρ k R L=∑ i:prismIndex,(hushL (scenery F x ρ k i)) * holdC x L R (mug i):=by
 funext N X; simp_rw [Finset.sum_apply,Pi.mul_apply,hushL,Algebra.smul_mul_assoc,one_mul,scenery]; let A:= juice (nodeC x) ρ k F (onC N X.1); change wrapCurrent x L R N A=_; nth_rw 1 [show A= ∑ i:prismIndex,(mug.coord i A) • mug i from (mug.sum_repr A).symm]; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul, hold_apply, RCLike.real_smul_eq_coe_smul (K:=ℂ)]; rfl
variable {k}
lemma currentLabel (p:0<k) : Voice (currentF F x ρ k R L) (κ F (nodeC x)):=by
 refine ⟨?_, currentSpeak F x ρ k R L⟩; rw [scenes]; apply Passion.weaveSum _ _; intro i _; refine (hushPass (g:=scenery F x ρ k i) (κ F (nodeC x)) ?_ ?_).spun ((holdPass x L R (mug i)).mono (singleton_subset_iff.mpr (juiceNode F x)))
 · intro X Y h; unfold scenery; rw [proper_juice F ρ k _ _ _ h] -- tune
 exact (Complex.continuous_ofReal.comp ((mug.coord i).continuous_of_finiteDimensional.comp (issue F ρ k p _)))
lemma afford_current (p:0<k) : ∃ t>(0:ℝ),∀ ρ:ℝ, amplitude t (currentF F x ρ k R L):=by
 have hp:∀ i:prismIndex,∃ t:ℝ, 0≤t ∧ ∀ ρ,∀ Z:LinksC, ‖scenery F x ρ k i Z‖≤t:=by intro i; let a: ColorL →L[ℝ] ℝ:=(mug.coord i).toContinuousLinearMap; refine ⟨‖a‖*(1+k),by positivity,fun ρ Z=> ?_⟩; unfold scenery; rw [Complex.norm_real]; exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_left (tasteB _ p) (norm_nonneg _))
 choose t ht T using hp; choose a c h using fun i:prismIndex=> (holdPass x L R (mug i)).rent; let b:=∑ i,t i*a i; have hx:0≤b:=sum_nonneg fun i _=>mul_nonneg (ht i) (c i); refine ⟨b+1,by linarith,fun ρ N Z=>?_⟩; rw [scenes,Finset.sum_apply,Finset.sum_apply]; apply le_trans (norm_sum_le ..); refine (sum_le_sum (g:=fun i=> t i*a i) (fun i _=>?_)).trans (le_of_lt (lt_add_one b)); rw [Pi.mul_apply,Pi.mul_apply,hushL,Algebra.smul_mul_assoc,one_mul,norm_smul]; exact mul_le_mul (T ..) (h ..) (norm_nonneg _) (ht i)
open Regis.Head
-- comparisons minister stamp forecast. Opponent at fixed rung: aperture always actual scale, sign origin and all faces designated.
abbrev pepperView (p:0<k):= plateView F D (nodeC x) (nodeC y) SU.group p
def tubV(p:0<k): Weaver:= panelet (pepperView F D x y p) ρ
variable (p:0<k)
include p
lemma tub_voice :Voice (tubV F D x y ρ p) (spanOf (pepperView F D x y p)):=by
 let Z:= pepperView F D x y p; refine ⟨?_, fun N=>painted_gauge Z _ N⟩
 rw [show tubV F D x y ρ p=hushL (fun i=> (Z.portrait ρ i:ℂ)) from funext fun N=> funext fun t=> paint_val ..]; apply hushPass; · exact fun a b h=> (designed Z ρ).locus ((a,1):PairsC) (b,1) h (fun _ _ _=> rfl)
 exact Complex.continuous_ofReal.comp (Z.diff.continuous.comp (continuous_pi fun i=>by fun_prop)) -- tune
lemma tub_budget : amplitude ((1+k)^2) (tubV F D x y ρ p):=by intro N X; let Z:= pepperView F D x y p; unfold tubV; rw [paint_val,norm_smul,norm_one,mul_one,Complex.norm_real]; exact Z.bound _
def bungalow (F:PlaqAxes)(x:Cover)(t:ℝ)(Z:ℝ)(U:LinksC):= SU.group.adjoint (travel U 0 (Etch.toWalk (nodeC x))) (juice (nodeC x) t Z F U)
def matchedGauge (F D:PlaqAxes)(x y:Cover)(t:ℝ)(Z:ℝ)(U:LinksC):= inner ℝ (bungalow F x t Z U) (bungalow D y t Z U)
lemma tub_appeal(U:Pane N) : Etch.portrait (pepperView F D x y p) ρ (onC N U)=matchedGauge F D x y ρ k (onC N U):=by
 let P:=pepperView F D x y p; let V:=onC N U; have hx(F:PlaqAxes)(x:Cover) : bungalow F x ρ k V= drinkT k (ρ • (colorOf F (nodeC x)).eval V):=by
    let u:=nodeC x; unfold bungalow juice; rw [←taste_transform,RG.Slot.eval]; simp [plaza,colorOf,Etch.entrust,Etch.toWalk,route_end,RG.Slot.offset,Etch.consume,map_smul] -- tune transported curve
 rw [matchedGauge,hx,hx]; rfl
lemma vacation_time(U:Fields N) : tubV F D x y ρ p N U=(matchedGauge F D x y ρ k (onC N U.1):ℂ) • 1:=by unfold tubV; rw [paint_val,tub_appeal]
end YM.CF.Hiro
#print axioms YM.CF.Hiro.currentSpeak
#print axioms YM.CF.Hiro.currentLabel
#print axioms YM.CF.Hiro.sceneryCoeff
#print axioms YM.CF.Hiro.afford_current
#print axioms YM.CF.Hiro.tub_appeal
