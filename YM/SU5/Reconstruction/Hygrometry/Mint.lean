import YM.SU5.Reconstruction.Hygrometry.Sandy
import YM.CF.Vp929.Budget.Correction
import YM.CF.BPress.Spin.Invest
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted RG Pressure Analysis
open PriceCliff RP
open scoped Classical ComplexOrder
open Wilson Skye Scree Girt Peaks Paige Vault Vale Vale.Grace Pastry
open Py Py.Rate 
variable {N m B:Side}{L:Side}{j:ℕ}{h:Odd L.val}{Y:Pricing j L h (Thread j)}{δ:ℝ}
local notation "N₀"=> CSide m B
variable (A: Grasp Y B δ)(p:Pearl A) (y:Stamped j L h Y)(u:A.roundZ ≤ (CSide m B).val)(g:0<δ)(v:1 ≤ j)
variable (T:Loom (CSide m B)) {k:ℕ}{d:ℝ}(R:Roof (CSide m B) d δ k T)(P:BudgetPoint)(D:PathData group)(Z:Clip) (θ:P.threshold ≤ d)
variable (K:Cascade.Interest (CSide m B))
variable (G': Mark (CSide m B))
namespace MeterFunding
-- prices invariant under β & path at that pose. crucial: partition may have altogether different phase.
noncomputable def eddy (T:Loom N)(F:Mark N)(p:Orbit N→ Phys N)(W:Orbit N):= letterRead (F (W.1,T W)) (p W)/ beamZ N (p W)
local notation "ℳ" β:max=> construct P D Z K β 0 0
local notation "Φ" β:max=> denZ (construct P D Z K β 0 0) A T
variable {x: Orbit (CSide m B)} (f: flags P.threshold x.1=∅)
include u f R θ
lemma magic (β:ℝ) : denZ (construct P D Z K β 0 0) A T x= Complex.exp ((ℳ β).betaL T x) • relV A K x.1:= by
 have he:(ℳ β).board x=1:=by
    unfold GramM.board; change exp (exponentL P 0 _+exponentL P 0 _) * fueled P _ _ = _; rw [still_Footprint,add_zero, NormedSpace.exp_zero,one_mul]; exact fuel_one _ _ _ f
 unfold denZ; rw [he]; have hb: IsStarProjection (spar j K.M (T x)):= (A.broadness _ u K.M).projection _ (R.paid x); change _ • acts (tank (spar j K.M (T x)) 1) _=_; rw [tank_eq _ _ hb,map_one,act_one]; rw [show T x=x.1 from Vale.Grace.Robes.solar x T R _ θ f] -- rew all incl outer warning
lemma orient (β:ℝ): eddy T G' (denZ (construct P D Z K β 0 0) A T) x=SpinPrice (relV A K x.1) (G' (x.1,x.1)):=by
 unfold eddy; rw [magic A u T R _ D Z θ K f, (letterRead _).map_smul]; unfold SpinPrice; change _*_/inner ℂ _ (_ • _)=_; rw [inner_smul_right, mul_div_mul_left _ _ (Complex.exp_ne_zero _),Vale.Grace.Robes.solar x T R _ θ f]; rfl -- shift β
lemma pureBeam (β:ℝ) : (inner ℂ (mateK N₀) ((Φ β) x)≠0) ↔ inner ℂ (mateK N₀) (relV A K x.1)≠0:= by rw [magic A u T R _ D Z θ K f, inner_smul_right]; simp [Complex.exp_ne_zero]
omit u f R θ
lemma freeze_anchor: relV A K 1= changeM (m:=m) A 1 K.M:=by unfold relV; rw [BPress.Spin.aim_zero]; simp only [Kennel.capT,mul_zero,zero_mul]; rw [show dg (0:Op (Single (CSide m B)))=0 from ?_, NormedSpace.exp_zero]; exact act_one _; ext; simp [dg,dyad]
lemma SpinPrice_berry (c:Cascade.Interest (CSide m B))(w:A.roundZ ≤ (CSide m B).val)(g:0≤δ)(v:1≤ j)(P:Pad j (CSide m B)): inner ℂ (mateK N₀) (relV A c 1)≠0:=by rw [freeze_anchor]; exact can_spend P.1 v (overhead A g w P _)
include p y u g v
variable {C:Hom.Credit}(q:Hom.InterestX C (CSide m B) K)
include q
lemma beamed {U:Pane (CSide m B)}(q':Guard U δ)(t: Skye.Seat (CSide m B)→ SU.E): inner ℂ (mateK N₀) (relV A K (Lattice.gauge t U))=inner ℂ (mateK N₀) (relV A K U):= by
 have he:= Hive.salt_g (M:=K.M) p y u v t K.P q.leanJ.1 U q'; let V' := quantU (tradew N₀ t); let φ:=acts V'.val
 change φ (relV A K U) = relV A K (Lattice.gauge t U) at he; rw [show _=_ from he.symm]; nth_rw 1 [← show φ (mateK N₀)=mateK N₀ from Girt.mastC t]; exact act_unit_inner ..
lemma spinsM {U: Pane (CSide m B)}(q':Guard U δ)(t: Skye.Seat (CSide m B)→ SU.E)(z:covariant G'):
    SpinPrice (relV A K (Lattice.gauge t U)) (G' (Lattice.gauge t U,Lattice.gauge t U))=SpinPrice (relV A K U) (G' (U,U)):=by
    unfold SpinPrice; rw [beamed A p y u g v K q q']; apply congrArg (· / _); let V' := quantU (tradew N₀ t); let φ:=acts V'.val
    rw [show relV A K (Lattice.gauge t U)= φ (relV A K U) from (Hive.salt_g p y u v t K.P q.leanJ.1 U q').symm, show G' (Lattice.gauge t U,Lattice.gauge t U)= twist V' (G' (U,U)) from z t (U,U)]; change inner ℂ _ (acts (twist V' _) (acts V'.val _))= _; rw [← Fock.swivel]; nth_rw 1 [←show φ (mateK N₀)=mateK N₀ from Girt.mastC t]; exact act_unit_inner ..
omit q p y u g v
include R θ
lemma beauty_at {W:Pane (CSide m B)}(z: flags P.threshold W= ∅) : Guard W δ := (show T (W,Classical.arbitrary _)=W from Vale.Grace.Robes.solar _ _ R _ θ z) ▸ R.paid (W,Classical.arbitrary _)
end MeterFunding
end YM.CF.Hygrometry
#print axioms YM.CF.Hygrometry.MeterFunding.orient
