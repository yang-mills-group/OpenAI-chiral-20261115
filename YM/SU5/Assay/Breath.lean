import YM.SU5.Assay.Shadow
import YM.SU5.Assay.Coffee
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Unit and mixed calibration with full grid price on the actual law. To be
 used for estimator testing only, not to claim measured propagating rank
 or singularity. Unit field in a slot is the time evolution that would take
 place without an insertion there.
-/
def breath :P.Glaze:=⟨1,by decide,∅,1,one_mem _,one_mem _,BFits.empty P 1⟩
abbrev breathes (s:ℕ):P.Glaze:=let _:ℕ:=s; P.breath
lemma breath_small : Glaze.Tiny P.breathes:=by
 have h:=P.macroStep_zero
 apply h.congr; intro s; change _=((1:ℕ):ℝ)*_;rw [Nat.cast_one,one_mul]
lemma breath_grows : Glaze.Grows j P.breathes:=by
 refine ⟨1,zero_le_one,1,zero_le_one,Eventually.of_forall (fun s=>?_)⟩
 change ‖P.meanBox j s (1+1) (P.shifts j _ 1)‖≤_
 rw [map_one,one_pow,mul_one,meanBox_unit _ _ _ (show 0<(1:ℕ)+1 by decide)]
 exact P.heat_norm ..

lemma seenBox_unit (s:ℕ){w:ℕ}(p:0<w):P.seenBox j x s w 1=(U).wax (P.tock s w):=by
 rw [P.tock_when]; unfold wax; rw [Real.toNNReal_coe]
 change P.colorSpace j x _ = P.colorSpace j x (P.risesColor _ _)
 apply congrArg (P.colorSpace j x); apply Subtype.ext; apply Subtype.ext
 change (P.doorBox j s w 1).1.1= P.euclOp j _
 rw [doorBox_val s (BEntry.one P j p) (one_mem _),meanBox_unit s _ _ p]
local notation "τ"=>P.tock
def unitLag (l r:ℝ):Y:= ω (l+r)
local notation "I₀"=>P.unitLag j x
lemma unit_base (A:P.Apron)(h:A.F=1)(l r:ℝ)(v:A.realWidth P j≤l)(t:A.realWidth P j≤r):
 P.base j x A l r= I₀ l r:=by
 let q:= A.realWidth P j
 have p:0≤q:= (A.real_width_pos P j).le
 unfold base hang sand
 rw [P.engine_seen,h,map_one,P.seenBox_unit j x _ (add_pos (A.pos j) (A.pos j)),P.reprise_wax,Nat.cast_add,P.tock_add]
 change ω (l-q)*ω (q+q)*ω (r-q)=ω (l+r)
 have he:=sub_nonneg.mpr v; have ht:=sub_nonneg.mpr t; change 0≤l-q at he
 rw [wax_sq (S) he (by linarith),wax_sq (S) (by linarith) ht,
   show l-q+(q+q)+(r-q)=l+r by abel]
lemma unit_otherLag : P.otherLag j x I₀=I₀:=by
 funext l r; unfold otherLag unitLag; rw [wax_symm,add_comm]
lemma unit_normal {D:ℕ→P.Apron}(h:P.Fades D)(q:∀s,(D s).F=1): P.Normal j x D I₀:=by
 refine ⟨h,fun l v r t=> (BSOT.stay (I₀ l r)).congr' ?_⟩
 filter_upwards [h.one v j,h.one t j] with i v' t'
 exact (P.unit_base j x (D i) (q i) l r v'.le t'.le).symm
lemma breath_normal : P.Normal j x (Glaze.serial P.breathes) I₀:=
 P.unit_normal j x P.breath_small.fades (fun _=>rfl)
lemma unit_credits :(S).Credits 0 I₀:=(P.breath_normal j x).credits
lemma unit_slot (a b:ℝ)(y:Vantage):P.slot j x I₀ a b y= ω (b-a):=by
 unfold slot flown locate unitLag
 rw [show y j-a+(b-y j)=b-a by abel,P.cart_wax,mul_assoc,P.cart_splice,add_neg_cancel,P.cart_null,mul_one]
lemma unit_coffee {a b:ℝ}{F:SampleDose}(h:Walled j F a b 0)(v:F.Normalized):
 P.coffee j x I₀ a b F= (S).wax (b-a):=by
 ext1 i; rw [(h.brew (P.unit_credits j x)).drink]
 simp_rw [P.unit_slot,integral_smul_const,integral_complex_ofReal,v.2,Complex.ofReal_one,one_smul]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
