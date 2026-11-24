import YM.SU5.FiniteGaugeData.Tower.Gauge
import YM.SU5.FiniteGaugeData.Tower.Pass
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Gauge acts on actual block: the one-particle map

Keep wave `Haro.SpaceM` (in particular commutes with matter at each site)
and use actual brix sum, avoiding a guard assumption in computing covariance
even at non-centered link backgrounds. All slots simultaneously. Does not
assert these reads distinguish a continuum chirality.
-/
open Fock Laurent Bloch Next.Free Fir Branch Tap Tenant Precision Drapes Vault
open Reed (Fine think)
section panel
variable {I:Type*}[Fintype I][DecidableEq I]
lemma panel_law (T V: I→Op SU.Slot){i j:I}(Q M:Op SU.Slot)(h:Q*V j=T i*M):
 (panel i j Q)*jump (Equiv.refl _) V= jump (Equiv.refl _) T * panel i j M:=by
 ext ⟨a,k⟩ ⟨c,g⟩
 simp only [Matrix.mul_apply,Fintype.sum_prod_type,jump_apply,Equiv.refl_apply,Tulip.panel,Matrix.of_apply]; by_cases ht:a=i <;> by_cases hh:c=j
 · subst a c; simp only [true_and,and_true,and_self,mul_ite,ite_mul]; simp; have hk:= Matrix.ext_iff.mpr h k g; simpa [Matrix.mul_apply,SU.Slot,Fintype.sum_prod_type] using hk
 all_goals simp [ht,hh,ite_mul,mul_ite]
end panel

section columns
variable {N P:Side}(G:Ratio N P)
variable (g: Seat P→ SU.E)
def colorField(u:Bool):Inta G→Op SU.Slot:= fun i=> (matter (g (Peaks.touch G u i))).val
def buoy(u:Bool):Op (Iota G):= jump (Equiv.refl _) (colorField G g u)
lemma placed (u:Bool):buoy G g u=((Peaks.parcel G u (1:ℝ)).run g).val:= Eq.symm (warrant ..)
lemma warp_boat: buoy G g true = foot G (tradew P g).val:= Eq.trans (placed G g true) rfl
local notation "HW" z=> buoy G g z
local notation "EW" => tradew N (Peaks.scaleG G g)
lemma drag_gauge {o:Lattice.Order}(p:Odd G.count.val)(x:Nom N P)(a b:St G.count)(z:Cover)(c:ℂ):
 drag G true false a b z c o (unionP (july G g x))*(HW false)=(HW true)*drag G true false a b z c o (unionP x):=by
 unfold drag; rw [sum_mul,mul_sum]; refine Finset.sum_congr rfl fun k _=>panel_law _ _ _ _ ?_
 let Q:= unionP x; let W:=unionP (july G g x); let A:=Peaks.touch G true (k,a); let B:=Peaks.touch G false (k+wrap N z,b); let t:=runD true false G.count a b z o; let h:= Rush.wind k z*c
 change (h • (track W.1 A t).1)* (matter (g B)).val = (matter (g A)).val * (h • (track Q.1 A t).1)
 rw [Matrix.smul_mul,Matrix.mul_smul]; apply congrArg
 change (Tulip.track (profile _) _ _).1 * _ = _ * (Tulip.track (profile _) _ _).1
 simp_rw [track_pr]
 change (matter (travel (Lattice.gauge g x.1) A t)).val * _ = _ * (matter (travel x.1 A t)).val
 rw [travel_gauge,show stop A t=B from worn G true false p a b z o k,map_mul,map_inv,map_mul]
 let U:=matter (g B)
 change (matter (g A) * matter _ * U⁻¹).val * U.val = _
 have hu:(U⁻¹).val*U.val=1:= U.property.1
 change (_ * _ * (U⁻¹).val)*U.val= _*_
 rw [mul_assoc _ _ U.val,hu,mul_one]

variable (j:ℕ)
local notation "F"=> tub (brix j G.count)
local notation "M"=>mosaic G true false F
lemma mosaic_law {R:ℕ}(l:Stencil.LaurentRadius j G.count R)(p:Odd G.count.val)(x:Nom N P): (HW true)*M (unionP x)= M (unionP (july G g x))*(HW false):=by
 unfold mosaic; rw [Matrix.smul_mul,Matrix.mul_smul,sum_mul,mul_sum]; apply congrArg; refine Finset.sum_congr rfl fun u _=>?_
 rw [Stencil.douse_sum G j l,Stencil.douse_sum G j l]; simp_rw [mul_sum,sum_mul,drag_gauge G g p]
lemma lobe_comm (a b:Bool): Peaks.lobe G a*(HW b)=(HW b)* Peaks.lobe G a:=by
 unfold buoy; rw [lobe_diag]
 ext ⟨y,k⟩ ⟨z,c⟩; rw [Matrix.diagonal_mul, Matrix.mul_diagonal]; by_cases h:y=z <;> simp [lobe_fine,jump_apply,h,mul_comm]
lemma cloaks {R:ℕ}(l:Stencil.LaurentRadius j G.count R)(p:Odd G.count.val)(A:Male)(z:Nom N P): Peaks.cloth j A G (unionP (july G g z))*(HW false)=(HW true)* Peaks.cloth j A G (unionP z):=by
 unfold Peaks.cloth; rw [add_mul,mul_add]; apply congrArg₂;
 all_goals rw [mul_assoc _ (lobe G _) (buoy G g _),lobe_comm G g, mul_assoc _ (M (unionP _)) (buoy G g _* lobe G _),←mul_assoc (M _) _ (lobe G _),←mosaic_law G g j l p,←mul_assoc (lobe G _) _ (lobe G _),←mul_assoc (lobe G _) (buoy G g true) (M (unionP z)),lobe_comm G g]; simp only [mul_assoc]
lemma coat_boat (x:Ket (Single N)): coat (patchQ G) (acts (EW).val x)=acts (HW false) (coat (patchQ G) x):=by
 rw [←coat_ret (patchQ G) x]
 rw [←act_mul,placed G g false,←level,edgeDesk,show ((Peaks.parcel G false (1:ℝ)).run g).val * endorse G 1 = endorse G (EW).val from (crest_pose G g (1:ℝ)).2, ←edgeDesk,economy,trails]
lemma fare_boat(Q:Haro.SpaceM): (EW).val*plankP N Q.val=plankP N Q.val*(EW).val:=by
 -- as in Bloom/Piper but on any periods
 let f:= love N; apply f.symm.injective; change f.symm _ = f.symm _; rw [map_mul,map_mul]; unfold plankP Tap.headW f; rw [StarAlgEquiv.symm_apply_apply,Cascade.twine]; simp only [jump_mul]; congr 1; ext1 i; rw [op_kron_mul,op_kron_mul]; simp only [one_mul,mul_one,Q.property.firm]; rfl
lemma carried(Q:Haro.SpaceM)(b:Bool):Commute (EW).val (feeL b N Q.val):=by
 letI : NormedAlgebra ℚ (Op (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ _; cases b
 · exact (Commute.exp_right (show Commute (EW).val (-(plankP N _)) from (show Commute _ _ from fare_boat G g Q).neg_right))
 exact (Commute.exp_right (show Commute (EW).val (plankP N Q.val) from fare_boat G g Q))
lemma route_color{R:ℕ}(l: Stencil.LaurentRadius j G.count R)(p:Odd G.count.val)(m:Male)(z: Nom N P)(b:Bool)(Q:Haro.SpaceM)(v:Ket (Single N)):
 byMode G j Q.val m (july G g z) b (acts (EW).val v) = acts (tradew P g).val (byMode G j Q.val m z b v):=by
 rw [byMode_eq,byMode_eq,route_foot,←warp_boat,←act_mul (feeL b N Q.val),(carried G g Q b).symm.eq,act_mul,coat_boat,←act_mul,←act_mul,cloaks G g j l p m z]

end columns
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.route_color
