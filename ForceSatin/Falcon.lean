import ForceSatin.SunS
import YM.Next.WARD_BIN.Rays
-- along joint S far connectors; NUMBER of them fixed but lengths may grow at a height sequence. One fullLease.
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 280000
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Lattice Laurent Bloch Lat Cube Rush SU Fir Nacre Ember Scroll Tulip Tenant Cascade
open Papyrus.Granat Thera Dial Verses
open MeasureTheory RG Exterior Precision Gleam Gleam.Luster Gleam.Luster.Risa Gleam.Luster.Almanac Skye Pannier.Chancel
open Wilson Tree BPress.Spin Branch
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Pressure Gentle Solace Regis.Resonance Lull Tree
open _root_.YM.Regis.Head
local notation "G5"=>SU.group
variable {c n:Side}{r:Ratio c (More n)} {z t:ℝ}
-- finitely many rail entries for polynomial. keep adjoint/contragredient explicit
inductive Rail where
| bot : SU.Slot→SU.Slot→Rail
| top : SU.F→SU.F→Rail
| lie : SU.group.ColorIndex→SU.group.ColorIndex→Rail
| cnj : Rail→Rail
namespace Rail
abbrev f0 (i:SU.group.ColorIndex):SU.group.Color:= EuclideanSpace.single i 1
abbrev lieP (i j:SU.group.ColorIndex)(x:SU.group.El):ℝ:= SU.group.adjoint x (f0 j) i
def cost (x:E) : Rail → ℂ | bot i j=> (matter x).val i j | top i j=>fund x i j| lie i j=> lieP i j x| cnj f=> star (cost x f)
abbrev flange: ℝ:= sphereRate+ 2*SU.group.colorScale
variable (x:E) (i:Rail)
lemma flange_p:0<flange:=by unfold flange; have v:=SU.group.colorScale_pos; exact add_pos sphereRate_cost.positive (mul_pos two_pos v)
lemma high : ‖cost x i‖ ≤ 1:=by induction i with
 | bot i j=> exact (norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary (matter x).property)
 | top i j=> exact (norm_entry ..).trans_eq (CStarRing.norm_of_mem_unitary (fund_U x))
 | lie i j=> change ‖(lieP i j x:ℂ)‖≤ _; rw [Complex.norm_real]; exact (coordinateG (G:=G5) ..).trans_eq (by simp [f0])
 | cnj i h=> simpa only [cost,norm_star] using h
lemma tracking : ‖cost x i-cost 1 i‖ ≤ flange*SU.group.chord x:=by
 have he:2*SU.group.colorScale>0:=mul_pos two_pos SU.group.colorScale_pos; have ht:= sphereRate_cost.positive
 have h:= mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (a:=sphereRate) he.le) (SU.group.chord_nonneg x)
 induction i with
 | bot i j=> apply (norm_entry ((matter x).val-(matter 1).val) i j).trans; apply le_trans _ h; rw [←BPress.chord.one]; exact sphereRate_cost.bot ..
 | top i j=> apply (norm_entry (fund x-fund 1) i j).trans; apply le_trans _ h; rw [← BPress.chord.one]; exact sphereRate_cost.top ..
 | lie i j=> let R:= SU.group.adjoint x (f0 j); rw [cost,cost,←Complex.ofReal_sub,Complex.norm_real]; unfold lieP; rw [Gauge.adjoint_one]; change |(R-f0 j) i| ≤ _; apply (coordinateG (G:=G5) _ i).trans; apply (Next.Fluctuations.adjoint_norm_sub (G:=G5) ..).trans; rw [show ‖f0 j‖=(1:ℝ) from by simp [f0],mul_one]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ht.le) (SU.group.chord_nonneg x)
 | cnj j ih=> change ‖star _-star (_:ℂ)‖ ≤ _; rw [←star_sub,norm_star]; exact ih
lemma regular: Continuous (fun x:E=>cost x i):=by induction i with
 | bot i j=> exact matter_cont.matrix_elem i j
 | top i j=> exact fund_cont.matrix_elem i j
 | lie i j=> exact Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp (_root_.YM.WardBin.adjoint_cont (G:=G5))) -- tune
 | cnj j ih=> exact ih.star
end Rail
namespace Tiling
lemma step_prec (p:Step)(x:Seat n):separation x (x+p.vec)≤1:=by rw [separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]; split; rw [pdist_neg]; all_goals exact pdist_step _ -- test
variable (S: Finset (Seat n))(T:Tiling c n r)(U:T.forest.Slice SU.group)(σ:Signed)(b:Seat n)(z:ℝ) (p:0≤z) (D:Finset (Cell (More n))) {m:ℕ}(h: fullLease (broken r z (T.forest.drape U)) D (S.image (affine σ b)) r m)
include p h
lemma step_charge (x:Seat n)(l:Step)(f:x∈S):SU.group.chord (l.read (pull σ b (T.forest.drape U)) x) ≤ suitedFee r.count.val z:=by
 rw [Step.pull_read]; let V:=T.forest.drape U; let v:=affine σ b x; have h:= (h v (mem_image_of_mem (affine σ b) f)).1; let W:=l.rotate σ ; rw [show (l.rotate σ).read V _= W.read (T.wash V) v from congrArg (fun X:Pane n=>W.read X v) (T.wash_fix U).symm]; apply T.safe_chord V p h.1 (Eq.symm (h.2 _ ?_)); exact (step_prec W v).trans (by unfold hallBill Sequest; omega)
lemma connect_charge (x:Seat n)(L:Walk)(f:(visits x L).toFinset ⊆ S): SU.group.chord (travel (pull σ b (T.forest.drape U)) x L) ≤ L.length * suitedFee r.count.val z:=by
 induction L generalizing x with
 | nil=> simp [travel]
 | cons i L ih=> rw [travel]; apply (SU.group.chord_triangle ..).trans ((add_le_add (step_charge S T U σ b z p D h _ _ (f (List.mem_toFinset.mpr List.mem_cons_self))) (ih _ (fun i g=>f (List.mem_toFinset.mpr (List.mem_cons_of_mem _ (List.mem_toFinset.mp g)))))).trans_eq ?_); rw [List.length_cons]; push_cast; rw [add_mul]; ring
end Tiling
open Tiling
structure CablePrice (N:Side) where
 step : Rail
 root : Skye.Seat N
 walk : Walk
abbrev ride (x:CablePrice n)(U:Pane n):ℂ:= Rail.cost (travel U x.root x.walk) x.step
open Rail
@[simp] lemma ride_flat(x:CablePrice n): ride x 1= Rail.cost 1 x.step:=by unfold ride; rw [trivial_hike]
def quilt (x:CablePrice n): Finset (Seat n) := (visits x.root x.walk).toFinset
variable (S: Finset (Seat n))(T:Tiling c n r)(U:T.forest.Slice SU.group)(σ:Signed)(b:Seat n)(z:ℝ) (p:0≤z) (D:Finset (Cell (More n))) {m j:ℕ} (h:fullLease (broken r z (T.forest.drape U)) D (S.image (affine σ b)) r m)
variable {F:Type*}[DecidableEq F] (f:F→ CablePrice n) (W:List F)
noncomputable abbrev cadence (W:List F)(f:F→ CablePrice n)(x:Pane n):ℂ:= (W.map (fun i=>ride (f i) x)).prod
lemma carriage (x:Pane n): ‖cadence W f x‖≤1:= (Lull.low (fun i=>ride (f i) x) W zero_le_one (fun i _=>Rail.high ..)).trans (by simp)
include p h
lemma tracks (v:∀ i∈W, quilt (f i) ⊆ S)(a K:ℝ)(u:0≤ a)(u':∀ i∈W, ((f i).walk.length:ℝ) ≤ a)(b':suitedFee r.count.val z ≤ K)(pK:0≤K)(hz:W.length ≤ j): ‖cadence W f (pull σ b (T.forest.drape U))-cadence W f 1‖ ≤ (j:ℝ)* (flange*(a*K)):=by
 let V:=T.forest.drape U; let Y(u) (i:F):=ride (f i) u; let c':ℝ:=flange*(a*K); have u₂:0≤c':=mul_nonneg flange_p.le (mul_nonneg u pK)
 have hm(i)(a':i∈W): ‖Y (pull σ b V) i-Y 1 i‖≤ c':=by
    unfold Y; rw [ride_flat]; refine (tracking ..).trans (mul_le_mul_of_nonneg_left ?_ flange_p.le); let y := (f i).root; apply (connect_charge S T U σ b z p D h y _ (v i a')).trans; exact le_trans (mul_le_mul_of_nonneg_left b' (Nat.cast_nonneg _)) (mul_le_mul_of_nonneg_right (u' i a') pK)
 have he:= Lull.compareAt _ _ W (M:=1) le_rfl u₂ (fun i _=> Rail.high ..) (fun i _ => Rail.high ..) hm; rw [one_pow,mul_one] at he; exact he.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hz) u₂)
#print axioms tracks
end YM.CF.Papyrus.Franc.SatinForce
