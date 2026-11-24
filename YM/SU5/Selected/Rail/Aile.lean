import YM.SU5.Selected.Rail.Fret
import YM.SU5.Selected.Airy.Approve
import YM.SU5.FiniteGaugeData.Signal.Platinum
/-! # Kernel with high order contact. In same AP radian units. Use disk, not determinant.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Crest.Rail
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Airy Fock Topology
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
local notation "I"=>Complex.I
local notation "φ" => 2*π
attribute [local instance] opCStarAlgebra
abbrev Maj:= Jill.Male
local notation "A"=> Aop
def stemGuard:= closedBall (0:Bin) π
variable {x:Bin}(h:x∈stemGuard)(M:Maj)
local notation "Kp"=> bar 4
local notation "Mp"=> mixL 4
def wagon (M:Maj)(x:Bin):Op SpinIdx:= (1-zen (Mp M.val (tmap x)))*A
abbrev finale(x:Bin) :Op SpinIdx:= (1-zen (tough x))*A
lemma stemG:x∈ stemGuard ↔ Bound π x:=by simp [stemGuard,Bound]
def vlow := (Jill.zip (by omega : 1≤4)).choose -- rho
lemma vpay: 0< vlow:=(Jill.zip (by omega : 1≤4)).choose_spec.choose_spec.1
include h
lemma gentil (t:x≠0): tmap x≠0:= by
 contrapose! t; funext i; apply Complex.ofReal_injective; change (x i:ℂ)= ((0:ℝ):ℂ); exact congrFun t i -- tmap binder definitional?
lemma disk_price : vlow*‖x‖^2 ≤ disk 4 M x:= ((Jill.zip (by omega : 1≤4)).choose_spec.choose_spec.2.2 M x (stemG.mp h)).1
lemma disk_crest (t:x≠0) :0<disk 4 M x:= (mul_pos vpay (pow_pos (norm_pos_iff.mpr t) _)).trans_le (disk_price h M)
lemma siege : IsStarProjection (Kp M.val (tmap x)):= CF.Signal.Sparkle.Retain.bright0 M (stemG.mp h) -- yes
private lemma terrainK : tmap x∈realCube zone:= base_subset_realCube zone_pos (b_base (stemG.mp h))
lemma wage(t:x≠0): (disk 4 M x:ℂ) • wagon M x = Kp M.val (tmap x)*A:=by
 let Z:= zen (Mp M.val (tmap x)); let f:=disk 4 M x; have h':Kp M.val (tmap x)=(f:ℂ) • ((1-Z)*A*(1+Z)):= (express 4 x M.val (terrainK h) M.property) ▸ (bar_full 4 M.val (terrainK h) (gentil h t) (graphs_ne (phys_mix 4 M.val M.property _ (terrainK h).1))).1
 have hz:A * ((1:Op SpinIdx)+ Z)*A=A:= by rw [mul_add,mul_one,add_mul,AOne,zenA,mul_assoc,sub_mul,one_mul,AOne,sub_self,mul_zero,add_zero]
 unfold wagon; rw [h',Matrix.smul_mul]; change (f:ℂ) • _= _; simp_rw [show ((1-Z)*A*(1+Z))*A=(1-Z)*(A*(1+Z)*A) by simp [mul_assoc],hz]; rfl
lemma disk_wagon (t:x≠0): vlow * ‖x‖^2 * ‖wagon M x‖ ≤ 1 := by
 refine le_trans (mul_le_mul_of_nonneg_right (disk_price h M) (norm_nonneg _)) ?_
 have ht:IsStarProjection A:=⟨AOne,Aadj⟩; rw [← Complex.norm_of_nonneg (disk_crest h M t).le, ← norm_smul, wage h _ t]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((siege h M).norm_le _)).trans (ht.norm_le _)) -- `←Complex.norm`; tune
-- multipliers by $(1-e^it)^K$
omit h M
def fade (t:ℝ):ℂ:=1-surge 1 t
def fleece (k:ℕ)(x:Bin):ℂ:= (fade (x 3))^k
@[fun_prop] lemma fade_c:Continuous fade:=by unfold fade surge; fun_prop
@[simp] lemma fade_z: fade 0=0:=by simp [fade,surge]
lemma poetics (t:ℝ) : ‖fade t‖≤ |t|:=by
 unfold fade surge; rw [one_mul,norm_sub_rev,Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]; norm_num; have ht: |(t/2)|= |t|/2:= by rw [abs_div, abs_of_pos (by norm_num: 0 < (2:ℝ))]
 linarith only [ht,(Real.abs_sin_le_abs (x:= t/2))] -- scope tune
@[fun_prop] lemma fleece_c (k:ℕ): Continuous (fleece k):=by unfold fleece; have e:=fade_c; fun_prop
lemma fleece_m (k:ℕ): ‖fleece k x‖ ≤ ‖x‖^k:= by unfold fleece; rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) ((poetics _).trans (norm_le_pi_norm x 3)) _
lemma arc_plain (k:ℕ)(F:Op SpinIdx)(H:vlow*‖x‖^2*‖F‖ ≤1): ‖fleece (k+2) x • F‖≤ vlow⁻¹* ‖x‖^k:=by
 rw [norm_smul]; apply (mul_le_mul_of_nonneg_right (fleece_m _) (norm_nonneg _)).trans; rw [pow_add,mul_comm vlow⁻¹,←div_eq_mul_inv]; apply (le_div_iff₀ vpay).mpr; nlinarith only [mul_le_mul_of_nonneg_left H (show 0≤‖x‖^k by positivity)] -- direction?
-- tune
include h
lemma imports {ι:Type*} {l: Filter ι}{W:ι→Jill.Male}{X:ι→Bin} (t:x≠0) (p:Tendsto W l mtn)(j:Tendsto X l (𝓝[stemGuard] x)): Tendsto (fun i=>wagon (W i) (X i)) l (𝓝 (finale x)):=by
 let G(i:ι):= Mp (W i).val (tmap (X i)); have he: Tendsto G l (𝓝 (tough x)):=by
    have hw:Continuous tmap:=by unfold tmap; fun_prop
    apply tendsto_pi_nhds.mpr; intro u; apply gulch (M':=Subtype.val ∘ W) ((tendsto_comap).comp p) (((hw.continuousOn (s:=stemGuard) x h).tendsto).comp j) (Filter.Eventually.of_forall (fun i=> (W i).property)) (stemG.mp h) t u; filter_upwards [j.eventually eventually_mem_nhdsWithin] with i h; exact b_base (stemG.mp h)
 let f(p:Momentum): Op SpinIdx:=(1-zen p)*A; have hv:Continuous f:= (continuous_const.sub zen_c).matrix_mul continuous_const; exact (hv.tendsto _).comp he -- needs additive ops matrix
-- mtn neBot
private def metro (i:ℕ):Maj:=⟨⟨2*i+1,by omega⟩, i,rfl⟩ -- obtain Odd.side
omit h
lemma metro_run:Tendsto metro atTop mtn:= tendsto_comap_iff.mpr (tendsto_atTop.mpr fun (i:Side)=> (eventually_ge_atTop i.val).mono (fun j p=> show i.val ≤ 2*j+1 from by omega))
include h
lemma moving(t:x≠0): vlow * ‖x‖^2* ‖finale x‖≤1 := by
 have ht:= imports (x:=x) h t metro_run (tendsto_const_nhdsWithin h)
 exact le_of_tendsto' (ht.norm.const_mul _) (fun i=> disk_wagon h _ t) -- name
end YM.CF.Crest.Rail
open YM.CF.Crest.Rail
#print axioms wage
#print axioms moving
#print axioms arc_plain
#print axioms fleece_m
