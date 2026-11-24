import YM.CF.Vp929.Pre.Fee
import YM.CF.Vp929.Contour.Gradient
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Bake Gas Wray Larch Nor
variable {a s d δ γ:ℝ}{G H:Pax n}
variable (p:0<d)(vx:0≤a)(h':1≤h)
namespace FeeBook
variable (q:FeeBook P.B γ d){s v₀ v₁:ℝ}
local notation "Lz"=> FeeD P
local notation "VQ"=> ticket_f P.B γ d
variable (ha:0<s)(pb:s≤1)
lemma MonoQ_join {b:ℝ}(T:MonoQ P h b G v)(T':MonoQ P h b H v) : Both (fun x=>MonoQ P h b x v) (Pair.cat G H):= by
 have hv:(2:ℝ)⁻¹*(v+v)=v:= by ring
 have hp:= (T.sub T').scale ((2*Complex.I)⁻¹); have h0:= (T.add T').scale (2:ℂ)⁻¹; rw [norm_inv,norm_mul,Complex.norm_I,mul_one,show ‖(2:ℂ)‖=(2:ℝ) from by norm_num,hv] at hp; rw [norm_inv,show ‖(2:ℂ)‖=(2:ℝ) from by norm_num,hv] at h0; exact ⟨h0,hp⟩
-- mean value interpolation between the two (unprojected real forms); the FeeD estimate gain s from the extended activity radius. Can take s of class even S_* here.
include ha pb h' vx q
lemma comparison (p₁:MonoQ P h (a+d) H (γ/2)) (p₂:MonoQ P h (a+d) (G-H) (s*γ/10)):
 MonoQ P h a (FeeD P G -FeeD P H) (2*VQ*s):= by
 let S:=Metric.ball (0:ℂ) 4
 let Gz(z:ℂ):= H+(z*((s⁻¹):ℝ):ℂ) • (G-H)
 have hG (z:ℂ)(p:z∈S): MonoQ P h (a+d) (Gz z) γ:=by
    apply (p₁.add (p₂.scale (z * ((s⁻¹):ℝ):ℂ))).purse; have hz:= mem_ball_zero_iff.mp p; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]; have he: ‖z‖ < 4:= hz; rw [show ‖z‖ * s⁻¹ * (s*γ/10)= ‖z‖ * (γ/10) from by field_simp]; nlinarith [q.coal]
 let F(z:ℂ):= Pair.cat ((Lz) (Gz z)) ((Lz) (Gz (star z)))
 have hu(u:ℂ)(p:u∈ S): star u∈ S:= mem_ball_zero_iff.mpr (by simpa only [norm_star] using mem_ball_zero_iff.mp p)
 have he z p: Both (fun x=> MonoQ P h a x VQ) (F z) := MonoQ_join (q.fee vx h' (hG z p)) (q.fee vx h' (hG _ (hu z p)))
 let z:ℂ:= s
 have hx': z∈ball (0:ℂ) 2:= mem_ball_zero_iff.mpr (by unfold z; rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]; linarith)
 have h0': (0:ℂ)∈ball (0:ℂ) 2:= mem_ball_self zero_lt_two
 let B: ball (0:ℂ) 2 ⊆ S:= ball_subset_ball (by norm_num: (2:ℝ) ≤ 4)
 have hP(i:Aura n)(U:Orbit n) :DifferentiableOn ℂ (fun z=> FeeD P (Gz z) i U) S:= by
    refine q.analytic vx h' isOpen_ball Gz hG ?_ i U; intro i U
    exact (differentiableOn_const (H i U)).add (((differentiableOn_id.mul_const (((s⁻¹):ℝ):ℂ))).smul (differentiableOn_const ((G-H) i U)))
 have hc : Census S F:= fun i U=> holo_cat (hP i U) (by
    apply DifferentiableOn.congr ((hP i U).mono fun z x=>?_ ); · intro z p; exact congrArg (fun z=>FeeD P (Gz z) i U) (star_star z)
    exact star_star z ▸ hu _ x)
 have u:Both (Enough (MonoQ P h a)) (F z-F 0):= ⟨⟨_,MonoQ.sub (he z (B hx')).1 (he 0 (B h0')).1⟩,⟨_,MonoQ.sub (he z (B hx')).2 (he 0 (B h0')).2⟩⟩
 have hz:Gz z= G:=by unfold z Gz;  rw [←Complex.ofReal_mul,mul_inv_cancel₀ ha.ne',Complex.ofReal_one,one_smul]; abel

 have hp0:Gz 0= H:=by unfold Gz; simp
 have hw: F z=(FeeD P G,0) ∧ F 0=(FeeD P H,0):=by
    have he:star z=z:= by change (starRingEnd ℂ) (s:ℂ) = (s:ℂ); simp
    rw [show F z = Pair.cat _ _ from rfl,show F 0=Pair.cat _ _ from rfl, he, hz,star_zero,hp0]
    constructor <;> apply Pair.ext_pm <;> simp only [Pair.plus_cat,Pair.minus_cat] <;> simp [Pair.plus,Pair.minus]
 let hv:= ((MonoQ.Team (n:=n) h' vx).gradient hc he u hx' h0' (t:=2) (w:=1) (by norm_num) zero_lt_one).1; change MonoQ P h a _ _ at hv; rw [hw.1,hw.2,sub_zero, (by rfl:z=(s:ℂ)), Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha] at hv;
 simpa only [div_one,Prod.fst_sub] using hv
end FeeBook
end YM.CF.Py.Rate
