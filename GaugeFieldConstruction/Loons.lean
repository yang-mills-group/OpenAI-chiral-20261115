import GaugeFieldConstruction.Eco
import YM.Planned.PRIMARY_INTEGRAL_295.Bijets
import GaugeFieldConstruction.Appanage
/-!
# Spline zeros -- through two, independently on each weighted-M.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Laurent Bloch Next.Free HarmP Fir Lat Finset
open Rush Peaks Planned.PrimaryIntegral295 Exterior
open scoped Topology ContDiff Matrix InnerProductSpace BigOperators Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
namespace Thorn
open Lenten Lenten.Bank
abbrev ray (i:Plane)(z:ℝ): Momentum:= angle (z • i) -- angle ambiguity
lemma ray_Z (i:Plane):ray i 0=0:=by rw [ray,zero_smul, ang₀]
lemma ray_D (i:Plane):ContDiffAt ℝ ω (ray i) 0:= by
 apply contDiffAt_pi.mpr; intro j; exact Complex.ofRealCLM.contDiff.contDiffAt.comp (f:=fun t:ℝ=>t*i j) _ (by fun_prop)
lemma tap_P {ι:Type*}{V:ι→ℝ}{f:ι→Momentum→ℂ}(v: Moderate V f)(P:ι)(u:Plane): ContDiffAt ℝ ω (f P ∘ ray u) 0:=by
 obtain ⟨σ,C,hp,hC,h⟩:= v; have he:ContDiffAt ℂ ω (f P) (ray u 0):=by
    rw [ray_Z]; apply (PolyDisc.formOf ?_).contDiffAt; filter_upwards [(cube_open σ).mem_nhds (cube_zero σ hp)] with x g; exact (h P).hol x g
 exact he.analyticAt.restrictScalars.contDiffAt.comp 0 (ray_D _)
variable (L M:Side)(u:Odd L.val)(h:Odd M.val){l:Site L} (b:Bool) (i:Plane)
include u h
lemma arm_K (l:Site L) (a z:SpinIdx): ContDiffAt ℝ ω (fun x:ℝ=>arm b 4 L M l (ray i x) a z) 0:=by exact tap_P ((armPay b 4 (by decide) (fun _:Unit=>L) (fun _=>M) (fun _=>u) (fun _=>h) (fun _=>l)).tap a z) () i
lemma Nil_arm {l:Site L} (p:l≠0)(a z:SpinIdx): TierS (fun x:ℝ=> arm b 4 L M l (ray i x) a z) 0 0 0:=by
 let v(x:ℝ):= muff 1 L (aliasAt (ray i x) l); have he : ContDiffAt ℝ ω v 0:=tap_P (muff_pay 1 (fun _:Unit=>L) (fun _=>u) (fun _=>l)) () i;
 let F(t:ℝ):= Fir.ray b 4 L M (ray i t) l a z
 have hf : ContDiffAt ℝ ω F 0:= tap_P ((rosePay b 4 (by decide) (fun _:Unit=>L) (fun _=>M) (fun _=>u) (fun _=>h) (fun _=>l) (fun _=>p)).tap a z) () i
 let Q:= (((Real.sqrt L.val)⁻¹:ℝ):ℂ);
 have hh(t:ℝ): arm b 4 L M l (ray i t) a z=Q * (v t*(v t*(v t*(v t*F t)))):=by unfold arm; rw [if_neg p]; simp only [Matrix.smul_apply,smul_eq_mul]; unfold v muff F Q; ring
 have ht : TierS v 0 (deriv v 0) (deriv (deriv v) 0):= ⟨he.of_le le_top, by unfold v; rw [ray_Z]; exact alias_muff 1 (by decide) _ _ u p,rfl,rfl⟩
 have hZ: TierS F (F 0) (deriv F 0) (deriv (deriv F) 0):=⟨hf.of_le le_top,rfl,rfl,rfl⟩; have hx:= (TierS.const Q).mul (ht.mul (ht.mul (ht.mul (ht.mul hZ))))
 simp only [mul_zero,zero_mul,add_zero,zero_add] at hx; exact hx.equal (Eventually.of_forall fun i=> (hh i).symm)
-- pilot only deterministic
omit u h
lemma pilot_K (k:ℝ)(v:0<k)(P:Flight 4 4)(l:Site P.L)(a b:TypeFace 1): ContDiffAt ℝ ω (fun t:ℝ=>Flight.pilot k P (ray i t) l a b) 0:=by
 apply tap_P (f:=fun p: Σ P:Flight 4 4, Site P.L=> fun i=> Flight.pilot k p.1 i p.2 a b) ((secure_both _ v (j:=4) (t:=4) le_rfl le_rfl).1.pay.tap a b) (⟨P,l⟩:Σ P: Flight 4 4,Site P.L) i
lemma Pilots (k:ℝ)(v:0<k)(P:Flight 4 4){l:Site P.L}(p:l≠0) (a b:TypeFace 1):TierS (fun t:ℝ=>Flight.pilot k P (ray i t) l a b) 0 0 0:=by
 have hz:= Carrier.pilot_vanish k v P le_rfl l p a b (ray_Z _) (ray_D i)
 exact ⟨(pilot_K i k v P l a b).of_le le_top,(by simpa using hz 0 (by decide)), (by simpa using hz 1 (by decide)),(by simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hz 2 (by decide))⟩ -- tune
end Thorn
end YM.CF.TableF
end
