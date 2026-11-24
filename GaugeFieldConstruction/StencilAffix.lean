import YM.SU5.Assay.Base
import YM.SU5.Assay.SandCup
/-!
# Four auxiliary comparisons for stamp-growth. Compiles independently of Chron. No predicates on static asymptotics assumed.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 400000
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
variable (P:Spine)(i:Axis)(x:P.Spectrum0 i)
local notation "T₀" => P.seasons i x
lemma neutralStampSt (g:ℕ→Vantage)(e:Tendsto g atTop (𝓝 0))
    (K:ℕ→ P.Apron)(T:ℝ→ℝ→(P.ManyF i x).Op)(c:ℕ→ℂ)(w: (T₀).Credits 0 T)
    (u:Tendsto (fun t=> (K t).realWidth P i) atTop (𝓝 0))
    (hz:∀ l r:ℝ,0<l→0<r→BSOT (fun t=> c t • P.locate i x (-g t) (P.base i x (K t) (l - g t i) (r + g t i))) atTop (T l r))
    {l r:ℝ}{α β:ℕ→ℝ}(hv:0<l)(hk:0<r)(a:Tendsto α atTop (𝓝 l))(b:Tendsto β atTop (𝓝 r)):
 BSOT (fun t=> c t • P.base i x (K t) (α t) (β t)) atTop (T l r):=by
 have hk': Tendsto (fun t=>g t i) atTop (𝓝 0):= ((continuous_apply i).tendsto (0:Vantage)).comp e
 let u':=l/2; let v':=r/2; let X(v:ℕ):= u'-g v i; let Y(v:ℕ):= v'+g v i; let V(t:ℕ):= c t • P.locate i x (-g t) (P.base i x (K t) (X t) (Y t)); have hU:0<u':=half_pos hv; have hT:0<v':=half_pos hk; have hx:u'<l:=half_lt_self hv; have hs:v'<r:=half_lt_self hk
 have heX:Tendsto X atTop (𝓝 u'):= by simpa [X] using hk'.const_sub u'
 have heY:Tendsto Y atTop (𝓝 v'):= by simpa [Y] using hk'.const_add v'
 let F(k:ℕ):= P.locate i x (g k) (V k); have hF:BSOT F atTop (T u' v'):=by have t:=P.locate_limit i x e (hz u' v' hU hT); rw [P.locate_zero] at t; exact t
 rw [w hU hT hx.le hs.le]
 refine BSOT.congr' ((T₀).sand_limit hF (a.sub heX) (b.sub heY)) ?_
 filter_upwards [Filter.Tendsto.eventually_lt heX a hx,Filter.Tendsto.eventually_lt heY b hs, Filter.Tendsto.eventually_lt u heX hU,Filter.Tendsto.eventually_lt u heY hT] with t p b q pT
 have hv:F t=c t • P.base i x (K t) (X t) (Y t):=by unfold F V; rw[P.locate_smul,P.locate_sum,add_neg_cancel,P.locate_zero]
 change _root_.YM.OS.Semigroup.sand _ (F t) (α t-X t) (β t-Y t)=_; rw[hv,P.base_step i x (K t) q.le pT.le p.le b.le]; exact (OS.Semigroup.sand_smul ..)
open Submodule
section Finite
variable {V I:Type*}{W:Type*}[AddCommGroup V][Module ℂ V][FiniteDimensional ℂ V][AddCommGroup W] [Module ℂ W] [TopologicalSpace W][IsTopologicalAddGroup W][T2Space W][ContinuousSMul ℂ W]
  (κ:V→ₗ[ℂ] W)(K:ℕ→V)(Γ:W)(t:Tendsto (fun i=> κ (K i)) atTop (𝓝 Γ)) (Z:Type*) [NormedAddCommGroup Z][NormedSpace ℂ Z]
include t
-- no topology on frame V; J here arbitrary in arbitrary target normed space Z.
lemma stampPocketSt : ∃ z:V, κ z=Γ:=by
 letI: FiniteDimensional ℂ (LinearMap.range κ):= Module.Finite.range _
 obtain ⟨z,hz⟩:= (LinearMap.range κ).closed_of_finiteDimensional.mem_of_tendsto t (Eventually.of_forall fun _=> LinearMap.mem_range_self κ _)
 exact ⟨z,hz⟩
lemma stampRefundSt (z:V)(hz:κ z=Γ)(u:∀ x,κ x=0→ x=0)(J:V→ₗ[ℂ] Z) : Tendsto (fun i=> J (K i)) atTop (𝓝 (J z)):=by
 letI: FiniteDimensional ℂ (LinearMap.range κ):= Module.Finite.range _
 have hi: LinearMap.ker κ = ⊥:= LinearMap.ker_eq_bot'.mpr u
 let X:= LinearEquiv.ofInjective κ (LinearMap.ker_eq_bot.mp hi); have he(s): X.symm (κ.rangeRestrict s)=s:= X.symm_apply_apply _
 let U:= J ∘ₗ X.symm.toLinearMap
 rw [← hz] at t; have hF':Tendsto (fun i=> κ.rangeRestrict (K i)) atTop (𝓝 (κ.rangeRestrict z)):= (tendsto_subtype_rng ..).2 t
 have h:= (U.continuous_of_finiteDimensional.tendsto _).comp hF'; simp_rw [Function.comp_def,U,LinearMap.comp_apply,LinearEquiv.coe_coe,he] at h; exact h
end Finite
noncomputable abbrev rentaSt (L:ℝ) := L^((3:ℝ)+(↑(0:ℕ):ℝ)+19/20)
lemma birthMeterSt (L x:ℝ)(h:1≤ L)(g:1≤ x)(w: 4*x * L^(15/8:ℝ)≤ L^(79/16:ℝ)): 0<x*(rentaSt L)⁻¹ ∧ x*(rentaSt L)⁻¹ < 1:=by
 have hx:0<L:=zero_lt_one.trans_le h; have hp:0<rentaSt L:= Real.rpow_pos_of_pos hx _; have hV:0<x:=zero_lt_one.trans_le g
 have hz:0<L^(15/8:ℝ):=Real.rpow_pos_of_pos hx _
 have he : L^(79/16:ℝ) ≤ rentaSt L * L^(15/8:ℝ):=by unfold rentaSt; rw [←Real.rpow_add hx]; exact Real.rpow_le_rpow_of_exponent_le h (by norm_num)
 refine ⟨mul_pos hV (inv_pos.mpr hp),?_⟩; rw [← div_eq_mul_inv, div_lt_one hp]; exact (by linarith : x < 4*x).trans_le (le_of_mul_le_mul_right (w.trans he) hz)
lemma overheadSTENDHAL {X:Type*} [NormedAddCommGroup X][NormedSpace ℝ X](f:X→L[ℝ] ℂ)(U:ℕ→X)(A:ℝ)
    (Δ L y H:ℝ)(hH:0<H)(p:0<L)(u:0<L*Δ)(w: L*Δ < 1) (k:ℕ)(v:ℕ→ℝ)(e:0<v k)(q:∀ᶠ s in atTop, 0<v s)
    (h:∀ᶠ s in atTop,‖U s‖≤L^s*A): Tendsto (fun s:ℕ=>‖((↑(v s/H^2):ℂ)*f (U s))‖*(y*(v k*Δ^(s-k)/v s))) atTop (𝓝 0):=by
 have hm:0 < Δ:= pos_of_mul_pos_right u p.le
 let X':=L * Δ; let d:=|y| * v k* (‖f‖*A)/H^2 * (Δ^k)⁻¹; have ha:Tendsto (fun i:ℕ=> X'^i*d) atTop (𝓝 0):=by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one u.le w).mul_const d
 rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) ?_ ha; filter_upwards [eventually_ge_atTop k,h,q] with s a h' t
 let C:=v s/H^2; let Lz:= v k * Δ^(s-k) / v s
 have hZ:0 < Lz:= div_pos (mul_pos e (pow_pos hm _)) t; have hC:0<C:=div_pos t (pow_pos hH _)
 change ‖‖(↑C:ℂ)* f (U s)‖*(y*Lz)‖ ≤ _; rw [norm_mul,norm_mul (↑C:ℂ), Complex.norm_real,Real.norm_of_nonneg hC.le, Real.norm_of_nonneg (mul_nonneg hC.le (norm_nonneg _)), norm_mul,Real.norm_eq_abs y,Real.norm_of_nonneg hZ.le]
 calc
    _ ≤ C*(‖f‖*(L^s*A))*(|y| * Lz):=by gcongr; exact (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left h' (norm_nonneg _))
    _ = _:=by unfold X' Lz d C; rw [pow_sub₀ (Δ) hm.ne' a, mul_pow L]; field_simp
#print axioms neutralStampSt
#print axioms stampRefundSt
#print axioms overheadSTENDHAL
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
