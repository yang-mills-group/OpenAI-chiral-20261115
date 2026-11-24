import YM.SU5.FiniteGaugeData.Chrono.Spill
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.StarOrder
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
variable (A:Repertory Y h R L a) (x:Decko Y h a)(w:Vect Y h a 0)
local notation "G" i:max=> store Y h i R L a A
local notation "V"=> Vect Y h a 0
local notation "H"=> A.space
open scoped NNReal
section
variable {H':Hilbert} (f:H'.Op) (p:0≤f)
include p
lemma power_sum (x y:ℝ≥0) : f^(↑(x+y):ℝ) = f^(x:ℝ)* f^(y:ℝ):= by
 rcases eq_zero_or_pos x with rfl|t; · rw [zero_add, NNReal.coe_zero, CFC.rpow_zero f p, one_mul]
 rcases eq_zero_or_pos y with rfl|u; · rw [add_zero,NNReal.coe_zero,CFC.rpow_zero f p, mul_one]
 have ht:0<x+y:=by positivity
 rw [← CFC.nnrpow_eq_rpow t, ← CFC.nnrpow_eq_rpow u, ← CFC.nnrpow_eq_rpow ht,CFC.nnrpow_add t u] -- include p section
lemma power_op_pos : ContinuousOn (fun x:ℝ≥0=> f^(x:ℝ)) (Set.Ioi 0):= by
 let X:=spectrum ℝ f
 let Z:=Set.Ioi (0:ℝ≥0)
 let B(t:Z): C(spectrum ℝ f, ℝ):= ⟨fun r=>(r.val) ^ (t.val:ℝ), (Real.continuous_rpow_const t.val.property).comp continuous_subtype_val⟩
 have he(t:Z) : f^(t.val:ℝ)=cfcHom (IsSelfAdjoint.of_nonneg p) (B t):= by rw [CFC.rpow_eq_cfc_real p, cfc_apply (fun r:ℝ=> r^(t.val:ℝ)) f (IsSelfAdjoint.of_nonneg p) (Real.continuous_rpow_const t.val.property|>.continuousOn)]; rfl
 apply continuousOn_iff_continuous_restrict.mpr
 rw [show Z.restrict (fun x:ℝ≥0=> f^(x:ℝ)) = (cfcHom (IsSelfAdjoint.of_nonneg p)) ∘ B from funext he]
 refine (cfcHom_continuous (IsSelfAdjoint.of_nonneg p)).comp (ContinuousMap.continuous_of_continuous_uncurry B ?_)
 exact (continuous_subtype_val.comp continuous_snd).rpow (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)) (fun t=> Or.inr t.1.property)

-- CFC on Hilbert parameter. Avoid elaborating of other positive instances on type aliases.
def anise (t:ℝ≥0) (f:H'.Op): H'.Op := f^(t:ℝ)
@[simp] lemma anise_zero : anise 0 f=1:=by unfold anise; rw [NNReal.coe_zero,CFC.rpow_zero f p]
omit p in
lemma anise_nn (t:ℝ≥0):0 ≤ anise t f:= CFC.rpow_nonneg
lemma anise_norm (c:‖f‖≤1)(t:ℝ≥0): ‖anise t f‖≤1:=by
 rcases eq_zero_or_pos t with rfl|q; · rw [anise_zero f p]; apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; rfl
 change 0<(t:ℝ) at q; rw [anise,CFC.norm_rpow _ q p]; exact Real.rpow_le_one (norm_nonneg _) c q.le
omit p in
lemma anise_free (t:ℝ≥0) (g:H'.Op) (c:Commute f g): Commute (anise t f) g := c.cfc_nnreal _
lemma anise_table (n i:ℕ)(q:0<n):anise ((i:ℝ≥0)/n) (f^n)=f^i:=by
 have hn:0<(n:ℝ):=by exact_mod_cast q
 have ht:0≤((i:ℝ≥0)/n:ℝ≥0):= bot_le
 change 0 ≤ (((i:ℝ≥0)/(n:ℝ≥0):ℝ≥0):ℝ) at ht
 unfold anise; rw [← CFC.rpow_natCast f n p, CFC.rpow_rpow_of_exponent_nonneg _ _ _ hn.le ht p]
 simp only [NNReal.coe_div,NNReal.coe_natCast]
 rw [show (n:ℝ)*_= (i:ℝ) from ?_, CFC.rpow_natCast f i p]; field_simp
end
local notation "Θ" i:max=> tock Y h i R L a a A
local notation "T" i:max => tock Y h i R L a a A 1 (fun _=>zero_le_one)
lemma thumb_nn : 0≤ T s:= (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (tock_positive Y h s R L a A _ zero_le_one)
lemma thumb_table : (Θ s) k (fun _=>Nat.cast_nonneg' k)= (T s)^k:= by
 induction k with
 | zero=> rw [pow_zero]; exact tock_zero ..
 | succ k ih => rw [pow_succ,← ih]; exact (tock_plus Y h s R L a a A k _ 1 (↑(k+1):ℤ) _ _ (by omega)).symm
abbrev tassel(Λ:Preparation) (s:ℕ):ℕ:= Λ.R.L.val^s
lemma tassel_pos : 0<tassel Λ s:= by unfold tassel; positivity
lemma thumb_scale : (T 0)=(T s)^(tassel Λ s):=by
 rw [cohere_clock Y h 0 s R L a a A 1 (fun _=>zero_le_one) (Nat.zero_le _) (fun _=>by unfold scaleR; positivity), ← thumb_table Y h s (tassel Λ s) R L a A]
 apply fun_congr_w (show scaleR Λ 0 s 1 = ↑(tassel Λ s) from by unfold scaleR tassel; push_cast; simp)
 -- avoid dependent rw across inequal proof
where fun_congr_w {aF b:ℤ}(e:aF=b){c d}: (Θ s) aF c=(Θ s) b d := by subst b; rfl -- angle binder shadows a!
-- Physical clock units = release cover `8B` GAUGE STEPS on s=0 (rather than e.g. 1 matter step); dense ticks at `tassel`. E4 `basis` use that unit ALL axes. Absolute Generator real time per that clock; reflection at cover. To use matter spacing set scale spatial same.
abbrev thetaX (Λ:Preparation)(n i:ℕ):ℝ≥0:= (i:ℝ≥0)/((tassel Λ n):ℝ≥0)
def rail (t:ℝ≥0) : A.space.Op:=anise t (tock Y h 0 R L a a A 1 (fun _=>zero_le_one))
local notation "F" => rail Y h R L a A
lemma rail_actual : (F) (thetaX Λ s k)=(Θ s) k (fun _=>Nat.cast_nonneg' _):=by
 rw [rail,thumb_scale Y h s R L a A,thumb_table]; exact anise_table (T s) (thumb_nn ..) (tassel Λ s) k (tassel_pos s)
@[simp] lemma rail_zero : (F) 0= 1:= anise_zero (T 0) (thumb_nn ..)
lemma rail_nn (t :ℝ≥0) : 0 ≤ (F) t:= anise_nn (T 0) t
lemma rail_bound (t:ℝ≥0): ‖(F) t‖ ≤ 1:= anise_norm (T 0) (thumb_nn ..) (toll_bound ..) t
lemma rail_add (t u:ℝ≥0) : (F) (t+u)=(F) t*(F) u:=power_sum (T 0) (thumb_nn ..) t u
lemma rail_free (t:ℝ≥0)(z:ℤ)(p:j=a→0≤z): Commute ((F) t) (tock Y h s R L a j A z p):= anise_free (T 0) t _ (tock_free Y h 0 s R L a a A 1 (fun _=>zero_le_one) j z p) -- need `simp only CFC.rpow_def`

lemma rail_all (v:A.space): Continuous (fun t=> (rail Y h R L a A t) v):=by
 -- use warmth for all mixed vectors dense. continuous at positive by embedding CFC; through zero true if warmed by t.
 have he (i:ℕ) (x:Decko Y h a): Continuous (fun t=> (rail Y h R L a A t) ((store Y h i R L a A) x)):=by
    obtain ⟨y,q⟩:= anticipates Y h i R L a A x; let t:=thetaX Λ (i+tic Kₜ) 1; have hv:0<t:=div_pos (by exact_mod_cast zero_lt_one) (Nat.cast_pos.mpr (tassel_pos _)); have hy:(F) t y=(G i) x:=(congrArg (fun f:A.space.Op=> f y) (rail_actual Y h (i+tic Kₜ) 1 R L a A)).trans q -- defeq Nat.cast_one
    let Q(u:ℝ≥0):= rail Y h R L a A (u+t); have hQ:Continuous Q:= (power_op_pos (T 0) (thumb_nn Y h 0 R L a A)).comp_continuous (continuous_id.add continuous_const) (fun i=> show 0 < i+t by positivity)
    suffices e: (fun u=> ((F) u) ((G i) x)) = fun u=> Q u y by rw [e]; exact (ContinuousLinearMap.apply ℂ A.space.space y).continuous.comp hQ
    exact funext fun u=> by rw [← hy]; unfold Q; rw [rail_add]; rfl
 have hx (w:Vect Y h a 0): Continuous fun t=> rail Y h R L a A t (A.paid w):=by obtain ⟨n,t⟩:= (eventual_table Y h R L a A w).exists; dsimp only at t; rw [←t]; exact he n _
 refine continuous_iff_continuousAt.mpr fun x=> Metric.tendsto_nhds.mpr fun ε hε=>?_
 obtain ⟨g,⟨k,rfl⟩,z⟩:= Metric.mem_closure_iff.mp (A.issued v) (ε/4) (by positivity); have hw(y:ℝ≥0): dist (((F) y) v) (((F) y) (A.paid k)) < ε/4:=by rw [dist_eq_norm,←map_sub]; exact lt_of_le_of_lt ((((F) y).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (rail_bound ..))) (by simpa [dist_eq_norm] using z)
 filter_upwards [Metric.tendsto_nhds.mp ((hx k).continuousAt (x:=x)).tendsto (ε/4) (by positivity)] with y v0
 have z':= dist_triangle (((F) y) v) (((F) x) (A.paid k)) (((F) x) v); have hu:= hw x; rw [dist_comm] at hu; have ht:= dist_triangle (((F) y) v) (((F) y) (A.paid k)) (((F) x) (A.paid k)); linarith [hw y]
#print axioms rail_all
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
