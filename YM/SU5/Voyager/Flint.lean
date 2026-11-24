import YM.SU5.Voyager.Orchard
/-! # Radial marks on spectral. DFT of spatial difference. -/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Orbit
open Function Filter Set Metric NormedSpace Complex MeasureTheory Measure
open Boundary Boundary.Probe Caino
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators
variable {X:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X] {H:Hilbert}
variable (T:Orbit H X)(P:PVM H X)(p z:X)(x:H)
local notation "V"=> T.translation
lemma playAngle (x y:H): inner ℂ (V p x) (V p y)=inner ℂ x y:= LinearIsometry.inner_map_map (𝕜:=ℂ) (show H.space →ₗᵢ[ℂ] H.space from { (V p).toLinearMap with norm_map':=T.unitary p}) x y
local notation "μ" y:max=> P.diagonal y
def mallet (p x:X):= ‖plane x p-1‖^2
lemma mallet_p(t:X):0 ≤ mallet p t:=sq_nonneg _
lemma mallet_budget (y:X): mallet p y ≤ 2^2:= pow_le_pow_left₀ (by positivity) (b:=2) ((norm_sub_le ..).trans (by rw [plane_norm,norm_one]; norm_num)) _
lemma mallet_t : Continuous (mallet p):= by unfold mallet plane; fun_prop
lemma starsA : star (plane z p)*(plane z p)=1 :=by rw [←plane_inverse,← plane_add,neg_add_cancel,plane_zero]
lemma mallet_color : (↑(mallet p z):ℂ)= (1+1)-plane z p-plane z (-p):=by
 let y:= plane z p; rw [plane_inverse]; have he(t:ℂ): conj t*t=↑(‖t‖^2):=by rw [Complex.sq_norm, mul_comm, mul_conj]
 change ((‖plane z p-1‖^2:ℝ):ℂ) = _; rw [←he]; change (star (y-1))*(y-1)=_-y-star y; rw [star_sub,star_one,mul_sub,sub_mul, starsA,mul_one,one_mul]; ring -- `sub_mul`
variable (h:T.Spectrum P)
include h
lemma windMarker : μ (V p x-x)= chisels (mallet p) (μ x):=by
 let ν:= chisels (mallet p) (μ x); have hw:Integrable (mallet p) (μ x):=(integrable_const (c:=(2:ℝ)^2)).mono' ((mallet_t p).aestronglyMeasurable) (ae_of_all _ fun x=>by rw [Real.norm_eq_abs,abs_of_nonneg (mallet_p ..)]; exact mallet_budget ..)
 letI : IsFiniteMeasure ν:=isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable hw.1 (ae_of_all _ fun x=>mallet_p p x)).2 hw)
 change _=ν; apply Measure.ext_of_charFun; funext A
 let k:= V p x; let g(b:X):= charFun (P.diagonal x) b; have hx(a b:X)(u:H): V a (V b u)=V (a+b) u:=DFunLike.congr_fun (T.sends a b) u
 have he: inner ℂ k (V A k) = g A:=by unfold g; rw [h]; unfold k; rw [hx,add_comm A,← hx]; exact playAngle ..
 have ht: inner ℂ k (V A x)= g ((-p)+A):= by unfold g; rw [h]; refine (congrArg (inner ℂ k) (show V p (V (-p+A) x)=V A x from (by rw [hx,add_neg_cancel_left])).symm).trans (playAngle ..)
 have hV(q:X): Integrable (fun y=>plane y q) (μ x):=(integrable_const (c:=(1:ℝ))).mono' (by unfold plane; fun_prop) (ae_of_all _ fun x=> (plane_norm ..).le)
 have hi(y:X):(↑(mallet p y):ℂ)*plane y A = plane y A - plane y (A+p)-plane y (-p+A)+ plane y A:=by rw [mallet_color,plane_add,plane_add]; ring
 rw [h, map_sub,inner_sub_left,inner_sub_right,inner_sub_right]; change _=∫ y,plane y A ∂ν; rw [show (∫ y,plane y A ∂ν) = _ from carves (μ x) (mallet p) ((mallet_t p).measurable) (mallet_p p) (fun y=>plane y A)]; change _= ∫ y,(↑(mallet p y):ℂ)*plane y A ∂(P.diagonal x); simp_rw [hi]; have u:Integrable (fun y=>plane y A-plane y (A+p)) (μ x):=(hV ..).sub (hV ..); have v:Integrable (fun y=>plane y A-plane y (A+p)-plane y (-p+A)) (μ x):= u.sub (hV ..); rw [integral_add v (hV A),integral_sub u (hV (-p+A)), integral_sub (hV A) (hV (A+p))]
 change inner ℂ k (V A k) - inner ℂ k (V A x) -(inner ℂ x (V A k)-inner ℂ x (V A x))=g A-g (A+p)-g (-p+A)+g A; rw [he,ht,show inner ℂ x (V A k)=g (A+p) from (by unfold k g; rw [hx,h]),show inner ℂ x (V A x) = g A from (h ..).symm]; ring
end YM.Spectral.Orbit
#print axioms YM.Spectral.Orbit.windMarker
