import YM.SU5.Selected.Attic.Ringtones
import YM.SU5.Selected.Cuve.Plead
import YM.SU5.Selected.Lantern.Scatter
import YM.SU5.Selected.Lantern.Particle
/-! # Copy degree. Geometric budget uses F(actual) not horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy Lantern
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
open Dais.Parity
open Cuve Lantern Tender Alternative
abbrev slopeU(y:ℕ):ℕ:= 2*(5+5*y)+1 -- 211 for y=20. matches E loan.
abbrev flareU(y:ℕ) := 3*slopeU y -- 633
abbrev tideU(y:ℕ):= flareU y+3 -- 636 local. take (opaque? slopeU reduc ok)
abbrev rent' (y d:ℕ):ℝ:= footW d (slopeU y) -- t0
abbrev billX (y d:ℕ):ℝ:=footW d (flareU y+1)
abbrev scot (d:ℕ):ℝ:=footW d 5
abbrev paidX(y d:ℕ):=footW d (tideU y)
lemma foot_lead{k:ℕ}(p:0<k)(y:ℕ): footW k y∈ Set.Ioc 0 1:=by
 refine ⟨by unfold footW; positivity,pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast p))⟩
lemma destiny (d k p:ℕ): footW d (k+p)=footW d k*footW d p:=pow_add ..
lemma destiny_v (d k p:ℕ): footW d k^p=footW d (k*p):= (pow_mul ..).symm
lemma twilight {k:ℕ}(p:1≤k): Tendsto (fun d=>footW d k) atTop (𝓝 0):=by simpa only [Function.comp, footW,zero_pow (by omega:k≠0)] using ((tendsto_inv_atTop_zero (𝕜:=ℝ)).comp tendsto_natCast_atTop_atTop).pow k -- field
-- book numeric inequality for powerV etc
variable {J V R T:ℝ}{w x:ℕ}
structure Tools (U R J B Ω:ℝ)(w d:ℕ) :Prop where
  rolls : billX w d+(billX w d+footW d (tideU w+3)*R) ≤ 1/3
  fees : billX w d+footW d (tideU w+3)*R+(R*2)*(billX w d+(billX w d+footW d (tideU w+3)*R)) ≤ rent' w d ^ (3:ℕ)
  hobby : J*southern (rent' w d) (scot d) (2*R)≤ (limitO (scot d) w J)⁻¹^2 * Real.exp (-(2*(Ω+1)))
  taxAge: U*scot d^2*(4*(B*d^2))^4 ≤1
#print Tools.mk
lemma benefits(d:ℕ)(p:0<d){x y:ℕ}(u:x≤y):footW d y≤ footW d x:=pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast p)) u
-- δ,σ root
private lemma late_light (R:ℝ)(p:0<R)(w:ℕ): ∀ᶠ d:ℕ in atTop, billX w d+(billX w d+footW d (tideU w+3)*R)≤1/3 ∧ billX w d+footW d (tideU w+3)*R+(R*2)*(billX w d+(billX w d+footW d (tideU w+3)*R))≤ rent' w d ^3:=by
 let D(y:ℕ)(d:ℕ):=footW d y; let k:= flareU w
 let Y:= D (k+1); let X:= D (tideU w+3); let B:= (1+R)+(R*2*(2+R)); have he:Tendsto (fun d=> Y d+(Y d+ X d*R)) atTop (𝓝 0):=by
    have hx:Tendsto Y atTop (𝓝 0):= twilight (by omega); have hu:Tendsto X atTop (𝓝 0):= twilight (by unfold tideU; omega); simpa only [add_zero,zero_mul] using (hx.add (hx.add (hu.mul_const _)))
 have hb:Tendsto (fun d:ℕ=>B*D 1 d) atTop (𝓝 0):=by simpa only [mul_zero] using ((twilight (k:=1) (by decide)).const_mul B)
 filter_upwards [eventually_gt_atTop 0,hb.eventually (ge_mem_nhds zero_lt_one), he.eventually (ge_mem_nhds (by norm_num: (0:ℝ)<1/3))] with d p' u v; refine ⟨v,?_⟩; have hp': X d≤Y d:= benefits d p' (by change _+(1:ℕ)≤_; unfold k tideU; omega); have hg:0≤ D k d:=by unfold D footW; positivity
 have ht : Y d+(X d)*R+R*2*(Y d+(Y d+ (X d)*R)) ≤ B*Y d:=by unfold B; nlinarith only [mul_le_mul_of_nonneg_right hp' p.le,mul_le_mul_of_nonneg_right hp' (sq_nonneg R)]
 change _≤ footW d _^_; apply ht.trans; rw [show Y d= D k d*D 1 d from destiny .., destiny_v]; have h:slopeU w*3=k:= by unfold k flareU; omega
 rw [h]; nlinarith only [mul_le_mul_of_nonneg_right (show B*D 1 d≤1 from u) hg]
-- Hobby. $τ$ power billing after turf. Make smooth dealing.
private lemma hey (J₀ Ω R:ℝ)(w:ℕ)(p:1≤J₀)(g:0<R): ∀ᶠ d:ℕ in atTop, J₀*southern (rent' w d) (scot d) (2*R)≤ (limitO (scot d) w J₀)⁻¹^2 * Real.exp (-(2*(Ω+1))):=by
 let A:=Real.exp (-(2*(Ω+1))); have ht:0<J₀:= zero_lt_one.trans_le p;
 let B:= J₀*(2*R+3); let β:=J₀⁻¹^ (2:ℕ)*A; have he:0<β:=by unfold β A; positivity
 have h:Tendsto (fun d:ℕ=> B*footW d 1) atTop (𝓝 0):=by simpa only [mul_zero] using (twilight (k:=1) (by decide)).const_mul B
 filter_upwards [eventually_gt_atTop 0,h.eventually (ge_mem_nhds he)] with d k v; let t:=scot d; let s:=t^ (2*w:ℕ); have h₀:0<t:=(foot_lead k _).1
 have hf : rent' w d = s* t^ (2:ℕ) * footW d 1:=by unfold t s rent' scot t scot; rw [destiny_v,destiny_v,←destiny,←destiny]; unfold slopeU; congr 1; omega
 rw [hf]; unfold southern limitO; change J₀*((s*t^2*footW d 1)*(2*R+3)*t⁻¹^ (2:ℕ)) ≤ (t⁻¹^ w* J₀)⁻¹^ (2:ℕ) *A; have hB:t^ (2:ℕ) * t⁻¹^ (2:ℕ)=1:=by rw [←mul_pow,mul_inv_cancel₀ h₀.ne',one_pow]
 rw [show J₀*((s*t^2*_)*(2*R+3)*_)=s*(B*footW d 1) from (by unfold B; linear_combination (norm:=ring) s*(J₀*(2*R+3)*footW d 1)*hB), mul_inv, mul_pow, ←inv_pow, inv_inv, ←pow_mul]; change B*footW d 1≤ β at v; rw [show w* (2:ℕ)=2*w by omega, mul_assoc (t^(2*w)) (J₀⁻¹^ (2:ℕ))]; exact mul_le_mul_of_nonneg_left v (pow_nonneg h₀.le _)
-- geometry exponent. still have `maxW+addgapK ≤ B*d^2`.
private lemma oldAge (U B:ℝ): ∀ᶠ d:ℕ in atTop, U*scot d^2*(4*(B*d^2))^4 ≤ 1:=by
 let Y:=U*(4*B)^4; have ht:Tendsto (fun d:ℕ=> Y*footW d 2) atTop (𝓝 0):=by simpa only [mul_zero] using (twilight (k:=2) (by decide)).const_mul Y
 filter_upwards [eventually_gt_atTop 0,ht.eventually (ge_mem_nhds zero_lt_one)] with d p v; refine le_trans (le_of_eq ?_) v; unfold Y footW scot footW; field_simp
-- footEP higher-power identity $∀G costs decomposition$ later. no signed comparison slab with radius decreasing arbitrarily. requirement real width.
theorem mirabilis (U B J R Ω:ℝ)(w:ℕ)(p:0<R)(q:1≤J): ∀ᶠ d:ℕ in atTop, Tools U R J B Ω w d:=by filter_upwards [late_light R p w, hey J Ω R w q p, oldAge U B] with d ⟨v,t⟩ x' u using ⟨v,t,x',u⟩
end YM.CF.Pannier.Chancel.Attic
open YM.CF.Pannier.Chancel.Attic
#print axioms twilight
#print axioms mirabilis
#print Tools
