import YM.SU5.Voyager.Sail
import YM.SU5.Voyager.Blades
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable {a j:Axis}{P: Spine} (x:P.Spectrum0 a)
open Aria Set TopologicalSpace Metric Casting
local notation "χ[" k "]"=> P.advocate a x k
local notation "H[" k "]"=> P.ManyF k χ[k]
local notation "Ω[" k "]"=> P.heaven k χ[k]
local notation "Ψ[" k "]"=> P.seasons k χ[k]
local notation "ω[" k "]"=> P.colorZero k χ[k]
local notation "W[" k "]"=>P.cartage k χ[k]
local notation "E[" k "]"=>(Ψ[k]).E
local notation "V[" k "]"=>P.tableau k χ[k]
variable (j) (k:Axis)
open OS.Semigroup.Burst
local notation "F₀"=> Flicker P
local notation "φ"=> specY x j
local notation "λ₁"=> (Ψ[j])
variable (J:P.Ellis a x)(h:k≠j)(t p:ℝ≥0)(u y:Vantage)
def fair : (P.ManyF j χ[j]).Op:= E[j] t * W[j] u
lemma fair_pay : ‖fair j x t u‖ ≤ 1:= by unfold fair; refine (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left (P.cart_pay j χ[j] _) (norm_nonneg (E[j] t))).trans ?_); rw [mul_one]; apply OS.Semigroup.shrinks
lemma fair_slot : star (fair j x t u) = fair j x t (-u) := by
 unfold fair; rw [star_mul,cart_adj,show star (E[j] t)=E[j] t from (λ₁).sym t,(delta_shadow j x (-u) t).eq.symm]
lemma fair_star (z v:H[j]): star (inner ℂ z (fair j x t u v)) = inner ℂ v (fair j x t (-u) z):=by rw [← fair_slot j x t u]; exact (inner_conj_symm (𝕜:=ℂ) (x:=(fair j x t u v)) (y:=z)).trans (ContinuousLinearMap.adjoint_inner_right ..).symm -- args
lemma farFlip (z v:H[j]): ‖inner ℂ z (fair j x t u v)‖= ‖inner ℂ v (fair j x t (-u) z)‖:=by rw [← fair_star,norm_star]
local notation "Δ"=> deltaMove j x
local notation "ρ"=> aislePt k (p:ℝ)
local notation "g[" B "," D "]"=> (Apron.realWidth P (Prod.fst B) k+Apron.realWidth P (Prod.fst D) k)
local notation "C[" F "," B "]"=> (‖glareY x (Apron.kiss P j (Prod.fst F)) k‖ * ‖flashY x (Prod.fst B) k‖)
lemma fair_delta(z v:H[j]): inner ℂ z (fair j x t u (Δ y v)) = inner ℂ z (fair j x t (u+y) v)-inner ℂ z (fair j x t u v):= (delta_sum ..).symm -- tune
include J h
lemma annual (F B:F₀) (g:g[F,B]<u k) : ‖inner ℂ (φ F) (fair j x t u (Δ ρ (φ B)))‖ ≤ C[F,B]*(2*(p:ℝ)/(u k-g[F,B])):=by
 have he:=earn j x k u J t p 1 h F B g; simp only [pow_one,quality, Nat.cast_one,mul_one] at he; exact he
lemma centennial (F B:F₀)(g:g[B,F]+(p:ℝ)< -u k): ‖inner ℂ (φ F) (fair j x t u (Δ ρ (φ B)))‖ ≤ C[B,F]*(2*(p:ℝ)/(-(u k+(p:ℝ))-g[B,F])):=by
 let q:=-u-ρ; have hp: -(u+ρ)=q:=by unfold q; abel
 have ht:q k=(-u k)-(p:ℝ):=by simp [q,aislePt]
 have hg:g[B,F]<q k:=by rw [ht]; linarith
 rw [fair_delta, ← norm_star]; rw [star_sub,fair_star,fair_star,hp,norm_sub_rev, show inner ℂ (φ B) (fair j x t (-u) (φ F)) = inner ℂ (φ B) (fair j x t (q+ρ) (φ F)) from (by rw [show q+ρ=-u from sub_add_cancel ..]),←fair_delta]
 exact (annual j x k J h t p q B F hg).trans_eq (by rw [ht, show (-u k)-(p:ℝ)=-(u k+(p:ℝ)) from (by ring)])
-- uniform even with t varying
lemma earnsFare (F B:F₀)(v:ℝ)(hv:0< v): ∀ᶠ n:ℝ in atTop,∀ (T:ℝ≥0)(r:Vantage), n ≤ |r k| → ‖inner ℂ (φ F) (fair j x T r (Δ ρ (φ B)))‖< v:=by
 let G:=g[B,F]; have he:G=g[F,B]:= add_comm ..; let Q:ℝ:=p; let C:= (C[B,F]+C[F,B]); let m:=(C*(2*Q)+1)/v; have hm:0 < m:=by positivity
 filter_upwards [eventually_ge_atTop ((G+Q)+m)] with n hq; intro T r hr; have hle: (G+Q)+m ≤ |r k|:= hq.trans hr
 have ht:0 ≤ Q:=p.property; have hc:0 ≤ C:=(by positivity); have hx: v*m=C*(2*Q)+1:=by unfold m; field_simp
 by_cases l:0≤r k
 · rw [abs_of_nonneg l] at hle; have hp:m ≤ r k-G:=(by linarith); have hu:0< r k-G:=hm.trans_le hp; have hu':0< r k-g[F,B]:= he ▸ hu
   refine (annual j x k J h T p r F B (by linarith)).trans_lt ((mul_le_mul_of_nonneg_right (show C[F,B]≤ C from le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (show 0 ≤ 2*(p:ℝ)/(r k-g[F,B]) from div_nonneg (by positivity) hu'.le)).trans_lt ?_)
   rw [← he, ← mul_div_assoc, div_lt_iff₀ hu]; change C*(2*Q)<_; linarith [mul_le_mul_of_nonneg_left hp hv.le]
 rw [abs_of_nonpos (le_of_not_ge l)] at hle; have hp:m ≤ -(r k+Q)-G:=(by linarith); have hu:0< -(r k+Q)-G:=hm.trans_le hp; have he':0< -(r k+(p:ℝ))-g[B,F]:=hu
 refine (centennial j x k J h T p r F B (by linarith)).trans_lt ((mul_le_mul_of_nonneg_right (show C[B,F]≤ C from le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (show 0 ≤ 2*(p:ℝ)/(-(r k+(p:ℝ))-g[B,F]) from div_nonneg (by positivity) he'.le)).trans_lt ?_)
 rw [← mul_div_assoc, div_lt_iff₀ he']; change C*(2*Q)<_; linarith [mul_le_mul_of_nonneg_left hp hv.le]
section mix
variable {I:Type*}{L:Filter I}(u:I→ℝ≥0)(r:I→ Vantage)
local notation "U"=> fun (i:I)=> fair j x (u i) (r i) -- parenthesis use
lemma flightyFare (e:Tendsto (fun i=>|(r i) k|) L atTop) (z:H[j]): Δ ρ z ∈ fleeting L (U):=by
 let S:= (fleeting L (U)); let V:= S.comap (Δ ρ).toLinearMap
 have he : IsClosed (V:Set H[j]):=(closedFleet L (U) (fun i=>fair_pay ..)).preimage (Δ ρ).continuous
 suffices op: (Submodule.span ℂ (Set.range (φ)))≤ V from closure_minimal (SetLike.coe_mono op) he (flash_grant x j z)
 refine Submodule.span_le.mpr ?_; rintro _ ⟨i,rfl⟩; refine payClosed L (U) φ (fun _=>fair_pay ..) _ (flash_grant x j) ?_
 intro l; refine Metric.tendsto_nhds.mpr fun ε y=>?_ ; filter_upwards [e.eventually (earnsFare j x k J h p l i ε y)] with z f; simpa [dist_eq_norm] using (f (u z) (r z) le_rfl)
omit J h
end mix
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
