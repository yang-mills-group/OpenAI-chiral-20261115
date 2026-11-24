import YM.SU5.Voyager.Ports
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
variable (j) (J:P.Ellis a x) (v w:P.ManyF j (P.advocate a x j))
open OS.Semigroup.Burst Submodule
local notation "λ₁"=> Ψ[j]
variable {I: Type*} {L:Filter I}(u:I→ℝ≥0)(r:I→Vantage)
local notation "M"=> fleeting L (fun i => fair j x (u i) (r i))
include J
lemma starsLo (k:Axis) (e:Tendsto (fun i=>|(r i) k|) L atTop)(y:v∈ (fleeting L (fun i => fair j x (u i) (r i)))ᗮ)(h:k≠j)(p:ℝ): W[j] (aislePt k p) v=v:=by -- requires J include
 have he(g:ℝ≥0): W[j] (-(aislePt k (g:ℝ))) v=v:=by
    apply ext_inner_left ℂ; intro w
    have hp:= (Submodule.inner_right_of_mem_orthogonal (flightyFare j x k J h g u r e w) y)
    let z:= (aislePt k (g:ℝ)); let T:=W[j] z; change inner ℂ (T w-w) v=0 at hp
    rw [inner_sub_left] at hp; rw [←cart_adj j x, show star T=T.adjoint from rfl] -- tune match z
    exact (ContinuousLinearMap.adjoint_inner_right T _ _).trans (sub_eq_zero.mp hp)
 by_cases h:p ≤0
 · let g:= Real.toNNReal (-p); have hu:(g:ℝ)= -p:= Real.coe_toNNReal _ (by linarith)
   have hz:-(aislePt k (g:ℝ))=aislePt k p:=by rw [hu]; funext i; by_cases l:i=k<;>simp [aislePt,l]
   rw [←hz]; exact he g -- rewrites v? v type only
 let z:= aislePt k p; have hp₀:p>0:=lt_of_not_ge h; let g:= Real.toNNReal p
 have hp:W[j] (-z) v=v:=by have ht:= he g; rw [show (g:ℝ)=p from Real.coe_toNNReal _ hp₀.le] at ht; exact ht
 exact (congrArg (W[j] z) hp.symm).trans (show W[j] z (W[j] (-z) v)=v by rw [← ContinuousLinearMap.comp_apply,←P.cart_paves,add_neg_cancel, P.cart_zero]; rfl)
omit J
lemma cartPins (h:∀ k:Axis,k≠j→ ∀ p:ℝ,W[j] (aislePt k p) v=v) (q:Vantage): W[j] q v=v:=by
 have he:q=∑ i:Axis,(aislePt i (q i)):= by funext i; rw [Finset.sum_apply, Finset.sum_eq_single i]; simp [aislePt]; intro k hk hp; simp [aislePt,Ne.symm hp]; simp
 let f(i):= aislePt i (q i)
 have hv:∀ (S:Finset Axis), W[j] (∑ i∈S,f i) v=v:= by
     intro S; induction S using Finset.induction_on with
     | empty=> rw [sum_empty,P.cart_zero]; rfl
     | insert i S hy ih=> rw [Finset.sum_insert hy, P.cart_paves,ContinuousLinearMap.comp_apply,ih]; by_cases h':i=j; subst i; unfold f; rw [P.cart_aisle]; rfl; exact h i h' _
 rw [he]; exact hv univ
lemma fair_heat (e:Tendsto u L atTop)(s:ℝ≥0): (E[j] s-1) v∈ fleeting L (fun i => fair j x (u i) (r i)):=by
 let x':= λ₁.orth v
 have hd:Tendsto (fun i=> E[j] (u i) ((E[j] s-1) v)) L (𝓝 0):=by
    have hp:Tendsto (fun i=> u i+s) L atTop:= tendsto_atTop_mono (fun i=>by simp) e
    rw [← sub_self x']; refine (((λ₁).emerges v|>.comp hp).sub (((λ₁).emerges v).comp e)).congr (fun i=>?_); change E[j] (u i+s) v-E[j] (u i) v=E[j] (u i) (E[j] s v-v); rw [map_sub,OS.Semigroup.time]; rfl -- matches comp
 have hw:Tendsto (fun i=> fair j x (u i) (r i) ((E[j] s-1) v)) L (𝓝 0):=by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_zero_iff_norm_tendsto_zero.mp hd).congr (fun i=>?_); unfold fair; rw [(delta_shadow j x (r i) (u i)).eq]; exact (P.cart_norm ..).symm
 intro y; simpa only [inner_zero_right] using ((tendsto_const_nhds (x:=y)).inner (𝕜:=ℂ) hw)
include J
lemma pins_mink (e:Tendsto u L atTop)(G:∀ k:Axis,k≠j→ Tendsto (fun i=>|(r i) k|) L atTop)(g:P.lodestarHere j (P.advocate a x j)) : (fleeting L (fun i => fair j x (u i) (r i)))ᗮ ≤ Submodule.span ℂ {Ω[j]}:=by
 intro v p; apply (P.heavenRank j χ[j] g v).2; constructor
 · apply (heat_iff_edge j (Ψ[j]) v).1; intro t
   apply ext_inner_left ℂ; intro w; rw [← OS.Semigroup.swing]; apply sub_eq_zero.mp
   rw [← inner_sub_left]; exact Submodule.inner_right_of_mem_orthogonal (fair_heat j x w u r e t) p -- tune
 intro s; rw [eyes_toFace j s,P.sails_smooth]
 exact cartPins j x v (fun k h t=>starsLo j x J v u r k (G _ h) p h t) (fun i:Axis=> s.val i) -- tune
lemma fleetOmega (e:Tendsto u L atTop)(G:∀ k:Axis,k≠j→Tendsto (fun i=>|(r i) k|) L atTop)(g:P.lodestarHere j (P.advocate a x j)) (hv:inner ℂ Ω[j] v=0):v∈ fleeting L (fun i => fair j x (u i) (r i)):=by
 letI : CompleteSpace (fleeting L (fun i => fair j x (u i) (r i))):= (closedFleet L (fun i=> fair j x (u i) (r i)) (fun i=>fair_pay ..)).completeSpace_coe
 exact Submodule.orthogonal_orthogonal (M) ▸ (Submodule.orthogonal_le (pins_mink j x J u r e G g) (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv))
lemma joint_mix (e:Tendsto u L atTop)(G:∀ k:Axis,k≠j→Tendsto (fun i=>|(r i) k|) L atTop)(g:P.lodestarHere j (P.advocate a x j)) : Tendsto (fun i=> inner ℂ w (fair j x (u i) (r i) v)) L (𝓝 (inner ℂ w Ω[j] * inner ℂ Ω[j] v)):=by
 let z := inner ℂ Ω[j] v; have hp:inner ℂ Ω[j] Ω[j]=1:=by rw [inner_self_eq_norm_sq_to_K, show ‖Ω[j]‖=1 from origin_norm _ (P.unit_too j χ[j])]; norm_num
 have hw:inner ℂ Ω[j] (v-z • Ω[j])=0:= by rw [inner_sub_right,inner_smul_right,hp,mul_one, show inner ℂ Ω[j] v=z from rfl, sub_self]
 have hv:= (show ∀ w:H[j],Tendsto (fun i=>inner ℂ w (fair j x (u i) (r i) (v-z • Ω[j]))) L (𝓝 0) from fleetOmega j x J _ u r e G g hw) w
 have he(t:ℝ≥0)(y:Vantage): fair j x t y Ω[j]= Ω[j]:= by change E[j] _ (W[j] _ _) =_; rw [P.cart_empty,P.heaven_hot]
 change Tendsto _ _ (𝓝 (inner ℂ w Ω[j] * z)); refine zero_add (inner ℂ w Ω[j]*z) ▸ (hv.add (tendsto_const_nhds (x:=inner ℂ w Ω[j]*z))).congr ?_
 intro i; simp only [map_sub,map_smul,inner_sub_right,he,inner_smul_right,mul_comm z,sub_add_cancel]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.joint_mix
