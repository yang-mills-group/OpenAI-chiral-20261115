import YM.SU5.Assay.BSOT
-- possibly add C* etc
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Metric Filter
open scoped Topology
open CF.Buffered.Afterglow.Tower.Aria (firmly)
variable {H:Hilbert}{I:Type*}{l:Filter I}{a b:I→H.Op}{x y:H.Op}
open MeasureTheory
open scoped InnerProductSpace
variable {G:Type*}[MeasurableSpace G] {μ:Measure G}{M N:G→H.Op}
open scoped Classical
/-!
# Integrate bounded operators on vectors, not presuming norm-measurable operators.
Charge even for starred integrals; suited for real-valued smears too.
-/
structure SInk (μ:Measure G)(M:G→H.Op): Prop where
  body: ∀ u:H,Integrable (fun g=>M g u) μ
  back: ∀ u:H,Integrable (fun g=>star (M g) u) μ
  ticket: ∃ d:G→ℝ,Integrable d μ ∧ ∀ᵐ g ∂μ, ‖M g‖ ≤ d g

lemma SInk.toll {d:G→ℝ}(p:Integrable d μ)(h:∀ᵐ g ∂μ, ‖M g‖ ≤ d g)(u:H):
 ‖∫ g,M g u ∂μ‖≤ (∫ g,d g∂μ)*‖u‖:=by
 rw [←integral_mul_const]; exact norm_integral_le_of_norm_le (p.mul_const _) (h.mono fun i v=> (M i).le_of_opNorm_le v u)

noncomputable def SInk.mail (p: SInk μ M): H.Op:=
 let f:H→ₗ[ℂ]H:=
   { toFun:=fun u=> ∫ g,M g u ∂μ
     map_add':=fun x y=>by simp only [map_add];exact integral_add (p.body x) (p.body y)
     map_smul':=fun z x=>by simp only [map_smul,integral_smul,RingHom.id_apply] }
 let w:=p.ticket.choose_spec
 f.mkContinuous _ (toll w.1 w.2)

/-- Junk value outside receipt qualification. -/
noncomputable def SInt (μ:Measure G)(M:G→H.Op) : H.Op:= if p:SInk μ M then p.mail else 0

namespace SInk
variable (p:SInk μ M)
include p
lemma click (u:H): SInt μ M u= ∫ g,M g u ∂μ:= by unfold SInt;rw [dif_pos p];rfl
lemma castLe {d:G→ℝ}(v:Integrable d μ)(h:∀ᵐ g ∂μ, ‖M g‖ ≤ d g): ‖SInt μ M‖≤∫g,d g∂μ:=by
 have q:0≤∫g,d g∂μ:= integral_nonneg_of_ae (h.mono fun i z=>(norm_nonneg ..).trans z)
 refine (SInt μ M).opNorm_le_bound q ?_
 intro u; rw [click p]; exact toll v h u
lemma turn (u:H):star (SInt μ M) u=∫g, star (M g) u ∂μ:=by
 apply ext_inner_left ℂ; intro x
 have e(A:H.Op):⟪x,star A u⟫_ℂ=⟪A x,u⟫_ℂ:=ContinuousLinearMap.adjoint_inner_right ..
 rw [e (SInt μ M)] -- tune wait p.mail ≠ literal
 rw [click p,← integral_inner (p.back u),← inner_conj_symm (∫ g,M g x ∂μ) u,← integral_inner (p.body x),← integral_conj]
 refine integral_congr_ae (Eventually.of_forall fun g=> (inner_conj_symm (M g x) u).trans (e (M g)).symm)
omit p

section sequence
variable [IsCountablyGenerated l]{A:I→G→H.Op}{d:G→ℝ}
variable (h:∀ᶠ i in l,SInk μ (A i))(q:Integrable d μ)(v:∀ᶠ i in l,∀ᵐ g ∂μ, ‖A i g‖≤d g)
   (t:∀ᵐ g ∂μ, BSOT (fun i=> A i g) l (M g))
include p h q v t
lemma passage : BSOT (fun i=>SInt μ (A i)) l (SInt μ M):=by
 refine ⟨⟨max (∫ g,d g∂μ) 0,le_max_right ..,(h.and v).mono fun i w=>(castLe w.1 q w.2).trans (le_max_left ..)⟩,fun u=>?_,fun u=>?_⟩
 · rw [click p]
   have ht:= tendsto_integral_filter_of_dominated_convergence _
      (h.mono fun _ w=>(w.body u).aestronglyMeasurable) ?B (q.mul_const ‖u‖) (t.mono fun _ w=>w.showAt u)
   exact ht.congr' (h.mono fun _ w=>(click w u).symm)
   case B=>exact v.mono fun i w=>w.mono fun j z=> (A i j).le_of_opNorm_le z u
 rw [turn p]
 have ht:= tendsto_integral_filter_of_dominated_convergence _
      (h.mono fun _ w=>(w.back u).aestronglyMeasurable) ?B (q.mul_const ‖u‖) (t.mono fun _ w=>w.starAt u)
 exact ht.congr' (h.mono fun _ w=>(turn w u).symm)
 case B=>exact v.mono fun i w=>w.mono fun j z=> (star (A i j)).le_of_opNorm_le ((norm_star _).trans_le z) u
end sequence
end SInk
end YM
