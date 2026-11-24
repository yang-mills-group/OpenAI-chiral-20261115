import VerifiedSatinGroundInteraction
import YM.SU5.Selected.GlassLaw
import YM.SU5.Selected.Sentry
/-! # Satisfy the one-axis coast criteria. Uses actual phase Full/Γ data, no Rot covariance. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 340000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Selected
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set Vacancy
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L₀" => Λ.R.L.val
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E) (s : ℕ)
variable {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b) (Qt : Clipped Y H (i ∘ a) (k ∘ b))
variable (j : Axis) (strict : Bool) (C : Arena Y H Q.circuit j 0 strict)
open TopologicalSpace OS.Ground YM.SelectionAnalysis Vacancy
variable (f : (displayAlgebra Y H V Q Qt j strict C) →⋆ₐ[ℂ] ℂ)
local notation "A" => Ark.Ht Y H Q.circuit j 0 strict C
local notation "𝔄" => displayAlgebra Y H V Q Qt j strict C
local notation "𝔅" => driveAlgebra Y H V Q Qt j strict C
local notation "ℛ" => Aurora Y H V Q j strict C
local notation "𝔙" t:max => Tower.Field Y H t j 0 strict
local notation "Ω₀" => seat0 Y H V Q j strict C
local notation "ω₀" => floorV Y H Q.circuit j 0 strict C
local notation "E₀" t:max x:max p:max => entrance Y H V t Q Qt j strict C x p
local notation "ιₜ" t:max => actor Y H t Q.circuit j 0 strict C
local notation "Φ" => atCharacter Y H V Q Qt j strict C f
local notation "Λ₀" => traveller Y H V Q Qt j strict C
local notation "Ε" t:max => response Y H V t Q Qt j strict C f
local notation "Π" B:max => procession Y H V Q Qt j strict C f B
local notation "Υ" u:max => moveMark Y H u strict
local notation "Θ" => mirrorInMarks Y H j strict
local notation "Τ" => Marks (tent Y H) strict
local notation "Μ" => timeMesh Λ
local notation "ψ" t:max n:max => heatStamp Y H V t Q Qt j strict C n
local notation "Σ₁" u:max d:max => shiftStamp Y H V Q Qt j strict C u d
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "Ρ" => indoor Y H V Q Qt j strict C f
local notation "Ω" => doorstep Y H V Q Qt j strict C f
local notation "Oa" => arrive Y H V Q Qt j strict C f
local notation "a₀" t:max x:max => bud Y H V t Q Qt j strict C f x
local notation "M₁" t:max => futureMark Y H t j strict
local notation "S"=> turnstile Y H V Q Qt j strict C f
local notation "R" => ride Y H V Q Qt j strict C f
local notation "P" k:max => (S).crew k
local notation "T" => look j
open Germ SelectionAnalysis Sunbelt
local notation "Ξ"=> mainsea Y H V Q Qt j strict C f
local notation "δ"=> daylight Μ
local notation "U" i:max z:max=> (((S).crew i).play z)
local notation "Γ"=> MeshClock.marks Μ
local notation "sel" v:max=> (Ξ).plane v
lemma coupling_chart (x y: 𝔙 s) (u:placement Λ) : Visits Y H V s Q Qt j strict C f x y u=inner ℂ (a₀ s x) ((sel u) (a₀ s y)):=rfl
lemma mealRight (x: Marks (tent Y H) strict) (l : Finset Cover) (h: InTest K true l false x.val) (t:Tower.region j 0 (K).ℓ l) : ∃ a:Tower.Field Y H s j 0 strict, x=(M₁ s) a:= by
  refine ⟨(⟨x.val, (purpose_ok ..).mpr ⟨?_, (marksSpec strict x).2⟩⟩:Tower.Field Y H s j 0 strict), rfl⟩
  exact (show _ from ⟨_,h,by rw [area0]; exact t⟩)
local notation "a⊙" k:max v:max x:max => sail Y H s j 0 strict (k:Trans j).val (k:Trans j).property ((2:ℤ)*v) x
local notation "C₀" k:max t:max=> Arena Y H Q.circuit k t strict
local notation "ξ" a:max v:max=> displacement Y H V Q Qt j strict C f a v
lemma wide_meal(k:Trans j)(x y:Tower.Field Y H s j 0 strict) (t:C₀ k.val 0) :
    ∃ (p : ℕ) (u v : Tower.Field Y H s k.val 0 strict),
      Duality Y H V s Q Qt j strict C f t (ξ k.val t) (a⊙ k (-(p:ℤ)) x) (a⊙ k (p:ℤ) y) u v:=by
  obtain ⟨sx,hx⟩:= (field_test Y H s j 0 strict x).paid; obtain ⟨sy,hy⟩:= (field_test Y H s j 0 strict y).paid
  let w:= (sx∪sy).sup (fun i:Cover=> (i k.val).natAbs); let p : ℕ:= w+(K).ℓ
  let x' := a⊙ k (-(p:ℤ)) x; let y' := a⊙ k (p:ℤ) y; let y₀:= plow K k.val p sy; let x₀ := plow K k.val (-(p:ℤ)) sx
  have hp(j:Cover)(hq:j∈sx∪sy) : |j k.val| ≤ (w:ℤ):= by rw [←Int.natCast_natAbs]; exact_mod_cast le_sup (f:=fun i:Cover=> (i k.val).natAbs) hq
  have ht:(p:ℤ)≤ ruler (K).B*p:= le_mul_of_one_le_left (by positivity) (ruler_gene (K).B)
  obtain ⟨v,he⟩:= mealRight Y H s k.val strict ((M₁ s) y') y₀ (flow_port _ _ _ hy) (by
    intro i l; obtain ⟨a,u,rfl⟩ := plow_stays K k.val p sy l; rw [moves,if_pos rfl]; have hv:=neg_le_of_abs_le (hp a (Finset.mem_union_right sx u)); unfold p at *; omega)
 -- filled
  let V₀:= mirrorInMarks Y H k.val strict ((Θ) ((M₁ s) x')); let x₂:= reflectedBox k.val 0 (reflectedBox j 0 x₀)
  have hx' : InTest K true x₀ false x'.val:= flow_port K k.val _ hx
  obtain ⟨u,he'⟩:= mealRight Y H s k.val strict V₀ x₂ (axial K k.val _ (axial K j _ hx')) (by
    intro a v; obtain ⟨i,g,r⟩:= reflect_stays k.val 0 (reflectedBox j 0 x₀) v; obtain ⟨m,g,u⟩:=reflect_stays j 0 x₀ g; obtain ⟨b,e,rfl⟩:=plow_stays K k.val _ sx g; rw [r,if_pos rfl,u,if_neg k.property,moves,if_pos rfl,mul_neg]; have hu:= le_of_abs_le (hp b (Finset.mem_union_left sy e)); unfold p at *; omega)
  refine ⟨p,u,v,fun i t'=> (across_response Y H V t' Q Qt j strict C f i k.val t).symm, ?_, congrArg Subtype.val he⟩
  have hv : (mirrorInMarks Y H k.val strict V₀).val=((Θ) ((M₁ s) x')).val:= mirror_invert K k.val _ (marksSpec strict _).1
  rw [he'] at hv; exact hv.symm

-- center shifted pair with common δ; no angular rotations.
lemma estate_centerout(k:Trans j)(x y:Tower.Field Y H s j 0 strict)(p:ℤ)(u:placement Λ)(l:marks Μ) :
    let t:=notch Μ s p
    Visits Y H V s Q Qt j strict C f x y (Function.update u k.val (l+t+t))=
      Visits Y H V s Q Qt j strict C f (a⊙ k (-p) x) (a⊙ k p y) (Function.update u k.val l):=by
  intro T'
  rw [coupling_chart,coupling_chart,←turnstile_in Y H V s Q Qt j strict C f x k (-p),←turnstile_in Y H V s Q Qt j strict C f y k p]
  have hz : (notch Μ s (-p)) = -T':=Subtype.ext (by change bell Μ s (-p)= -bell Μ s p; simp [bell]); rw [hz]
  let Z(v:Γ):= Function.update u k.val v; let x:=a₀ s x; let y:=a₀ s y -- shadow
  change inner ℂ x ((sel (Z _)) y)=inner ℂ ((U k (-T')) x) ((sel (Z l)) ((U k T') y))
  rw [← Players.shift_g] -- rhs
  have h(v:Γ) : (sel (Z (v+T')))= (sel (Z v)).comp (U k T'):= (Ξ).carries_spot u k v _ T' rfl
  have he:(U k T').comp (sel (Z l))=(sel (Z l)).comp (U k T'):= (Ξ).plane_cross (R) rfl (follows_road Y H V Q Qt j strict C f) k T' (Z l)
  rw [h (l+T'),h l, ←ContinuousLinearMap.comp_apply (U k T') (sel (Z l)), he]; rfl

lemma time_coast(x y:Ρ)(ε:ℝ)(p:0<ε): ∃ t:ℝ,∀ (u:placement Λ)(p q:Γ),t ≤ (p:ℝ) → t ≤ (q:ℝ) →
    ‖inner ℂ x ((sel (Function.update u j p)) y)-inner ℂ x ((sel (Function.update u j q)) y)‖≤ε:=by
 let d:=‖y‖+1; let r:=ε/2/d; obtain ⟨L,hL⟩:= Filter.eventually_atTop.mp (Metric.tendsto_nhds.mp ((R).emerges x) r (by unfold r d; positivity))
 refine ⟨(L:ℝ),fun u v w h e=>?_⟩
 have he (v:Γ): inner ℂ x ((sel (Function.update u j v)) y)= inner ℂ ((R).E v.val.toNNReal x) ((S).raw T (fun i=> u i.val) y):=by
    unfold Sunbelt.plane; rw [Function.update_self,show (fun i:{x:Axis // x≠j}=> Function.update u j v i.val)=(fun i=>u i.val) from funext (fun i=> update_of_ne i.property ..)]; exact ((R).swing ..).symm
 let V':= (v:ℝ).toNNReal; let W:= (w:ℝ).toNNReal; rw [he v,he w,← inner_sub_left]; let x' := (R).orth x
 have t (v:Γ) (h:(L:ℝ) ≤ (v:ℝ)) : L ≤ v.val.toNNReal:= by change (L:ℝ)≤ (↑(v.val.toNNReal):ℝ); rwa [Real.coe_toNNReal v.val ((NNReal.zero_le_coe ..).trans h)] -- name tune
 refine (norm_inner_le_norm ..).trans ?_
 rw [← dist_eq_norm]; refine (mul_le_mul ((dist_triangle _ x' _).trans (add_le_add ((hL V' (t v h)).le) ((dist_comm ..).trans_le ((hL W (t w e)).le)))) (show ‖(S).raw _ _ y‖≤d from (raw_price (Ξ) _ _ y).trans (by unfold d; linarith)) (norm_nonneg _) (by unfold r d; positivity)).trans_eq ?_; unfold r; have : d ≠ 0:= ne_of_gt (by unfold d; positivity); field_simp; ring

lemma across_meals(k:Trans j)(x y:Tower.Field Y H s j 0 strict): (Ξ).Coasts k (a₀ s x) (a₀ s y):=by
 intro ε v
 let C' := Classical.choice (voyage_H Y H V Q.circuit k.val 0 strict); obtain ⟨p,u,w,g⟩:= wide_meal Y H V s Q Qt j strict C f k x y C'
 let t:= notch Μ s (p:ℤ); let f':= displacement Y H V Q Qt j strict C f k.val C'; let U' := bud Y H V s Q Qt k.val strict C' f' u; let W:= bud Y H V s Q Qt k.val strict C' f' w
 obtain ⟨L,hL⟩:= time_coast Y H V Q Qt k.val strict C' f' U' W ε v
 refine ⟨max 0 L+(t:ℝ)+(t:ℝ),fun o r r' h i s'=>?_⟩
 let z (r:Γ):= r-t-t; let V₀ (r:Γ):= Function.update o k.val r
 have he (r:Γ)(h:max 0 L+(t:ℝ)+(t:ℝ)≤ (r:ℝ)): max 0 L ≤ ((z r):ℝ):= by unfold z; change _≤ (r:ℝ)-(t:ℝ)-(t:ℝ); linarith
 let Y':= mainsea Y H V Q Qt k.val strict C' f'
 have h' (r:Γ)(v:max 0 L ≤ (z r:ℝ)) : inner ℂ (a₀ s x) ((sel (V₀ r)) (a₀ s y))= inner ℂ U' (Y'.plane (Function.update o k.val (z r)) W):= by
    rw [← coupling_chart]; unfold V₀
    nth_rw 1 [← show z r+t+t=r by unfold z; abel]; refine (estate_centerout Y H V s Q Qt j strict C f k x y (p:ℤ) o (z r)).trans ((Duality.compare Y H V s Q Qt j strict C f C' f' (a⊙ k (-(p:ℤ)) x) (a⊙ k (p:ℤ) y) _ _ g _ ?_ ?_).trans (coupling_chart Y H V s Q Qt k.val strict C' f' u w _))
    · unfold uptown; rw [Function.update_of_ne k.property.symm]; exact s'
    unfold uptown; rw [Function.update_self]; exact (le_max_left ..).trans v
 change ‖inner ℂ _ ((sel (V₀ r)) _) - inner ℂ _ ((sel (V₀ r')) _)‖≤_; rw [h' r (he r h), h' r' (he r' i)]; exact hL o (z r) (z r') ((le_max_right ..).trans (he r h)) ((le_max_right ..).trans (he r' i))

theorem mix_first (k:Trans j) (x y:Ρ): (Ξ).Coasts k x y:= by
  have h:= stroll_dense Y H V Q Qt j strict C f; apply solidPair (Ξ) (R) rfl (h.prod h) k _ x y
  rintro ⟨a,b⟩ ⟨p,q⟩; obtain ⟨i,u,w⟩:= Set.mem_iUnion.mp p; obtain ⟨r,v,z⟩:= Set.mem_iUnion.mp q
  change a₀ i u=a at w; change a₀ r v=b at z; subst a; subst b; let t:= max i r; have h₁:i≤t:= le_max_left ..; have h₂:r≤t:= le_max_right ..
  have hz:= across_meals Y H V t Q Qt j strict C f k (Raise Y H Q.circuit j 0 strict i t h₁ u) (Raise Y H Q.circuit j 0 strict r t h₂ v); rw [flourishes Y H V i, flourishes Y H V r] at hz; exact hz
end YM.CF.Buffered.Afterglow.Tower.Selected
#print axioms YM.CF.Buffered.Afterglow.Tower.Selected.mix_first
