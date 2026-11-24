import YM.CF.Exa.Canton
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
open Tap Tenant Proa
variable {ι:Type*}{n:ℕ}
local notation "ρ"=> fun a m=> ((a/(m+1:ℝ))⁻¹)^m -- scope
lemma strokeT (T S: WG ι)(p:Lively T)(t:Lively S)(q:∀ i X,S i X 1=0)(m:ℕ)(ε:ℝ)(v:0<ε): ∃ r C B a e K J:ℝ, 0<r ∧0<C∧ 0<B∧ 0<a∧ 0<e∧ 0 ≤ K ∧ 0 ≤ J ∧ a≤1∧ ((a/(m+1:ℝ))⁻¹)^m*K≤ ε ∧ ∃ N:ℕ,∀ (M:Side),N≤M.val→∀ i (b d:ℝ),0≤b→ b≤r→0<d→d ≤ e→∀ (κ:Type)[TopologicalSpace κ][Nonempty κ](Z:κ→ Op Slot),Continuous Z→(∀ i,Mind (Z i))→(∀ i,‖Z i‖ ≤ b)→ Flyer M (T i M) (S i M) (e:=d) (fun i=> -(plankP M (Z i))) b C (J*b^2+K*b) a:=by
 obtain ⟨B,c,e₀,hB,hc,he,c',A,C⟩:= p.link t; let M':= wingRent Aop B; let Q':=wingRent (Aop-(1/2:ℂ) • 1) B; let Y:=max c (max M' Q'); have hY:0<Y:=hc.trans_le (le_max_left ..)
 let W:=tox Y B; have hW:0<W:=by unfold W tox budK Uni capW dawH; positivity
 let X:= deft Y B; have hX:0<X:=by unfold X deft grantsP wornP prima zeta tox budK Uni capW dawH; positivity
 obtain ⟨a,e,v',ha,hs,hV,hD,he',hr,H',L,G⟩:= estate_m m C hB he hc (min (ε/W) Y) (lt_min (by positivity) hY) (fun i N _=> q ..)
 let R:ℝ:= min 1 (min (1/(4*Y)) (1/(4*(Uni Y B)))); have hp':0 < Uni Y B:=by unfold Uni capW dawH; positivity
 have hk:v'≤Y:=by
    apply (le_mul_of_one_le_left hr _).trans (H'.trans (min_le_right ..)); apply one_le_pow₀; rw [one_le_inv₀ (by positivity)]; exact (div_le_self ha.le (by simp)).trans he'
 have hu:a≤ B:=hD.trans (half_le_self hB.le)
 refine ⟨R,X,B,a,e,W*v',W,by positivity,hX,hB,ha,hs,by positivity,hW.le,he',by rw [mul_left_comm]; exact (mul_comm ..).le.trans ((le_div_iff₀ hW).mp (H'.trans (min_le_left ..))),max c' L,fun M z i b d b' k g h κ _ _ Z h' y v =>?_⟩
 let Q(t:κ):= -(plankP M (Z t))
 have h₁:Solo a v' (S i M) d:=axis_down a v' (G i M ((le_max_right ..).trans z)) _ g h
 have h₂:Solo a Y (T i M) d:=((axis_down B _ (A i M ((le_max_left ..).trans z)) _ g (h.trans hV)).drop hu).books (le_max_left ..)
 have h₃:Solo a Y (fun _=> tickA M) d:= ((soil_tick B d).drop hu).books ((le_max_left ..).trans (le_max_right ..)) -- check soil args implicit
 have h₄: Milli d M (fun i _=>Q i) (Y*b) a:= (((barK (a:=B) d M Z b (Aop-(1/2:ℂ) • 1) b' h' v (fun i g=>(y i).firm g)).neg_m.dusk hu).tall (mul_le_mul_of_nonneg_right ((le_max_right ..).trans (le_max_right ..)) b'))
 have hx:Y*b ≤1/4:=by
    have he:b≤1/(4*Y):= k.trans ((min_le_right ..).trans (min_le_left ..)); rw [le_div_iff₀ (by positivity)] at he; linarith
 have hg: Uni Y B*b ≤ 1/4:=by
    have he:b≤1/(4*Uni Y B):= k.trans ((min_le_right ..).trans (min_le_right ..)); rw [le_div_iff₀ (by positivity)] at he; linarith
 rw [show W*b^2+ _=tox Y B*(b^2+v'*b) from ?_]; exact climb M _ _ a B b b' ha.le hY hu v' h₄ h₁ h₂ hr hk (k.trans (min_le_left ..)) hx hg g h₃
 unfold W; ring
end YM.CF.Exa
