import YM.SU5.FiniteGaugeData.Hierarchy.Elegy
/-! # Norm control on the physical recipe products of all (also mixed) resolutions.

 Local norms. Claims on insertions at funded HORIZONS (include after some factors would already stop at lower s). Schedule geometrization below. Not continuity in s.
-/
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
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Charm
namespace Playlist
namespace Show
local notation "U" => W (tent Y h)
local notation "M" => Motif (tent Y h)
local notation "H₁"=> Theater (tent Y h)

variable (Z:ℕ→ Finset Cover)
local notation "Hᵣ" i:max => folio Λ l Z i
local notation "Wᵣ" i:max => GridStep Λ l (folio Λ l Z i)
local notation "Dₛ" i:max => salary Y h (folio Λ l Z i) i

abbrev lead (J: Wicket Λ l)(i:ℕ): Call Λ l:= fun S s=> J S s i

def inPrice (x:H₁)(p:Contract Y h Z x):= (urn Y h (folio Λ l Z s) s i K) (major Y h s Z x p (lead J i))

include K R
lemma final_bill (x:H₁)(a:Arrive Y h x s)(p:Contract Y h Z x): chorusRead Y h K R x = (singer Y h (folio Λ l Z s) s K) (major Y h s Z x p P):=by rw [ties Y h s K R x a,singer_eval, major_score Y h s K R]

local notation "C"=> readCost Y h (folio Λ l Z s) s
local notation "M₁" i:max k:max=> mkForm Y h (folio Λ l Z s) s i k
local notation "σ"=> singer Y h (folio Λ l Z s) s K
local notation "τ"=> urn Y h (folio Λ l Z s) s
local notation "praise"=>playTime Y h s Z

omit K R in
lemma carried : Spanned Y h s Z (tour Y h i k):=fun _ _=>snag_size ..
omit K in
lemma carried_I : Spanned Y h s Z (lead J i) := fun j _=> salaries_I Y h (folio Λ l Z j) j i R
omit K in
lemma carried_E : Spanned Y h s Z P := fun j _=> salaries_P Y h (folio Λ l Z j) j R

omit K R in
lemma native_pricing (g:Works Y Z i k s) (x:H₁)(a:Contract Y h Z x) (v:Fields (side Y i s)) : ‖actual Y h s i k x v‖ ≤ duration (folio Λ l Z s)*playTime Y h s Z x a:=by
 rw [← actual_eq _ _ _ _ _ _ g _ a]; exact (sold_q_bound Y h _ _ _ _ v).trans (mul_le_mul_of_nonneg_left (budget_major Y h _ _ _ _ a (carried Y h s i k Z)) (duration_pos _).le)

omit K R in
private lemma excursion {T':Type*}[NormedAddCommGroup T'][NormedSpace ℂ T']{x y:T'} (P Q:T'→L[ℂ] ℂ){a C' ε:ℝ}(v:‖Q‖≤ C')(e:‖x‖≤a)(d: ‖x-y‖≤ ε*a)(p:‖P-Q‖ ≤ ε): ‖P x-Q y‖ ≤ ε*(C'+1)*a:=by
  rw [←sub_add_sub_cancel (P x) (Q x) (Q y),←map_sub]; have hp:‖P x-Q x‖≤ε*a:= le_trans ((P-Q).le_opNorm x) (mul_le_mul p e (norm_nonneg _) ((norm_nonneg (P-Q)).trans p)); exact (norm_add_le ..).trans ((add_le_add hp ((Q.le_opNorm _).trans (mul_le_mul v d (norm_nonneg _) ((norm_nonneg Q).trans v)))).trans_eq (by ring))

lemma read_shadow (x:H₁)(p:Contract Y h Z x)(t:Arrive Y h x s)
    (w:Works Y Z i k s){ε:ℝ}(e:0≤ ε)(a: forArt s Z (tour Y h i k) P ε)(d:‖mkForm Y h (folio Λ l Z s) s i k-(σ)‖≤ ε) :
    ‖readout Y h s i k x-chorusRead Y h K R x‖ ≤ ε*(readCost Y h (folio Λ l Z s) s+1)*playTime Y h s Z x p:= by
 rw [(real_receipt Y h s i k Z w x p).2.2.2, final_bill Y h s K R Z x t p]; exact excursion _ _ (income_w ..) (budget_major _ _ _ _ _ _ _ (carried Y h s i k Z)) (budget_diff Y h _ _ _ _ (carried Y h s i k Z) (carried_E Y h s R Z) e a _ p) d

lemma earnings (ε:ℝ)(p:0<ε): ∀ᶠ r:ℕ in atTop,
  (∀ (x:Theater (tent Y h))(a:Contract Y h Z x), Arrive Y h x s→
     ‖inPrice Y h s (u r) (J:=J) K Z x a - chorusRead Y h K R x‖≤ ε*playTime Y h s Z x a) ∧
  ∀ k, legacy Y (u r) (v k)→ Works Y Z (u r) (v k) s ∧ ∀ (x:Theater (tent Y h))(a:Contract Y h Z x),Arrive Y h x s→
      ‖readout Y h s (u r) (v k) x - chorusRead Y h K R x‖ ≤ ε*playTime Y h s Z x a:=by
 have he:= readCost_nn Y h (Hᵣ s) s; let t:= ε/(C+1); have ht:0<t:=by unfold t; positivity
 have hp(i:Fin (s+1)):= hired Y h (folio Λ l Z i) i K R t ht
 filter_upwards [(eventually_all (ι:=Fin (s+1))).mpr hp, boutique_P Y h (folio Λ l Z s) s K t ht] with i e hq
 have ht': t*(C+1)=ε:= div_mul_cancel₀ _ (by linarith)
 constructor
 · intro x a p; unfold inPrice; rw [final_bill Y h s K R Z x p a, ←ht']; -- rewriting all ε destruct?
   apply excursion (τ (u i) K) (σ) (income_w ..) (budget_major _ _ _ _ _ _ _ (carried_I Y h s (u i) R Z)) (budget_diff Y h s Z (lead J (u i)) P (carried_I Y h s (u i) R Z) (carried_E Y h s R Z) ht.le ?_ x a) hq.1
   intro j p; exact (e ⟨j,p.trans (by omega)⟩).1
 intro k g
 have hv:Works Y Z (u i) (v k) s:= fun j q=> ((e ⟨j,q.trans_lt (Nat.lt_succ_self _)⟩).2 k g).1
 refine ⟨hv,fun x a p=>?_⟩; rw [←ht']
 exact read_shadow Y h s (u i) (v k) K R Z x a p hv ht.le (fun j q=> ((e ⟨j,q.trans (Nat.lt_succ_self _)⟩).2 k g).2) (hq.2 k g).2
#print axioms earnings
-- UV then IR on any Theatre element, UV bound again at sufficiently late period.
lemma cleared_I : ∀ᶠ i:ℕ in atTop, ∀ ε:ℝ,0<ε → ∀ᶠ r:ℕ in atTop, Works Y Z i (v r) s ∧ ∀ (x:H₁)(a:Contract Y h Z x),
   ‖readout Y h s i (v r) x-inPrice Y h s i (J:=J) K Z x a‖ ≤ ε*playTime Y h s Z x a:=by
  have hp (i:Fin (s+1)):= solvent_often Y h (Hᵣ i.val) i
  filter_upwards [(eventually_all (ι:=Fin (s+1))).mpr hp,boutique_urn Y h (folio Λ l Z s) s K] with i G V
  intro ε e; have he:= readCost_nn Y h (Hᵣ s) s; let t:= ε/(C+1); have ht:0<t:=by unfold t; positivity
  have hv(j:Fin (s+1)):= (Metric.tendsto_nhds (α:=Slip Λ l (Hᵣ j.val))).mp ((R.evening (Hᵣ j.val) j).inner i) t ht
  filter_upwards [(Metric.tendsto_nhds (α:= Catalog (Hᵣ s) →L[ℂ] ℂ)).mp V t ht,(eventually_all (ι:=Fin (s+1))).mpr hv,(eventually_all (ι:=Fin (s+1))).mpr (fun j=>often_offer_inner Y h _ _ i K (G j))] with r a v' W
  have hp:Works Y Z i (v r) s:= fun j p=> W ⟨j,p.trans_lt (Nat.lt_succ_self _)⟩; refine ⟨hp,fun x p=>?_⟩
  have hz:t*(C+1)=ε:= div_mul_cancel₀ ε (by linarith); rw [(real_receipt Y h s i (v r) Z hp x p).2.2.2, ← hz]; unfold inPrice
  refine excursion _ _ (income_v ..) (budget_major Y h _ _ _ _ _ (carried Y h s i (v r) Z)) (budget_diff Y h s Z _ _ (carried Y h s i (v r) Z) (carried_I Y h s i R Z) ht.le ?_ _ p) (by rw [←dist_eq_norm (mkForm Y h _ _ _ _)]; exact a.le)
  intro j p; exact (v' ⟨j,p.trans (Nat.lt_succ_self _)⟩).le.trans_eq' (dist_eq_norm (snag Y h (Hᵣ j) j i (v r)) _)

lemma lifts (x:H₁) (p:Contract Y h Z x)(v':Arrive Y h x s) :
 (∀ᶠ i:ℕ in atTop,Tendsto (fun r=> readout Y h s i (v r) x) atTop (𝓝 (inPrice Y h s i (J:=J) K Z x p))) ∧ Tendsto (fun i=>inPrice Y h s (u i) (J:=J) K Z x p) atTop (𝓝 (chorusRead Y h K R x)) ∧ (∀ k:ℕ→ℕ,eligiblePath Y u v k→ Tendsto (fun i=> readout Y h s (u i) (v (k i)) x) atTop (𝓝 (chorusRead Y h K R x))) := by
 let P:= (praise) x p; have he:0<P+1:=by have z:= play_nn Y h s Z x p; unfold P; positivity
 let W(t:ℝ):= t/(P+1); have hW(t:ℝ)(u:0<t):0<W t := div_pos u he; have hp(t)(u:0<t):W t*P<t:=calc
   _ < W t*(P+1):= by nlinarith [hW t u]
   _ = t:= div_mul_cancel₀ _ he.ne'
 refine ⟨(cleared_I Y h s K R Z).mono ?_,?_⟩
 · intro i q; refine Metric.tendsto_nhds.mpr fun t u=>?_ ; filter_upwards [q _ (hW t u)] with r he; rw [dist_eq_norm]; exact (he.2 _ p).trans_lt (hp t u)
 refine ⟨Metric.tendsto_nhds.mpr ?_,fun k q=>Metric.tendsto_nhds.mpr ?_⟩<;> intro t a
 · filter_upwards [earnings Y h s K R Z _ (hW t a)] with r he; rw [dist_eq_norm]; exact (he.1 x p v').trans_lt (hp t a)
 filter_upwards [earnings Y h s K R Z _ (hW t a),q] with r he z; rw [dist_eq_norm]; exact (((he.2 (k r) z).2) x p v').trans_lt (hp t a)
#print axioms lifts
end Show
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
