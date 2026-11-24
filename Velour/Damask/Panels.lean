import Velour.Damask.Swirl
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Damask
open Function Set Filter Complex Metric Polynomial
open scoped Topology BigOperators Polynomial Classical

variable {κ:Type*}{A:κ→ℝ→Prop}{B:κ→ℂ→ℂ}{n:ℕ}
local notation "τ"=> 2*Real.pi
structure Panels (A:κ→ℝ→Prop)(B:κ→ℂ→ℂ)(n:ℕ):Prop where
 cover (x:ℝ) : ∃i:κ,A i x
 localize (i:κ)(x:ℝ): A i x → ∀ᶠ y in 𝓝 x,A i y
 meet (x:ℝ)(i j:κ): A i x→A j x→B i ↑x=B j ↑x
 period (x:ℝ)(i:κ): A i x→ A i (x+(τ))∧ B i ↑(x+(τ):ℝ)=B i ↑x
 beams (i:κ)(z:ℂ):A i z.re→ AnalyticAt ℂ (B i) z
 spends (i:κ)(x:ℝ): A i x →
    ∃c:ℝ,∀ᶠ y in 𝓝 x,∀z:ℂ,z.re=y→ ‖B i z‖ ≤ c* Real.exp |z.im| ^ n


lemma realHit {f g:ℂ→ℂ}{x:ℝ}(h:∀ᶠ y:ℝ in 𝓝 x, f y=g y):
    ∃ᶠ z in 𝓝[≠] (x:ℂ),f z=g z:=by
 have t:Tendsto (fun y:ℝ=>(y:ℂ)) (𝓝[≠] x) (𝓝[≠] (x:ℂ)):=by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds
    exact eventually_mem_nhdsWithin.mono fun _ p=> mt ofReal_injective.eq_iff.mp p
 intro e; obtain ⟨y,u,v⟩ := ((h.filter_mono nhdsWithin_le_nhds).and (t.eventually e)).exists; exact v u

namespace Panels
variable (h:Panels A B n)
include h
lemma meets (z:ℂ)(i j:κ)(p:A i z.re)(r:A j z.re): B i z=B j z:=by
 let x:=z.re
 let g:=fun y:ℝ=> (x:ℂ)+y*I
 have t:IsPreconnected (range g):=isPreconnected_range (by fun_prop)
 have v: ∀w∈range g,w.re=x:=by rintro w ⟨y,rfl⟩; simp [g]
 refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
   (show AnalyticOnNhd ℂ (B i) _ from fun w u=>h.beams _ _ ((v _ u).symm ▸ p))
   (show AnalyticOnNhd ℂ (B j) _ from fun w u=>h.beams _ _ ((v _ u).symm ▸ r))

   t (show (x:ℂ)∈range g from ⟨0,by simp [g]⟩)
    (realHit (((h.localize i _ p).and (h.localize j _ r)).mono fun y k=>h.meet _ _ _ k.1 k.2))
    ⟨_,Complex.re_add_im z⟩

def chain (h:Panels A B n)(z:ℂ):ℂ:= B (h.cover z.re).choose z
lemma chain_eq (z:ℂ)(i:κ)(p:A i z.re):h.chain z=B i z:=h.meets _ _ _ (h.cover _).choose_spec p

lemma aglow:AnalyticOnNhd ℂ h.chain univ:=by
 intro z _
 obtain ⟨i,p⟩:=h.cover z.re
 exact (h.beams _ _ p).congr ((continuous_re.continuousAt.eventually (h.localize _ _ p)).mono
      fun w u=> (h.chain_eq _ _ u).symm)

lemma retraced : Periodic h.chain (↑(τ:ℝ):ℂ):=by
 let f:= fun z:ℂ=> h.chain (z+(↑(τ:ℝ):ℂ))
 have y(x:ℝ):f x=h.chain x:=by
    obtain ⟨i,p⟩:=h.cover x
    obtain ⟨q,t⟩:= h.period x i p
    unfold f
    rw [←ofReal_add,h.chain_eq _ i (by simpa using q),h.chain_eq _ i (by simpa using p),t]
 have hf:AnalyticOnNhd ℂ f univ:= fun z _=> (h.aglow _ trivial).comp
     (analyticAt_id.add analyticAt_const)
 exact fun z=>hf.eqOn_of_preconnected_of_frequently_eq h.aglow
    isPreconnected_univ (mem_univ _) (realHit (x:=0) (Eventually.of_forall y)) (mem_univ z)


lemma localPrice (x:ℝ):
 ∃c:ℝ,∀ᶠ y in 𝓝 x,∀z:ℂ,z.re=y → ‖h.chain z‖ ≤ c* Real.exp |z.im| ^ n:=by
 obtain ⟨i,p⟩:=h.cover x
 obtain ⟨c,q⟩:=h.spends i x p
 refine ⟨c,((h.localize i x p).and q).mono fun y v z e=>?_⟩
 rw [h.chain_eq _ i (e.symm ▸ v.1)]; exact v.2 z e

lemma stripPrice :
 ∃c:ℝ,∀z:ℂ,z.re ∈ Icc 0 (τ) → ‖h.chain z‖ ≤ c* Real.exp |z.im| ^ n:=by
 refine isCompact_Icc.induction_on
    (p:= fun w:Set ℝ=>∃c:ℝ,∀z:ℂ,z.re∈w→ ‖h.chain z‖ ≤ c* Real.exp |z.im| ^ n)
    ?_ (fun _ _ p a=>?_ ) (fun _ _ p a=>?_ ) ?_
 · exact ⟨0,fun z e=>e.elim⟩
 · obtain ⟨c,q⟩:=a; exact ⟨_,fun _ e=>q _ (p e)⟩
 · obtain ⟨c,q⟩:=a; obtain ⟨d,t⟩:=p
   refine ⟨max c d,fun z r=>?_⟩
   exact r.elim (fun v=>(t z v).trans (by gcongr;apply le_max_right))
     (fun v=>(q z v).trans (by gcongr; apply le_max_left))


 intro x _
 obtain ⟨c,q⟩:=h.localPrice x
 exact ⟨_,mem_nhdsWithin_of_mem_nhds q,c,fun z p=>p z rfl⟩

lemma Osc : Oscillates n h.chain:=by
 refine ⟨h.retraced,analyticOnNhd_univ_iff_differentiable.mp h.aglow,?_⟩
 obtain ⟨c,q⟩:=h.stripPrice
 refine ⟨c,fun z=>?_⟩
 obtain ⟨m,g,-⟩:=existsUnique_sub_zsmul_mem_Ico (show 0<(τ) from by positivity) z.re 0
 rw [zero_add,zsmul_eq_mul] at g
 let y:= z-m*(↑(τ:ℝ):ℂ)
 have r:y.re∈Icc 0 (τ):=by simpa [y] using (Ico_subset_Icc_self g)
 have a:=q y r
 have b:h.chain z=h.chain y:= (congrArg _ (sub_add_cancel z _).symm).trans (h.retraced.int_mul m y)
 rw [b]; exact a.trans_eq (by simp [y])
lemma studded: Studded n h.chain:=h.Osc.daily
#print axioms studded

