import YM.CF.Arena.Yale
import YM.CF.Vale.Hark
/-! Replacement for Arena.Yale.saga; DON’T use old API (hypothesis quantified over order zero `Before`, cannot instantiate!). Here use `Push.Uniform.pre_order`. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
lemma sagaValid(K:Teller G)(P:Patch)(q:Chi)(l n j:ℕ)(hl:5 ≤ l)(hy:l ≤ 18)(hg:l+78 ≤ j)(hp:5 ≤ n)(hv:P.Branches K.bind G)(T:∀ i:ℕ,3 ≤ i → i ≤ n+3 →  Push.Uniform.Before G K.top.width K.top.paths K.j K.bind i): ∃ W E,∃ r:ℕ,∃ s t C D σ:ℝ,nib W∧CapY E∧ j ≤ r ∧ 0<s∧0<t∧0<C∧0<D∧0<σ∧∀ᶠ x in atTop, let R:=horn x l; let B:= W R; let A:= D*temp x^(l+2-4); let p:=E R; p ≤ (r-1)*radiusB x ∧∀ {c f:Side}(S:StepData (More c) f)(T:Tube G S), Prime P K S T x →∀ d:ℝ, let F:=fun t:Tab S=> fame T t q x d l; (r+r+101)*radiusB x ≤ (More c).val→ ∃ O, Woven F O p 2 n σ (C*B) (A*B) ∧ ∀ (i:Site (More c))(V:Config G (More c))(t':Tab S)(a:Stores S), a.flags=RG.flags (temp x) V→ let Z:=issued x j r F O a t' i ∘ Vmove x V; let u:= compass n 2 x (C*B) (A*B) t; Allows n Z 0 (compass n 2 x C A s+(plot p*u+ plot p*u))∧ (i∉ a.dome (p+r*radiusB x) → Allows n Z 0 (compass n 4 x (C*B) (A*B) t)):=by
 obtain ⟨E,W,hE,hW,hD,H⟩:=weave n hp; obtain ⟨σ,D,C,hσ,hσ',hD',hC,H'⟩:= tallValid K P q l n (by omega) hy hp hv T
 have hEE:=hE; choose K' hK using hEE -- maybe choose
 let u:=K'*(l+77); let r:= j+1+u; have h:1≤j:=by omega
 have ht: j ≤ r:=by omega
 obtain ⟨s,hs,hv⟩:= trod (j-2) n σ (by omega) hσ hσ'; obtain ⟨t,hT,hv'⟩:= trod (r-2) n σ (by omega) hσ hσ'
 have hα:Tendsto (fun x=>D*temp x^(l+2-4)) atTop (𝓝 0):=by have he:=(show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0); simpa only [zero_pow (show l+2-4 ≠0 by omega),mul_zero] using ((he.pow (l+2-4)).const_mul D)
 refine ⟨W,E,r,s,t,C,D,σ,hW,hE,ht,hs,hT,hC,hD',hσ,?_⟩; filter_upwards [H',Work.E01.radiusB_tendsto.eventually_ge_atTop 1000,hv,hv', PatchReads.reserve K P,hα.eventually (ge_mem_nhds hC)] with x hX hR hY hY' hT' ha; intro R B A p
 have hz:E R ≤ u * radiusB x:=by refine (hK R).trans ((mul_assoc K' (l+77) (radiusB x)) ▸ (Nat.mul_le_mul_left K' (by unfold Pad R horn; simp_rw [Nat.add_mul]; omega)))
 have hS: p ≤ (r-1)*radiusB x:= hz.trans (Nat.mul_le_mul_right _ (by omega)); refine ⟨hS,?_⟩; intro c f S T P d F hU; have h_e(t:Tab S):=hX _ _ P.Post t (P.turns t).1 (P.turns t).2 d
 have he : 0 ≤ A:= mul_nonneg hD'.le (pow_nonneg (temp_nonneg _) _)
 obtain ⟨V,hV⟩:= H S F (horn x l) σ C A hσ hσ' he ha (by refine lt_of_le_of_lt hS (lt_of_lt_of_le ?_ hU); exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)) (fun _ _ _ v=> fameK (hT' _ _ P.Post.got P.Post.size P.Post.funds.1) hR v) (fun i v=>(h_e i).1 v) (fun i j=>(h_e i).2 j) (opera_G P.Post.funds.1)
 refine ⟨V,hV,?_⟩; intro i U t' a hx Z v
 obtain ⟨h1,h2,h3,h4⟩:= hY'; obtain ⟨v1,v2,v3,v4⟩:= hY; have hB:0 ≤ B:= hib hW R; have hu: (r-1)=(r-2+1):=by omega
 have hp(X₀:SpaceX G (More c))(i:Site (More c))(hp:i∉ a.dome (r*radiusB x))(k:ℕ)(hi:2 ≤ k)(hu':k ≤4)(hR:Urge X₀ i 2 k p n σ (C*B) (A*B)): Allows n (X₀ ∘ Vmove x U) 0 (compass n k x (C*B) (A*B) t):= h4 S U a i (by rwa [show r-2+2=r by omega]) hx (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hU) X₀ 2 k p (C*B) (A*B) (by omega) hi (hu ▸ hS) hR
 constructor
 · have hK:0 ≤ v:=by unfold v compass composeCost vatP; positivity -- C*B
   have ht:0 ≤ compass n 2 x C A s:=by unfold compass composeCost vatP; positivity
   refine payW _ _ _ F V _ _ _ hV (mul_nonneg hC.le hB) (mul_nonneg he hB) hK _ ht (fun i j f v u p=> hp f i j _ le_rfl (by decide) ⟨v,u,p⟩) (fun i h=>?_) i; exact v4 S U a i (by rwa [show j-2+2=j by omega]) hx (Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hU) (F t' i) 2 2 R C A (by omega) le_rfl (Nat.mul_le_mul_right _ (by omega)) ((h_e t').1 i)
 intro j; have hv:= hV.power t' i; unfold Z; rw [riseU _ _ _ _ _ (p:=j) ht hV]; exact hp _ i (fun u=> j (farther (by omega) u)) _ (by decide) le_rfl hv
end YM.CF.Arena
