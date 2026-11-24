import YM.CF.DPress.FD.Warp.Merchant
/-!
# CSP receipts and assembly

 Invariant on every picked stencil extension step of the FD prescription.
 -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row
open Cube (More)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
abbrev Late(n:Side)(k:ℕ):Finset (Front n):= univ.filter (fun x=>∃ i:Fin 5, x=Sum.inr i ∧ k ≤ i.val)
lemma ClearV {F:rug n}{k:ℕ}: Skip F (Late n k)↔ ∀ i:Fin 5,k ≤ i.val →F (.inr i)=0:=by
 constructor; · intro p i h; exact p _ (by simp [Late,h])
 intro h i g; obtain ⟨i,rfl,t⟩:= (Finset.mem_filter.mp g).2; exact h i t
lemma ClearR (s:Sweep n){F:rug n}{k:ℕ}(v:Skip F (Late n k)):Skip (Tw.Ω s F) (Late n k):=ClearV.mpr fun i p=>by rw [η_w,ClearV.mp v _ p,win_z]
variable (s:Sweep n)(X:Clove n m)
lemma retire (S:MaskU n){F:Clove n m}{a:ℝ}(p:Tends S F a):Tends (ζ s⁻¹ S) ((clove n m).mv s F) a:=by
 obtain ⟨g,p,v,h⟩:=p; have hx (i:leaf n m)(k:i∈ facet (ζ s⁻¹ S)):ωr s⁻¹ i ∈ facet S:=by simpa only [inv_inv,ζ_rev] using (ω_f s⁻¹ k) -- inv_inv rfl?
 refine ⟨(clove n m).mv s g,⟨fun i t=>sheetX s (p (hx i t)),fun i t=> fitX s (v _ (hx i t)), fun i t j u=> ?_⟩⟩
 rw [valid_v,valid_v]; apply Eq.trans_le ((neat s).dist_eq ..); exact (h _ (hx i t) _ (hx j u)).trans_eq (by rw [ωT])
lemma reserve {N:ℕ} {F G: Clove n m}{a:ℝ}{S:MaskU n}(p: Receipt S (Late n N) a F G) : Receipt (ζ s⁻¹ S) (Late n N) a ((clove n m).mv s F) ((clove n m).mv s G):=by
 have ht (i:leaf n m)(v:i∈ boundary (ζ s⁻¹ S)): ωr s⁻¹ i ∈ boundary S:=by simpa only [inv_inv,ζ_rev] using (ω_b s⁻¹ v)
 refine ⟨fun i t=> congrArg ((chart n).mv s) (p.1 (ht i t)), fun i k=>ClearR s (p.2.1 (ωr s⁻¹ i) (?_)),retire s _ p.2.2⟩
 simpa only [inv_inv,ζ_rev] using (ω_f s⁻¹ k)
lemma Tay (Y:Clove n m)(S:MaskU n)(p:Set.EqOn X Y (boundary S)): Set.EqOn ((clove n m).mv s X) ((clove n m).mv s Y) (boundary (ζ s⁻¹ S)):=by intro i t; apply congrArg ((chart n).mv s); apply p; simpa only [inv_inv,ζ_rev] using (ω_b s⁻¹ t)
-- Polish proposal. Prepare universal ticket.
lemma shine (s:Sweep n){U V:Clove n m}{b:ℝ}{S:MaskU n}{N:ℕ}(p:Receipt (ζ s⁻¹ S) (Late n N) b ((clove n m).mv s U) V):Receipt S (Late n N) b U ((clove n m).mv s⁻¹ V):=by
 have h:=reserve s⁻¹ p; rwa [inv_inv,ζ_rev,(clove n m).vert] at h
structure ClerkK(n:Side)(m k:ℕ)(a:ℝ) where
 f : Cotton n→ MaskU n → Clove n m→ Clove n m
 m_p : ∀ c S,Measurable (f c S)
 good : ∀ c S X,(∃ g, Receipt S (Late n k) a X g)→ Receipt S (Late n k) a X (f c S X)
 w_p : ∀ S c c' X X', c S=c' S→ Set.EqOn X X' (boundary S) → f c S X=f c' S X'
 rot : ∀ c X S (i:Sweep n), f (act i c) (ζ i⁻¹ S) ((clove n m).mv i X)= (clove n m).mv i (f c S X)
lemma hires (a:ℝ): Nonempty (ClerkK n m r a):=by
 choose G h p t using (fun i:MaskU n=> poll (m:=m) i (Late n r) a); let V:= clove n m; let F(η:Cotton n)(i:MaskU n):= tune V V G (scale n) (η i) i
 refine ⟨{f:=F,m_p:=fun c S => (sane_M (c S)⁻¹).comp ((h _).comp (sane_M _)),good:=fun c S X x=>?_, w_p:=?_, rot:=?_}⟩
 · apply shine (c S); apply p; obtain ⟨f,g⟩:=x; exact ⟨V.mv (c S) f,reserve _ g⟩
 · intro S c d X Y v q; unfold F tune; rw [v,t]; apply Tay (d S) X Y S q
 intro c X S i; exact tune_v V V i c (scale n) S id (fun _=>rfl) X G
end Turf
end YM.CF.DPress.FD
