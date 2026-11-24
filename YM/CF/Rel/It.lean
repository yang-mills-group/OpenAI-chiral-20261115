import YM.CF.Rel.Rim
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
open Cube
variable {F:FileM (More n) G}(p:LayerP n F){Z:G.Color→ₗᵢ[ℝ]G.Color}
lemma nib.sumV {α:Type}[Fintype α](f:α→ℕ→ℝ)(h:∀ i,nib (f i)): nib (fun k=> ∑ i,f i k):=by
 suffices he:∀ s:Finset α,nib (fun k=>∑ i∈s,f i k) from he _
 intro s; induction s using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact nib_const _ le_rfl
 | @insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i).add ih
lemma Cap_sumC{α:Type}[Fintype α](f:α→ℕ→ℕ)(h:∀ i,CapY (f i)): CapY (fun k=>∑ i,f i k):=by
 suffices he:∀ s:Finset α,CapY (fun k=>∑ i∈s,f i k) from he _
 intro s; induction s using Finset.induction_on with
 | empty=>simp only [sum_empty]; exact seedR _
 | @insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i).add ih
lemma condo (v:Charm)(h:phi v=0): v=0:=by by_contra hv; obtain ⟨i,hv⟩:= φ_pos v hv; exact hv (by simp [h,Exterior.q,axes])
lemma journey(G:Gauge)(C:G.Color→ₗᵢ[ℝ] G.Color)(hG:G.Simple)(m j t:ℕ)(p:j+2 ≤ m)(hw: j+2+t ≤ m+1):∃ M K,CapY M∧(∀ l:ℕ,l≤ M l)∧ nib K ∧
 ∀ l:ℕ,∀ σ:ℝ,0<σ→σ ≤ 1→∀ A B:ℝ,0≤ A →0≤B→B≤ A→∀ (n:Side)(F:FileM (More n) G), M l< (More n).val→ LayerP n F→(∀ i,CakeF (F i) i l m σ A)→(∀ i,cFoot (j+2) (satX (F i)))→(∀ i,j+2 ≤ i→i<j+2+t→ Prox F i B) → (j=0→Head (More n) C F)→∀ d:Charm, Place (laidC d n F) (gammaT n d) (M l) (j+2) (j+2+t) m (A*K l) (B*K l) σ:=by
 have he(d:Charm): phi d=0∨∃ i, Exterior.q (axes (phi d)) i≠0:=by
    by_cases hx:d=0; · exact Or.inl (funext fun i=> by simp [hx,phi])
    exact Or.inr (φ_pos d hx)
 choose M K hM hN hK h using fun d=>ruby G m j 0 t p hw (phi d) (he d)
 let E:=fun l:ℕ=> ∑ i,M i l; let X:=fun l:ℕ=> E l+ 10*(payG l+1); let V:=fun l:ℕ=>∑ i,K i l
 have hv:∀ l d,M d l ≤ X l:=fun l d=> (single_le_sum (f:=fun i=>M i l) (fun _ _=>Nat.zero_le _) (mem_univ d)).trans (Nat.le_add_right ..)
 refine ⟨X,V, (Cap_sumC M hM).add (((dawn_m CapY.lives).add (seedR 1)).scal 10),fun l=>(hN 0 l).trans (hv l _),nib.sumV K hK,?_⟩
 intro l σ ho h₀ A B ha hb hs n F hm hz hy hc ht hC d; let W:=laidC d n F; let p':=payG l; have hφ := mer hz d hy; have heQ : lunar j (phi d) (gammaT n d) W p' := by
    intro q he; have hΩ :=condo d he; have h₅:=hC q; refine ⟨by simp [hΩ,gammaT],?_⟩; have hp := hatch hz h₅; have hi:=p; rw [q] at hi; rw [hΩ] at hφ; unfold W; rw [hΩ]; apply clearF (hφ 0).toAtom hG ((hφ 0|>.ledger 0 (by simpa using ho)).smooth.of_le (by exact_mod_cast hi)) ?_ hp; unfold X at hm; change _ < _; omega
 obtain ⟨P,Q,hP,hQ,v,V'⟩:=(h d l σ ho h₀ A B ha hb hs _ _ W (lt_of_le_of_lt (hv l d) hm) (revive d n F) (fitP n d) hφ (slideY hz d 0 hc hy ho p) (fun i hi hu=> cash_s hz hy (ht i hi hu) ho (by omega) d) heQ).legs
 have H: K d l ≤ V l:=single_le_sum (f:=fun i=>K i l) (fun i _=>hib (hK i) _) (mem_univ d)
 exact ⟨P,Q,hP.up (mul_le_mul_of_nonneg_left H ha) le_rfl (hv ..) (hv ..) le_rfl,hQ.under le_rfl (hv ..) (mul_le_mul_of_nonneg_left H hb),v,V'⟩
end YM.CF.Rel
