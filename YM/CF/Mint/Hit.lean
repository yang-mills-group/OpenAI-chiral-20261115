import YM.CF.Mint.Cash
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mint
open Function NormedSpace Filter Finset Graph Lattice Laurent Wilson Analysis Pressure Tulip Lat Cube SU Emu Rush Scree Graph RG Scroll Peaks Drapes Cascade Vault Sods Spire Paige Nova Girt Skye Kea Ember
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {x y A:ℕ→ℝ}{c b w η r a e K b' v C' l s' γ μ τ H m L':ℝ}{S T:ℕ→Side}{β θ V L1 δ L:ℕ→ℝ}{J B:Side}{O:Odd J.val}{j k:ℕ}{Y:Pricing j J O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}
-- nonuniform sequences. loop exponent update tracks budget. 
namespace Roe
variable {N:ℕ→Side} (D:Pic.Span hP K b' v C' l s' k) {I:∀ i,GramM (mid (N i) B)} {C Q h:ℝ}
local notation "NP"=> (fun i=> mid (N i) B)
variable (Z:WindS B N x h C r μ L' w γ c b V θ L I)
include D Z
open MeasureTheory Fock Dial
variable (F:∀ i,Loom (mid (N i) B)) (W:∀ᶠ i in atTop,SkinT (I i) (F i) e) {d vA r₀ C₀ E':ℝ}{n₀:ℕ} (U:Port D d E' C₀ vA r₀ n₀)(g:C₀ ≤h)
omit D Z
lemma tone_l{A B:ℕ→ℂ}(h:Tendsto A atTop (𝓝 0))(p:∀ᶠ i in atTop,‖B i‖≤w) : Tendsto (fun i=>A i*B i) atTop (𝓝 0):=by rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢; exact squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) (p.mono fun i u=> (norm_mul ..).trans_le (mul_le_mul_of_nonneg_left u (norm_nonneg _))) (by simpa only [zero_mul] using h.mul_const w)
lemma power_v {Z X M G:ℕ→ℂ}{P:ℕ→ℝ}(p:∀ᶠ i in atTop,0<P i∧ M i≠0∧P i*b≤‖G i‖)(e:Tendsto (fun i=>(Z i-X i)/(P i:ℂ)) atTop (𝓝 0))(q:Tendsto (fun i=>(M i-G i)/(P i:ℂ)) atTop (𝓝 0))(h:0<b)(k:ℂ)(hp:Tendsto (fun i=>X i / M i) atTop (𝓝 k)): Tendsto (fun i=>Z i/G i) atTop (𝓝 k):=by
 let y(i):=(P i:ℂ)/G i; have hz:∀ᶠ i in atTop,G i ≠0:=p.mono fun i ⟨w,v,g⟩=>norm_pos_iff.mp ((mul_pos w h).trans_le g)
 have he:∀ᶠ i in atTop,‖y i‖≤b⁻¹:=by filter_upwards [p,hz] with i ⟨g,p,k⟩ v; unfold y; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg g.le, div_le_iff₀ (norm_pos_iff.mpr v)]; exact le_trans (le_of_eq (show P i= b⁻¹*(P i*b) from (by field_simp))) (mul_le_mul_of_nonneg_left k (by positivity))
 have ht:= (tone_l e he).add (hp.mul ((tone_l q he).add_const 1)); simp only [zero_add,mul_one] at ht; apply ht.congr'; filter_upwards [p,hz] with i ⟨g,p,k⟩ v; have he:(P i:ℂ) ≠0:=by exact_mod_cast g.ne'
 change (Z i-X i)/_ * y i + X i / M i * ((M i-G i)/_ * y i +1) = _; unfold y; field_simp; ring
end Roe
end YM.CF.Mint
