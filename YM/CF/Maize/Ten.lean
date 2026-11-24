import YM.CF.Maize.Pence
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Maize
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Gloss Floe Ave Phase.Sample Jet Pastry Drapes
variable {H e p a d r k D:ℝ}{n:ℕ}
lemma earned (p:0<a)(g:0<r)(v:r<1)(c:0<k) : ∃ σ:ℝ,0<σ∧ σ<1∧∀ (H:ℝ),∀ (t:1≤H) (b:ℝ), 0 < b → ∀ B : Side,∀ (k:ℝ),∀ᶠ n in atTop, Real.exp (k*21^4) * (16*(7*(B.val:ℝ)+1)^4*((4 * bulk a quota * (D*r^n))*(bond σ H n)^2))≤ b:=by
 let s:=Real.sqrt r; have hs:0<s:=Real.sqrt_pos.mpr g; have hx:s^2=r:= Real.sq_sqrt g.le; have ht:s<1:=by nlinarith
 obtain ⟨σ,hk,h⟩:= exists_between ht; have hS:=hs.trans hk; let q:=r/(σ^2); have he:0<q:=div_pos g (pow_pos hS _); have hQ:q<1:=by apply (div_lt_one (by positivity:0<σ^2)).mpr; nlinarith
 refine ⟨σ,hS,h,fun H h' b p' B k=>?_⟩; let W:=4*bulk a quota; let V:= Real.exp (k*21^4)*(16*(7*(B.val:ℝ)+1)^4); let f(n:ℕ):=V*((W*D*H^2)*q^n); have hh:Tendsto f atTop (𝓝 0):=((summable_geometric_of_lt_one he.le hQ).mul_left _|>.mul_left _).tendsto_atTop_zero
 filter_upwards [hh.eventually (gt_mem_nhds p')] with n s; apply le_trans _ s.le; apply le_of_eq; unfold f q bond V W; rw [div_pow,div_pow, ←pow_mul, pow_mul' σ]; ring -- tune
lemma cloth_K (b:0<r)(g:0<p)(hx:1≤H)(n:ℕ) : ∃ (σ:ℝ), 0<σ ∧ σ<1 ∧ ∃ M:ℕ, ∀ B:Side,M≤B.val → ∃ C:ℝ,0≤C ∧ ∀ (h:ℝ),∀ y:1≤h,∀ᶠ k:ℕ in atTop,∀ (e:ℝ), Room B e →∀ (m:Side) (f: Foot m B),∃ (t:1≤bond σ h k) (F: Stamp m B→ Train m B e→Ewe m B)(w:Stamp m B→ℝ), Construct m B _ t e k f r p F w ∧ ∀ S, shines e H n (F S) (bond σ h k) (C*w S):=by
 obtain ⟨a,v,s,d,p₁,p₂,p₃,p₄,p₅,Y⟩:=μLife
 obtain ⟨σ,hσ,t,A⟩:= earned (D:=s) p₁ p₄ p₅ b
 obtain ⟨M,h⟩:= exists_nat_gt (r*21^4/(a/2))
 refine ⟨σ,hσ,t,M,fun B u=>?_⟩; obtain ⟨C,z,E⟩:=shine_ink n B p₂ hx; have he: r*21^4≤a/2*(B.val:ℝ):= by apply le_trans (le_of_lt ((div_lt_iff₀ (half_pos p₁)).mp h)); rw [mul_comm]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast u) (half_pos p₁).le
 refine ⟨C,z,fun H' p'=>?_⟩; filter_upwards [A H' p' p g B r] with k hK m pY z₁ l; -- m:e pY room
 obtain ⟨h,v,b'⟩:=Y k; let z:= codify (m:=z₁) (B:=B) l
 obtain ⟨H₂,U',G,J,hq,w⟩:=tipV skin_CT (h z) p₂; obtain ⟨H₁,Qc,HQ,K,hQ,g'⟩:=tipV skin_CT (v z) p₂; obtain ⟨H₀,Ux,L,K',hL,J'⟩:= tipV skin_CT (b' z) p₂
 have hp: ∀ S:Stamp z₁ B,Linen (n:=Elf z₁ B) S (user H₂ p₂ S) (user H₁ p₂ S) (user H₀ p₂ S) (sigK _) (U' S) (Qc S) (Ux S):=fun S=>⟨J S,K S,K' S⟩
 let Q(y):=Linen.coins (U' y) (Qc y) (Ux y) * (bond σ H' k)^2; let V:=bond_good p' hσ t k; obtain ⟨T,D'⟩:=minted pY V hp p₁ hq hQ hL r b he
 refine ⟨V,(fun i=>sailm (H₂ i) (H₁ i) (H₀ i) p₂),Q,⟨fun S=>wand pY V (hp S),T,fun i=>(D' i).trans hK,fun x t=>?_⟩,fun i=> E _ _ pY _ V (G i) (HQ i) (L i)⟩
 let y: Post z₁ B:=⟨_,tenant_t pY t⟩; let R:= Floe.uθ y p₂; unfold sailm town; simp_rw [entrance (m:=z₁) (B:=B) (v:=none) (p:=stick 0) (q:=stick 0) (tenant_t pY t)]; rw [sum_quilt (n:=Elf z₁ B)]; unfold retire silt
 congr 1 -- tune
 · exact (pp_c _ _ _|>.symm.trans (w y))|>.symm
 · exact ((pe_c _ _ _).symm.trans (g' y)).symm
 exact ((pz_c _ _ _).symm.trans (J' y)).symm
end YM.CF.Maize
