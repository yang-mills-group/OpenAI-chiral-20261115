import YM.CF.BProof.Bias.Cascade
import YM.CF.BProof.Bias.Chordal
/-! lem:B-bias, with same R_M allowances as used by later movement of marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bias
open Function Filter Fock Finset Branch Tenant Cube SU Tulip Lat Lattice Dial Spin Fig Align Stint Wick Hearth
open Fir Laurent Rush Bloch Next.Free BZ Real Tape Mapping Angular Hero Dream Trek
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Kronecker Matrix.Norms.L2Operator Hearth Classical
attribute [local instance] opCStarAlgebra
variable {a b l r δ c v η g:ℝ}{j:ℕ} (P: Spin.Ready j a b l r) {K:ℕ}
-- describe layout/gauges at reference x. built separately.
variable {N:Side}(z:Fin 5){F:Core j a b l r N}
structure Portrait (z:Fin 5)(Y:Yard (More N))(x:Loft F δ c v η):Prop where
   ivory : Ivory x (StackS Y)
   call : Call (StackS Y) (bright Y) BB (BBz z) (LastC x)
structure ScopeP (D:ℕ) (P: Spin.Ready j a b l r)(δ c v g:ℝ)(t:ℕ)(z:Fin 5):Prop where
    claim {N:Side}{F:Core j a b l r N}{η:ℝ}{Y:Yard (More N)}(H:Honor P F δ)(x:Loft F δ c v η) (i:Y.Index): z≠0→ t≤N.val → 2*t<Y.long → Y.short≤D→ Portrait z Y x → ∃ y∈area Y i t,∀ x':Site N, time x'=y → Tape.bias x (node x')≤ -g
variable {P}
lemma Portrait.blank (h:1≤j)(H:Honor P F δ){Y:Yard (More N)}{x:Loft F δ c v η}(W:Portrait 0 Y x)(o:Site (More N)): Tape.bias x o=0:=by
 have he:= pure_vac x h ((show BBz 0=BB from BBz_zero) ▸ W.call) H W.ivory; apply Tape.bias_zero x o; change offCut (piF x.val.1) (pair (LastC x))*star _=_; rw [he,zero_mul]
variable (D:ℕ)(δ c v P)
lemma more (h:1≤j)(u:0<c)(X:1≤v): ∃ K g,0<g∧ScopeP D P δ c v g K z:=by
 by_cases p:z=0; exact ⟨1,1,one_pos,⟨fun _ _ _ t=> (t p).elim⟩⟩
 obtain ⟨r,n,f,k,g,H,S⟩:= Bias.expect δ c v P BB (BBz z) (BBz_diff p).symm X u h D -- tune signature args
 let d:=pairsZ r n+2*f; refine ⟨max (max d k) r,g,H,?_⟩; let A:=max (max d k) r; constructor; intro N F η Y h x i t w h' e W
 exact S.toll h _ x (area Y i (pairsZ r n)) (area Y i A) (bright Y) (StackS Y) ((le_trans (le_trans (le_max_right ..) (le_max_left ..)) w)) W.ivory W.call (currents Y i r n D (by have hv:r≤A:= le_max_right ..; change 2*A<_ at h'; omega) e) (area_up Y i (pairsZ r n) f A ((le_max_left ..).trans (le_max_left ..)))
variable {D P c δ v}
lemma ScopeP.up {g s:ℝ}{t t':ℕ}(p:ScopeP D P δ c v g t z)(u:t≤t')(v':s≤g): ScopeP D P δ c v s t' z:=by
 constructor; intro N F η Y h x i e y w g H; obtain ⟨q,f,B⟩:= p.claim h x i e (u.trans y) (by omega) g H; exact ⟨q,(areaT Y).mpr (Y.vic_nearer _ _ _ _ u ((areaT Y).mp f)),fun i T=>(B i T).trans (neg_le_neg v')⟩
variable (P δ c v D)
lemma bought (h:1≤j)(u:0<c)(X:1≤v):∃ K g,0<g∧∀ z:Fin 5, ScopeP D P δ c v g K z:=by
 choose R F g t using (fun i=> more δ c v P i D h u X); let v:=Fintype.ofFinite (Fin 5); let K:= univ.sup R; let T:=univ.inf' (univ_nonempty) F; refine ⟨K,T,(by unfold T; apply (lt_inf'_iff _).mpr; intro i _; exact g i),fun i=> ScopeP.up i (t i) (le_sup (f:=R) (mem_univ i)) (inf'_le F (mem_univ i))⟩
lemma bias_nonpos (x:Loft F δ c v η)(i:Site (More N)): Tape.bias x i≤0:=by obtain ⟨t,h⟩:= Tape.levy x i; exact t.trans (mul_nonpos_of_nonpos_of_nonneg (by norm_num) h)
end YM.CF.BProof.Bias
