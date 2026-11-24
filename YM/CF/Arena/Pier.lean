import YM.CF.Rel.It
import YM.CF.Cay.Pric
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Arena
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open Jet Rel Stationary Push.Loops
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
section
variable {X:SpaceX G n}{i:Site n}{j:ℕ}
theorem coat(G:Gauge)(m r:ℕ):∃ N K,CapY N∧(∀ i,i ≤ N i) ∧ nib K∧ ∀ l:ℕ,∀ σ:ℝ,0<σ→σ ≤ 1→∀ B A:ℝ,∀{n:Side}(X:SpaceX G n)(p:Site n),m ≤ r→N l<n.val→CakeF X p l r σ A → cFoot m (satX X)→‖cake m (satX X)‖ ≤ B→ ∃ V:SpaceX G n, CakeF V p (N l) r σ (K l*B)∧ cFoot m (satX V) ∧ cFoot (m+1) (satX (X-V)):=by
 let N(i:ℕ):= i+payG i+tile (payG i); have hz:= dawn_m CapY.lives; have hN:CapY N:= (CapY.lives.add hz).add (sizeTile hz)
 obtain ⟨f,hF,h⟩:= fees G m r; let K(i):= payM m i*f (payG i)
 refine ⟨N,K,hN,fun i=>by unfold N; omega,(cCult m CapY.lives).mul (TargetV hF hz),?_⟩; intro l σ hs hk B A n X p hv hm hP hp hx
 have he: ContDiffAt ℝ (m:ℕ∞ω) (satX X) 0:= ((hP.ledger _ (by simpa using hs)).order hv).smooth
 obtain ⟨W,hW,hV,hY,hZ⟩:= oblige hP.toAtom he hp (by unfold N at hm; omega) hx
 let F(i):=fans p i (W i); let V:=∑ i,F i; have hp'(i):CakeF (F i) p (N l) r σ (‖W i‖*f (payG l)):=by
    by_cases hv:i∈ Pots p (payG l) m
    · exact (h _ _ _ hv _ (hV i)).under hk (by unfold N; omega) le_rfl
    rw [show F i=0 from by unfold F; rw [hY i hv]; rfl]; exact CakeF.zeroP (mul_nonneg (norm_nonneg _) (hib hF _)) -- tune
 have hg:CakeF V p (N l) r σ (K l*B):=by refine (CakeF.sigmaH univ fun i _=>hp' i).under le_rfl le_rfl ?_ ; rw [← sum_mul]; exact (mul_le_mul_of_nonneg_right hW (hib hF _)).trans_eq (by unfold K; ring)
 have hu:ContDiffAt ℝ (m:ℕ∞ω) (satX V) 0:= ((hg.ledger _ (by simpa using hs)).order hv).smooth
 let M:=trim m (satX X); let P(d:Disk n m)(v:InputZ G n):=engages W d (fun _=>v); have hP:M=∑ i,P i:=by ext1 i; rw [Finset.sum_apply]; exact hZ ..
 have ht:Rel.prism m V M:=by rw [hP]; exact Rel.prism.sumZ _ _ _ (fun i _=>fans_p _ _ _)
 have hh:Rel.prism m X M:= (argent he).mp hp
 have hrp:ContDiffAt ℝ (m:ℕ∞ω) (satX (X-V)) 0:=he.sub hu; have hr: Rel.prism m (X-V) 0:= sub_self M ▸ hh.sub ht
 exact ⟨V,hg,(asideF hu _ ht).1,nextF hrp hr⟩
end
lemma orbit_G (k:Site n)(F:FileM n G)(p:shapeV k F): F=Sean k (F 0):=funext fun i=> funext (p i)
-- lift from shapeV and projected Prox at all tags. Ruby first argument m≥3, analytic Cake each. head not required. shapeV zero, arbitrary n with k=0
open Cube
lemma trunkM (G:Gauge)(m:ℕ)(hG:G.Simple)(hm:5 ≤ m):∃ M K,CapY M ∧ (∀ i,i ≤ M i)∧ nib K∧∀ r:ℕ,∀ σ:ℝ,0<σ→σ ≤ 1→∀ C A:ℝ,0 ≤ C→ C ≤ A →∀{n:Side}(F:FileM (More n) G), shapeV 0 F→ M r<(More n).val → (∀ i,CakeF (F i) i r m σ A)→cFoot 2 (satX (F 0))→‖cake 2 (satX (F 0))‖ ≤ C→ (∀ i,3 ≤ i → i ≤4→Prox F i C) → ∃ D Q R, Travel 0 m 3 (M r) (M r) σ (A*K r) D ∧ CakeF Q 0 (M r) m σ (C*K r) ∧ CakeF R 0 (M r) m σ (A*K r) ∧ cFoot 2 (satX Q)∧ cFoot 5 (satX R) ∧ F 0+D=Q+ R:=by
 obtain ⟨p',K,hK,hK',hv,H⟩:=coat G 2 m; obtain ⟨N,T,hN,hN',hM,V⟩:=ruby G m 1 1 2 (by omega) (by omega)  (phi 0) (Or.inl (funext fun i=>by simp [phi])) -- ambiguous argument binder
 let X:= N ∘ p'; let P(i):=1+K i*(1+plot (p' i)); let M(i):=P i*T (p' i); let S(i):=K i+M i; let F(i):=1+(M i+M i)+S i
 have hp:nib P:= (nib_const _ zero_le_one).add (hv.mul ((nib_const _ zero_le_one).add (plot_n hK))); have ht:nib M:= hp.mul (TargetV hM hK); have hz:nib S:=hv.add ht; have hF:nib F:=((nib_const _ zero_le_one).add (ht.add ht)).add hz
 refine ⟨X,F,CapZ hN hK,fun i=>(hK' _).trans (hN' _),hF,?_⟩; intro r σ hσ hσ' C A hC hA n U hu hh hpX hx hvQ htU
 let p'':=p' r; let q:=K r; have h':p'' < (More n).val:= lt_of_le_of_lt (hN' _) hh
 obtain ⟨Q,hQ,v,w⟩:= H r σ hσ hσ' C A _ 0 (by omega) (by assumption) (hpX 0) hx hvQ
 let W:= U-Sean 0 Q; have hk(k:Site (More n)):W k=Sean 0 (U 0-Q) k:= by ext1 i; change U k i- pulseP 0 k* _=_; rw [hu k i]; exact (mul_sub ..).symm
 let e:=C*P r; let d:= A*P r; have ha:0 ≤ A:= hC.trans hA; have he:0 ≤ q:= hib hv r; have hf:P r≥0:=hib hp r; have hx:M r≥0:= hib ht r; have hy:F r≥ M r:=by unfold F; have hy:=hib hz r; linarith
 have hS:S r ≤ F r:=by unfold F; linarith
 have HW(k:Site (More n)): CakeF (W k) k p'' m σ d:=by
    have hb := (((hpX k).under le_rfl (hK' r) le_rfl).less (tide 0 k hQ)); unfold W; refine hb.under le_rfl le_rfl ?_; refine (add_le_add le_rfl (mul_le_mul_of_nonneg_left hA he)).trans ?_; have hg: 0 ≤ (plot p'':ℝ):=by positivity
    unfold d P; nlinarith only [mul_nonneg (mul_nonneg he ha) hg]
 have hpZ(x:ℕ)(p:1+2 ≤ x)(h:x < 1+2+2): Prox W x e:=by
    let g:ℕ:=x-1; have hg:x=g+1:=by omega
    have ha : ‖(0:InputZ G (More n))‖<σ:=by simpa using hσ
    have hi: x ≤ m:=by omega
    have ht:Prox (Sean 0 Q) x (plot p''*(q*C)):= hg.symm ▸ scopes (A:=q*C) g (fun i=> tide 0 i hQ) hσ (hg ▸ hi) -- tune
    have hh:= sunny (X:=W) (htU x (by omega) (by omega)) ht (fun i=> ((hpX i).ledger _ ha).smooth.of_le (by exact_mod_cast hi)) (fun i=> ((tide 0 i hQ).ledger _ ha).smooth.of_le (by exact_mod_cast hi)) (fun i=>((HW i).ledger _ ha).smooth.of_le (by exact_mod_cast hi)) (by simp [W,sum_sub_distrib]); intro i j; refine (hh i j).trans ?_; unfold e P; nlinarith only [mul_nonneg he hC]
 obtain ⟨D,R,hD,hR,v',u⟩:= -- hu physical energy terms
   (V p'' σ hσ hσ' d e (mul_nonneg ha hf) (mul_nonneg hC hf) (mul_le_mul_of_nonneg_right hA hf) _ 0 W hh (by rw [funext hk]; exact Sea 0 (U 0-Q)) (by simpa [gammaT] using (fitP n 0)) HW (by rw [hk 0,show Sean 0 (U 0-Q) 0=_ from stroll_z (U 0-Q) 0]; exact w) hpZ (fun h=>by omega)).legs
 -- tune
 let N:=U 0+D-(Q+R)
 have hp'':p'' ≤ X r:= hN' _; have ht :e*T p'' = C*M r:=by unfold e M; ring
 have haM:d*T p''=A*M r:=by unfold d M; ring
 have hz': CakeF (Q+R) 0 (X r) m σ (C*S r):= by apply ((hQ.under le_rfl hp'' le_rfl).add hR).under le_rfl le_rfl; rw [ht]; exact le_of_eq (by unfold S; ring)
 have hρ := (hD.cakeF hσ (by omega)).1
 have hg0: ‖(0:InputZ G (More n))‖<σ:=by simpa using hσ
 refine ⟨D,Q+R,N,hD.up (haM.le.trans (mul_le_mul_of_nonneg_left hy ha)) le_rfl le_rfl le_rfl le_rfl,hz'.under le_rfl le_rfl (mul_le_mul_of_nonneg_left hS hC),?_,merger v v' (by decide) ((hQ.ledger _ hg0).smooth.of_le (by exact_mod_cast (le_trans (by decide : 2 ≤ 5) hm))) ((hR.ledger _ hg0).smooth.of_le (by exact_mod_cast (le_trans (by decide : 2 ≤ 5) hm))),?_,by unfold N; abel⟩
 · refine ((((hpX 0).under le_rfl ((hK' _).trans hp'') le_rfl).add hρ).less hz').under le_rfl le_rfl (_root_.le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hA (hib hz _))) (le_of_eq ?_)); rw [haM]; unfold F; ring
 rw [show N=W 0+D-R from by change _= U 0-stroll 0 0 Q+D-R; rw [stroll_z]; unfold N; abel]; exact u
end YM.CF.Arena
