import YM.CF.Rel.Votes
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
variable {v:Axis→ℝ}{k:Site n}{F:FileM n G}{o:Site n}{j s N M:ℕ}
def stormM(t m:ℕ):ℕ:= pcost (t+1) m+cSize t (pcost (t+1) m)
open Jet
lemma pollen(h:0<σ){x:Site n}{f:SpaceX G n}(p:CakeF f x r s σ A)(h':j ≤ s) : ‖cake j (satX f)‖≤ A:=by
 have hv:=p.ledger 0 (by simpa using h); apply le_trans _ (hv.norm_le _ h'); unfold cake; rw [norm_smul]; apply mul_le_of_le_one_left (norm_nonneg _); rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos j)
-- connection budgets for singular decomposition
lemma sappy{B:ℝ} (l n':ℕ)(h:shapeV k F)(hp:Push.Loops.Matches (axes v) k)(he:0≤ A)(hc:0≤ C)(σ:ℝ)(ht:0<σ)(hσ:σ ≤ 1)(hf:∀ i,CakeF (F i) i M s σ A)(hs: n'+2 ≤ s)(hF:cFoot (n'+2) (satX (F 0)))(hr:payG M<n.val)(hy: Prox F (n'+2) C)(hZ:2*cSize n' (pcost (n'+1) (payG M))<n.val)(f:ℕ→ℝ)(HG:∀ i,0≤ f i)(H:∀ u:ℕ,∀{n:Side}(o:Site n)(P:Disk n (n'+2)),P∈Pots o u (n'+2)→∀ z:Delph G (n'+2),Trade z→CakeF (fans o P z) o (tile u) s 1 (‖z‖*f u))
 (hq:∀ W: KitM G n (n'+2), (∑ i,‖W i‖) ≤ payM (n'+2) M*A→(∀ i,Trade (W i))→ nerve 0 (payG M) W → (∀ u,cake (n'+2) (satX (F 0)) u=∑ p, engages W p u) → ∀ a:SpotG G (n'+2), let T:= breathL W k a; let V:=stormM n' (payG M); (∀ i,Pond V (payM (n'+2) M*A) (T i)) → (∀ i,Pond V (paysV n' (payG M) M*C) (clipP T v i))→ FootB T v M l (C*B) (A*B))
 (ho:2*l<n.val)(hX:payG M+tile (payG M) ≤ N)(hN:tile (l+1)+1 ≤ N):
 ∃ D Q:SpaceX G n, Travel k s (n'+2) N N σ (payM (n'+2) M*A*f (payG M)+capMult G (n'+1)*(A*B)*f (l+1)) D ∧ CakeF Q 0 N s σ (qMult G (n'+1)*(C*B)*f l)∧ cFoot (n'+2) (satX Q) ∧ cFoot (n'+3) (satX (F 0+D-Q)):=by
 have h0: ‖(0:InputZ G n)‖<σ:=by simpa using ht
 have hv(i):ContDiffAt ℝ (↑(n'+2:ℕ):WithTop ℕ∞) (satX (F i)) 0:= ((hf i).ledger 0 h0).smooth.of_le (by exact_mod_cast hs)
 obtain ⟨W,hW₀,hW,p₀,p'⟩:=oblige (hf 0).toAtom (hv 0) hF hr (pollen ht (hf 0) hs); let R:=pcost (n'+1) (payG M); let J:= stormM n' (payG M)
 have ha :0 ≤ payM (n'+2) M*A:=(Finset.sum_nonneg fun _ _=>norm_nonneg _).trans hW₀
 have hk(a:SpotG G (n'+2))(i): Pond J (paysV n' (payG M) M*C) (clipP (breathL W k a) v i):=(lensF h hp p₀ ha hc hW₀ hy (fun i=>(hf i).toAtom) hv p' hZ a i).mono le_rfl (Nat.le_add_left ..) -- tune exponent order
 choose X HX V hP hQ P using fun a=> hq W hW₀ hW p₀ p' a (fun i=> (forda W p₀ k a i hW₀).mono le_rfl (Nat.le_add_right ..)) (hk a)
 let D:=intoX W k; let E:=intoY V k; let Q:=intoQ X (n:=n)
 have hx:Travel k s (n'+2) N N σ (payM (n'+2) M*A*f (payG M)) D:=(poly_x f H p₀ hW hW₀ hs (HG ..)).up le_rfl le_rfl hX hX hσ
 have hy:Travel k s (n'+2) N N σ (capMult G (n'+1)*(A*B)*f (l+1)) E:= (polY f H HG (X:=V) hQ ho hs).up le_rfl le_rfl hN hN hσ
 obtain ⟨hK,hπ⟩:=paceQ f H HG HX ho hs
 have hqθ:CakeF Q 0 N s σ (qMult G (n'+1)*(C*B)*f l):= hK.under hσ (by unfold tile at *; omega) le_rfl
 let π:= hx.plus hy ht hs
 refine ⟨D+E,Q,π,hqθ,hπ,?_⟩
 have hw:prism (n'+2) (F 0) (fun x=>∑ p,engages W p (fun _=>x)):=by
    have he:= (argent (hv 0)).mp hF; unfold trim Tensor.diagonal at he; simp_rw [p'] at he; exact he
 apply nextF _ (dent_x (m:=n'+1) V X k W v hp (F 0) hw hW hP P); apply ContDiffAt.of_le (n:=s) _ (by exact_mod_cast hs); exact (((((hf 0).under le_rfl (show M ≤ N from by unfold payG at hX; omega) le_rfl).add (π.cakeF ht hs).1).less hqθ).ledger 0 h0).smooth
end YM.CF.Rel
