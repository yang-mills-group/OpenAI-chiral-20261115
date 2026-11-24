import YM.CF.Rel.Shive
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
-- cost polynomials allow M=n-growth
lemma CapZ {f g:ℕ→ℕ}(hf:CapY f)(h:CapY g): CapY (f∘g):=by obtain ⟨a,hp⟩:=hf; obtain ⟨b,h⟩:= (seedR 1).add h; refine ⟨a*b,fun M=>?_⟩; rw [Nat.mul_assoc]; exact (hp _).trans (Nat.mul_le_mul_left a (h _))
lemma TargetV {f:ℕ→ℝ}{g:ℕ→ℕ}(hf:nib f)(hg:CapY g): nib (fun i=>f (g i)):=by
 obtain ⟨K,n,hn,hQ⟩:=hf; obtain ⟨v,hv⟩:= (seedR 1).add hg; refine ⟨K*v^n,n,mul_nonneg hn (by positivity),fun i=>⟨(hQ _).1,?_⟩⟩
 rw [mul_assoc,←mul_pow]; exact ((hQ _).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (hv i)) n) hn))
lemma hib{v:ℕ→ℝ}(hp:nib v)(x:ℕ):0 ≤ v x:=by obtain ⟨_,_,_,he⟩:=hp; exact (he _).1
def lunar(m:ℕ)(v:Axis→ℝ)(k:Site n)(F:FileM n G) (r:ℕ):Prop:= m=0 → v=0→ k=0∧ Ridge (F 0) r
lemma dawn_m {f:ℕ→ℕ}(h:CapY f):CapY fun x=> payG (f x):=(((h.add (seedR 1)).scal 9).add (seedR 1))
lemma drips (t:ℕ) {p:ℕ→ℕ}(h:CapY p): CapY fun x=>pcost t (p x):= ((h.scal 2|>.scal 4).scal t)
lemma lambL(t:ℕ){p:ℕ→ℕ}(h:CapY p):CapY fun x=> cSize t (p x):= drone t (h.add (seedR _))
lemma bet_m(t:ℕ){p:ℕ→ℕ}(h:CapY p):CapY fun x=>stormM t (p x):=(drips _ h).add (lambL _ (drips _ h))
lemma sizeTile{p:ℕ→ℕ}(h:CapY p):CapY fun x=> tile (p x):= ((h.scal 4|>.scal 2).add (seedR 4))
lemma plot_n{p:ℕ→ℕ}(h:CapY p):nib fun x=>(plot (p x):ℝ):=by unfold plot; simp_rw [Nat.cast_pow]; exact (nib.mate ((h.add h).add (seedR 1))).pow 4
lemma cCult(t:ℕ){p:ℕ→ℕ}(h:CapY p):nib fun x=>payM t (p x):=by
 have hi : nib fun x=> payF (p x):= (nib_const (4:ℝ) (by positivity)).mul ((nib.mate (dawn_m h)).pow _)
 simp_rw [payM,Nat.cast_pow,Nat.cast_mul]; exact (hi.pow _).mul (((plot_n h).mul (nib_const _ (Nat.cast_nonneg (Fintype.card Axis)))).pow _)
lemma pry(t:ℕ){u v:ℕ→ℕ}(h:CapY u)(p:CapY v):nib fun x=> paysV t (u x) (v x):=by unfold paysV; push_cast; exact ((plot_n (lambL t (drips _ h))).pow _).mul ((plot_n (p.scal 2)).pow _)
-- discharge mire
lemma brake (m:ℕ)(v:Axis→ℝ)(h:v=0∨∃ i, Exterior.q (axes v) i ≠ 0): ∃ N K,CapY N∧ nib K∧∀ M A C, 0 ≤ A→0≤ C→ C ≤ A→∀ F:CurRun (m+2)→Space (m+1)→ℂ,(∀ i,Pond M A (F i))→(∀ i,Pond M C (clipP F v i))→(m=0→v=0→∀ i:CurRun (m+2), Disjoint (i 0).val (i 1).val→ F i 0=0)→ FootB F v M (N M) (C*K M) (A*K M):=by
 by_cases hx:m=0∧ v=0; swap
 · have he : 1+2*(m+1)>4∨∃ i, Exterior.q (axes v) i≠0:=by
      rcases h with h | h
      · exact Or.inl (by simp only [h, and_true] at hx; omega)
      exact Or.inr h
   obtain ⟨N,K,hN,hK,h⟩:= palm0 m v he; exact ⟨N,K,hN,hK,fun M A C a c p F hf hp _=> h M A C a c p F hf hp⟩
 rcases hx with ⟨rfl,rfl⟩; obtain ⟨N,K,hN,hK,h⟩:=pa; exact ⟨N,K,hN,hK,fun M A C a c p F hf hp hh=> h M A C a c p F hf hp (hh rfl rfl)⟩ -- tune shadow
structure Jump (p:ℕ)(s:ℕ) (F:SpaceX G n)(k:Site n)(l:ℕ)(M A σ: ℝ):Prop where
 legs:∃ D Q:SpaceX G n, Travel k s p l l σ M D∧ CakeF Q 0 l s σ A ∧ cFoot p (satX Q)∧ cFoot (p+1) (satX (F+D-Q))
lemma sunrise {G:Gauge}(m t:ℕ)(ht:m+2 ≤ t)(v:Axis→ℝ)(h:v=0∨∃ i, Exterior.q (axes v) i≠0) : ∃ N K,CapY N∧(∀ l:ℕ,l≤ N l)∧ nib K∧∀ l:ℕ,
 ∀ σ:ℝ,0<σ→σ ≤ 1→∀ A C:ℝ,0≤ A →0 ≤ C→ C≤ A→∀ (n:Side)(k:Site n)(F:FileM n G),N l<n.val → shapeV k F→ Push.Loops.Matches (axes v) k→(∀ i,CakeF (F i) i l t σ A)→ cFoot (m+2) (satX (F 0)) → Prox F (m+2) C → lunar m v k F (payG l) → Jump (m+2) t (F 0) k (N l) (A*K l) (C*K l) σ:=by
 obtain ⟨N,K,hN,hK,p⟩:=brake m v h; obtain ⟨f,hf,Hf⟩:=fees G (m+2) t
 let s (i):= N (stormM m (payG i)); let Z (i):= cSize m (pcost (m+1) (payG i)); have hZ:CapY Z:=lambL _ (drips _ (dawn_m CapY.lives))
 let Λ (i):=payG i+tile (payG i)+(tile (s i+1)+1+2*s i)+2*Z i+i; have hs:CapY s:= CapZ hN (bet_m _ (dawn_m CapY.lives));
 let Q (i):=payM (m+2) i+paysV m (payG i) i; have hp':=pry m (dawn_m CapY.lives) CapY.lives; let B (i):= Q i*K (stormM m (payG i)); have hB:nib B:= ((cCult (m+2) CapY.lives).add hp').mul (TargetV hK (bet_m _ (dawn_m CapY.lives)))
 let J (i):= payM (m+2) i*f (payG i)+capMult G (m+1)*B i*f (s i+1); have hJ:nib J:= ((cCult (m+2) CapY.lives).mul (TargetV hf (dawn_m CapY.lives))).add (((nib_const _ (Nat.cast_nonneg (Fintype.card _))).mul hB).mul (TargetV hf (hs.add (seedR 1)))) -- tune
 let U (i):= qMult G (m+1)*B i*f (s i); have hU:nib U:= ((nib_const _ (Nat.cast_nonneg (Fintype.card _))).mul hB).mul (TargetV hf hs)
 refine ⟨Λ,J+U,?_,fun i=>by unfold Λ; omega,hJ.add hU,?_⟩
 · let P:CapY payG:=dawn_m CapY.lives; exact ((((P.add (sizeTile P)).add (((sizeTile (hs.add (seedR 1))).add (seedR 1)).add (hs.scal 2))).add (hZ.scal 2)).add CapY.lives)
 intro l σ ho hσ A C ha hb hk n k F hr hφ hc hP hp hT hg -- adapt
 let y:=payM (m+2) l; let M:=stormM m (payG l); let t':=paysV m (payG l) l
 have hQ : ∀ V:KitM G n (m+2), (∑ i,‖V i‖) ≤ y*A→(∀ i,Trade (V i))→ nerve 0 (payG l) V → (∀ u,cake (m+2) (satX (F 0)) u=∑ p, engages V p u) → ∀ a:SpotG G (m+2), let T':= breathL V k a; (∀ i,Pond M (y*A) (T' i)) → (∀ i,Pond M (t'*C) (clipP T' v i))→ FootB T' v l (s l) (C*B l) (A*B l) :=by
    intro V Hv hI hY H a X hx he
    have hv:0≤ t':=hib hp' _; have hy:0 ≤ y:=by unfold y payM payF; positivity
    have hw:0 ≤ Q l:= add_nonneg hy hv; have hu :0 ≤ K M:= hib hK M
    have hf : t'*C ≤ C*Q l:= (mul_comm ..).le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hy) hb)
    apply finances (p M (A*Q l) (t'*C) (mul_nonneg ha hw) (mul_nonneg hv hb) (hf.trans (mul_le_mul_of_nonneg_right hk hw)) _ (fun i=> (hx i).mono ((mul_comm y A).le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) ha)) le_rfl) he ?_) le_rfl ((mul_le_mul_of_nonneg_right hf hu).trans_eq (mul_assoc ..)) (mul_assoc ..).le
    intro h hv i hi; have h':=hg h hv; obtain ⟨hg,hS⟩:= h'; subst h; subst k; exact moneyV (F 0) V hY hS H a i hi
 obtain ⟨D,Y,hD,he,h₁,h₂⟩:= sappy (s l) m hφ hc ha hb σ ho hσ hP ht hp (by unfold Λ at hr; omega) hT (by change _*Z l < _; unfold Λ at hr; omega) f (hib hf) Hf hQ (by unfold Λ at hr; omega) (show _ ≤ Λ l from by unfold Λ; omega) (by unfold Λ; omega)
 let P:=Λ l
 refine ⟨D,Y,hD.up ?_ le_rfl le_rfl le_rfl le_rfl, he.under le_rfl le_rfl ?_,h₁,h₂⟩
 · apply le_trans (le_of_eq (show _=A*J l from by unfold J; ring)); exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hib hU _)) ha
 apply le_trans (le_of_eq (show _=C*U l from by unfold U; ring)); exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hib hJ _)) hb
end YM.CF.Rel
