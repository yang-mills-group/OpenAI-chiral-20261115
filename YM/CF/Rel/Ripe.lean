import YM.CF.Rel.Waves
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rel
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable{G:Gauge}{n:Side}{m l r:ℕ}{A C σ:ℝ}
open Stationary Push.Loops
variable {v:Axis→ℝ}{k:Site n}{F X:FileM n G}{x:Site n}{j M N:ℕ}{f g:SpaceX G n}{B:ℝ}
-- morning combination
structure Place (F:FileM n G)(k:Site n)(l:ℕ)(i t r:ℕ)(A C σ:ℝ): Prop where
 legs:∃ D Q:SpaceX G n, Travel k r i l l σ A D∧ CakeF Q 0 l r σ C∧ cFoot i (satX Q)∧ cFoot t (satX (F 0+D-Q))
lemma merger {Q H: SpaceX G n}(p:cFoot r (satX Q))(h:cFoot l (satX H))(hp:r ≤ l)(he:ContDiffAt ℝ r (satX Q) 0)(hf:ContDiffAt ℝ r (satX H) 0): cFoot r (satX (Q+H)):=by
 intro i hi; rw [show satX (Q+H)=satX Q+satX H from rfl,iteratedFDeriv_add_apply (he.of_le (by exact_mod_cast hi.le)) (hf.of_le (by exact_mod_cast hi.le)),p i hi,h i (hi.trans_le hp),add_zero]
lemma ruby(G:Gauge)(r j t h:ℕ)(he:j+2 ≤ r)(hl:j+2+h ≤ r+1)(v:Axis→ℝ) (hv:v=0∨∃ i, Exterior.q (axes v) i≠0):
 ∃ N K,CapY N∧(∀ l:ℕ,l≤ N l)∧ nib K ∧ ∀ l:ℕ,
 ∀ σ:ℝ, 0<σ→σ ≤ 1→∀ A C:ℝ,0 ≤ A →0 ≤ C→ C≤ A→∀ (n:Side)(k:Site n)(F:FileM n G),N l<n.val → shapeV k F→ Push.Loops.Matches (axes v) k→(∀ i,CakeF (F i) i l r σ A)→ cFoot (j+2) (satX (F 0)) →(∀ i:ℕ, j+2 ≤ i→ i< j+2+h → Prox F i C) → lunar j v k F (payG l) → Place F k (N l) (j+2) (j+2+h) r (A*K l) (C*K l) σ:=by
 induction h generalizing j with
 | zero=> refine ⟨fun n=>n,fun _=>0,CapY.lives,fun _=>le_rfl,nib_const _ le_rfl,fun _ _ ho ht _ _ H h k n a f hx hh hr he hw hp hq=> ?_⟩; refine ⟨0,0,Travel.stilt le_rfl (by positivity),CakeF.zeroP (by positivity),hatZ,?_⟩; simpa only [Nat.add_zero,sub_zero,add_zero] using hw
 | succ h ih=>
    by_cases hx:h=0; · subst hx; obtain ⟨N,K,hN,hK,H,hX⟩:=sunrise (G:=G) j r he v hv; refine ⟨N,K,hN,hK,H,fun l σ ho hσ A C ha hc hk n k F hn hF hv hp h hh hz=> ⟨(hX l σ ho hσ A C ha hc hk _ _ _ hn hF hv hp h (hh _ le_rfl (by omega)) hz).legs⟩⟩
    obtain ⟨M,T,hM,h₁,hT,H⟩:=sunrise (G:=G) j r he v hv
    obtain ⟨N,K,hN,h₂,hK,J⟩:= ih (j+1) (by omega) (by omega)
    let E(l:ℕ):=1+(3*T l+plot (M l)*T l)
    let P(l:ℕ):= E l*K (M l)+T l
    have hE:nib E:=(nib_const 1 zero_le_one).add (((nib_const 3 (by norm_num)).mul hT).add ((plot_n hM).mul hT));
    refine ⟨N ∘ M,P, CapZ hN hM,fun i=>(h₁ i).trans (h₂ _),((hE.mul (TargetV hK hM)).add hT),?_⟩
    intro l σ ho hσ A C ha hc hk n k F hn hF hv hp h₅ hh hz
    obtain ⟨D,Q,hD,hQ,HQ,Hd⟩:= (H l σ ho hσ A C ha hc hk n k F ((h₂ _).trans_lt hn) hF hv hp h₅ (hh _ le_rfl (by omega)) hz).legs
    let V:= Sean k (F 0+D-Q); let e:= T l; let t:= K (M l); let X:= A*E l; let C':= C*E l
    have hΩ:= hib hE l; have hΞ:= hib hT l
    have hg(i:Site n): V i= F i+Sean k D i-Sean k Q i:=by
       ext1 x; simp only [V,Sean,Pi.add_apply,Pi.sub_apply,mul_sub,mul_add, show F i x= _ from hF i x] -- tune
    have he0: V 0= _:=show V 0=F 0+D-Q from stroll_z ..
    have ht' : C'*t + C*e ≤ C*P l:=by unfold C' P e t; rw [mul_add]; exact le_of_eq (by ring)
    have hu:= mul_nonneg ha hΩ; have hy:= mul_nonneg hc hΩ
    have hR: ∀ i,CakeF (V i) i (M l) r σ X:=fun i=> by
       apply tide; apply ((((hp 0).under le_rfl (h₁ l) le_rfl).add (hD.cakeF ho he).1).less hQ).under le_rfl le_rfl
       apply (add_le_add le_rfl (mul_le_mul_of_nonneg_right hk hΞ)).trans; unfold X E; nlinarith only [ha,hΞ,show 0≤ A*plot (M l)*T l from by positivity]
    have hσ': ‖(0:InputZ G n)‖<σ:=by simpa using ho
    have HE(i)(hi:j+1+2 ≤ i)(hh': i < j+1+2+h):Prox V i C':=by
       have ht : i ≤ r:=by omega
       obtain ⟨d,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (show i ≠0 by omega)
       have he: (∑ i,V i)=(∑ i,F i)-∑ i, Sean k Q i:=by simp_rw [hg,sum_sub_distrib,sum_add_distrib,none_s hD]; abel
       have Hh:= sunny (hh (d+1) (by omega) (by omega)) (scopes d (fun i=>tide k i hQ) ho ht) (fun i=> ((hp i).ledger 0 hσ').smooth.of_le (by exact_mod_cast ht)) (fun i=> ((tide k i hQ).ledger 0 hσ').smooth.of_le (by exact_mod_cast ht)) (fun i=> ((hR i).ledger 0 hσ').smooth.of_le (by exact_mod_cast ht)) he
       intro i s; apply (Hh i s).trans; unfold C' E; nlinarith only [show 0≤ C*T l from by positivity]
    rw [←he0] at Hd
    obtain ⟨F',Q',HF,HQ',He,H'⟩:= (J (M l) σ ho hσ X C' hu hy (mul_le_mul_of_nonneg_right hk hΩ) n k V hn (Sea k _) hv hR Hd HE fun h=>by omega).legs
    let d:= N (M l); have h0: CakeF Q 0 d r σ (C*e):= hQ.under le_rfl (h₂ _) le_rfl
    refine ⟨F'+D,Q'+Q,?_,(HQ'.add h0).under le_rfl le_rfl ht',?_ ,?_⟩
    · apply ((HF.up le_rfl (show j+2 ≤ j+1+2 by omega) le_rfl le_rfl le_rfl).plus (hD.up le_rfl le_rfl (h₂ _) (h₂ _) le_rfl) ho he).up _ le_rfl le_rfl le_rfl le_rfl
      apply le_of_eq; unfold X P; ring
    · rw [add_comm Q' Q]; exact merger HQ He (by omega) ((hQ.ledger 0 hσ').smooth.of_le (by exact_mod_cast he)) ((HQ'.ledger 0 hσ').smooth.of_le (by exact_mod_cast he)) -- merger implicit unused
    rw [show F 0+ (F'+D) - (Q'+Q)=V 0+F'-Q' from by rw [he0]; abel]; rwa [show j+2+(h+1)=j+1+2+h from by omega]
end YM.CF.Rel
