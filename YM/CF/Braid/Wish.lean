import YM.CF.Braid.Abs
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
-- merge
variable {F Y:U2}
def clipP(F:CurRun (t+1)→Space t→ℂ)(v:Axis→ℝ)(i:Run (t+1))(p:Space t):= fromCurl (cardR v p) (fun j=> F j p) i
def FootB (F:CurRun (t+1)→Space t→ℂ)(v:Axis→ℝ)(m M:ℕ)(C D:ℝ):=∃ Y:CurRun (t+1)→Space t→ℂ,(∀ i,Pond M C (Y i))∧ wallS (cardR v) M (t+1) D (F-Y)
lemma Pond.at0{f:Phase α→ℂ}(h:Pond M A f):‖f 0‖≤ A:=by obtain ⟨S,v,hp,hx,h⟩:=h.there; rw [h]; simp_rw [mode_constant,one_mul]; exact (norm_sum_le ..).trans hx
lemma press_0{F:U2} (h:∀ i, Pond M A (F i)):∀ i, Rays 2 (clipP F (0:Axis→ℝ) i ∘ axes):=by
 intro i; let m':= Embedding.refl (Keys 1); let X:=inlet F (strands m'); have hx:JetWall 1 X:=by
    intro p j; let u(p':Space 1)(i:TypeFace 2)(x:Unit):= F (Fin.cons p (Fin.cons i default)) p'; have hv: Board M A u:=fun i x=>h _
    have he(z:Phase (Keys 1)): X z p j=cob 1 (projected (stick 0)) u z (j 0) ():=by unfold X inlet; rw [fromCurl_cons]; unfold cob Matrix.mulVec dotProduct; refine sum_congr rfl fun i _=>?_ ; unfold fromCurl; simp; rfl
    simp_rw [he]; exact jets_cob (ray_symbol (stick 0)) (excited hv) _ _
 have hm(p :Corn (Keys 1)): clipP F 0 i (axes p)= cob 1 missing X (axes p) (i 0) (Fin.tail i):=by
    unfold clipP; rw [fromCurl_cons]; simp only [cardR,twist0, Fin.cons_zero,Fin.tail_cons]; rfl
 change Rays _ (fun p=> clipP F 0 i (axes p)); simp_rw [hm]; exact miss_jet hx _ _
def har (t:ℕ)(m:ℕ):ℕ:=m+Mimi m+t
abbrev tax0(m:ℕ):= handC m*mate 1 (Mimi m)
lemma earnedP(K:ℕ)(B:ℝ)(h:0≤B)(hp:∀ (m:ℕ)(A E:ℝ)(F:U2),0 ≤ A→0 ≤ E→ Fall F 0 → Paid m A F→(∀ i,‖F i 0‖ ≤ E) →∃ Y:U2, Fall Y 0∧Paid K (E*B) Y∧ ∀ i,Y i 0=F i 0)(he:0 ≤ A)(hf:Paid M A F)(hc:0 ≤ C)(hm:∀ i,Pond M C (clipP F 0 i))(hv: ∀ i:CurRun 2, Disjoint (i 0).val (i 1).val → F i 0=0) :
 let N:=har K M; let Q:=asked (N+1); let X:=C*tax0 M; let x:= X + X*B; let h':= A+x
 FootB F 0 M (getRank 0 N Q+N) x (getPay 0 N Q h' (h'*topG 1^1*payT2 (N+1))):=by
 intro N Q X x h'; let m:=clipP F 0
 have hw : cardR (t:=1) (0:Axis→ℝ)=plotted := by unfold plotted cardR; rw [twist0];
 have hh: Contractible m:=by intro p i b; rw [← hw]; exact chr (cardR (0:Axis→ℝ) (axes p)) (fun j=> F j (axes p)) i b
 obtain ⟨b,hb,hh,hB⟩:=twoP M C 0 m hc hm hh (press_0 hf)
 rw [← hw] at hB
 have hx :0 ≤ X:= mul_nonneg hc (mul_nonneg (by unfold handC liftCost topG puff; positivity) (mate_pos ..))
 have ht :0 ≤ x:= add_nonneg hx (mul_nonneg hx h); have hz:0 ≤ h':=add_nonneg he ht
 have hL:M ≤ N:=by unfold N har; omega
 have hJ:Mimi M ≤ N:=by unfold N har; omega
 have hk:K ≤ N:=by unfold N har; omega
 have hb(i): Pond N X (b i):= (hb i).mono (mul_assoc ..).le hJ
 let D:=F-b; have hD:Paid N (A+X) D:= fun i=> ((hf i).mono le_rfl hL).rest (hb i)
 have hΛ:Fall D 0:=by
    intro i; rw [show (fun j=> D j (axes i))=(fun j=>F j (axes i))-fun j=> b j (axes i) from rfl, sub_p]; ext1 k; simp only [Pi.sub_apply,hB]; exact sub_self _
 obtain ⟨w,hy,hy',hy₁⟩:=hp N (A+X) X D (add_nonneg he hx) hx hΛ hD (by
    intro i; by_cases H:Disjoint (i 0).val (i 1).val
    · change ‖F i 0-b i 0‖ ≤ _; rw [hv i H,zero_sub,norm_neg]; exact (hb i).at0
    obtain ⟨k,hk,hj⟩:= Finset.not_disjoint_iff.mp H; rw [void_0 hD hΛ i k hk hj,norm_zero]; exact hx)
 let Z:= D-w; have hE:Paid N h' Z:=fun i=> ((hD i).rest ((hy' i).mono le_rfl hk)).mono (le_of_eq (add_assoc ..)) le_rfl
 let W:=getRank 0 N Q
 refine ⟨b+w,fun i=> ((hb i).add ((hy' i).mono le_rfl hk)).mono le_rfl (Nat.le_add_left ..),?_⟩
 rw [show F-(b+w)=Z from by unfold Z D; abel]
 have hv':Fall Z 0:=fun i=>(sub_p (cardR 0 (axes i)) (fun j=> D j (axes i)) (fun j=>w j (axes i))).trans (by rw [hΛ i,hy i,sub_self])
 have hP:∀ i,Rays 1 (Z i ∘ axes):=by
    intro i; apply (rays_at_zero ((hE i).analytic.analytic_real _)).mpr; rw [Function.comp_apply,show axes (0:Corn (Keys 1))=0 from funext fun i=>by simp [axes]]; exact sub_eq_zero.mpr (hy₁ i).symm
 exact wallS.cheaper _ (big2 hz hE hP hv') le_rfl (Nat.le_add_right ..)
end YM.CF.Braid
