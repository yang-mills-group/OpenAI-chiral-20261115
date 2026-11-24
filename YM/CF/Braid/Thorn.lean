import YM.CF.Braid.Jupiter
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
lemma finances{V:CurRun (t+1)→ Space t→ℂ}{k:Axis→ℝ}{m w:ℕ}{B D:ℝ}(hp:FootB V k m M A C)(h:M ≤ N)(ha:A≤ B)(he:C ≤ D): FootB V k w N B D:=by obtain ⟨X,hx,hP⟩:=hp; exact ⟨X,fun i=> (hx i).mono ha h, wallS.cheaper _ hP he h⟩
lemma get_smulM (t M R:ℕ)(A C D:ℝ):getPay t M R (A*C) (A*D)=A*getPay t M R C D:=by unfold getPay; ring
lemma billM(t M R:ℕ){A B C D:ℝ}(p:A≤ B)(hp:C≤ D):getPay t M R A C≤ getPay t M R B D:=by
    unfold getPay; have he:=mate_pos (t+1) R; have hk:0≤ topG 2:=by unfold topG; positivity; -- fix newline
    gcongr; exact rank_p ..
def PrimeP(t:ℕ)(v:Axis→ℝ)(N:ℕ→ℕ)(K:ℕ→ℝ):Prop:=∀ M A C,0≤ A→0 ≤ C → C ≤ A→ ∀ F: CurRun (t+2)→Space (t+1)→ℂ,(∀ i,Pond M A (F i))→ (∀ i,Pond M C (clipP F v i))→ FootB F v M (N M) (C*K M) (A*K M)
lemma palm0(t:ℕ)(θ:Axis→ℝ) (p:1+2*(t+1)>4∨∃ i,q (axes θ) i ≠ 0):∃ N K, CapY N ∧ nib K ∧ PrimeP t θ N K:=by
 have ht : ∃ D:ℝ, 0≤D∧(1+2*(t+1)>4∨∃ i:Axis,q (axes θ) i≠0∧ ‖(q (axes θ) i)⁻¹‖≤D):=by
    rcases p with he|⟨i,hi⟩; exact ⟨0,le_rfl,Or.inl he⟩; exact ⟨_,norm_nonneg _,Or.inr ⟨i,hi,le_rfl⟩⟩
 obtain ⟨D,hD,ht⟩:=ht
 let n:=t+1; let μ:= liftL n; let w(m):=m+μ m; let R(m):=paneR n 1 (w m+n); let T(m):= getRank t (w m) (R m)+w m; have hc:CapY w:= CapY.lives.add (paned n 0 CapY.lives); have hR:CapY R:=paned n 1 (hc.add (seedR n)); let ξ(m):=palmJ D n 0 m*mate n (μ m); have hξ:nib ξ:= (panned D n 0 hD CapY.lives).mul ((puff_m (paned n 0 CapY.lives)).pow n)
 let L(m):= getPay t (w m) (R m) (1+ξ m) ((1+ξ m)*topG 1^n*palmJ D n 1 (w m+n)); have hW:nib (fun m=> 1+ξ m):=(nib_const 1 zero_le_one).add hξ; have hL:nib L:=say_m t hc hR hW ((hW.mul ((ape 1).pow _)).mul (panned D n 1 hD (hc.add (seedR n))))
 refine ⟨T,ξ+L,(slimR t hc hR).add hc,hξ.add hL,fun M A C a c h F hf hp=> ?_⟩
 obtain ⟨i,j,u,p⟩:=hξ; obtain ⟨k,l,v,p'⟩:=hL
 have he:0≤ ξ M:= (p M).1; have hw:0≤ L M:= (p' M).1
 apply finances (carps θ t F A C D a c hD ht hf hp) le_rfl (mul_le_mul_of_nonneg_left (show ξ M ≤ ξ M+L M from le_add_of_nonneg_right hw) c)
 let z:=A+C*ξ M; have hk : z≤ A*(1+ξ M):=by rw [mul_add,mul_one]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h he)
 have hp : z*topG 1^n*palmJ D n 1 (w M+n) ≤ A*((1+ξ M)*topG 1^n*palmJ D n 1 (w M+n)):= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (by unfold topG; positivity)) (palm_pos D hD ..)).trans_eq (by ring)
 exact (billM _ _ (R M) hk hp).trans ((get_smulM ..).le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left he) a))
lemma pa:∃ N L,CapY N∧ nib L∧∀ M A C,0≤A→0 ≤ C→ C ≤ A→∀F:U2,Paid M A F→(∀ i,Pond M C (clipP F 0 i))→(∀ i:CurRun 2, Disjoint (i 0).val (i 1).val→ F i 0=0)→FootB F 0 M (N M) (C*L M) (A*L M):=by
 obtain ⟨K,B,h,H⟩:=roller
 let N:=har K; let Q(m):=asked (N m+1); let Y(m):= getRank 0 (N m) (Q m)+N m; let U(m):=tax0 m*(1+B); let V(m):= getPay 0 (N m) (Q m) (1+ U m) ((1+U m)*topG 1^1*payT2 (N m+1))
 have he:=tat_m CapY.lives; have hu:nib U:= he.mul (nib_const (1+B) (by linarith)); have hN:CapY N:=(CapY.lives.add (asked_c CapY.lives)).add (seedR K); have hx:CapY (fun m=> N m+1):=hN.add (seedR 1); have hQ:CapY Q:= asked_c hx; have ht:nib (fun m=>1+ U m):=(nib_const _ zero_le_one).add hu; have hv:nib V:=say_m _ hN hQ ht ((ht.mul ((ape 1).pow 1)).mul (hnd_m hx))
 refine ⟨Y,U+V,(slimR _ hN hQ).add hN,hu.add hv,fun M A C a c p F hf hp hw=> ?_⟩
 have hF:=earnedP K B h H a hf c hp hw; dsimp only at hF;
 rw [show C*tax0 M+C*tax0 M*B=C*U M from by unfold U; ring] at hF; obtain ⟨i,j,r,hh⟩:= hu; obtain ⟨k,l,s,hv⟩:=hv
 apply finances hF le_rfl (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hv M).1) c)
 let z:=A+C*U M; have he:0≤ U M:=(hh M).1
 have hz:z ≤ A*(1+U M):= by rw [mul_add,mul_one]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_right p he)
 have ht:z*topG 1^1*payT2 (N M+1) ≤ A*((1+U M)*topG 1^1*payT2 (N M+1)):= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz (by unfold topG; positivity)) (by unfold payT2 liftCost puff topG; positivity)).trans_eq (by ring)
 exact (billM _ _ (Q M) hz ht).trans ((get_smulM ..).le.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left he) a))
end YM.CF.Braid
