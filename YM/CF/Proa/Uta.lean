import YM.CF.Proa.Fro
set_option autoImplicit false
noncomputable section
namespace YM.CF.Proa
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Phase Spire
set_option synthInstance.maxSize 8000
open Acorn
open MeasureTheory Jet Phase.Sample
variable {U D Y n ι:Type}{j N:ℕ}{a v K P e h:ℝ}
lemma profile_X(N:ℕ)(P:ℝ)(p:0≤P) :∃ Y:ℝ,0≤Y∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{n:Side}(f:E→Bkg (More n))(x),TransK N f x P→ Allows N (profile ∘ f) x Y:=by
 obtain ⟨c,h,H⟩:= compact_allow N p SU.triple trie
 let Z:=max (composeCost N c P) P; let W:=starL' ℝ (A:=Twig); let A:= max Z (‖W.toContinuousLinearMap‖*Z); have he:P≤Z:=le_max_right ..; have hl:Z≤A:=le_max_left ..
 refine ⟨A,(p.trans he).trans hl,@fun E _ _ n f x g=>?_⟩
 refine allows_pi ((p.trans he).trans hl) fun i=>allows_pi ((p.trans he).trans hl) fun u=>?_
 let t:= g i
 have hx: Allows N (fun y=>brand (f y i)) x Z:= (((H _ t.value).comp (f:=fun x=> SU.fund (f x i)) t).mono (le_max_left ..)).pair (t.mono he)
 cases u; exact (hx.linear W.toContinuousLinearMap le_rfl).mono (le_max_right ..); exact hx.mono hl
lemma victoria (N:ℕ)(P:ℝ)(b c d:ℝ)(g:0≤P)(w:0<d)(ht:0<b)(hr:0<c):∃ C:ℝ,0<C∧∀ m B:Side,let G:= idrat (CSide m B); ∀ e:ℝ,0<e→ e ≤ d→ ∀ K:Coil (CSide m B) (CSide m B)→Op (Iota G),Crown (badge _) (temper G d) (temper G d) b c (fun x=> K x.val)→ Plum (newX (Spire.soar m B e) (aether N P e m B) N) (tempo G 1).home (fun x=>cue false true (K (unionP (x.val,x.val)))) (b/2) C:=by
 obtain ⟨a,v,H⟩:= profile_X N P g
 let M:=(1+2^N/d)^N; let C':= max 1 (composeCost N M a); have hp:1≤ C':=le_max_left ..; let K:=max c (quartzK b c); have hy:c≤K:=le_max_left ..; refine ⟨C'*K,mul_pos (lt_of_lt_of_le one_pos hp) (hr.trans_le hy),?_⟩; intro m B G e he hu A hk
 obtain ⟨F,C,h,T,U⟩:=hk; let X:=newX (Spire.soar m B e) (aether N P e m B) N
 let f(x:CapX m B e):↑(legal G d):= ⟨_,ambient _ _ he hu (jointly x.val x.property he)⟩
 have hf:Continuous f:= by unfold f; exact (((profile_c.comp continuous_subtype_val).prodMk (profile_c.comp continuous_subtype_val))).subtype_mk _
 let V(S)(x):= F S (f x)
 have hx(S:Broc.Table m B)(i j:Iota G): Pro X S (fun x=>V S x i j) (C'*C S i j):=by
    let p:=(h S).expo i j; let W:=fun x=> F S x i j
    refine ⟨mul_nonneg (zero_le_one.trans hp) p.positive,fun e=>(p.triggered (right_ne_zero_of_mul e)).1,p.connected.comp hf,fun x=>(p.bounded _).trans (le_mul_of_one_le_left p.positive hp),?_,?_⟩
    · intro x y g; apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; apply (p.variation (f x) (f y)).trans; rw [show (tempo G d).eval S (f x) (f y)=0 from ?_,mul_zero]
      have hu:cloudG G S=S:=qtz m S; change deal _ S (unionP _) (unionP _) / _= _; unfold deal; rw [hu]; have he:Tulip.fare S (profile x.val) (profile y.val)=0:=by
          unfold fare; apply sum_eq_zero; intro i hy
          have hp: x.val i=y.val i:=g i (mem_filter.mp hy).2.1 (mem_filter.mp hy).2.2; rw [show profile x.val i=profile y.val i from funext fun z=>by unfold profile; rw [hp],sub_self,norm_zero]
      simp only [unionP]; rw [he,add_zero,zero_div]
    intro E _ _ _ S' x q t i' l; let Y:=fun x=> (f (q x)).val; have he: Allows N Y i' a := (H (fun i=>(q i).val) _ (t i' l)).pair (H (fun i=>(q i).val) _ (t i' l))
    have hy:Metric.ball (Y i') d ⊆ legal G d :=fun r hr'=>⟨((q i').val,(q i').val),⟨(q i').property.shrink hu,(q i').property.shrink hu,fun z=> ((jointly (q i').val (q i').property ‹0<e›).follow z).trans hu⟩, mem_ball_iff_norm.mp hr'⟩ -- tune
    have hx: Allows N (equalizer W ∘ Y) i' (composeCost N (C S i j*M) a) := (allows_looks ((h S).fuel i j) p.connected hy w N p.bounded).comp he
    refine (hx.mono ?_).germ ?_
    · rw [show composeCost N (C S i j*M) a=composeCost N M a* C S i j by unfold composeCost; ring]; exact mul_le_mul_of_nonneg_right (le_max_right ..) p.positive
    filter_upwards [] with u; exact dif_pos (f (q u)).property
 let D:=skewer false true C; let N' S i j:=C'*D S i j
 refine ⟨fun S x=>cue false true (V S x),N',fun S i j=>?_,(((ledger_cue false true T).funds (zero_le_one.trans hp)).lowers ?_).book (mul_le_mul_of_nonneg_left hy (zero_le_one.trans hp)),?_, fun x=>?_⟩
 · by_cases g:i.1=false∧ j.1=true
   · simp only [cue,N',D,skewer, Matrix.of_apply,g]; exact ⟨hx S i.2 j.2,fun v=>(((h S).expo ..).triggered (right_ne_zero_of_mul v)).2⟩
   simp only [cue,N',D,skewer, Matrix.of_apply,if_neg g,mul_zero, ne_eq,not_true,IsEmpty.forall_iff,and_true]
   have ht: ‖(0:ℂ)‖=0:=norm_zero; exact ht ▸ Pro.nonzero S (by simp)
 · intro S x y; apply mul_le_mul_of_nonneg_right (rent_up (show b/2 ≤ b from (half_lt_self ht).le) _); refine mul_nonneg (zero_le_one.trans hp) ?_; unfold D skewer; split; exact (h S).nonn _ _; rfl
 · intro x; unfold hitE; have he(S): ledgerV (N' S)=C'*ledgerV (C S):=by unfold N' ledgerV; simp only [← Finset.mul_sum]; exact congrArg (fun p=>C'*p) (ledger_c (C S) false true)
   simp_rw [he,mul_left_comm _ C',←mul_sum]; exact mul_le_mul_of_nonneg_left ((Branch.tall (s:=temper G d) (t:=temper G d) (fun S=>(h S).toTicket) T ht (temper_cap ..) quota_p.le x).trans (le_max_right ..)) (zero_le_one.trans hp)
 have hp:= U (f x); rw [show A _=_ from hp]; ext i j; by_cases h:i.1=false∧ j.1=true <;> simp [cue,h,Matrix.sum_apply,V]
end YM.CF.Proa
