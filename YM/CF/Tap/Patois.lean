import YM.CF.Tap.Mirth
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[Fintype ι][DecidableEq ι]{A:Cover→ℂ}{a m}{H:ι→ℝ}
private lemma spread (p:Cp m A a)(q:1≤m)(h:∀ i:Axis,(∑' x:Cover,(x i:ℂ)*A x)=0)(k:(∑' x,A x)=0)(F:List Axis→Cover→ι→ℂ)(i:ι):
 Summable (fun x:Cover=> A x*(F [] 0 i+trix F x i)) ∧ (∑' x:Cover,A x*(F [] 0 i+trix F x i))=0:=by
 let V(j:Axis)(x:Cover):= ((x j:ℂ)*A x)*F [j] 0 i
 have he(j): Summable (V j):=((moments p q j).1).mul_right _
 have hp:Summable fun x=>∑ j,V j x:= summable_sum (fun i _=> he i)
 have ht(x): A x*(F [] 0 i+trix F x i)= A x*F [] 0 i+ ∑ j,V j x:=by simp only [mul_add,trix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_sum]; congr 1; apply Finset.sum_congr rfl; intro j _; unfold V; ring
 simp_rw [ht]; have hl:= (p.falls.2.1.of_norm).mul_right (F [] 0 i); refine ⟨hl.add hp,?_⟩; rw [hl.tsum_add hp,tsum_mul_right,k,Summable.tsum_finsetSum (fun j _=>he j)]; simp_rw [V,tsum_mul_right,h,zero_mul, sum_const_zero,add_zero] -- tune
private lemma stage_p {F:List Axis→Cover→ι→ℂ}(p:Cp m A a)(q:1≤m)(h:∀ i:Axis,(∑' x:Cover,(x i:ℂ)* A x)=0)(k:(∑' x,A x)=0)(u:∀ i, 1≤ H i){B:ℝ}(v:∀ x, paidX H (thorn F x) ≤B*tweight m x)(z:0≤ B): paidX H (fun i=>∑' x,A x*F [] x i) ≤ B*a:=by
 let P(x:Cover):=‖A x‖*(B*tweight m x); have he(x): P x=B*(tweight m x*‖A x‖):=by unfold P; ring
 have hp: Summable P:=funext he ▸ p.2.1.mul_left B
 let G(x:Cover)(i:ι):=A x* thorn F x i
 have hT(x): paidX H (G x) ≤ P x :=by
    change paidX H (A x • thorn F x)≤ _; rw [p_smul]; exact mul_le_mul_of_nonneg_left (v x) (norm_nonneg _)
 let Q(x:Cover)(i:ι):= H i *‖G x i‖; have hu(x i):0≤Q x i:=mul_nonneg (zero_le_one.trans (u _)) (norm_nonneg _)
 have hh x i : Q x i ≤ P x := le_trans (Finset.single_le_sum (fun i _=>hu x i) (mem_univ _)) (hT x)
 have hd(x i): ‖G x i‖≤ Q x i:=le_mul_of_one_le_left (norm_nonneg _) (u i)
 have hv (i): Summable (fun x=> ‖G x i‖):= hp.of_nonneg_of_le (fun x=>norm_nonneg _) (fun x=>(hd x i).trans (hh x i))
 unfold paidX; calc
   _ ≤ ∑ i,∑' x,Q x i:=by
      apply sum_le_sum; intro i _; obtain ⟨hj,hk⟩:=spread p q h k F i
      have hz(x): A x* F [] x i= G x i + A x* (F [] 0 i + trix F x i):=by unfold G thorn; rw [Pi.sub_apply,Pi.add_apply,mul_sub,sub_add_cancel]
      simp_rw [hz]; rw [(hv i).of_norm.tsum_add hj,hk,add_zero]; unfold Q; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hv i)) (zero_le_one.trans (u i))
   _ ≤ ∑' x,P x:=by
     have hp'(i):Summable fun x=>Q x i:= (hv i).mul_left _
     rw [← Summable.tsum_finsetSum (fun i _=>hp' i)]; exact (summable_sum (fun i _=>hp' i)).tsum_le_tsum hT hp
   _ ≤ _:=by simp_rw [funext he,tsum_mul_left]; exact mul_le_mul_of_nonneg_left p.2.2 z
variable {c f: Side} (J:ℕ)
lemma mornY (H: Matrix (Single f) (Single c) ℂ)(A:Cover→Pal)(x:Site f)(i:coneA SU.Slot)(y:Single c)(k m)(s:RailP m A k):
   (love f (Rush.cart f A)*H) ((x,i.1),i.2) y = ∑ j:coneA SU.Slot, ∑' z, A z i j * (Rush.wind x z * H ((x+wrap f z,j.1),j.2) y):=by
 let v:=helix f; rw [Matrix.mul_apply,← Equiv.sum_comp v.symm]; change (∑ b:Model f,(love f _) _ (v.symm b)*H (v.symm b) y)= _; unfold Model; rw [Fintype.sum_prod_type, sum_comm]; apply sum_congr rfl; intro j _
 let P(b:Site f)(z:Cover):= wagon f A z (x,i) (b,j) * H (v.symm (b,j)) y; let Q(b:Site f):=∑' z,P b z
 have he(b): Summable (P b):= (wagon_sum (readsP s) ..).mul_right _
 rw [show ∑ b:Site f,(love f (Rush.cart f A)) ((x,i.1),i.2) (v.symm (b,j))*H (v.symm (b,j)) y = ∑ b,Q b from ?_] -- maybe Coe cast tune
 swap; · unfold Q P; simp_rw [tsum_mul_right]; rfl
 unfold Q; rw [← Summable.tsum_finsetSum (fun i _=>he i)]; refine tsum_congr fun b=>?_ ; unfold P; rw [sum_eq_single (x+wrap f b),wagon_app,if_pos rfl]; change _ *(H ((_,_),_) _)=_; ring -- tune
 intro z _ h; simp only [wagon_app, if_neg h.symm,zero_mul]; simp
lemma giant (m:ℕ)(h:Even J)(v:4≤J)(p:2≤m)(u:Bool) : ∃ B:ℝ,0<B∧∀ {c f:Side}(G: Ratio c f)(w:Odd G.count.val)(T:Script Male),Use J G.count @T →∀ (M:Male)(F: Cover→ Pal)(W: Momentum→ Pal)(k:ℝ), Reads F W → RailP m F k → NullW (potion J M W) →∀ x:Single f,
   let K:=love f (Rush.cart f (Tern J M F))*fan G w T J u M []
   paidX (streak G m x) (fun j:Single c=>K x j)≤ B*k*lace 2 G.count:=by
 obtain ⟨A,H₀,P₀⟩:=pawn_p J m (by omega) false; obtain ⟨C,H₁,P₁⟩:=pawn_p J m (by omega) true
 obtain ⟨D,d,Y⟩:=resto J m h v p u
 let l:= Fintype.card (coneA SU.Slot); let B:=D*l^3*A*C; have hp:0<(l:ℝ):= Nat.cast_pos.mpr Fintype.card_pos
 refine ⟨B,by unfold B; positivity,fun {c f} G w T s M F W k H q V x=>?_⟩
 obtain ⟨⟨x,a⟩,i⟩:=x; intro K; let P:=Tern J M F; let z:Single f:=((x,a),i); let Z:=pax G w T J u M; let X:=fan G w T J u M []; let t:ℝ:=l*((l*(A*k))*C); have he:RailP m P t:= foldYP (foldYP (P₀ M) q) (P₁ M)
 let E:=potion J M W; have hv: Reads P E:= reads_fold (foldYP (P₀ M) q) (P₁ M) (reads_fold (P₀ M) q (hel_pawn J (by omega) M false) H) (hel_pawn J (by omega) M true)
 let L:= lace 2 G.count; let u(j:coneA Slot):Single f:=((x,j.1),j.2); let A(j:coneA Slot)(v:Single c):=∑' b:Cover,P b (a,i) j*Z (u j) [] b v -- A shadow
 let R:=streak G m z; have hP(j: Single c):0≤R j:= streak_pos ..
 have hx(j): paidX R (A j)≤ D*L*t:=by
    have hz:=valueK hv V he (by omega) (a,i) j
    apply stage_p (he (a,i) j) (by omega) hz.2 hz.1 (fun i=> by unfold streak gum; exact one_le_pow₀ (by simp)) (Y G w T s M (u j)) (show 0≤ D *lace 2 G.count by unfold lace; positivity) -- y?
 have hm:(fun y:Single c=> K z y)= ∑ j:coneA Slot,A j:=by ext1 y; simp_rw [Finset.sum_apply]; exact mornY X P x (a,i) y _ _ he -- tune
 change paidX _ (fun j=> K z j)≤ _; rw [hm]; refine le_trans ?_ ((sum_le_sum (fun j (_:j∈univ)=> hx j)).trans_eq ?_)
 · unfold paidX; rw [Finset.sum_comm]; -- need on RHS
   simp_rw [Finset.sum_apply]; apply sum_le_sum; intro i _; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (hP i)
 simp only [sum_const,card_univ,nsmul_eq_mul]; unfold B L t; change (l:ℝ)*_= _; push_cast; ring
end YM.CF.Tap
