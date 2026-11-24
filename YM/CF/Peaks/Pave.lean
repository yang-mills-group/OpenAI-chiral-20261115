import YM.CF.Peaks.Pitch
/-! Weighted transfer of open endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}
lemma unanimousK (u v:Bool)(o₀:Lattice.Order)(L:Side)(ho:Odd L.val)(f:∀ i:ι, (S:Side)→Track S) (p: ∃ σ C:ℝ,0<σ∧0<C∧∀ i r t,Width σ C fun x=> f i L x r t): Save L u v (fun i _ _ G x=>douse G u v (f i G.count) o₀ x):=by
  obtain ⟨σ,C,h,p,hP⟩:=p; obtain ⟨d,M,h₀,hk,h1,H⟩:=uplands h L
  let q:= ↑(Fintype.card Slot)*(M*C); let Y:=Fintype.card (St L) * (↑(Fintype.card (St L))*q); let V:ℝ:=(Fintype.card Lattice.Order:ℝ)⁻¹
  refine recorded (L:=L) (u:=u) (v:=v) (A:=fun i _ _ G x=>douse G u v (f i G.count) o₀ x) (k:=0) (C:=Y) (fun i N P G he hg=>?_) h₀ h₀
  subst L
  let S:= parcel G u d; let T:= parcel G v d
  let F(o:Lattice.Order)(r t):=fun n (x: legal G d)=> drag G u v r t (names n) (f i G.count (names n) r t) o x.val
  have hr (o r t):Crown (badge (legal G d)) S T d q (fun x=>∑' n,F o r t n x):=by
    let c(n:ℕ):= ‖f i G.count (names n) r t‖
    let A n:= Real.exp (σ*Laurent.size (names n))*c n; let Z (n:ℕ):= (↑(Fintype.card Slot)*M)*A n
    have hz:=hP i r t; have hx:= hz.2.1
    have hA : Summable A:=hx.comp_injective names.injective; have hZ: Summable Z:= hA.mul_left _
    have hl(n) : Crown (badge _) S T d (Z n) (F o r t n) := by
      apply swipe G u v ho _ _ _ _ o _ _ _ h₀ hk h₀.le; intro R; let k:= names n
      have Hx:= H (Laurent.size k) R (run_len u v G.count r t k o); apply le_trans (mul_le_mul_of_nonneg_left (_root_.le_trans (le_of_eq (mul_assoc _ _ _).symm) (mul_le_mul_of_nonneg_right Hx (norm_nonneg (f i G.count k r t)))) (Nat.cast_nonneg _)); unfold Z A c; exact le_of_eq (by ring)
    refine (Crown.tsK Z hl h₀.le hZ).books ?_
    unfold Z q; rw [tsum_mul_left,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ h1.le; unfold A c; rw [names.tsum_eq (f:=fun x:Cover=>Real.exp (σ*Laurent.size x)*‖f i G.count x r t‖)]; exact hz.2.2
  have hy(o): Crown (badge (legal G d)) S T d Y (fun x=>douse G u v (f i G.count) o x.val):=by
    have hh:= Crown.sumK univ _ _ fun r _=> Crown.sumK univ _ _ fun t _=> hr o r t; simp only [sum_const,card_univ,nsmul_eq_mul] at hh; exact hh
  exact hy o₀
lemma doused {N P:Side}(G:Ratio N P)(u v:Bool)(f:Track G.count)(h:∀ r t,Summable fun x=>‖f x r t‖)(o):douse G u v f o 1=cart N f ⊗ₖ (1:Op Slot):=by
    ext ⟨⟨y,b⟩,j⟩ ⟨⟨x,c⟩,l⟩; simp only [douse,Matrix.sum_apply]; simp_rw [kernel_entry (dragged _ _ _ _ _ _ _ (h _ _)), drag_one];
    rw [sum_eq_single b]; swap; intro i _ he; simp [Ne.symm he]; swap; simp
    rw [sum_eq_single c]; swap; intro i _ he; simp [Ne.symm he]; swap; simp
    change _=cart N f _ _ * _; simp only [cart,Matrix.of_apply,wagon_app]; rw [← tsum_mul_right,← names.tsum_eq]; simp [eq_comm]
lemma Scroll {L:Side}{A:Script ι}{u v:Bool}{e m h d:ℝ}{w k}(p:Score L A u v d h w k e)(hx:0<m)(he:m≤e): Score L A u v d h w k m:=by
  intro i N P G e' hm
  obtain ⟨V,C,h,f,Q⟩:=p i G e' hm
  let F:legal G m → legal G e:=fun x=>⟨x.val,insideP G x.property he⟩
  have ht:Towards (tempo G e) (badge _) (tempo G m) (badge _) F 1:=by
    refine ⟨continuous_subtype_val.subtype_mk _,rfl,rfl,fun _ _=>rfl,fun P x z=>?_,fun b H K HK γ q=>H K HK (F ∘ γ) q⟩
    let W:= deal G P x.val z.val; change W/|e| ≤ 1*(W/|m|); rw [one_mul,abs_of_pos (hx.trans_le he),abs_of_pos hx]; exact div_le_div_of_nonneg_left (deal_pos ..) hx he
  refine ⟨_,C, fun S=>ht.suite (parcel_eq ..) (parcel_eq ..) (h S) le_rfl,f,fun d=> Q (F d)⟩
variable (j:ℕ)(u:Bool)(D:List Axis)(hd:D.length+2≤j)
def optical (L:Side)(ho:Odd L.val)(T:Script Male):Script Male:=fun i _ _ G x=> grapple D i G x*(pine j L ho T u i G x * hood G)
include hd in
lemma sweepFunds (L : Side) (ho:Odd L.val): Save L true false (surfcoat j u D):=by
  refine unanimousK _ _ _ L ho (fun (i:Male) L=>tub (coverlet u j L i.val D)) ?_
  have hp: Pay (fun _:Male=> followV D L) fun i => coverlet u j L i.val D:=by unfold coverlet; apply col_quote; intro i; exact portrait u j (fun _:Male=>L) (fun i=>i.val) (fun _=> ho) (fun i=>i.property) (fun _=> i) D hd
  obtain ⟨⟨σ,C,h,ht,H⟩,_⟩:= tub_bill hp (fun i p hp x hx=> by unfold coverlet; congr 1; exact funext fun r=>spans _ _ _ _ _ _ hp _ hx)
  exact ⟨σ,C*followV D L,h,mul_pos ht (Vpos ..),H⟩
include hd in
lemma Scale (m:ℕ)(hj:Even j): ∃ C:ℝ, 0<C∧∀ L: Side,∀ ho:Odd L.val,∀ T : Script Male, Use j L T→∃ d a:ℝ,0<d∧0<a∧∃ k:ℕ, Score L (optical j u D L ho T) true false a (C*followV D L) m k d :=by
  obtain ⟨C,h,H⟩:= wide j u D hd m
  refine ⟨C+1,by linarith,fun L ho T ht=>?_⟩
  let Gℓ:= grapple_f j L ho hj (by omega) T ht D
  let A:=optical j u D L ho T; let B:Script Male:=fun i _ _ G x=> A i G x-surfcoat j u D i G x
  have hp: Save L true false @A:=Gℓ.mul ((pine_funds j L ho hj (by omega) T ht u).mul (hood_tag L ho))
  have he: Save L true false @B:=hp.sub (sweepFunds j u D hd L ho)
  obtain ⟨a,hP,hV⟩:=H L ho; obtain ⟨b,k,d,hb,hk,hq,v,hL⟩:=he
  have hs(i c f)(G: Ratio c f)(hp:G.count=L)(_:v≤c.val): B i G 1=0:=by
    let X:=tub (coverlet u j G.count i.val D); let ht':Odd G.count.val := hp.symm ▸ ho
    unfold B A surfcoat optical; rw [sticks j L ho hj (by omega) T ht G hp i D,pine_stencil j L ho hj (by omega) T ht G hp i u D hd]; rw [doused G true false _ (furl j u D hd G ht' i).sumK]; exact sub_self _
  obtain ⟨y,s,yh,tg,hx,r,hU⟩:= weighted (decayV (A:=@B) hL (lt_min hP hq) (min_le_right a d)) hb hk (lt_min hP hq) _ (Vpos D L) (fun i N P G hu hv=> hs i N P G hu hv) m -- implicit lambdas
  refine ⟨s,min y a,tg,lt_min yh hP,r,fun i N P G ht hv=>?_⟩
  have hy:= (hU i G ht hv).desc (min_le_left y a) (by positivity)
  have hb:= ((Scroll (A:=surfcoat j u D) hV tg (hx.trans (min_le_left a d))) i G ht (Nat.zero_le _)).desc (min_le_right y a) (by positivity)
  have he':(fun x: legal G s=> B i G x.val + surfcoat j u D i G x.val)=(fun x:legal G s=> A i G x.val):= by funext x; simp [B]
  have hu:=hy.plus hb; rw [he'] at hu; apply hu.prime; intro i; simp [add_mul,add_comm]
end YM.CF.Peaks
