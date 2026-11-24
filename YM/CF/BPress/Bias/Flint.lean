import YM.CF.BPress.Bias.Spark
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Bias
open Function Finset Filter Lattice Laurent Bloch Next.Free Fir Lat Spin Rush Blank
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
attribute [local instance] opCStarAlgebra
local notation "π"=> Real.pi
variable {N:Side}
abbrev prin:= @Lat.principal
lemma wind_speed (a b: Per N)(h:b.val≤a.val): winding b≤ winding a:=by unfold winding; gcongr
lemma wind_muster (v:ℝ)(p:0<v): ∃ (r:ℝ)(n:ℕ),0<r∧∀ N:Side,n≤N.val→∃ a b:Per N, r≤Lat.principal a ∧ Lat.principal a ≤v ∧ Lat.principal b= -Lat.principal a ∧ (Lat.principal a)*N.val ≤ 3*π * ((univ : Finset (Per N)).filter fun u=>|Lat.principal u| ≤ Lat.principal a).card:=by
 let μ := min (1/8) (v/(3*π)); have hm:0<μ:=lt_min (by norm_num) (by positivity); have h₁:μ≤1/8:=min_le_left ..; have h₂:μ≤v/(3*π):=min_le_right ..; have hp:=Real.pi_pos; obtain ⟨n,g⟩:=exists_nat_gt (2/μ); refine ⟨μ*π,n,mul_pos hm hp,fun N h=>?_⟩
 let z:ℝ:= N.val; let m:= ⌊μ*z⌋₊; have hy:z>0:= nPos N; have hi:2<μ*z:=by rw [mul_comm]; rw [← div_lt_iff₀ hm]; exact g.trans_le (Nat.cast_le.mpr h)
 have ha: (m:ℝ)≤ μ*z:= Nat.floor_le (mul_pos hm hy).le; have he:(m:ℝ)> μ*z-1:= Nat.sub_one_lt_floor _
 have hm' : 1<(m:ℝ):=by linarith
 have hx : m<N.val:=by apply (Nat.cast_lt (α:=ℝ)).mp; change _<z; nlinarith [mul_le_mul_of_nonneg_right h₁ hy.le]
 let t:= N.val-(m+1); have ht:t+m+1=N.val:= by dsimp only [t]; omega
 let a: Per N:=m; let b: Per N:=t
 have ta(i:ℕ)(h:i<N.val): (i: Per N).val=i:=by rw [ZMod.val_natCast,Nat.mod_eq_of_lt h]
 have za:a.val=m:=ta _ hx; have zb:b.val=t:=ta _ (by omega)
 have hz:Lat.winding a <π:=mul_lt_of_lt_one_left hp (by rw [div_lt_one hy,za]; change _ < z; nlinarith [mul_le_mul_of_nonneg_right h₁ hy.le])
 have he': ∀ b:Per N,b.val ≤ a.val → Lat.principal b=winding b:=fun b t=> if_pos ((wind_speed _ _ t).trans hz.le)
 have hb: winding b=2*π-winding a:=by
    unfold winding; rw [za,zb]; have hh: (t:ℝ)+m+1=z:=by unfold z; exact_mod_cast ht
    change _/z*_=_-_/z*_; field_simp; linear_combination 2*hh
 refine ⟨a,b,?_⟩; rw [he' a le_rfl]; rw [show Lat.principal b=winding b-2*π from if_neg (by linarith)]
 have hv : ∀ k ∈ range m, (k:Per N)∈ (univ : Finset (Per N)).filter fun u=> |Lat.principal u|≤ winding a:=by
    intro k hk; rw [mem_range] at hk; let b:Per N:=k; have hu:b.val≤ a.val:=by rw [za,ta _ (hk.trans hx)]; exact hk.le
    exact mem_filter.mpr ⟨mem_univ _,by rw [he' b hu, abs_of_pos (winding_bounds _).1]; exact wind_speed _ _ hu⟩
 have hcard : m ≤ ((univ : Finset (Per N)).filter fun u=> |Lat.principal u|≤ winding a).card:=by
    rw [← card_range m]; -- issue all m?
    exact card_le_card_of_injOn (Nat.cast:ℕ→Per N) hv fun i p j q h=> by rw [← ta i ((mem_range.mp p).trans hx),← ta j ((mem_range.mp q).trans hx), h] -- tune
 refine ⟨?_,?_,by linarith,?_⟩
 · apply mul_le_mul_of_nonneg_right _ hp.le; rw [za,le_div_iff₀ hy]; linarith
 · have hy': μ*z*3 ≥ (2*(m:ℝ)+1):=by linarith
   unfold winding; rw [za]; exact (mul_le_mul_of_nonneg_right ((div_le_iff₀ hy).mpr (by linarith : (2*(m:ℝ)+1:ℝ) ≤ μ*3*z)) hp.le).trans (by linarith [(le_div_iff₀ (show 0< 3*π by positivity)).mp h₂])
 · unfold winding; rw [za, mul_right_comm,div_mul_cancel₀ _ hy.ne']; have hh: 2*(m:ℝ)+1 ≤ 3*m:=by linarith
   exact (mul_le_mul_of_nonneg_right hh hp.le).trans (by rw [mul_right_comm]; unfold winding at hcard; rw [za] at hcard; gcongr)

-- one axis reflected; don't need temporal point k 0 prescribed (choose w)
abbrev needle (k:Site N)(b:Per N):Site N:=update k 0 b
local notation "pmt(" k ")"=>pm k 0
abbrev markFreq (b:Per N)(τ:ℝ):=Complex.exp (((Lat.principal b*τ:ℝ):ℂ)*Complex.I)
abbrev Turn (f:Momentum→Op SpinIdx)(k:Site N)(τ:ℝ) := (N.val:ℂ)⁻¹ • (∑ b: Per N, markFreq b τ • f (mel (needle k b)))
lemma make_split (a b:Per N) (v: 0≤Lat.principal a)(h:Lat.principal b= -Lat.principal a) : ∃ k l: Site N, |pm k axisR|=Lat.principal a ∧ |pm l axisR|=Lat.principal a ∧ ∀ t: Per N, Reflection (Lat.principal a) (needle k t) (needle l t):=by
 let k:Site N:=fun _=>a; let l:=update k axisR b; have hs: axisR≠0:=by decide
 refine ⟨k,l,abs_of_nonneg v,by simp only [pm,Function.comp_apply,l,update_self,h,abs_neg,abs_of_nonneg v],fun t=>?_⟩; constructor
 · simp [pm,needle,k,hs]
 · simp [pm,needle,l,hs,h]
 · intro i hu; by_cases h:i=0 <;> simp [needle,h,hu,l]
 intro i hi; simp [pm,needle,k,v,hi,abs_of_nonneg]

def graphX (j:ℕ)(M:Jill.Male)(p : Momentum): Op SpinIdx:= -Fir.zen (mixL j M.val p)*angle true
section
open Reflection
variable {j:ℕ}{M:Jill.Male}
lemma mainLine (k:Site N) : graphX j M (mel k) 2 0 - graphX j M (mel k) 3 1=2*A j M k:=by
 unfold graphX; rw [lid]; norm_num [cup,A,zen,Fock.cutM,Momentum,Axis,Matrix.diagonal_apply,show (2:Fin 4)=Fin.succ (Fin.succ 0) from rfl, show (3:Fin 4)=Fin.succ (Fin.succ (Fin.succ 0)) from rfl,show (2:Fin 3)=Fin.succ (Fin.succ 0) from rfl,Matrix.mul_apply,Fin.sum_univ_succ, plusHalf, gammaOp, SpinIdx]; ring_nf; simp only [show (2:Fin 4)=Fin.succ (Fin.succ 0) from rfl, show (3:Fin 4)=Fin.succ (Fin.succ (Fin.succ 0)) from rfl, Matrix.cons_val_zero, Matrix.cons_val_succ]; ring
lemma balance_line (k:Site N)(τ:ℝ): let x:=Turn (graphX j M) k τ; ∑ b:Per N, markFreq b τ * A j M (needle k b)=(N.val:ℂ)/2*(x 2 0-x 3 1):=by
 intro x; unfold x Turn; simp only [Matrix.smul_apply,Matrix.sum_apply, smul_eq_mul]; rw [←mul_sub,← sum_sub_distrib, ←mul_assoc, show (N.val:ℂ)/2*(N.val:ℂ)⁻¹=1/2 by field_simp]; rw [mul_sum]; refine sum_congr rfl fun i _=>?_ ; rw [←mul_sub,mainLine]; ring

local notation "c"=> 1/(96*π : ℝ)
variable (h:1≤j)
include h
lemma turnsPrice (T:ℝ) (t:0≤T) : ∃ (r : ℝ)(n : ℕ),0<r ∧ ∀ (M:Jill.Male)(N:Side), n≤N.val → ∀ (τ:ℝ),|τ|≤T→∃ k:Site N, let Y:=Turn (graphX j M) k τ; r≤|pm k axisR| ∧ ∃ a b : SpinIdx,b∈plusHalf ∧ a∉ plusHalf ∧ c/2 ≤ ‖Y a b‖:=by
 obtain ⟨η,C,p,q,K⟩:= reflectionSpark h T t; have hv:0<c:=by positivity
 obtain ⟨r,n,e,R⟩:=wind_muster _ (lt_min p (div_pos hv q)); refine ⟨r,n,e,fun M N H τ τ' =>?_⟩; obtain ⟨a,b,w,g,he,s⟩:=R N H; let u:= Lat.principal a; have hu:0<u:=e.trans_le w; obtain ⟨k,l,hk,hl,h₁⟩:=make_split a b hu.le he
 let m:ℝ:= N.val; let v(k:Site N):=Turn (graphX j M) k τ; let y(k:Site N):=(m:ℂ)/2*((v k) 2 0-(v k) 3 1); have ht(k):y k= ∑ b:Per N, markFreq b τ * A j M (needle k b):=(by unfold y m v; push_cast; exact balance_line k τ|>.symm); have hm:m>0:= nPos N
 have hy(k:Site N)(b:Per N) : pmt(needle k b)=Lat.principal b:=by simp [needle,pm]
 let J:Finset (Per N):= univ.filter fun i=>|Lat.principal i|≤u; have he₀ :c*m ≤ (y k-y l).re:=by
    let E(b:Per N):ℝ:=if b∈J then 1/(16*u) else 0
    rw [ht k,ht l, ←sum_sub_distrib, Complex.re_sum]; have hz(b: Per N) : -(C*u)+E b ≤ (markFreq b τ*A j M (needle k b)-markFreq b τ*A j M (needle l b)).re:=by
       have hx:= K M τ τ' u hu (g.trans (min_le_left ..)) N _ _ (h₁ b); rw [hy] at hx; unfold E J; rw [← mul_sub]; simpa only [mem_filter,mem_univ,true_and,markFreq] using hx
    have hl₁:=sum_le_sum (s:=(univ:Finset (Per N))) fun i _=> hz i; apply le_trans ?_ hl₁; rw [sum_add_distrib,sum_const,show ∑ i:Per N,E i=(J.card:ℝ)*(1/(16*u)) by unfold E; rw [←sum_filter]; simp [nsmul_eq_mul]]; simp only [card_univ,Per,ZMod.card,nsmul_eq_mul]
    have hc:C*u≤c:=by rw [mul_comm]; exact (le_div_iff₀ q).mp (g.trans (min_le_right ..))
    have Ht: m * (1/(48*π)) ≤ J.card*(1/(16*u)):=by rw [mul_one_div,mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]; change u*m≤3*π*J.card at s; linarith
    change _ ≤ m*(-(C*u))+_; have hc₁:=mul_le_mul_of_nonneg_left hc hm.le; have hJe:2*c*m=m*(1/(48*π)):=by ring
    linarith
 by_contra! f; dsimp only at f; have vc(k:Site N)(v':r≤|pm k axisR|) : ‖y k‖<c*m/2:=by
   have he(a b:SpinIdx)(h:a∉plusHalf)(g:b∈plusHalf):‖v k a b‖<c/2:=lt_of_not_ge fun l=>f k ⟨v',_,_,g,h,l⟩
   unfold y; rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm, show ‖(2:ℂ)‖=(2:ℝ) by simp]; have Ht:= (norm_sub_le ((v k) 2 0) ((v k) 3 1)).trans_lt (add_lt_add (he _ _ (by decide) (by decide)) (he _ _ (by decide) (by decide))); nlinarith
 have h':= ((Complex.re_le_norm _).trans (norm_sub_le (y k) (y l))).trans_lt (add_lt_add (vc k (w.trans_eq hk.symm)) (vc l (w.trans_eq hl.symm))); linarith
end
end YM.CF.BPress.Bias
