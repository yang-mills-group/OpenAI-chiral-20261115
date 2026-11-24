import YM.CF.Onyx.Gold
import YM.CF.Jill.Pine
import YM.CF.Rush.Rill
import YM.CF.Tulip.Metro
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Tenant Fock Tulip Dial Fir Ember
attribute [local instance] opCStarAlgebra
variable {N : Side} {k:ℕ} {d b:ℝ}
abbrev Φ0 (k:ℕ) (M:Tulip.Male) (x:Site N): ℝ := Jill.disk k M (pm x)
def pilotB (N:Side)(k:ℕ)(M:Tulip.Male):ℝ:= ((N.val:ℝ)^4)⁻¹*(∑ x:Site N, Φ0 k M x)
-- exact all diag formula. Antipodal issues `principal` with edge π; use reciprocal shift. 
private lemma mpos (x:Site N): mel x ∈ realCube zone:= base_subset_realCube zone_pos (mel_h x)
private lemma antipode (k:ℕ)(M:Tulip.Male)(x: Site N):bar k M.val (mel x)+bar k M.val (mel (backN x))= (2:ℂ) • ((Φ0 k M x:ℂ) • Aop+(1-(Φ0 k M x:ℂ)) • (1-Aop)):=by
 obtain ⟨w,g⟩:= dollar x; let l:= M.val; let P:= mel x; let V:= -P
 have he:V∈realCube zone:= realCube_neg (mpos x); have hp:V+reciprocal w∈realCube zone:=by rw [← show mel (-x-1)=_ from g]; exact mpos _
 rw [show mel (backN x)=_ from g,bar_overlap k M.val he w hp];
 have hu : shell k l V=shell k l P:= Onyx.foxy k M (mpos _) he; have hv : zen (skin k l V)= -zen (skin k l P):=by
    rw [skin_mix k l he,skin_mix k l (mpos x), show mixL k l V= _ from mix_neg k M.val M.property P, hu, smul_neg, ← neg_one_smul ℂ (_ • _) , zenS,neg_one_smul] -- tune
 change bar k l P+bar k l V=(2:ℂ) • _
 let y:=Φ0 k M x; have hh:shell k l P=(y:ℂ):= Jill.express k (pm x) _ (mpos x) M.property; unfold bar; rw [hu,hv,mul_neg,hh,ordA]; change _= (2:ℂ) • ((y:ℂ) • Aop + (1-(y:ℂ)) • _); module
lemma pilot_add (k:ℕ)(M:Tulip.Male)(x:Site N): shell k M.val (mel x) = (Φ0 k M x:ℂ):= Jill.express _ _ _ (mpos x) M.property
private lemma fourier_p(x k:Site N): Fourier N x k * star (Fourier N x k)= ((N.val:ℂ)^4)⁻¹:=by
 unfold Fourier; simp only [Matrix.of_apply,star_div₀]; rw [div_mul_div_comm, mul_comm (frequency k x),frequency_unit]; unfold normF; simp only [star_pow,star_natCast,one_div]; ring
lemma sell_diag0 (k:ℕ)(M:Tulip.Male) (x:Site N)(i j:SpinIdx) :
   plates N (bar k M.val) (x,i) (x,j)=(pilotB N k M:ℂ)*Aop i j+(1-(pilotB N k M:ℂ))*(1-Aop) i j:=by
 let p(l:Site N):= bar k M.val (mel l) i j; let e:= (N.val:ℂ)^4; let f:=pilotB N k M
 rw [Rush.price]; simp_rw [mul_right_comm _ (bar k _ _ _ _), fourier_p,←mul_sum]; change e⁻¹*(∑ l,p l)=(f:ℂ)*_+(1-(f:ℂ))*_
 let b(l:Site N):ℂ:= Φ0 k M l; let s:= ∑ x:Site N,b x
 have he:(f:ℂ)= e⁻¹*s:=by
    unfold f pilotB e s b -- unfold order
    push_cast
    rfl -- maybe simp
 have hr:(∑ l:Site N, p l)= s*Aop i j+(e-s)*(1-Aop) i j:=by
    have hx(t): p t+p (backN t)=2*(b t*Aop i j+(1-b t)*(1-Aop) i j):=congr_fun (congr_fun (antipode k M t) i) j
    have ht: (∑ l: Site N,p l)+(∑ l: Site N,p l)=∑ t:Site N,(p t+p (backN t)):=by rw [sum_add_distrib, Equiv.sum_comp (backN (N:=N))]
    simp_rw [hx,←mul_sum, sum_add_distrib,sub_mul,←sum_mul] at ht; simp_rw [sum_sub_distrib, sum_const,nsmul_eq_mul,card_univ,site_card,Nat.cast_pow,←sum_mul] at ht; unfold s e; linear_combination ht/2 -- tune
 have hv:e≠0:=pow_ne_zero _ (show (↑N.val:ℂ)≠0 from by exact_mod_cast N.property.ne')
 rw [he,hr]; field_simp -- tune
-- diagonal compression for full site
lemma sell_diag(k:ℕ)(hk:1≤k)(M:Tulip.Male)(x:Site N)(i j:SpinIdx)(a b:SU.Slot) :
    (funde k M N 1) ((x,i),a) ((x,j),b) = if i=j ∧ a=b then (if i∈plusHalf then (pilotB N k M:ℂ) else (1-(pilotB N k M:ℂ))) else 0:=by
 rw [funde_flat k hk M N, show cart N (tub (bar k M.val))=plates N (bar k M.val) from cart_traded (A:=bar k M.val) (cBar k M.val true hk M.property) N, Matrix.kroneckerMap_apply]; change plates N (bar k M.val) (x,i) (x,j)*(1:Op SU.Slot) a b=_
 rw [sell_diag0 k M, Adef,←raising]; by_cases g:i=j; swap; · by_cases h:a=b <;> simp [g,h, cutM,Matrix.one_apply];
 subst j; by_cases t:a=b <;> by_cases p:i∈plusHalf <;> simp [t,p,cutM,Matrix.one_apply]
private lemma Φn(k:ℕ)(M:Tulip.Male)(x:Site N):(0:ℝ)≤Φ0 k M x:=norm_nonneg _
private lemma Φb(k:ℕ)(M:Tulip.Male)(x:Site N):Φ0 k M x≤1:=by
 let p:=mel x; let v:=mixL k M.val p; let S:ℝ:=∑ i:Axis,(v i).re^2; have h:S≥0:= sum_nonneg fun i _=>sq_nonneg _
 have ht := pilot_add k M x; rw [shell_inv _ _ (mpos x) (mel_away x),prodM_self _ (phys_mix k M.val M.property _ (mpos x).1)] at ht; change (1+ (S:ℂ))⁻¹=( _ :ℝ) at ht -- tune
 have hx: (1+S)⁻¹=Φ0 k M x:=by exact_mod_cast ht
 rw [←hx]; exact inv_le_one_of_one_le₀ (by linarith)
lemma pilot_range (N:Side)(k:ℕ)(M:Tulip.Male): 0 ≤ pilotB N k M ∧ pilotB N k M ≤1 := by
 unfold pilotB; have h:= nPos N; have hq:(∑ x:Site N,Φ0 k M x) ≤ ∑ _x:Site N,(1:ℝ):= sum_le_sum fun i _=> Φb k M i; simp only [sum_const,card_univ,site_card,nsmul_eq_mul,mul_one,Nat.cast_pow] at hq; exact ⟨mul_nonneg (by positivity) (sum_nonneg (fun i _=> Φn k M i)),(mul_le_mul_of_nonneg_left hq (by positivity)).trans_eq (inv_mul_cancel₀ (pow_ne_zero _ h.ne'))⟩
variable {V T:ℕ} {C:ℝ}
section
variable (h:4 ≤ V)(g:N.val ≤ (T+1)*V)(t:T*V ≤ N.val)(e:0<T)
def spanned (T:ℕ)(N:Side) : Finset (Site N) := univ.filter fun k=>∀ x:Axis, T ≤ (k x).val ∧ (k x).val < 2*T
include h g t e
lemma travel_budget (x:Site N)(p:x∈spanned T N) : Real.pi/V ≤‖pm x‖ ∧ ‖pm x‖ ≤ 4*Real.pi/V:=by
 have he:4 ≤ (V:ℝ):= Nat.ofNat_le_cast.mpr h; have hp:(T:ℝ)*V ≤ N.val:=by exact_mod_cast t
 have hT:(N.val:ℝ)≤ (T+1:ℝ)*V:=by exact_mod_cast g
 have hn:= nPos N; have hv:0<(V:ℝ):=by linarith
 have hx:=Real.pi_pos; have hh(i:Axis): Real.pi/V ≤ |pm x i| ∧ |pm x i|≤ 4*Real.pi/V:=by
    obtain ⟨l,p⟩:= (mem_filter.mp p).2 i; let k:=x i; let j:=k.val; let P:=(2*(j:ℝ)+1)/(N.val:ℝ); let Q:=P *Real.pi
    have hj:(T:ℝ)≤ (j:ℝ):= Nat.cast_le.mpr l; have hj':(j:ℝ)+1 ≤ 2*(T:ℝ):=by exact_mod_cast Nat.succ_le_of_lt p -- why succ math
    have hr: 1/(V:ℝ) ≤ P:=by
        refine (_root_.div_le_div_iff₀ hv hn).mpr ?_; rw [one_mul]; nlinarith only [mul_nonneg (by positivity : 0 ≤ (j:ℝ)) hv.le, mul_le_mul_of_nonneg_right hj hv.le, hT]
    have hd: P ≤ 4/V:=by
        apply (_root_.div_le_div_iff₀ hn hv).mpr; nlinarith only [mul_le_mul_of_nonneg_right hj' hv.le,hv, hp]
    have hQ:0 ≤ Q:= by unfold Q; exact mul_nonneg ((one_div_pos.mpr hv).le.trans hr) hx.le
    have hy: |pm x i|= Q:=by change |if Q ≤ Real.pi then Q else _|=_; rw [if_pos (show Q ≤ Real.pi from (mul_le_of_le_one_left hx.le (le_trans hd (by rw [div_le_one hv]; exact he)))),abs_of_nonneg hQ]
    rw [hy]; refine ⟨?_,?_⟩
    refine (mul_le_mul_of_nonneg_right hr hx.le).trans' (le_of_eq ?_); ring
    exact (mul_le_mul_of_nonneg_right hd hx.le).trans_eq (by ring)
 exact ⟨(hh 0).1.trans (norm_le_pi_norm (pm x) 0),(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i=> (hh i).2⟩
omit g e
lemma spanned_size : T^4 ≤ (spanned T N).card:=by
 let A:= Axis→Fin T; let f(k:A):Site N:=fun i => (T+(k i).val:ℕ)
 have hT:2*T≤ N.val:=by exact le_trans ((mul_comm 2 T).le.trans (Nat.mul_le_mul_left T (by omega))) t
 have hx (i k): (f i k).val = T+(i k).val:= ZMod.val_natCast_of_lt (lt_of_lt_of_le (by have h:= (i k).isLt; omega) hT)
 have hf:Function.Injective f:=by intro i j q; funext k; apply Fin.ext; have ht:= congrArg ZMod.val (congrFun q k); rw [hx,hx] at ht; omega
 have hp: (univ:Finset A).card=T^4:=by rw [card_univ,Fintype.card_pi_const,Fintype.card_fin]; -- tune
 have he: univ.image f ⊆ spanned T N:=by intro i u; obtain ⟨v,_,rfl⟩:=mem_image.mp u; exact mem_filter.mpr ⟨mem_univ _,fun x=>by rw [hx]; have h:= (v x).isLt; omega⟩
 have ht:= card_le_card he; rwa [card_image_of_injective _ hf,hp] at ht
include g e
lemma tiny_funds (F: Site N→ℝ)(d:ℝ) (p:0≤d)(hf:∀ x,F x ≥ 0)(u:∀ x∈spanned T N,d≤ F x): let Z:= (((2:ℝ)*V)^4)⁻¹*d; Z ≤ (((N.val:ℝ)^4)⁻¹ * ∑ i,F i):=by
 intro Z; let U:= ∑ i,F i; have hv:0<(V:ℝ):=by exact_mod_cast show 0<V by omega
 have hy:(T:ℝ)≥1:= Nat.one_le_cast.mpr e; have hx:(N.val:ℝ) ≤ 2*V*T:=by
    have hT:(N.val:ℝ) ≤ (T+1:ℝ)*V:=by exact_mod_cast g
    nlinarith only [mul_le_mul_of_nonneg_right hy hv.le,hT]
 have hL:(T:ℝ)^4*d≤U:=by
    refine (mul_le_mul_of_nonneg_right (show (T:ℝ)^4 ≤ (spanned T N).card from (by exact_mod_cast spanned_size h t)) p).trans ?_
    calc
       _ = ∑ _i∈ spanned T N,d:=by simp
       _ ≤ ∑ i∈ spanned T N,F i:= sum_le_sum u
       _ ≤ _:= sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> hf i)
 unfold Z; rw [inv_mul_eq_div, inv_mul_eq_div,_root_.div_le_div_iff₀ (by positivity) (pow_pos (nPos N) _)]; refine ?_; calc
    _ ≤ d*(2*V*(T:ℝ))^4:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nPos N).le hx _) p
    _ = ((T:ℝ)^4*d)*(2*(V:ℝ))^4:=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right hL (show 0≤(2* (V:ℝ))^4 by positivity)
-- exact opposite payment
end
private lemma arrange {V:ℕ}(h:4≤ V)(t:V ≤ N.val):∃ T:ℕ,0<T ∧ N.val ≤ (T+1)*V ∧ T*V≤N.val:=by
 have he:0<V:=by omega
 refine ⟨N.val/V, Nat.div_pos t he, (by rw [Nat.add_mul,Nat.one_mul]; have h1:= Nat.mod_add_div N.val V; have h2:= Nat.mod_lt N.val he; rw [mul_comm] at h1; omega),Nat.div_mul_le_self ..⟩
lemma firm_price (k:ℕ)(hk:1≤k):∃ c:ℝ,0<c∧ c<1 ∧∃ V:ℕ,∀ N:Side,V≤N.val→∀ M:Tulip.Male, c ≤ pilotB N k M ∧ pilotB N k M ≤ 1-c:=by
 obtain ⟨b,T,g,e,P⟩:=Jill.zip hk
 -- choose V so T* (4*pi)^2 / V^2 small
 let x:= 2*T*(4*Real.pi)^2
 obtain ⟨i,u⟩:= exists_nat_gt x; let v:=i+4; have he:4≤v:=by omega
 have hp:4≤(v:ℝ):= Nat.ofNat_le_cast.mpr he; have hv:0<(v:ℝ):=by linarith
 have ht : T*(4*Real.pi/v)^2 ≤ 1/2:=by
    have hx:x ≤ (v:ℝ):= u.le.trans (Nat.cast_le.mpr (show i ≤ v from by omega)); unfold x at hx; rw [div_pow, ←mul_div_assoc]; apply (div_le_iff₀ (pow_pos hv _)).mpr; nlinarith only [hx,sq_nonneg ((v:ℝ)-1),hp]
 let q:= Real.pi/v; let f:= ((2*(v:ℝ))^4)⁻¹ * min (b*q^2) (1/2); let w:= min f (1/2); have hy:0< q:=by unfold q; positivity
 have hh:0 < w:=lt_min (mul_pos (inv_pos.mpr (by positivity)) (lt_min (by positivity) (by norm_num))) (by norm_num)
 refine ⟨w,hh,(min_le_right ..).trans_lt (by norm_num),v,fun N t M=>?_⟩; obtain ⟨j,h,H,S⟩:=arrange he t
 have l(i:Site N): Jill.Bound Real.pi (pm i):=(pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr fun x=> abs_le.mpr ⟨(pm_zone i x).1.le,(pm_zone i x).2⟩
 have hz(i:Site N)(g':i∈spanned j N): min (b*q^2) (1/2)≤ Φ0 k M i ∧ min (b*q^2) (1/2) ≤ 1-Φ0 k M i:=by
    let X':= l i; obtain ⟨p,w⟩:= P M (pm i) X'; obtain ⟨r,v⟩:=travel_budget he H S h i g'
    have hr : b*q^2 ≤ b*‖pm i‖^2:=by gcongr; -- tune q nonneg
    have hy: Φ0 k M i ≤ 1/2:= w.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) v _) e.le).trans ht); exact ⟨(min_le_left ..).trans (hr.trans p), (min_le_right ..).trans (by linarith)⟩
 have hZ(y:Site N→ℝ)(k:∀ i:Site N,y i≥0)(t:∀ i∈spanned j N, min (b*q^2) (1/2) ≤ y i): w≤ ((N.val:ℝ)^4)⁻¹ * ∑ i:Site N,y i:= (min_le_left ..).trans (tiny_funds he H S h y _ (le_min (by positivity) (by positivity)) k t)
 refine ⟨hZ _ (Φn k M) (fun i u=> (hz i u).1), ?_⟩; have ht:= hZ _ (fun i=>sub_nonneg.mpr (Φb k M i)) (fun i t=> (hz i t).2); let x:=(N.val:ℝ)^4; unfold pilotB; rw [sum_sub_distrib,sum_const,card_univ,site_card,nsmul_eq_mul,mul_one,Nat.cast_pow,mul_sub,inv_mul_cancel₀ (pow_pos (nPos N) 4).ne'] at ht; linarith
#print axioms firm_price
#print axioms sell_diag
end YM.CF.Window.Brique
