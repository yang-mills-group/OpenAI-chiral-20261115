import YM.CF.Rush.Livery
/-! Position quaternionic conjugation, including the endpoint sign at π. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Complex
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}{a:Type*}[DecidableEq a][Fintype a]
private lemma innate(k:Per N): ZMod.val (-k-1)+k.val+1=N.val:=by
  let v:=k.val; have hv:v<N.val:=ZMod.val_lt _
  have hh:(↑(N.val-(v+1)):Per N)= -k-1:=by rw [Nat.cast_sub (by omega),ZMod.natCast_self,Nat.cast_add_one]; simp only [v,ZMod.natCast_zmod_val]; abel
  have ht:= congrArg ZMod.val hh; rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by omega)] at ht
  change _+v+1=_; omega
lemma vortex(k:Per N): BZ.phase (Lat.principal (-k-1))=BZ.phase (-principal k):=by
  have he := innate k
  have hp: winding (-k-1)= -winding k+2*Real.pi:=by
    have h : 0<(N.val:ℝ):=side_pos N
    have hx : ((ZMod.val (-k-1):ℝ)+k.val+1)=N.val:= by exact_mod_cast he
    unfold winding; field_simp; nlinarith only [hx]
  have hy (v:ℝ):BZ.phase (-v)= (BZ.phase v)⁻¹:=by unfold BZ.phase; rw [ofReal_neg,neg_mul, exp_neg]
  rw [hy,wind_eq, wind_eq, hp,←hy]; unfold BZ.phase; push_cast; rw [add_mul,Complex.exp_add]; simp -- name clash
lemma league {x y:ℝ}(h:BZ.phase x=BZ.phase (-y)):∃ i:ℤ,x= -y+2*Real.pi*i:=by
  obtain ⟨i,g⟩:=Complex.exp_eq_exp_iff_exists_int.mp (show Complex.exp ((x:ℂ)*Complex.I)=Complex.exp (((-y:ℝ):ℂ)*Complex.I) from h)
  have h:=congrArg Complex.im g; simp at h; refine ⟨i,?_⟩; rw [h]; ring
lemma dollar(k:Site N): ∃ z:Cover,mel (-k-1)= -mel k+reciprocal z:=by
  have h(i:Axis): ∃ z:ℤ,pm (-k-1) i= -pm k i+(2*Real.pi)*z:=league (vortex (k i))
  choose z hz using h; refine ⟨z,?_⟩; ext i:1; change (↑(pm (-k-1) i):ℂ)=-((pm k i:ℝ):ℂ)+_; rw [hz]; push_cast; rfl
lemma mode_negate (p:Momentum)(h:physical p)(x): mode (-p) x=star (mode p x):=by
  unfold mode; rw [show star (Complex.exp _)=Complex.exp (star _) from (Complex.exp_conj _).symm]; congr 1; simp only [Pi.neg_apply,star_mul,star_sum,star_intCast]; simp_rw [show ∀ i:Axis, star (p i)=p i from fun i=>congr_fun h i]; simp [mul_comm]
def backN : Equiv.Perm (Site N):=⟨(- · -1),(- · -1),fun x=>by change -(-x-1)-1=x; simp,fun x=>by change -(-x-1)-1=x; simp⟩
lemma rent(x i:Site N): Fourier N x (backN i) = star (Fourier N x i):=by
  obtain ⟨w,h⟩:= dollar i; change mel (backN i)=_ at h
  unfold Fourier; simp only [Matrix.of_apply,← freq_mode,h,mode_phase,mode_periodic, mul_one,mode_negate _ (mel_h i).1]; simp [normF]
lemma price (P:Momentum→Op a)(x k: Site N)(i j:a): plates N P (x,i) (k,j)=∑ l:Site N, Fourier N x l* P (mel l) i j*star (Fourier N k l):= by
  rw [plates,twist_formula,Matrix.mul_apply,Fintype.sum_prod_type]
  simp_rw [deck]; simp [overU, Matrix.one_apply,mul_ite,apply_ite]
lemma shape(P Q:Momentum→Op a)(h:∀ k: Site N, Q (mel k)=cc (P (mel (backN k)))):cc (plates N P)=plates N Q:=by
  ext ⟨x,i⟩ ⟨k,j⟩; change star (plates N P (x,i) (k,j))=_; rw [price,price,←Equiv.sum_comp (backN (N:=N)),star_sum]; refine sum_congr rfl ?_; intro l _; rw [rent,rent,h]; simp only [star_star,star_mul,cc_apply]; ring
lemma zenR(p:Momentum)(h:physical p): zen p * spinJ=spinJ*cc (zen (-p)):=by
  have he(n:Axis):star (p n)=p n:=congr_fun h n
  have hx (f : Axis→Op SpinIdx):cc (∑ i:Axis,f i)=∑ i:Axis,cc (f i):=by ext; simp [Matrix.sum_apply]
  unfold zen; rw [hx,Matrix.sum_mul,Matrix.mul_sum]
  apply Finset.sum_congr rfl; intro k _; simp only [cc_smul,Pi.neg_apply, star_neg, he, Matrix.smul_mul, Matrix.mul_smul, spinJ_inter]; simp -- clash
lemma barR (j N)(u:Bool)(hO:Odd N.val){p:Momentum}(h:p∈realCube zone)(hx:p≠0): bent u j N p*spinJ=spinJ*cc (bent u j N (-p)):=by
  let v:=mixL j N p
  have he:=aspTrace u j N hO h hx; have hf:=aspTrace u j N hO (realCube_neg h) (neg_ne_zero.mpr hx)
  have hz: prodM (-v) (-v)=prodM v v:=by simp [prodM]
  have hp:= phys_mix j N hO _ h.1
  have hg: Aop * spinJ=spinJ*cc Aop:=by rw [Adef,Matrix.smul_mul,add_mul,one_mul,cc_smul, cc_add,cc_one,Matrix.mul_smul,mul_add,mul_one, spinJ_grading]; norm_num
  have hh: angle u * spinJ=spinJ*cc (angle u):=by cases u <;> simp [angle,cc_sub,sub_mul,hg,mul_sub]
  rw [he,hf,shell_inv _ _ h hx,shell_inv _ _ (realCube_neg h) (neg_ne_zero.mpr hx), mix_neg _ _ hO, hz,prodM_self v hp, Matrix.smul_mul, cc_smul, Matrix.mul_smul];
  have hs: ∀ x:ℝ,star ((1+(x:ℂ))⁻¹)=(1+(x:ℂ))⁻¹:=by intro x; simp
  rw [hs]; apply congrArg
  have hT: (1+zen v)*spinJ= spinJ*cc (1+zen (-v)):=by rw [cc_add,cc_one, add_mul,mul_add,one_mul,mul_one,zenR _ hp]
  have hu: (1-zen v)*spinJ=spinJ*cc (1-zen (-v)):=by rw [cc_sub,cc_one, sub_mul,mul_sub,one_mul,mul_one,zenR _ hp]
  rw [mul_assoc,hT,←mul_assoc ( (1-zen _)*angle u),mul_assoc _ (angle u), hh,←mul_assoc,hu, cc_mul,cc_mul]; simp only [mul_assoc]; rfl
lemma bonK (j:ℕ)(L:Side)(h:Odd L.val)(p:Momentum)(hp:physical p): cc (brix j L (-p))=brix j L p:=by
  have hh:physical (-p):=by unfold physical; rw [star_neg,hp]
  rw [brix_scale _ _ hp,brix_scale _ _ hh,cc_add, cc_sub, cc_one, show cc (peb L)=peb L by ext ⟨x,b⟩ ⟨y,d⟩; by_cases e:x=y <;> by_cases f:y=0 <;> by_cases g:b=d <;> by_cases v:x=0 <;> simp_all [peb,spike,s_app,e,f,g,v]]; congr 1
  ext ⟨x,b⟩ ⟨y,d⟩; rw [cc_apply, Matrix.mul_apply,Matrix.mul_apply]; simp only [Fintype.sum_prod_type,St]; -- tune
  rw [←Equiv.sum_comp (Equiv.neg (Site L)),star_sum]; apply Finset.sum_congr rfl; intro l _; rw [star_sum]; refine sum_congr rfl ?_; intro k _
  by_cases e:b=k <;> by_cases f:k=d <;> by_cases z:y=0 <;> by_cases v:b=d <;> simp_all [trident,aliasBlock,sprig, c_app,e,f,z,Equiv.neg_apply,alias_reverse _ h, mode_negate _ (alias_real hp _),money,muff_even j L h,muff_real j L h _ (alias_real hp _),mul_comm]
end YM.CF.Rush
