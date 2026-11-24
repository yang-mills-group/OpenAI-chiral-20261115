import YM.CF.Fir.Origin
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric
open scoped Topology Matrix BigOperators

def D (N:Side) (p : Momentum) := (N.val:ℂ)^2*gD (narrow N p)
def ds (N:Side) (p:Momentum) : Momentum := (N.val:ℂ) • sine (narrow N p)
def Cminus (N:Side) (p:Momentum) := rad (narrow N p)-kin (narrow N p)
lemma ds_expand (N:Side) (p:Momentum) (a:Axis) : ds N p a=(N.val:ℂ)*sine (narrow N p) a := rfl
lemma ds_sq (N:Side) (p:Momentum) : (∑ a : Axis, ds N p a ^ 2)=D N p*Cminus N p := by
  simp_rw [ds_expand,mul_pow,← Finset.mul_sum]; rw [D,Cminus,gD,mul_assoc]; congr 1
  have he := r_square (narrow N p); unfold mag at he; rw [add_mul, mul_sub, mul_sub]
  linear_combination -he -- check
lemma pl_seed (N:Side) (p:Momentum) (a:Axis): (N.val:ℂ)^2*pl (narrow N p) a=1/2*(seedQ N p a*seedQ N (-p) a) := by
  have he (z:ℂ) : 2*(1-Complex.cos z)=chip z*chip (-z) := by
    unfold chip Complex.cos; rw [mul_neg,mul_comm Complex.I z]
    have hh : Complex.exp (z*Complex.I)*Complex.exp (-(z*Complex.I))=1:= by rw [← Complex.exp_add]; simp
    simp only [neg_mul]
    linear_combination -hh
  rw [seedQ,seedQ,show narrow N (-p) a= -(narrow N p a) by simp [narrow]]; unfold pl
  rw [show ∀ a b c : ℂ,(a*b)*(a*c)=a^2*(b*c) by intros; ring, ← he]
  ring
lemma sin_seed (N:Side) (p:Momentum) (a:Axis): ds N p a= (Complex.I / 2)*(seedQ N (-p) a-seedQ N p a) := by
  rw [seedQ,seedQ,show narrow N (-p) a= -(narrow N p a) by simp [narrow],ds_expand,sine,Complex.sin]; unfold chip
  rw [mul_neg (a:=Complex.I),mul_comm Complex.I]; ring
lemma pl_level (p:Momentum) : pl p=pl (narrow (1:Side) p) := by simp [narrow]
lemma shape (N:Side) (p:Momentum) : D N p= (∑ a, ((N.val:ℂ)^2*pl (narrow N p) a)*(∑ j∈Finset.univ.erase a, pl (narrow N p) j)) / (rad (narrow N p)+1)+(1/2:ℂ)*divisor N p := by
  let q:=narrow N p
  have he : ∀ a, (N.val:ℂ)^2*pl q a=1/2*(seedQ N p a*seedQ N (-p) a) := pl_seed N p
  have hh : (N.val:ℂ)^2 * (∑ a, pl q a)=1/2*divisor N p := by unfold divisor; simp_rw [Finset.mul_sum,he]
  have ht : rad q-1 = (∑ i, pl q i*(∑ j∈Finset.univ.erase i, pl q j))/(rad q+1) := by
    rw [eq_div_iff (sector _), sub_mul]; have hx := (r_square q).trans (pile q); linear_combination hx
  rw [D]; change (N.val:ℂ)^2*(rad q+kin q)=_
  unfold kin; rw [show rad q+(-1+∑ a,pl q a)=rad q-1+∑ a,pl q a by ring,ht,mul_add,hh, ← mul_div_assoc,Finset.mul_sum]
  simp only [mul_assoc,q]
lemma na_phys (N:Side) {p:Momentum} (h:physical p) : physical (narrow N p) := by unfold narrow physical; simp [show star p=p from h]
lemma D_lower (N:Side) {p:Momentum} (hp : physical p) : 1/2*(divisor N p).re ≤ (D N p).re := by
  set v:= fun i : Axis => ((narrow N p) i).re with hq
  have he:= pq (narrow N p) (na_phys N hp); rw [shape,← show tmap v=narrow N p from he,Complex.add_re,r_real]
  have hh (a : Axis) : pl (tmap v) a = ((1-Real.cos (v a):ℝ):ℂ) := by simp [pl,tmap]
  let x:ℝ:= ∑ i : Axis, (N.val:ℝ)^2 * (1-Real.cos (v i))*(∑ j∈Finset.univ.erase i, (1-Real.cos (v j)))
  have hx: 0≤x:=Finset.sum_nonneg fun i _=>mul_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))) (Finset.sum_nonneg fun i _=>sub_nonneg.mpr (Real.cos_le_one _))
  simp_rw [hh]; rw [show (∑ i:Axis, (N.val:ℂ)^2*((1-Real.cos (v i):ℝ):ℂ)*(∑ j∈Finset.univ.erase i, ((1-Real.cos (v j):ℝ):ℂ)))=((x:ℝ):ℂ) by norm_cast; simp only [x,PNat.pow_coe,Nat.cast_pow], show (x:ℂ)/ ((BZ.wave v:ℂ)+1)=((x/(BZ.wave v+1):ℝ):ℂ) by norm_cast,Complex.ofReal_re]; norm_num [Complex.mul_re, div_nonneg hx (by linarith [r_ge v] : 0≤BZ.wave v+1)]
-- inspect

variable {ι : Type*}
lemma pl_mod (M:ι→Side) (ho:∀ i, Odd (M i).val) (a: Axis) : Moderate (fun _:ι=>1) fun i p=> pl (narrow (M i) p) a := by
  simp_rw [← alias_zero_eq]
  apply Moderate.on_alias (f:=fun _ p => pl p a) _ M ho (fun _=>0)
  have hx:=seed_control (fun _:ι=>(1:Side)) (fun _=>a)
  have hh : ∀ p:Momentum, pl p a=1/2*(seedQ 1 p a*seedQ 1 (-p) a) := fun p=> by simpa [narrow] using pl_seed 1 p a
  simpa only [hh,mul_one] using (Moderate.const (1/2)).mul (hx.mul hx.reverse)
lemma rad_mod (M:ι→Side) (ho:∀ i, Odd (M i).val) : Moderate (fun _:ι=>1) fun i p=> rad (narrow (M i) p) := by
  simp_rw [← alias_zero_eq]; apply Moderate.on_alias _ _ ho; obtain ⟨η,C,hp,hC,H⟩:= rad_uniform; exact ⟨η,C,hp,hC,fun i => by simpa using H⟩
lemma rOne (M:ι→Side) (ho:∀ i, Odd (M i).val) : Moderate (fun _:ι=>1) fun i p=> (rad (narrow (M i) p)+1)⁻¹ := by
  have hx:= rad_mod M ho
  have he: Firm (fun _:ι=>1) fun i p=> rad (narrow (M i) p)+1 := by
    refine ⟨1,1,by norm_num,one_pos,fun i p hp=>?_⟩
    let v := narrow (M i) p
    change _≤‖rad v+1‖; apply le_trans _ (Complex.re_le_norm _)
    rw [← pq v (na_phys _ hp.1),r_real]; norm_num [r_ge _, (BZ.wave_pos _).le]
  simpa only [inv_one] using (hx.add (Moderate.const 1)).inv he (fun _=>one_pos)
lemma ink (M L:ι→Side)(hm:∀ i, Odd (M i).val)(hl:∀ i, Odd (L i).val)
    (l:∀ i, Site (L i)) : Moderate (fun i=>grade (l i)^2) fun i p=> ((L i).val:ℂ)^2*D (M i) (aliasAt p (l i)) := by
  let z (i:ι) : ℂ:=((L i).val:ℂ)
  have hh (a:Axis) : Moderate (fun i=>grade (l i)^2) fun i p=> z i^2 * (((M i).val:ℂ)^2*pl (narrow (M i) (aliasAt p (l i))) a) := by
    have he:= (scaled_seed L M hl l (fun _=>a)).raise_price (u:=fun i=>grade (l i)) (fun i=>up_le ..)
    have hx : Moderate (fun i=>grade (l i)) fun i p=> z i*seedQ (M i) (-aliasAt p (l i)) a := by
      have hb:= ((scaled_seed L M hl (fun i=> -l i) (fun _=>a)).raise_price (u:=fun i=>grade (-l i)) (fun i=>up_le ..)).reverse
      simpa only [alias_reverse _ (hl _),pdist_neg,z, grade] using hb
    convert (Moderate.const (1/2)).mul (he.mul hx) using 2
    · simp [sq]
    ext p; simp only [pl_seed,z]; ring
  let X i p := (1/2:ℂ)*blow (M i) p (l i)
  have hy : Moderate (fun i=>grade (l i)^2) X := by simpa only [X,one_mul] using (Moderate.const (1/2)).mul (blow_control L M hl l)
  let Y (i:ι) (p:Momentum):= ∑ a, (z i^2*(((M i).val:ℂ)^2*pl (narrow (M i) (aliasAt p (l i))) a))*(∑ j∈Finset.univ.erase a, pl (narrow (M i) (aliasAt p (l i))) j)
  have hY : Moderate (fun i=> grade (l i)^2) Y := by
    apply Moderate.sum _ _ (fun _=>by positivity)
    intro a _; simpa only [mul_one] using (hh a).mul (Moderate.sum (Finset.univ.erase a) _ (fun _=>zero_le_one) (fun b _=> (pl_mod M hm b).on_alias L hl l))
  have hz:= hY.mul ((rOne M hm).on_alias L hl l); simp only [mul_one] at hz; convert hz.add hy using 2; ext p:1; dsimp only [Y,X]; rw [shape,blow, mul_add,div_eq_mul_inv,← mul_assoc ((_:ℂ)^2), Finset.mul_sum]; simp_rw [z,mul_assoc]; ring
lemma lamp (M L:ι→Side)(hl:∀ i, Odd (L i).val)(l:∀ i, Site (L i))(ho:∀ i,l i≠0) : Firm (fun i=>grade (l i)^2) fun i p=>((L i).val:ℂ)^2*D (M i) (aliasAt p (l i)) := by
  obtain ⟨η,C,hp,hC,H⟩:=blow_firm L M hl l ho
  refine ⟨η,C/2,hp,by positivity,fun i p hp=> ?_⟩
  let q := aliasAt p (l i)
  have hh : physical q:= alias_real hp.1 _
  have he:= H i p hp
  change _≤‖blow (M i) p (l i)‖ at he; unfold blow at he; rw [norm_mul,norm_pow,Complex.norm_natCast,divisor_normSq _ hh,Complex.norm_real,Real.norm_eq_abs, abs_of_nonneg (by positivity)] at he
  have ht:= D_lower (M i) hh; rw [divisor_normSq _ hh,Complex.ofReal_re] at ht
  rw [norm_mul,norm_pow,Complex.norm_natCast]; dsimp only
  change _≤ _*‖D (M i) q‖
  dsimp only at he; nlinarith [mul_le_mul_of_nonneg_left (ht.trans (Complex.re_le_norm _)) (sq_nonneg ((L i).val:ℝ))]
end YM.CF.Fir
