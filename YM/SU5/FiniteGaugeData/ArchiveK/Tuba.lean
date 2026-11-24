import YM.SU5.FiniteGaugeData.ArchiveK.Vern
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
attribute [local instance] opCStarAlgebra
variable (G:E4≃ₗᵢ[ℝ] E4) (p:Space3)(x:E4)
local notation "∆"=> depthG G
local notation "Ω" => sailX G
open LightK
-- scalar time-normal derivative. weighted sum of actual Green with spin coefficients = `∫ right weight`. all actual.Wave. coeff cost scales.D. need universal bound by eventual α; finite const.OK
abbrev Glue:= (Fin 2) × Fin 2
abbrev hat_a(x:Glue): SpinIdx:= x.1.castLE (by decide)
def hed_a(x:Glue): SpinIdx:= ⟨x.2.val+2,by obtain h:= x.2.isLt; omega⟩
local notation "θ"=> hat_a
local notation "β"=> hed_a
lemma hat_mem(u:Glue): hat_a u∈ plusHalf:=by obtain ⟨u,v⟩:=u; fin_cases u<;> decide +revert
lemma hed_mem(u:Glue) : hed_a u∈ plusHalfᶜ:=by obtain ⟨u,v⟩:= u; fin_cases v<;> decide +revert
-- drizzle 4 sparse vectors basis for 2x2. dual extract
lemma roll_cast (u v:Axis): ∑ i:Glue, star (drizzle u (hat_a i) (hed_a i))* drizzle v (hat_a i) (hed_a i)= if u=v then 2 else 0:=by
 let κ:= (2:ℂ)
 have h00: drizzle 0 0 2= -(Complex.I* (0)):=rfl
 have h01: drizzle 0 0 3= -(Complex.I* (-I)):=rfl
 have h02: drizzle 0 1 2= -(Complex.I* (-I)):=rfl
 have h03: drizzle 0 1 3= -(Complex.I* (0)):=rfl
 have h10: drizzle 1 0 2= -(Complex.I* (0)):=rfl
 have h11: drizzle 1 0 3= -(Complex.I* ((-1))):=rfl
 have h12: drizzle 1 1 2= -(Complex.I* (1)):=rfl
 have h13: drizzle 1 1 3= -(Complex.I* (0)):=rfl
 have h20: drizzle 2 0 2= -(Complex.I* ((-I))):=rfl
 have h21: drizzle 2 0 3= -(Complex.I* (0)):=rfl
 have h22: drizzle 2 1 2= -(Complex.I* (0)):=rfl
 have h23: drizzle 2 1 3= -(Complex.I* (I)):=rfl
 have h30: drizzle 3 0 2= -(Complex.I* (1)):=rfl
 have h31: drizzle 3 0 3= -(Complex.I* (0)):=rfl
 have h32: drizzle 3 1 2= -(Complex.I* (0)):=rfl
 have h33: drizzle 3 1 3= -(Complex.I* (1)):=rfl
 fin_cases u <;> fin_cases v <;> simp only [Fintype.sum_prod_type, Glue, Fin.sum_univ_two, show ∀ i:Fin 2, θ (0,i)=0 from (fun i=>rfl), show ∀ i:Fin 2,θ (1,i)=1 from (fun i=>rfl), show ∀ i:Fin 2,β (i,0)=2 from (fun i=>rfl), show ∀ i:Fin 2,β (i,1)=3 from (fun i=>rfl)] <;> (first|rw [if_pos (by decide)]|rw [if_neg (by decide)]) <;>
   simp only [show (⟨0,by decide⟩:Axis)=0 from rfl,show (⟨1,by decide⟩:Axis)=1 from rfl,show (⟨2,by decide⟩:Axis)=2 from rfl,show (⟨3,by decide⟩:Axis)=3 from rfl,h00, h01, h02, h03, h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33] <;> norm_num
abbrev buffer (p:Space3):= leer (pulseG G p)^8
-- `trace`. aim ∘ sax * −i = depth contraction. `flute` normalization τ I. coeff includes weight gain/2 etc. want = ∫ W. 
def weigh (i:Glue):ℂ:= ((gain:ℂ)/τ)*(-Complex.I)/2 * ∑ j:Axis, ((sailX G j):ℂ)*star (drizzle j (θ i) (β i))
def shear(x:E4):ℂ:= ∑ i:Glue,weigh G i* spiral x (θ i) (β i)
private lemma shear_Q(x:E4) : shear G x = (-Complex.I/τ)* (∑ i:Axis,((sailX G i):ℂ)* sax i x):= by
 unfold shear weigh spiral; simp_rw [Matrix.sum_apply,Matrix.smul_apply, Finset.mul_sum, smul_eq_mul,Finset.sum_mul]; -- tune
 let a(i:Glue)(j:Axis):=drizzle j (θ i) (β i); let u(i:Axis):= ((sailX G i):ℂ); let z:=(gain:ℂ) /τ* (-I)/2; let v(i:Axis):= (↑(gain⁻¹:ℝ):ℂ)*sax i x
 rw [sum_comm]; refine Finset.sum_congr rfl fun i p=>?_ ; rw [sum_comm]; change ∑ j:Axis,∑ k:Glue,z*(u j*star (a k j))*(v i*a k i)= _; have he (j:Axis): ∑ k:Glue,z*(u j*star (a k j))*(v i*a k i)=(z*u j*v i)*(if j=i then 2 else 0):=by rw [←roll_cast, Finset.mul_sum]; apply sum_congr rfl; intro k _; unfold a; ring
 simp_rw [he]; simp only [mul_ite,mul_zero,Finset.sum_ite_eq',mem_univ,true_and,↓reduceIte]; change z*u i*v i*2=(-I/τ)*(u i*sax i x); unfold z v; have he:gain≠0:=gain_h.ne'; have hv:τ≠0:=tau_pos.ne'; rw [ofReal_inv]; field_simp
-- ∑ sail_i*fl = τ I . W.
private lemma pool(h:p≠0) : ∑ i:Axis, ((sailX G i):ℂ)*flute G p i= (τ:ℂ)*Complex.I*buffer G p:= by
 let E:= ‖p‖; let u:= sailX G; let v:= seedX G p; let q(i:Axis):= (u i:ℂ); let f:= pulseG G p; have he : (∑ i:Axis, q i*f i)= Complex.I*‖p‖:=by
    unfold q u f pulseG; simp only [Pi.add_apply,mul_add, Finset.sum_add_distrib,Pi.smul_apply,smul_eq_mul]; rw [show ∑ i:Axis,((sailX G i):ℂ)*brushQ (seedX G p) i=(0:ℂ) from ?_]; swap; · unfold brushQ Fir.tmap; norm_cast; rw [←pis, real_inner_comm,sail_zero];
    let J:= Complex.I*‖p‖; rw [Finset.sum_congr rfl (g:=fun i=>J*(q i*brushQ u i)) (fun i _=>mul_left_comm ..), ←mul_sum, show ∑ i:Axis,q i*brushQ u i=1 from ?_]; swap; · unfold q u brushQ Fir.tmap; norm_cast; rw [←pis]; exact billS G
    rw [mul_one,zero_add]
 let A:ℂ:= ((τ/‖p‖ : ℝ):ℂ); let B:=buffer G p; have ht: ∀ i:Axis, q i*flute G p i=(A*B)*(q i*f i):=by intro; unfold flute A B f buffer; ring
 change ∑ i:Axis, q i * flute G p i= _; simp_rw [ht]; rw [←mul_sum,he]; unfold A; change _=(τ:ℂ)*Complex.I* B; rw [ofReal_div]; have hx:‖p‖≠0:= norm_ne_zero_iff.mpr h; field_simp -- tune commute.

lemma market_int (t:20<depthG G x) : Integrable (fun p:Space3=> buffer G p *rise (pulseG G p) x):=by
 let b:= depthG G x-20; apply Integrable.mono' (exp3 b (sub_pos.mpr t)) (by unfold buffer rise; fun_prop) ?_
 filter_upwards with p; rw [norm_mul,loftB]; unfold buffer; apply (mul_le_mul_of_nonneg_right (bump G (p:=p)) (Real.exp_pos _).le).trans; rw [←Real.exp_add]; unfold b; apply Real.exp_monotone; apply le_of_eq; ring
lemma market_Q (t:20<depthG G x): shear G x=∫ p:Space3,buffer G p*rise (pulseG G p) x:=by
 rw [shear_Q]; simp_rw [serenade G _ x t,← integral_const_mul]; rw [←integral_finsetSum (s:=(univ:Finset Axis)),←integral_const_mul]; swap; · intro i _; exact (omega_int G i x t).const_mul _
 apply integral_congr_ae; filter_upwards [zero_free _] with p h; simp_rw [← mul_assoc (↑(sailX G _):ℂ)]; -- Invalid index
 rw [←sum_mul,pool G p h]; have ht: τ≠0:= tau_pos.ne'; field_simp; ring_nf; simp
variable (L:FilterK)
def garnet(p:Space3):= L.pay G p * buffer G p
@[fun_prop] lemma garnet_safe : Continuous (garnet G L):=by unfold garnet buffer; fun_prop
-- shifted.X offset representation right. scales local R_
lemma garnet_tee (t: ∀ i∈L.s,20 < depthG G (x+emitX i)) : Integrable (fun p:Space3=> garnet G L p*rise (pulseG G p) x) ∧ ∫ p:Space3,garnet G L p*rise (pulseG G p) x=∑ i∈ L.s,L.f i *shear G (x+emitX i):=by
 let f(a:Cover)(p:Space3):= L.f a*(buffer G p * rise (pulseG G p) (x+emitX a)); have he: (fun p=>garnet G L p*rise (pulseG G p) x)= fun p=>∑ i∈L.s,f i p:=by ext1 p; unfold garnet FilterK.pay; rw [Finset.sum_mul,Finset.sum_mul]; apply sum_congr rfl; intro i _; unfold f; rw [rise_add,gust_R]; ring
 have hp(i:Cover)(p:i∈L.s): Integrable (f i):= (market_int G _ (t i p)).const_mul _; rw [he]; constructor; · exact integrable_finsetSum _ hp
 rw [integral_finsetSum _ hp]; refine Finset.sum_congr rfl fun i v=>?_ ; unfold f; rw [integral_const_mul, market_Q G _ (t i v)]
-- filter growth price.
lemma garnet_cost : ∃ α τ':ℝ,0<α ∧ 0<τ'∧ ∀ p:Space3, ‖garnet G L p‖ ≤ τ'*Real.exp (α*‖p‖):=by
 obtain ⟨z,u⟩:=(L.s.finite_toSet.image (fun i=>-(depthG G (emitX i)))).bddAbove; let b:= |z|+21; let B:=∑ i∈L.s,‖L.f i‖; refine ⟨b,B+1,?_,?_,fun v=>?_ ⟩; · unfold b; positivity
 · unfold B; positivity
 let f(i:Cover):= L.f i*gust G v i; change ‖(∑ i∈ L.s,f i)*leer (pulseG G v)^8‖ ≤ _; have ht:∀ i∈ L.s,‖f i‖ ≤ ‖L.f i‖*Real.exp (|z| *‖v‖):= by
    intro i x; obtain h:= u (Set.mem_image_of_mem _ x); unfold f; rw [norm_mul,gust_R,loftB]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (norm_nonneg _); rw [neg_mul, ← mul_neg, mul_comm]; exact mul_le_mul_of_nonneg_right (h.trans (le_abs_self _)) (norm_nonneg _)
 rw [norm_mul]; refine (mul_le_mul ((norm_sum_le ..).trans (sum_le_sum ht)) (bump G) (norm_nonneg _) (by positivity)).trans ?_; rw [←sum_mul]; unfold b; change B*Real.exp _*_≤_; rw [mul_assoc,←Real.exp_add]; gcongr; linarith; linarith [norm_nonneg v] -- tune
#print axioms garnet_tee
end YM.CF.Window.ArchiveK
