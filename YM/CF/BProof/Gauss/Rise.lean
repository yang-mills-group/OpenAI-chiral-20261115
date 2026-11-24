import YM.CF.BProof.Gauss.Host

/- Lower mass estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gauss
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Roll Precision
open scoped Topology BigOperators Classical Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable {s:Side}(Y:Yard s)(T:PathData G)(M:ℕ)(c:Clip)(θ:ℝ)(S:Finset Y.Col)(w:Y.Branch)

def diff (b:Y.Door) := w b-shade Y b w
def toll (b:Y.Col) := ∑ i:Y.Apt,‖diff Y w (b,i)‖^2
lemma toll_est (b:Y.Col)(r:Fin Y.short)(i:TAxis): ‖w (b,r,i)‖ ≤ (r.val+1)*Real.sqrt (toll Y w b):=by
 have H (r:Fin Y.short): ‖diff Y w (b,r,i)‖ ≤ Real.sqrt (toll Y w b):= Real.le_sqrt_of_sq_le (single_le_sum (f:=fun i=>‖diff Y w (b,i)‖^2) (fun _ _=>sq_nonneg _) (mem_univ (r,i)))
 let k:=Real.sqrt (toll Y w b); have he(n:ℕ)(h:n<Y.short) : let r:Fin Y.short:=⟨n,h⟩; ‖w (b,r,i)‖ ≤ ((n:ℝ)+1)*k:=by
    induction n with
    | zero=> intro r; have hp:diff Y w (b,r,i)=w (b,r,i):=by unfold diff shade; rw [show Y.project b.2 i b.1 r.val=none from proj0 ..]; change w _-0=w _; rw [sub_zero] -- tune
             simpa only [hp,Nat.cast_zero,zero_add,one_mul] using H r
    | succ n ih=> intro r; let r':Fin Y.short:=⟨n,by omega⟩; have hp:diff Y w (b,r,i)=w (b,r,i)-w (b,r',i):=by unfold diff shade; rw [show Y.project b.2 i b.1 r.val=some (b,r',i) from Y.projd b.1 b.2 i r']; rfl
                  have hx:= norm_le_norm_sub_add (w (b,r,i)) (w (b,r',i)); rw [←hp] at hx; convert hx.trans ((add_le_add (H r) (ih r'.isLt)).trans_eq (show k+ (n+1:ℝ)*k=((↑(n+1:ℕ):ℝ)+1)*k by push_cast; ring))
 exact he r.val r.isLt
lemma payable (b:Y.Col) : ∑ i:Y.Apt,‖w (b,i)‖^2 ≤ (3*(Y.short:ℝ)*(Y.short:ℝ)^2)*toll Y w b:= by
 let x(i:Y.Apt):=‖w (b,i)‖
 have H (i:Y.Apt) : ‖w (b,i)‖^2≤ (Y.short:ℝ)^2*toll Y w b := by
    have hp:0≤ toll Y w b:=sum_nonneg fun _ _=>sq_nonneg _; rw [← Real.sq_sqrt hp,← mul_pow]; apply pow_le_pow_left₀ (norm_nonneg _); apply le_trans (toll_est Y w b i.1 i.2); gcongr; exact_mod_cast i.1.isLt
 apply (sum_le_sum (fun i _=>H i)).trans; rw [sum_const,card_univ,nsmul_eq_mul,show Fintype.card Y.Apt=Y.short*3 from by simp [Apt,TAxis]]; push_cast; exact le_of_eq (by ring)
private lemma good_r (K: Charge.Room Y M)(b:Y.Door)(p:b.1∉ S): Sum.inl (Y.rise b)∈ good Y M S:=mem_filter.mpr ⟨mem_univ _,ripe Y _, (rises_c Y M S K b).2 p⟩
lemma start_pos (K: Charge.Room Y M)(h:0≤θ): θ*c.direct*(∑ b∈ Sᶜ,toll Y w b) ≤ 2*work Y M S c T θ w := by
 let f (b:Y.Door):Tile s:= .inl (Y.rise b); have hf: Injective f:=fun _ _ h=> Y.birth_inj (Sum.inl.inj h)
 let Z:= (Sᶜ)×ˢ (univ:Finset Y.Apt); let Q(a:Tile s):=2*Form.Q T M c θ a (Y.roll w)
 have hv(i):0≤Q i:=by unfold Q Form.Q; have hp:= (unit_p c i θ h).1; positivity
 unfold work; rw [mul_sum (s:=good Y M S)]; change _ ≤ ∑ i∈ _, Q i -- tune
 refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (f:=Q) (s:=Z.image f) (by intro y hx; obtain ⟨i,e,rfl⟩:=mem_image.mp hx; exact good_r Y M S K i (mem_compl.mp (mem_product.mp e).1)) (fun i _ _ => hv i)); rw [sum_image hf.injOn]; have ht(b:Y.Door): Q (f b)=θ*c.direct*‖diff Y w b‖^2:=by unfold Q f; rw [model_one ..]; unfold diff; ring
 simp_rw [ht]; unfold Z; rw [sum_product]; unfold toll; simp_rw [mul_sum]; exact le_rfl

def part (c:Clip)(d:ℕ):ℝ:=1/2*c.direct/(3*d*d^2)
def floor (c:Clip)(d:ℕ):ℝ:= min (part c d) 1
lemma part_p (d:ℕ)(h:0<d): 0<part c d:=by unfold part; have :=c.quadratic_pos; positivity
lemma floor_p (d:ℕ)(h:0<d): 0<floor c d:=by unfold floor; rw [lt_min_iff]; exact ⟨part_p c d h,zero_lt_one⟩
lemma floor_le (d:ℕ) : floor c d≤1:=min_le_right ..
lemma lower_pay (K:Charge.Room Y M)(h:1/2≤θ)(x: Plan Y) : floor c Y.short * dotProduct x x ≤ dotProduct x ((host Y T M c θ S)*ᵥx):=by
 let u:=Y.short; let B:=floor c u; let w:=lowerMap Y x; let t(b:Y.Col):=∑ i:Y.Apt,‖w (b,i)‖^2; rw [paycheck,tally]; change B*(∑ b,t b) ≤ (∑ b∈S,t b)+2*work Y M S c T θ w; rw [← sum_add_sum_compl S,mul_add]; have hp:0<(u:ℝ):=by exact_mod_cast Y.short_pos
 have hk:0<B:=floor_p c _ Y.short_pos
 apply add_le_add (mul_le_of_le_one_left (sum_nonneg fun b _=>sum_nonneg fun i _=>sq_nonneg _) (floor_le ..)) (le_trans _ (start_pos Y T M c θ S w K (by linarith)))
 rw [mul_sum,mul_sum]; refine sum_le_sum fun i hi=>?_ ; apply le_trans (b:= B * ( (3*(u:ℝ)*(u:ℝ)^2)*toll Y w i)) (mul_le_mul_of_nonneg_left (payable ..) hk.le)
 rw [← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun i _=>sq_nonneg _); have he:B≤(1/2*c.direct)/(3*u*u^2):= min_le_left .. -- tune Nat exponent casts
 exact ((le_div_iff₀ (by positivity)).1 he).trans (mul_le_mul_of_nonneg_right h c.quadratic_pos.le)
end YM.CF.BProof.Gauss
