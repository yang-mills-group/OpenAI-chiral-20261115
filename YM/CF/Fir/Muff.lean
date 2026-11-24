import YM.CF.Fir.Kappa
set_option autoImplicit false
noncomputable section
namespace YM.CF.Fir
open Function Filter Lattice Laurent Bloch Next.Free Metric Finset
open scoped Topology Matrix BigOperators

/-- power, allows high moment arms. -/
def muff (j:ℕ)(N:Side)(p:Momentum) := (∏ i, plank N (p i))^j
@[simp] lemma muff_zero (j N): muff j N 0=1:=by simp [muff]
@[simp] lemma muff_one (j p) : muff j 1 p=1:=by simp [muff]
lemma muff_even (j:ℕ)(N:Side)(h:Odd N.val)(p:Momentum): muff j N (-p)=muff j N p:=by simp [muff,plank_even N h]
lemma muff_real (j:ℕ)(N:Side)(h:Odd N.val)(p:Momentum)(hp:physical p): star (muff j N p)=muff j N p:=by
  have he (i:Axis) : star (p i)=p i:=congr_fun hp i
  unfold muff; simp only [star_pow,star_prod,plank_bar,he,plank_even N h]
lemma muff_join (j:ℕ)(L M:Side)(h:Odd L.val)(e:Odd M.val)(p:Momentum) : muff j (L*M) p=muff j L (M.val • p)*muff j M p:=by
  have he : ∀ i:Axis, plank (L*M) (p i)=plank L ((M.val • p) i) * plank M (p i):= fun i=> by simpa [nsmul_eq_mul] using (plank_bind L M h e (p i)).symm
  unfold muff; simp_rw [he, Finset.prod_mul_distrib,mul_pow]
lemma muff_period (j N)(p:Momentum)(x:Cover): muff j N (p+reciprocal x)=muff j N p:=by simp only [muff,Pi.add_apply,reciprocal,plank_repeat]
lemma alias_muff (j:ℕ) (hj:0<j) (N:Side) (l:Site N) (hN:Odd N.val) (he:l≠0): muff j N (aliasAt 0 l)=0:=by
  obtain ⟨i,hi⟩ := hit_grade l; have hg:=grade_gt he
  have hh : lift l i ≠0:=by intro h; simp_all [up]
  let z:= aliasAt (0:Momentum) l i
  have hc : chip z≠0:=by
    rw [ne_eq]; intro hd
    have hb := meter.below z (zone_in_disk _ (alias_in_cube zone_pos (cube_zero zone zone_pos) l hN) i)
    have hx:= scaled_alias_lower l (cube_zero zone zone_pos) i hh
    change zone * up l i ≤ (N.val:ℝ)*‖z‖ at hx; rw [hd,norm_zero] at hb
    exact (not_lt.mpr hb) (mul_pos meter.low_pos (pos_of_mul_pos_right ((mul_pos zone_pos (up_pos ..)).trans_le hx) (side_pos _).le))
  have hr : rail N z=0:=by
    have hb:=rail_chip N z
    rw [show (N.val:ℂ)*z=0+2*(Real.pi:ℂ)*(lift l i) from (by dsimp only [z]; rw [alias_value,mul_div_cancel₀ _ (side_ne _),Pi.zero_apply]),chip_repeat,chip_origin] at hb
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right hc)).resolve_left (side_ne N)
  have hp : plank N z=0:=by rw [plank,hr,mul_zero]
  unfold muff; rw [Finset.prod_eq_zero (Finset.mem_univ i) hp,zero_pow hj.ne']

variable {ι : Type*} (M L:ι→Side) (hm:∀ i, Odd (M i).val)(hl:∀ i, Odd (L i).val)(l:∀ i, Site (L i))
lemma muff_pay (j:ℕ) (L:ι→Side) (hl:∀ i, Odd (L i).val) (l:∀ i, Site (L i)) : Moderate (fun i=>decay j (l i)) fun i p=> muff j (L i) (aliasAt p (l i)) := by
  obtain ⟨B,hB,H⟩:= alias_rail
  refine ⟨zone,(B^4)^j,zone_pos,pow_pos (pow_pos hB _) _,fun i=>⟨fun p _=>?_,fun p hp=>?_⟩⟩
  · unfold muff plank rail twirl aliasAt; fun_prop
  dsimp only; rw [muff,norm_pow,norm_prod]
  calc
    _ ≤ (∏ a: Axis, (B*(up (l i) a)⁻¹))^j := pow_le_pow_left₀ (by positivity) (Finset.prod_le_prod (fun a _=>by positivity) (fun a _=> (H _ (hl i) p hp _ _).2)) j
    _ = _ := by rw [decay,mix, Finset.prod_mul_distrib]; simp [Axis,mul_pow]
lemma D_cost (M:ι→Side)(hm:∀ i,Odd (M i).val) : Moderate (fun _:ι=>1) fun i=>D (M i):=by
  have h := ink M (fun _=>1) hm (fun _=>odd_one) (fun _=>0)
  simpa [grade,pdist,lift,narrow,alias_zero_eq] using h
lemma C_cost (M:ι→Side)(hm:∀ i, Odd (M i).val) : Moderate (fun _:ι=>1) fun i=> Cminus (M i):= by
  unfold Cminus kin; exact (rad_mod M hm).sub ((Moderate.const (-1)).add (Moderate.sum _ _ (fun _=>zero_le_one) fun a _=> pl_mod M hm _))
include hl in
lemma ds_scaled (a:Axis): Moderate (fun i=> grade (l i)) fun i p=> ((L i).val:ℂ)*ds (M i) (aliasAt p (l i)) a := by
  have h : Moderate (fun i=>grade (l i)) fun i p=> ((L i).val:ℂ)*seedQ (M i) (aliasAt p (l i)) a:=
    (scaled_seed L M hl l (fun _=>a)).raise_price (fun i=>up_le ..)
  have hx : Moderate (fun i=>grade (l i)) fun i p=> ((L i).val:ℂ)*seedQ (M i) (-aliasAt p (l i)) a:=by
    have he:= ((scaled_seed L M hl (fun i=> -l i) (fun _=>a)).raise_price (u:=fun i=>grade (-l i)) (fun i=>up_le ..)).reverse
    simpa only [alias_reverse _ (hl _),grade,pdist_neg] using he
  convert (Moderate.const (Complex.I/2)).mul (hx.sub h) using 2
  · simp
  ext p:1; rw [sin_seed]; ring
lemma ds_cost (M:ι→Side) (a): Moderate (fun _:ι=>1) fun i p=> ds (M i) p a:=by
  have h:= ds_scaled M (fun _=>1) (fun _=>odd_one) (fun _=>0) a
  simpa [grade,pdist,lift,narrow,alias_zero_eq] using h
end YM.CF.Fir
