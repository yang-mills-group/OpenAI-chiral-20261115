import YM.SU5.SatinWard.Resolution.CanvasAr
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.MeshClock
open Function Set Filter Metric
open scoped Topology NNReal
namespace Carousel
/- real funding of Holder from many single-axis steps. -/
variable (M: Mesh){G I:Type*}[NormedAddCommGroup G]{α x y K C:ℝ}(p:0<α) (h:G→ G) {f:ℝ→ G}
local notation "σ" h:max=> (mill M h:ℝ)
local notation "κ"=> coinB M α
local notation "Λ"=> (M.L:ℝ)
noncomputable abbrev arcStage (n:ℕ)(x:ℝ) :=⌊x/(mill M n:ℝ)⌋₊
noncomputable def arcTick (n:ℕ)(x:ℝ):ℝ:= arcStage M n x*(mill M n:ℝ)
variable (hx:0≤ x) {n:ℕ}
local notation "P" h:max=> arcTick M h x
local notation "u" t:max=> arcStage M t x
lemma gears : Tendsto (fun v=> (mill M v:ℝ)) atTop (𝓝 0):= NNReal.tendsto_coe.mpr (MeshClock.vanishes M)
include hx
lemma arc_price(v:ℕ) : arcTick M v x ≤ x ∧ x < arcTick M v x+(mill M v:ℝ):=by
 let u':= (u v); let h:=gear_pos M v; constructor
 · exact (le_div_iff₀ h).mp (Nat.floor_le (by positivity : 0 ≤ x/(σ v)))
 have h':x/(σ v)<(u'+1:ℕ):= Nat.lt_of_floor_lt (Nat.lt_succ_self u'); have he:=(div_lt_iff₀ h).mp h'; change x<(u':ℝ)*σ v+σ v; push_cast at he; linarith -- name he!!
lemma arc_switch(v:ℕ) : ∃ i:ℕ,i ≤ M.L∧ P (v+1)=P v+(i:ℝ)*σ (v+1):=by
 let t:= P v; let S:=P (v+1); let a:= u (v+1); let b:= u v; have hv: b*M.L ≤ a:=by
    let h':= gear_pos M (v+1); apply (Nat.le_floor _); push_cast; rw [le_div_iff₀ h',mul_assoc,←speedup]; exact (arc_price M hx v).1
 obtain ⟨i,y⟩:=Nat.exists_eq_add_of_le hv
 have he:P (v+1)=P v+(i:ℝ)*σ (v+1):=by
    change (a:ℝ)*σ (v+1)=_+_; rw [y]; -- `unfold arcTick` rewrites sigma inside b def, maybe ring
    change ((b*M.L+i:ℕ):ℝ)* σ (v+1)= (b:ℝ)*σ v+_; rw [speedup M v]; push_cast; ring
 refine ⟨i, ?_, he⟩; have h0:= arc_price M hx v; have h1:= (arc_price M hx (v+1)).1; rw [he] at h1
 have hp: t+i*(σ (v+1)) < t+ (M.L:ℝ)*(σ (v+1)):= (h1.trans_lt h0.2).trans_eq (congrArg (t+·) (speedup ..)); have ht: (i:ℝ) < M.L:=lt_of_mul_lt_mul_right (lt_of_add_lt_add_left hp) (gear_pos M (v+1)).le; exact_mod_cast ht.le -- ambiguous `+` notation. names.
lemma arc_pass : Tendsto (fun v:ℕ=>arcTick M v x) atTop (𝓝 x):=by
 have h:Tendsto (fun v:ℕ=> x-(mill M v:ℝ)) atTop (𝓝 x):=by simpa using (gears M).const_sub x
 refine tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun i=>?_) (fun i=> (arc_price M hx i).1); exact (sub_lt_iff_lt_add.mpr (arc_price M hx i).2).le
lemma arc_depart (hx':x<(mill M n:ℝ)) : arcTick M n x=0:=by have h:arcStage M n x<1:=(Nat.floor_lt (show 0≤ x/(σ n) by have h:=gear_pos M n; positivity)).mpr (by rw [Nat.cast_one,div_lt_one (gear_pos ..)]; exact hx'); rw [arcTick,show arcStage M n x=0 from (by omega),Nat.cast_zero,zero_mul]
omit hx
variable (hc:Continuous f) (U: 0≤ K) -- remove v
variable (F: ∀ (x:ℝ)(v:ℕ), ‖f (x+(mill M v:ℝ))-f x‖ ≤ K*(mill M v:ℝ)^α)
include F hc p U hx
lemma broke (v:ℕ) : ‖f (y+x)-f (y+P v)‖ ≤ roseMax M α*K*(σ (v+1))^α:=by
 let s:= σ (v+1); let h₁:=gear_pos M (v+1); let X(n:ℕ):= f (y+P (n+v)); let E:=Λ*K* (s^α); let he:=gear_inc M
 have hp (n:ℕ):dist (X n) (X (n+1))≤ E*κ^n:=by
    let j:= n+v; let A:=σ (j+1); have hA:0<A:=gear_pos ..; let T':=K*A^α; let h':=F (y+ P j) (j+1)
    unfold X; rw [dist_eq_norm,norm_sub_rev,Nat.add_right_comm n 1 v]; obtain ⟨i,h,e⟩:=arc_switch M hx j; change ‖f (y+arcTick M (j+1) x)-_‖ ≤ _; rw [e,←add_assoc,←nsmul_eq_mul] -- nsmul wrong orientation
    refine le_trans (creep (K*(A^α)) f (y+ P j) A (fun x=> F x _) i) ((mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ)|>.mpr h) (by positivity)).trans_eq ?_)
    have hv: A^α=s^α*κ^n:=by unfold A s; rw [show j+1=v+1+n from (by omega),rez ]
    unfold E; rw [hv]; ring -- indentation hv
 have h₀:Tendsto X atTop (𝓝 (f (y+x))):= (tendsto_add_atTop_iff_nat v).mpr ((hc.tendsto _).comp ((arc_pass M hx).const_add y)) -- needs `(f:=fun n=> f ...)`
 let T:=dist_le_of_le_geometric_of_tendsto₀ κ E (κ_small M p) hp h₀; unfold X at T; rw [dist_eq_norm,norm_sub_rev, Nat.zero_add] at T; exact T.trans_eq (by unfold E s roseMax; ring)
omit hx
variable (C₀:∀ x,‖f x‖≤ C)
include C₀
lemma wander_high (x:ℝ)(p0:0<x)(y:ℝ) :‖f (y+x)-f y‖≤ (2*C*((mill M 0:ℝ)^α)⁻¹+roseMax M α*K)*x^α:=by
 obtain hU:= gears M
 let t:=2*C*((mill M 0:ℝ)^α)⁻¹; have hc':0≤C:= (norm_nonneg _).trans (C₀ 0)
 obtain h:= gear_pos M 0; have ht:0≤t:=by unfold t; positivity
 let h':= Real.rpow_pos_of_pos p0 α
 by_cases s: σ 0 ≤x
 · let q:= Real.rpow_le_rpow h.le s p.le; change _ ≤(t+_)*_; refine (norm_sub_le ..).trans ((add_le_add (C₀ _) (C₀ _)).trans ?_); calc
       _= t*((σ 0)^α):=by unfold t; field_simp; ring
       _≤ (t+roseMax M α*K)*x^α:=mul_le_mul (le_add_of_nonneg_right (mul_nonneg (rosePos M p).le U)) q (Real.rpow_pos_of_pos h _).le (by have hu:=rosePos M p; positivity)
 have hv:∃ n:ℕ, σ n≤ x:= (hU.eventually (ge_mem_nhds p0)).exists; let n:= Nat.find hv; have k:σ n≤x:= Nat.find_spec hv; have g:0 < n:= by by_contra! g; exact s ((show n=0 from Nat.le_zero.mp g) ▸ k)
 let d:= n-1; have h0: d<n:= by omega
 have hm:x< σ d:= lt_of_not_ge (Nat.find_min hv h0)
 have hx:= broke (f:=f) (y:=y) M p p0.le hc U F d; rw [arc_depart M p0.le hm, add_zero] at hx; let e:= Real.rpow_le_rpow (gear_pos M (d+1)).le (show σ (d+1)≤x from (by rw [show d+1=n from (by omega)]; exact k)) p.le; exact hx.trans (mul_le_mul (le_add_of_nonneg_left ht) e (by apply Real.rpow_nonneg (gear_pos ..).le) (add_nonneg ht (mul_nonneg (rosePos M p).le U))) -- order broke params
lemma polar_arc(x y:ℝ): ‖f (y+x)-f y‖ ≤ (2*C*((mill M 0:ℝ)^α)⁻¹+roseMax M α*K)* |x|^α:=by
 rcases lt_trichotomy 0 x with h|h|h
 · rw [abs_of_pos h]; exact wander_high M p hc U F C₀ x h y
 · subst x; simp [p.ne']
 have hx:=wander_high M p hc U F C₀ (-x) (neg_pos.mpr h) (y+x); rw [←sub_eq_add_neg,add_sub_cancel_right] at hx; rw [norm_sub_rev,abs_of_neg h]; exact hx
#print axioms polar_arc
end Carousel
end YM.CF.Buffered.Afterglow.Tower.MeshClock
