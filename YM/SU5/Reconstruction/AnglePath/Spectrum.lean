import YM.SU5.Reconstruction.AnglePath.Energy
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

open Multiplier Chirp
open Complex
variable (C:Clasp J H D)
local notation "X'"=> spectrum ℂ C.angle
local notation "p"=> C.realF
local notation "V" =>C.motion
noncomputable def oracle(z:ℂ)(t:ℝ):ℂ:= exp ((1-z)*(Real.log t:ℝ) + z*(Real.log (1-t):ℝ))
noncomputable def spool(z:ℂ): J.Op:=order C.motion (oracle z ∘ C.realF)
abbrev scroll:Set ℂ := {z:ℂ | z.re ∈ Icc (0:ℝ) 1}
-- endpoint logs may not align at spectral x=0,1, but no endpoint mass whatsoever.
lemma oracle_cost {z:ℂ}(h:z∈scroll)(t:ℝ)(e:t∈Icc (0:ℝ) 1): ‖oracle z t‖ ≤ 1:= by
 unfold oracle; simp only [norm_exp,mul_re,add_re,sub_re,one_re,ofReal_im,ofReal_re,mul_zero,sub_zero,Real.exp_le_one_iff]; exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.2) (Real.log_nonpos e.1 e.2)) (mul_nonpos_of_nonneg_of_nonpos h.1 (Real.log_nonpos (sub_nonneg.mpr e.2) (sub_le_self _ e.1)))
lemma book(z:ℂ)(h:z∈scroll): Registers C.motion (oracle z ∘ C.realF) (spool C z):= order_reads _ ⟨by unfold oracle; fun_prop,1,zero_le_one,fun x=> oracle_cost h _ (C.price x)⟩
abbrev income:Set ℂ:= {z:ℂ| z.re∈ Ioo (0:ℝ) 1}
lemma interiorOpen : IsOpen income:= Complex.continuous_re.isOpen_preimage _ isOpen_Ioo
lemma deeply : income ⊆ scroll:= fun _ h=>⟨h.1.le,h.2.le⟩
lemma pathway : AnalyticOnNhd ℂ (spool C) income:=full_roofs V interiorOpen (fun z=> oracle z ∘ C.realF) 1 (spool C) (fun x u=>book C x (deeply u)) (fun y=>Differentiable.differentiableOn (by unfold comp oracle; fun_prop)) (fun x u y=>oracle_cost (deeply u) _ (C.price y)) (fun x=> by unfold oracle; fun_prop)
lemma pathway_w (x:J):ContinuousOn (fun z=> spool C z x) scroll:=by
 classical
 intro z h; let F(w:ℂ):= if w∈scroll then w else z
 have he(w:ℂ): F w∈scroll:= by unfold F; split <;> assumption
 have eq:F=ᶠ[𝓝[scroll] z] id:=Eventually.mono self_mem_nhdsWithin (fun x hx=> if_pos hx)
 apply Tendsto.congr' (f₁:=fun w=> spool C (F w) x) (eq.mono fun w ew=> congrArg (fun z=>spool C z x) ew)
 refine Registers.tends _ _ _ (book C z h) (fun w=> book C (F w) (he w)) x 1 (Eventually.of_forall fun w=> Eventually.of_forall (fun u=> oracle_cost (he w) _ (C.price u))) ?_
 apply Eventually.of_forall; intro u; exact ( (show Continuous (fun z=> oracle z (p u)) from by unfold oracle; fun_prop).continuousWithinAt.tendsto.comp (tendsto_id.congr' eq.symm)) -- wrong filters
private lemma oracle_eq_l(z:ℝ)(i:z∈Ioo (0:ℝ) 1): oracle 0 z=(z:ℂ) :=by simp only [oracle,sub_zero,one_mul,zero_mul,add_zero, ← ofReal_exp, Real.exp_log i.1]
private lemma oracle_eq_r(z:ℝ)(i:z∈Ioo (0:ℝ) 1): oracle 1 z=((1-z:ℝ):ℂ) :=by simp only [oracle,sub_self,one_mul,zero_mul,zero_add, ← ofReal_exp, Real.exp_log (sub_pos.mpr i.2)]
private lemma oracle_pos(z:ℝ)(t:ℝ) : 0≤ oracle (t:ℂ) z:=by
 rw [show oracle (t:ℂ) z= (↑(Real.exp ((1-t)*Real.log z+t*Real.log (1-z))):ℂ) from ?_]; swap; · unfold oracle; push_cast; rfl
 exact mod_cast (Real.exp_pos _).le
lemma spool_first : spool C 0=C.angle:= by
 have h:=book C 0 (by simp [scroll]); exact h.single (C.angle_reads.agrees h.price (fun x=> (C.inOpen x).mono (fun u hu=> (oracle_eq_l _ hu).symm)))
lemma spool_last : spool C 1=1-C.angle:=by
 have h:=book C 1 (by simp [scroll]); refine h.single (((Registers.one V).sub C.angle_reads).agrees h.price (fun x=> (C.inOpen x).mono (fun u hu=>?_))); change 1- (C.realF u:ℂ)=oracle 1 (C.realF u); rw [oracle_eq_r _ hu]; push_cast; rfl
lemma peels : Commute (peel C.l) (peel C.r) := by
 apply rootComm; rw [peel,C.complement]; apply Commute.symm; apply rootComm; exact (Commute.one_left C.angle).sub_left (Commute.refl _)
private lemma spool_pos (t:ℝ)(x:(t:ℂ)∈scroll): 0 ≤ spool C t:=by
 let T:= spool C t; apply (ContinuousLinearMap.nonneg_iff_isPositive T).2; apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp; apply (LinearMap.isPositive_iff_complex _).2; intro u
 have hv: 0≤ inner ℂ u (spool C t u):= by rw [(book C (t:ℂ) x).awakes]; exact integral_nonneg (fun _=> oracle_pos ..)
 have he:0 ≤ inner ℂ (T u) u:= by rw [←inner_conj_symm]; simpa only [←Complex.star_def,star_nonneg_iff] using hv
 exact ⟨Complex.ext rfl he.2, he.1⟩
private lemma square_mid (x:ℝ): oracle (1/2) x * oracle (1/2) x= oracle 0 x*oracle 1 x:=by unfold oracle; rw [←Complex.exp_add,←Complex.exp_add]; ring_nf
local notation "U" => peel C.l
local notation "R" => peel C.r
lemma spool_mid : spool C (1/2)=peel C.l * peel C.r:=by
 let T:= C.angle*(1-C.angle); have he:( ((1/2:ℝ):ℂ))=1/2:= by push_cast; rfl
 let S:= spool C (1/2); have y:(1/2:ℂ)∈ scroll:= by rw [←he]; norm_num [scroll]
 have z : 0 ≤ spool C (1/2):= he ▸ spool_pos C (1/2) (he.symm ▸ y)
 have w:0 ≤ U*R:= Commute.mul_nonneg (positive_peel _) (positive_peel _) (peels C)
 have hx: S*S=T:=by
    have a:=book C _ y; apply (a.times a).single
    rw [show T=spool C 0 * spool C 1 from (by unfold T; rw [spool_first,spool_last]),show (oracle (1/2) ∘ p)*(oracle (1/2) ∘ p)=_ from funext fun x:X'=> show (oracle (1/2) ∘ p) x*(oracle (1/2) ∘ p) x= ((oracle 0 ∘ p)*(oracle 1 ∘ p)) x from square_mid (p x)]; exact (book C 0 (by simp [scroll])).times (book C 1 (by simp [scroll]))
 refine (CFC.sqrt_unique hx z).symm.trans (CFC.sqrt_unique ?_ w)
 have P': Commute (peel C.l) (peel C.r):=peels C
 unfold T; rw [mul_assoc,←mul_assoc R,←P'.eq,mul_assoc U R,←mul_assoc,peel_sq,peel_sq,C.complement]; rfl
end YM.CrossedFrame.Cardio
