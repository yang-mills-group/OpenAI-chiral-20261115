import YM.SU5.Reconstruction.Anvil.Arch
/-! # depot within Arc. Unique paying choice (may vary per boundary point). -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Anvil
open Function Set Metric Filter
open scoped Topology BigOperators
local notation "π"=> Real.pi
local notation "ℭ"=> circleMap 0 1
variable {n:ℕ}
namespace Score
variable (C: Score n) (r:ℝ) (i:Spin n) (a:ℝ)
local notation "P" i:max=> C.post i
local notation "P'" i:max=> C.post (shift i)
local notation "Ω" i:max => Real.cos (C.span i)
local notation "Σ'" i:max => Real.sin (C.span i)
local notation "U" i:max => Ioo (C.past i) (C.future i)
local notation "ŵ" q:max i:max=> Real.cos (q-C.middle i)
local notation "D" i:max=> C.radial i (ℭ r)
local notation "α" i:max=> draft (C.post i) 1 (ℭ r)
local notation "β" i:max=> draft (C.post (shift i)) 1 (ℭ r)
def represents (z:ℂ):= (a:ℂ)*C.jet i z/(cove (P i) z*cove (P' i) z)
abbrev raymark (r a:ℝ) := a^2*((1+ŵ r i)/(ŵ r i-Ω i))
section arcs
variable {j:Spin n} (h:r∈ Ioo (C.past j) (C.future j))
local notation "R" i:max => C.represents i a (ℭ r)
lemma post_rim (i:Spin n): C.post i∈ Rim:= normP _
lemma middle_span (i:Spin n): C.middle i ∈ U i:= by
  constructor <;> change _ < _ <;> unfold middle <;> linarith [(C.bud i).1,show C.past i+2*C.span i=C.future i from rfl]
include h
private lemma nonzero_stamp : ŵ r i - Ω i ≠ 0 ∧ α i≠0 := by
  constructor; · rcases eq_or_ne i j with rfl|p; exact (sub_pos.mpr (C.off_center h)).ne'; exact (sub_neg.mpr (C.unlit i p h)).ne
  exact crystal_ne.mp (cove_pos (C.post_rim i) (C.not_post r h _))
private lemma aperture : 1/α i-1/β i=((Σ' i/(ŵ r i-Ω i):ℝ):ℂ)*Complex.I:=by
  have e:= C.nonzero_stamp r i h; have e':= C.nonzero_stamp r (shift i) h; have H: D i ≠0:= div_ne_zero (pillar (normP _)) (pillar (normP _));
  rw [div_sub_div _ _ e.2 e'.2,one_mul,mul_one,C.frame_withdraw i r,C.frame_poles i r]
  let s:=Σ' i; let u:=ŵ r i-Ω i; change ↑(2*s)*_*D i / (↑((2:ℝ)*u)*D i)= ((s/u:ℝ):ℂ)*Complex.I; have v:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.1; push_cast; field_simp
lemma raymark_open : (R i)^2=(C.raymark i r a:ℂ):=by
 rw [represents,div_pow,mul_pow,mul_pow,cove,cove,crystal,crystal,C.frame_poles i r,C.brace i r]
 have h': D i ≠0:= div_ne_zero (pillar (normP _)) (pillar (normP _)); let s:= (1+ŵ r i); let u:= (ŵ r i-Ω i); change (a:ℂ)^2*(↑(2*s)*_) /(↑(2*u)*_)= ((a^2*(s/u):ℝ):ℂ); have v:(u:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (C.nonzero_stamp r i h).1; push_cast; field_simp
lemma ledger (A:Spin n→ℝ) (η:ℝ)(F:∀ i,(A i)^2*(1+Ω i)=η*Σ' i) : ∑ i,C.raymark i r (A i) = ∑ i,(A i)^2:=by
  let f (i:Spin n):=1/α i
  have H(i): C.raymark i r (A i)-(A i)^2=η*(Σ' i/(ŵ r i-Ω i)):=by
     have he:= (C.nonzero_stamp r i h).1; unfold raymark; let b:=A i; let x:=ŵ r i; let y:=Ω i
     rw [← mul_div_assoc,← mul_div_assoc,← F]; field_simp; ring
  have R0 : ∑ i: Spin n,(Σ' i/(ŵ r i-Ω i))=0:=by
    have he (i): (f i).im-(f (shift i)).im=Σ' i/(ŵ r i-Ω i):=by
      rw [←Complex.sub_im,C.aperture r i h]; simp only [Complex.mul_I_im,Complex.ofReal_re]
    simp_rw [← he]; rw [Finset.sum_sub_distrib]; apply sub_eq_zero.mpr; exact (Equiv.sum_comp (finRotate (n+1)) (fun i=>(f i).im)).symm -- tune
  apply sub_eq_zero.mp; rw [←Finset.sum_sub_distrib]; simp_rw [H]; rw [← Finset.mul_sum,R0,mul_zero]
lemma interior_cost (p:0<a):0<C.raymark j r a:=by
 let x:=ŵ r j; unfold raymark; have h1:=C.off_center h; have hz:= Real.neg_one_le_cos (C.span j); exact mul_pos (by positivity) (div_pos (by linarith) (sub_pos.mpr h1))
lemma uncovers (u:i≠j): C.raymark i r a≤0 :=by unfold raymark; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (div_nonpos_of_nonneg_of_nonpos (by linarith [Real.neg_one_le_cos (r-C.middle i)]) (sub_nonpos.mpr (C.unlit i u h).le))
-- R_j real on its own arc, indeed positive; others are pure imaginary
private lemma central (p:0<a): (R j).re≠0 ∧ (R j).im=0:=by
 have H':(R j).re^2-(R j).im^2=C.raymark j r a:=by rw [← sqc,C.raymark_open r j a h, Complex.ofReal_re]
 have he: (R j).re ≠ 0:=by intro F; rw [F] at H'; nlinarith only [H', C.interior_cost r a h p,sq_nonneg (R j).im]
 have E:(2*(R j).re)*(R j).im=0:=by rw [← sci,C.raymark_open r j a h, Complex.ofReal_im]
 exact ⟨he,(mul_eq_zero.mp E).resolve_left (mul_ne_zero (by norm_num) he)⟩
lemma pure_other (q:i≠j): (R i).re =0:= by
 have he:(R i).re^2-(R i).im^2=C.raymark i r a:=by rw [← sqc,C.raymark_open r i a h,Complex.ofReal_re]
 have E:2*(R i).re*(R i).im=0:=by rw [← sci,C.raymark_open r i a h,Complex.ofReal_im]
 by_contra b; rw [(mul_eq_zero.mp E).resolve_left (mul_ne_zero (by norm_num) b)] at he; nlinarith [C.uncovers r i a h q, sq_pos_of_ne_zero b]

omit h
private lemma realprod {a b:ℂ} (v:a≠0)(q:b≠0) (x:0≤ a.re)(y:0≤ b.re)(Z:a.im*b.im≤0): 0 < (a.sqrt*b.sqrt).re:=by
 have t:= crystal_real x v; have p:= crystal_real y q; rw [Complex.mul_re]; apply sub_pos.mpr; apply lt_of_le_of_lt _ (mul_pos t p)
 have he : (2*a.sqrt.re*(2*b.sqrt.re))*(a.sqrt.im*b.sqrt.im)= a.im*b.im := Eq.trans (show _= (a.sqrt^2).im*(b.sqrt^2).im from (by rw [sci,sci]; ring)) (by rw [crystal,crystal]); by_contra! v; exact not_lt_of_ge Z (he ▸ mul_pos (by positivity) v)
private lemma central_point (i:Spin n) (p:0<a): 0< (C.represents i a (ℭ (C.middle i))).re:=by
 let t:=C.middle i; let e:=C.middle_span i; let z:= ℭ t; let h: z ∈ Pane:= sphere_subset_closedBall (normP t); have x(k): draft (P k) 1 z≠0:= crystal_ne.mp (cove_pos (C.post_rim k) (C.not_post _ e k)); let u:= cove (P i) z*cove (P' i) z
 have b:0<u.re:=by
   apply realprod (x _) (x _) (onDisc (C.post_rim i) h) (onDisc (C.post_rim (shift i)) h); rw [post_next]; simp only [draft,post,Complex.ofReal_one,one_mul,z,div_c,Complex.sub_im,im_c,Complex.one_im]; rw [show t-C.past i=C.span i from by unfold t middle; ring, show t-C.future i= -(C.span i) from by unfold t middle future; ring, Real.sin_neg]; nlinarith only [sq_nonneg (Real.sin (C.span i))]
 have hQ: u≠0:=by intro v; simp [v] at b
 change 0< ((a:ℂ)*C.jet i z/u).re; unfold jet radial z; rw [div_self (pillar (normP _)), show (1:ℂ)+1=2 from by norm_num,Complex.div_re]; simp; have ht:= Complex.normSq_pos.mpr hQ; positivity
include h
private lemma arc_cont : ContinuousAt (fun x:ℝ=> C.represents i a (ℭ x)) r:= by
 let z:=ℭ r; let t:z∈Pane:= sphere_subset_closedBall (normP r); have d : Continuous (C.jet i):= by unfold jet radial; fun_prop
 refine ContinuousAt.comp (g:=C.represents i a) ?_ (continuous_circleMap ..).continuousAt
 exact ((continuousAt_const.mul d.continuousAt).div ((cove_cont (C.post_rim i) t).mul (cove_cont (C.post_rim (shift i)) t)) (mul_ne_zero (cove_pos (C.post_rim i) (C.not_post r h _)) (cove_pos (C.post_rim (shift i)) (C.not_post r h _))))
lemma arc_payment (p:0<a):0< (R j).re ∧ (R j).im=0:=by
  let f (x:ℝ):=(C.represents j a (ℭ x)).re; refine ⟨?_, (C.central r a h p).2⟩
  by_contra! Q
  have e:ContinuousOn f (U j):= fun w p=> (Complex.continuous_re.continuousAt.comp (C.arc_cont w j a p)).continuousWithinAt
  obtain ⟨u,v,g⟩:= isPreconnected_Ioo.intermediate_value h (C.middle_span j) e (show 0∈Icc (f r) _ from ⟨Q,(C.central_point a j p).le⟩)
  exact (C.central u a v p).1 g -- central order
end arcs
end Score
end YM.Anvil
