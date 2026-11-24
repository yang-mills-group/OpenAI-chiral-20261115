import YM.SU5.WakeInvestment.Contracts

/-!
Compute (WA.11)'s logarithmic growth estimate instead as ODE for the polynomial *product*
at small parameter (the ones in `WickA`, WA.9). This even keeps real-part/sign of the estimates
and doesn't have to expand a matrix log. Must absorb both particle and hole for each copy, and
sum that cost at **operator quadratic-form** before paying against the signed Mark product.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Fock Lattice Finset NormedSpace Set
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I:Type*} [LinearOrder I] [Fintype I]
variable (P : Op I) {n:ℕ}

abbrev cloud {I:Type*} [LinearOrder I] [Fintype I] (A: FC I) (r:ℝ) : FC I := 1+r • A
def stripTil (F:Fin n→ FC I)(s:ℝ) := (List.ofFn fun i=> cloud (F i) s).prod

private lemma tilZero (F:Fin n→FC I) : stripTil F 0=1:=by
  induction n with
  | zero=>simp [stripTil]
  | succ n ih=> rw [stripTil,List.ofFn_succ,List.prod_cons]; let G : Fin n→ FC I:= fun j=> F j.succ; change (1+ (0:ℝ) • F 0)*stripTil G 0=_; simp [ih G]

private lemma strip_succ {n:ℕ} (F:Fin (n+1)→ FC I)(r:ℝ): stripTil F r=cloud (F 0) r* stripTil (F ∘ Fin.succ) r:=by
 rw [stripTil, List.ofFn_succ,List.prod_cons]; rfl

/-- The omission rule for the body *and* its derivative. -/
private theorem meddle (F:Fin n→ FC I) (e:∀ i j, Commute (F i) (F j)) (s:ℝ) :
    ∃ G:Fin n→FC I, (∀ i, cloud (F i) s * G i = stripTil F s) ∧
    HasDerivAt (stripTil F) (∑ i, F i * G i) s := by
 induction n with
 | zero=> refine ⟨F, fun i => Fin.elim0 i, ?_⟩; simp [show stripTil F=(fun x:ℝ=> (1:FC I)) by ext; simp [stripTil], hasDerivAt_const] -- ext tune
 | succ n ih=>
   let K:Fin n→FC I:= F ∘ Fin.succ; let V : ℝ→ FC I:= cloud (F 0); let u := V s
   obtain ⟨G,hp,h⟩:= ih K (fun i j=>e _ _); let W : Fin (n+1) → FC I := Fin.cons (stripTil K s) (fun i:Fin n=> u*G i)
   have hF(i:Fin n):Commute (K i) u:= (Commute.one_right (K i)).add_right ((e i.succ 0).smul_right s)
   refine ⟨W,?_,?_⟩
   · intro i; refine Fin.cases ?_ ?_ i
     · simp only [W,Fin.cons_zero,strip_succ]; rfl
     · intro i; have he: Commute (cloud (K i) s) u:= (Commute.one_left u).add_left ((hF i).smul_left s)
       rw [strip_succ]; change cloud (K i) s * Fin.cons (α:=fun _=> FC I) _ _ (Fin.succ i)=u*stripTil K s
       rw [Fin.cons_succ,←mul_assoc,he.eq,mul_assoc, hp]
   have hv : HasDerivAt V (F 0) s:=by
       have u:= ((hasDerivAt_const s (1:FC I)).add ((hasDerivAt_id' s).smul_const (F 0))) -- indentation?
       rw [one_smul, zero_add] at u; exact u
   have hx : ∑ i: Fin (n+1), F i * W i= F 0 * stripTil K s + V s * ∑ i:Fin n,K i * G i:= by
     rw [Fin.sum_univ_succ,mul_sum]; simp only [W,Fin.cons_succ,Fin.cons_zero]; congr 1; apply sum_congr rfl; intro i _; change K i * (u*_) = u * _; rw [←mul_assoc (K i), (hF i).eq,mul_assoc]
   rw [hx]; exact (hv.mul h).congr_of_eventuallyEq (Eventually.of_forall fun i => strip_succ F i)


/-- re-test each in tilted coordinates independently -/
def reopen (u:ℝ) (F:FC I) := wholeTilt P u * F * wholeTilt P (-u)

def rolling (F:Fin n→ FC I)(x:Wave I) (u:ℝ) : Wave I := acts (wholeTilt P (1-u)*stripTil F u) x

private theorem act_all (x:Wave I) {F:ℝ→FC I} {t:ℝ} {f:FC I} (h:HasDerivAt F f t) : HasDerivAt (fun i=> acts (F i) x) (acts f x) t:= by
 let U:FC I→ₗ[ℂ] Wave I:= ⟨⟨fun V=> acts V x,fun i j=>act_add ..⟩,fun c V=>act_smul ..⟩; let V:= U.toContinuousLinearMap.restrictScalars ℝ; exact V.hasFDerivAt.comp_hasDerivAt t h

/-- Differential identity at *actual* occupation, TiltGenerator. -/
private lemma conduct (F : Fin n→FC I) (e:∀ i j, Commute (F i) (F j)) (x:Wave I) (s:ℝ) :
    let f:= rolling P F x; let z(i):= reopen P (1-s) (F i)
    ∃ y:Fin n→Wave I, (∀ i, acts (cloud (z i) s) (y i)=f s) ∧ HasDerivAt f ((∑ i, acts (z i) (y i)) - acts (excit P) (f s)) s := by
  intro f z; obtain ⟨G,hg,h⟩:= meddle F e s; let V:=wholeTilt P (1-s); let Y(i):= V*G i
  have hv(i): z i*Y i = V*(F i*G i):=by
     let B:=wholeTilt P (-(1-s)); have ht:B*V=1:= mul_eq_one_comm.mp (wholeTilt_inv P (1-s)); unfold Y z reopen; unfold V; rw [←mul_assoc _ (wholeTilt P (1-s)),mul_assoc (_*F i) _ _,ht,mul_one,mul_assoc]
  refine ⟨fun i=>acts (Y i) x,fun i=>?_,?_⟩
  · rw [←act_mul]; change acts _ x=acts (V*stripTil F s) x; apply congrArg (fun P:FC I=> acts P x); rw [←hg i]; unfold cloud; rw [add_mul,one_mul, Algebra.smul_mul_assoc,hv,add_mul,one_mul,Algebra.smul_mul_assoc,mul_add,Algebra.mul_smul_comm]
  let A:=stripTil F s; let B:= (∑ i, F i* G i); let W(r:ℝ):= wholeTilt P (1-r); let d := W s * B-excit P * (W s * A); let u:= W * stripTil F; have hm:HasDerivAt W (-(excit P * W s)) s:=by
    let g:(ℝ→ℝ):=fun r=> 1-r; have H:HasDerivAt g (-1) s:= by simpa only [zero_sub] using (hasDerivAt_id' s).const_sub (1:ℝ)
    have hV: HasDerivAt (wholeTilt P) (excit P * wholeTilt P (g s)) (g s):=hasDerivAt_exp_smul_const' (excit P) (g s)
    have uP:= hV.scomp s H; rw [neg_smul,one_smul] at uP; exact uP
  have hu: HasDerivAt u d s:=(hm.mul h).congr_deriv (by change -(excit _ * W s)* A+ W s*B=d; unfold d; noncomm_ring)
  have hT : (∑ i, acts (z i) (acts (Y i) x)) - acts (excit P) (f s)= acts d x:=by
     simp_rw [←act_mul,hv,←act_sum,←mul_sum]; unfold f rolling; rw [←act_mul,←act_sub]
  rw [hT]; exact act_all x hu

variable (σ C:ℝ)
-- Each leaf's contribution in (1) staying on both sides as s F is advanced
private theorem suppress (a:0≤σ) (p:σ≤1/2)(s:ℝ)(u:|s| ≤ 1)(x y:Wave I) (A: FC I)(q:‖A‖≤σ)(v:acts (cloud A s) y=x) :
    (inner ℂ x (acts A y)).re ≤ (grain x A).re + 2* σ^2 * ‖x‖^2 := by
  let S:= s • acts A y; have hv:y+S=x:=by unfold cloud at v; rw [act_add,act_one,realScalarActs] at v; exact v
  have hy: ‖S‖ ≤ σ*‖y‖ :=by
    unfold S; rw [norm_smul,Real.norm_eq_abs]; exact (mul_le_of_le_one_left (norm_nonneg _) u).trans ((paid_normW A y).trans (by gcongr))
  have ht:‖y‖ ≤ 2*‖x‖:= by
    have hx:‖y‖≤ ‖x‖ + ‖S‖:= (show y=x-S from (eq_sub_of_add_eq hv)).symm ▸ norm_sub_le x S -- rewrites hy?
    nlinarith only [hx,hy,mul_le_mul_of_nonneg_right p (norm_nonneg y)]
  change _ ≤ (inner ℂ x (acts A x)).re + _
  apply sub_le_iff_le_add'.mp
  rw [←Complex.sub_re, ←inner_sub_right, ←map_sub,show y-x= -S from (by rw [←hv]; abel)]
  apply (Complex.re_le_norm _).trans; rw [map_neg,inner_neg_right,norm_neg]; apply (norm_inner_le_norm ..).trans
  refine (mul_le_mul_of_nonneg_left ((paid_normW ..).trans (mul_le_mul q (hy.trans (mul_le_mul_of_nonneg_left ht a)) (norm_nonneg _) a)) (norm_nonneg _)).trans_eq (by ring)

/-- Log Tangle lemma, right through the claimed WA estimates. Uses *real* part of the
integrated ticket for any assigned copies F (measured including the complex interpolation κ),
even when C may be negative. `x` here can vary arbitrarily. No Fresnel/positivity conjecture on
a contacted phase. Just Hilbert budget. -/
theorem engross (a:0 ≤ σ)(p:σ≤1/2)(x:Wave I)(F:Fin n→FC I)(e:∀ i j, Commute (F i) (F j))
    (hp:∀ i,∀ t:ℝ, |t| ≤ 1 → 0 ≤ t → ‖reopen P t (F i)‖ ≤ σ)
    (t:∀ y:Wave I,∀ t:ℝ, |t| ≤ 1 → 0 ≤ t → (∑ i, (grain y (reopen P t (F i))).re) ≤ C*‖y‖^2 + heatCost y P) :
    ‖acts (stripTil F 1) x‖ ≤ Real.exp (C+n*(2*σ^2)) * ‖acts (wholeTilt P 1) x‖ := by
  let f:= rolling P F x; let B:= C+n*(2*σ^2)
  have hd(s:ℝ) (v:s∈Icc (0:ℝ) 1) : ∃ f':Wave I, HasDerivAt f f' s ∧ (inner ℂ (f s) f').re ≤ B*‖f s‖^2 := by
    obtain ⟨y,hY,Y⟩:=conduct P F e x s
    refine ⟨_,Y,?_⟩; let u:=f s; let g i:=reopen P (1-s) (F i); change (inner ℂ u (_-_)).re≤ _
    rw [inner_sub_right,inner_sum,Complex.sub_re,Complex.re_sum]; have ha:|1-s|≤1:=by rw [abs_le]; constructor <;> linarith [v.1,v.2]; -- hmm indentation
    have h0 : 0 ≤ 1-s := sub_nonneg.mpr v.2
    have hz := t u (1-s) ha h0; have hw(i:Fin n):=suppress σ a p s (by rw [abs_of_nonneg v.1]; exact v.2) u (y i) (g i) (hp i (1-s) ha h0) (hY i)
    have he: ∑ i, (inner ℂ u (acts (g i) (y i))).re ≤ _ := sum_le_sum (fun i _=> hw i); rw [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at he
    change (∑ i,(grain u (g i)).re)≤C*‖u‖^2+(inner ℂ u (acts (excit P) u)).re at hz
    change (∑ i, (inner ℂ u (acts (g i) (y i))).re)-(inner ℂ u (acts (excit P) u)).re≤ B*‖u‖^2; unfold B; linarith only [he,hz]
  let g(s:ℝ):= ‖f s‖^2*Real.exp (-2*B*s); -- need DerivAt norm mix.
  have hv(s:ℝ) (v:s∈Icc (0:ℝ) 1) : ∃ w:ℝ, HasDerivAt g w s ∧ w≤0:=by
    obtain ⟨w,h,e⟩:= hd s v
    have hh: HasDerivAt (fun y:ℝ=> ‖f y‖^2) (2*(inner ℂ (f s) w).re) s:=by
      -- choose ℝ inner possibly not coerce
      have ht:=(Complex.reCLM.hasFDerivAt (x:=_)).comp_hasDerivAt s (h.inner ℂ h); convert ht using 1
      all_goals try rfl
      all_goals try (ext i; simp [inner_self_eq_norm_sq_to_K,←Complex.ofReal_pow])
      simp; rw [←inner_conj_symm w (f s)]; change _=_+(Complex.re (star (inner ℂ (f s) w))); rw [Complex.star_def,Complex.conj_re]; ring
    have he : HasDerivAt (fun s:ℝ=> Real.exp (-2*B*s)) ((-2*B)*Real.exp (-2*B*s)) s:=by
      have ht:= ((hasDerivAt_id' s).const_mul (-2*B)).exp; rw [mul_one] at ht; exact ht.congr_deriv (mul_comm ..)
    refine ⟨_, hh.mul he, ?_⟩
    nlinarith only [mul_le_mul_of_nonneg_right e (Real.exp_pos (-2*B*s)).le]
  have hG : AntitoneOn g (Icc 0 1):= by
    apply antitoneOn_of_deriv_nonpos (convex_Icc ..)
    · intro i p; exact (hv i p).choose_spec.1.continuousAt.continuousWithinAt
    · intro i p; exact (hv i (interior_subset p)).choose_spec.1.differentiableAt.differentiableWithinAt
    intro i p; rw [(hv i (interior_subset p)).choose_spec.1.deriv]; exact (hv i (interior_subset p)).choose_spec.2
  have he:= hG (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  unfold g at he; rw [mul_zero,Real.exp_zero,mul_one,mul_one,show -2*B= -(2*B) by ring,Real.exp_neg, show Real.exp (2*B)=(Real.exp B)^2 from (by simpa using Real.exp_nat_mul B 2),←div_eq_mul_inv,div_le_iff₀ (pow_pos (Real.exp_pos _) 2)] at he -- tune
  rw [show f 1=acts (stripTil F 1) x by simp [f,rolling,wholeTilt], show f 0=acts (wholeTilt P 1) x from (by unfold f rolling; rw [tilZero,mul_one,sub_zero])] at he
  apply le_of_pow_le_pow_left₀ (n:=2) (by decide) (by positivity)
  rw [mul_pow, mul_comm ((Real.exp B)^2)]; exact he
#print axioms engross
end YM.CF.WakeInvestment
