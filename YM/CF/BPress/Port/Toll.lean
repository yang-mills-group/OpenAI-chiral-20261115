import YM.CF.BPress.Port.Star
import YM.CF.BPress.Wealth.ErrorBudget
/-! Gaussian cancellation pointwise including discrepancy and S vacancy at true fields, exact prefactor. No Wick or biases here. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Port
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Cube Bands Pressure Wealth Finset Weave Branch
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ENNReal
open SU Gauge Next.SectorChange
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B)(D:ℕ)(J:ChartRatio group)(κ y:ℝ)(A:BEnd X)(F:Fare X)(S:Seal X.Hcols)
def Rcoord (v:Fills X) := let x:=(offer X).symm v; inner ℝ x (errorT X A (F S) x)/2
-- sums
abbrev job_m (D:ℕ)(J:ChartRatio group)(y:ℝ):= N_v D y*gH D J y
def diceV:= (job_m B.D J y)^(Fintype.card X.Hcols)*detM X (F ∅)
def softLog (x:Fills X):=∑ i∈ Sᶜ, logPay B.D J y (wjson (F S) x i)
lemma tax_carve (x : Fills X) : taxG X J y F S x= (job_m B.D J y)^(Sᶜ.card) * Real.exp (softLog X J y F S x + ∑ i∈ Sᶜ, hardHit X i x):=by
 unfold taxG tax_column; rw [prod_mul_distrib,prod_const,softLog,← sum_add_distrib, Real.exp_sum]
lemma det_diff (F:Fare X)(i : Seal X.Hcols)(p: ∀ S,0<detM X (F S)): detM X (F i) = detM X (F ∅)* Real.exp (jacdiff X F i):=by unfold jacdiff detL; rw [Real.exp_sub, Real.exp_log (p _),Real.exp_log (p _)]; field_simp [(p ∅).ne']
variable {X F A J y κ}{T:Sheet.Atlas}{P:Weave.Budget}(q:Afford J T P B.D κ y)(r:LocalRatio J)(e:Summer X F P.upper (P.low y) (P.reach y) (P.chunks y))(f:Whole X S (F S) 1)
-- generic algebra no need H A: A symmetric whole on S in hessian
lemma Rcreed (v:RaySpace X)(g:Whole X S A 1)(f : Whole X S (F S) 1):
 let x:= offer X v
 let P:= keepOnly X Sᶜ (F S v)
 (∑ i∈ Sᶜ, hardHit X i x) - inner ℝ P (A P)/2=Rcoord X A F S x:=by
 intro x P; have he : inner ℝ v (errorT X A (F S) v)= ‖v‖^2 - inner ℝ (F S v) (A (F S v)):=by
   change inner ℝ v (v- F S (A (F S v)))=_; rw [inner_sub_right,real_inner_self_eq_norm_sq]; apply congrArg (fun w:ℝ=>‖v‖^2-w); exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp f.self) v _).symm
 let w:= F S v; let z:= keepOnly X S w; have hk:v=v:=rfl; have hh : inner ℝ w (A w)= ‖z‖^2+inner ℝ P (A P):= by
   have he:g.self = g.self:=rfl; conv_lhs=> rw [mask_add X S w, map_add, inner_add_left, inner_add_right,inner_add_right,show A _=_ from g.agrees w,one_smul,real_inner_self_eq_norm_sq]
   unfold z w P; rw [g.complement]; rw [mask_disjoint, real_inner_comm (x:=keepOnly X S _) (y:=keepOnly X Sᶜ _), mask_disjoint]; ring -- tune polarity rw ambiguity
 have hp : ‖v‖^2= ‖z‖^2 + ∑ i∈ Sᶜ, ‖x i‖^2:=by rw [splitSoft X S v, show keepOnly X S v=z from (by unfold z w; rw [f.reads,one_smul]),← sect_norm X Sᶜ v] -- tune x
 unfold Rcoord hardHit; change ∑ i∈Sᶜ, _ - _ = _; dsimp only [x]; rw [MeasurableEquiv.symm_apply_apply,he, show inner ℝ (F S v) _= _ from hh, hp]; rw [← Finset.sum_div]; unfold x; ring
variable {M:ℕ}{d:Clip}{σ Λ C:ℝ}{β:ℝ}{R:PathData group}(H:R.Bounds d σ C Λ) (p: High B M)
include q r e
lemma log_mapL (v:RaySpace X)(W:Offers X)(u: aware X κ y F S (offer X v,W))(Z:Barrel X y (offer X v)):
  softAl X κ y (Aback X (bodyBase X y F S (offer X v,W))) T= g y • lead X (keepOnly X Sᶜ (F S v)):=by
 let Q:= (F S v); let U:= bodyBase X y F S (offer X v,W); let K:= issueT X y S (offer X Q) W; have he: U= K:=by unfold U K bodyBase Q; dsimp only; rw [wjson_r]
 have hp:= q.outward r S e v Z; let G:= Aback X K; have hx:S=pick X κ y K:=by rw [← he]; exact u.symm -- tune semicolon
 unfold Aback; change softAl X κ y ((heart X).symm U) T=_; rw [he]; funext i; change _ = g y • (lead X _) i; rw [stay]; split; next e=> have ht:= mem_compl.mp e; rw [q.log_sect r S Q W hx ?_ i ht]; exact q.thread r Q i; simp_rw [wjson_r] at hp; exact fun i _=>hp i
 next e=> have hv:i.1∈ S:= not_not.mp fun v=> e (mem_compl.mpr v); rw [softAl,Wealth.low,if_pos (_:i.1∈ chosen X κ y ((heart X).symm K)),smul_zero]; exact (show S=chosen X κ y ((heart X).symm K) from hx) ▸ hv
include H p f
lemma Rpoint (v:RaySpace X) (W:Offers X)(u: aware X κ y F S (offer X v,W))(Z:Barrel X y (offer X v)): let w:=perturb T X κ y (Aback X (bodyBase X y F S (offer X v,W))); (∑ i∈ Sᶜ, hardHit X i (offer X v)) - ∑ i∈ Θ X M S, second R d M β i w = Rcoord X (wave X M R d β y H S) F S (offer X v):=by
 intro w; let A:= wave X M R d β y H S; let P:= keepOnly X Sᶜ (F S v); have hk : w=picture X y (lead X P) :=by unfold w perturb; rw [log_mapL S q r e v W u Z]; rfl
 rw [hk]; have hh : Whole X S A 1:=⟨section_sym ..,fun v=>by unfold Flare; rw [one_smul]; exact hess_sev X M R d β y H S v p⟩; have he:= Rcreed S v hh f; dsimp only at he; change _ - inner ℝ P (A P)/2= _ at he; rw [← he]; congr 1; rw [show inner ℝ P (A P) / 2 = _ from epoch_area X M R d β y H S P]; unfold P; rw [disjoint_mask]; simp -- tune

lemma stamp_point (v:RaySpace X)(W:Offers X)(u: aware X κ y F S (offer X v,W))(Z:Barrel X y (offer X v)):
 let A:=wave X M R d β y H S; let k:= (offer X v,W); let P:=perturb T X κ y (Aback X (bodyBase X y F S k))
 detM X (F S)*taxG X J y F S k.1* Real.exp (-(∑ i∈ Θ X M S, second R d M β i P)) = diceV X J y F * (job_m B.D J y)⁻¹^S.card * Real.exp (jacdiff X F S + softLog X J y F S k.1+ Rcoord X A F S k.1):=by
 intro A k P; rw [det_diff X F S (fun S=>e.root_pos S),tax_carve]; let c:= job_m B.D J y; have hc:0<c:= mul_pos (v_pos ..) (gH_pos B.D J y r q.young); rw [diceV]; let n:=Fintype.card X.Hcols; have ht:n=Sᶜ.card+ S.card:= (card_compl_add_card S).symm; let D:= detM X (F ∅); let l:= jacdiff X F S; let Y:=softLog X J y F S k.1; let p':= Rcoord X A F S k.1; have hf : Y+(∑ i∈ Sᶜ, hardHit X i k.1) + -(∑ i∈ Θ X M S, second R d M β i P)= Y+p':=by rw [add_assoc,← sub_eq_add_neg,Rpoint S q r e f H p v W u Z]; -- tune shadow y
 have he : c^Sᶜ.card=c^n * c⁻¹^S.card:=by rw [ht,pow_add,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_pos hc _|>.ne'),mul_one]; -- tune
 let Z':= ∑ i∈Sᶜ, hardHit X i k.1
 let G:= -(∑ i∈Θ X M S, second R d M β i P)
 change D*Real.exp l*(c^Sᶜ.card*Real.exp (Y+Z')) * Real.exp G = c^n*D * c⁻¹^S.card * Real.exp (l+Y+p'); rw [add_assoc l,← show Y+Z'+G=Y+p' from hf,Real.exp_add l (Y+Z'+G),Real.exp_add (Y+Z') G,he]; ring
end YM.CF.BPress.Port
