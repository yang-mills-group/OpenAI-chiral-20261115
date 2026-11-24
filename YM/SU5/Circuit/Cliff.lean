import YM.SU5.Circuit.Ruby
set_option autoImplicit false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06
open Work.F07 (Band)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
variable {n:Side}{M:Bed}{q:Clip}{η σ C v:ℝ}
variable (x:Floor M q n v C)(L:M.covered σ C)(u:0<σ)
include L u x
lemma cliff (i: Site n) : M.metric.read (rubyM i)=(q.direct:ℂ) • 1+(M.roots.read (rubyM i))ᴴ*M.roots.read (rubyM i):=by
 have ht:=expanse M.metric (Row.rights σ C L.2.1 u.le) n; have he:= expanse M.roots (Row.rights σ C L.2.2.2.1 u.le) n
 have hz:= Expanse.plusR (Expanse.weight (unit_exp (TypeFace 2) n) q.direct) (Expanse.chain (Expanse.flip he) he); rw [← full_cover, x.roots] at hz; exact congr_fun (Expanse.just ht hz) i
lemma under_foot (i: Site n) : (tab M.metric i).IsHermitian ∧ ∀ X, q.direct * sqLength X ≤ pairingRe (tab M.metric i) X X:=by
 rw [tab,cliff x L u i]; constructor
 · unfold Matrix.IsHermitian; simp [conjTranspose_add,conjTranspose_mul]
 intro X; rw [pairingRe_add,pairingRe_gram,pairingRe_scale,price_unit]; exact le_add_of_nonneg_right (sqLength_nonneg _)
omit L u x in
lemma band_bound_l {m:Type} [Fintype m][DecidableEq m](K:Matrix m m ℂ)(h:K.IsHermitian)(p:∀ a, η*sqLength a≤pairingRe K a a)(u:0<η) : η^Fintype.card m≤ ‖K.det‖:=by
 let A:= 1+∑ i,∑ j,‖K i j‖; let B:=countCeil m ^ 2*A; have he:0<A:=by unfold A; positivity; -- tune
 have hv:0<B:=by unfold B; have hh:=countCeil_pos m; positivity
 apply (band_bill h (fun i=> ⟨p i,?_⟩) u hv).1
 refine (le_abs_self (pairingRe K i i)).trans ((pairingRe_diag K he.le ?_ i))
 intro j k; exact (Finset.single_le_sum (f:=fun t=> ‖K j t‖) (fun i _=> norm_nonneg _) (mem_univ k)).trans ((Finset.single_le_sum (f:=fun i=>∑ l,‖K i l‖) (fun z _=> Finset.sum_nonneg fun j _=> norm_nonneg _) (mem_univ j)).trans (le_add_of_nonneg_left (by norm_num)))
-- gauge-fixed
abbrev wireC := Matrix (TypeFace 1) (TypeFace 1) ℂ
abbrev orbC:= Matrix (TypeFace 2) (TypeFace 2) ℂ
def cliffMap (M:Bed)(p:Momentum):wireC:= mirage 1 1 p * M.metric.read p * signal 1 1 p + signal 1 0 p*mirage 1 0 p
abbrev Cov (M: Bed)(p:Momentum):orbC:=signal 1 1 p*(cliffMap M p)⁻¹*mirage 1 1 p -- applied to stencil at point
omit L u x in
lemma trough (p:Momentum): mirage 1 1 p* signal 1 1 p+signal 1 0 p*mirage 1 0 p=(divisor 1 p) • (1:wireC):=by
 unfold mirage signal; rw [crossed 0]; simp only [sub_add_cancel]; congr 1; unfold divisor tripQ seedQ; apply sum_congr rfl; intro i _; simp [narrow_apply,mul_comm]
omit L u x in
lemma trackCloses (p:Momentum)(X:TypeFace 1→ℂ)(h:physical p):
 sqLength (signal 1 1 p*ᵥX)+sqLength (mirage 1 0 p *ᵥ X)=(divisor 1 p).re * sqLength X:=by
 let U:=signal 1 1 p; let V:=signal 1 0 p; rw [mirage_herm 1 p h]
 change sqLength (U*ᵥX)+sqLength (Vᴴ*ᵥX)=_
 rw [← pairingRe_gram,← pairingRe_gram,←pairingRe_add,conjTranspose_conjTranspose]
 have he:= trough p; rw [mirage_herm 1 p h, mirage_herm 1 p h] at he; rw [show Uᴴ*U+V*Vᴴ=_ from he]
 have hr: ((divisor 1 p).re:ℂ)=divisor 1 p:=(Silver.chipSq _ h).of_real
 nth_rw 1 [← hr]; rw [pairingRe_scale,price_unit]
def aimRock(q:Clip):= min q.direct 1*Next.Free.meter.low^2
omit L u x in
lemma aimed (q:Clip) : 0<aimRock q:= by unfold aimRock; have hk:= Next.Free.meter.low_pos; exact mul_pos (lt_min q.quadratic_pos one_pos) (by positivity)
lemma clip_beam (i:Site n)(hn: Even n.val) : (cliffMap M (rubyM i)).IsHermitian ∧ ∀ V,aimRock q*‖ruby i‖^2 *sqLength V≤pairingRe (cliffMap M (rubyM i)) V V:=by
 have ht:=ruby_pigment i; let p:= rubyM i; rw [cliffMap,mirage_herm 1 _ ht,mirage_herm 1 _ ht]; let Z:=signal 1 1 p; let A:= tab M.metric i; let Y:=signal 1 0 p; obtain ⟨he,hf⟩:=under_foot x L u i; change IsHermitian (Zᴴ*A*Z+Y*Yᴴ)∧∀ V, _≤ pairingRe (Zᴴ*A*Z+Y*Yᴴ) V V
 constructor
 · unfold IsHermitian; simp [conjTranspose_mul,conjTranspose_add,show Aᴴ=A from he, Matrix.mul_assoc]
 intro V; rw [pairingRe_add, paid_through]
 have hx:=trackCloses p V ht; rw [mirage_herm 1 p ht] at hx; let Cx:= sqLength V; let m:= min q.direct 1; have hm:0≤m:=(lt_min q.quadratic_pos one_pos).le; let Z':= sqLength (Z*ᵥV); let Y':=sqLength (Yᴴ*ᵥV)
 calc _≤ m*((divisor 1 p).re*Cx):=by
        have ht:Next.Free.meter.low^2*‖ruby i‖^2 ≤ (divisor 1 p).re:= (mul_le_mul_of_nonneg_left (abut (ruby i)) (sq_nonneg _)).trans (divisor_real_bounds 1 (ruby_spin i hn)).1
        unfold aimRock; change m* _*_*Cx ≤ _; rw [mul_assoc m, mul_assoc m]; gcongr; exact sqLength_nonneg V
      _=m*Z'+m*Y':=by rw [←mul_add]; exact congrArg (m*·) hx.symm
      _≤_:=by
        apply add_le_add ((mul_le_mul_of_nonneg_right (min_le_left ..) (sqLength_nonneg _)).trans (hf (Z*ᵥV)))
        rw [show Y*Yᴴ=(Yᴴ)ᴴ*Yᴴ from (congrArg (· * Yᴴ) (conjTranspose_conjTranspose _).symm),pairingRe_gram]
        exact mul_le_of_le_one_left (sqLength_nonneg _) (min_le_right ..)
lemma det_fort (i:Site n)(hn:Even n.val)(e:0<‖ruby i‖) : aimRock q ^4 * ‖ruby i‖^8 ≤ ‖(cliffMap M (rubyM i)).det‖:=by
 obtain ⟨he,hh⟩:= clip_beam x L u i hn; have ht:= band_bound_l _ he hh (mul_pos (aimed q) (by positivity)); rw [show Fintype.card (TypeFace 1)=4 from (Fintype.card_congr axisEquiv).symm] at ht -- tune
 apply le_trans (le_of_eq ?_) ht; ring
lemma dizzy (i:Site n)(hn:Even n.val) : (signal 1 1 (rubyM i)) * (cliffMap M (rubyM i))⁻¹ *mirage 1 1 (rubyM i) * (tab M.metric i) *signal 1 1 (rubyM i) = signal 1 1 (rubyM i) := by
 let p:=rubyM i; let A:=tab M.metric i; let S:=signal 1 1 p; let T:=signal 1 0 p; let J:=mirage 1 1 p; let K:=mirage 1 0 p; let B:=cliffMap M p; change S*B⁻¹*J*A*S=S
 by_cases e:ruby i=0
 · have h:p=0:=by unfold p rubyM; rw [e]; rfl
   have ht:S=0:=by unfold S; rw [h]; simp [signal,chip,tripQ,wedge]; -- tune
   rw [ht]; simp
 have hc: IsUnit B.det:=isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((by apply lt_of_lt_of_le (mul_pos _ _) (det_fort x L u i hn (norm_pos_iff.mpr e)); all_goals first | exact pow_pos (aimed _) _ | exact pow_pos (norm_pos_iff.mpr e) _):0<‖B.det‖))
 have he:S*T=0:=signal_chain ..; have hg: K*J=0:=mirage_chain ..
 have h:Commute B (T*K):=by
   change (J*A*S+T*K)*(T*K)=(T*K)*(J*A*S+T*K)
   rw [Matrix.add_mul,Matrix.mul_add]; congr 1; simp_rw [Matrix.mul_assoc]; rw [← Matrix.mul_assoc S, he,←Matrix.mul_assoc K, hg]; simp
 have hk:B⁻¹* (T*K)=(T*K)*B⁻¹:=by
   rw [←mul_one (B⁻¹ * (T*K)), ←Matrix.mul_nonsing_inv _ hc, ←mul_assoc _ B, mul_assoc B⁻¹ _ B,h.eq.symm] -- tune direction
   simp_rw [←mul_assoc B⁻¹ B]; rw [Matrix.nonsing_inv_mul _ hc]; simp
 rw [show S*B⁻¹*J*A*S= S*B⁻¹*(B-T*K) from (by rw [show B=J*A*S+T*K from rfl,add_sub_cancel_right]; simp only [←Matrix.mul_assoc]), Matrix.mul_sub, Matrix.mul_assoc S _ B, Matrix.nonsing_inv_mul _ hc,Matrix.mul_one, Matrix.mul_assoc, hk,← Matrix.mul_assoc S,← Matrix.mul_assoc S,he]; simp
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.det_fort
#print axioms YM.Regis.Circuit.dizzy
