import YM.SU5.FiniteGaugeData.Galope.Carmine
import YM.SU5.FiniteGaugeData.Galope.Goblin
import YM.SU5.FiniteGaugeData.Drachma.Deli
/-! # Leading volume upper budget: gauge price. carry charges. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle Avenue Press Poeme Haute Lantern Lantern.Cup Wrist Rally Next.SectorChange RouteM
open Pressure Precision Exterior Laurent Bloch CF.Font
open Drachma Drachma.Tame Drachma.Tokens
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge} {s:Stage}{R:PathData G}{P:Bed}{M k w v:ℕ}{A:Finset (Cell n)}{Z:Finset (Site n)}{o:Site n}{p:BudgetPoint}{C r x Λ α τ μ a h ε b β:ℝ}{J:ChartRatio G}
namespace Recruit
variable {T:Arms G s}
open PathData
def tempLost(J:ChartRatio G)(β K:ℝ):= |coinV J β|+dozer G/2*Real.log (sheetB K)
lemma sheet_log(K:ℝ):0≤Real.log (sheetB K):= Real.log_nonneg (by unfold sheetB; refine le_trans (by norm_num: (1:ℝ)≤4) (le_add_of_nonneg_right (by positivity)))
lemma tempLost_pos(J:ChartRatio G)(β K:ℝ): 0≤tempLost J β K:= by unfold tempLost; exact add_nonneg (abs_nonneg _) (mul_nonneg (by unfold dozer; positivity) (sheet_log _))
lemma unit_cap(Z: Finset (Site n))(p:Z⊆ zones n M)(h:k≤M): (parcelM Z k:ℝ) ≤ 4*ser n:=by
 let b:ℝ:=tileC n; have he: (parcelM Z k:ℝ) ≤ 3*ser n+1:=by unfold ser; exact_mod_cast registered p h
 have hp:1≤ ser n:=by unfold ser; exact_mod_cast (show 1≤ Fintype.card (Site n) from Fintype.card_pos)
 linarith
lemma for_ledger (A:Finset (Cell n))(Y:Attains T J n p β α μ M k w)(pZ:Z⊆ glow A M)(z:Floor P s.clip n a C)(u:0<a)(hr: (1-α)^2 *β ≤ gross w s β α) : let f:=feeZ T J p β α Λ μ P A Z k w M; 0< f ∧ Real.log f≤ angular n J P β + greatF T n w M p β α Λ - A.card * bonusK p s β + ((disc Z k:ℝ)+1)*tempLost J β C+ (parcelM Z k:ℝ)*(Real.log μ-dozer G *Real.log (1-α)):=by
 intro f; let u':= Y.lucent.chart; have hh:= u'.scale; have hm:0<μ:=Y.homeF; let B:=buy Z k; let S:=chrome G P Z k; have he:= live_sigma (Z:=Z) (k:=k) G z u
 let ρ:=gross w s β α; have h1:0<ρ:=Y.spry; let c:= holdK S ρ; have hz:0<c:= lensP he h1; have hβ:0<β:=Y.warm; have hw:0<1-α:=sub_pos.mpr Y.legal; let q:ℝ:=dozer G; have hp:0≤q:=Nat.cast_nonneg _; let dm:ℕ:=Fintype.card G.ColorIndex
 let N:ℕ:=parcelM Z k; have ht:0≤(N:ℝ):=Nat.cast_nonneg _; let V:=coinV J β

 let d:=disc Z k; have h':k≤M:=by have h:=Y.tall; refine le_trans ?_ h; unfold debit roomCard; omega
 have hΔ:(N:ℝ)+d=3*ser n+1:=by unfold ser; exact_mod_cast Eq.trans (Nat.add_comm N d) (disc_book (pZ.trans (glow_in ..)) h')
 have hL:0<chassis P n:=chassis_p z u; have hu: q*Real.log (chassis P n) ≤ Real.log S.det+ (d:ℝ)*q*Real.log (sheetB C):=by
    have hu:=upDet h' (pZ.trans (glow_in ..)) z u G; change (chassis P n)^dm ≤ S.det * ((sheetB C)^d)^dm at hu; have he:= Real.log_le_log (pow_pos hL dm) hu; rw [Real.log_mul ((live_sigma G z u).det_pos.ne') (by have h:=sheet_ok C; positivity)] at he; simp_rw [Real.log_pow] at he; linarith only [he] -- tune
 have he':V=Real.log J.scale+q*(Real.log (Real.sqrt (2*Real.pi))-Real.log β/2):=by rw [Real.log_sqrt (by positivity)]; exact pocketU u' hβ
 let U:=greatF T n w M p β α Λ - A.card*bonusK p s β; have hg:f=(J.scale*μ)^N *Real.exp U *c:=rfl
 rw [hg]; refine ⟨by positivity,?_⟩
 rw [Real.log_mul (by positivity) hz.ne',Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow,Real.log_mul hh.ne' hm.ne',show Real.log c= _ from crest_bill S he h1,Fintype.card_prod,Fintype.card_coe]; unfold angular; push_cast; have hv:(N:ℝ)*V≤ 3*ser n*V+((d:ℝ)+1)*|V|:=by
    have hq : N * V=3*ser n*V+(1-d)*V:=by linarith only [show ((N:ℝ)+d)*V=(3*ser n+1)*V from congr_arg (·*V) hΔ]
    rw [hq]; refine add_le_add (le_refl _) ?_; have h0:0 ≤ (d:ℝ):=Nat.cast_nonneg _; rw [sub_mul,one_mul]; linarith only [le_abs_self V, mul_le_mul_of_nonneg_left (neg_le_abs V) h0]
 have hs:0 ≤ q*Real.log (sheetB C):=mul_nonneg hp (sheet_log _)
 have hl:=Real.log_le_log (show 0<(1-α)^2*β by positivity) hr; rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl; push_cast at hl; -- want V
 change _ ≤ 3*ser n*V-q/2*Real.log (chassis P n)+ _- _ +((d:ℝ)+1)*tempLost J β C + N*_ -- tune parentheses
 unfold tempLost; dsimp only [U]; linarith only [hu,hs,hv,mul_le_mul_of_nonneg_left hl (mul_nonneg ht hp),congr_arg (fun x=> (N:ℝ)*x) he']
open Metric
lemma shim(w:ℕ)(s:Stage): 0≤primeShare w s:=by unfold primeShare; apply div_nonneg (by positivity) s.clip.quadratic_pos.le
lemma unite {p:ℝ}(u:0<β)(h:p<1)(e:primeShare w s ≤ p): (1-p)^2*β ≤ gross w s β p:= by
 have hκ : 0<1-p:=sub_pos.mpr h; let y:= (1-p)*β; calc
    _ =(1-p)*y:=by unfold y; ring
    _ ≤ (1-primeShare w s)*y := mul_le_mul_of_nonneg_right (sub_le_sub_left e _) (mul_nonneg hκ.le u.le)
lemma resonant (ε:ℝ)(hp:0<ε)(G:Gauge): ∃ μ>1, ∃ α:ℝ, 0<α ∧ α<1 ∧ 4*(Real.log μ-dozer G*Real.log (1-α)) ≤ ε:=by
 let q:=dozer G; have he:0≤q:=Nat.cast_nonneg _; let k:=ε/(4*(1+q)); have hk:0<k:=div_pos hp (by linarith)
 have h:0<1-Real.exp (-k):=by have hx:=Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hk); linarith
 refine ⟨Real.exp k,Real.one_lt_exp_iff.mpr hk,1-Real.exp (-k), h,sub_lt_self _ (Real.exp_pos _),?_⟩; rw [sub_sub_cancel,Real.log_exp,Real.log_exp]
 apply le_of_eq; unfold k q; field_simp; ring
lemma fee_cost (A:Finset (Cell n))(Y:Attains T J n p β α μ (lic w) (coreN w) w)(z:Floor P s.clip n a C)(u:0<a)(hr:primeShare w s≤ α)(he:0<ε)(hh:0≤h)(hm:Real.log μ-dozer G*Real.log (1-α) ≤ ε)(ho:tempLost J β C ≤ h*w)(hw: Intro n w):
 feeZ T J p β α Λ μ P A (glow A (lic w)) (coreN w) w (lic w) ≤
 Real.exp (angular n J P β +greatF T n w (lic w) p β α Λ + (4*ε+diamC*h/w)*ser n + A.card*(h*w*tB (coreN w) - bonusK p s β)):=by
 let Z:= glow A (lic w); let k:=coreN w; let N:=parcelM Z k; let X:=T; let d:=disc Z k
 obtain ⟨pZ,HZ⟩:=for_ledger (Λ:=Λ) A Y (le_refl Z) z u (unite Y.warm Y.legal hr); let L:= ser n; let w':ℝ:=w; have hy:0<w':=by unfold w'; exact_mod_cast (lt_of_lt_of_le (by decide: (0:ℕ)<2) hw.1)
 apply (Real.log_le_iff_le_exp pZ).1
 let m:ℝ:= μ
 have hE:= qualify hw A; have hk: (d:ℝ)*0≤ 4:=by simp
 have hB: ((disc Z k:ℝ)+1)*tempLost J β C ≤ diamC*h/w*L + A.card*( h*w*(tB k:ℝ)):=by
    apply (mul_le_mul_of_nonneg_left ho (by positivity : 0 ≤ (disc Z k:ℝ)+1)).trans; rw [div_mul_eq_mul_div]
    -- multiply both sides*w and cancel
    apply le_of_mul_le_mul_right _ hy
    have hg: ((diamC*h*L)/w)*w'=diamC*h*L:= div_mul_cancel₀ _ hy.ne'
    rw [_root_.add_mul (diamC*h*L/(w:ℝ)),hg]; linarith only [mul_le_mul_of_nonneg_left hE hh]
 have hg:(parcelM Z k:ℝ)*(Real.log μ-dozer G*Real.log (1-α)) ≤ 4*ε*L:= (_root_.mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)).trans ((mul_le_mul_of_nonneg_right (unit_cap Z (glow_in ..) (by unfold lic; omega)) he.le).trans_eq (by ring)) -- tune
 linarith only [HZ,hB,hg]
end Recruit
end YM.SU5.FiniteGaugeData.Galope
