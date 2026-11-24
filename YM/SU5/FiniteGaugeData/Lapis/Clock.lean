import YM.SU5.FiniteGaugeData.Lapis.Whirl
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Precision Tree Pressure Laurent Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Gaussian
open Drachma Affiche Galope Avenue Galope.Press Wrist Poeme Haute Punch Affiche Lantern Lantern.Cup RouteM Rally Syl
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Dig
variable {n: Side}{G: Gauge}{Z: Finset (Site n)} {M w k:ℕ} {C κ K α L β a Δ μ g:ℝ} {p:BudgetPoint}{P:Bed}{u:Stage}{R:PathData G} {S:Arms G u} {A:Finset (Cell n)} {F:Portion n G→ℝ}{J':ChartRatio G}{ε:ℝ}
local notation "α'" => heightK p M
local notation "η" => bonusK p u β
local notation "I" => buy Z k
local notation "J" => Plush G (buy Z k)
variable (T: Attains S J' n p β α μ M k w)(hz:Z⊆ glow A M) (D:Floor P u.clip n a C)(w0:0<a)(W:R.Bounds u.clip u.width u.paths Δ)(B:Attached P R)(O:Ocean G (buy Z k))
local notation "r'"=> gross w u β α
local notation "ZK"=> zodiac P G (buy Z k)
local notation "H"=> heatC (billsC k w Z) W B
local notation "M'"=> primeShare w u
open Cold Recruit
local notation "tk" => tileC n
local notation "γ" => (Fintype.card G.ColorIndex:ℝ)
local notation "u₀" => coreN w
local notation "ZoneK" => glow A (lic w)
abbrev τPeak (d C:ℝ)(w:ℕ):=C*d/(w:ℝ)^2
abbrev hunger (G:Gauge)(p L:ℝ):=L^2*(Fintype.card G.ColorIndex:ℝ)/p
lemma friar (Q a C L p:ℝ)(hp:0<p)(he:0≤a)(hd:0≤C) (q:0≤Q):
 2*L*Real.sqrt Q*Real.sqrt (a*C) ≤ p*Q + (L^2*C/p)*a:=by
 refine le_of_mul_le_mul_right ?_ hp; have hb: Real.sqrt (a*C)^2=a*C := Real.sq_sqrt (mul_nonneg he hd); let t:=Real.sqrt Q; have ht:t^2=Q:= Real.sq_sqrt q; let r:=Real.sqrt (a*C); have hl: (L^2*C/p)*p=L^2*C:=div_mul_cancel₀ _ hp.ne'; -- tune
 field_simp; nlinarith only [sq_nonneg (p*t-L*r),show r^2= a*C from hb, ht, congr_arg (fun z=>L^2*z) hb, congr_arg (fun z=>p^2*z) ht]
lemma asceticA (Q K v:ℝ)(h:K≤4*Q)(hp:0≤Q)(u:0≤v): Real.sqrt (K*v) ≤ 2*Real.sqrt v* Real.sqrt Q:=by
 refine le_trans (Real.sqrt_monotone (mul_le_mul_of_nonneg_right h u)) ?_
 have ht:0≤Real.sqrt v:=Real.sqrt_nonneg _; apply le_of_eq; rw [show 4*Q*v=4*v*Q from by ring, Real.sqrt_mul (by positivity),Real.sqrt_mul (by norm_num)]; norm_num
lemma catholic (hu:0≤L)(u:Intro n w)(q:0<ε)(c:ℝ): Fee G n L (disc ZoneK u₀) (parcelM ZoneK u₀) c ≤ ((4*Real.sqrt (Fintype.card G.ColorIndex:ℝ)* (L*‖1-c‖)+ε+τPeak diamC (hunger G ε L) w)*(tileC n:ℝ)+(hunger G ε L) * A.card*tB u₀):=by
 let Z:=glow A (lic w); let k:=coreN w; let x:ℝ:=disc Z k; let b:ℝ:= tileC n; let K:ℝ:= parcelM Z k; let d:ℝ:=Fintype.card G.ColorIndex; let Hw:ℝ:=w; have hH:0 < Hw:=by unfold Hw; exact_mod_cast (lt_of_lt_of_le (by decide:(0:ℕ)<2) u.1)
 have hb:0≤ b:=Nat.cast_nonneg _; have hz:0 ≤ x:=Nat.cast_nonneg _; have hd:0 ≤ d:=Nat.cast_nonneg _; let D:ℝ:=hunger G ε L; have hD:0≤ D:=by unfold D hunger; positivity
 let Y:=Real.sqrt b; have hp:Y^2=b:= Real.sq_sqrt hb; have hy:=Real.sqrt_nonneg b
 have hk: K≤4*b:=unit_cap _ (glow_in ..) (show coreN w ≤ lic w by unfold lic; omega) -- visible
 have hh: Real.sqrt (K*d) ≤2*Real.sqrt d *Y:= asceticA _ _ _ hk hb hd
 let a:=‖1-c‖; have ha:a≥0:=norm_nonneg _
 have hc:2*L*units n * (a * Real.sqrt (K*d)) ≤ 4*Real.sqrt d*(L*a)*b:=by calc
    _ ≤ 2*L*Y*(a*(2*Real.sqrt d*Y)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh ha) (mul_nonneg (by positivity) (unitZ _))
    _ = _:=by linear_combination 4*Real.sqrt d* L * a *hp
 have he:= friar b x d L ε q hz hd hb; let z:ℝ:= A.card; let e:ℝ:=tB k
 have hσ:x ≤ diamC*b/Hw^2+z*e:=by
    have hw:= qualify u A; let L:= Hw^2; have hL:0<L:= pow_pos hH _; refine le_of_mul_le_mul_right ?_ hL; -- Lean lemma notation .mp? actually relation iff .mpr? check
    linarith only [show (x+1)*L≤diamC*b+z*e*L from hw, congr_arg (fun t:ℝ=>x*t) (rfl : L=Hw^2),hL,show (diamC*b/Hw^2)*L=diamC*b from div_mul_cancel₀ _ hL.ne'] -- tune
 change 2*L*Y*(Real.sqrt (x*d)+a*Real.sqrt (K*d))≤ (4*Real.sqrt d*(L*a)+ε+ D*diamC/Hw^2)*b + D*z*e
 have hx0: D*(diamC*b/Hw^2)=D*diamC/Hw^2*b:= by ring -- tune
 rw [mul_add]; linarith only [hc, (show 2*L*Y*Real.sqrt (x*d)≤ε*b+D*x from he), hx0,mul_le_mul_of_nonneg_left hσ hD]
include T
lemma tachy (z:α≤1/2)(a:primeShare w u ≤ α) : |Real.sqrt β/Real.sqrt r'|≤2 ∧ ‖1-Real.sqrt β/Real.sqrt r'‖≤2*α:=by
 let r:=r'; let t:=Real.sqrt β/Real.sqrt r; have hr:0<r:= T.spry; have hx:0<Real.sqrt r:=Real.sqrt_pos.mpr hr; have hβ:=T.warm; have ht:0<t:=div_pos (Real.sqrt_pos.mpr hβ) hx; let g:=1-α; have hg:0< g:=sub_pos.mpr T.legal; let u':=primeShare w u; have he:r≤β:=by
    have h0:0≤u':=shim ..; have hm:0<α:=T.witness; have hv:= mul_le_mul_of_nonneg_right (show 1-u' ≤1 from sub_le_self _ h0) (mul_nonneg hg.le hβ.le); change (1-u')*(g*β) ≤ β; unfold g at hv ⊢; nlinarith only [mul_pos hm hβ,hv]
 have hu:t≥1:=by apply (le_div_iff₀ hx).2; rw [one_mul]; exact Real.sqrt_monotone he
 have hb:g^2*β≤r:=unite hβ T.legal a
 have h1:t*g ≤1:=by rw [show t*g=Real.sqrt β*g/Real.sqrt r from by unfold t; ring]; apply (div_le_one hx).2; apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hg.le) hx.le).1; rw [mul_pow,Real.sq_sqrt hβ.le,Real.sq_sqrt hr.le,_root_.mul_comm β]; exact hb
 have h2: 1/2≤g:=by unfold g; linarith only [z]
 have h3:t≤2:=by nlinarith only [mul_le_mul_of_nonneg_left h2 ht.le,h1]
 refine ⟨(abs_of_pos ht).le.trans h3,?_⟩; change ‖1-t‖≤_; rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hu)]; unfold g at h1; nlinarith only [h1,mul_le_mul_of_nonneg_right h3 T.witness.le]
open Drachma.Tame Drachma.Tokens
omit T
lemma chukker (h:LocalRatio J')(p:0≤L)(u:0<ε): ∃ (μ α:ℝ), 1<μ ∧ 0<α ∧ α≤1/2 ∧ Real.log μ-dozer G*Real.log (1-α) ≤ ε ∧ 4*Real.sqrt γ * (L*(2*α))≤ε:=by
 let b':=4*Real.sqrt (Fintype.card G.ColorIndex:ℝ)*L*2; have hu:0≤b':=by unfold b'; positivity; -- avoid h irrelevant later use implicit G issue
 obtain ⟨μ,hμ,α,t,z,v⟩:=resonant ε u G; let q:= ε/(b'+1); let B:= min (min q α) (1/2:ℝ); have hb: B≤1/2:= min_le_right ..; have hx:B≤ α:= (min_le_left ..).trans (min_le_right ..); have hz:0<q:=div_pos u (by linarith); have hQ:B≤q:=(min_le_left ..).trans (min_le_left ..)
 refine ⟨μ,B,hμ,lt_min (lt_min hz t) (by norm_num),hb,?_,?_⟩
 · have he:Real.log (1-α) ≤ Real.log (1-B):=Real.log_le_log (sub_pos.mpr z) (sub_le_sub_left hx _); linarith only [u,mul_le_mul_of_nonneg_left he (show 0≤dozer G from Nat.cast_nonneg _),v]
 norm_num1 -- tune
 have hY: q*(b'+1)=ε:=div_mul_cancel₀ _ (by linarith); have he:b'*B≤ b'*q:= mul_le_mul_of_nonneg_left hQ hu; unfold b' at he hY; nlinarith only [he,hY,hz]
end Dig
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Dig.tachy
#print axioms YM.SU5.FiniteGaugeData.Lapis.Dig.chukker
