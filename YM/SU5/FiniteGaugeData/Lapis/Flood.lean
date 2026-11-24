import YM.SU5.FiniteGaugeData.Lapis.Polar
import YM.SU5.FiniteGaugeData.Lapis.Clock
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
open Drachma.Tame Drachma.Tokens
local notation "ρ₀" => Real.sqrt β/Real.sqrt r'
local notation "c'" => greatF S n w M p β α Δ
local notation "Vt" => ser n
local notation "Ψ" => High W B D F κ w0
abbrev service(L:ℝ):=8*L^2+Motion.bill (4*L)
-- prices templates already in Growth α.F.
private lemma mend (r a:ℝ)(p:0≤r)(u:Stage):∀ᶠ x in atTop, r*↑(radiusB x)*(tB (coreN (radiusB x)):ℝ) ≤ frostM u x/16:=by
 filter_upwards [posterior u (4*r) (by positivity)] with x hx; linarith only [hx]
lemma official (S:Arms G u)(b:LocalRatio J')(p':0 ≤ L)(g:0≤Δ)(e:0<ε)(C:ℝ): ∀ᶠ x in atTop, ∀ β:ℝ,x/2≤β→β ≤ 2*x→ ∀ p:BudgetPoint,p.threshold=temp x→ ∀ n:Side, Intro n (radiusB x)→∀ R:PathData G,∀ W:R.Bounds u.clip u.width u.paths Δ,∀ (P:Bed) (a:ℝ)(D:Floor P u.clip n a C)(w0:0<a)(B:Attached P R)(κ:ℝ),|κ|≤2 →∀ (A:Finset (Cell n))(δ:ℝ)(Q U:Config G n→ℝ)(F:Portion n G→ℝ), Boat Q W B p F A (glow A (lic (radiusB x))) (lic (radiusB x)) (coreN (radiusB x)) (radiusB x) κ β δ→ Opal L F→ Envelope U →(∀ v,U v≠0 → (∀ i: Cell n,i∈ A ↔ p.threshold < G.chord (faceValue v i)) ∧ U v ≤ Real.exp (Q v- R.principal u.clip p β v)) → (∫ t,U t∂prior G n) ≤ Real.exp (angular n J' P β+ High W B D F κ w0+ (δ+ε+service L)*ser n - A.card*(bonusK p u β)*(3/4)):=by
 let d:= ε/12; have hd:0<d:=div_pos e (by norm_num); obtain ⟨μ,h₀,pμ,h,t,ha,hV⟩:= chukker b p' hd; let α:= h₀; let L':=hunger G d L; have hh:0≤L':=by unfold L' hunger; positivity
 obtain ⟨H',hH,h'⟩:= committed b C; let D':= τPeak diamC L'; let f(x:ℝ):=radiusB x; have hf:Tendsto (fun x=> (radiusB x:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
 have hb': Tendsto (fun x=> diamC*H'/(radiusB x:ℝ)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop hf; have hb:Tendsto (fun x:ℝ=>D' (radiusB x)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (n:=2) (by norm_num)).comp hf) -- tune
 have hp:h₀<1:=by linarith only [t]
 filter_upwards [hb.eventually (ge_mem_nhds hd),hb'.eventually (ge_mem_nhds hd),attainer S b pμ h hp,mend H' 0 hH u,mend L' 0 hh u,h',eventually_gt_atTop (0:ℝ),great_pos S g h hd] with x hu hw ht h1 h2 eρ hx hg β hβ htβ p pp n Qv R W P a D hi B κ hκ A δ Q U F h0 pF pU Fv
 let w:=radiusB x; let M:=lic w; let k:=coreN w; obtain ⟨Y,T⟩:=ht β hβ p pp n Qv; let Z:= glow A M; let K:=buy Z k; let Ψ₀:= High W B D F κ hi; let τ:=angular n J' P β; let b:= allowance p u A β δ; let γ:= bonusK p u β; let v:=greatF S n w M p β α Δ; let r:= Real.sqrt β / Real.sqrt (gross w u β α)
 let Jv:= H'*(w:ℝ)* tB k; let U':ℝ:=tileC n; have hw': (1:ℝ)≤ w:=by unfold w; exact_mod_cast (Qv.1.trans' (by norm_num))
 have hΓ:frostM u x≤ γ:= bonus_fit u x hx p pp hβ; have sqC:Jv≤ γ/16:=h1.trans (div_le_div_of_nonneg_right hΓ (by norm_num)); have hL: L'*tB k ≤ γ/16:=calc
    _ ≤ L'*w*(tB k:ℝ):=mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hh hw') (by positivity)
    _ ≤ _:= h2.trans (div_le_div_of_nonneg_right hΓ (by norm_num))
 have he:0≤U':=Nat.cast_nonneg _
 have hu':= fee_cost (Λ:=Δ) A Y D hi T hd hH ha (eρ β hβ htβ) Qv; obtain ⟨pq,hx⟩:=tachy (n:=n) Y t T
 have hR:4*Real.sqrt (Fintype.card G.ColorIndex:ℝ)*(L*‖1-r‖)≤d:= (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx p') (by positivity : 0 ≤ 4*Real.sqrt (Fintype.card G.ColorIndex:ℝ))).trans hV
 have hy':=catholic (A:=A) (G:=G) p' Qv hd r
 apply silo («I»:=K) U _ pU; intro O; let f':= weather G L Z k r
 apply (tireless Y (le_refl Z) D hi W B O pU Fv pF h0 p' hκ t pq).trans; apply (mul_le_mul_of_nonneg_right hu' (by positivity :0≤ Real.exp (b+rent n L+Ψ₀+f'))).trans
 rw [←Real.exp_add]; apply Real.exp_monotone
 let z:ℝ:= A.card; change τ + v+ (4*d +diamC*H'/w)*U' + z*(Jv-γ) +(b+rent n L+Ψ₀+f') ≤ τ + Ψ₀ + _*U' - _ -- tune
 have heS: Fee G n L (disc Z k) (parcelM Z k) r ≤ (d+d+d)*U'+ z* (γ/16):=by
    apply hy'.trans; change (_+d + τPeak diamC L' w)*U'+L'*z*tB k ≤ _; apply add_le_add (mul_le_mul_of_nonneg_right (add_le_add (add_le_add_left hR _) hu) he); apply (mul_le_mul_of_nonneg_left hL (show 0≤ z from Nat.cast_nonneg _)).trans' (Eq.le ?_); ring -- tune
 unfold service f' weather rent b allowance fine; linarith only [heS,mul_le_mul_of_nonneg_left sqC (show 0 ≤ z from Nat.cast_nonneg _), mul_nonneg hd.le he,mul_le_mul_of_nonneg_right hw he,show v≤d*U' from hg β hβ htβ p pp n, show ε*U'=d*12*U' from congr_arg (·*U') (by unfold d; ring)] -- tune
end Dig
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Dig.official
