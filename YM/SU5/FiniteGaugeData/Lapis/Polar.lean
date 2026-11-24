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
variable {U Q:Config G n→ℝ}(hs:Envelope U)(h0:∀ x:Config G n,U x≠0→(∀ i:Cell n,i∈A ↔ p.threshold<G.chord (faceValue x i))∧ U x≤ Real.exp (Q x- R.principal u.clip p β x))
variable (t:Opal L F)(Zq:Boat Q W B p F A Z M k w κ β ε)(uL:0≤L)(pk:|κ|≤2)(hα:α ≤1/2)(hρ: |Real.sqrt β/Real.sqrt (gross w u β α)|≤2)
local notation "Φ" => skyR (κ:=κ) (β:=β) (Z:=Z) (k:=k) F W B
local notation "fₐ" => allowance p u A β ε
local notation "c₀" => rent n L
local notation "C'"=> feeZ S J' p β α Δ μ P A Z k w M
local notation "Z'"=> greatF S n w M p β α Δ
local notation "ψ₀"=> High W B D F κ w0
local notation "t₀" => weather G L Z k (Real.sqrt β / Real.sqrt r')
include T hz hs h0 uL t Zq pk hα hρ
lemma tireless: (∫ i,U (makeup O i) ∂ piHaar G (↥(buy Z k))) ≤
 (C')*Real.exp (fₐ+c₀+ψ₀+t₀) :=by
 let K:= buy Z k; let J₀:=Plush G K; let X:= zodiac P G K; let ν:=orient O Z M; let Z₀:=Z'; let τ:=r'; let E:= ψ₀; let E':=t₀; let U' (i:Batch G K):= U (Vogue Z M k O i); have hz' := onRoad_mp («I»:=buy Z k) ν; let T':=piHaar G (↥K)
 have hβ:=T.warm; have hv: 0≤(1-α)*β/2:=by have hw:=sub_pos.mpr T.legal; positivity
 have hm:k<M:=by refine Nat.lt_of_lt_of_le ?_ T.tall; unfold debit roomCard; omega
 let a':= hz.trans (glow_in ..)
 have hy: (∫ i,U (makeup O i) ∂T')=(∫ i,U' i∂T'):=by
    let V(i):=U (makeup O i); have hv:=integral_map (μ:=T') (f:=V) hz'.measurable.aemeasurable (by rw [show T'=_ from rfl,hz'.map_eq]; exact (hs.meas.comp (makeup_ok O)).aestronglyMeasurable); rw [hz'.map_eq] at hv; exact hv -- μ shorthand??? literal local μ
 let Δ':= Z'- (A.card:ℝ)*(η); let I₀:=Δ' + fₐ + c₀; let x':= flake O M; obtain ⟨m,v⟩:= true_offer (w:=w) D W B hm.le a' x'
 let ηu(x:coin J):= Real.exp (Φ x); let f(x:coin J):= ηu (x+m)* doll X (x+m) τ; let E₀:=Real.exp I₀; let t':= holdK X τ
 obtain ⟨iF,hF⟩:= Syl.windmills F t a' hm.le W B D w0 T.spry uL pk hρ; obtain ⟨tF,h'⟩:= stage X (shine K G D w0) ηu m T.spry iF
 have hp(x):0≤f x:= mul_nonneg (Real.exp_pos _).le (doll_p ..); have hh:(∫ x:coin J,f x) ≤ holdK X τ*Real.exp (E+E'):=le_trans h'.le (mul_le_mul_of_nonneg_left hF (lensP (shine K G D w0) T.spry).le)
 rw [hy]; apply le_trans (thrill T.lucent T.homeF.le U' (int_e U hs _ (show Measurable (Vogue Z M k O) from (makeup_ok O).comp hz'.measurable)) f tF hh hp (K:=E₀) (Real.exp_pos _).le ?_) (le_of_eq ?_); swap
 · let c:= (J'.scale*μ)^K.card; rw [Fintype.card_coe]; change (c*Real.exp I₀)*(t'*Real.exp (E+E'))=c*Real.exp Δ'*t'*Real.exp (fₐ+c₀+E+E'); have he: Real.exp I₀*Real.exp (E+E') = Real.exp Δ'*Real.exp (fₐ+c₀+E+E'):=by rw [←Real.exp_add, ←Real.exp_add]; unfold I₀; congr 1; abel -- tune newline
   calc
      _ = c*t'*(Real.exp I₀*Real.exp (E+E')):=by ring
      _ = _ :=by rw [he]; ring
 intro j u₀; let V:= Vogue Z M k O j; let Y:= care O M j; let q:=assetX Y Z M; obtain ⟨hP,e⟩:=h0 V u₀; obtain ⟨x,c,g,l,br,Vφ⟩:= section_bound O S p.threshold_pos.le hz hm T.wide j hP T.frameH; let d:= tape.symm x
 refine ⟨x,g,c,?_⟩; let V':= kickC I (d+m); let c':=dotProduct (d+m) (X*ᵥ (d+m)); let h':=‖H q-H V'‖
 have ht: accepts u R (billsC k w Z) q ≥ (1-M')*c'+h'^2:= by change _ ≥ _ + ‖H q - H V'‖^2; rw [show q=x'+kickC I d from Vφ]; exact v _
 have hh':= weights (k:=k) S p V Y ν rfl q W br hz hP T.atfar T.tall l T.rood T.warm.le T.witness T.legal.le; let θ:= ((1-α)*β/2)*h'^2
 have hv₀ : - R.principal u.clip p β V ≤ Δ'+ -τ/2*c' - θ:=by unfold τ Δ' θ gross bonusK greatF; linarith only [hh', mul_le_mul_of_nonneg_left ht hv]
 let κ':=κ*Real.sqrt β; let z:=Φ (d+m); have he: Q V≤ c₀+θ+z+fₐ:=by
    have p0:= recoil (n:=n) h' (norm_nonneg _) uL T.warm.le pk hα
    have hU:= t.breeze -- t shadowed
    have he:= le_of_abs_le (hU (κ'• H q) (κ'•H V')); rw [← smul_sub,norm_smul,show F (κ'•H V')=z from Syl.restrictP t W B (d+m) w κ'] at he; linarith only [Zq V ν q hP l br,(show F (κ' • H q)-z≤rent n L +θ from he.trans p0)] -- tune
 change U V ≤ Real.exp I₀* (Real.exp z *Real.exp _); apply e.trans; rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
 change _ ≤ I₀+(z + -τ/2 * c'); unfold I₀; linarith only [hv₀,he]
end Dig
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Dig.tireless
