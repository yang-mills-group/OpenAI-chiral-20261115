import YM.SU5.FiniteGaugeData.LapisQ.Probia
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxSize 23000
noncomputable section
namespace YM.SU5.FiniteGaugeData.LapisQ
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Lapis Punch Affiche Work.F06
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
set_option quotPrecheck false
namespace Nectar
open Nosh Apoth Real Vulcan Willow Lumi Cordon Tulipe
variable {G:Gauge}{n:Side} {ρ C Δ σ Q a b w:ℝ} {P:Bed} {u:Stage}{R: PathData G}
local notation "Ω"=> (Slot × Cover)
variable (F:Floor P u.clip n ρ C)(d:0<ρ)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(p:P.metric.strip σ Q)(hr:0<σ) (t:Site n)(r:ℝ)(x:Cover)
variable (a₁:G.ColorIndex)
local notation "κ₁"=>sineB F d a₁ a₁
local notation "Fw" => rayBeam F d
local notation "E"=> Vault (Plush G (denim n))
local notation "μ"=> stdGaussian (Vault (Plush G (denim n)))
noncomputable abbrev beamsS(t:Site n)(r:ℝ):G.ColorIndex→ Vault (Plush G (denim n)):= fun i=> r • rayBeam F d i (t,f0)
lemma rim (y:E): r • faceCurl (t,leg0) (olive F d G y)= opus (beamsS (G:=G) F d t r) y:=by
 ext i; change r *beams F d i y (t,f0)=inner ℝ (r • rayBeam F d i (t,f0)) y; rw [beamPrice,real_inner_smul_left]
include W A p hr
lemma gateZ: Gate u P ρ C σ Q n (sineB F d a₁ a₁):= ⟨F,d,p,hr,splend F d W A a₁, sunM F d W A a₁⟩
local notation "𝕍" x:max=> songV (κ₁) x
omit W A p hr in
private lemma shiftedK {C:Matrix (Body 2 n) (Body 2 n) ℝ}(x y:Site n)(h:stationaryB C): C (x,f0) (y,f0)=songV C (y-x):=by
 have he:=congrFun (congrFun (h (-x)) (x,f0)) (y,f0); change C (x+-x,f0) (y+-x,f0)= C (x,f0) (y,f0) at he; rw [add_neg_cancel] at he; rw [sub_eq_add_neg]; exact he.symm
omit p hr in
private lemma p_matchD (i:G.ColorIndex)(x y:Body 2 n): inner ℝ (Fw i x) (Fw i y)=sineB F d a₁ a₁ x y:=by
 exact (beamPrice F d i _ _).symm.trans (congrFun (congrFun (pigment F d W A i a₁) x) y)
omit p hr in
private lemma t_matchD (i j:G.ColorIndex)(x y: Body 2 n)(e:i≠j): inner ℝ (Fw i x) (Fw j y)=0:=by
 exact (beamPrice F d i _ _).symm.trans (show sineB F d i j x y=0 from (congrFun (congrFun (abyss F d W A i j e) x) y))
lemma stoutS (i j:G.ColorIndex)(x y:Site n): inner ℝ (Fw i (x,f0)) (Fw j (y,f0))= if i=j then songV (sineB F d a₁ a₁) (y-x) else 0:=by
 by_cases v:i=j; · subst j; rw [if_pos rfl]; exact (p_matchD F d W A a₁ _ _ _).trans (shiftedK x y (gateZ F d W A p hr a₁).stands)
 exact (t_matchD F d W A _ _ _ _ v).trans (if_neg v).symm
lemma matC : Dun (beamsS (G:=G) F d (0:Site n) r) (beamsS F d t r) (r^2 * (songV (sineB F d a₁ a₁) 0)) (r^2 * songV (sineB F d a₁ a₁) t):=by
 have he(y z: Site n)(i j:G.ColorIndex):inner ℝ (beamsS (G:=G) F d y r i) (beamsS F d z r j)=if i=j then r^2*(𝕍 (z-y)) else 0:=by
    unfold beamsS; rw [real_inner_smul_left,real_inner_smul_right,stoutS F d W A p hr a₁]; split_ifs <;> ring
 unfold Dun; simp_rw [he,sub_self,sub_zero]; tauto
abbrev eyeS (G:Gauge)(x:Cover):= dualY G (sprinkle 0 leg0) (sprinkle x leg0)
abbrev pollenJ (G:Gauge)(x:Cover)(t:ℝ) := divanF (eyeS G x) F d (eyeS G x).seen t
lemma parZ : pollenJ F d G x r= sheet (r^2*songV (sineB F d a₁ a₁) 0) (r^2*songV (sineB F d a₁ a₁) (wrap n x)) (Fintype.card G.ColorIndex):= by
 let T:= eyeS G x; let B:=beamsS (G:=G) F d; unfold pollenJ divanF; change (∫ y:E,T.seen (r • pollen T 1 0 (olive F d G y))∂stdGaussian _)=_; rw [← canon (B (0:Site n) r) (B (wrap n x) r) (matC F d W A p hr (wrap n x) r a₁)]
 apply integral_congr_ae; refine Eventually.of_forall fun y=>?_ ; let z:= olive F d G y; change mentor (r • (pollen T 1 0 z) false)*mentor (r • (pollen T 1 0 z) true)=_; rw [baseNeed,baseNeed, show T.beam false=sprinkle 0 leg0 from rfl, show T.beam true=sprinkle x leg0 from rfl, wet0,wet0,map_zero,add_zero,add_zero]; unfold z; rw [rim F d, rim F d]
-- Uniform comparison once shell.S.Frame keep one r AND d in response; no product priced separately
omit W A p hr
section
variable (G)
variable [Nonempty G.ColorIndex]
lemma cubage (Q σ ρ:ℝ)(b c:ℝ)(d:0<b)(u:0<ρ)(ℓ k:ℕ)(j:Axis)(q₀:0<k):∃ e:ℝ,0<e ∧∃ I D J:ℕ,∀ {n:Side},I ≤ n.val → ∀ {u:Stage}{P:Bed}{C:ℝ}{R:PathData G}{Δ:ℝ}(F:Floor P u.clip n ρ C),R.Bounds u.clip u.width u.paths Δ → Attached P R → P.metric.strip σ Q → 0<σ → ∀{r:ℝ}, b≤r → r≤c → ∃ y∈ marketZ D,lapse ℓ y ∧ 0<y j ∧∃ l:ℕ,0<l∧ l<J ∧ e ≤ pollenJ F ‹0<ρ› G y r - pollenJ F ‹0<ρ› G (leapU y j k l) r:=by -- ‹ › shadow u identifiers rename
 obtain ⟨a,e,M,L,U₀,W⟩:= Cordon.steamQ ℓ k j ρ σ Q u q₀; -- order check
 let v:= a^2-(a/2)^2; let Y:= b^4*v; have he:0<v:=by unfold v; rw [sub_pos]; exact pow_lt_pow_left₀ (half_lt_self e) (half_pos e).le (by omega)
 have hv : 0<Y:=mul_pos (pow_pos d 4) he; obtain ⟨z,f,P'⟩:= sonic_gap (k:=Fintype.card G.ColorIndex) hv Fintype.card_pos (c^2*(1/ρ)); refine ⟨z,f, M,U₀,L,?_⟩
 intro n v0 u' P C R Δ F xJ₁ xJ₂ aW h0 r y₀ tZ; let a₁:=Classical.arbitrary G.ColorIndex; let X:= sineB F u a₁ a₁; have hg:= gateZ F u xJ₁ xJ₂ aW h0 a₁; obtain ⟨z,p,q,hx,hw,i,v_,w,h⟩:= W n v0 X hg; refine ⟨z,p,q,hx,i,v_,w,?_⟩; let t₁:= leapU z j k i; let My(y:Cover):= songV X (wrap n y); let ts(w:Cover):=r^2*My w; let C0:=songV X 0; let D0:= r^2*C0; have hf(w:Cover): |ts w| ≤ D0 := valNon (beamsS F u 0 r) (beamsS F u (wrap n w) r) (matC F u xJ₁ xJ₂ aW h0 _ r a₁)
 rw [parZ F u xJ₁ xJ₂ aW h0 r z a₁,parZ F u xJ₁ xJ₂ aW h0 r t₁ a₁]
 have hq : a^2≤ My z^2:=calc
    _ ≤ |My z|^2:= pow_le_pow_left₀ e.le hw _
    _ = _:= sq_abs _
 have hq': My t₁^2 ≤ (a/2)^2:=calc
    _ = |My t₁|^2:=(sq_abs ..).symm
    _ ≤ _:=pow_le_pow_left₀ (abs_nonneg _) h _
 refine P' D0 (ts z) (ts t₁) (le_trans (mul_le_mul_of_nonneg_left (le_of_abs_le (life_spend hg 0)) (sq_nonneg _)) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (d.le.trans y₀) tZ _) (by positivity))) (hf _) (hf _) ?_
 have hv:v*r^4=(r^2)^2*v:=by ring
 have hx':(ts z)^2-(ts t₁)^2=r^4*(My z^2-My t₁^2):=by unfold ts; ring
 apply le_sub_iff_add_le'.mp -- want `u*v + ...≤`; tune 
 rw [hx']; apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ d.le y₀ _) he.le); exact mul_le_mul_of_nonneg_left (sub_le_sub hq hq') (by positivity)
end
end Nectar
end YM.SU5.FiniteGaugeData.LapisQ
#print axioms YM.SU5.FiniteGaugeData.LapisQ.Nectar.cubage
