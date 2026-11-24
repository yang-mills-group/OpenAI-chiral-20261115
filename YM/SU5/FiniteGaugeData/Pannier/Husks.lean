import YM.SU5.FiniteGaugeData.Pannier.Marigold
/-! # High observation scale pressure relative to classical link measure order. -/

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
-- asymptotic height cost after relative stripping. Late threshold can depend on the rest of the choices.
private lemma decline {V A:ℝ}(p:1<V)(u:2≤V)(t:0≤A) (d:ℕ→ℝ) (h:∀ᶠ s in atTop, V*d (s+1)≤d s+A) :∀ᶠ s in atTop, d s ≤ A+1:=by
 obtain ⟨i,k⟩:= eventually_atTop.mp h
 let x(j):=(d (i+j)-A)
 let B:= d i - A
 let ε:ℝ:=V⁻¹
 have hh:0<V:=zero_lt_one.trans p
 have l(k:ℕ):0< V^k:=pow_pos hh _
 have h0(j:ℕ):V*x (j+1)≤x j:=by
    have he:=k (i+j) (Nat.le_add_right ..); unfold x; rw [Nat.add_assoc] at he; nlinarith only [he,t,u]
 have hx(j): x j ≤ B/V^j:=by
    induction j with
    | zero=> simp [x,B]
    | succ j ih=> refine (le_div_iff₀ (l _)).2 ?_; rw [pow_succ]; calc
                        _ = V*x (j+1)*V^j := by ring
                        _ ≤ x j*V^j:= mul_le_mul_of_nonneg_right (h0 j) (l _).le
                        _ ≤ _ := (le_div_iff₀ (l _)).1 ih
 obtain ⟨N,hp⟩:=eventually_atTop.mp ((tendsto_pow_atTop_atTop_of_one_lt p).eventually_ge_atTop B)
 filter_upwards [eventually_ge_atTop (i+N)] with n q

 let k:= n-i
 have ht: x k≤1:= (hx k).trans ((div_le_one (l k)).mpr (hp k (by unfold k; omega)))
 unfold x at ht; rw [show i+k=n from (by unfold k; omega)] at ht; linarith
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
local notation "y" i:max=> hat Λ.R.L Λ.x i
local notation "L"=> (Λ.R.L.val:ℝ)
local notation "Φ" s:max => Λ.C s
def attrition : ℕ→ℝ
 | 0=> Y.τ
 | s+1=> (attrition s+Φ (y s))/L^4 -- recursion explicit implicit Y argument?
local notation "Pμ" i:max => attrition Y i
local notation "Jm"=> Λ.block

lemma expansionStep (i t:ℕ): sites (Λ.Ctor (Y.ir i) (t+1))=L^4*sites (Λ.Ctor (Y.ir i) t):= by
 rw [sites, sites]; unfold Ctor cell CSide More; rw [mesh_succ]; push_cast; ring
lemma turnover (Λ:Preparation): Tendsto (hat Λ.R.L Λ.x) atTop atTop:= by
 have he : 0 < billX Λ.R.L:= mul_pos (Gauge.slopeConstant_pos Thera.yet_one) (Real.log_pos (by exact_mod_cast (show 1<Λ.R.L.val by have he:=Λ.V.tallX; omega)))
 exact tendsto_atTop_add_const_left _ _ (tendsto_natCast_atTop_atTop.atTop_mul_const he)

def mulch (x:ℝ):= 3*(halfLie SU.group *Real.log x)
include Y
lemma extinguishes {A:ℝ}(p:Inflation A Λ):∀ᶠ s in atTop, attrition Y s ≤ mulch (hat Λ.R.L Λ.x s)+ (A+1):=by
 let f(s):= attrition Y s-mulch (hat Λ.R.L Λ.x s)
 have hp: 2 ≤ L:= by exact_mod_cast (show 2 ≤ Λ.R.L.val by have he:= Λ.V.tallX; omega)
 have he: (2:ℝ) ≤ L^4:=hp.trans (le_self_pow₀ (one_le_two.trans hp) (by norm_num))
 apply (decline (V:=L^4) ((by norm_num :(1:ℝ)<2).trans_le he) he p.pos.le f ?_).mono (fun i t => by unfold f at t; linarith)
 filter_upwards [(turnover Λ).eventually p.requisite] with s v
 let x:= hat Λ.R.L Λ.x
 have hl(i):0<x i:= zero_lt_one.trans_le (Y.oneP.trans (Vale.crown ..))
 let g:= Rate.Pannier.halfLie SU.group
 have h:x s ≤ x (s+1):=by unfold x hat; push_cast; nlinarith [Gauge.slopeConstant_pos Thera.yet_one,show 0 ≤ billX Λ.R.L from mul_nonneg (Gauge.slopeConstant_pos Thera.yet_one).le (Real.log_nonneg (one_le_two.trans hp))] -- tune implicit he?
 have hu:= mul_le_mul_of_nonneg_left (Real.log_le_log (hl s) h) (show 0≤ g from pen_log_nonneg SU.group)
 have hx : Scales.y SU.group Λ.R.L (x s)=x (s+1):= (hat_succ ..).symm
 unfold f mulch; change L^4*(attrition Y (s+1)-3*(g*Real.log (x (s+1)))) ≤ (attrition Y s- _)+A
 rw [mul_sub,attrition, ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)] -- check lemma
 change Λ.C (x s) ≤ ((L^4-1)*3)*(g*Real.log (Scales.y SU.group Λ.R.L (x s)))+A at v
 rw [hx] at v
 change attrition Y s+Λ.C (x s)- L^4 * (3*(g*Real.log (x (s+1)))) ≤ attrition Y s-3*(g*Real.log (x s))+A
 linarith
include Λ
local notation "Volx" i:max t:max => sites (Λ.Ctor (Y.ir i) t)
private lemma inScale (i k t:ℕ)(h:(Y.voyage i).kick≤ k)(ht:t ≤ Y.uv k) :
     Real.exp (-attrition Y t *sites (Λ.Ctor (Y.ir i) t)) ≤ ‖compensated Λ.U (((Y.voyage i).X (Y.uv k)).gram t) ((Y.voyage i).CapeT t)‖ := by
 let H := (Y.voyage i).X (Y.uv k); let l:ℕ→ℂ:= fun t=>partitionZ (H.gram t) Λ.U ((Y.voyage i).CapeT t)
 induction t with
 | zero=> exact (Y.voyage i).lower k h
 | succ j ih=>
    have hg:= ih (le_of_lt ht); let V0:= Volx i j; let Vp:=Volx i (j+1); let Z:= ‖l j‖; let a:= H.gram j; let b:=H.gram (j+1)
    have ht':=H.perSite j ht; change |a.v.re-b.v.re| ≤ _ at ht'
    simp only [compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hg ⊢; change Real.exp (-Pμ (j+1)* Vp)≤ Real.exp (-b.v.re)*‖l (j+1)‖
    rw [show l (j+1)=l j from (H.balance _ ht).trans (H.balance _ (le_of_lt ht)).symm]; let B:=Φ (y j); let W:=Pμ j
    change Real.exp (-W*V0)≤ Real.exp (-a.v.re)*Z at hg
    calc _= Real.exp (-B*V0)*Real.exp (-W*V0):=by rw [show Vp=L^4*V0 from expansionStep ..,←Real.exp_add]; congr 1; change (-((W+B)/_)*_)=_; field
         _ ≤ Real.exp (-B*V0)*(Real.exp (- a.v.re)*Z) := mul_le_mul_of_nonneg_left hg (by positivity)
         _ ≤ _ := by
            rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; change |a.v.re-b.v.re|≤ B*V0 at ht'; linarith [(abs_le.mp ht').1]

/-- Uniform in period and equipped cutoff on the actual course. -/
theorem compensates {A:ℝ}(p:Inflation A Λ): ∀ᶠ s:ℕ in atTop,∀ i k,
    (Y.voyage i).kick≤ k → s ≤ Y.uv k → Real.exp (-(mulch (hat Λ.R.L Λ.x s)+(A+1))*sites (Λ.Ctor (Y.ir i) s)) ≤ ‖compensated Λ.U (((Y.voyage i).X (Y.uv k)).gram s) ((Y.voyage i).CapeT s)‖ := by
 filter_upwards [extinguishes Y p] with s v i k hp h
 exact (inScale Y i k s hp h).trans' (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg v) (zero_le_one.trans (sites_pos _))))
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.compensates
