import Gingham.Linen.Hank
import YM.CF.Vp929.Match.Rays
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
namespace MatchW
open Py.Rate Haro Cadre Wray Larch Ione
open Push.AbsoluteSums Haro Glyph Trees
open scoped Mew
local notation "Qu"=> Tenant.quota^2
variable (T S:BeatL n) {p:BudgetPoint}{v W e:ℝ}{B:ℕ}{L:Scree.Loom n}
open Technique
variable {T S} (Ω:Technique p W e d B L T S a b c r)
namespace Technique
local notation "Xp"=> Ω.note + Ω.note
local notation "Kr"=> Rinse (Seat n) (Copy n)
local notation "Er"=> ΘS r
local notation "λχ" i:max=> Ω.bond.litB Ω.H Ω.pay W Ω.floor Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize i
local notation "πχ"=> Pair (ΘS r)
local notation "I_"=> Complex.I
variable {Wk f m₁ m₂ u0 Λ ψ δ θ x g γΓ θΓ dΓ vδ r₁ s:ℝ}
local notation "Pk"=> cap1 p (BondL.øK r) W
local notation "VK"=> Vow.Cusp n
local notation "Θp"=> Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ
variable (Th: Py.Mood p (512*Wk) W a (Tenant.quota^2 * b) (Tenant.quota^2 * c) r s m₁ m₂ u0 vδ r₁ Λ ψ θ δ γΓ θΓ dΓ)

local notation "αB"=> p.supportExponent+1+1
include Ω Th
lemma rollH_raised (i:Er):IncX Utrue (Ω.lerW i) p.raisin W (φcape p.raisin a (Qu*b*r) (Qu*c*r) W)∧ IncX Utrue (Ω.ler i) p.raisin W (cap1 p.raisin (BondL.øK r) W):=by
 have k : 2*p.raisin.supportExponent*Fief.tileN 1 ≤ a/2*p.B := by
    apply le_trans _ (Th.speed.nf.trans _)
    · apply mul_le_mul_of_nonneg_right _ (by positivity)
      change 2*(p.supportExponent+1)≤_; unfold wu; linarith
    exact mul_le_mul_of_nonneg_right (by linarith only [Ω.pos]) (by positivity)
 rw [mul_assoc Qu b _,mul_assoc Qu c _]
 let A:= Ω.bond
 exact ⟨Ione.addT p.raisin (A.pay_r (p:=p.raisin) Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos k Ω.raw) (A.pay_z (p:=p.raisin) Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.pos k Ω.raw), A.starH (p:=p.raisin) Ω.H Ω.pay W Ω.floor i Ω.hope Ω.v0 Ω.threshold Ω.tally Ω.rate Ω.Bsize Ω.economic Ω.pos k⟩


/-- Internal verseY.1 excluding V_, suitable for adding to taped.1 minus noncash. -/
abbrev plies (i: Pair (ΘS r))(F:Pair (Vow.Cusp n))(τ:Ids n): RegBudget n :=
 Ω.lerW i.1+cast_E (Ω.νpoint i F).1 τ+Ω.ler i.1
abbrev plies_est (p:BudgetPoint)(s a b c r W:ℝ):ℝ :=
  φcape p.raisin a (Qu*b*r) (Qu*c*r) W+s^2+cap1 p.raisin (BondL.øK r) W
lemma plies_raised (i:πχ)(F:Pair VK)(pA:Coverable p W B F m₁ m₂)(hZ:Cash.poise (Ω.νpoint i F).1)(τ:Ids n): IncX Utrue (Ω.plies i F τ) p.raisin W (plies_est p s a b c r W) := by
 obtain ⟨A,U⟩:= Ω.rollH_raised Th i.1
 apply (Ione.addT p.raisin _ U)
 refine (Ione.addT p.raisin A ?_)
 obtain ⟨v,t,f⟩:= ((Ω.project_K Th i F pA).1).1
 apply Fixed.Voltage.upgradeI _ _ (worth_two p _ τ hZ.2 hZ.1 (zero_le_one.trans Ω.floor) t f)
 change tintK p (rentΦ p γΓ dΓ) θΓ vδ ≤ _
 linarith only [Th.lens,sq_nonneg s]
omit Th
lemma plies_roll (i:πχ)(F:Pair VK) (B:Pair (RegBudget n))(τ:Ids n) :
  (Ω.rollT i F B τ).1=B.1+Ω.plies i F τ :=by
 change B.1+_+_+_=B.1+(_+_+_)
 simp only [lerW,add_assoc]


omit Ω in
private lemma spanStep (i : ℕ) : 1≤ spanV i := by unfold spanV; exact_mod_cast Nat.one_le_pow 4 _ (by omega : 0 < i+i+1)












omit Ω
private lemma aim_one (B:ℕ) (w:ℝ) (v:0<a)(u:0≤w) : 1≤ aimV B a w := by
 have q:= Tenant.quota_bound
 have h : Summable (fun i:ℕ=> Real.exp (-a/2*i)*(quota*((i:ℝ)+1)^4)):=by
   have t: ‖Real.exp (-a/2)‖ < 1:=by
     rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
     exact Real.exp_lt_one_iff.mpr (by linarith)
   let r:=Real.exp (-a/2)
   have h':= (summable_nat_add_iff (f:=fun i:ℕ=>(i:ℝ)^4*r^i) 1).mpr (summable_pow_mul_geometric_of_norm_lt_one 4 t)
   refine (h'.mul_right ((Real.exp (-a/2))⁻¹*quota)).congr ?_
   intro i
   rw [Nat.cast_add, Nat.cast_one, pow_succ, mul_comm (-a/2), Real.exp_nat_mul]
   have g:r ≠ 0:=(Real.exp_pos _).ne'
   change (i+1:ℝ)^4 * (r^i*r) * (r⁻¹*quota)=r^i*_
   field_simp
 unfold aimV
 refine one_le_mul_of_one_le_of_one_le (spanStep B) ?_
 refine one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) ?_
 refine le_trans ?_ (h.le_tsum 0 (fun b _=>by
     have hp:0≤quota:=by linarith
     positivity))
 norm_num; linarith


include Ω Th
private lemma fit_size :
    0≤ Qu*b*r ∧ 0≤ Qu*c*r ∧ Qu*b*r≤1 ∧ Qu*c*r≤1 ∧ BondL.øK r≤1 := by
 have hb:0≤Qu*b*r:=by rw [mul_assoc]; exact Ω.bond.coreS.bank.posP
 have hc:0≤Qu*c*r:=by rw [mul_assoc]; exact Ω.bond.elt.bank.posP
 have hw:=Ω.floor
 have huv: 5*(Qu*b*r)+Qu*c*r ≤ δ := by
   apply le_trans _ Th.speed.fee
   unfold feeΨ
   refine le_mul_of_one_le_left (by positivity) ?_
   exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by simp) (one_le_pow₀ hw))
    (aim_one _ _ Ω.pos (by unfold wu; linarith only [p.exponent_pos]))
 have he:δ ≤ 1:= le_trans (le_mul_of_one_le_left Th.speed.zen (spanStep _))
   (Th.speed.endP.trans (by norm_num [wΨ]))
 have hb1:Qu*b*r≤1:=by linarith only [huv,hb,hc,he]
 refine ⟨hb,hc,hb1,by linarith only [huv,hb,hc,he],?_⟩
 refine le_trans ?_ hb1; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left Ω.bill (by positivity)


local notation "k6"=> 4+coinK 6 2  -- precedence!
abbrev yucc:= tollL0 6 2 2 * quota
abbrev qwick1 (W:ℝ):ℝ:=
 ((6:ℕ)+1:ℝ)*W^2*(yucc*1*2^(k6))
abbrev qwick2(W:ℝ)(b:ℕ):ℝ:=
 ((6:ℕ)+1:ℝ)*W^2*(yucc*1*(16 * fernL (k6) * (1+(b:ℝ))^((k6)+1)))
def bill_roll (W:ℝ)(b:ℕ) :ℝ:= qwick2 W b+qwick2 1 b+1+qwick1 W
omit Th Ω
open Linen
lemma poly_roll (W:ℝ): PolyBill (bill_roll W) := by
 have hx:=quota_bound
 have hy:0≤yucc:= mul_nonneg (by unfold tollL0 gown; positivity)
    (le_trans (by norm_num) hx)
 have hv:0≤fernL (k6):= by unfold fernL; positivity
 have k(v:ℝ):PolyBill (qwick2 v):= (PolyBill.const (by positivity)).mul ((PolyBill.const (by positivity)).mul ((PolyBill.const (by positivity)).mul ((PolyBill.plus (PolyBill.const zero_le_one) PolyBill.mid).expN _)))
 exact (((k W).plus (k _)).plus (PolyBill.const zero_le_one)).plus (PolyBill.const (by unfold qwick1; positivity))


private lemma ecap1 (po:p.order=6)(pw:p.power=2)(ps:p.supportExponent=1)
    {d:ℝ} (k:d≤1):cap1 p.raisin d W ≤ qwick1 W := by
 have hy: 0≤yucc:= mul_nonneg (by unfold tollL0 gown; positivity)
    (le_trans (by norm_num) quota_bound)
 unfold cap1 κY numV
 have pe : p.raisin.supportExponent=2 := by change p.supportExponent+1=_; rw [ps]; norm_num
 rw [pe, show p.raisin.order=6 from po, show p.raisin.power=2 from pw]
 -- avoid gcongr reducing
 exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left k hy) (by positivity)) (by positivity)
private lemma ecap2 (po:p.order=6)(pw:p.power=2)(ps:p.supportExponent=1)
    {d:ℝ} (k:d≤1) (u:0<a) (v:a⁻¹≤1+(p.B:ℝ)) : cap2 p.raisin d W a ≤ qwick2 W p.B := by
 have hy: 0≤yucc:= mul_nonneg (by unfold tollL0 gown; positivity)
    (le_trans (by norm_num) quota_bound)
 unfold cap2 κY numV
 have pe : p.raisin.supportExponent=2 := by change p.supportExponent+1=_; rw [ps]; norm_num
 rw [pe, show p.raisin.order=6 from po, show p.raisin.power=2 from pw]
 refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left k hy) ?_ (by unfold fernL oom; positivity) (mul_nonneg hy zero_le_one)) (by positivity)
 exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr u.le) v _) (by unfold fernL; positivity)


include Ω Th
lemma cap_roll (po:p.order=6)(pw:p.power=2)(ps:p.supportExponent=1)(g:s^2 ≤ 1):
   plies_est p s a b c r W ≤ bill_roll W p.B := by
 obtain ⟨_,_,l,v,u⟩:= fit_size Ω Th
 have ht:a⁻¹≤1+(p.B:ℝ):= by
   rw [inv_eq_one_div]; apply (div_le_iff₀ Ω.pos).mpr
   have k:=Th.speed.ny
   rw [ps] at k
   have w : (1:ℝ)≤Fief.tileN 1 := by norm_num [Fief.tileN]
   nlinarith only [w,k,Ω.pos]
 exact add_le_add (add_le_add (add_le_add (ecap2 po pw ps v Ω.pos ht)
                 (ecap2 po pw ps l Ω.pos ht)) g) (ecap1 po pw ps u)


#print bill_roll
#print PolyBill
#check plies_roll
#check plies_raised
#print axioms cap_roll
#print axioms poly_roll
#print axioms plies_raised

