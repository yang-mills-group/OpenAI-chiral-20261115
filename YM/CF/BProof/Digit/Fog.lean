import YM.CF.BProof.Digit.Bow
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Digit
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
open Haro Ione Larch Glyph
section
variable {N:Side}
end
open Exa Tap Dial
open Push.AbsoluteSums Trees Mew Floral Axial
open scoped YM.CF.Mew YM.CF.Sour.Axial
variable {T S:BeatL n}{U:Scree.Loom n}{R t d a b c W z₀ z₁:ℝ}{q:ℕ} {m:Cash P}
-- pay requirements. power later enforced
structure LoomPay (P:BudgetPoint)(m:Cash P)(R W a b c:ℝ) : Prop extends m.Warrant where
 fp: 0<R
 aa: 0<a
 ab: a≤1
 ny:2*P.supportExponent*Fief.tileN 1≤a/2*P.B
 nf:2*(wu P+2)*Fief.tileN 1 ≤ a/2/2*P.B
 cap: feeΨ P a (knot R b) (knot R c) W ≤ m.d/20
-- flag leaves + read with master inflation
structure Quir (m:Cash P)(B:Cusp n)(δ:ℕ)(W:ℝ):Prop where
 theme :∀ X:Aura n,∀ D⊆ X.val,Lives P δ X D (B X D)
 maxH : Binder P W (wu P) (Fine B) (m.sh/10)
 maxF : Flaws P W (wu P) B (m.sf/10)
namespace Quir
variable {B:Cusp n}{δ:ℕ}
lemma perks (v:Quir m B δ W)(p:0 ≤ W):0 ≤ m.sh∧0 ≤ m.sf:=by
 have ht:0 ≤ wu P:=(Cash.Φk P).trans (Cash.uv P); exact ⟨nonneg_of_mul_nonneg_left (by simpa [div_eq_mul_inv] using Binder.pos v.maxH ht p) (by norm_num : 0 < (10:ℝ)⁻¹),nonneg_of_mul_nonneg_left (by simpa [div_eq_mul_inv] using Flaws.pos v.maxF p ht) (by norm_num : 0< (10:ℝ)⁻¹)⟩ -- tune
lemma prices (v:Quir m B δ W)(p:0≤W): ∃ Q,m.grapes Q B δ W:=by
 obtain ⟨u,h⟩:= v.perks p; exact Leaf.appointed v.theme (v.maxH.mono (by linarith)) (v.maxF.mono (by linarith))
end Quir
local notation "δ"=> cipherK q
variable (k:Arbor P U q t d W z₀ z₁) (F:BondL T S (body_Q (N:=n) 1) b c a d) (p:LoomPay P m R W a b c)[Nonempty (ΘS R)]
local notation "A₀"=> orchard F R p.fp.le
include p
lemma creed : HiveQ ((A₀).bead W P) P (wu P+2) (m.d/20):= fun i=>(fee_bead F p.fp.le p.aa p.nf i).trans p.cap
lemma cop : HiveQ ((A₀).bead W P) P (wu P+2) m.d:= fun i=> (creed F p i).trans (by linarith [p.zen])
omit p
variable {ε hd:ℝ} {B G:Cusp n}
abbrev hallNR (u:ℝ):= 1+u⁻¹
local notation "h_"=> hallNR (ε+hd)
structure Court (B G:Cusp n)(P:BudgetPoint)(δ₀:ℕ)(m:Cash P)(R W ε hd:ℝ)(Q₀ Q₁:ΘS R) :Prop where
 lo:Quir m B δ₀ W
 hi:Quir m G δ₀ W
 he: 0≤ε
 he':ε≤1
 ah:0≤hd
 bh:hd≤2
 dist: ‖Q₁.val-Q₀.val‖≤ hd*R
 pos:0 < ε+hd
 tel : Binder P W (wu P) (Fine (G-B)) (ε*(m.sh/10))
 sale : Flaws P W (wu P) (G-B) (ε*(m.sf/10))
namespace Court
variable {Q₀ Q₁:ΘS R}(v:Court B G P (cipherK q) m R W ε hd Q₀ Q₁)
def ray (x:ℂ):= B+x • (G-B) -- no p
include v
lemma hl:1<h_:= lt_add_of_pos_right _ (inv_pos.mpr v.pos)
lemma warp_e (x:ℂ)(u:x∈disk h_) : ‖x‖*ε≤2 ∧ 1+‖x‖*hd≤4 :=by -- tune binder x
 have hh:‖x‖ ≤ h_ := (mem_ball_zero_iff.mp ‹x∈disk _›).le; let S':=(ε+hd)⁻¹; have het:=inv_mul_cancel₀ (ne_of_gt v.pos); have ht:S'*ε≤1:=le_trans (mul_le_mul_of_nonneg_left (show ε≤ε+hd from (le_add_of_nonneg_right v.ah)) (inv_nonneg.mpr v.pos.le)) het.le; have hz:S'*hd≤1:=le_trans (mul_le_mul_of_nonneg_left (show hd≤ε+hd from (le_add_of_nonneg_left v.he)) (inv_nonneg.mpr v.pos.le)) het.le
 constructor
 · refine le_trans (mul_le_mul_of_nonneg_right hh v.he) ?_; unfold hallNR; change (1+S')*ε ≤ _; linarith only [ht,v.he']
 apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hh v.ah) 1) -- tune comm
 change 1+(1+S')*hd≤4; linarith only [hz,v.bh]
omit v
local notation "J"=> stack k F
local notation "J₀"=> (J Q₀.val)
local notation "y"=> Q₁.val-Q₀.val
local notation "μ₀"=> (A₀).bead W P
include p k F v
lemma pursue (x:ℂ)(u:x∈disk h_): let μ:= μ₀+‖x‖ • (hd • μ₀); let Y:Bag n:=tuneB k F Q₀.val+x • tuneB k F y; let K:=J₀+x • J (y)
     wire P W δ K μ Y ∧ HiveQ μ P (wu P+2) m.d ∧ Burst P K (tuneZ k F Q₀.val+x • tuneZ k F y):=by -- local notation `(y)` parentheses precedence tune
 intro μ Y K; obtain ⟨z,t⟩:= sounds k F p.fp.le hd v.ah y v.dist
 refine ⟨wire.lamp_a (kernel_p k F p.fp.le Q₀) (wire.lamp_c z x),fun i=>?_, (kernel_v k F p.fp.le Q₀).plus (t.sail x)⟩
 have he:0 ≤ ‖x‖ := norm_nonneg _; have hh:= v.ah; obtain ⟨-,h⟩:= warp_e v x u; unfold μ; rw [tall_add,tall_s,tall_s]; have hu:=creed F p i; have hp:=p.zen; rw [show tallB _ _ _ _+ _= (1+‖x‖*hd)*tallB (μ₀) P.B (wu P+2) i from (by ring)]; exact (mul_le_mul_of_nonneg_left hu (by positivity)).trans ((mul_le_mul_of_nonneg_right h (by positivity : 0≤ m.d/20)).trans (by linarith)) -- tune
omit F p
lemma heights_c(x:ℂ)(u:x∈disk h_) : ∃ Q,m.grapes Q (B+x • (G-B)) (cipherK q) W:=by
 have h0:= zero_le_one.trans k.hw; obtain ⟨ht,hp⟩:= v.lo.perks h0; obtain ⟨he,-⟩:=warp_e v x u
 refine Leaf.appointed (fun X D z=> lives_sum (v.lo.theme X D z) (lives_c ?_ x)) (Wallet.mono (Binder.plus v.lo.maxH (Binder.σ v.tel x)) ?_) (Wallet.mono (Flaws.plus v.lo.maxF (Flaws.σ v.sale x)) ?_)
 · -- tune lives
    change Lives P (cipherK q) X D ((G-B) X D); have e: Lives P (cipherK q) X D ((G X D)+(-1:ℂ) • (B X D)):= lives_sum (v.hi.theme X D z) (lives_c (v.lo.theme X D z) (-1:ℂ)); simpa [sub_eq_add_neg] using e
 · nlinarith only [ht,mul_le_mul_of_nonneg_right he ht]
 nlinarith only [hp,mul_le_mul_of_nonneg_right he hp]
end Court
end YM.CF.Sour.Digit
