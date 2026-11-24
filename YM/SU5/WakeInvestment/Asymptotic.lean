import YM.SU5.WakeInvestment.Lens

/-!
# Acquisition order and an explicit small rate

Using power-of-X chip, the resolution of q-Mark instances can pass on this Ward estimate with
errors AFTER amplification by the requisite $\tau_s^{-1}$ test on the integral's derivative —
here τ means estimating parameter on that Mark; not editing Porch by changing the grams, thresholds,
or period rules. Co-efficient estimates for Holder comparison with real parts collected from
**pose measurements**, not Gaussian field independence. Integer plan (exponents on chip):
* Gram angular loss -320 from Yoke meter.
* Saber horizon 40, column error -8 (can pay ≤ -10 with constants; retain -8).
* Take Mark cost at -200 width; can pay Lyrics up through -199 on those conditional polynomial
  representatives, log payment via bounds on re-tested norm at -198 and energy-absorption into N.
Keep residual through -205 (allow –204 for orientation or gauge; assert -205 from spin Tilt).
No claim yet here that WA.7 data themselves available, or uniformity in number of such sequential
queries. Goal use with any fixed `p_X^A` legislative bounds (S from manuscript: $p_X=...$),
as that is smaller than even one chip power after taking the appropriate threshold.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.WakeInvestment
open Function Filter Metric Finset BProof Pressure
open Papyrus Papyrus.Franc
open scoped Topology ContDiff Matrix MatrixOrder BigOperators InnerProductSpace ComplexOrder

abbrev chip (x a:ℝ) := coin x (a/400000) 0 0
lemma chip_add (x a b:ℝ) : chip x (a+b)=chip x a*chip x b:= by rw [coin_mul]; unfold chip; ring_nf
lemma chip_pow (x a:ℝ)(i:ℕ) : (chip x a)^i=chip x (a*i):=by rw [coin_pow]; unfold chip; ring_nf
lemma chip_pos (x a:ℝ) : 0<chip x a:= coin_pos ..
lemma chip_spend (a b C D:ℝ) (p:a < b)(d:0<D):∀ᶠ x in atTop,C*chip x a < D*chip x b:=coin_budget (Or.inl (div_lt_div_of_pos_right p (by norm_num))) C D d

lemma meterChip (x:ℝ): Worth.meterC x=chip x (-320):=by unfold Worth.meterC Worth.r_meter chip; norm_num

abbrev horizonS (x:ℝ) := ⌈chip x 40⌉₊ -- no comparison to paths of step

lemma rise_law (C:ℝ)(u:0<C) : ∀ᶠ x in atTop, 1 ≤ (↑(horizonS x):ℝ)*(chip x (-8)^2/C)^2:=by
 filter_upwards [chip_spend 0 8 (C^2) 1 (by norm_num) zero_lt_one] with x v
 apply le_trans _ (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _))
 rw [div_pow,←mul_div_assoc,chip_pow,chip_pow,← chip_add, le_div_iff₀ (pow_pos u 2)]
 push_cast; rw [show 40+(-8:ℝ)*2*2=8 by norm_num,one_mul]; exact le_of_lt (by simpa only [chip,zero_div,coin_zero,mul_one,one_mul] using v)

lemma fee_chip (x:ℝ) (w:ℝ)(m:ℕ) (p:1 ≤ chip x 40) :
    fee (chip x (-199)) m (1+horizonS x) w (chip x (-8)) (chip x (-198)) ≤
      18*(tiltBound*wordToll w m)^2*chip x (-318)+tiltBound*wordToll w m*chip x (-207)+ 2*chip x (-396) := by
  unfold fee; let N : ℝ := (horizonS x)
  have h₁ : 1+N ≤ 3*chip x 40 := by
    have h:N < chip x 40+1:= Nat.ceil_lt_add_one (zero_le_one.trans p); linarith only [h,p]
  let W:=tiltBound*(1+N); let T:= tiltBound*(3*chip x 40); have hx:= tiltBound_pos; have hw:0≤W:=by unfold W N; positivity
  have hu:W^2 ≤ T^2:=pow_le_pow_left₀ hw (mul_le_mul_of_nonneg_left h₁ hx.le) _
  let u:=chip x (-8); let n:=chip x (-199); let s:=wordToll w m; let r:=chip x (-198)
  change (W^2+W^2)*(n*s)^2 + tiltBound*u*n*s + 2*r^2 ≤ _
  have he:T=3*tiltBound*chip x 40:=by unfold T; ring
  apply (add_le_add_left (add_le_add_left (mul_le_mul_of_nonneg_right (add_le_add hu hu) (sq_nonneg _)) _) _).trans_eq
  have hf:T^2*n^2=(3*tiltBound)^2*chip x (-318):=by
    rw [he, mul_pow _ (chip x 40),mul_assoc]; congr 1; unfold n; rw [chip_pow,chip_pow,←chip_add]; norm_num
  have hg:r^2=chip x (-396):=by unfold r; rw [chip_pow]; norm_num
  have hk:u*n=chip x (-207):=by unfold u n; rw [←chip_add]; norm_num
  rw [mul_pow n,hg,mul_assoc tiltBound u n,hk,add_mul,←mul_assoc (T^2),hf]; ring

lemma year_chip (w:ℝ)(m:ℕ) : ∀ᶠ x in atTop,
    fee (chip x (-199)) m (1+horizonS x) w (chip x (-8)) (chip x (-198)) ≤ chip x (-205) := by
  let A:= tiltBound*wordToll w m
  filter_upwards [chip_spend 0 40 1 1 (by norm_num) zero_lt_one,
     chip_spend (-318) (-205) (18*A^2) (1/4) (by norm_num) (by norm_num),
     chip_spend (-207) (-205) A (1/4) (by norm_num) (by norm_num),
     chip_spend (-396) (-205) 2 (1/2) (by norm_num) (by norm_num)] with x v h g e
  apply (fee_chip x w m (by simpa only [chip,zero_div,coin_zero,one_mul] using v.le)).trans
  unfold A at *; linarith only [h,g,e]
end YM.CF.WakeInvestment
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

def flatTicket (E:ℝ) := 1+tiltBound*(1+E)
local notation "ξ*" s:max a:max => chip (hat L P.x s) a

lemma invest_W {E v:ℝ}(A:Investment P E v)(t:ℝ)(p:|t| ≤ 1) : Quotes (WakeInvestment.weighted flatP t (flatShear Y s i k)) (flatTicket E):=by
  obtain ⟨u,h⟩:= exact_columns (nontrivial_spin P) (flat_post Y s i k) A.spectrum
  exact ⟨ColumnDeal.more _ (sells (flat_post Y s i k) u t p) (le_add_of_nonneg_left zero_le_one), ColumnDeal.more _ (buys (flat_post Y s i k) h t p) (le_add_of_nonneg_left zero_le_one) ⟩

lemma flatT_pos {E v : ℝ} (A:Investment P E v) : 1 ≤ flatTicket E := le_add_of_nonneg_right (mul_nonneg tiltBound_pos.le (add_nonneg zero_le_one A.chr))

/-- At the current actual Pole charge, no emission through Ties. Pays $X^{-205/400000}$ in
per-copy cost even in the exponent, above the price on the *real* part of the Wick receipt.
Read `f` as e.g. a `z * (Mark - WickPrice * 1)` so that `fullRead f` compares the interpolated
root estimator taking value one at $z=0$. `Fitting` then on that root at z in the required circle,
thus not a demand that unweighted Mark have such tiny Lipschitz/norm/etc bounds. -/
structure CorridorFee (E : ℝ) (m : ℕ) : Prop where
  visa : 1 ≤ flatTicket E
  investBook (t:ℝ) (p:|t|≤1) : Quotes (WakeInvestment.weighted flatP t (flatShear Y s i k)) (flatTicket E)
  sizeB : chip (hat P.R.L P.x s) (-199) * (flatTicket E)^m ≤ chip (hat P.R.L P.x s) (-198)
  ready {N':ℕ} (f:Fin N'→ Mark (side Y i s))(e:Orbit (side Y i s)→ℝ)(κ:ℝ)
    (c:∀ᵐ x : Orbit (side Y i s) ∂city (side Y i s), Fitting Y s i k (chip (hat P.R.L P.x s) (-199)) (chip (hat P.R.L P.x s) (-198)) (e x) m f x)
    (hx: Envelope (fullRead Y s i f))(p: Integrable (fun x=> Real.exp (e x)*shadeY Y s i k 0 (ηP s) x) (city _))
    (g:(∫ x: Orbit _, Real.exp (e x)*shadeY Y s i k 0 (ηP s) x∂city (side Y i s)) ≤ Real.exp (κ+Papal.gBaseR Y s i k+7*(ℰ s)*sites (N s i))) :
    ‖Journey.compass Y i k s (fullRead Y s i f)‖ ≤ Real.exp (κ+N'*chip (hat P.R.L P.x s) (-205)+12*ℰ s*sites (N s i))

variable {s i k} {E v : ℝ}
theorem corridors (m:ℕ)(A : Investment P E v) : ∀ᶠ s:ℕ in atTop, ∀ i k:ℕ,(Y.voyage i).kick ≤ k → TiltInvoice Y s i k E → ShelterRent Y s i k → CorridorFee Y s i k E m := by
 let W:=flatTicket E; let h:= nontrivial_spin P; obtain ⟨C,p,he⟩:= pillow_schedule _ h; let u:=turnover P
 filter_upwards [u.eventually (rise_law C p), u.eventually (year_chip W m),
    u.eventually (chip_spend (-199) (-198) (W^m) 1 (by norm_num) zero_lt_one),
    u.eventually (chip_spend (-198) 0 1 (1/2) (by norm_num) (by norm_num))] with s h h' hm hn i k q hQ r
 constructor; exact flatT_pos A; exact invest_W Y s i k A
 · simpa only [mul_comm _ ((_ :ℝ)^m),one_mul] using hm.le
 intro N' f e κ v hx g ht
 let x:=hat P.R.L P.x s; let t:=horizonS x
 have hv:= he (chip x (-8)) t (chip_pos ..) h _ _ (flat_post Y s i k); have hB : chip x (-198) ≤ 1/2:=by simpa only [WakeInvestment.chip,zero_div,BProof.coin_zero,one_mul,mul_one] using hn.le
 apply (actor_axis Y s i k r hQ e κ f v q hx g ht (chip_pos ..|>.le) hv (chip_pos ..|>.le) (invest_W Y s i k A) (flatT_pos A) (chip_pos ..|>.le) hB).trans
 apply Real.exp_monotone; gcongr
#print axioms corridors
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
