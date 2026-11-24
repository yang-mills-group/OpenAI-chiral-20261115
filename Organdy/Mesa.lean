import Organdy.Policy
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
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
/-! # Sparse projection resulting state & compass; holder price use ANY such solid mover at this height below purchase. -/

open Regis Lamour.Bridge Organdy Organdy.Optic
namespace Bazaar
open Larva (Chip Domaine dint)

open Papal Celeste Clock Hookah Rake Cliplet
local notation "θx" s:max=>hat P.R.L P.x s
local notation "N" s:max i:max=> (Journey.side Y i s)
local notation "ℰ" s:max=> meterC (θx s)
set_option linter.unusedVariables false
set_option maxRecDepth 4000
namespace Tablewalk
variable (P)

local notation "LL" => P.R.L.val
local notation "wh" s:max=>webX (θx s)
lemma liftCount {x LLx:ℝ}(h:1<LLx)(p:1 ≤ x):
    ∃ k:ℕ, x ≤ LLx^k ∧ LLx^k ≤ x*LLx:=by
 have hx:∃ k:ℕ,x  ≤  LLx^k:=((tendsto_pow_atTop_atTop_of_one_lt h).eventually_ge_atTop x).exists
 refine ⟨Nat.find hx, Nat.find_spec hx,?_⟩
 generalize e:Nat.find hx=k
 cases k
 · exact (pow_zero _).trans_le (one_le_mul_of_one_le_of_one_le p h.le)
 next n=>
     rw [pow_succ]
     have z:= Nat.find_min hx (show n<Nat.find hx by omega)
     exact mul_le_mul_of_nonneg_right (le_of_not_ge z) (zero_le_one.trans h.le)

lemma legal : 1<(LL:ℝ):=by
 by_contra! w
 have e:(LL:ℝ)=1:=le_antisymm w (by exact_mod_cast P.R.L.property)
 obtain ⟨n,u⟩:=((turnover P).eventually_gt_atTop P.x).exists
 unfold Vale.hat Vale.billX at u
 simp [e] at u

lemma diminish:Tendsto (fun s=> (θx s)/(LL:ℝ)^s) atTop (𝓝 0):=by
 have p:= ((tendsto_pow_const_div_const_pow_of_one_lt 0 (legal P)).const_mul P.x).add
   ((tendsto_pow_const_div_const_pow_of_one_lt 1 (legal P)).mul_const (Vale.billX P.R.L))
 rw [mul_zero,zero_mul,add_zero] at p
 unfold Vale.hat
 simpa [mul_one,add_div,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,mul_add] using p

lemma backhaul (h:ℕ):
  ∀ᶠ s in atTop,(wh s)^100*(LL:ℝ)^ (h+1)  ≤  (LL:ℝ)^s:=by
   let c:ℝ:=(LL:ℝ)^ (h+1)
   have y:=Pays.leap (Pays.scale c (whole 0 100 0)) (w:=1) (p:=0) (q:=0) (by norm_num [Worth.Earlier])
   have e:0<(LL:ℝ):=zero_lt_one.trans (legal P)
   filter_upwards [
      (turnover P).eventually y,
      (turnover P).eventually_gt_atTop 0,
      (diminish P).eventually (ge_mem_nhds zero_lt_one)] with s j g k
   apply (le_trans _ ((div_le_one (pow_pos e s)).mp k))
   rw [web_pow,mul_comm]
   exact j.trans_eq (by simpa using BProof.coinY g)

local notation "bw" s:max=>radiusB (θx s)
local notation "B"=>P.block.val
-- macro width
abbrev ruler(s:ℕ):= (1+bw s)^4
lemma sidewalk :
    ∀ᶠ s in atTop,
      ((16 * B * LL^2 * ruler P s:ℕ):ℝ)  ≤  wh s:=by
   let c:ℝ:=16* B*(LL:ℝ)^2
   have p:=Pays.scale c (pot (plus (merit (constant 1) (w:=0) (p:=0) (q:=2) (by norm_num [Worth.Earlier])) rising) 4)

   filter_upwards [(turnover P).eventually (Pays.leap p (w:=0) (p:=1) (q:=0) (by norm_num [Worth.Earlier]))] with s v
   unfold ruler
   simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
   exact v

variable (H:Real.exp 1 ≤ P.x)
include H in
lemma ruler_mono {s u:ℕ}(p:u ≤ s):ruler P u ≤ ruler P s:=by
  have p':1<θx u:=(Real.one_lt_exp_iff.mpr zero_lt_one).trans_le (H.trans (Vale.crown P.R.L P.x u))
  have y: (θx u) ≤ θx s := by unfold Vale.hat; have h:=Vale.pitch P.R.L; gcongr
  have g:= Real.log_nonneg p'.le
  unfold ruler radiusB
  gcongr


-- d aligned to two widths W_l
def hike (s l j:ℕ):ℕ:= 2*(LL^(s-l)*(16*B*LL^j))
include H
lemma now (k:ℕ) :
  ∀ᶠ s in atTop, ∃ l j:ℕ,k ≤ l ∧ l ≤ s ∧
       (wh s)^100  ≤  (LL:ℝ)^(s-l) ∧ (LL:ℝ)^(s-l)  ≤  (wh s)^100*LL ∧
       ruler P l  ≤  LL^j ∧ LL^j  ≤  ruler P l * LL ∧
       (wh s)^99  ≤  distanceP (hike P s l j) ∧ distanceP (hike P s l j)  ≤  (wh s)^101 ∧
       reach (θx s) (hike P s l j):=by
 filter_upwards [backhaul P k, sidewalk P, (turnover P).eventually (aisleWide 1)] with s b g t
 let w:=wh s
 have f:1 ≤ w:= t.gw
 have h:=legal P
 obtain ⟨n,p,z⟩:=liftCount h (show 1 ≤ w^100 from one_le_pow₀ f)
 have q:n+k ≤ s:=by
    by_contra! j
    have y:(LL:ℝ)^s < (LL:ℝ)^(n+k):=pow_lt_pow_right₀ h j
    have i:=mul_le_mul_of_nonneg_right z (pow_nonneg (zero_le_one.trans h.le) k)
    rw [←pow_add,mul_assoc,←pow_succ'] at i
    exact y.not_ge (i.trans b)

 let l:=s-n; have u:l ≤ s:=by omega
 have e:s-l=n:=by omega
 have ew:1 ≤ ruler P l:=by unfold ruler; exact Nat.succ_le_iff.mpr (by positivity)
 obtain ⟨j,pj,qj⟩:=liftCount h (show 1 ≤ (ruler P l:ℝ) by exact_mod_cast ew)
 have a:ruler P l ≤  LL^j:=Nat.cast_le (α:=ℝ)|>.mp (by rw [Nat.cast_pow LL j];exact pj)
 have d: LL^j  ≤  ruler P l * LL:= Nat.cast_le (α:=ℝ)|>.mp (by rw [Nat.cast_pow,Nat.cast_mul];exact qj)

 have he: distanceP (hike P s l j) = (LL:ℝ)^n * (16*((P.block.val:ℕ):ℝ)*(LL:ℝ)^j) :=by
    rw [hike,e,distanceP,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow]
    norm_num
 have low: w^99  ≤  distanceP (hike P s l j):=by
    have ge: 1 ≤ (P.block.val:ℝ):=by exact_mod_cast P.block.property
    rw [he]
    exact (((pow_le_pow_right₀ f (show (99:ℕ) ≤ 100 by decide)).trans p).trans
     (le_mul_of_one_le_right (by positivity)
       (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) ge)
         (one_le_pow₀ h.le))))

 have y: (LL:ℝ)*(16* (P.block.val:ℝ)*(LL:ℝ)^j) ≤ w:=by
   rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow] at g
   have z:LL^j ≤ ruler P s*LL:=d.trans (Nat.mul_le_mul_right _ (ruler_mono P H u))
   have e':(LL:ℝ)^j ≤ ruler P s* (LL:ℝ):=by exact_mod_cast z
   apply le_trans _ g
   apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e' (by positivity: (0:ℝ)  ≤  16*B)) (zero_le_one.trans h.le))
   exact le_of_eq (by ring)
 have high : distanceP (hike P s l j)  ≤  w^101:=by
    rw [he]
    exact (mul_le_mul_of_nonneg_right z (by positivity)).trans ((mul_assoc ..).le.trans
      ((mul_le_mul_of_nonneg_left y (pow_nonneg (zero_le_one.trans f) _)).trans_eq (pow_succ w 100).symm))
 rw [←e] at p z
 exact ⟨l,j,by omega,u,p,z,a,d,low,high,(half_le_self (by positivity)).trans low,high.trans (le_mul_of_one_le_left (by positivity) (by norm_num))⟩
