import YM.SU5.LitCurrent.Candle
import YM.SU5.LoomForce.Arise
import YM.SU5.LoomForce.AbsenceA
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
namespace LoomForce
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP
     Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
     InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Papal Lamour.Bridge Celeste Exterior SpinReceipt Yoke Jewel EmberWind Hiro Onyx
open Regis.Head Regis.Head.Brecht Regis.Circuit
open YM.Stationary (Gaia)

variable (P : Spine) {s i k n : ℕ}
local notation "Λ" => P.par
local notation "Γ" => P.run
namespace Sundial
open LitCurrent LitCurrent.Surplus
open Pressure Worth Worth.Pays BProof
open Next.Rank.Spindle
-- physical-in-microscope timelike here. choose x at 0 (wrapped to every n).
local notation "Ξ"=>takenVolume P
local notation "Υ"=>takenCutoff P
open ProbabilityTheory MeasureTheory
variable {φ : ℕ→ℕ}{β : ℕ→ℝ}(C:Pooling P.run (takenVolume P) (takenCutoff P) φ β)
variable (A:ℝ)(u:0<A)
local notation "X" s:max=> hat (Λ).R.L (Λ).x s
local notation "U" s:max => sPow Λ s A
local notation "Pp" s:max => radiusB (X s)
local notation "Γσ" s:max=> Sheds (Pp s)

-- budget footprint estimates for BOTH; actual Kappa; Shadow in future, whole aperture also tag
local notation "G_" s:max=> shadowR P A s
local notation "Y"=> P.run
local notation "Φ" R:max b:max N:max=> readingFob b R (0:Site N)
local notation "Kα"=> P.calibration
local notation "τ"=> Sheds
open LitCurrent LitCurrent.Surplus
open CF.Pannier.Chancel Rous Scree Papal Salt
variable (s:ℕ)
def debit (A:ℝ)(s:ℕ):ℕ:= 20+creditJ+radiusB (hat P.par.R.L P.par.x s)+2*(shadowR P A s).natAbs
abbrev vision (N:Side):= node (0:Site N)
lemma fundsDebit (N:Side) : debit P A s ≥ 12+Pp s + creditJ + separation (vision N) (sendSite (-(G_ s)) (vision N)):= by
 let T:= shadowR P A s; have h:= shadow_pos P A s; let Z:= vision N; let x:= nodeC (0:Cover); let u:= shadowShift (-T) x
 have he:u∈skyDeck x (2*T.natAbs+2):=by
   apply (pav_v ..).mpr; intro i; unfold u shadowShift; by_cases hp:i=3
   · subst i; have h:0<T:=h; simp [fling_move,x,nodeC,abs_of_pos h]; omega
   simp [Ne.symm hp,fling_move]; positivity
 have hx:Z=wrap (More N) x:= by simpa only [map_zero] using Lifted.node_of N (0:Cover)
 have ht:sendSite (-T) Z=wrap (More N) u:=hx ▸ send_pay _ _ _
 have hz: separation Z (sendSite (-T) Z) ≤ 2*T.natAbs+2:= blocks_test.mp (show sendSite (-T) Z∈ BlockP _ Z from by unfold BlockP; rw [ht,hx,←wrap_pav]; exact mem_image_of_mem _ he)
 unfold debit; change _+2*T.natAbs ≥ _+separation Z (sendSite (-T) Z); omega
abbrev litRegion (s':ℕ):= skyDeck (nodeC 0) (24*radiusB (hat P.par.R.L P.par.x s')+12)
include u
lemma debit_cal : ∀ᶠ s in atTop, (↑(debit P A s):ℝ)≤ sPow Λ s (A+1) ∧ SlabMark.Between Kα 3 (-(G_ s)) (G_ s) (litRegion P s):=by
 let V(s:ℕ):=Pp s; let G(s:ℕ):= (G_ s); let R(s:ℕ):=U s
 let b:ℝ:= 2*(ruler P.par.block:ℝ)+20+creditJ; let L:ℕ:=(Kα).ℓ
 let h':=Pays.plus (Pays.plus (Pays.whole 0 A 0) (merit Pays.rising (b:=0) (q:=0) (Or.inr (Or.inl ⟨rfl,u⟩)))) (merit (constant b) (Or.inr (Or.inl ⟨rfl,u⟩)))
 have hm:= radius_down P A u 48 (2*(13+(L:ℝ))) |>.eventually (ge_mem_nhds (zero_lt_one))
 filter_upwards [hm,(turnover Λ).eventually (leap (w:=0) (p:=A+1) (q:=0) h' (Or.inr (Or.inl ⟨rfl,by linarith⟩)))] with s b' h₂
 obtain ⟨p,q⟩:=shadow_pay P A s; have hs:= (G s).natCast_natAbs; rw [abs_of_pos (shadow_pos P A s)] at hs; have ht: (↑(G s).natAbs:ℝ)=(G s:ℝ):=by rw [←Int.cast_natCast (R:=ℝ),hs]
 refine ⟨le_trans ?_ h₂, fun i hx=>?_⟩
 · unfold debit; push_cast; change _+_+(Pp s:ℝ)+2*((G s).natAbs:ℝ)≤ R s+(Pp s:ℝ)+b; rw [ht]; unfold b G R; linarith only [q]
 have hv: 24*V s+13+L≤(G s).natAbs:=by
    apply Nat.cast_le (α:=ℝ)|>.mp
    have hp:= (div_le_one (show 0 < R s from BProof.coin_pos ..)).mp b'; push_cast; rw [ht]; change _ ≤ 2*(G s:ℝ) at p; unfold V G R at *; linarith only [hp,p]
 have hl:= (pav_v ..).1 hx 3; simp only [nodeC,smul_zero,zero_add,Pi.one_apply] at hl -- not var h from LitRegion
 unfold V G L at *; omega
#print axioms debit_cal
-- rent qualifiers others
omit u
variable {r:ℕ}{t:ℝ}{w:ℕ}
local notation "N_" s:max n:max=> matterSide P s n
local notation "Ω_" s:max n:max=> RootBook P.run (Ξ n) (Υ n) s
local notation "K_" s:max n:max=> ((Y).voyage (Ξ n)).CapeT s -- issue notation capture
-- resolution after applying occupancy coupon
local notation "AΓ" g:max s:max=> sPow Λ s g
local notation "αΓ" s:max => sPow Λ s A
variable {a b d v:ℝ} (p: MaskPoint P.run r s (takenVolume P n) (takenCutoff P n) a b)
    (E:StampMark P r s (takenVolume P n) (takenCutoff P n) a v)
local notation "θΓ" s:max n:max=> (Ω_ s n).p
local notation "kα" s:max n:max=> (Ω_ s n).p.B/10 -- precedence
abbrev stageFace (A:ℝ)(β:ℕ→ℝ)(j:Bool):= LitCurrent.Surplus.mark j ((P.run.voyage (takenVolume P n)).CapeT s) (RootBook P.run (takenVolume P n) (takenCutoff P n) s).p ((RootBook P.run (takenVolume P n) (takenCutoff P n) s).p.B/10) (-(shadowR P A s)) E ((sPow P.par s A)^4) (κFix β s) 0
include p
lemma futures (β:ℕ→ℝ) : let R:=-(shadowR P A s); let X':=stageFace P s E A β
    let N:= matterSide P s n
    AtSupport false ((litRegion P s).image (wrap (More N))) (X' false) ∧ AtSupport false ((reflectedBox 3 R (litRegion P s)).image (wrap (More N))) (X' true) ∧ X' true=reflMark 3 R (X' false)∧ (∀ i,covariant (X' i)) :=by
 intro R X' N
 let Q:= nodeC (0:Cover); let S:=θΓ s n; let k:= (Ω_ s n).p.B/10; let K:=(P.run.voyage (Ξ n)).CapeT s; let w:= κFix β s; let U_:= αΓ s ^ 4; let C':ℂ:= ((U_*w^2:ℝ):ℂ); let X₀:= inspectFoot S (0:Site N)
 have hp:S.B=Pp s:=p.B0; have ht:X' false=C' • gaugeSeed K S k 0 E:= funext fun i=>(mul_smul ..)
 have he:X' true=reflMark 3 R (X' false):=by funext V; change auditTax R true _ _ _ _ _ _ E _ • _= _; unfold X' reflMark stageFace LitCurrent.Surplus.mark auditTax; rw [theta_smul,theta_one,star_mul']; congr 1; rw [show star C'=C' from Complex.conj_ofReal _,tax_real _ p.C]; rfl
 let T:= (litRegion P s).image (wrap (More N)); have hT: AtSupport false T (X' false):=by
    apply AtSupport.mono (S:=X₀) ?_ ?_ -- name
    · exact ht ▸ (gauge_support K S _ _ E p.C).smulM _
    unfold T litRegion; rw [wrap_pav, ← show node (0:Site N)=wrap (More N) (nodeC 0) from by simpa only [map_zero] using node_of N (0:Cover)]
    intro i h; obtain ⟨j,g,v⟩:=halo_spec.mp (Next.Rank.Thirst.inspect _ h); obtain ⟨t,x,y⟩:=halo_spec.mp g; rw [mem_singleton.mp x] at y; refine halo_spec.mpr ⟨node 0,mem_singleton_self _,(separation_triangle _ j _).trans ?_⟩; rw [hp] at y; omega
 refine ⟨hT,?_,he,fun j=>(genuineStamp (Pp s) R 0 p.C E (fundsDebit P A s N) (αΓ s ^4) w p.B0 j).2⟩ -- infer or explicit
 rw [he,reflectedBox,image_image]; have ht':(wrap _ ∘ (plane 3 R).motion)=(plane 3 R).anon N ∘ wrap (More N):= funext fun i=> (Shape.anno ..).symm; rw [ht',←image_image]
 exact hT.refl 3 R
#print axioms futures
omit p
lemma pairedAhead (J:ℕ→ℕ) (t:StrictMono J) (r:ℕ) : ∀ᶠ n in atTop,
 Ferry P.run s (takenVolume P (J n)) (takenCutoff P (J n)) ∧
   s<P.run.uv (takenCutoff P (J n)) ∧ 4*r+40<(matterSide P s (J n)).val ∧2*(r+1)<(More (matterSide P s (J n))).val :=by
 filter_upwards [((P.run.uv_grows.comp (P.law.pick.grow_k.comp P.history.growsB)).tendsto_atTop.comp t.tendsto_atTop).eventually_gt_atTop s,
    t.tendsto_atTop.eventually (P.history.finance s), (matterSide_grows P s|>.comp t.tendsto_atTop).eventually_ge_atTop (⟨4*r+41,by omega⟩:Side)] with n v x z
 let N:= N_ s (J n); change 4*r+41 ≤ N.val at z; exact ⟨x,v,by change 4*r+40 <N.val; omega,by change _ < N.val*2; omega⟩
#print axioms pairedAhead
end Sundial
end LoomForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
