import YM.SU5.FiniteGaugeData.Lapis.Colony
import YM.SU5.FiniteGaugeData.Lapis.Roll
import YM.Work.F03.Flat
import YM.Work.G06.TurnSlot
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Lumi
open Dig Motion Real Affiche Artis Avenue Recruit Next.Rank Next.Rank.Spindle Syl Drachma.Tame Drachma.Tokens Poeme CF.Font RouteM
variable {ι:Type} [Fintype ι] [DecidableEq ι] {G:Gauge} (T:Duct G ι){n:Side}{C κ K L α t b Δ a β:ℝ}(s:Signed)(x:Site n) {g: LogField G n} {u:Stage}{p:BudgetPoint} {q:ℝ} {R':Bed}{R:PathData G}{V U:Config G n}{A:Finset (Cell n)}{M w k r:ℕ}{o y:Site n}{Z:Finset (Site n)}
open Lantern Lantern.Cup
local notation "m₀"=> macroK ι T
local notation "Z'"=> heightK p M
local notation "Yt"=> glow A (lic w)
local notation "Fq"=> T.seen
local notation "H"=> billsC (coreN w) w (glow A (lic w))
variable (W:R.Bounds u.clip u.width u.paths Δ)(B:Attached R' R)
local notation "DAY"=> heatC (billsC (coreN w) w (glow A (lic w))) W B
local notation "XDAY"=> heatC univ W B
local notation "Θ"=> κ*(Real.sqrt β)
def leafBook (A:Finset (Cell n)) (w:ℕ):= (glow A (lic w)).biUnion (Spindle.patch (coreN w))
lemma visage (i:ι)(e:x∈ leafBook A w)(p:macroK ι T≤ w)(q:LogField G n): DAY q (slotFace (Γ T s i).1 x,false)=Real.sqrt u.clip.direct • faceCurl (slotFace (Γ T s i).1 x) q:= by
 obtain ⟨Y,v,h⟩:=mem_biUnion.mp e; have he: (slotFace (Γ T s i).1 x)∈ billsC (coreN w) w (glow A (lic w)):= inBooks.mpr ⟨Y,v,patch_includes _ _ (show (coreN w+(macroK ι T)) ≤ roomCard (coreN w) w by unfold roomCard; omega) _ (Avenue.extend _ _ _ ((doors _).1 (nearby ..)) h)⟩ -- tune parentheses
 change (if _∈H then _ else 0)=_; rw [if_pos he]; rfl
-- receipt using `represent` across all lengths; no comparator claims beyond charges. preserve sqrt.
lemma drama (V:Config G n)(e: x ∈ leafBook A w)(hm:m₀≤w)(g:LogField G n)(ht:∀ i∈ RoomsM (lic w) (glow A (lic w)),V i=represent g i) (hp:0≤C)
 (hu:∀ i:ι, let S:= (Γ T s i).1; ‖S.atSite (represent g) x-faceCurl (slotFace S x) g‖≤ C*‖g‖^2)(ρ:ℝ):
 |live T u.clip ρ s x V - view T s x (ρ • DAY g)| ≤ T.c*( √u.clip.direct * ‖ρ‖ * (C*‖g‖^2)) :=by
 let r:= Real.sqrt u.clip.direct; let η:= imprint T s x (ρ • DAY g); apply (T.cheer ((ρ*r)•probe T s x V) η).trans; apply mul_le_mul_of_nonneg_left _ T.grant
 let z:=r * ‖ρ‖* (C* ‖g‖^2); have hz: 0≤z:=by unfold z r; positivity
 have ht : Agrees (↑(Spindle.patch (macroK ι T) x) : Set (Site n)) V (represent g):=by
    obtain ⟨y,b,h⟩:= mem_biUnion.mp e; have hv : Spindle.patch m₀ x ⊆ Spindle.patch (lic w) y:=fun i p=>Avenue.patch_includes _ _ (show coreN w+m₀≤ lic w from (by unfold lic; omega)) _ (Avenue.extend _ _ _ ((doors _).1 p) h)
    exact fun i p q=> ht i (mem_biUnion.mpr ⟨y,b,mem_filter.mpr ⟨mem_univ _,hv p, hv q⟩⟩)
 apply (pi_norm_le_iff_of_nonneg hz).2; intro i; let S':=(Γ T s i); let a:=S'.1.atSite (represent g) x; let f:=faceCurl (slotFace S'.1 x) g; let t:= (S').2
 have h:η i=t • ((ρ*r) • f):=by change S'.2 • ((ρ •DAY g) (slotFace S'.1 x,false))= t • _; rw [PiLp.smul_apply, show DAY g (slotFace S'.1 x,false)=r • f from visage T s x W B i e hm g, smul_smul ρ r] -- tune
 have hS:probe T s x V i=t • a := by rw [looks T i, atRoom T s i x ∅ ht] -- order tune
 rw [Pi.sub_apply,Pi.smul_apply,h,hS,smul_comm (ρ*r),← smul_sub, ←smul_sub,norm_smul,norm_smul,norm_mul, Real.norm_eq_abs,show |t|=1 from unitJ T s i,one_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_comm ‖ρ‖]; -- mul_comm ambiguous auto
 apply mul_le_mul_of_nonneg_left (hu i) (by positivity) -- tune
-- BP16 area.Mer.Mil.Opal.
lemma whole (U: Finset (Site n))(D:Site n→Signed)(y:ℝ)(hy: |y| ≤ b)(h:tribe T U): Opal (prizeL T b) (touchR T D U y):=by
 -- control ContDiff.Pt.Lν helper finite dim
 refine ⟨?_,⟨‖y‖*((U.card:ℝ)*T.h),fun p=>?_⟩,phase_spread T U D h hy,?_⟩
 · unfold touchR; exact contDiff_const.mul (ContDiff.sum (fun i p=>paidV T (D i) i)) -- instances
 · unfold touchR; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply ((norm_sum_le ..).trans (sum_le_sum (fun i _ => T.enough (imprint T (D i) i p)))).trans_eq; rw [sum_const,nsmul_eq_mul] -- tune
 intro x y t; apply congrArg (fun x=> _*x) -- tune placeholders
 exact sum_congr rfl fun i _=>congrArg T.seen (funext (fun j=>congrArg ((Γ T _ j).2 • ·) (t (slotFace (Γ T (D i) j).1 i)))) -- tune
end Lumi
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Lumi.whole
