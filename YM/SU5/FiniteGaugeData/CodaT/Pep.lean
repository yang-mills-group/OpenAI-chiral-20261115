import YM.SU5.FiniteGaugeData.CodaT.Print
import YM.SU5.FiniteGaugeData.Eight.Diameter
import YM.SU5.FiniteGaugeData.Hierarchy.Zone
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
abbrev projectF (A:Sourced N) :Mark N:= fun X=> dg (A X.1)
/-- Behaves well even on small support overlapping, price uniform. -/
structure Desire (K:Calibration) (S:Finset Cover) where
 paid: W K
 at_site: Locator K paid S
 fits: S.Nonempty
 print(N:Side): Sourced N
 ticket(m:Side): paid.val m= projectF (print (K.c m))
 col(m:Side)(u:Pane m): Cellar (modesIn m (region S m)) (print m u)
 nil(m:Side)(u:Pane m): print m u* print m u=0
 basso(m:Side)(u:Pane m): Matrix.trace (print m u)=0
 gauge(m:Side)(g:Mosquito m)(u:Pane m): print m (gauge g u)= twist (tradew m g) (print m u)
 owed:ℝ
 hv:0 < owed
 price(m:Side)(U:Pane m): ‖print m U‖≤ owed
 melt(ε:ℝ)(_h:0<ε): ∃ s:ℝ,0<s ∧∀ (N:Side)(U:Pane N),fieldR (region S N) s U→ ‖print N U-print N 1‖ ≤ ε
 off: IsNilpotent paid
lemma seatCard (S:Finset Cover)(N:Side): (modesIn N (region S N)).card ≤ S.card* Fintype.card (SpinIdx×SU.Slot):= by
 let T:=region S N; let W:=modesIn N T; let J(i:W): T×SpinIdx×SU.Slot:=(⟨node i.val.1.1,(modes_at ..).mp i.property⟩,i.val.1.2,i.val.2)
 change W.card ≤ _; apply le_trans (b:= T.card*_); swap; · exact Nat.mul_le_mul_right _ card_image_le -- tune meta
 rw [← Fintype.card_coe W,←Fintype.card_coe T, ←Fintype.card_prod]; apply Fintype.card_le_of_injective J; intro i j v; exact Subtype.ext (Prod.ext (Prod.ext (needle (congrArg (fun i:T×SpinIdx×SU.Slot=> i.1.val) v)) (congrArg (fun i=>i.2.1) v)) (congrArg (fun i=> i.2.2) v))
variable (A:Desire K S)
def radiusN (S:Finset Cover): ℕ:= S.sup fun x=> univ.sup fun i:Axis=> (x i).natAbs
lemma cover_box(i:Axis)(p:Cover)(s:p∈ S): |p i| ≤ (radiusN S:ℤ):=by
 let x:=p i; change |x| ≤ _; rw [←Int.natCast_natAbs]; exact_mod_cast ((le_sup (f:=fun i:Axis=>(p i).natAbs) (mem_univ i)).trans (le_sup (f:=fun x:Cover=> univ.sup fun i:Axis=>(x i).natAbs) s)) -- tune
abbrev spreadN (S:Finset Cover):=2*radiusN S
lemma spread_film (i:Axis) : film (-(radiusN S:ℤ)) (spreadN S) S i:=by
 intro x p; have hp:= abs_le.mp (cover_box i x p); unfold spreadN; omega
lemma spread_region (N:Side)(S:Finset Cover): radiusE (region S N) (spreadN S):=by
 let T:= wrap (More N); intro i u j v; obtain ⟨x,p,rfl⟩:=mem_image.mp u; obtain ⟨y,q,rfl⟩:=mem_image.mp v; change separation (T x) (T y) ≤ _
 have h(i): (-(spreadN S:ℤ))≤ x i-y i ∧ x i-y i≤ spreadN S:=by
    have hp:= spread_film i x p; have hq:= spread_film i y q; omega
 rw [separation,←map_sub]; apply Work.E01.pdist_wrap_le; rw [box_test]; exact ⟨fun i=>(h i).1,fun i=>(h i).2⟩
abbrev calibrationH (S:Finset Cover)(c:ℝ):ℝ:=((S.card * Fintype.card (SpinIdx×SU.Slot):ℕ):ℝ)*(1+c)
lemma calib_pos (S:Finset Cover)(hc:0≤ c): 0≤calibrationH S c:=by unfold calibrationH; positivity
namespace Desire
abbrev slope(K:Calibration)(A:Desire K S)(j:ℕ)(N:Side)(M:Male):= Relief.cup (Dial.tickA N) (Dial.spar j M (1:Pane N)) (A.print N 1)
include A
local notation "k_"=> calibrationH S c
variable {ζ:ℂ}
lemma pay (p:Fable G Q)(P:pointM (Single N) Q G c)(hc:0≤c) (W:Pane N): ‖Relief.cup Q G (A.print N W)‖ ≤ calibrationH S c*A.owed:=by
 refine (cardPay p.tender P _ (A.col N W).leftP).trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (seatCard S N)) (add_nonneg zero_le_one hc)) (A.price ..) (norm_nonneg _) (calib_pos S hc))
lemma stitch (p:Fable G Q)(P:pointM (Single N) Q G c)(hc:0≤c) {U:Pane N}(hx:‖A.print N U - A.print N 1‖≤r) : ‖Relief.cup Q G (A.print N U)- Relief.cup Q G (A.print N 1)‖ ≤ calibrationH S c*r:=by
 rw [←cup_sub]; let T:=cutM (modesIn N (region S N)); have ht:T*(A.print N U-A.print N 1)=A.print N U-A.print N 1:= by rw [mul_sub, show T*A.print N U=_ from (A.col N U).leftP,(A.col N 1).leftP];
 exact (cardPay p.tender P _ ht).trans (mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (seatCard S N)) (add_nonneg zero_le_one hc)) hx (norm_nonneg _) (calib_pos S hc))
variable (p:Fable G Q) (P:pointM (Single N) Q G c) (hc:0≤c) (hr:0 < r)
 (hx:∀ U:Pane N,fieldR (region S N) t U → ‖A.print N U-A.print N 1‖ ≤ r)
abbrev bend(G Q:Op (Single N))(z:ℂ):ℝ:= (z*Relief.cup Q G (A.print N 1)).re
variable (hr':‖ζ‖≤r)
include p P hc hr hx hr'
def icicle : Picture G Q (spreadN S) t (r*A.owed) (k_*r^2) (A.bend G Q ζ) (2*r*k_*A.owed) where
 F:= ζ • A.print N
 S:=region S N
 nonemptyP:= A.fits.image (wrap (More N))
 geography:=spread_region N S
 g g U:=by rw [Pi.smul_apply,A.gauge,Pi.smul_apply,twist_scalar]
 cellar X:=⟨by rw [Pi.smul_apply,Matrix.mul_smul,(A.col ..).leftP], by rw [Pi.smul_apply,Matrix.smul_mul,(A.col ..).rightP]⟩
 nilQ X:=by rw [Pi.smul_apply,Matrix.smul_mul,Matrix.mul_smul,A.nil,smul_zero,smul_zero]
 traceF X:=by rw [Pi.smul_apply,Matrix.trace_smul,A.basso,smul_zero]
 metric X:=by rw [Pi.smul_apply, norm_smul]; exact mul_le_mul hr' (A.price ..) (norm_nonneg _) hr.le
 rough X:=by
    have he(U:Pane N): |(Relief.cup Q G (ζ • A.print N U)).re| ≤ r*(calibrationH S c*A.owed) :=by
       rw [cup_smul]; exact (Complex.abs_re_le_norm _).trans ((norm_mul ..).trans_le (mul_le_mul hr' (A.pay p P hc U) (norm_nonneg _) hr.le))
    unfold bend; rw [ Pi.smul_apply, ←cup_smul]; linarith only [(abs_le.mp (he X)).2,(abs_le.mp (he 1)).1]
 soothing X z:=by
    have he:(Relief.cup Q G (ζ • A.print N X)).re - A.bend G Q ζ ≤ r*(calibrationH S c*r) :=by
       unfold bend; rw [cup_smul, ← Complex.sub_re]; exact (Complex.re_le_norm _).trans (by rw [← _root_.mul_sub,norm_mul]; exact mul_le_mul hr' (A.stitch p P hc (hx X z)) (norm_nonneg _) hr.le)
    rw [Pi.smul_apply]; linarith only [he]
end Desire
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
