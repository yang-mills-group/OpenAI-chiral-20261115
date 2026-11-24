import YM.SU5.Relativistic.Microscope
import YM.SU5.Selected.Apart

/-!
# The resolution-polynomial algebra as actual physical chiral probes

Interpret ALL local resolution polynomials, including multiple-height products
and ones paying output-link arguments. Keep one fixed support at any meeting
height, then upwards control to the microscopic horizon in any paid course
entry, whether or not the cover support wraps injectively yet. Eventually in
period, prove no issue of hosting that support either (EVEN as the cutoff and
hence its size grows at arbitrary rates relative to volume). At the microscopic
horizon even the ones with synthetic output-link dependence at effective scale
are gauge-input only. Full signed readings; not positive (could be complex).
Use both functions exact and actual. Then results in Φ come from a genuine
component-selection on precisely such readings.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function NormedSpace Filter Metric Lattice Cube Finset MeasureTheory RG Wilson
open Lat Mir Phase RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Scree Window Vale Girt Lifted
open Py Py.Rate LocalLimit Preparation Satin Heat Fock SlabMark PhaseChoice Push.SectorMeasure
open Tapestry Tapestry.Altitude Tapestry.Exhibition
open Journey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical InnerProductSpace
attribute [local instance] opCStarAlgebra

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l)) (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
local notation "L" => Λ.R.L.val
variable (s : ℕ) {a : Set ℕ} (i k : ℕ)
local notation "T" => Y.uv k
local notation "N" i:max n:max => side Y i n
local notation "μ" => Wilson.prior SU.group (More (side Y i (Y.uv k)))
local notation "q₀" x:max n:max i:max k:max=> attire (breathing Y H n i k x)
local notation "W₀" n:max S:max=> volumeAround Λ l n S
local notation "U₀"=> a∩Set.Iic s
local notation "A"=> Dome (tent Y H)
local notation "BPoly" => Altitude.Cloud (Dome (tent Y H))
variable {U : Set RSpace}
variable {wide : Bool}

/-- Physical containment visible in the height-s + support tariff. -/
lemma pocketEvery {x:Altitude.Cloud (Dome K)} (h:x∈ jetty Λ l K wide (handstamp U) (a∩ Set.Iic s)) :
    ∃ (S: BillOfWork) (r:ℝ), Pocket K S s r x ∧ ∀ k:ℕ, k ≤ s → SupportedPhysically Λ l k (S k) U:=by
  suffices hhp : ∃ S:BillOfWork, x∈ fountainHeads K S s ∧ ∀ k:ℕ,k ≤ s → SupportedPhysically Λ l k (S k) U by
    obtain ⟨S,w,g⟩:=hhp; obtain ⟨r,w⟩:=Tapestry.issued.mp w; exact ⟨S,r,w,g⟩
  apply boarded (P:={f|Officer (U₀) (fun i=> keep Λ l i K wide (handstamp U)) f}) (M:= fun x=>∃ S:BillOfWork, x∈ fountainHeads K S s ∧ ∀ k:ℕ,k ≤ s → SupportedPhysically Λ l k (S k) U) ?_ ?_ ?_ ?_ h
  · intro f (t : Officer _ _ f)
    choose S v using fun j=> (keeps Λ l j K wide (handstamp U)).mp (t.observes j)
    refine ⟨S, officer_stone (Set.Iic s) (fun i=>bay K (S i) true) ?_,fun i _=> (v i).2⟩
    refine ⟨t.toll,fun i=> widerBay K _ wide (v i).1,fun i u=> t.forbids i ?_⟩
    exact fun v=> u v.2
  · exact ⟨fun _ => ∅,(fountainHeads ..).zero_mem,fun i _ x hx => False.elim ((Finset.notMem_empty x) hx)⟩
  · rintro x y _ _ ⟨S,p,t⟩ ⟨W,u,w⟩; let E:BillOfWork:= fun i=> S i∪ W i
    exact ⟨E,(fountainHeads K E s).add_mem (coin_mono K S E s s (fun i _=> subset_union_left) le_rfl p) (coin_mono K W E s s (fun i _ => subset_union_right) le_rfl u), fun i v=> unionPrinted Λ l i _ _ (handstamp U) (t i v) (w i v)⟩
  rintro z x _ ⟨S,p,w⟩; exact ⟨S,(fountainHeads K S s).smul_mem p z,w⟩

lemma ascent_actual {x:Altitude.Cloud (Dome K)} (p:x∈shorter (Dome K) s) :
    attire (breathing Y H (s+1) i k x) = ascender Y s i k (attire (breathing Y H s i k x)):= by
  let D:=tidalDressing Y H i k
  have h : breathing Y H (s+1) i k x = Tapestry.music Y s i k (breathing Y H s i k x):=
    Decking.joins D s x (auxiliaryPad K) p
  rw [h,Tapestry.music,flowing]

lemma multi_extent {S:BillOfWork} {r:ℝ} {x: BPoly} (p:Pocket (tent Y H) S s r x) (n:ℕ)
    (q: Tapestry.Pay Y (s+n) i k) :
    AtSupport false (Satin.region (volumeAround Λ l n (frameBudget S Λ l s)) (side Y i (s+n))) (attire (breathing Y H (s+n) i k x)) := by
  induction n with
  | zero=> exact textureBudget Y H S s i k q x p
  | succ n ih=>
    have he: Tapestry.Pay Y (s+n+1) i k := (Nat.add_assoc ..).symm ▸ q
    have hv : Tapestry.Pay Y (s+n) i k :=⟨q.1,Nat.le_of_lt he.2⟩
    rw [← Nat.add_assoc s n,ascent_actual Y H (s+n) i k (climbs (Dome K) (by omega : s ≤ s+n) p.funded)]
    exact ascendSupport Y (s+n) i k _ he (ih hv)

lemma multi_reader {x: BPoly} (u:x∈ shorter (Dome K) s) (p:Tapestry.Pay Y s i k) :
    taking Y H i k x= microscope Y i k (attire (breathing Y H T i k x))/microscope Y i k 1:= by
  let Q:=Tapestry.breathing Y H (Y.uv k) i k x
  rw [taking_phys Y H T i k x ⟨p.1, le_rfl⟩ (climbs (Dome K) p.2 u)]
  change markedRead _ _ _ / _ = _
  rw [(onePrior Y i k (attire Q) (Ward.signs Q).env p.1).2,(same_denominator Y (Y.uv k) i k p.1 le_rfl).1]

/-- Package root localization for one `circum` polynomial. At budget entry with
paid height, every possible intermediate breathing has this certificate, even
at horizon T→∞ (cost not uniform in sup norm asserted). Thus literally computed
at the bare level inside the fixed physical footprint advertised. -/
lemma continuum_footprint {x:BPoly} (p:x∈ circum Λ l K wide U (a∩ Set.Iic s)) :
    ∃ S:Finset Cover, (∀ n:ℕ, SupportedPhysically Λ l (s+n) (volumeAround Λ l n S) U) ∧
      (∀ᶠ i : ℕ in atTop,Host Y H i s S) ∧
      ∀ (i k n : ℕ), Tapestry.Pay Y (s+n) i k → AtSupport false (Satin.region (volumeAround Λ l n S) (side Y i (s+n))) (attire (breathing Y H (s+n) i k x)) ∧
        covariant (attire (breathing Y H (s+n) i k x)) ∧
        taking Y H i k x= Journey.compass Y i k (s+n) (attire (breathing Y H (s+n) i k x)) ∧
        microscope Y i k 1 ≠ 0 ∧ taking Y H i k x=microscope Y i k (attire (breathing Y H (Y.uv k) i k x))/microscope Y i k 1:= by
  obtain ⟨S,r,t,g⟩:= pocketEvery Y H s ((well_spec ..).mp p).1
  have h := t.funded
  refine ⟨frameBudget S Λ l s,fun n=> SupportedPhysically.persists (Λ:=Λ) (l:=l) (S:=frameBudget S Λ l s) (frame_lines S s Λ l (V:=handstamp U) g) n, eventually_host Y H ..,?_⟩
  intro i k n q
  have hs:x∈shorter (Dome K) (s+n):= climbs (Dome K) (by omega : s ≤ s+n) h
  exact ⟨multi_extent Y H s i k t n q,paid_coherence Y H i k (s+n) q x p hs,
      taking_phys Y H (s+n) i k x q hs,(same_denominator Y (s+n) i k q.1 q.2).2,
      multi_reader Y H (s+n) i k hs q⟩

-- `pinhole` is used to read all Dome marks at any level. It *implements*
-- native train from there all the way up. Printed support matters here even
-- for identifying the family: `exhibit` casts across Side equalities.
lemma agrees_at_pin (x : A) (S:Finset Cover) (t:x∈bay K S true) (w:Host Y H i s S)
    (n : ℕ) (a:Tapestry.Pay Y (s+n) i k) :
    attire (breathing Y H (s+n) i k (Altitude.pinhole (Dome (tent Y H)) s x)) =
      distribute Y H (s+n) i (Tower.train Y H s n i k S x.val):=by
  let F:= Altitude.pinhole (Dome (tent Y H)) s x; let h := (Tapestry.locates ..).1 t
  induction n with
  | zero=>
     rw [Nat.add_zero,breathing,Decking.outcrop]
     change exhibit Y H s i x.val=distribute Y H s i x.val
     rw [present_send]
     rfl
  | succ n ih=>
    have he: Tapestry.Pay Y (s+n+1) i k := (Nat.add_assoc ..).symm ▸ a
    rw [← Nat.add_assoc s n,ascent_actual Y H (s+n) i k (climbs (Dome K) (by omega : s ≤ s+n) (short_pinhole s x)), ih ⟨he.1,Nat.le_of_lt he.2⟩]
    rw [train_step]
    exact (reserved Y H (s+n) (W₀ n S) i k he (Tower.prepared_train Y H s S n i k h) (by rw [Nat.add_assoc s n]; exact w.usable (n+1))).symm
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.continuum_footprint
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.agrees_at_pin
