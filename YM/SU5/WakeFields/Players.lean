import YM.SU5.WindTorque.Issuance
--# precursor used by our mixed geometry checkpoint already (Geometry...)
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 2500
noncomputable section
namespace YM.CF.Buffered.EmberWind
open Finset Function Filter NormedSpace SU Lat Lattice Cube MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
        ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch
        Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
open Ballad Hiro
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel
open WakeInvestment

namespace MixedCards

-- all stamps; choose q current (1/16 * raw) or mixed V staff at same spin W.spin
abbrev Ticket := Option Lead.Clan

variable (U V : Staff) (τ : Ticket) (n : Side)
open EmberWind.Staff

def matter (L : Staff) (U : Lead.Clan) : Weaver :=
  (1/16 : ℂ) • SitSpin.raw L.u U L.spin.1 L.spin.2

-- all AtSupport, Cov semantics on n

def play (c : ColorL) : FC (Single n) := match τ with
 | none => wrapCurrent U.u U.spin 1 n c
 | some t => matter U t n (1,1)

def actor (ρ : ℝ) (r : ℕ) (t : ℝ) : Weaver := match τ with
 | none => U.rungWeave ρ r t
 | some q => matter U q

lemma shift_play (ρ : ℝ) (r : ℕ) (t : ℝ) (X : Fields n) : actor U τ ρ r t n X = play U τ n (U.pearl ρ n r t X.1) := by
  cases τ; exact Staff.onMark ..; rfl

open CF.Lamour.Bridge CF.Lamour.Bridge.Celeste

lemma matter_voice (U : Staff) (b : Lead.Clan) : Voice (matter U b) {U.xo} := (SitSpin.voice ..).hushed _

lemma axle (ρ : ℝ) (r : ℕ) (t : ℝ) : covariant (actor U τ ρ r t n) := by
  cases τ with | none => exact oneVox U ρ r t _ | some => exact (matter_voice U _).2 n

lemma global_play (g : SU.E) (c : ColorL) :
    play U τ n (SU.group.adjoint g c) = twist (quantU (tradew n (fun _ => g))) (play U τ n c) := by
  cases τ
  · unfold play
    rw [←hold_apply _ _ _ _ (simultaneous (fun _=>g) (1,1)),←hold_apply _ _ _ c (1,1)]
    exact current_cov U.u U.spin 1 c _ (fun _ => g)
  rename_i b
  let V : Seat n → SU.E := fun _=>g
  let X : Fields n := (1,1)
  have he : matter U b n (simultaneous V X) = matter U b n X := rfl
  exact he.symm.trans ((matter_voice U b).2 n V X)

variable {n}
-- Cadre on region S

lemma ready (t : Lead.Clan) {S : Support (More n)} (h : U.scope n ∈ S) (c : Fields n) :
    Cadre (modesIn n S) 2 (Fintype.card SU.Slot) (matter U t n c) := by
  let a := SitSpin.raw U.u t U.spin.1 U.spin.2
  have he : dBook n {U.xo} ⊆ S := by exact image_singleton (f:=⇑(wrap (More n))) (a:=U.xo) |>.le |>.trans (singleton_subset_iff.mpr h)
  have p : ‖(1/16:ℂ)‖≤1 := by norm_num
  exact ((((SitSpin.cadre t U.u n U.spin.1 U.spin.2 c).scale (1/16)).buy le_rfl
                (by exact mul_le_of_le_one_left (Nat.cast_nonneg _) p)).cover (modes_monotone he))

def topFare := max (max 1 Staff.regiment) (Fintype.card SU.Slot)
lemma atFare : 1 ≤ topFare := (le_max_left ..).trans (le_max_left ..)
lemma fare_nn : 0 ≤ topFare := zero_le_one.trans atFare

variable {K : ℝ} (g : 1 ≤ K)
include g in
lemma play_color {S : Support (More n)} (h : U.scope n ∈ S) (c : ColorL) (hf : ‖c‖ ≤ K) :
    Cadre (modesIn n S) 2 (topFare * K) (play U τ n c) := by
  cases τ with
  | some t => exact (ready U t h _).buy le_rfl ((le_max_right ..).trans (le_mul_of_one_le_right fare_nn g))
  | none => exact (spin_at U.u U.spin c n S h).buy le_rfl (mul_le_mul ((le_max_right ..).trans (le_max_left ..)) hf (norm_nonneg _) fare_nn)

lemma play_change {S : Support (More n)} (h : U.scope n ∈ S) {c c' : ColorL} {ε : ℝ} (v : ‖c-c'‖≤ε) :
    Cadre (modesIn n S) 2 (topFare * ε) (play U τ n c - play U τ n c') := by
  cases τ with
  | some t =>
    rw [play,play,sub_self]; exact ((Cadre.zero _).buy le_rfl (mul_nonneg fare_nn ((norm_nonneg _).trans v)))
  | none =>
    unfold play; rw [←map_sub]; exact (spin_at U.u U.spin (c-c') n S h).buy le_rfl
                      (mul_le_mul ((le_max_right ..).trans (le_max_left ..)) v (norm_nonneg _) fare_nn)

variable {J : Type*} (A : J → Staff) (D : J → Ticket) (L : List J)
variable (ρ : ℝ) (r : ℕ) (t : ℝ) (c : J → ColorL)

def concert : Weaver := (L.map fun i => actor (A i) (D i) ρ r t).prod

def judged (n : Side) (c : J → ColorL) : FC (Single n) := (L.map fun i => play (A i) (D i) n (c i)).prod

lemma concert_eq (U : Fields n) : concert A D L ρ r t n U = judged A D L n (fun i => (A i).pearl ρ n r t U.1) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    let B := fun j => (A j).pearl ρ n r t U.1
    change actor (A i) (D i) ρ r t n U * concert A D L ρ r t n U = _ * judged A D L n B
    rw [ih,shift_play]

lemma judges (g : SU.E) (c : J → ColorL) (n : Side) :
    judged A D L n (fun i => SU.group.adjoint g (c i)) =
        twist (quantU (tradew n (fun _ => g))) (judged A D L n c) := by
  induction L with
  | nil => exact (map_one _).symm
  | cons i L ih =>
    let T := twist (quantU (tradew n (fun _ => g))); let C := fun i => SU.group.adjoint g (c i)
    change play (A i) (D i) n (SU.group.adjoint g (c i)) * judged A D L n C = T (play (A i) (D i) n (c i) * judged A D L n c)
    rw [map_mul]; exact congrArg₂ (·*·) (global_play _ _ _ _ _) ih

variable {S : Support (More n)} (h : ∀ i, (A i).scope n ∈ S)
include g h
variable (n)
lemma judged_color (h' : ∀ i, ‖c i‖≤K) : Cadre (modesIn n S) (2*L.length) ((topFare * K)^L.length) (judged A D L n c) := by
  induction L with
  | nil =>
    rw [List.length_nil,mul_zero,pow_zero]; exact Cadre.unit
  | cons i L ih =>
    rw [List.length_cons,Nat.mul_succ,Nat.add_comm,pow_succ']; exact (play_color _ _ g (h i) _ (h' i)).and_ ih

lemma judged_change (h' : ∀ i, ‖c i‖≤K) (c' : J → ColorL) (hc' : ∀ i, ‖c' i‖≤K)
    {ε : ℝ} (v : ∀ i, ‖c i - c' i‖ ≤ ε) (he : 0 ≤ ε) :
    Cadre (modesIn n S) (2*L.length) (L.length * (topFare*K)^L.length * ε) (judged A D L n c-judged A D L n c') := by
  have HP := (mul_nonneg fare_nn (zero_le_one.trans g))
  induction L with
  | nil => simp only [judged, List.length_nil,List.map_nil,List.prod_nil,sub_self,mul_zero,Nat.cast_zero,zero_mul]
           exact Cadre.zero _
  | cons i L ih =>
    let y := judged A D L n c; let y' := judged A D L n c'
    let x := play (A i) (D i) n (c i); let x' := play (A i) (D i) n (c' i)
    have R := play_color _ (D i) g (h i) _ (hc' i); let P' := topFare*K
    have X := (play_change _ (D i) (h i) (v i)).buy le_rfl (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right fare_nn g) he)
    rw [show judged A D (i :: L) n c - judged A D (i :: L) n c'=(x-x')*y+x'*(y-y') from (by change x*y-x'*y'= _; rw [_root_.sub_mul,mul_sub]; abel), List.length_cons,Nat.mul_succ,Nat.add_comm]
    exact ((X.and_ (judged_color n g A D L c h h')).add (R.and_ ih)).buy le_rfl (le_of_eq (by rw [pow_succ',Nat.cast_add,Nat.cast_one]; ring))

omit g h
variable [Fintype J]
abbrev materialL (J : Type*) := J × SU.group.ColorIndex -- use abbrev

lemma smoothLayer : ContDiff ℝ 1 (play U τ n) := by
  unfold play; cases τ with
  | none => exact (wrapCurrent U.u U.spin 1 n).toContinuousLinearMap.contDiff
  | some h => exact contDiff_const

lemma smoothA : ContDiff ℝ 1 (judged A D L n) := by
  induction L with
  | nil => exact contDiff_const
  | cons i L ih =>
    let x := play (A i) (D i) n; let y := judged A D L n
    change ContDiff ℝ 1 (fun c => x (c i)*y c)
    exact ((smoothLayer _ _ _).comp (show ContDiff ℝ 1 (fun c : J → ColorL => c i) from by fun_prop)).mul ih

omit [Fintype J] in
lemma broadVenue (Q : Calibration) (m : Side) (v : n = Q.c m) {e w : ℕ} (o : Seat n)
    (p : ∀ i, (A i).Pays r w) (h : ∀ i, (A i).tenancy n r Staff.clearance e o) :
    AtSupport false (BlockP e o) (concert A D L ρ r t n) := by
  have F (i) (b : Ticket) : AtSupport false (BlockP e o) (actor (A i) b ρ r t n) := by
    cases b with
    | none => exact Py.Rate.LocalLimit.Preparation.Yoke.Jewel.deckVenue _ _ (p i) _ Q _ v (h i)
    | some b =>
      refine ((matter_voice (A i) b).1.bounded n).mono ?_
      let U := A i
      have hh := (p i).withinP (A i) n
      have hz : U.scope n ∈ BlockP e o := h i (Corona.halo_mono (show r ≤ r+Staff.clearance+8 by omega) (Subset.refl _) hh.2.1)
      exact image_singleton (f:=⇑(wrap (More n))) (a:=U.xo) |>.le |>.trans (singleton_subset_iff.mpr hz)
  induction L with
  | nil => exact AtSupport.oneM _
  | cons i L ih => exact (F i (D i)).mulM ih

omit [Fintype J] in
lemma covariant_concert : covariant (concert A D L ρ r t n) := by
  induction L with
  | nil => intro g x; exact (map_one _).symm
  | cons i L ih =>
    intro g x; change actor (A i) (D i) ρ r t n (simultaneous g x)*concert A D L ρ r t n (simultaneous g x)= (twist (quantU (tradew n g))) (actor (A i) (D i) ρ r t n x * concert A D L ρ r t n x)
    rw [map_mul,axle _ _ n,ih]
#print axioms global_play
#print axioms judged_change
#print axioms broadVenue
end MixedCards
end YM.CF.Buffered.EmberWind
