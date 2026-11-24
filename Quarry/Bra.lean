import Quarry.Mark
import YM.CF.Buffered.StepIdentity

/-!
 # Replacing the (even) Y° operator at the actual bra under the insertion.
 Can use this even against an arbitrary ket and with disjoint spectators.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 700000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet
open Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Buffered
open StressExchange (preJ houseW)

variable {N : Side}
local notation "Ω" => Single N

theorem mill_house (x : Site N) : millQ x = houseW x := by
  rw [millSt]; unfold Tye.stock StressExchange.houseW
  apply congrArg Matrix.diagonal; funext i; simp [StressExchange.inhabit, Font.place_x, unaryN.eq_iff]

theorem square_inside (x : Site N) (m : ℕ) (l : List Axis) (S : Sa N)
    (H : halo (l.length*(6*m)) {node x} ⊆ S) : ClippedAt S (squareSum millQ m l x) := by
  induction l generalizing x with
  | nil =>
    have ht : node x∈S := H (halo_subset _ _ (mem_singleton.mpr rfl))
    change ClippedAt _ (millQ x); rw [mill_house]
    unfold ClippedAt
    ext i j
    rw [StressExchange.houseW,cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : i=j
    · subst i; by_cases z : j.1.1=x
      · have hz : j∈modesIn N S := (modes_at ..).2 (z.symm ▸ ht)
        simp [hz]
      simp [cutM, z, StressExchange.inhabit]
    simp [cutM,h]
  | cons i l ih =>
    unfold ClippedAt; rw [squareSum]; unfold stripSum
    rw [mul_sum, sum_mul]; apply sum_congr rfl; intro k v
    apply ih; intro y p
    obtain ⟨j, r, g⟩ := halo_spec.mp p
    refine H (halo_spec.mpr ⟨node x, mem_singleton_self _, (separation_triangle (node x) j y).trans ?_⟩)
    have hp : separation (node x) j ≤ 6*m := by
      rw [mem_singleton.mp r,Hove.ζdist]; have he := leap_strip x i m k (mem_range.mp v); omega
    rw [List.length_cons, Nat.add_mul]; omega

local notation "ν" => mateK N
local notation "A₀" => tickA N

lemma square_beam (x : Site N) (m : ℕ) (l : List Axis) : Commute A₀ (squareSum millQ m l x) := by
  induction l generalizing x with
  | nil =>
    change Commute A₀ (millQ x); rw [mill_house, touchP]
    unfold StressExchange.houseW Commute SemiconjBy cutM
    rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
    congr 1; ext i; exact mul_comm ..
  | cons i l ih =>
    unfold squareSum; unfold Commute SemiconjBy stripSum
    rw [mul_sum,sum_mul]; exact sum_congr rfl fun i _ => ih _

theorem bar_void (x : Site N) (m : ℕ) (i : Orbit N) : acts (star (barS0 N m x i)) ν=0 := by
  have hp : IsStarProjection A₀ := by rw [touchP]; exact cutM_idp _
  rw [barS0,star_sub, star_smul, star_one, act_sub, act_smul, act_one,
      StressExchange.sandwichV _ hp (square_beam x m _) ν (tickB N), sub_self]

def AtBra (P Q : FC Ω) := acts (star P) (mateK N)=acts (star Q) (mateK N)
namespace AtBra
variable {A B C D : FC (Single N)}
lemma plus_z (p : AtBra A C) (q : AtBra B D) : AtBra (A+B) (C+D) := by
  unfold AtBra at *; rw [star_add,star_add,act_add,act_add,p,q]
lemma sub_z (p : AtBra A C) (q : AtBra B D) : AtBra (A-B) (C-D) := by
  unfold AtBra at *; rw [star_sub,star_sub,act_sub,act_sub,p,q]
lemma sum_z {ι : Type*} (I : Finset ι)(F G : ι → FC Ω)(p : ∀ i ∈ I, AtBra (F i) (G i)) :
    AtBra (∑ i∈I, F i) (∑ i∈I, G i) := by
  induction I using Finset.induction_on with
  | empty => rw [sum_empty,sum_empty]; rfl
  | insert i I t h=> rw [sum_insert t,sum_insert t]; exact (p i (mem_insert_self ..)).plus_z (h fun j v => p j (mem_insert_of_mem v))
lemma scale_z (p : AtBra A C) (z : ℂ) : AtBra (z•A) (z•C) := by
  unfold AtBra at *; rw [star_smul,star_smul, act_smul,act_smul,p]
lemma trans_z (p : AtBra A B)(q : AtBra B C) : AtBra A C := Eq.trans p q
lemma symm_z (p : AtBra A B) : AtBra B A := Eq.symm p
lemma tail (p : AtBra A B) (T : FC Ω) : AtBra (A*T) (B*T) := by
  unfold AtBra at *; rw [star_mul,star_mul,act_mul,act_mul,p]
theorem read (p : AtBra A B) (q : Phys N) : Buffered.letterRead A q = Buffered.letterRead B q := by
  change inner ℂ ν (acts A q) = inner ℂ ν (acts B q); unfold AtBra at p
  rw [←act_inner,←act_inner,p]
end AtBra

variable (p : BudgetPoint) (K : Scree.Loom N) (o : Site N) (m : ℕ)
variable {X : SOp N} {a b t d : ℝ} {k q : ℕ} (P : Trunk (node o) X k a b d)
    (L : Roof N t d q K) (hp : p.threshold ≤ t) (hd : 0 < d) (size : k + q ≤ p.B)
local notation "σ" x:max => offsetMask p.B x
open Advance
local notation "draw" => drawn K


lemma preJ_zero : StressExchange.preJ (tickA N) 0 = 0 := by simp [StressExchange.preJ,Fock.dg,dyad]
include P L hp hd size
lemma topBra (x : Orbit N) : AtBra (topMark p K o X (draw x))
    (houseK p (σ o) (blazePlate K X - barS0 N m o) x) := by
  by_cases t : x∈pingMask p (σ o)
  · unfold houseK; rw [Set.indicator_of_mem t,Pi.sub_apply,blazePlate]
    have h : halo (k+q) {node o} ⊆ σ o := Corona.halo_mono size le_rfl
    change AtBra ((hatKernel p K _ _ x.1).trace • 1) _
    rw [hatKernel_pass P L hp hd h x t]
    unfold AtBra; rw [star_sub,act_sub,bar_void,sub_zero]
  change AtBra ((hatKernel p K _ _ x.1).trace • 1) _
  rw [hatKernel_closed x.1 t,Matrix.trace_zero,zero_smul, houseK, Set.indicator_of_notMem t]
  rfl
lemma bondBra (u : Orbit N) (x : Site N) : AtBra (bondMark p K o X x (draw u)) (coverLine K p o x X u) := by
  let Y := co_Ψ x o X
  change AtBra (preJ (tickA N) (hatKernel p K _ Y u.1)) _
  unfold coverLine houseK
  by_cases v : u ∈ pingMask p (σ x)
  · have hY := markArrival o P x; have h : halo (k+q) {node x} ⊆ σ x := Corona.halo_mono size le_rfl
    change Trunk _ Y _ _ _ _ at hY
    rw [Set.indicator_of_mem v, hatKernel_pass hY L hp hd h u v]
    exact (StressExchange.bra_eq _ (show IsStarProjection (tickA N) from (touchP N).symm ▸ cutM_idp _) ν (tickB N)).symm
  rw [Set.indicator_of_notMem v, hatKernel_closed u.1 v, preJ_zero]
  rfl

variable {J : Axis → SOp N} (δ : ∀ i, Trunk (node o) (J i) k a b d)
include δ
lemma wardBra (x : Orbit N) : AtBra (wardMark p K o m J X (draw x)) (puffLine K p o J X m x) := by
  refine AtBra.plus_z (topBra p K o m P L hp hd size x) ?_
  unfold highLine; rw [Finset.sum_apply, Finset.sum_apply]
  exact AtBra.sum_z _ _ _ (fun i _ => (bondBra p K o (δ i) L hp hd size x _).sub_z (bondBra p K o (δ i) L hp hd size x _))

variable (high : 6 ≤ p.B) (width : 4*m ≤ p.B)
omit P L hp hd size δ
-- y° stencil has extra non-grammar dΓ terms; allow them as
-- even charge operators **for comparison**. Establish genuine mode support before commuting.
lemma sectorSub' {S : Finset Ω} {A B : FC Ω} (p : Sector S false A) (q : Sector S false B) :
    Sector S false (A-B) := by
  rw [sub_eq_add_neg]
  exact p.add (neg_one_smul ℂ B ▸ (q.scale (-1)))
include width high P L hp hd size δ
lemma wardSector (y : Orbit N) : Sector (modesIn N (port p o)) false (puffLine K p o J X m y) := by
  refine Sector.add (P:=(houseK p (σ o) (blazePlate K X-barS0 N m o)) y) ?_ ?_
  · by_cases t : y ∈ pingMask p (σ o)
    · rw [houseK, Set.indicator_of_mem t, Pi.sub_apply]
      refine sectorSub' (Sector.one.scale _) (sectorSub' (pair_charge ?_) (Sector.one.scale _))
      exact square_inside o m _ _ (by simp only [port,List.length_ofFn]; apply Corona.halo_mono (by omega) le_rfl)
    rw [houseK, Set.indicator_of_notMem t]; exact Sector.zero _
  have he (i : Axis) (x : Site N) (g : separation o x ≤ m) :
      Sector (modesIn N (port p o)) false (coverLine K p o x (J i) y) := by
    unfold coverLine houseK
    by_cases w : y ∈ pingMask p (σ x)
    · rw [Set.indicator_of_mem w]
      apply pair_charge
      exact (markArrival o (δ i) x).modes L hd y ((Corona.halo_mono (show k ≤ p.B from by omega) le_rfl : halo k {node x}⊆σ x).trans ((within_inspect _).trans (portClear p o high (by omega) x g)))
    rw [Set.indicator_of_notMem w]; exact Sector.zero _
  change Sector _ _ (highLine _ _ _ _ _ y)
  unfold highLine; rw [Finset.sum_apply]; apply Sector.sumS; intro i _
  exact sectorSub' (he i _ (stopBeam o i m).1) (he i _ (stopBeam o i m).2)

variable (ha : 0 ≤ a)
omit P L hp hd high width size δ
lemma sectorComm {F G : FC Ω} {S T : Sa N} {β : Bool} (p : Sector (modesIn N S) false F)
    (e : Sector (modesIn N T) β G) (w : Disjoint S T) : Commute F G := by
  change _*_=_*_
  simpa [Sector.grainB] using p.apart e (show Disjoint (modesIn N S) (modesIn N T) from
      disjoint_left.mpr (fun i h => fun g => disjoint_left.mp w ((modes_at ..).1 h) ((modes_at ..).1 g)))
include P L hp hd ha high width size δ
lemma spectator {T : Sa N} (w : Disjoint (port p o) T) (y : Orbit N) {F : FC Ω}
    {β : Bool} (e : Sector (modesIn N T) β F) : AtBra (F * wardMark p K o m J X (draw y))
      (F * puffLine K p o J X m y) := by
  let H := wardStencil p K o P L hp hd size ha δ high (show m ≤ p.B by omega)
  let pV := sectorComm ((H.foot.allV (draw y)).sector) e w
  rw [←pV.eq, ←(sectorComm (wardSector p K o m P L hp hd size δ high width y) e w).eq]
  exact (wardBra p K o m P L hp hd size δ y).tail F

end YM.CF.Swell
