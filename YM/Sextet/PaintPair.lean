import YM.Sextet.ScentMirror
/-!
# Terms of Eq. `eq:fullscr` used in six-family transport

Single price and centering. Pair power-normalizations, product identification, somatic
budgets. These keep the termwise presentation of the mark before `M` or `Θ` pricing.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open PhaseChoice (handstamp circum)
variable (P:Spine) (K:P.Register) (A B:P.Apron) (t:ℕ) (f g:Vantage→ℝ)
local notation "h₄" => (((P.macroTick t)^4:ℝ):ℂ)
local notation "h₈" => (((P.macroTick t)^8:ℝ):ℂ)
local notation "pts" => P.grid t

section Single
variable (x:P.Spectrum0 3)
local notation "Θ" => P.spirits K 3 x

lemma paint_set (hf:HasCompactSupport f) (a:A.s≤t) :
    Θ (P.paintPoly A t f)= ((P.macroTick t)^4*(∑ᶠ q:Cover, f (pts q)):ℝ) • P.singleState 3 A.s x A.F := by
  have u:support (f ∘ pts) ⊆ ↑(P.fineSites t hf) := fun _ h=>P.fine_mem_of t hf h
  have Z:=finsum_eq_sum_of_support_subset _ u
  conv_rhs=>
    lhs
    rhs
    change ∑ᶠ q,(f ∘ pts) q
    rw [Z]
  rw [show Θ (P.paintPoly A t f)=P.singleState 3 t x (P.paintMark A t f) from P.oneCup ..,
      paintMark,P.fine_sum t hf,map_smul,map_sum]
  simp [P.selected_aim 3 x _ t a, Complex.real_smul,Finset.sum_mul,mul_assoc]

theorem paint_mass (hf:HasCompactSupport f) (p:Continuous f) :
    Tendsto (fun i=> Θ (P.paintPoly A i f)) atTop
      (𝓝 ((∫ y,f y) • P.singleState 3 A.s x A.F)) := by
  have e: Tendsto (fun i=> (P.macroTick i)^4*(∑ᶠ q:Cover, f (P.grid i q))) atTop
       (𝓝 (∫ y,f y)) := by
    refine (YM.Sextet.Quadrature.ages p hf (P.macroTick_pos) P.macroTick_null).congr fun i=>?_ 
    simp_rw [P.grid_node];rfl
  refine (e.smul_const _).congr' ?_
  filter_upwards [eventually_ge_atTop A.s] with i hi using (P.paint_set K A i f x hf hi).symm

theorem paint_order_one (hf:HasCompactSupport f) (p:Continuous f) (J:P.Ellis 3 x) :
    Tendsto (fun i=> Θ (P.paintPoly A i f)) atTop
      (𝓝 (∫ y, (f y:ℂ)*P.commonWell 3 x (fun _:Unit=>A) (fun _=>y) [()])) := by
  simp_rw [P.singleton_price x J];rw [integral_mul_const,integral_complex_ofReal]
  rw [← Complex.real_smul]
  exact P.paint_mass K A f x hf p

theorem paint_zero (s n:ℕ) (Z:Lead.Clan) (h:s ≤ t) (hf: HasCompactSupport f) :
    Θ (P.paintPoly (P.macroBody Z s n) t f)=0 := by
  have b:=P.one_point 3 x Z h n 0
  rw [P.selected_aim 3 x _ t h] at b
  rw [P.paint_set K _ t f x hf h,b,smul_zero]

theorem paint_zero_opposed (s n:ℕ) (Z:Lead.Clan) (j:Axis) (h:s ≤ t) (hf: HasCompactSupport f) :
    Θ (P.paintPoly ((P.macroBody Z s n).kiss P j) t f)=0 := by
  have b:=P.one_point_mirror 3 x j Z h n 0
  rw [P.selected_aim 3 x _ t h] at b
  rw [P.paint_set K _ t f x hf h,b,smul_zero]
end Single

section Expansion

def markPair := P.paintMark A t f * P.paintMark B t g
def paintPair := P.paintPoly A t f * P.paintPoly B t g

lemma pin_paintPair : P.paintPair A B t f g=
    Altitude.pinhole _ t (P.markPair A B t f g) :=
  (map_mul (Altitude.pinhole ..) _ _).symm

lemma scrollPair (p q:Cover) : P.fullScroll t (usher A B) (usher p q) [false,true]=
    P.aimMark A t p*P.aimMark B t q := by
  rw [fullScroll,List.map_cons,List.map_cons,List.map_nil,List.prod_cons,List.prod_cons,List.prod_nil,mul_one]
  rfl

/-- Eq. `eq:fullscr`, pair version used in both conclusions. Sums range over independent
positions, already arrived on opposed or unopposed probes as appropriate **at height t**.
Finite set version charges all posed products meeting the two compact support qualifications,
with weight zero permitted. Mesh normalization power 8 in that same unit as widths. -/
lemma markPair_charges (h:HasCompactSupport f) (k:HasCompactSupport g) :
    P.markPair A B t f g=h₈ • ∑ p∈P.fineSites t h, ∑ q∈P.fineSites t k,
      ((f (pts p):ℂ)*(g (pts q):ℂ)) • P.fullScroll t (usher A B) (usher p q) [false,true] := by
  unfold markPair paintMark
  rw [P.fine_sum t h,P.fine_sum t k,smul_mul_assoc,_root_.mul_smul_comm,smul_smul]
  congr 1
  · push_cast;ring
  rw [sum_mul]
  simp only [mul_sum,smul_mul_assoc,_root_.mul_smul_comm,smul_smul,scrollPair]
  simp only [mul_comm (_:ℂ)]

theorem paint_fullscr (h:HasCompactSupport f) (k:HasCompactSupport g) :
    P.paintPair A B t f g=Altitude.pinhole _ t (h₈ • ∑ᶠ pq:Cover × Cover,
      (((f (pts pq.1)*g (pts pq.2):ℝ)):ℂ) •
         P.fullScroll t (usher A B) (usher pq.1 pq.2) [false,true]) := by
  simp_rw [Complex.ofReal_mul]
  rw [P.pin_paintPair,P.markPair_charges A B t f g h k,
    finsum_eq_sum_of_support_subset _ (s:=(P.fineSites t h) ×ˢ (P.fineSites t k)) (by
       simp only [support_subset_iff, Finset.mem_coe,Finset.mem_product]
       intro pq p
       have a:f (pts pq.1)≠0:= fun e=>p (by simp [e])
       have b:g (pts pq.2)≠0:= fun e=>p (by simp [e])
       exact ⟨P.fine_mem_of t h a,P.fine_mem_of t k b⟩), sum_product _ _]

lemma read_markPair (h:HasCompactSupport f) (k:HasCompactSupport g) (T:P.Test →ₗ[ℂ] ℂ) :
    T (P.markPair A B t f g)=h₈ * ∑ p∈P.fineSites t h, ∑ q∈P.fineSites t k,
      ((f (pts p):ℂ)*(g (pts q):ℂ)) * T (P.aimMark A t p*P.aimMark B t q) := by
  rw [P.markPair_charges A B t f g h k]
  simp only [map_smul,map_sum,P.scrollPair,smul_eq_mul]

theorem blocked_paint (h:HasCompactSupport f) (k:HasCompactSupport g)
    (T:P.Test →ₗ[ℂ] ℂ) (u:∀ p q, pts p∈tsupport f→pts q∈tsupport g→
       T (P.aimMark A t p * P.aimMark B t q)=0) :
    T (P.markPair A B t f g)=0 := by
  rw [P.read_markPair A B t f g h k T,
    sum_eq_zero (fun p hp=>sum_eq_zero fun q hq=> by
       rw [u p q ((P.fine_mem t h _).mp hp) ((P.fine_mem t k _).mp hq),mul_zero]),mul_zero]

lemma paintPair_ask (a j:Axis) (x:P.Spectrum0 a) :
    P.spirits K a x (P.paintPair A B t f g)=
      P.singleState j t (P.advocate a x j) (P.markPair A B t f g) := by
  rw [P.pin_paintPair,P.center_fuse a x K j]

lemma paintPair_here (x:P.Spectrum0 3) :
    P.spirits K 3 x (P.paintPair A B t f g)=P.singleState 3 t x (P.markPair A B t f g) := by
  rw [P.pin_paintPair]; exact P.oneCup ..
end Expansion

section Qualifications
variable (h:HasCompactSupport f) (k:HasCompactSupport g) (s:A.s≤t) (v:B.s≤t)
include h k

theorem markPair_enclave : P.markPair A B t f g∈enclave P.calibration :=
  Subalgebra.mul_mem _ (P.paint_singlet A t f h) (P.paint_singlet B t g k)

theorem turn_paintPair (j:Axis) :
    P.corePlane.oppose P.par j P.calibration (P.paintPair A B t f g)=
      P.paintPair (A.kiss P j) (B.kiss P j) t (turnSmear j f) (turnSmear j g) := by
  unfold paintPair
  rw [Sunlight.opposeMany,P.oppose_poly A j t f h,P.oppose_poly B j t g k]

theorem shift_paintPair (p:Cover) :
    P.walkList t p ordinate (P.paintPair A B t f g)=
      P.paintPair A B t (shiftSmear (pts p) f) (shiftSmear (pts p) g) := by
  unfold paintPair; rw [map_mul,P.shift_poly A t f p h,P.shift_poly B t g p k]

lemma shift_paint_read (a:Axis) (x:P.Spectrum0 a) (p:Cover) :
    P.spirits K a x (P.paintPair A B t (shiftSmear (pts p) f) (shiftSmear (pts p) g))=
      P.spirits K a x (P.paintPair A B t f g) := by
  rw [P.paintPair_ask K _ _ _ _ _ _ 3,P.paintPair_ask K _ _ _ _ _ _ 3]
  unfold markPair
  rw [←P.shift_paint A t _ p h,←P.shift_paint B t _ p k,←map_mul]
  exact P.selected_cruise ..

local notation "V" => P.poseLayer A f∪P.poseLayer B g
include s v K
lemma markPair_location :
    P.markPair A B t f g∈keep P.par P.width t P.calibration true (handstamp (V)) :=
  Subalgebra.mul_mem _ (P.paint_support A t f K s h Set.subset_union_left)
      (P.paint_support B t g K v k Set.subset_union_right)
theorem paintPair_well :
    P.paintPair A B t f g∈circum P.par P.width P.calibration true (V) {t} :=
  Subalgebra.mul_mem _ (P.paint_well A t f K s h Set.subset_union_left)
    (P.paint_well B t g K v k Set.subset_union_right)
end Qualifications
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
