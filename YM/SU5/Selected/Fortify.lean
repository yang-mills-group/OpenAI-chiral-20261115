import VerifiedSatinGroundInteraction
/-! # Reflect a Perron pair before the many-copy estimate
Unlike the single-read estimate, start also with a reflected pair (at
pose selected on the observing lattice with room) to pay for a square
upper bound. This new consultation will need pricing (increasing height)
before nominating the government. Uses the one election; do not attempt
splitting the pair product into factors without proof. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 30000
set_option maxHeartbeats 250000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra

namespace Cliplet.StageTw
variable {K : Calibration} {m n : Side} {B : ℕ} {ν : Mark n → ℂ}
  {M : Tulip.Male} {R : ℝ} {j k w d t : ℕ} {γ τ : ℝ}

-- variant of Trefl used twice
private lemma lengthPick {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega

lemma stratum (h : StageTw K ν j R d M)
    (g:n=K.c m) (v:B+addgap K≤ n.val) (A:List (Cliplet n k))
    (f:Flight j M w d t γ τ A)(a:1≤A.length)(b:A.length≤2)
    (p:∀ i,cows i (whereV A) B) :
    ∃ (Z:ℕ) (U:List (Cliplet n k)), Flight j M w d t γ τ U ∧
      U.length=Z*A.length ∧ 0<Z ∧ U.length ≤ (More n).val^4 ∧
      (More n).val^4 ≤ Z*(4*(B+addgap K))^4 ∧ ‖ν (probe A)‖^Z≤ ‖ν (probe U)‖:=by
  obtain ⟨X,q,r⟩:= lengthPick (x:=n.val) (show 0< B+addgap K from Nat.add_pos_right _ addgap_pos) v
  obtain ⟨U,f',H,t'⟩:= h.scatter g q univ A f (fun i _=>p i)
  rw [show (univ:Finset Axis).card=4 from by simp [Axis]] at H t'
  refine ⟨_,U,f',H,by positivity,?_,?_,t'⟩
  · rw [H]
    have hr:2^X ≤ n.val:= q.trans' (Nat.le_mul_of_pos_right (2^X) (Nat.add_pos_right _ (show 0<addgap K from addgap_pos)))
    apply le_trans (Nat.mul_le_mul (Nat.pow_le_pow_left hr 4) b)
    change n.val^4*2 ≤ (n.val*2)^4
    rw [mul_pow]; omega
  rw [← mul_pow]; apply pow_le_pow_left'
  change n.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 r); exact le_of_eq (by ring)
end Cliplet.StageTw
-- reflected union placement
open Afterglow.Satin Lifted
section geometry
variable {n:Side} (d q w J:ℕ)(a:Axis)
-- `B≥1`, choose one fermion origin with room by J gauge units (can be addgap).
-- origin depends on resolution-independent budget. For all periods.
def scheduled (B J:ℕ) : Cover := fun _ => ((B+J:ℕ):ℤ)
def breadth (B J:ℕ) := 10*(2*B+J)
local notation "B₀" => payout d q w

lemma senSize (B J:ℕ){x:Cover}(h:x∈ Sen (scheduled B J) B) (a:Axis):
    (J:ℤ) ≤ x a ∧ x a ≤ (4*((B:ℤ)+J)+2):=by
  obtain ⟨y,e,rfl⟩:= mem_image.mp h
  have h₁:= (box_test.mp e).1 a; have h₂:= (box_test.mp e).2 a
  change _≤ y a+nodeC (scheduled B J) a∧ y a+nodeC (scheduled B J) a ≤_
  unfold nodeC scheduled; simp only [Pi.add_apply,Pi.one_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply]; omega
-- sharpen upper to 3B+ etc
lemma length_sen {a:Axis} (B J:ℕ) (he:0 < B) {x:Cover}(h:x∈Sen (scheduled B J) B): x a ≤ (8*B+3*J:ℕ) :=by
  obtain ⟨y,u,rfl⟩:= mem_image.mp h
  have hv:=(box_test.mp u).2 a
  change y a+nodeC (scheduled B J) a ≤ _
  unfold nodeC scheduled; simp only [Pi.add_apply,Pi.one_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply]; omega
-- Eventually positive time
open Py Py.Rate LocalLimit Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ P.x)(s:ℕ)(B:ℕ)
local notation "K"=>tent Y H
local notation "O"=>scheduled B (addgap (tent Y H))
local notation "S₀"=> Sen O B
lemma placement : Tapestry.Ledge P l (S₀) a 0:= by
  intro x hx; have hr:= (senSize _ _ hx a).1
  let J:=addgap K; change _ ≤ x a; unfold addgap stepgap at hr -- oops also at O inside h
  change ((2*(reserve P l+4*_):ℕ):ℤ) ≤ x a at hr
  omega
lemma shelfF : ∀ᶠ i in atTop, Islet (Papal.count Y s i) O B ⊆ band (Papal.count Y s i) a 0 (tent Y H).ℓ := by
  filter_upwards [Tapestry.eventuallyFits Y H (Sen O B) s a 0 (placement a Y H B)] with i h
  rw [sen_islet (n:=Papal.count Y s i)]; exact h
-- shifted union inside width breadth
lemma cows_s (B J:ℕ) (e:0< B) (a i:Axis) :
    cows i (hyphen a 0 (Islet n (scheduled B J) B) ∪ Islet n (scheduled B J) B) (breadth B J) := by
  let W:=8*B+3*J; unfold breadth
  refine ⟨-(W:ℤ),fun z hz=>?_⟩
  rw [sen_islet (n:=n)] at hz -- tune same occurrences
  rcases mem_union.mp hz with p | p
  · obtain ⟨x,h₀,rfl⟩:= mem_image.mp p; obtain ⟨x,g,rfl⟩:= mem_image.mp h₀
    let r:Cover:= (plane a 0).motion x
    refine ⟨r i,?_,?_,?_⟩
    · unfold r W; have hx:= senSize B J g i; have hl:= length_sen (a:=i) B J e g; rw [fling_move]; split <;> omega
    · unfold r W; have hx:= senSize B J g i; have hl:= length_sen (a:=i) B J e g; rw [fling_move]; split <;> omega
    rw [Shape.anno]; rfl
  obtain ⟨x,u,rfl⟩:=mem_image.mp p
  refine ⟨x i,?_,?_,rfl⟩
  · have h:=(senSize _ _ u i).1; unfold W; omega
  have h:=length_sen (a:=i) B J e u; unfold W; omega
end geometry
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.cows_s
#print axioms YM.CF.Pannier.Chancel.Cliplet.StageTw.stratum
