import VerifiedSatinGroundInteraction
import YM.SU5.FiniteGaugeData.Tower.RoomShape
/-! # Winemakers opposite. Start with a *fixed-plane* double on every observing torus
of the same election. Need high density, and uniformity in k.
Geometric extension of `Trefl.StageTw.trefoil`. -/

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Cliplet RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open Mir Phase RP Reflect Advance Nacre Window Vale Girt Lifted Scree
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m n:Side}{B l: ℕ}
-- only here. no assertions about an arbitrary Course

def grain (B:ℕ): Cover := fun _ => 2*(B:ℤ)

lemma bounds_Sen_grain {x : Cover} (p : x ∈ Sen (grain B) B) (i : Axis) : 3*(B:ℤ)+1 ≤ x i ∧ x i ≤ 5*(B:ℤ)+1 := by
 obtain ⟨y,g,rfl⟩:=mem_image.mp p
 change 3* _+1 ≤ y i + nodeC (grain B) i ∧ y i + nodeC (grain B) i ≤ _
 unfold nodeC grain
 simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply]
 simp only [nsmul_eq_mul,Nat.cast_ofNat]
 have hy:=box_test.mp g
 have h₁:=hy.1 i
 have h₂:=hy.2 i
 omega

open Tower -- Between?
lemma between_grain (p : addgap K ≤ B) (j : Axis) (x : ℤ) (e : 12* (B:ℤ) ≤ x) :
    SlabMark.Between K j 0 x (Sen (grain B) B) := by
 intro z hz; obtain ⟨u,v⟩:=bounds_Sen_grain hz j
 have h:= (show 0<addgap K from addgap_pos); unfold addgap stepgap at p h; omega

-- density including opposite sides: in the fixed band around origin
lemma cows_grain (p : 0<B)(j i : Axis) :
    cows i (hyphen j 0 (Islet n (grain B) B) ∪ Islet n (grain B) B) (12*B) := by
 rw [sen_islet]
 refine ⟨-(6*(B:ℤ)),?_⟩
 intro x hx
 rcases mem_union.mp hx with E|E
 · obtain ⟨y,h,rfl⟩:= mem_image.mp E; obtain ⟨z,g,rfl⟩ := mem_image.mp h
   let y:=wrap (More n) z; obtain ⟨u,v⟩:=bounds_Sen_grain g i
   change Chord _ _ (((plane j 0).anon n y) i)
   by_cases a:i=j
   · subst j
     have ht : ((plane i 0).anon n y) i-((0:ℤ):Per (More n))=-(y i-((0:ℤ):Per (More n))) := across_coord i 0 _
     simp only [Int.cast_zero,sub_zero] at ht
     exact ⟨-(z i),by omega,by omega,by rw [ht,Int.cast_neg]; rfl⟩
   rw [show (((plane j 0).anon n y) i) = y i from (by
      simp [plane,Shape.anon,affine,Signed.mirror,Signed.act,a,Ne.symm a])]; exact ⟨z i,by omega,by omega,rfl⟩
 obtain ⟨z,g,rfl⟩:=mem_image.mp E; obtain ⟨u,v⟩:=bounds_Sen_grain g i; exact ⟨z i,by omega,by omega,rfl⟩

namespace Cliplet
variable {ν:Mark n→ℂ}{M:Tulip.Male}{R:ℝ}{j k w d t:ℕ}{γ τ:ℝ}
variable (h:StageTw K ν j R d M)
namespace StageTw
-- copy powers-of-two lower from StageTw.goldilock
private lemma quarterChoose {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega

include h
lemma doubles (g:n=K.c m)(G:addgap K ≤ B) (v:12*B+addgap K≤ n.val) (i:Axis) (F:Cliplet n k)
    (f:Perron j M w d t γ τ F) (p:F.broad=Islet n (grain B) B) :
    ∃ (r:ℕ) (U: List (Cliplet n k)), Flight j M w d t γ τ U ∧ 0<r ∧ U.length= r*2 ∧ U.length ≤ (More n).val^4 ∧
       (More n).val^4 ≤ r*(4*(12*B+addgap K))^4 ∧ ‖ν (reflMark i 0 F.frame* F.frame)‖^r≤ ‖ν (probe U)‖:=by
 have G' := addgap_pos.trans_le G
 let A:= [F]; let T:=A.map fun a=> a.mirror i 0; let D:=T++A
 have ha: Flight j M w d t γ τ A:=Flight.alone f
 have he: whereV A=Islet n (grain B) B:=by simp [whereV,A,p]
 have ht: whereV D= hyphen i 0 (whereV A)∪ whereV A:=by unfold D T; rw [combine,Flight.reflect_consistent]
 have hp: whereV A⊆ band n i 0 K.ℓ:=by
   rw [he,sen_islet]; exact SlabMark.enters_arc K i (between_grain G i _ (by omega)) rfl
 have hf: Flight j M w d t γ τ D:= (ha.reflect i 0 (h.across i 0) h.hire).tack _ ha (by rw [Flight.reflect_consistent]; exact west K i 0 _ hp)
 obtain ⟨u,a,l⟩:= quarterChoose (x:=n.val) (y:=12*B+addgap K) (by omega) v
 obtain ⟨U,f',H,hY⟩:= h.scatter g a univ D hf (fun i b=>by rw [ht,he]; exact cows_grain G' _ _)
 have hw:(univ: Finset Axis).card=4:=by simp [Axis]
 let r:ℕ:= (2^u)^4
 have Hr:U.length=r*2:=by simpa [D,T,A,hw,r] using H
 refine ⟨r,U,f',by unfold r; positivity,Hr,?_,?_,?_⟩
 · change _ ≤ (n.val*2)^4; rw [Hr,mul_pow]; refine mul_le_mul' ?_ (by decide)
   exact pow_le_pow_left' (a.trans' (Nat.le_mul_of_pos_right (2^u) (by omega))) _
 · unfold r; rw [← mul_pow]; apply pow_le_pow_left'; change n.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
 rw [show probe D = reflMark i 0 F.frame*F.frame from ?_,hw] at hY; exact hY
 unfold D T; rw [probe_combine,Flight.reflect_probes]; simp only [A,probe_cons,probe_nil,mul_one]
end StageTw
end Cliplet
end YM.CF.Pannier.Chancel
#print axioms YM.CF.Pannier.Chancel.Cliplet.StageTw.doubles
