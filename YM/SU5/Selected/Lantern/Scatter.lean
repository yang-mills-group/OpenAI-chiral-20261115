import YM.SU5.Selected.Lantern.Count
import YM.SU5.FiniteGaugeData.Pannier.Trefl
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
local notation "I"=>Complex.I
open Buffered.Afterglow Buffered.Afterglow.Journey
variable {n m:Side} {k j w t :ℕ} {τ η ξ J R δ :ℝ}{q:Type}[Fintype q][DecidableEq q]
 {M:Tulip.Male} {ν:Mark n→ℂ}{K:Calibration}{l B:ℕ}
namespace Roads
variable (h: Twosome K n ν) (hs:safeReflect M j δ n)
local notation "Act"=>Service M j w t τ η ξ J R δ q k
include h hs
lemma stand (g:n=K.c m) (A:List (Cab n)) (i:Axis)
    (f:Act A) (q:cows i (Resort A) B)(v:2^l*(B+addgap K)≤ n.val) :
    ∃ V:List (Cab n),Act V ∧ V.length=2^l*A.length ∧ ‖ν (guest A)‖^(2^l)≤ ‖ν (guest V)‖ ∧ ∀ a,a≠i → ∀ s,cows a (Resort A) s → cows a (Resort V) s := by
 induction l generalizing B A with
 | zero=> exact ⟨A,f,by simp,by simp,fun a _ s u=>u⟩
 | succ l ih=>
    have ht:B+addgap K ≤ n.val:= v.trans' (Nat.le_mul_of_pos_left _ (pow_pos two_pos _)); obtain ⟨z,p,u,e⟩:=topLong (i:=i) g _ q ht; let s:= Heat.gaugeShift K.B z
    let U:= A.map fun a=> a.shadow i s; let W:= U++A; have h'': Resort W=hyphen i s (Resort A)∪ Resort A:=by unfold W U; rw [resort_duc,Service.back_wall]; -- fix rfl
    have hp:Resort A⊆ band n i s K.ℓ:=p
    have hx: Act W := (f.back i s hs).append f (by rw [Service.back_wall]; exact west K i s _ hp) -- wtf
    have hw:= h i z (guest A) (f.permit hp)
    obtain ⟨Y,a,b,r,g'⟩:= ih W hx (B:=2*B+addgap K) (by rw [h'']; exact u) (by rw [pow_succ] at v; exact v.trans' (le_of_eq (by ring)))
    refine ⟨Y,a,?_,?_,fun a g t k=> g' a g t (h''.symm ▸ e a g t k)⟩
    · rw [b,pow_succ]; unfold W U; rw [List.length_append,List.length_map]; ring -- W/U let
    rw [pow_succ',pow_mul]; have he:reflMark i (Heat.gaugeShift K.B z) (guest A)*guest A=guest W:=by unfold W U; rw [guest_comb,Service.back_refl] -- let
    rw [he] at hw; exact (pow_le_pow_left₀ (by positivity) hw _).trans r
-- spill all axes
lemma scatter (g:n=K.c m)(v:2^l*(B+addgap K)≤ n.val)(S:Finset Axis) (A:List (Cab n))(f:Act A)
    (p:∀ a∈S,cows a (Resort A) B) : ∃ U:List (Cab n), Act U ∧ U.length=(2^l)^S.card*A.length ∧ ‖ν (guest A)‖^((2^l)^S.card) ≤ ‖ν (guest U)‖:=by
 induction S using Finset.induction_on generalizing A with
 | empty=> exact ⟨A,f,by simp,by simp⟩
 | @insert i S x ih=>
    obtain ⟨U,hU,a,b,vL⟩:= stand h hs g A i f (p i (mem_insert_self ..)) v
    obtain ⟨Z,gX,e,l'⟩:= ih U hU (fun s v=> vL s (fun h=>x (h ▸ v)) _ (p s (mem_insert_of_mem v))) -- extras
    rw [card_insert_of_notMem x,pow_succ']; refine ⟨Z,gX,?_,?_⟩
    · rw [e,a]; ring
    rw [pow_mul]; exact (pow_le_pow_left₀ (by positivity) b _).trans l'
omit h hs
lemma goldilock {x y:ℕ}(p:0<y)(v:y≤x):∃ k:ℕ, 2^k*y ≤ x ∧ x≤2*2^k*y:=by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e: Nat.find ht=k
  cases k with
  | zero=> simpa using v
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
include h hs
/-- One-datum general, including already-mirrored pair. late n lower bound. -/
theorem replicate (g:n=K.c m)(v:B+addgap K≤n.val)(F:List (Cab n))(f:Act F)
   (z:∀ i,cows i (Resort F) B) : ∃ U: List (Cab n), ∃ u:ℕ, Act U∧ 0 < u ∧ U.length=u*F.length ∧ u≤(More n).val^4 ∧ (More n).val^4 ≤ u*(4*(B+addgap K))^4 ∧ ‖ν (guest F)‖^u ≤ ‖ν (guest U)‖:=by
 obtain ⟨k',a,l⟩:= goldilock (x:=n.val) (show 0<B+addgap K from Nat.add_pos_right _ addgap_pos) v
 obtain ⟨U,g',e,y⟩:= scatter h hs g a univ F f (fun i _=> z i)
 rw [Finset.card_fin 4] at e y
 refine ⟨U,_,g',by positivity,e,?_,?_,y⟩
 · change _ ≤ (n.val*2)^4; apply pow_le_pow_left'; have hq:= a.trans' (Nat.le_mul_of_pos_right (2^k') (Nat.add_pos_right _ (show 0 < addgap K from addgap_pos))); omega
 · rw [←mul_pow]; apply pow_le_pow_left'; change n.val*2 ≤_; apply le_trans (Nat.mul_le_mul_right 2 l); exact le_of_eq (by ring)
end Roads
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern
#print axioms Roads.replicate
