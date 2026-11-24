import YM.CF.DPress.Wagon.Clock
import YM.CF.BPress.Schedule
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Wagon
open Function Filter Lattice RG Wilson MeasureTheory Skye Rush Spire Scree Tulip
open Fock Finset Scroll SU Lat Cube Phase Branch BPress Chess
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal ComplexOrder Matrix.Norms.L2Operator Kronecker YM.CF.BPress
attribute [local instance] opCStarAlgebra
variable {n L:Side}
namespace Buses
variable {N P: Side}{U:GapSize}{k r:ℕ}{x y:ℝ}
structure Sign (S:BandWidth)(L:Side)(p:ℕ)(b:ℕ): Prop where
 blank : S.blank.val = 2*L.val
 marked : S.P=S.blank.val*p
 tall : b ≤ S.collar
 grip : 0<b
variable {S:BandWidth} (A:Bands (More N) S) (p:Sign S L k r) {c:ℝ}(u:1≤c)
open Race Race.Ribbon Race.Credit
include p
lemma signk : 0< k:=by by_contra! v; have ht:= p.marked; rw [Nat.eq_zero_of_le_zero v,mul_zero] at ht; have hp:=S.P_pos; omega
lemma tide : S.full.val = (2*L.val)*(k+1):=by change S.P+_= _; rw [p.marked,p.blank]; ring
noncomputable def mint : Race N L := ⟨A.Q.val*(k+1),0,(by have hp := A.size_eq; change N.val*2= _ at hp; rw [tide p] at hp; nlinarith),r,p.grip⟩
-- Ribbon height.Staging cost clock. RPC.T. expose full
abbrev sharp : (mint A p).Ribbon:=⟨k,1,signk p,by norm_num,c,u⟩
local notation "Ψ"=> mint A p
local notation "Uq"=> sharp A p u
local notation "V'"=> More N
include A
lemma cost_r : (Wall.len L)*(k+1)=((S.full.val:ℕ):ℤ):=by rw [tide p]; unfold Wall.len; push_cast; rfl -- maybe associativity
lemma board_v : A.Q.val*(sharp A p u).Γtime 1=(mint A p).η:=by change _* (1*k+1*1)=_; rw [one_mul,one_mul]; rfl
lemma sit_T : (sharp A p u).Frame 1:=by refine ⟨by norm_num,?_⟩; rw [← board_v A p u]; exact Nat.le_mul_of_pos_left _ A.Q.property
abbrev lexp(k:ℕ)(i:ℕ):ℤ:=↑((k+1)*i:ℕ)
lemma paceT(i:A.Index) : Wall.len L*lexp k i.val= ((S.full.val*i.val:ℕ):ℤ) :=by rw [Nat.cast_mul,← cost_r A p]; unfold lexp; push_cast; ring
lemma seek (i:A.Index) : A.band i⊆ (mint A p).S_ (lexp k i.val) (lexp k i.val + k):=by
 intro x h; obtain ⟨a,m,z⟩:= arc_cases _ _ _ h; let C:=Wall.len L; let v:= lexp k i.val; have ht: x 0=A.start i+a:=congrFun z 0; refine (Race.S_i ..).2 ⟨(Wall.len L* lexp k i.val)+( (S.collar:ℕ):ℤ)+(a:ℤ),?_,?_,?_⟩
 · rw [paceT A p i]; push_cast; change x 0= _; rw [ht]; unfold Bands.start Bands.offset; push_cast; rfl -- tune instances
 · have hp:= p.tall; change _+ (↑r:ℤ) ≤ _; omega
 have hp := p.tall; rw [mul_add]; have he:S.P=S.marked.val+2*S.collar:=rfl; have hu:Wall.len L*k=S.P:=by rw [p.marked,p.blank]; unfold Wall.len; push_cast; rfl
 rw [hu]; change _+(r:ℤ) ≤ _; omega
lemma tape (i:A.Index)(F: Fixed.Test N) (b:Bool) (v:IsMark (A.band i) F c): ((sharp A p u).stripe (sit_T A p u)).part (lexp k i.val) b b F:= (Uq).pinL (sit_T ..) _ _ (pin ((Uq).entry _ false (v.weaken (seek A p i) le_rfl))) -- tune shape.Z.(lexp+k).len
end Buses
end YM.CF.DPress.Wagon
