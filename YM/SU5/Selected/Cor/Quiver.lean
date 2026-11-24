import YM.SU5.Selected.Cor.Light
import YM.CF.Matter.Mass
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
open Window (family)
-- pack all exactly; choose arbitrary copies periods later. Station r = Fin (copy)× color subtype.
structure Quiver (T:Type)[Fintype T][DecidableEq T] where
 kin : Window.Family
 slot : T ↪ SU.Slot
 home (x : SU.Slot) : family x=kin ↔ ∃ i, slot i=x
 unit : SU.E→* UNI T
 sap (x:SU.E): (matter x).val * mask slot= mask slot*(unit x).val
 det (x:SU.E):(unit x).val.det=1
variable (i:Fin 3)
namespace Quiver
private lemma map_land {n m:Type*}[Fintype n][Fintype m][DecidableEq n][DecidableEq m](f:m ↪ n)(A:Op n)(B:Op m)(v:∀ i j,A (f i) (f j)= B i j)(u:∀ i x,i∉Set.range f→A i (f x)=0):A*mask f=mask f*B:=by
 ext i j; rw [mask_mem]; by_cases h:i∈ Set.range f
 · obtain ⟨x,rfl⟩:=h; simp [v,Matrix.mul_apply, mask,f.injective.eq_iff,ite_mul]
 rw [u i j h]; symm; rw [Matrix.mul_apply]; refine sum_eq_zero (fun k _=>?_); unfold mask; rw [Matrix.of_apply,if_neg (fun Q=>h ⟨_,Q.symm⟩),zero_mul]
def departT : SU.Ten ↪ SU.Slot := ⟨fun p=>(i,Sum.inl p),fun _ _ p=> Sum.inl.inj (Prod.mk.inj p).2⟩
def departF : SU.F ↪ SU.Slot:= ⟨fun p=>(i,Sum.inr p),fun _ _ p=> Sum.inr.inj (Prod.mk.inj p).2⟩
def ultraT : SU.E→* UNI SU.Ten where
 toFun q:=⟨ExTwo.wedgeOp (fund q),ExTwo.wedge_mem (fund_U ..)⟩
 map_one':= Subtype.ext (by change ExTwo.wedgeOp (fund 1)=1; rw [fund_one,ExTwo.wedge_one])
 map_mul' x y:=Subtype.ext (ExTwo.wedge_mul ..)
def ultraF: SU.E→* UNI SU.F where
 toFun q:= ⟨CF.cc (fund q),by constructor; rw [← CF.cc_star,←CF.cc_mul,show star (fund q) * fund q=1 from (fund_U q).1, CF.cc_one]; rw [←CF.cc_star,←CF.cc_mul,show fund q*star (fund q)=1 from (fund_U q).2,CF.cc_one]⟩
 map_one':=Subtype.ext (by change CF.cc (fund 1)=1; rw [fund_one, CF.cc_one])
 map_mul' x y:= Subtype.ext (CF.cc_mul ..)
lemma departureT (x:SU.Slot): family x=(i,true) ↔ x∈ Set.range (departT i):=by
 rcases x with ⟨t,a|a⟩
 · unfold family; simp only [Prod.mk.injEq]; constructor; · rintro ⟨rfl,w⟩; exact ⟨a,rfl⟩
   rintro ⟨a,p⟩; exact ⟨(Prod.mk.inj p).1.symm,rfl⟩
 constructor; · intro h; have h:= (Prod.mk.inj h).2; cases h
 rintro ⟨t,h⟩; have hx:= (Prod.mk.inj h).2; cases hx
lemma departureF (x:SU.Slot): family x=(i,false) ↔ x∈ Set.range (departF i):=by
 rcases x with ⟨t,a|a⟩; constructor; intro h; have h:= (Prod.mk.inj h).2; cases h; rintro ⟨t,h⟩; have hx:=(Prod.mk.inj h).2; cases hx
 unfold family; simp only [Prod.mk.injEq]; constructor; rintro ⟨rfl,w⟩; exact ⟨a,rfl⟩; rintro ⟨a,p⟩; exact ⟨(Prod.mk.inj p).1.symm,rfl⟩
def starT : Quiver SU.Ten:= ⟨(i,true),departT i,(departureT i),ultraT,(fun x=> map_land _ _ _ (fun i j=> by simp [departT,triple,SU.each,Join.both]; rfl) fun a v h=> Window.neq_block x (show family a ≠ _ from fun e=> h ((departureT i a).1 e))),fun x=> by change (ExTwo.wedgeOp (fund x)).det=1; rw [ExTwo.wedge_det, fund_det, one_pow]⟩ -- tune
-- $u$ anti 5, orientation first. 
def starF: Quiver SU.F:= ⟨(i,false),departF i,departureF i,ultraF,(fun x=> map_land _ _ _ (fun i j=> by simp [departF,triple,SU.each,Join.both]; rfl) fun a v h=> Window.neq_block x (show family a ≠ _ from fun e=> h ((departureF i a).1 e))),fun x=> by change (CF.cc (fund x)).det=1; rw [CF.cc,Matrix.det_transpose, Matrix.star_eq_conjTranspose,Matrix.det_conjTranspose, fund_det]; simp⟩
variable {T:Type}[Fintype T][DecidableEq T]
end Quiver
open Quiver
variable {T:Type}[Fintype T][DecidableEq T]
-- group element L of copies·T, ultimately dimension=10. Never mixes copies; fixed center character from kin, no cp mix.
structure Society (T:Type)[Fintype T][DecidableEq T] where
 qu : Quiver T
 number : ℕ
 pos : 0<number
 counts : number ≤ 2
 quorum : number* Fintype.card T =10
namespace Society
variable (P:Society T)
def stemT:Society SU.Ten:=⟨starT i,1,by omega,by omega, by rw [pairs]⟩
def stemF:Society SU.F:=⟨starF i,2,by omega,by omega,by decide⟩
lemma families (x:Window.Family) : ∃ (T:Type)(_d:Fintype T)(_e:DecidableEq T) (P:Society T), P.qu.kin=x:=by
 rcases x with ⟨i,u|u⟩; exact ⟨_,_,_,stemF i,rfl⟩; exact ⟨_,_,_,stemT i,rfl⟩
-- avoid TC clashes with shadow Fin in consumer. Use explicit `$letI` or @.
abbrev Amount := Fin P.number
abbrev Club := Amount P × T
def arm (g:SU.E): UNI P.Club:= ⟨jump (Equiv.refl P.Amount) (fun _ => (P.qu.unit g).val), jump_unitary _ _ (fun _=>(P.qu.unit g).property)⟩
lemma arm_d (g:SU.E): (P.arm g).val.det=1:=by change (jump (Equiv.refl P.Amount) (fun _ => (P.qu.unit g).val)).det=1; rw [jump_replicate, Matrix.det_kronecker, Matrix.det_one,P.qu.det]; simp
lemma club_card : Fintype.card P.Club=10:=by unfold Club Amount; simp [P.quorum]
lemma fullH (t:T): Window.family (P.qu.slot t)=P.qu.kin:= (P.qu.home _).2 ⟨t,rfl⟩
end Society
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb
#print axioms Society.families
#print axioms Society.arm_d
