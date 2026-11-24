import YM.SU5.Selected.Cairn.Acre
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Attic.Cairn
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest Airy Rail Lantern Lantern.Bulb Attic Cuve
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 20000
local notation "I"=>Complex.I
open Mint
namespace Giant
variable (A:Giant)
abbrev Notes := A.TourA.UnitX
abbrev Block := A.TourA.Lolli
variable {N:Side}(Z:A.Notes→basisRule) {T:Type}[Fintype T][DecidableEq T] (P:Society T)
def embb (v:P.Amount):Fin 2:= Fin.castLE P.counts v
abbrev Sing:= A.Block × P.Club
abbrev Plot:= Bool × A.Sing P
def make_(e:A.Plot P) : A.Notes× SU.Slot:=((e.1,e.2.1,embb P e.2.2.1),P.qu.slot e.2.2.2)
lemma faithful : Injective (A.make_ P):=by
 rintro ⟨b,i,p,x⟩ ⟨a,z,q,y⟩ e; have hx: Injective (embb P):= Fin.castLE_injective P.counts; have v:=Prod.mk.inj (Prod.mk.inj e).1
 exact Prod.ext v.1 (Prod.ext (Prod.mk.inj v.2).1 (Prod.ext (hx (Prod.mk.inj v.2).2) (P.qu.slot.injective (Prod.mk.inj e).2)))
abbrev P0:= mask (A.make_ P)
noncomputable def banquet(b:Bool):= Screen (A.TourA.consent b)* A.P0 P
lemma banquet_cost(b:Bool): ‖A.banquet P b‖≤1:= ((portion_le _ _ (faithful A P))).trans ((tap_cost _).trans (A.TourA.consent_cost b))
lemma tune_b(b:Bool): (A.banquet P b)ᴴ*(Screen (A.TourA.blueprint))* A.P0 P=1:=by
 unfold banquet; rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one,Matrix.mul_assoc (A.P0 P)ᴴ,tap_times, Tour.target, show Screen _= _ from (Matrix.one_kronecker_one : _=_)]; -- Screen tune
 rw [Matrix.mul_one,mask_self _ (A.faithful P)]
abbrev atPut (N:Side): Site N:=wrap N A.pin
noncomputable def Sweet (N:Side)(b:Bool):= hiveX A.Whistle A.n A.t (A.atPut N) * banquet A P b
noncomputable def Bass (N:Side)(k:ℕ):= rootV Z (A.atPut N) k* A.P0 P
noncomputable def Horn (M:Tulip.Male)(N:Side)(k:ℕ):= marquee Z (A.atPut N) M k (park N A.Core)* A.P0 P -- hidden
local notation "st" b:max => Sweet A P N b
local notation "π" i:max => P.qu.slot i
lemma starb (b:Bool): st b= Screen (Rail.clerks A.Whistle N (A.atPut N) A.n A.t * A.TourA.consent b)* A.P0 P:=by unfold Sweet; rw [banquet,←Matrix.mul_assoc]; exact congrArg (fun q: WRect (Single N) (A.Notes×SU.Slot)=>q*A.P0 P) (tap_times ..)
local notation "d" k:max=> Bass A Z P N k
variable (i:A.Block)(b a:Bool)
lemma sweet_l (x:Site N×SpinIdx)(v:SU.Slot)(z:P.Amount)(j:T):
   Mint.yoke (st b) i a (x,v) (z,j)=Tour.ph b* Rail.clerks A.Whistle N (A.atPut N) A.n A.t x (A.TourA.hilt b (a,i,embb P z)) * (1:Op SU.Slot) v (π j) :=by
 rw [Mint.yoke_at,starb,mask_mem,make_,Screen,Matrix.kronecker_apply,Tour.consent,Matrix.mul_smul,Matrix.smul_apply,mask_mem]; rfl -- unwrap (x,v)
lemma bass_l (x:Site N×SpinIdx)(v:SU.Slot)(z:P.Amount)(j:T)(k:ℕ): Mint.yoke (Bass A Z P N k) i a (x,v) (z,j)= exactU Z N (A.atPut N) k x (a,i, embb P z)* (1:Op SU.Slot) v (π j):=by unfold Bass; rw [Mint.yoke_at,mask_mem,make_,rootV,Screen,Matrix.kronecker_apply] -- tune
-- orientation root basis intertwined. Reuse SU. for any `F*mask`.
lemma yoke_sch (E:WRect (SpinN N) A.Notes) : Mint.yoke (Screen E * A.P0 P) i b= (E*mask (fun j:P.Amount=>(b,i,embb P j))) ⊗ₖ (mask P.qu.slot):= by ext ⟨x,j⟩ ⟨p,t⟩; rw [Mint.yoke_at,mask_mem,make_,Screen,Matrix.kronecker_apply,Matrix.kronecker_apply,mask_mem]; simp [Matrix.one_apply,mask]
lemma yoke_court (E:WRect (SpinN N) A.Notes)(g:SU.E): (tradew N (fun _=>g)).val * Mint.yoke (Screen E * A.P0 P) i b = yoke (Screen E * A.P0 P) i b*(P.arm g).val:= by
 rw [yoke_sch, show (tradew N (fun _ => g)).val=(1:Op (Site N× SpinIdx))⊗ₖ(matter g).val from jump_replicate .., show (P.arm g).val=(1:Op P.Amount)⊗ₖ (P.qu.unit g).val from jump_replicate ..]; rw [← Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one, P.qu.sap]
lemma clan (E:WRect (SpinN N) A.Notes): Contained (labelQ N P.qu.kin) (Screen E*A.P0 P) := by
 apply (containedP ..).2; rintro ⟨x,j⟩ e ⟨b,i,v,t⟩; rw [mask_mem,make_, Screen,Matrix.kronecker_apply, Matrix.one_apply_ne, mul_zero]; intro u; apply e; exact (labelAt ..).2 (show Window.family j=_ from u.symm ▸ P.fullH _)
lemma desc_s {X: Op (Single N)}{E:WRect (Single N) (A.Plot P)}(p:X*E=E): X * yoke E i b=yoke E i b:=by unfold yoke; rw [←Matrix.mul_assoc,p]
end Giant
end YM.CF.Pannier.Chancel.Attic.Cairn
open YM.CF.Pannier.Chancel.Attic.Cairn.Giant
#print axioms starb
#print axioms clan
#print axioms sweet_l
#print axioms bass_l
#print axioms tune_b
#print axioms yoke_court
