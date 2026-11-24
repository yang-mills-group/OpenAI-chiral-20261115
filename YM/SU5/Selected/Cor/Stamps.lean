import YM.SU5.Selected.Cor.Bright
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
namespace Mezz
open Lifted (nodeC node_of)
variable (A:Mezz) {T:Type}[Fintype T][DecidableEq T](P:Society T)
local notation "W" => WRect
abbrev Needles := ((A.Lot × Fin 2) × Bool) × SU.Slot
abbrev Scout := (A.Lot × Fin 2) × Bool
abbrev Tack := A.Lot × P.Club -- P.Amount × T
def seat_port (v: Bool× A.Tack P): A.Needles := (((v.2.1, Fin.castLE P.counts v.2.2.1),v.1),P.qu.slot v.2.2.2)
set_option synthInstance.maxSize 24000
lemma seat_cast : Injective (seat_port A P):=by rintro ⟨i,v,a,b⟩ ⟨j,w,c,d⟩ e; exact Prod.ext (Prod.mk.inj (Prod.mk.inj e).1).2 (Prod.ext (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e).1).1).1 (Prod.ext (Fin.castLE_injective P.counts (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj e).1).1).2) (P.qu.slot.injective (Prod.mk.inj e).2)))
variable (N:Side)(F: Coast→ Wq A.marks)
-- sections of hire ... use lean `np` actual.
def multi_pay: W (Single N) (A.Needles):= hire _ F (A.detent N) ⊗ₖ (1:Op SU.Slot)
abbrev Fish := WRect (Single N) (Bool × A.Tack P)
def dart : A.Fish P N:= (A.multi_pay N F)* mask (A.seat_port P)
lemma read_d (i:A.Lot)(b:Bool)(p:P.Amount)(t:T)(x:Site N × SpinIdx)(j:SU.Slot) : A.dart P N F (x,j) (b,(i,(p,t)))= hire _ F (A.detent N) x ((i,Fin.castLE P.counts p),b) * ((1:Op SU.Slot) j (P.qu.slot t)):= by
 unfold dart; rw [mask_mem,multi_pay, Matrix.kronecker_apply]; rfl
-- local column bundle size p.Club. Separate budgets only at $v=t$; mixing estimates also later. $freeC$ clear.
variable (i:A.Lot)(b:Bool)
def cork (X:A.Fish P N): WRect (Single N) P.Club:= X * mask (fun x:P.Club=>(b,(i,x)))
lemma beer_at (X:A.Fish P N)(t:P.Club)(v:Single N): cork A P N i b X v t=X v (b,(i,t)):= mask_mem ..
lemma rasp_l (V:WRect (Single N) P.Amount): True:= trivial
-- intertwiner bare right these P.amount orbit do not change. root SU.E constant. $Recall det$.
theorem spirits (g:SU.E): (tradew N (fun _=>g)).val * (A.cork P N i b (A.dart P N F)) = A.cork P N i b (A.dart P N F) * (P.arm g).val :=by
 let f:= fun x:P.Amount=> ((i,Fin.castLE P.counts x),b); let Y:= hire _ F (A.detent N) * mask f; let U:= mask P.qu.slot; let L:= A.cork P N i b (A.dart P N F)
 have ht : L= Y ⊗ₖ U:=by
    ext ⟨p,z⟩ ⟨v,t⟩; unfold L; rw [beer_at,read_d,Matrix.kronecker_apply]; unfold Y; rw [mask_mem, Matrix.one_apply]; rfl
 rw [show A.cork P N i b (A.dart P N F)= _ from ht]; rw [show (tradew N (fun _ => g)).val=(1:Op (Site N× SpinIdx)) ⊗ₖ (matter g).val from jump_replicate .., show _=(1:Op P.Amount)⊗ₖ (P.qu.unit g).val from (show (P.arm g).val=_ from jump_replicate ..)]; rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one,P.qu.sap] -- U abbr
variable {w:ℕ}{C δ η:ℝ}(X Z: Coast→ Wq A.marks)(V: TideFrame (G:=A.G) A.n A.marks X Z A.D w δ η C)(h:w ≤ A.W)
-- support. lesser real evaluation. orientation. output Cork similar budget. Label & yaw.
lemma dart_label : Contained (labelQ N P.qu.kin) (A.dart P N F):= by
 apply (containedP ..).mpr; rintro ⟨x,j⟩ h ⟨b,i,p,t⟩; rw [read_d, Matrix.one_apply_ne ?_,mul_zero]; intro z; exact h ((labelAt ..).2 (z.symm ▸ P.fullH _))
include h V
private lemma dive (t:Cover)(u: Piece t w) (p:Fin 2) : node ((A.detent N ((i,p),b)).1+ wrap N t)∈ park N A.OuterPos:= by
 change node (wrap N ((A.globeY (i,p) b).1)+ _ ) ∈_; rw [←map_add,node_of]; exact mem_image_of_mem _ (A.rays_day b i p w h t u)
lemma dart_x : Contained (modesIn N (park N A.OuterPos)) (A.dart P N X):= by
 apply (containedP ..).mpr; rintro ⟨⟨x,j⟩,v⟩ p ⟨b,i,y,z⟩; rw [read_d]; by_contra e; obtain ⟨t,t',u,k⟩:= V.turnX (A.detent N) _ _ _ (left_ne_zero_of_mul e);
 exact p ((modes_at ..).2 (show node x∈ _ from t'.symm ▸ dive A N i b X Z V h t u _)) -- order vars tune
lemma dart_z : Contained (modesIn N (park N A.OuterPos)) (A.dart P N Z) := by
 apply (containedP ..).mpr; rintro ⟨⟨x,j⟩,v⟩ p ⟨b,i,y,z⟩; rw [read_d]; by_contra e; obtain ⟨t,t',u,k⟩:= V.turnY (A.detent N) _ _ _ (left_ne_zero_of_mul e);
 exact p ((modes_at ..).2 (show node x∈ _ from t'.symm ▸ dive A N i b X Z V h t u _))
lemma dart_pitch: Contained ((Tset N)ᶜ) (A.dart P N X):= by
 apply (containedP ..).mpr; rintro ⟨⟨x,j⟩,v⟩ p ⟨b,i,y,z⟩; rw [read_d]; by_contra e; obtain ⟨t,t',u,k,w⟩:= V.turnX (A.detent N) _ _ _ (left_ne_zero_of_mul e); apply p; subst j; exact mem_compl.mpr fun p=> (show (2:SpinIdx)∉ plusHalf by decide) ((Window.mem_Tset ..).mp p)
lemma cork_pos {x:Site N} {j:SpinIdx} {v:SU.Slot}{u:P.Club}(p: cork A P N i b (A.dart P N X) ((x,j),v) u≠0):
      ∃ t∈ A.yard i.1 true, A.Claw t b ∧ node x=(wrap (More N)) t:= by
 rcases u with ⟨y,c⟩; rw [beer_at,read_d] at p; obtain ⟨t,g,h',w',a⟩:= V.turnX (A.detent N) _ _ _ (left_ne_zero_of_mul p); let p':= Fin.castLE P.counts y; let z:= (A.globeY (i,p') b).1+t; refine ⟨nodeC z,A.rays_X b i p' w h t h' a,(A.rays b i p' w h t h').2,?_⟩; subst x; rw [←node_of]; change node (wrap N ((A.globeY (i,p') b).1) +_)= _; rw [←map_add]
lemma cork_minus {x:Site N} {j:SpinIdx} {v:SU.Slot} {u:P.Club} (f:j∈plusHalf)(p:cork A P N i b (A.dart P N Z) ((x,j),v) u≠0):
      ∃ t∈ A.yard i.1 false, A.Claw t b ∧ node x=(wrap (More N)) t:= by
 rcases u with ⟨y,c⟩; rw [beer_at,read_d] at p; obtain ⟨t,g,h',a⟩:= V.turnY (A.detent N) _ _ _ (left_ne_zero_of_mul p); let p':= Fin.castLE P.counts y; let z:= (A.globeY (i,p') b).1+t; refine ⟨nodeC z, A.rays_V b i p' w h t h' (a f),(A.rays b i p' w h t h').2, ?_⟩; subst x; rw [←node_of]; change node (wrap N ((A.globeY (i,p') b).1) +_)= _; rw [←map_add]
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms spirits
#print axioms cork_pos
#print axioms dart_x
#print axioms cork_minus
