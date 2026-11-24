import Merino.Mitre.Velvet
import Merino.Medal.Diadem
import YM.CF.Roots.Hat
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2000
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 620000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Merino.Mitre
open Fock Finset Lattice Lat Spire Scroll Cube Branch Skye Tenant RG BProof
open scoped BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Buffered
variable {N:Side}
open Brooch

open Roots Lamour.Bridge.Celeste.Clock Fabric Thera

variable (F:Obs N)(z:Site N)(a:ℝ)(B:ℕ)
abbrev paddle (b:ℕ):=cape_B b + cape_B b + b + b
abbrev birthplace(z:Site N)(t:Sweep N) := boxA t (node z)
abbrev across (s t:Sweep N):=paddle B<separation (birthplace z s) (birthplace z t)
abbrev ball(F:Obs N)(s:Sweep N):=toMark (Bide.move s⁻¹ F)
structure Ample (F:Obs N)(z:Site N)(a:ℝ)(B:ℕ)(A:Fabric N):Prop where
 keep:AtSupport false A.S A.x
 val: ∀ V,‖A.x V‖≤a
 pair:∃ s t:Sweep N, birthplace z s ∈ A.S ∧ birthplace z t ∈ A.S ∧
   across z B s t ∧ A.x=ball F s * ball F t

lemma birthplace_flip(s:Sweep N)(i:Axis)(w:ℤ):birthplace z ((flipL i w)*s)=(plane i w).anon N (birthplace z s):=
  (push_box ..).trans (fl_box ..)


lemma reflBound{P:Mark N}(h:∀ V,‖P V‖≤a)(i:Axis)(w:ℤ):∀ V,‖reflMark i w P V‖≤a:=
 fun V=>(Bide.pay_s true (carR i w N) (P (reflFields i w V))).trans_le (h _)
variable {F z B a}{A:Fabric N}
lemma flips(h:Bide.plainP F)(p:Ample F z a B A)
 (i:Axis)(w:ℤ):Ample F z a B (A.twistL i w):=by
 obtain ⟨s,t,g,k,r,u⟩:=p.pair
 let v:Sweep N:=flipL i w
 refine ⟨p.keep.refl i w,reflBound _ p.val _ _,v*s,v*t,?_,?_,?_,?_⟩
 · rw [birthplace_flip];exact mem_image.mpr ⟨_,g,rfl⟩
 · rw [birthplace_flip];exact mem_image.mpr ⟨_,k,rfl⟩
 · simpa only [across,birthplace,push_box,sitT] using r
 change reflMark i w A.x = _
 unfold ball v
 rw [u,posed i w s h, posed i w t h];exact funext fun V=>theta_mul ..

variable {U:List (Fabric N)}


lemma flatten(h:Sylvan (Ample F z a B) (paddle B) U) :
 ∃ I:List (Sweep N), I.length=2*U.length ∧ buffet U=(I.map (ball F)).prod ∧
   (∀ s∈I,∃ A∈U,birthplace z s ∈ A.S) ∧ I.Pairwise (across z B):=by
 induction U with
 | nil=> exact ⟨[],by simp[buffet]⟩
 | cons A U ih=>
   obtain ⟨s,t,g,k,r,v⟩:=(h.core A List.mem_cons_self).pair
   obtain ⟨d,f⟩:=List.pairwise_cons.mp h.annex
   obtain ⟨I,i,j,l,e⟩:=ih ⟨fun a' h'=>h.core _ (List.mem_cons_of_mem _ h'),f⟩
   refine ⟨s::t::I,by simp[i];omega,by simp [buffet_more,v,j,mul_assoc],?_,?_⟩
   · intro m p
     simp only[List.mem_cons] at p
     rcases p with rfl|rfl|y'
     · exact ⟨_,List.mem_cons_self,g⟩
     · exact ⟨_,List.mem_cons_self,k⟩
     obtain ⟨x,p,u⟩:= l m y'
     exact ⟨_,List.mem_cons_of_mem _ p,u⟩
   simp only [List.pairwise_cons,List.forall_mem_cons]
   have u(j)(p:birthplace z j∈A.S)(w)(x:w∈I):across z B j w:=by
     obtain ⟨a,o,b⟩:=l w x
     exact d a o _ p _ b
   exact ⟨⟨r,u s g⟩, u t k,e⟩


abbrev host (z:Site N)(s:Sweep N):Site N:=(castX s).mills N z
lemma arrived : node∘host z = birthplace z:=funext fun _=>Shape.nodex ..

variable (z) (I :List (Sweep N))
abbrev sit : Fin I.length → Seat N:= birthplace z ∘ I.get

lemma guests(h:I.Pairwise (across z B)):
 Force_M B (sit z I) 1 ∧ ψS (sit z I) (List.finRange _):=by
 have g(i j: Fin I.length)(p:i≠j):paddle B<separation (sit z I i) (sit z I j):=
    (lt_or_gt_of_ne p).elim ((List.pairwise_iff_get.mp h) i j)
    fun u=>((List.pairwise_iff_get.mp h j i u) : paddle B<separation (sit z I j) (sit z I i)).trans_eq (separation_comm ..)
 refine ⟨⟨fun i j q=> g i j (ne_of_apply_ne _ q), ?_⟩, (List.nodup_finRange _).map ?_⟩
 · intro y
   refine Finset.card_le_one.mpr fun i q j k=>?_ ; by_contra a
   rw [reach_B] at q k
   have b:= (separation_triangle (sit z I i) y (sit z I j)).trans (Nat.add_le_add (le_of_eq_of_le (separation_comm ..) ((mem_filter.mp q).2)) ((mem_filter.mp k).2))
   have d:=g i j a
   unfold paddle at d
   omega
 intro i j v;by_contra k
 have a:=g i j k;rw [v,separation_self] at a;omega

end YM.CF.Merino.Mitre
