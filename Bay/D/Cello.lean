import Bay.D.Villa
import Bay.D.Quavers
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
local notation "T4"=>SU.group
open Buffered Py Py.Rate LocalLimit Preparation Buffered.Afterglow
open Tower VacuumSelection Tapestry
open scoped ComplexOrder NNReal ENNReal

open SlabMark MeshClock
open Lamour.Bridge.Celeste.Clock Fabric
open YM.CF.Pannier.Chancel


open YM.CF.Pannier.Chancel 
variable {N:Side} {L J:List (Fabric N)} {v d:ℕ} {W:Fabric N→Prop}
abbrev Kspan (N:Side) (S:Finset Cover):= S.image (wrap (More N))

/-- Record the actual layout as a single touch. -/
def Staff (W:Fabric N→Prop) (a:Mark N) (S: Finset Cover) (d:ℕ):Prop:=
   ∃ L:List (Fabric N), Sylvan W 0 L ∧ a=buffet L ∧ Fabric.Broad 0 L ⊆ Kspan N S ∧ L.length=d
namespace Staff
variable {a b:Mark N} {S T:Finset Cover}
lemma foldr (h:∀{x},W x→∀ i z,W (x.twistL i z))
  (p: Staff W a S d)(i:Axis)(z:ℤ):
 Staff W (reflMark i z a) (reflectedBox i z S) d :=by
 obtain ⟨L,e,rfl,r,k⟩:=p
 refine ⟨_,e.away h i z,(buffet_turn L i z).symm,?_,(List.length_map ..).trans k⟩
 rw [Broad_turn]
 intro y u
 obtain ⟨x,g,rfl⟩:=mem_image.mp u
 obtain ⟨x,f,rfl⟩:=mem_image.mp (r g)
 rw [Shape.anno]
 exact mem_image_of_mem _ (mem_image_of_mem _ f)
lemma times (p:Staff W a S d) (q:Staff W b T v)
 (h: Disjoint (Kspan N S) (Kspan N T)):
 Staff W (a*b) (S∪T) (d+v):=by
 obtain ⟨L,e,rfl,r,k⟩:=p
 obtain ⟨J,f,rfl,s,l⟩:=q

 refine ⟨_,e.tack f (h.mono r s),(buffet_tack ..).symm,?_,by rw[List.length_append,k,l]⟩
 rw[Broad_append,Kspan,image_union]
 exact union_subset_union r s
variable (K:Calibration) (j:Axis) (t:ℕ) {i:Side}

lemma bowed (r:∀{x},W x→∀ i z,W (x.twistL i z))
 (p:Staff W (a) S d) (u:Kspan N S ⊆ Buffered.band N j 0 K.ℓ) :
 Staff W
 (reflMark j (gaugeT K t) (reflMark j 0 (reflMark j 0 a * a)))
 (plow K j t (reflectedBox j 0 S ∪ S)) (2*d) :=by
 have a₀ : Kspan N (reflectedBox j 0 S)⊆ hyphen j 0 (Kspan N S):=by
    intro y f
    obtain ⟨x,e,rfl⟩:=mem_image.mp f
    obtain ⟨x,g,rfl⟩:=mem_image.mp e
    rw [← Shape.anno]
    exact mem_image_of_mem _ (mem_image_of_mem _ g)
 have v:= (p.foldr r j 0).times p ((west K j 0 _ u).mono_left a₀)
 have v:= (v.foldr r j 0).foldr r j (gaugeT K t)
 rw[support_translation,sub_zero,←two_mul] at v
 exact v
end Staff

variable (K:Calibration)(j:Axis)(t B:ℕ)

def Feeling (S:Finset Cover):Prop := Reach K j t S ∧ ∃x, Transom j S x B
lemma Feeling.grow {S:Finset Cover}
 (p:Feeling K j t B S):
 Feeling K j (2*t) B (plow K j t (reflectedBox j 0 S ∪ S)):=by
 obtain ⟨x,e⟩:=p.2
 refine ⟨reach_grow _ _ _ _ p.1,x, fun i n y h=>?_⟩
 obtain ⟨y,u,rfl⟩:=plow_stays K j (t:ℤ) _ h
 rw[moves,if_neg n]
 rcases mem_union.mp u with f|f
 · obtain ⟨z,g,rfl⟩:=mem_image.mp f; rw[fling_move,if_neg (Ne.symm n)];exact e _ n _ g
 exact e _ n _ f

lemma treble {S:Finset Cover}
 (h:Feeling K j t B S) (n:ℕ):
 ∃ T, Feeling K j (Nup t n) B T ∧ ∀ᶠ m:Side in atTop, ∀ (Q:Side) (g:K.c m=Q)
   (W:Fabric Q→Prop) (F:Buffered.Family K), 
   (∀{x},W x→∀ i z,W (x.twistL i z))→ Staff W (arrange _ _ g (F m)) S 1 →
     Staff W (arrange _ _ g (singing K j t F n m)) T (2^n) :=by
 induction n with
 | zero=> simp only[Nup,singing,pow_zero,one_mul]; exact ⟨S,h,Eventually.of_forall (fun _ _ _ _ _ _ p=>p)⟩

 | succ n ih=>
   obtain ⟨T,f,r⟩:=ih
   rw [show Nup t (n+1)=2*Nup t n by unfold Nup; rw [pow_succ']; ring]
   refine ⟨_,Feeling.grow _ _ _ _ f,?_⟩
   filter_upwards [r,recedes K (Reach.above _ _ _ f.1)] with m u v Q g W F y p
   have b:=u _ g _ _ y p
   subst Q
   rw [singing,pow_succ']
   exact Staff.bowed K j _ y b v

abbrev taps : ℕ:=16 * K.B.val
def gaps (Q:ℕ) (j:Axis) (w:ℕ) : Axis→ℕ:= fun i=> if i=j then w*Q else Q

lemma Feeling.slots {T:Finset Cover}{r:ℕ}
 (h:Feeling K j (r*t) B T) (p:taps K*t≤B) (q:∀i,gaps B j r i + addgap K ≤ N.val)
 {S:Finset (Seat N)}(u:S⊆ Kspan N T): Will K N (gaps B j r) S:=by
 refine ⟨q,fun i=>?_⟩
 have a:ruler K.B*((r*t:ℕ):ℤ) ≤ (r:ℤ)*B := by
    have v:r*(taps K*t) ≤ r*B:=Nat.mul_le_mul_left _ p
    rw[Nat.cast_mul,mul_left_comm]
    unfold ruler;unfold taps at v
    exact_mod_cast v
 obtain ⟨x,e⟩:=h.2
 refine ⟨if i=j then 0 else x i,fun y s=>?_⟩
 obtain ⟨z,f,rfl⟩:=mem_image.mp (u s)
 have w:=h.1 z f
 refine ⟨z i, ?_,?_,rfl⟩
 · split_ifs with l
   · subst i;omega
   exact (e i l _ f).1
 dsimp[gaps]
 split_ifs with l
 · subst i; rw [Nat.cast_mul]; omega
 exact (e i l _ f).2
