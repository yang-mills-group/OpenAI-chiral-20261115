import YM.SU5.Selected.Cor.Park
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
open Lifted (nodeC node_of)
open Tender (Weeks Mile Acres widthK)
-- Geometry primitive Sleigh packages parameters throughout. Chisel includes $addgap relative to release later. $w $v widths explicit indexes.
structure Mezz where
 G : Side
 D : Side
 u : ℕ+
 ℓ : ℕ+
 q : ℕ+
 ride : ℕ -- CP6 extension. offset early-edge of later gauge-root by 2*ride (clipped to passW)

variable (p:Mezz)
namespace Mezz
def n:=Tender.nudge p.ℓ.val
def marks := 10*p.u.val
def W :ℕ:= p.D.val*p.G.val*p.q.val
def beams :ℕ:=400*p.W
def vol :ℕ:= 200*p.W
def pal : Cover:= fun i=> if i=3 then (800*p.W) else 0 -- cast arithmetic to ℤ
def Broad := plant p.beams p.pal
def Core := plant p.vol p.pal
lemma pal_z : p.pal 3=800*p.W:= if_pos rfl
lemma pal_tr {a: Axis}(v:a≠3):p.pal a=0:=if_neg v
abbrev BlockDay := Tender.Weeks p.G p.q.val
abbrev Lot := Acres p.G p.D p.u.val p.q.val
variable (i : BlockDay p)
-- seed time roots $center=t$. true = Down low X later, false → V earlier. (Matches `tape true ...`)
def forkD :ℕ:=400*p.W+p.D.val*i.val
local notation "D₀"=> p.D.val
local notation "W₀"=> p.W
local notation "Z₀"=> (2:ℤ)* ↑(forkD p i)
variable (b:Bool)
-- width for multiple schedules. legate turn requires expanded course.
def passW:= harbor p.n p.marks
def slopeW :ℤ:= if b then Z₀+2*p.n else Z₀
def leftP :ℤ:= p.slopeW i b -(if b then 0 else (2*p.passW:ℤ))
def rightP :ℤ:= p.slopeW i b + (if b then 2*p.passW else 0)+1
private def faceT (w:ℤ): Cover:=fun i=>if i=3 then w else 0
def grape := faceT (p.slopeW i b + (if b then 2*(min p.ride p.passW :ℕ) else 0))
def uganda (w n:ℤ): Cover:= fun j=> if j=3 then w else n
-- horizon $LOOM$ geography
def yard : Finset Cover:= Finset.Icc (uganda (p.leftP i b) (-100*W₀)) (uganda (p.rightP i b) (100*W₀))
-- prefixes & charge
local notation "N₀"=> p.n
local notation "H₁"=> p.passW
local notation "L₀"=> p.leftP i
local notation "U₀"=> p.rightP i
local notation "Y"=> p.yard i b
lemma left_down : L₀ true=Z₀+2*N₀:=by simp [leftP,slopeW]
lemma left_up: L₀ false=Z₀-2*H₁:=by simp [leftP,slopeW]
lemma right_down : U₀ true=Z₀+2*N₀+ 2*H₁+1:= rfl
lemma right_up : U₀ false= Z₀+1:=by simp [rightP,slopeW]
lemma slope_mid: L₀ b ≤ p.slopeW i b ∧ p.slopeW i b ≤ U₀ b:= by cases b <;> simp only [leftP,rightP,Bool.false_eq_true,ite_false,ite_true] <;> omega
lemma yard_test (x:Cover): x∈Y ↔ L₀ b ≤ x 3 ∧ x 3 ≤ U₀ b ∧ ∀ j≠(3:Axis),-(100:ℤ)*W₀ ≤ x j ∧ x j ≤ 100*W₀:=by
 rw [yard,Finset.mem_Icc]; constructor
 · rintro ⟨a,d⟩; refine ⟨a 3,d 3,fun j w=>?_⟩; specialize a j; specialize d j; unfold uganda at *; simp_all
 rintro ⟨c,d,e⟩; refine ⟨fun j=>?_,fun j=>?_⟩; all_goals unfold uganda; by_cases q:j=3;
 · subst j; exact c
 · rw [if_neg q]; exact (e _ q).1
 · subst j; exact d
 rw [if_neg q]; exact (e _ q).2
lemma grape_at: grape p i b∈ Y:= by
 apply (yard_test p i b _).mpr; rw [grape]; unfold faceT; refine ⟨?_,?_,fun j v=>?_⟩
 · have h : 2* min p.ride p.passW ≤ 2*p.passW:= Nat.mul_le_mul_left _ (min_le_right ..); have hp:= (p.slope_mid i b).1; rw [if_pos rfl]; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;> omega
 · have h : (min p.ride p.passW) ≤ p.passW:= min_le_right ..; rw [if_pos rfl]; cases b <;> unfold rightP <;> simp only [Bool.false_eq_true,ite_false,ite_true] at * <;> omega
 rw [if_neg v]; omega
lemma geo_w : 0< p.W:=by unfold W; positivity
lemma geo_g : p.G.val ≤ p.W:=by unfold W; exact (Nat.le_mul_of_pos_left _ p.D.property).trans (Nat.le_mul_of_pos_right _ p.q.property)
lemma geo_q : p.q.val ≤ p.W:= Nat.le_mul_of_pos_left _ (mul_pos p.D.property p.G.property)
lemma geo_d : p.D.val≤ p.W := (Nat.le_mul_of_pos_right _ p.G.property).trans (Nat.le_mul_of_pos_right _ p.q.property)
lemma Broad_in: p.pal∈ p.Broad:=plant_id ..
lemma Core_subset:p.Core⊆p.Broad:= from_plant p.pal (by unfold vol beams; omega)
lemma Core_pos: p.Core.Nonempty:= ⟨_,plant_id ..⟩

-- stage compact
structure Legate : Prop where
 turn : p.n + 2*p.passW+100*p.ℓ.val ≤ p.D.val
variable (h : Legate p)
lemma fork_range : 400*W₀ ≤ forkD p i ∧ forkD p i <401* W₀:= by
 have he: p.D.val*i.val < p.W:=by unfold W; rw [Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_left i.isLt p.D.property
 unfold forkD; omega
lemma fork_tr (a:Axis)(h:a≠3): p.grape i b a=0:=if_neg h
-- priority cut $Disc readiness
include h
lemma yard_hirez (x:Cover) (t:x∈Y): (790:ℤ)*W₀ ≤ x 3 ∧ x 3 ≤ 820*W₀:=by
 have hz:= h.turn; have hv:=(yard_test _ _ _ _).1 t; have ht:= p.geo_d; have h':= p.geo_w; have hG:=p.fork_range i; cases b; · rw [left_up,right_up] at hv; omega
 rw [left_down,right_down] at hv; omega
lemma yard_core : Y⊆ p.Core:=by
 intro x t; have hv:=((yard_test ..).1 t).2.2; have ht:= yard_hirez p i b h _ t; apply plant_test.mpr; apply box_test.mpr; constructor <;> intro j <;> rw [Pi.sub_apply,Mezz.vol] <;> by_cases a:j=3
 · subst j; rw [pal_z]; omega
 · rw [pal_tr p a]; specialize hv j a; omega
 · subst j; rw [pal_z]; omega
 rw [pal_tr p a]; specialize hv j a; omega
lemma slew {v w:BlockDay p}(d:v<w): p.rightP v true + (100:ℤ)* p.ℓ.val ≤ p.leftP w false := by
 have hv:forkD p v+p.D.val ≤ forkD p w:=by
    unfold forkD; have he: v.val<w.val:=d; calc _ =400*W₀+p.D.val*(v.val+1) := by ring
                                         _ ≤ _ :=by gcongr; omega
 have hc:=h.turn; have hL:0<p.ℓ.val:=p.ℓ.property; rw [left_up,right_down]; omega
lemma horizon : U₀ false + (100:ℤ)*p.ℓ.val ≤ L₀ true:=by rw [left_down,right_up]; unfold n Tender.nudge; omega
lemma yards_separated1: Disjoint (p.yard i true) (p.yard i false) := Finset.disjoint_left.mpr (fun {x} u v=>by
 have hx:= ((yard_test p i true x).1 u).1; have hl:=((yard_test p i false x).1 v).2.1; have hq:=horizon p i h; have hn:0<p.ℓ.val:=p.ℓ.property; omega)
lemma yards_progress {j k:BlockDay p} (d:j<k)(u v:Bool) : p.rightP j u + 100 * (p.ℓ.val:ℤ) ≤ p.leftP k v:= by
 have he:=slew p h d; have hx:p.rightP j u≤ p.rightP j true:=by
    cases u; · have t:= horizon p j h; have hz:=slope_mid p j true; omega
    exact le_rfl
 have ht:p.leftP k false ≤ p.leftP k v:=by cases v; exact le_rfl; have t:= horizon p k h; have hz:=slope_mid p k false; omega
 omega
lemma yards_apart {j k:BlockDay p} (d:j<k)(u v:Bool) : Disjoint (p.yard j u) (p.yard k v):=Finset.disjoint_left.mpr (fun {x} i j' => by
 have h':=yards_progress p h d u v; have hQ:= ((yard_test p j u _).1 i).2.1; have ht:= ((yard_test p k v _).1 j').1; have hn:0<p.ℓ.val:=p.ℓ.property; omega)
lemma yards_separate : Pairwise (Disjoint on (Function.uncurry p.yard)) := by
 rintro ⟨i,b⟩ ⟨j,c⟩ u; rcases lt_trichotomy i j with v|v|v; exact yards_apart _ h v _ _; subst i; cases b <;> cases c; exact absurd rfl u; exact (p.yards_separated1 _ h).symm; exact p.yards_separated1 _ h; exact absurd rfl u; exact (yards_apart _ h v _ _).symm
-- charge and landscape. true=one center-activated patch (large k2). choose adjacent plane gap.
omit h
def OuterPos := p.Core.filter fun x => 1 ≤ x 0
-- early as negative for V clips; late-X all. use standing available around x
variable (a:Axis)
lemma Outer_room:p.OuterPos ⊆ p.Core:= filter_subset ..
lemma Outer_spin (a:Axis)(q:a≠3): gleams p.Core a:=gleam_plant _ _ a (pal_tr p q)
lemma Broad_spin (a: Axis)(q:a≠3): gleams p.Broad a:=gleam_plant _ _ a (pal_tr p q)
lemma yard_spin (q:a≠3): gleams Y a:=by
 apply GleamHome; intro x t; obtain ⟨t,v,e⟩:=(yard_test ..).1 t; apply (yard_test ..).mpr; rw [fling_move,if_neg q]; refine ⟨t,v,fun j s=>?_⟩; specialize e j s; rw [fling_move]; split_ifs <;> omega

private lemma outerB (S:Finset Cover)(h:∀ t∈ S,(1:ℤ) ≤ t 0) : Disjoint S ((S.image (plane 1 0).motion).image (plane 0 0).motion):= by
 apply disjoint_left.mpr; intro i t u; obtain ⟨x,hp,rfl⟩:=mem_image.mp u; obtain ⟨y,v,rfl⟩:=mem_image.mp hp; have he:=h _ t; have hg:=h _ v; rw [fling_move,if_pos rfl,fling_move,if_neg (by decide : (1:Axis)≠0)] at he; omega
lemma Outer_dis : Disjoint (p.OuterPos) ((p.OuterPos.image (plane 1 0).motion).image (plane 0 0).motion):= outerB _ (fun _ u=> (mem_filter.mp u).2)
-- pairwise charge patches exactly at set J, $top$ & coordinate. use upper bool 
variable (x:Cover)
abbrev Claw (x:Cover) (b:Bool): Prop:= (b=true) ↔ (40:ℤ)* p.W ≤ x 2
def Zumba : Finset Cover:= univ.biUnion (fun i:BlockDay p=> (p.yard i true).filter fun x=> (40 :ℤ)*p.W ≤ x 2)
def clan (b s:Bool):Finset Cover:= if s then if b then p.yard i b∩p.Zumba else p.yard i b else (p.yard i b) \ p.Zumba -- maybe syntactic double
lemma Zumba_subset_core (u:Legate p) : p.Zumba ⊆p.Core:=by
 intro x b; obtain ⟨i,_,t⟩:= mem_biUnion.mp b -- arity
 exact (yard_core _ _ _ u) ((mem_filter.mp t).1)
lemma Zumba_left (t:x∈ Y)(v:Legate p): x∈p.Zumba ↔ b=true ∧ (40:ℤ)*W₀ ≤ x 2:=by
 unfold Zumba; rw [mem_biUnion]; constructor
 · rintro ⟨w,_,f⟩; obtain ⟨e,z⟩:= mem_filter.mp f; have he : (w,true)=(i,b):= by by_contra d; exact Finset.disjoint_left.mp (yards_separate p v d) e t
   exact ⟨(Prod.mk.inj he).2.symm,z⟩
 rintro ⟨rfl,y⟩; exact ⟨_,mem_univ i,mem_filter.mpr ⟨t,y⟩⟩
lemma Zumba_spin (q:a≠2)(s:a≠3): gleams p.Zumba a:=by
 apply GleamHome; intro t v; obtain ⟨w,h,u⟩:= mem_biUnion.mp v; obtain ⟨e,v⟩:= mem_filter.mp u; refine mem_biUnion.mpr ⟨w,h,mem_filter.mpr ⟨yard_spin p w true a s ▸ mem_image_of_mem _ e,?_⟩⟩; rw [fling_move, if_neg q]; exact v
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms Zumba_left
#print axioms slew
