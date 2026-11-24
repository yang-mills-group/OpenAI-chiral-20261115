import YM.CF.BProof.Mapping.Posts
import YM.CF.BProof.Gauss.Spread

-- One patch Λ arbitrary per allowed s. Site→Block via column `allocation` ensures
-- equality geometry for neighborhood & connectedness in proof. Use dependent Side vector API.
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Lattice Finset Function Filter Grid Circle Cube Angular Angular.Yard Prox Micro Relation
open scoped Topology BigOperators Classical
variable {s c: Side}(Y:Yard s)
namespace House
abbrev Season (Y:Yard s)(c:Side): Axis→ Side:= Fin.cases Y.q fun _=>c
abbrev Block (Y:Yard s)(c:Side):= Grid.Vertex (Season Y c)
def one (x:Block Y c): Y.Index := x 0
def two (x:Block Y c): Space c:= fun i=> x i.succ
def place (k:Y.Index)(x:Space c): Block Y c := Fin.cons k x
@[simp] lemma one_place (k:Y.Index)(x:Space c): one Y (place Y k x)=k:=rfl
@[simp] lemma two_place (k:Y.Index)(x:Space c): two Y (place Y k x)=x:=Fin.tail_cons ..
@[simp] lemma place_house (x:Block Y c): place Y (one Y x) (two Y x)=x:= Fin.cons_self_tail ..
def equiv : Block Y c≃ Y.Index×Space c where
 toFun x:=(one Y x,two Y x)
 invFun x:=place Y x.1 x.2
 left_inv x:=place_house Y x
 right_inv x:=by dsimp only; rw [one_place,two_place]; -- tune
abbrev Bed (Y:Yard s)(c:Side) := gridBase (Season Y c)
lemma clock (x y:Block Y c)(k:ℕ): Grid.dist x y≤ k ↔ δ (one Y x) (one Y y)≤ k ∧ Grid.dist (two Y x) (two Y y) ≤k:= by
 constructor; intro h; exact ⟨Grid.dist_le.mp h 0, Grid.dist_le.mpr (fun i=> Grid.dist_le.mp h i.succ)⟩; intro h; apply Grid.dist_le.mpr; intro i; exact Fin.cases h.1 (fun i=> Grid.dist_le.mp h.2 i) i
lemma within {i j:Y.Index}{x y:Space c}{k}: Grid.dist (place Y i x) (place Y j y)≤k ↔δ i j≤ k ∧ Grid.dist x y ≤ k:=by rw [clock]; simp only [one_place,two_place]
@[simp] lemma dist_two (b:Y.Index)(x y:Space c): Grid.dist (place Y b x) (place Y b y)=Grid.dist x y:= Nat.le_antisymm ((within ..).2 ⟨(d_id ..).trans_le (Nat.zero_le _),le_rfl⟩) (((within ..).1 le_rfl).2)

variable (g:Ratio c s)
def col (x: Site s): Y.Col:=(Posts.night Y (time x),space x)
def hide (a:Y.Col): Block Y c:= place Y a.1 (elder g a.2)
def addr (x:Site s):Block Y c:= hide Y g (col Y x)
lemma season (i:Y.Index)(x:Site s)(h:Y.Gap i (time x)): one Y (addr Y g x)=i:= Posts.gap Y i _ h
lemma contract (h:g.count.val≤Y.grid.count.val)(k:ℕ)(x y:Site s)(p:Grid.dist x y≤k*g.count.val): Grid.dist (addr Y g x) (addr Y g y)≤ k:= by
 apply (within ..).2; exact ⟨Posts.neighbor _ _ _ k (le_trans (Grid.dist_le.mp p 0) (Nat.mul_le_mul_left k h)), Posts.elder_lip g (space x) (space y) k (Grid.dist_le.mpr fun i=> Grid.dist_le.mp p i.succ)⟩
lemma next_d (i j:Y.Index)(x:Space s) (h:Circle.δ i j≤1): Grid.dist (hide Y g (i,x)) (hide Y g (j,x)) ≤1:= (within ..).2 ⟨h,by simp⟩
lemma near_hide (a b:Y.Col)(k:ℕ)(p:(Gauss.base Y).N a b (k*g.count.val)) : Grid.dist (hide Y g a) (hide Y g b) ≤k:= (within ..).2 ⟨p.1 ▸ (d_id ..).trans_le (Nat.zero_le _),Posts.elder_lip g _ _ k p.2⟩ -- tune
lemma height (b:Block Y c): (Finset.univ.filter fun i:Y.Col=>hide Y g i=b).card≤g.count.val^3:=by
 let T:=univ.filter fun x:Space s=> elder g x=two Y b; have hx:T.card≤g.count.val^3:=Posts.elder_count g _
 apply le_trans _ hx; let d(x:Space s):Y.Col:=(one Y b,x); apply le_trans _ (card_image_le (f:=d)); apply card_le_card; intro x he; replace he:= (mem_filter.mp he).2; unfold d T; rw [← he]; apply mem_image.mpr; exact ⟨x.2,mem_filter.mpr ⟨mem_univ _,(two_place ..).symm⟩,rfl⟩ -- tune rewriting local defs
lemma nights (r:ℕ)(x:Y.Index)(v: 2*r <Y.long): (univ.filter (Y.Vic x r)).card ≤ Y.short+2*r+1:=by
 apply le_trans (card_le_card (t:=arc (before (Y.v x) r) (Y.short+2*r)) (fun a (h:a∈ _) => mem_arc.mpr ((Y.vic_pad _ _ _ v).mp ((mem_filter.mp h).2)))) (arc_card _ ((Y.padding _ v).trans Y.count_lt)).le
lemma senior (k:ℕ)(b:Block Y c)(v:2*k+1<Y.long):
    (univ.filter fun x: Site s=> addr Y g x=b ∧ ∃ i,Y.Vic i k (time x)).card ≤ (Y.short+2*k+1)* g.count.val^3:=by
 let T:=univ.filter (Y.Vic (one Y b) k); let U:=univ.filter fun x:Space s=> elder g x=two Y b
 apply le_trans (b:=T.card*U.card) _ (Nat.mul_le_mul (nights Y k (one Y b) (by omega)) (Posts.elder_count g (two Y b))); rw [← card_product]; apply le_trans _ (card_image_le (f:=(fun p: Per s × Space s => BProof.join p.1 p.2))) -- tune namespace
 apply card_le_card; intro y h; obtain ⟨p,i,g₁⟩:= (mem_filter.mp h).2; have hv:= Posts.vic Y i _ v g₁; apply mem_image.mpr; refine ⟨(time y,space y),mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,mem_filter.mpr ⟨mem_univ _,?_⟩⟩,join_time_space _⟩
 · rw [←p,addr,hide,one_place,col]; dsimp only; rw [hv]; exact g₁
 rw [← p,addr,hide,two_place]; exact rfl
end House
end YM.CF.BProof.Mapping
