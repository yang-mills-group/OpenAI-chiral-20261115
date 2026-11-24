import YM.CF.BProof.Grid.Bill
import YM.Lattice.Support
import YM.Corona.Fill
import YM.Push.LOCAL_SPLITTING.Orientation

/-! Connected sets & orientations on micro torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Micro
open RG Wilson Lattice Relation Finset Function
open scoped Topology BigOperators Classical
variable {G:Gauge}{s:Side}(σ:Signed)(o:Site s)

abbrev Loc (S:Support s): Prop := Grid.Conn S 1
abbrev Spanned (S:Support s)(x y:Site s): Prop := Grid.PathIn S 1 x y
@[simp] lemma sep (x y:Site s): Grid.dist x y=separation x y:=rfl
lemma span_dist {S:Support s} (h:Loc S) {x y:Site s} (hx:x∈S)(hy:y∈S) : separation x y < S.card:= by
 have ht: range (separation x y+1)⊆ S.image (Grid.dist x):=by
   intro i hi; obtain ⟨z,u,p⟩ := Grid.visits_all S h x y hx hy i (by rw [sep]; exact Nat.le_of_lt_succ (mem_range.mp hi)); exact mem_image.mpr ⟨_,u,p⟩
 exact le_trans ((card_range _) ▸ card_le_card ht) card_image_le
lemma turnShips (S:Support s) : Loc S ↔ Lattice.Corona.Ships S 1:=Iff.rfl
lemma halo_loc (r:ℕ){S:Support s}(h:Loc S): Loc (halo r S):= (turnShips _).2 (Corona.ship_halo r (fun i hi j hj=> Grid.path_mono Subset.rfl (by omega : 1≤r+r+1) (h i hi j hj)))
lemma single (x:Site s): Loc ({x}:Support s):=by intro a ha b hb; rw [mem_singleton.mp ha,mem_singleton.mp hb]
-- equiv action
abbrev spin (x:Site s): Site s:= σ.act x
def equiv : Site s ≃ Site s where
 toFun:=spin σ
 invFun:=spin σ⁻¹
 left_inv:=σ.inv_act
 right_inv:=σ.act_inv -- tune

def move (S:Support s):= S.image (equiv σ)
@[simp] lemma move_card (S:Support s): (move σ S).card=S.card:=card_image_of_injective S (equiv σ).injective
lemma moves {S:Support s}{t:Site s}(h:t∈S): spin σ t∈ move σ S := mem_image_of_mem (equiv σ) h
lemma move_loc {S:Support s}(h:Loc S): Loc (move σ S) := by
 intro a ha b hb; obtain ⟨x,hx,rfl⟩:= mem_image.mp ha; obtain ⟨y,hy,rfl⟩:= mem_image.mp hb
 exact ReflTransGen.lift (equiv σ) (fun a b ⟨h,g,e⟩=> ⟨moves σ h,moves σ g,(show separation _ _ ≤ _ by change separation (σ.act a) (σ.act b) ≤ 1; rw [separation_signed]; exact e)⟩) x y (h _ hx _ hy) -- tune
lemma move_halo (x:Site s)(r:ℕ): move σ (halo r {x})=halo r {spin σ x}:=by
 have he(y z:Site s):equiv σ y∈ halo r {spin σ z} ↔ y∈ halo r {z}:=by change σ.act y∈ halo r {σ.act z} ↔ _; simp [halo_spec]
 ext t; obtain ⟨z,rfl⟩:=(equiv (s:=s) σ).surjective t; rw [he,move,mem_image]; simp
lemma agrees_turn (S:Support s)(U V:Config G s)(h: Agrees (move σ S) U V): Agrees (↑S) (pull σ 0 U) (pull σ 0 V) := by
 apply Push.Local.agrees_pull; convert h using 1 -- show equiv=turnSites? definition
 rw [show ⇑(Push.Local.turnSites σ (0:Site s))=⇑(equiv σ) from funext fun p=> show σ.act p+0=(σ.act p:Site s) from add_zero _]; rfl

lemma to_step (d:Step)(x:Site s): Grid.dist x (x+d.vec) ≤1:=by rw [sep,separation_comm,separation,add_sub_cancel_left,Step.vec]; split; rw [pdist_neg]; exact pdist_step _; exact pdist_step _
lemma visits_loc (W:Walk)(x: Site s): Loc ((visits x W).toFinset):=by
 induction W generalizing x with
 | nil=> simpa [visits] using single x
 | cons d t ih=>
   let V:=visits (x+d.vec) t; have hp:x+d.vec∈ V.toFinset:=by cases t <;> simp [V,visits]
   let Z:=insert x V.toFinset; change Loc (x:: V).toFinset; rw [List.toFinset_cons]; change Loc Z; have hv(y)(g:y∈Z):Spanned Z (x+d.vec) y:=by
     rcases mem_insert.mp g with v|v; rw [v]; exact Grid.sym (.single ⟨mem_insert_self ..,mem_insert_of_mem hp,to_step d x⟩)
     exact Grid.path_mono (subset_insert ..) le_rfl (ih _ _ hp _ v)
   exact fun i p j g=> (Grid.sym (hv i p)).trans (hv j g)
lemma visits_length (W:Walk)(x:Site s): (visits x W).toFinset.card≤ W.length+1:= (List.toFinset_card_le _).trans_eq (by induction W generalizing x with |nil=>rfl| cons a b ih=> simp [visits,ih])
end YM.CF.BProof.Micro
