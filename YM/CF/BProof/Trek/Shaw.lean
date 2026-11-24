import YM.CF.BProof.Trek.Rod
import YM.CF.BProof.Mapping.Shadow
/-! Unsafe blocks and micro price licenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c a:Side}(Y:Yard s)(g:Ratio c s)
abbrev Blocks (Y:Yard s)(c:Side):= Finset (House.Block Y c)
variable (B:Blocks Y c)
def ClearB (i:Y.Index)(p:Space s)(v:ℕ) := Disjoint B (House.ray Y (House.hide Y g (i,p)) v)
abbrev distant (x:Site s)(v:ℕ) := ClearB Y g B (tag Y x) (BProof.space x) v
-- price U_H true only for links in ground of safe Vic. center consistency assumption.
def ChillF (r:ℕ) := {x:Site s| ¬ Y.Vic (tag Y x) r (time x) ∨ distant Y g B x 2} -- complement of unsafe
lemma clear_weaker (i:Y.Index)(p:Space s){x y:ℕ}(h:ClearB Y g B i p x)(t:y≤x): ClearB Y g B i p y:= Disjoint.mono_right (House.ray_in Y x t) h -- tune
lemma spaceClose(x y:Site s): Grid.dist (BProof.space x) (BProof.space y)≤ separation x y:= Grid.dist_le.mpr fun i=>Lattice.component_le (x-y) i.succ -- tune
lemma hide_close (i:Y.Index){p q:Space s}{r:ℕ}(h:Grid.dist p q≤r*g.count.val) : Grid.dist (House.hide Y g (i,p)) (House.hide Y g (i,q))≤r:=by rw [House.hide,House.hide,House.dist_two]; exact Posts.elder_lip g p q r h
lemma clear_panel (i:Y.Index)(p q:Space s){u v r:ℕ}(h: Grid.dist (Grid.elder g p) (Grid.elder g q)≤r)(e:r+v≤u)(t:ClearB Y g B i p u): ClearB Y g B i q v:= by
 apply Disjoint.mono_right _ t; intro b hb; obtain ⟨a,c⟩:= (House.ray_spec ..).1 hb; refine (House.ray_spec ..).2 ⟨(Grid.triangle _ (House.hide Y g (i,q)) b).trans ((Nat.add_le_add ?_ a).trans e),c⟩; rw [House.hide,House.hide, House.dist_two]; exact h
lemma near_clear (x y:Site s) {r u:ℕ}(p:distant Y g B x (u+r))(t:tag Y x=tag Y y)(h:separation x y ≤ r*g.count.val): distant Y g B y u:=by unfold distant; rw [← t]; apply clear_panel Y g B _ (BProof.space x) _ (Posts.elder_lip g _ _ r ((spaceClose ..).trans h)) (Nat.add_comm r u).le p
lemma nearB (r:ℕ)(x:Site s)(p:x∉ChillF Y g B r):Y.Vic (tag Y x) r (time x) ∧ ¬ distant Y g B x 2:=by unfold ChillF at p; simp only [Set.mem_setOf_eq,not_or,not_not] at p; exact p
lemma spinChill (r:ℕ)(x:Site s)(u:x∈ ChillF Y g B r) (p:Y.Vic (tag Y x) r (time x)): distant Y g B x 2:= u.resolve_left (not_not.mpr p)
@[simp] lemma emptyB (i:Y.Index)(p:Space s)(r:ℕ): ClearB Y g ∅ i p r:= disjoint_empty_left ..
-- micro distance ≤1 step variation
namespace Knob
variable (S:Set (Site s))(r:ℕ)(x:Site s)
def aim (x:Site s) := Finset.inf' (insert r ((univ.filter Sᶜ).image (Lattice.separation x))) (insert_nonempty ..) id
lemma ltr : aim S r x≤r:= inf'_le id (mem_insert_self ..)
lemma stepZ {t:ℕ} : t≤ aim S r x ↔ t≤r∧ ∀ y:Site s,y∉ S → t≤ separation x y:=by simp only [aim,le_inf'_iff,forall_mem_insert,forall_mem_image, id_eq,mem_filter,mem_univ,true_and,Set.compl_setOf]; rfl -- tune
lemma hop {y:Site s}(h:y∉ S): aim S r x≤ separation x y:= ((stepZ S r x).1 le_rfl).2 y h
lemma aim_var(y:Site s): aim S r x ≤ aim S r y+separation x y:=by
 generalize o:aim S r y=t; have hp:= (stepZ S r y).1 o.ge
 by_cases p:r=t; · rw [←p]; exact (ltr S r x).trans (by omega)
 have hw:∃ z,z∉ S ∧ t=separation y z:=by
   by_contra! w; have he:t+1 ≤ aim S r y:=(stepZ S r y).2 ⟨by omega, fun z g=>by have hx:=w z g; have ht:=hp.2 z g; omega⟩; omega -- tune by omega on hp/t
 obtain ⟨z,g,v⟩:=hw; rw [v]; exact (hop S r x g).trans ((separation_triangle ..).trans_eq (Nat.add_comm ..))
lemma vital (x y:Site s) (p:separation x y<aim S r x): y∈ S:=by by_contra t; exact p.not_ge (hop S r x t)
end Knob
-- taper. leases mark exact outside model. 
variable {u v:ℝ}{H:Herald u v}{t:ℕ}(C:Sized t H.whole)
namespace Sized
def fixed(r:Side)(u:ℕ) :ℕ:=2*r.val+1
def live (S:Set (Site s))(x:Site s) := Rise.easeD (2*H.whole.val+1) C.taperW (Knob.aim S C.extentT x)
lemma live_z (S:Set (Site s))(x:Site s): C.live S x∈Zone:= Rise.easeD_zone .. -- tune param C
lemma live_in(S:Set (Site s))(x:Site s)(h:0<C.live S x) : 2*H.whole.val+1<Knob.aim S C.extentT x:= lt_of_not_ge (fun w=> h.ne' (Rise.enter (2*H.whole.val+1) C.taperW _ w C.taperP))
lemma live_far(S:Set (Site s))(x: Site s)(h:C.extentT ≤ Knob.aim S C.extentT x): C.live S x=1:=Rise.exit _ _ _ h C.taperP
lemma payW(S:Set (Site s))(x y:Site s)(h:separation x y≤1): |C.live S x-C.live S y|≤ rateH/(C.taperW:ℝ):= Rise.easeD_bill _ _ _ _ C.taperP ((Knob.aim_var ..).trans (Nat.add_le_add_left h _)) ((Knob.aim_var ..).trans (Nat.add_le_add_left ((separation_comm ..).trans_le h) _))
end Sized
-- Hale outside taper iff test large; lungs. no other gap may cause taper
include H C
variable (L:Pad Y H C g.count.val)
include L
lemma grasp (x y:Site s)(t:y∉ ChillF Y g B C.blockY)(h:separation x y≤ C.extentT): tag Y x=tag Y y ∧ Y.Vic (tag Y y) C.nearM (time x) :=by
 obtain ⟨hp,u⟩:= nearB Y g B _ y t; have hv:= along_t Y y x (tag Y y) hp ((separation_comm ..).trans_le h); have ht:= C.near; change _+C.extentT ≤ _ at ht
 have he:= Y.vic_nearer _ _ _ _ ht hv; exact ⟨Posts.vic Y _ _ L.slim he, he⟩ -- tune C order
lemma behold (x:Site s)(h: ¬ Y.Vic (tag Y x) C.nearM (time x) ∨ distant Y g B x 3): C.extentT≤ Knob.aim (ChillF Y g B C.blockY) C.extentT x:=by
 apply (Knob.stepZ ..).2; refine ⟨le_rfl,fun y t=>Nat.le_of_not_lt (fun e=>?_ )⟩; obtain ⟨p,u⟩:=grasp Y g B C L x y t e.le; rcases h with h|h; exact h (p.symm ▸ u); apply (nearB Y g B C.blockY y t).2; apply near_clear Y g B x y (r:=1) h p; rw [one_mul]; exact e.le.trans (le_trans (b:=C.nearM) (by have u:= C.near; unfold Sized.extentT; omega) ((by omega : C.nearM≤C.nearM+10).trans L.high))
end YM.CF.BProof.Trek
