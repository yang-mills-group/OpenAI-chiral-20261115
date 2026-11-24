import YM.CF.Vp929.Paint.Mesh
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape
open Finset Function Rooms Lattice Atlas Paint Mesh
open scoped Classical
namespace Mesh
local notation "N"=>spanR
local notation "B"=> Fin 4
variable {r:ℕ}(n:Side)(p:2*(N*r)< n.val)(s:March)
local notation "R"=> N*r
def stone (S T:Finset (Site n))(r:ℕ):Prop:=∀x∈S,∀y∈T, r<separation x y
abbrev wide (S:Finset (Site n))(r:ℕ):= halo r S
protected lemma stone.sym (S T:Finset (Site n))(r:ℕ) (h:stone n S T r) : stone n T S r:=fun x t y v=> by rw [separation_comm]; exact h _ v _ t
private lemma fard(S T: Finset (Site n))(h:stone n S T (3*(N*r)))(a b: Site n)(p:a∈wide n S R)(q:b∈wide n T R): R<separation a b:=by
 obtain ⟨x,z,p⟩:=halo_spec.mp p; obtain ⟨y,v,q⟩:= halo_spec.mp q; let e:=h x z y v; have u:=separation_triangle x a y; have s:= separation_triangle a b y; rw [separation_comm y] at q; omega
private lemma farf(S T:Finset (Site n))(h:stone n S T (3*(N*r))) :Disjoint (wide _ (S.image (netA n).embed) (N*R)) (wide _ (T.image (netA n).embed) (N*R)):=by
 refine Finset.disjoint_left.mpr fun a p q=>?_; obtain ⟨_,z,p⟩:= halo_spec.mp p;
 obtain ⟨_,w,q⟩:=halo_spec.mp q; obtain ⟨x,Z,rfl⟩:= mem_image.mp z; obtain ⟨y,W,rfl⟩:=mem_image.mp w; let E:=h x Z y W; rw [separation_comm _ a] at q; have A:=near_embed n (r:=2*R) x y ((separation_triangle _ a _).trans ((Nat.add_le_add p q).trans_eq (by ring))); omega
private lemma nearD (x:Site n)(d:Cover)(v:Scope r d): separation x (x+wrap n d)≤ r:=by rw [separation_comm,separation, add_comm x, add_sub_cancel_right]; exact warp _ d v
include p in
private lemma nonzero(d:Jux r): wrap n d.val.val ≠ 0:=by intro z; apply d.property; rw [← warp_unique n d.val.val p d.val.property,z]; funext i; simp [Lattice.lift]
include p in
private def Voyage(d:Jux r):Ticket (Site n→B):=(voyage_set _ (nonzero n p d)).choose
private abbrev VLaw(n:Side)(p:2*R<n.val):=Ticket.together (fun d:Jux r=> Voyage n p d)
local notation "Ω"=> Dye n r
private abbrev FLaw(n:Side):=Ticket.together (fun _:Site (fresh n)=> Ticket.unif Arm)
abbrev κ(n:Side)(p:2*(spanR*r)<n.val): Ticket (Dye n r):= Ticket.apart (VLaw n p) (FLaw n)
variable (S T:Finset (Site n))(h:stone n S T (3*(spanR*r)))
include p h
private lemma indV(Y Z:Finset (Site n)) (u:Y=wide _ S R) (v:Z=wide _ T R) : (VLaw n p).Indep (Ticket.dash (fun _:Jux r=> Vision Y id)) (Ticket.dash (fun _:Jux r=> Vision Z id)):= by
 have R₁(d : Jux r): (Voyage n p d).Indep (Vision Y id) (Vision Z id):=by
    refine (voyage_set _ (nonzero n p d)).choose_spec.2 Y Z ?_ ?_ ?_
    · exact Finset.disjoint_left.mpr fun i a b=> by have e:= fard n S T h i i (u ▸ a) (v ▸ b); rw [separation_self] at e; omega
    · intro x a b; exact (fard n S T h x (x+wrap n d.val.val) (u ▸ a) (v ▸ b)).not_ge (nearD n x d.val.val d.val.property)
    intro x a b; exact (fard n T S (stone.sym _ _ _ _ h) x (x+wrap n d.val.val) (v ▸ a) (u ▸ b)).not_ge (nearD n x d.val.val d.val.property)
 exact Ticket.docks (fun d:Jux r=> Voyage n p d) (fun _=> Vision Y id) (fun _=> Vision Z id) R₁
omit S T p h in
private lemma marksA (S:Finset (Site n))(a b:Ω) (E:Ticket.dash (fun _: Jux r=> Vision (wide _ S R) id) a.1=Ticket.dash (fun _: Jux r=> Vision (wide _ S R) id) b.1) (v:Vision (wide _ (S.image (netA n).embed) (N*R)) id a.2 = Vision (wide _ (S.image (netA n).embed) (N*R)) id b.2): Vision S (marked n) a = Vision S (marked n) b:=by
 funext z; rcases z with ⟨x,X⟩; let y:=(netA n).embed x; let F:=S.image (netA n).embed; have t:y∈ F:=Finset.mem_image_of_mem _ X
 have ht(ω)(k:separation y ω ≤ N*R):a.2 ω=b.2 ω:= congrFun v ⟨ω,halo_spec.mpr ⟨y,t,k⟩⟩
 suffices e:cloth n a x=cloth n b x from Prod.ext (congrArg code e) (ht y (by rw [separation_self]; omega))
 apply Prod.ext; · exact funext fun d=>funext fun i=>congrFun (congrFun E d) (⟨x+wrap n i.val, halo_spec.mpr ⟨x,X, nearD _ _ _ i.property⟩⟩:↑(wide _ S R))
 exact funext fun i=>ht (y+wrap (fresh n) i.val) (nearD _ _ _ i.property)
theorem indep : (κ n p).Indep (Vision S (marked n)) (Vision T (marked n)):=by
 let Q(W:Finset (Site n)) := Ticket.dash (fun _: Jux r=> Vision (wide _ W R) (id : (Site n→B) → _))
 let Bf(W:Finset (Site n)):= Vision (wide _ (W.image (netA n).embed) (N*R)) (id:(Site (fresh n)→Arm)→_)
 have u: (κ n p).Indep (Prod.map (Q S) (Bf S)) (Prod.map (Q T) (Bf T)):= Ticket.apairs _ _ (indV n p S T h _ _ rfl rfl) (ticket_set (Ticket.unif Arm) _ _ (farf n S T h))
 exact Ticket.less _ (fun i j _ _ v=> marksA _ S i j (congrArg Prod.fst v) (congrArg Prod.snd v)) (fun i j _ _ v=> marksA _ T i j (congrArg Prod.fst v) (congrArg Prod.snd v)) u
omit S T h
lemma genuine(a:Ω)(v:(κ n p).bill a≠0): Atlas.Proper (scene n a) :=by
 let t:=netA n; have e(i:Jux r):(Voyage n p i).bill (a.1 i)≠0:=fun z=> v (mul_eq_zero.mpr (Or.inl (Finset.prod_eq_zero (mem_univ i) z)))
 intro d z h; dsimp only [scene] at h; rw [map_add] at h; apply e d; unfold Voyage; rw [(voyage_set _ (nonzero n p d)).choose_spec.1]; exact Paint.Voyage.varn _ _ _ _ h
lemma pay_sym(a:Ω)(s:March): (κ n p).bill (billow n s a)=(κ n p).bill a:=by
 change (∏d:Jux r,(Voyage n p d).bill ((billow n s a).1 d))* (∏ _:Site (fresh n),(1:ℤ))=(∏d:Jux r,(Voyage n p d).bill (a.1 d))*∏ _:Site (fresh n),(1:ℤ)
 apply congrArg (·*_); refine Fintype.prod_equiv (wr s.step r) _ _ fun i=>?_ ; unfold Voyage; rw [(voyage_set _ _).choose_spec.1,(voyage_set _ _).choose_spec.1]; apply Paint.Voyage.eq_turn _ _ _ _ _ (grid n s)
 · intro x; rw [grid_sl, Signed.act_add,grid_sl,reeling]; abel
 rw [reeling]; exact (AddEquiv.addOrderOf_eq (@Signed.actEquiv (Per n) _ s.step) _).symm
end Mesh
end YM.CF.VolumeCape
