import GaugeFieldConstruction.Plank
import YM.CF.Buffered.Probes
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Skye Window Vale
variable (x: Cover)(d:ℕ)
-- arbitrary radius box
abbrev cartO(x:Cover)(d:ℕ):Finset Cover := Icc (fun i=> x i-(d:ℤ)) (fun i=>x i+d)
abbrev knotX(x:Cover)(d:ℕ)(n:Side):=halo d ({wrap (More n) x}:Support (More n))
lemma cart_spec (u:Cover): u∈ cartO x d ↔ ∀ i:Axis,(u i-x i).natAbs≤ d:=by
 rw [mem_Icc]; constructor
 · intro ⟨p,h⟩ i; have hz:x i-(d:ℤ) ≤ u i:=p i; have hp:u i ≤ x i+(d:ℤ):=h i; omega
 intro h; exact ⟨fun i=>by change x i-(d:ℤ) ≤ _; specialize h i; omega,fun i=>by change _≤ x i + (d:ℤ); specialize h i; omega⟩
variable (n)
-- rooted integer lift
abbrev prospect (x:Cover){n: Side}(a:Seat n):Cover:= x+Lattice.lift (a-wrap (More n) x)
lemma prospect_eta (i: Seat n): wrap (More n) (prospect x i)=i:=by rw [prospect,map_add,wrap_lift]; abel
variable {n d x}
lemma cart_M {i:Cover}{c:ℕ}(u:i∈ cartO x c)(h:c ≤ d): i∈cartO x d:= (cart_spec ..).2 fun j=> ((cart_spec ..).1 u j).trans h
lemma prospect_F {i:Cover}(u: i∈cartO x d)(w: d < n.val) : prospect x (wrap (More n) i)=i:=by
 unfold prospect; rw [← map_sub]; have he:Lattice.lift (wrap (More n) (i-x))=i-x:= lift_eq_iff.mpr ⟨rfl,fun k=>by
    have hx:= (cart_spec ..).1 u k; change -(↑(More n).val:ℤ) < 2*(i k-x k) ∧ 2*(i k-x k)≤ (More n).val; change -((n.val*2:ℕ):ℤ) < _ ∧ _ ; change _ ∧ _≤ ((n.val*2:ℕ):ℤ); omega⟩ -- tune
 rw [he]; abel
lemma cart_I (d:ℕ)(w:d<n.val): Set.InjOn (wrap (More n)) (↑(cartO x d):Set Cover):=fun _ u _ h e=> (prospect_F u w).symm.trans ((congrArg _ e).trans (prospect_F h w)) -- tune
lemma prospect_R (i: Seat n): prospect x i ∈ cartO x d ↔ i∈ knotX x d n:=by
 rw [cart_spec,halo_spec]; simp only [Finset.mem_singleton, exists_eq_left]; rw [separation_comm,separation]; change _ ↔ univ.sup _ ≤ d; rw [Finset.sup_le_iff]; unfold prospect; simp
lemma cart_T (w:d<n.val): (cartO x d).image (wrap (More n))=knotX x d n:=by
 ext i; rw [mem_image,← prospect_R]; constructor
 · intro ⟨j,h,e⟩; rw [←e,prospect_F h w]; exact h
 intro h; exact ⟨_,h,prospect_eta ..⟩
-- adjacency local.
lemma prospect_Q (w:d+1<n.val)(i:Seat n)(k:Axis)(h:i∈knotX x d n) : prospect x (i+step k) =prospect x i+step k:=by
 have he: wrap (More n) (prospect x i+step k)=i+step k:= by rw [map_add,wrap_step,prospect_eta]
 rw [←he]; apply prospect_F _ w; rw [cart_spec]; intro j; have hz:= (cart_spec ..).1 ((prospect_R i).2 h) j
 change ((prospect x i j+ step k j)-(x j)).natAbs≤ _; simp only [Lattice.step,Pi.single_apply]; split<;>omega -- tune
variable (x) {n:Side}
abbrev snake {n:Side}(V:LinksC): Pane n:=fun e=> V (prospect x e.1,e.2)
lemma snake_c : Continuous (snake (n:=n) x):= continuous_pi fun _=> continuous_apply _
variable {x}
lemma cart_L (w:d<n.val)(V: LinksC):Agrees (cartO x d) V (onC n (snake (n:=n) x V)):=by rintro ⟨i,j⟩ h u; rw [onC_spec]; unfold snake; rw [prospect_F h w]
lemma cart_S (w:d+1<n.val){V U:LinksC}(h:Agrees (cartO x d) V U):Agrees (knotX x d n) (snake (n:=n) x V) (snake (n:=n) x U):=by
 rintro ⟨i,j⟩ u v; apply h (prospect x i,j) ((prospect_R _).2 u); rw [←prospect_Q w i j u]; exact (prospect_R _).2 v
lemma porch (w:d<n.val)(V:Pane n): snake (n:=n) x (onC n V)=V:=by funext e; unfold snake; rw [onC_spec,prospect_eta]
-- ping
abbrev deckQ(i:Cover)(p:PlaqAxes):Finset Cover:=(visits i (square p.val.1 p.val.2)).toFinset
lemma onE (V:Pane n)(i:Cover)(p:PlaqAxes): faceValue (onC n V) (i,p)=faceValue V (wrap (More n) i,p):=by have he:= travel_at 0 V i (square p.val.1 p.val.2); rw [add_zero] at he; exact he
variable {V:LinksC}
lemma loopQ (i:Cover)(p:PlaqAxes)(W:LinksC)(h:Agrees (deckQ i p) V W):faceValue V (i,p)=faceValue W (i,p):=travel_local _ _ _ _ (fun b u v=>h b (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr v)) -- tune face_value
lemma touchK (i:Cover)(p:PlaqAxes): touched (wrap (More n) i,p)=(deckQ i p).image (wrap (More n)):=by simp [touched,deckQ,square_corners] -- tune
lemma cart_step {i:Cover}(p:i∈cartO x d)(j: Axis): i+step j∈cartO x (d+1):=by
 rw [cart_spec]; intro k; have hx:= (cart_spec ..).1 p k; change ((i k+step j k)-_).natAbs≤ _; simp only [Lattice.step,Pi.single_apply]; split<;>omega -- i implicit fix
lemma cart_step_b (i:Cover)(d:ℕ)(j:Axis)(h:i+step j∈ cartO x d): i∈cartO x (d+1):=by
 rw [cart_spec]; intro k; have hp:= (cart_spec ..).1 h k; change ((i k+step j k)-_).natAbs ≤ d at hp; simp only [Lattice.step,Pi.single_apply] at hp; split at hp<;>omega
lemma deck_Q {i: Cover}(w: i∈cartO x d)(p:PlaqAxes): deckQ i p ⊆ cartO x (d+2):=by
 intro j h; simp [deckQ,square_corners] at h; rcases h with rfl|rfl|rfl|rfl; exact cart_M (c:=d+1) (cart_step (d:=d) w _) (by omega); exact cart_step (cart_step (d:=d) w _) _; exact cart_M (c:=d+1) (cart_step (d:=d) w _) (by omega); exact cart_M (c:=d) w (by omega)
lemma deck_H(i:Cover)(p:PlaqAxes)(h:¬Disjoint (cartO x d) (deckQ i p)): i∈ cartO x (d+2):=by
 obtain ⟨j,v,k⟩:=Finset.not_disjoint_iff.mp h; simp [deckQ,square_corners] at k; rcases k with rfl|rfl|rfl|rfl; exact cart_M (c:=d+1) (cart_step_b _ d _ v) (by omega); exact cart_step_b _ _ _ (cart_step_b _ d _ v); exact cart_M (c:=d+1) (cart_step_b _ d _ v) (by omega); exact cart_M (c:=d) v (by omega)
lemma deck_T(w:d+6 < n.val)(i: Seat n)(p:PlaqAxes)(h:¬Disjoint (knotX x d n) (touched (i,p))): ¬ Disjoint (cartO x d) (deckQ (prospect x i) p):=by
 obtain ⟨j,hx,hy⟩:=Finset.not_disjoint_iff.mp h; let l:= prospect x j; have hf: l∈cartO x d:= (prospect_R j).2 hx; have hi: prospect x i∈cartO x (d+2):=by
    apply (prospect_R _).2; apply halo_spec.mpr; refine ⟨_,mem_singleton_self _,?_⟩; have ht:separation (wrap (More n) x) j ≤ d:=by have he:=halo_spec.mp hx; simpa using he; -- line end
    have hv:=Work.E01.sep_touched (i,p) j hy; rw [separation_comm] at hv; exact (separation_triangle _ _ _).trans (add_le_add ht hv)
 rw [show touched (i,p)=(deckQ (prospect x i) p).image (wrap (More n)) from by rw [←touchK, prospect_eta]] at hy; obtain ⟨x',t,rfl⟩:=Finset.mem_image.mp hy; have hz : x'∈cartO x (d+2+2):= deck_Q hi p t; have he:l=x':=prospect_F hz (by omega); exact Finset.not_disjoint_iff.mpr ⟨l,hf,he.symm ▸ t⟩ -- tune l generalized
variable (x d)
def pingV(t:ℝ)(V:LinksC): Prop:= ∀ (i:Cover)(p:PlaqAxes), ¬ Disjoint (cartO x d) (deckQ i p) → SU.group.chord (faceValue V (i,p)) < t
variable {t:ℝ}
lemma ping_K (V:Pane n): pingS t ((cartO x d).image (wrap (More n))) V → pingV x d t (onC n V):=by
 intro h i p g; rw [onE]; obtain ⟨j,u,v⟩:=Finset.not_disjoint_iff.mp g; apply h; exact Finset.not_disjoint_iff.mpr ⟨_,mem_image_of_mem _ u, show (wrap (More n) j) ∈ _ from by rw [touchK]; exact mem_image_of_mem _ v⟩
lemma ping_W (w:d+6<n.val)(V:Pane n): pingV x d t (onC n V) ↔ pingS t (knotX x d n) V:=by
 constructor
 · rintro h ⟨i,p⟩ g; have he:= h _ _ (deck_T w i p g); simpa only [onE,prospect_eta] using he
 rw [←cart_T (show _ from (Nat.lt_trans (by omega) w))]; exact ping_K x d V -- tune
lemma ping_D {U:LinksC}(v:Agrees (cartO x (d+4)) V U)(p:pingV x d t V): pingV x d t U:=by
 intro i j h; rw [←loopQ i j U (let f:= deck_Q (deck_H i j h) j; fun i a b=>v i (f a) (f b))]; exact p _ _ h
-- on snake also gives meas. pick side sufficiently large.
lemma ping_view (w:d+6<n.val)(V:LinksC): pingV x d t V↔ pingS t (knotX x d n) (snake x V):=by
 rw [←ping_W x d w]; have h:=cart_L (x:=x) (d:=d+4) (by omega:d+4<n.val) V; exact ⟨ping_D _ _ h,ping_D _ _ fun i u v=> (h i u v).symm⟩
lemma ping_o : IsOpen {V:LinksC|pingV x d t V}:=by let n:Side:=⟨d+7,by omega⟩; rw [show {V: LinksC|pingV x d t V}= snake (n:=n) x ⁻¹' {U:Pane n| pingS t (knotX x d n) U} from Set.ext fun a=> ping_view _ _ (show d+6<n.val from by dsimp [n]; omega) _]; exact Scree.ping_o.preimage (snake_c ..)
end ArtCart
end MastTin
end YM.CF.XGarden
end
