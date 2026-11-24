import YM.CF.BProof.Cabinet.Slide

/- near-bad in gap=tangential only. utilities for esp and core-local. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Cabinet
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Pods Posts
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "wB"=> House.Season mH Y.c'
local notation "g₀"=>Y.g
variable (x x':Pod Y) (r m k:ℕ)
-- utilities
variable {A D T: Finset (House.Block Y.yard Y.c')}
abbrev halo (A:Finset B)(k:ℕ):=A.biUnion (fun b=> ray mH b k)
lemma nearer (h:A⊆ D)(p:m≤k): halo Y A m⊆ halo Y D k:=by intro i v; obtain ⟨j,u,h'⟩:= mem_biUnion.mp v; exact mem_biUnion.mpr ⟨_,h u,ray_in mH k p h'⟩ -- order
lemma halo_m (b:B) : b∈ halo Y A m↔∃ i∈A,b ∈ ray mH i m:=mem_biUnion
lemma halo_spec (b:B): b∈ halo Y A m ↔∃ i∈ A,i∈ ray mH b m:=by rw [halo_m]; apply exists_congr; intro i; rw [ray_spec,ray_spec]; rw [Grid.dist_symm]; exact and_congr_right (fun l=> and_congr_right (fun _=> eq_comm))
lemma halo_in(A:Finset B):A⊆ halo Y A m:=fun i v=> (halo_m ..).2 ⟨i,v,ray_home ..⟩
lemma halo_close : halo Y A m⊆ Grid.collar A m:=by intro i l; obtain ⟨z,v,p⟩:= (halo_spec ..).1 l; exact Grid.collar_mem.mpr ⟨z,v,((ray_spec ..).1 p).1⟩
lemma halo_size : (halo Y A m).card≤ A.card*House.fourBill m:=(card_le_card (halo_close Y m)).trans (Grid.collar_volume ..)
lemma ray_flip {i j:B} : i∈ ray mH j k ↔ j∈ ray mH i k:= by rw [ray_spec,ray_spec, Grid.dist_symm]; exact and_congr_right fun _=> eq_comm
lemma ray_net {i j b:B}(p:j∈ ray mH i k)(h:b∈ ray mH j m): b∈ ray mH i (k+m):=by obtain ⟨e,t⟩:= (ray_spec ..).1 p; obtain ⟨u,v⟩:= (ray_spec ..).1 h; exact (ray_spec ..).2 ⟨(Grid.triangle i j b).trans (Nat.add_le_add e u),v.trans t⟩
lemma halo_far {i j:B}(e:k+m≤r)(h:j∈ ray mH i k)(p:i∉ halo Y A r): j∉ halo Y A m:=by
 intro o; obtain ⟨b,u,v⟩:= (halo_spec ..).1 o; exact p ((halo_spec ..).2 ⟨b,u,ray_in mH r e (ray_net Y m k h v)⟩) -- tune
abbrev rise(A:Finset B) (Q:Finset B) := A∩ Q
abbrev plate(Q:Cores Y r):= (plan wB r).T Q
abbrev touchT(P:Finset B)(x:Pod Y) := see (plan wB r) P (recital Y r x)
abbrev wheel(P:Finset B)(x:Pod Y):= comfort (plan wB r) P (recital Y r x)
abbrev Esp(P:Finset B) := Contour.Season.esp r (bitL Y) P
abbrev Spiced(b:Finset B)(x x':Pod Y):= Contour.Season.beams b x x' -- tune
lemma esp_g (p: Esp Y r T x x') : Spiced Y (wheel Y r T x) x x':= p.2
lemma esp_paid (p:Esp Y r T x x')(Q:Cores Y r)(g:Q∈ touchT Y r T x) : Spiced Y (plate Y r Q) x x':= fun i l=> p.2 i (mem_union_right _ (Contour.hull_sub (plate Y r) _ Q g l))
lemma esp_bit (p:Esp Y r T x x')(Q:Cores Y r)(g:Q∈ touchT Y r T x) : Q∈ recital Y r x':= (mem_filter.mp (show Q∈touchT Y r T x' from (show touchT Y r T x=touchT Y r T x' from p.1) ▸ g)).1
lemma esp_here (p:Esp Y r T x x') : Spiced Y T x x':= fun i l=> p.2 i (mem_union_left _ l)
variable {x}
lemma excited(Q:Cores Y r)(u:Q∈ recital Y r x): Q.val⊆ bitL Y x:=fun i v=> Tower.coverE wB r (bitL Y x) ▸ (Contour.hull_sub (plan wB r).S _ Q u (show i∈ (plan wB r).S Q from v)) -- tune
lemma atOwn {i:B}(p:i∈ bitL Y x): ∃ Q∈ recital Y r x,i∈ Q.val:= by rw [← coverE wB r (bitL Y x)] at p; exact mem_biUnion.mp p
lemma belongsCore(Q R:Cores Y r) (v:Q∈recital Y r x)(u:R ∈ recital Y r x){i:B}(h:i∈ plate Y r Q)(p:i∈ plate Y r R): Q=R:= flock_inj _ (Tower.orbitF wB r (bitL Y x)) v u h p -- tune
lemma actualCore(Q:Cores Y r)(u:Q∈recital Y r x){j:B}(v:j∈ bitL Y x)(e:j∈ plate Y r Q): j∈ Q.val:=by
 obtain ⟨R,l,g⟩:= atOwn Y r v; exact (belongsCore Y r R Q l u ((plan wB r).sub R g) e) ▸ g
lemma secure(Q:Cores Y r)(p:T⊆ plate Y r Q)(u:Q∈ recital Y r x): touchT Y r T x=(if T.Nonempty then {Q} else ∅):=by
 unfold touchT see; split; next h=>
    apply Finset.ext; intro i; rw [mem_singleton]; constructor; intro h; obtain ⟨l,v⟩:= mem_filter.mp h; obtain ⟨j,p',k⟩:=not_disjoint_iff.mp v; exact belongsCore Y r i Q l u p' (p k)
    obtain ⟨i,v⟩:=h; rintro rfl; exact mem_filter.mpr ⟨u,not_disjoint_iff.mpr ⟨i,p v,v⟩⟩ -- tune shadow name
 next h=>
    simp [not_nonempty_iff_eq_empty.mp h]
lemma exp_stays(Q:Cores Y r)(p:T⊆ plate Y r Q)(u:Q∈ recital Y r x): wheel Y r T x⊆ plate Y r Q:=by
 unfold wheel comfort; rw [show see _ _ _= _ from secure Y r Q p u]; apply union_subset p; split; · exact (by simp [Contour.hull,plate])
 exact (by simp [Contour.hull])
lemma esp_stay (Q:Cores Y r)(u:Q∈recital Y r x)(v:Q∈recital Y r x'){z}(hz:z ⊆ plate Y r Q)(p: Spiced Y (plate Y r Q) x x') : Esp Y r z x x':= ⟨(secure Y r Q hz u).trans (secure Y r Q hz v).symm, fun i l=> p i (exp_stays Y r Q hz u l)⟩
-- B-Qlast near-bad. x worlds sign sharing definitions.
abbrev hNear:ℕ:=29
def nearL (x:Pod Y) := halo Y (sick Y x) hNear -- uses implicit x; move binder?
def fault (x:Pod Y)(Q:Cores Y r): Finset B:= sick Y x∩ Q.val
def sober (Q:Cores Y r)(A:Finset B):= Q.val \ halo Y A hNear
lemma inter_p (Q:Cores Y r)(p:Spiced Y (plate Y r Q) x x'): fault Y r x Q=fault Y r x' Q:=by ext i; simp only [fault,mem_inter]; apply and_congr_left; intro he; exact Brick.Act.sick_id mH Y.g y p i ((plan wB r).sub Q he)
lemma fault_near(Q:Cores Y r)(v:Q∈recital Y r x){i:B}(p:i∈ Q.val)(h:hNear≤r) : i∈ halo Y (fault Y r x Q) hNear↔ i∈ halo Y (sick Y x) hNear:=by
 constructor; intro t; exact nearer Y _ _ (inter_subset_left (s₂:=Q.val)) le_rfl t -- tune implicit m k
 intro t; obtain ⟨b,g,k⟩:= (halo_spec ..).1 t; have hz : b∈ plate Y r Q:=by unfold plate; rw [Tower.whole]; exact Grid.collar_mem.mpr ⟨i,p,((ray_spec ..|>.1 ((ray_flip ..).1 k)).1.trans h)⟩
 exact (halo_spec ..).2 ⟨b, mem_inter.mpr ⟨g,actualCore Y r Q v (enlargement Y x g) hz⟩, k⟩
lemma sober_base(Q:Cores Y r)(h:A⊆ Q.val): ((sober Y r Q A) ∪ (Q.val∩ halo Y A hNear))=Q.val:=by ext i; simp only [sober,mem_union,mem_inter,Finset.mem_sdiff]; tauto
lemma sober_size(Q:Cores Y r): (Q.val \ sober Y r Q A).card ≤ A.card*House.fourBill hNear:= (card_le_card (fun i (h:i∈ Q.val \ sober Y r Q A)=> (by by_contra p; exact (Finset.mem_sdiff.mp h).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h).1,p⟩) : i ∈ halo Y A hNear))).trans (Cabinet.halo_size Y _)
lemma faulty_cost(Q:Cores Y r)(h:A⊆ Q.val): A⊆ Q.val \ sober Y r Q A:=by intro i p; exact Finset.mem_sdiff.mpr ⟨h p,fun g=> (Finset.mem_sdiff.mp g).2 (halo_in Y _ A p)⟩
end YM.CF.BProof.Cabinet
