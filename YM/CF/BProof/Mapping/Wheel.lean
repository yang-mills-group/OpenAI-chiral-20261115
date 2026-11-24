import YM.CF.BProof.Mapping.Up
import YM.CF.BProof.Mapping.Budget

/- Beam: lifted payments from micro & columns. Works for generic entropy with Tess tag countable addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.House
open RG Wilson Function Filter Matrix MeasureTheory Finset Prox Moment Push.AbsoluteSums Gauss Lattice Angular Angular.Yard Grid Relation
open scoped Topology BigOperators Classical
variable {s c:Side}(Y:Yard s)(g:Ratio c s)(S: Hall s)(C:ℕ)
variable {A:Type*}
-- Micro
section
variable (T:A→ Support s)(p:A→ℝ)(F:A→ Sites (Season Y c))(r k:ℕ)(a d E:ℝ)
-- v permission also short terms; no need total reads; uniform Factor
abbrev up (r:ℕ) := fourBill r*7^4
abbrev upward (size k C:ℕ)(r:ℕ) := fourBill r*House.rate size k C
abbrev root_port (D k L:ℕ) := (D+2*k+1)*L^3
abbrev TT (D k r L:ℕ)(θ α:ℝ) := table 4 (up r) (root_port D k L) α θ
lemma micro (h:Factor g.count.val (up r) (upward S.X.size S.k C r) a d)
    (v:2*k+1<Y.long)(G:Toll T p (3*a) E)(K:∀ i,p i ≠0 → Seek Y (T i) k ∧ ∃ Q : House.Queue Y g S (T i) C r, F i=Q.Z):
    Toll F p d (E*TT Y.short k r g.count.val a d):=by
 let B:=House.Bed Y c; let U (x : Site s):= ∃ i,Y.Vic i k (time x)
 have hv:0≤E:= budget_nonneg (G.pays (0:Site s)); apply Factor.grant (B:=B) (f:= addr Y g) (S:=T) (H:=?_) (L:=?_) _ _ _ _ _ _ _ _ _ h G hv U ?_ -- tune
 · intro j; unfold U; convert! senior Y g k j v using 2; congr! 1; tauto
 · intro i hi; obtain ⟨t,Q,q⟩:=K i hi; rw [q]; exact Q.bound.trans_eq (by unfold up upward; ring)
 intro i hi; obtain ⟨t,Q,q⟩:= K i hi; rw [q]; obtain ⟨x,p,hx⟩:= t.near; exact ⟨Q.funds,x,p,hx,Q.lunch (to_collar _ _ (to_collar _ _ (mem_image_of_mem _ p)))⟩ -- order tune
end

-- Column. connectivity means one gap. morph.
section
variable (S: Finset Y.Col)(r:ℕ)(h:(Gauss.base Y).C S)
def holes := Grid.collar (S.image (hide Y g)) r
lemma holed {b}(h:b∈ S): hide Y g b∈ holes Y g S r:=Grid.to_collar _ _ (mem_image_of_mem _ h)
include h
lemma shifts_conn : Conn (S.image (hide Y g)) 1 := by
 intro x hx y hy; obtain ⟨a,hu,rfl⟩:=mem_image.mp hx; obtain ⟨b,v,rfl⟩:=mem_image.mp hy; refine ReflTransGen.lift (hide Y g) (fun i j hp=> ?_) _ _ (h a hu b v); exact ⟨mem_image_of_mem _ hp.1,mem_image_of_mem _ hp.2.1,near_hide Y g i j 1 ((Gauss.base Y).mono (by rw [one_mul]; exact g.count.property : 1≤1*g.count.val) hp.2.2)⟩
lemma hole_conn : Conn (holes Y g S r) 1:=Grid.collar_conn _ _ (shifts_conn Y g S h)
abbrev expense (r:ℕ) := fourBill r*5^3
lemma hole_card (t:S.Nonempty) : (holes Y g S r).card*g.count.val ≤ expense r * (S.card+g.count.val):=by
 obtain ⟨x,hx⟩:=t; have he(i:Y.Col)(hi:i∈ S): i.1=x.1:= ((Gauss.base Y).dia h hi hx).1
 let Z:= S.image Prod.snd; have hz:Conn Z 1:=by
    intro i hi j hj; obtain ⟨a,u,rfl⟩:=mem_image.mp hi; obtain ⟨b,v,rfl⟩:=mem_image.mp hj; refine ReflTransGen.lift Prod.snd (fun i j hp=> ?_) _ _ (h a u b v); exact ⟨mem_image_of_mem _ hp.1,mem_image_of_mem _ hp.2.1,hp.2.2.2⟩
 let T:= S.image (hide Y g); let V:= Z.image (elder g); have hp : T⊆ V.image (place Y x.1):=by
   intro i hi; obtain ⟨a,u,rfl⟩:= mem_image.mp hi; unfold hide; rw [he _ u]; exact mem_image_of_mem (place Y x.1) (mem_image_of_mem _ (mem_image_of_mem _ u))
 let d:=g.count.val; have ht:T.card*d ≤5^3*(S.card+d):=by
    apply (Nat.mul_le_mul_right _ ((card_le_card hp).trans card_image_le)).trans; apply le_trans (Nat.mul_le_mul_right d (card_le_card (Grid.to_collar V 0))); apply (port_card g Z hz 0).trans; apply Nat.mul_le_mul_left; exact Nat.add_le_add_right card_image_le _
 unfold holes; refine (Nat.mul_le_mul_right _ (Grid.collar_volume ..)).trans ?_; change T.card*fourBill r*d≤_; rw [mul_comm T.card, mul_assoc]; unfold expense; rw [mul_assoc]; gcongr
end
abbrev TZ (r L:ℕ)(θ α:ℝ) := table 4 (expense r) (L^3) α θ
lemma issue_column (T:A→Finset Y.Col)(p:A→ℝ)(r:ℕ)(a d E:ℝ)(h:Factor g.count.val (expense r) (expense r) a d)(k:Toll T p (3*a) E)(g':∀ i,p i≠0→ (T i).Nonempty ∧ (Gauss.base Y).C (T i)) : Toll (fun i=> holes Y g (T i) r) p d (E*TZ r g.count.val a d):=by
 let B:=House.Bed Y c; have hu:0≤E:= budget_nonneg (k.pays (0,0)); apply Factor.grant (B:=B) (f:=hide Y g) (S:=T) (R:=fun _=>True) _ _ _ _ _ _ _ _ _ h k hu ?_ ?_ ?_ -- tune
 · intro i; simpa only [true_and] using height Y g i
 · intro i hp; apply (hole_card Y g (T i) r (g' i hp).2 (g' i hp).1).trans_eq; ring
 intro i hp; obtain ⟨⟨x,hi⟩,k⟩:=g' i hp; exact ⟨hole_conn Y g (T i) r k,x,hi,trivial, holed Y g (T i) r hi⟩
end YM.CF.BProof.Mapping.House
