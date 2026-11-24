import YM.CF.BProof.Mapping.Deep
import YM.CF.BProof.Template

/- Deep frame footprints from Design. Both sides licensed, price including extending
 neighboring at space request location. no Lc in Size of output except division promise. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping.House
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable {s c: Side}(Y:Yard s)(g:Ratio c s)
variable (S:Hall s)(i:Y.Index)(T:Support s)

/-- M bound for memory scale R from Hall; choose before y grid. -/
structure Fund (C:ℕ) : Prop where
  cap : 32≤Y.long
  reach : S.g.count.val ≤ C*Deep.D Y
  block : g.count.val ≤ Deep.D Y
  fine : 4≤ S.c.val
  dyad : S.g.count.val=2^S.k
  after : S.X.k₀≤S.k
namespace Fund
variable {g S Y}
end Fund
variable (C:ℕ)(p:Fund Y g S C)

-- use projection padded by one. Cost factor 3ⁿ independent of height.
def tilt (Q:Support s) := Grid.collar (Q.image space) 1
abbrev memory (b k C:ℕ) := b*(C+(1+k)*27)
structure Lesson (Q:Support s) where
  Z : Finset (Space s)
  rises : tilt Q⊆ Z
  connects : Grid.Conn Z 1
  bound : Z.card≤ memory S.X.size S.k C * Q.card
  solid (U V: Face.Sheet s) (h k : Face.Frame s) : Set.EqOn h k Z → Grid.Wire.Agrees G (↑Z) U V → Set.EqOn (Face.smooth S.g S.X S.k U h) (Face.smooth S.g S.X S.k V k) ↑(tilt Q)
lemma tilt_price (Q:Support s) : (tilt Q).card≤ Q.card*27:= by
 calc
   _ ≤ (Q.image space).card*27:= Grid.collar_volume ..
   _ ≤ _:= Nat.mul_le_mul_right _ card_image_le
lemma tilt_conn (Q:Support s)(h:Micro.Loc Q):Conn (tilt Q) 1:= Grid.collar_conn _ _ (trail space Q 1 h (fun x y k=> Grid.dist_le.mpr (fun i=>Grid.dist_le.mp k i.succ)))
include p
lemma teach (Q:Support s)(v:Q.Nonempty)(h:Micro.Loc Q)(w:Deep.D Y≤ Q.card): Nonempty (Lesson S C Q):=by
 obtain ⟨Z,hZ,k,-,e,h₁⟩:= S.X.reaches S.g S.k (tilt Q) p.fine p.dyad p.after (Finset.Nonempty.mono (Grid.to_collar ..) (v.image _)) (tilt_conn _ h); refine ⟨Z,hZ,k,e.trans ?_, fun U V h k f h' =>?_⟩
 · unfold memory; rw [mul_assoc]; apply Nat.mul_le_mul_left; simpa [add_mul,mul_assoc,mul_comm Q.card] using (Nat.add_le_add (p.reach.trans (Nat.mul_le_mul_left C w)) (Nat.mul_le_mul_left (1+S.k) (tilt_price Q))) -- tune p included? er
 have hs : Grid.Wire.Agrees G (↑Z) (Face.react h U) (Face.react k V):=by
    intro x p; have ha:x.1∈ Z:=p.1; have hk:x.1+tstep x.2∈ Z:=Face.slide_t .. ▸ p.2; unfold Face.react; rw [f ha,h' x p, f hk] -- tune slide
 intro x p; unfold Face.smooth; rw [Pi.mul_apply,Pi.mul_apply,h₁ _ _ hs p,f (hZ p)]

-- glue, cost distortion per component. Φ license use two. thick patch pads under user exponent.
def aisles (Z:Finset (Space s)) (i:Y.Index) := (Z.image (elder g)).image (place Y i)
def allowD (b k C:ℕ) := 7^3*(memory b k C+1)
include p
lemma cap_aisles (Q:Support s)(Z:Lesson S C Q)(w:Deep.D Y≤Q.card)(i:Y.Index): (aisles Y g Z.Z i).card*g.count.val ≤ allowD S.X.size S.k C *Q.card:=by
 apply le_trans (Nat.mul_le_mul_right g.count.val (card_image_le)); apply le_trans (Nat.mul_le_mul_right g.count.val (card_le_card (Grid.to_collar _ 1)))
 apply le_trans (port_card g _ Z.connects 1); unfold allowD; rw [mul_assoc (7^3)]; apply Nat.mul_le_mul_left (7^3); exact (Nat.add_le_add Z.bound (p.block.trans w)).trans_eq (by ring) -- tune constant n
lemma aisles_conn (Q:Support s)(Z:Lesson S C Q)(i:Y.Index): Grid.Conn (aisles Y g Z.Z i) 1:= trail (place Y i) _ _ (elders _ _ Z.connects) (fun x y h=>by simpa using h)
omit p
lemma side_l (i:Y.Index) (b c:Bool) : Circle.δ (location Y i b) (location Y i c)≤1:=by
 have ht : Circle.δ (i-1) i ≤1:=by have h:= Posts.castδ (i-1) 1; simpa using h
 cases b<;> cases c <;> unfold location Circle.δ <;> simp only [Bool.false_eq_true,↓reduceIte] <;> first | exact ht| exact (Cube.d_sym ..).trans_le ht | simp [Cube.d_id] -- tune

lemma aisles_meet (Q:Support s)(q: Q∈ Deep.Stack Y T (Deep.D Y) i)(Z:Lesson S C Q) (b:Bool): ∃ x∈Grid.collar (T.image (addr Y g)) 1, x ∈ aisles Y g Z.Z (location Y i b):= by
 obtain ⟨x,v⟩:= (Deep.brings Y T (Deep.D Y) i Q q).2.2; let p:=space x; let k:= Grid.elder g p; let X:= place Y (location Y i b) k; have hx:= (Deep.brings Y T (Deep.D Y) i Q q).2.1 v; obtain ⟨h,a⟩:= mem_inter.mp hx; refine ⟨X, Grid.collar_mem.mpr ⟨_,mem_image_of_mem _ h,?_⟩, mem_image_of_mem (place Y (location Y i b)) (mem_image_of_mem (elder g) (Z.rises (to_collar _ _ (mem_image_of_mem space v))))⟩
 unfold addr hide X; apply (within ..).2; unfold col; dsimp only [k,p]; rw [Posts.band Y i (time x) ((Deep.riseS ..).1 a).1]; exact ⟨side_l ..,by simp⟩
-- Lesson select via `choose!` perhaps Price extended supports halo of 4.
end YM.CF.BProof.Mapping.House
