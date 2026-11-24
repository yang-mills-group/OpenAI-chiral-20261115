import YM.CF.BProof.Grid.Vertex
import YM.Corona.Fill

/-! Cardinality and walk currencies for the *anisotropic* block graphs. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Grid
open Lattice Function Finset Cube Relation
variable {n:ℕ} {s: Fin n→ Side}
abbrev Sites (s : Fin n→ Side):= Finset (Vertex s)

def collar (S:Sites s)(k:ℕ):Sites s:= Finset.univ.filter fun x=>∃ y∈S,Grid.dist x y≤k
@[simp] lemma collar_mem {S: Sites s}{k x}:x∈collar S k ↔ ∃ y∈S,Grid.dist x y≤k:=by simp [collar]
theorem to_collar (S:Sites s)(k:ℕ): S⊆collar S k:=fun x hx=> collar_mem.mpr ⟨x,hx,by simp⟩
theorem nearby {S:Sites s}{x y:Vertex s}{k b}(h:Grid.dist x y ≤ k)(u:y∈collar S b): x∈collar S (k+b):=by
 obtain ⟨z,hz,d⟩:= collar_mem.mp u; exact collar_mem.mpr ⟨_,hz,(triangle x y z).trans (Nat.add_le_add h d)⟩
lemma collar_le {S T:Sites s}{k b}(h:S⊆T)(e:k≤b): collar S k⊆collar T b:= by intro i hi; obtain ⟨j,hj,l⟩:= collar_mem.mp hi; exact collar_mem.mpr ⟨j,h hj,l.trans e⟩

lemma collar_volume (S:Sites s) (k:ℕ) : (collar S k).card ≤ S.card*(2*k+1)^n:=by
 let C : Finset (Fin n→ℤ) := Icc (fun _=>- (k:ℤ)) (fun _=>k)
 let F(x : Vertex s× (Fin n→ℤ)) : Vertex s := x.1 + fun i=> Int.cast (x.2 i)
 have h : collar S k ⊆ (S×ˢ C).image F:=by
    intro x hx; obtain ⟨y,hy,h⟩:= collar_mem.mp hx; let z(i):=ZMod.valMinAbs (x i-y i); refine mem_image.mpr ⟨(y,z),mem_product.mpr ⟨hy,mem_Icc.mpr ⟨fun i=>?_,fun i=>?_⟩⟩,?_⟩
    · have hp:(z i).natAbs ≤ k:= dist_le.mp h i; dsimp only; omega -- syntax
    · have hp:(z i).natAbs≤k:= dist_le.mp h i; dsimp only; omega
    ext i; simp [F,z]
 apply (card_le_card h).trans (card_image_le.trans ?_); rw [card_product]; apply Nat.mul_le_mul_left; unfold C; rw [Pi.card_Icc]; simp [Int.card_Icc]; gcongr; omega -- tune

abbrev EdgeIn (S:Sites s)(k:ℕ)(x y : Vertex s): Prop := x∈S ∧ y∈ S∧ Grid.dist x y≤k
abbrev PathIn (S:Sites s)(k:ℕ)(x y:Vertex s):=ReflTransGen (EdgeIn S k) x y
def Conn (S:Sites s)(k:ℕ) := ∀ x∈S,∀ y∈ S, PathIn S k x y
lemma sym {S:Sites s}{k x y}(h : PathIn S k x y) : PathIn S k y x:= by induction h with|refl=>exact .refl|tail _ p ih=> exact .head ⟨p.2.1,p.1,(dist_symm ..) ▸ p.2.2⟩ ih
lemma path_mono {S T:Sites s}{k d x y}(h:S ⊆ T)(v:k ≤ d)(e: PathIn S k x y) : PathIn T d x y:=ReflTransGen.mono (fun _ _ ⟨hx,hy,hz⟩=>⟨h hx,h hy,hz.trans v⟩) _ _ e
lemma join {S T:Sites s}{k}(h:Conn S k)(g:Conn T k)(x)(hx:x∈S)(u:x∈T):Conn (S∪T) k:=by
 have hl(y)(hy:y∈S∪ T):PathIn (S∪ T) k x y:=by rcases mem_union.mp hy with hq|hw; exact path_mono subset_union_left le_rfl (h _ hx _ hq); exact path_mono subset_union_right le_rfl (g _ u _ hw)
 exact fun i p j h=>(sym (hl i p)).trans (hl j h)
lemma pile {ι:Type*}(I:Finset ι){S:Sites s}{k:ℕ}(h:Conn S k)(F:ι→Sites s)(g:∀ i∈I,Conn (F i) k)(p:∀ i∈I,∃ x∈S,x∈F i): Conn (S∪ I.biUnion F) k:=by
 classical
 induction I using Finset.induction_on with
 | empty=>simpa using h
 | @insert i I u ih=>
   obtain ⟨x,hx,hw⟩:=p i (mem_insert_self ..); rw [biUnion_insert,union_left_comm,union_comm (F i)]
   exact Grid.join (ih (fun i h=>g _ (mem_insert_of_mem h)) (fun i h=>p _ (mem_insert_of_mem h))) (g i (mem_insert_self ..)) x (mem_union_left _ hx) hw -- tune

lemma cast_lap {N : Side} (x : ℤ) : (ZMod.valMinAbs (x : Per N)).natAbs ≤ x.natAbs := Corona.lap (n:=N) (fun _=>x) 0

def run (x y : Vertex s)(b:ℕ) : Vertex s:= x+ fun i=>Int.cast (max (-(b:ℤ)) (min (b:ℤ) ((y i-x i).valMinAbs)))
@[simp] lemma run_start (x y : Vertex s) : run x y 0=x:=by ext i; simp [run]
lemma run_stop (x y:Vertex s){b:ℕ}(h:dist x y≤b):run x y b=y:=by
 ext i; unfold run; dsimp only [Pi.add_apply]; have ht:=(dist_le.mp ((dist_symm ..) ▸ h : dist y x ≤ b)) i; unfold delta1 at ht
 rw [show max (-(b:ℤ)) _=(y i-x i).valMinAbs from by omega,ZMod.coe_valMinAbs]; abel
lemma run_step (x y:Vertex s){a b}(h:a≤b):dist (run x y a) (run x y b) ≤ b-a:=by
 apply dist_le.mpr; intro i; unfold delta1 run; simp only [Pi.add_apply,add_sub_add_left_eq_sub]; rw [← Int.cast_sub]
 apply (cast_lap ..).trans; omega

def road {A:Type*}[DecidableEq A](F:ℕ→A)(k:ℕ):= (Finset.range (k+1)).image F
lemma track (x:ℕ→ Vertex s)(m k:ℕ)(h:∀ i<m,dist (x i) (x (i+1))≤k):Conn (road x m) k:=by
 unfold road; induction m with
 | zero=> intro a w b g; simp only [zero_add,range_one,image_singleton,mem_singleton] at w g; rw [w,g]
 | succ i ih=>
   let q := (range (i+1)).image x; change Conn ((range _).image _) k; rw [range_add_one,image_insert]
   have he:= ih fun l p=> h _ (by omega)
   have hu:x i∈q:= mem_image_of_mem _ (mem_range.mpr (by omega)); let S:= insert (x (i+1)) q
   have hp(y)(p:y∈ S):PathIn S k (x i) y:=by
     rcases mem_insert.mp p with v|v; rw [v]; exact .single ⟨mem_insert_of_mem hu,mem_insert_self ..,h _ (by omega)⟩
     exact path_mono (subset_insert ..) le_rfl (he _ hu _ v)
   exact fun u hx t ht=>(sym (hp u hx)).trans (hp t ht)
lemma attach (x y:Vertex s)(k:ℕ)(h:dist x y≤k):
    ∃ T:Sites s,x∈T∧ y∈T∧ Conn T 1∧ T.card≤k+1∧∀ z∈T, Grid.dist x z≤k:=by
 let f:= run x y; refine ⟨road f k,?_,?_,track f _ _ (fun i _=> (run_step x y (Nat.le_succ i)).trans (by omega)),card_image_le.trans_eq (card_range _),?_⟩
 · exact run_start x y ▸ mem_image_of_mem f (mem_range.mpr (by omega))
 · exact run_stop x y h ▸ mem_image_of_mem f (mem_range.mpr (by omega))
 rintro z hx; obtain ⟨i,hi,rfl⟩:=mem_image.mp hx; have ht:= mem_range.mp hi; apply le_trans (b:=i) _ (Nat.le_of_lt_succ ht); simpa only [run_start,Nat.sub_zero] using run_step x y (Nat.zero_le i)
end YM.CF.BProof.Grid
