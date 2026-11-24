import YM.SU5.Selected.Hill.Seneca
import YM.SU5.Selected.Chene.Quill
-- deep vs no-wrap clips.
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Filter Metric Lattice Tree Wilson RG Function Finset Next.Rank.Axial
open scoped Topology BigOperators Classical
variable {n:Side}
def hearty {n:Side} (r:Side)(B:ℕ) (x:ℕ): Prop:= B≤ x%r.val ∧ x%r.val+B<r.val∧x+B<n.val
def recess (r:Side)(B:ℕ) (x:Site n): Prop:=∀ i, hearty (n:=n) r B (landmark x i)
variable {x y:Site n}{r:Side}{B B':ℕ}
lemma smaller (h:recess r B x)(p:B'≤ B):recess r B' x:=by
 intro i; obtain ⟨he,hf,hg⟩:= h i; unfold hearty; omega
private lemma val_x (x:ZMod n.val)(y:ℤ)(p:y=(x.val:ℤ)) : (y:Per n)=x:=by subst y; simp
private lemma val_y (x:ZMod n.val)(y:ℤ)(p:0≤y)(t:y<n.val)(h:(y:Per n)=x): y=(x.val:ℤ):=by
 lift y to ℕ using p; subst x; rw [Int.cast_natCast,ZMod.val_natCast_of_lt (by exact_mod_cast t)]
lemma nonwrap {i:Axis}(p:B≤landmark x i)(t:landmark x i+B<n.val)(h:separation y x≤B) : landmark x i ≤ landmark y i+B ∧ landmark y i≤ landmark x i+B :=by
 let z:= lift (y-x) i; have he:z.natAbs ≤ B:= (component_le (y-x) i).trans h
 let v:= (landmark x i:ℤ)+z; have hp:v=(landmark y i:ℤ):=by
    apply val_y _ _ (by unfold v; omega) (by unfold v; omega)
    rw [show v=_ from rfl,Int.cast_add,landmark,val_x (x i) _ rfl, show (z:Per n)=y i-x i from congrFun (wrap_lift (y-x)) i,add_comm, sub_add_cancel]
 unfold v at hp; omega
private lemma nest (x y r B B':ℕ)(p:0<r)(u:B+B'≤x%r)(v:x%r+(B+B')<r)(s:x≤y+B)(t:y≤x+B) : y/r=x/r∧ B'≤y%r∧ y%r+B'<r:=by
 have he:= Nat.mod_add_div x r; obtain ⟨j,hj⟩:∃ j:ℕ,y=j+r*(x/r):=by use y-r*(x/r); omega
 have hx:j+B'<r:= by omega
 have hy:j<r:=by omega
 have hf:y%r=j:=by rw [hj,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hy]; -- tune
 refine ⟨?_, ?_, by rwa [hf]⟩
 · rw [hj,Nat.add_mul_div_left _ _ p,Nat.div_eq_of_lt hy,zero_add]
 · omega
lemma central (e:recess r (B+B') x)(h:separation y x≤ B): region r y=region r x∧ recess r B' y:=by
 have hp(i:Axis): region r y i= region r x i ∧ hearty (n:=n) r B' (landmark y i):=by
    obtain ⟨u,v,t⟩:=e i; have he:landmark x i%r.val ≤ landmark x i:=Nat.mod_le ..; obtain ⟨w,z⟩:= nonwrap (show B ≤ landmark x i from by omega) (by omega) h
    obtain ⟨o,j,k⟩:=nest _ _ r.val B B' r.property u v w z; exact ⟨o,j,k,by omega⟩
 exact ⟨funext (fun i=>(hp i).1),fun i=>(hp i).2⟩
lemma recess_all (e:recess r 1 x) (i:Axis) : sheltered r (x,i):= by obtain ⟨x,f,g⟩:=e i; exact ⟨g,f⟩
lemma recess_pin (i:Axis)(v:Per n) : ¬recess r 1 (Chene.Trunk.lineK n i v):=by
 intro h; obtain ⟨j,x⟩:= exists_ne i; have hp:= (h j).1; simp only [landmark,Chene.Trunk.lineK,if_neg x.symm,ZMod.val_zero,Nat.zero_mod] at hp; omega
def orbit (r:Side)(x:Site n) : Finset (Site n):= univ.filter (fun y=> region r y=region r x)
private lemma n_ident {x y r:ℕ}(h:x/r=y/r)(p:x%r=y%r): x=y:=by
 have hx:= Nat.mod_add_div x r; have hy:= Nat.mod_add_div y r; rw [h,p,hy] at hx; exact hx.symm
lemma orbit_bill (x:Site n)(r:Side) : (orbit r x).card≤ r.val^4:=by
 let f (x:Site n)(i:Axis) : Fin r.val:= ⟨skid r x i,skid_lt r x i⟩
 have ht:Fintype.card (Axis→Fin r.val)=r.val^4:=by simp [Axis]
 rw [← ht,← card_univ]; apply card_le_card_of_injOn f (fun i h=> mem_univ _); intro i hi j hj t; have h:region r i= region r j:= (mem_filter.mp hi).2.trans ((mem_filter.mp hj).2.symm)
 funext k; apply ZMod.val_injective; exact n_ident (congrFun h k) (congrArg Fin.val (congrFun t k))
abbrev track (p:ℕ→Prop)[DecidablePred p] (n:Side) : Finset (Per n):= univ.filter fun i => p i.val
private lemma fragment {p:ℕ→Prop}[DecidablePred p] (S:Finset ℕ)
  (f:ℕ→ℕ)(t:∀{i:ℕ},i<n.val→p i→f i∈ S)(h:∀{i j:ℕ},i<n.val→j<n.val→p i→p j→i/r.val=j/r.val→f i=f j→i=j): (track p n).card≤ (n.val/r.val+1)*S.card:=by
 rw [← card_range (n.val/r.val+1),← card_product]; refine card_le_card_of_injOn (fun i:Per n=> (i.val/r.val,f i.val)) (fun i hi=> ?_) (fun i hi j hj g=> ?_)
 · exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right i.val_lt.le)),t i.val_lt (mem_filter.mp hi).2⟩
 exact ZMod.val_injective _ (h i.val_lt j.val_lt (mem_filter.mp hi).2 (mem_filter.mp hj).2 (congrArg Prod.fst g) (congrArg Prod.snd g))
private lemma ragged (B:ℕ)(r n:Side) : (track (fun i => ¬hearty (n:=n) r B i) n).card ≤ 3*(n.val/r.val+1)*B:=by
 let D:= track (fun i=> ¬hearty (n:=n) r B i) n; let L:=track (fun i=>i%r.val<B) n; let R:=track (fun i=>r.val ≤ i%r.val+B) n; let A:= track (fun i=> n.val ≤ i+B) n
 let k:=n.val/r.val+1
 have H:D ⊆ L∪ R∪ A:=fun i p=>by
    let x:=ZMod.val i; have hp:= (Finset.mem_filter.mp (show i∈D from p)).2; by_contra w; simp [L,R,A,track] at w; unfold hearty at hp; omega
 have hl:L.card ≤ k*B:=by
    rw [←card_range B]; apply fragment (r:=r) _ (fun i=>i%r.val) (fun _ h=> mem_range.mpr h); intro i j _ _ _ _ h p; exact n_ident h p
 have hr:R.card ≤ k*B:=by
    rw [←card_range B]; refine fragment (r:=r) _ (fun i=> r.val-1-i%r.val) ?_ ?_
    · intro i hi h; apply mem_range.mpr; have he:i%r.val<r.val:= Nat.mod_lt i r.property; omega
    intro i j hi hj _ _ h p; exact n_ident h (by have ha:i%r.val<r.val:= Nat.mod_lt i r.property; have hb:j%r.val<r.val:=Nat.mod_lt j r.property; omega)
 have ha:A.card≤ k*B:=by
    rw [←card_range B]; refine fragment (r:=r) _ (fun i=>n.val-1-i) ?_ ?_
    · intro i hi h; apply mem_range.mpr; omega
    intro i j hi hj _ _ _ h; omega
 apply (card_le_card H).trans; apply (card_union_le ..).trans; change _ ≤ 3*k*B; rw [mul_assoc]; linarith [card_union_le L R]
-- wrappers for omitted counting
def slice (i:Axis)(S:Finset (Per n)):= univ.filter (fun x:Site n=> x i∈S)
lemma slice_bill(i:Axis)(S:Finset (Per n)): (slice i S).card≤ S.card*n.val^3:=by
 let F:= Equiv.piSplitAt i (fun (_:Axis)=> Per n)
 have he:Fintype.card {j:Axis//j≠i}=3:=by rw [Fintype.card_subtype_compl]; simp [Axis]
 have ht:Fintype.card ({j:Axis//j≠i}→Per n)=n.val^3:=by rw [Fintype.card_fun,ZMod.card,he]
 rw [←ht,← card_univ,←card_product]; exact card_le_card_of_injOn F (fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2,mem_univ _⟩) F.injective.injOn
-- stripe only. rough tiles use orbit_bill. compose earnings later after shell lemma.
theorem count_edge (r n : Side)(B:ℕ) : (univ.filter fun x:Site n=> ¬ recess r B x).card ≤ 12*(n.val/r.val+1)* B*n.val^3:=by
 let A:= track (fun i=> ¬ hearty (n:=n) r B i) n; let D:=3*(n.val/r.val+1)*B*n.val^3
 have hx: 12*(n.val/r.val+1)* B*n.val^3 = ∑ i:Axis, D:=by simp [Axis,D]; ring
 rw [hx]; refine (card_le_card (t:=univ.biUnion (fun i:Axis=> slice i A)) ?_).trans (card_biUnion_le.trans (sum_le_sum fun i _=> ?_));
 · intro i hi; have hp: ¬∀ j:Axis, hearty (n:=n) r B (landmark i j) := (mem_filter.mp hi).2; obtain ⟨j,h⟩:= not_forall.mp hp; exact mem_biUnion.mpr ⟨j,mem_univ j,mem_filter.mpr ⟨mem_univ i,mem_filter.mpr ⟨mem_univ _,h⟩⟩⟩
 exact (slice_bill i A).trans (Nat.mul_le_mul_right _ (ragged B r n))
end YM.Hill.Box
#print axioms YM.Hill.Box.central
#print axioms YM.Hill.Box.count_edge
#print axioms YM.Hill.Box.orbit_bill
