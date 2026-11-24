import YM.CF.Petal.Coils
set_option linter.unusedSectionVars false

/-! Deletion ratios and supported logarithms, no volume-small partition function assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Petal
open scoped BigOperators Topology
open Branch NormedSpace Function Finset
variable {I Y E D G : Type*} [DecidableEq I] [Fintype Y] [DecidableEq Y] [NormedCommRing E] [NormOneClass E] [NormedAlgebra ℝ E] [CompleteSpace E] [TopologicalSpace D] {L : Lodge Y E D G} {b : Branch.Field Y} {X : I→Seal Y} {w : I→ℝ} {F : Seal I→D→E} {A : Seal I} {r : ℝ}
structure Offer (L : Lodge Y E D G) (b : Branch.Field Y) (A : Seal I) (X : I→Seal Y) (w : I→ℝ) (F : Seal I→D→E) (r : ℝ) : Prop where
  built i (g:i∈A) : w i≠0 → Grove b (X i)
  placed S (g:S⊆A) : Token L (roof X S) (F S) (heavy w S) (fun _=>True)
  startE x : F ∅ x=1
  stitch i j (p:i⊆A) (u:j⊆A) (k:Disjoint i j) (e : Disjoint (roof X i) (roof X j)) x : F (i∪j) x=F i x * F j x
  credit i (p:i∈A) : 0≤ w i
  cash x : ∑ i∈ hose X x A, rent (r+2) (X i)*w i ≤ 1/4
variable {S T : Seal I}
def Floor (F : Seal I→D→E) (T : Seal I) (x : D) := ∑ i∈T.powerset,F i x
lemma Shelf.door (tS:S⊆A) (h : Offer (G:=G) (D:=D) (Y:=Y) (E:=E) L b A X w F r) (y : Y) (t:D) : Floor F S t= Floor F (crease {y} X S) t + ∑ i∈(tuft {y} X S).erase ∅, F i t * Floor F (crease (insert y (roof X i)) X S) t := by -- tune L shadow
  unfold Floor; rw [plum X {y}]; let T := tuft {y} X S
  rw [← add_sum_erase T _ (tuft_zero ..)]
  congr 1
  · simp only [roof_empty,union_empty,empty_union]
  apply sum_congr rfl; intro i p
  obtain ⟨u,v⟩:=tuft_mem.mp (mem_of_mem_erase p)
  rw [singleton_union, mul_sum]; apply sum_congr rfl; intro j t
  have he : j ⊆ crease ({y}∪roof X i) X S := by rw [singleton_union]; exact mem_powerset.mp t
  exact h.stitch i j (Subset.trans u tS) (Subset.trans (Subset.trans he (filter_subset ..)) tS) (Attach.root X {y} v he) (Disjoint.mono_left subset_union_right (roof_id he).symm) _
lemma Offer.less (H : Offer L b A X w F r) (p : T⊆A) : Offer L b T X w F r := by
  refine ⟨fun i k=>H.built i (p k),fun S k=> H.placed S (Subset.trans k p),H.startE,fun i j t u=> H.stitch i j (Subset.trans t p) (Subset.trans u p),fun i k=>H.credit i (p k),fun x=> le_trans ?_ (H.cash x)⟩
  apply sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ p); exact fun i k _=> mul_nonneg (rent_pos ..).le (H.credit _ (mem_filter.mp k).1)
lemma Offer.floor_lo (H : Offer L b A X w F r) (p : ∀ i∈A,X i=∅) (t : D) : Floor F A t=1 := by
  rw [Floor,sum_eq_single_of_mem _ (mem_powerset.mpr (empty_subset _)),H.startE]; intro S h k
  have ht := mem_powerset.mp h; obtain ⟨i,l⟩:= nonempty_iff_ne_empty.mpr k
  have hv : heavy w S=0 := by
    have he : w i=0 := by
      by_contra g; have hj : ∀ S, Grove b S → S.Nonempty := by intro S h; cases h <;> simp; done
      have hp := hj _ (H.built i (ht l) g); rw [p i (ht l)] at hp; simp at hp
    exact prod_eq_zero l he
  have he := H.placed S ht; exact norm_le_zero_iff.mp ((L.normF _).trans ((he.owns t).trans hv.le))
-- anchored inverse ratios multiply some carried petals at removed sites
lemma shell_k (b : Branch.Field Y) (i : Y) (S T : Seal Y) (p : Shell b i S) (q : Shell b i T) : Shell b i (S∪T) := ⟨p.1.unite q.1 p.2 q.2,mem_union_left _ p.2⟩
def Roofed (b : Branch.Field Y) (B S : Seal Y) := Grove b S ∧ B ⊆ S
def Sent (L : Lodge Y E D G) (b : Branch.Field Y) (r : ℝ) (F : Seal I→D→E) (X : I→Seal Y) (A : Seal I) (z : Y) := ∃ V, Pool L r (1/4) (Shell b z) V ∧ ∀ x, Floor F A x=(1+V x)*Floor F (crease {z} X A) x
lemma subdeliver (P : Seal I) (Q B : Seal Y) (k : 0≤r) (e : Q⊆B) (h : ∀ T⊆P,∀ x, Sent L b r F X T x) {M : D→E} {a : ℝ} (K : Pool L r a (Roofed b B) M) : ∃ N, Pool L r (a*2^Q.card) (Roofed b B) N ∧ ∀ x, M x * Floor F (crease Q X P) x=N x * Floor F P x := by
  induction Q using Finset.induction_on generalizing P M a with
  | empty=> refine ⟨M,by simpa using K,fun x=>?_⟩; simp [crease]
  | insert y S p ih=>
    let t := crease {y} X P; have ht : t⊆ P := filter_subset ..
    obtain ⟨N,hn,H⟩:= ih t ((subset_insert y S).trans e) (fun R f=> h R (Subset.trans f ht)) K
    obtain ⟨V,W,hp⟩:= h P (Subset.refl _) y
    let C : D→E := fun x=>Ring.inverse (1+V x)
    have hc : Pool L r 2 (fun T=>Shell b y T ∨ T=∅) C := W.ounce k (shell_k b y)
    have hl (x:D) : C x*Floor F P x=Floor F t x := by unfold C; rw [hp, ←mul_assoc,Ring.inverse_mul_cancel _ (W.room_name k (shell_k b y) x),one_mul]
    refine ⟨fun x=>N x*C x,?_,fun x=>?_⟩
    · rw [card_insert_of_notMem p, pow_succ,←mul_assoc]; apply hn.combine hc k; intro S T K U
      rcases U with l|l; exact ⟨K.1.unite l.1 (K.2 (e (mem_insert_self ..))) l.2,K.2.trans subset_union_left⟩; rwa [l,union_empty]
    dsimp only; rw [←singleton_union,crease_m,H x,mul_assoc, show Ring.inverse (1+V x)*Floor F P x=Floor F t x from hl x] -- tune
lemma ascent (H : Offer L b A X w F r) (k : 0≤r) : ∀ z,Sent L b r F X A z := by
  induction A using Finset.strongInductionOn with
  | _ A ih=>
    intro z; let B := crease {z} X A; have hp : B⊆ A := filter_subset ..
    by_cases g : A⊆B
    · refine ⟨fun _=>0,(Pool.free).costUp (by norm_num),fun x=> by rw [show crease {z} X A=A from Finset.Subset.antisymm hp g]; simp⟩
    have hx : B ⊂ A := ssubset_iff_subset_not_subset.mpr ⟨hp,g⟩ -- tune
    let T := (tuft {z} X A).erase ∅; let C i := rent r (roof X i)*heavy w i*2^(roof X i).card
    have he (i) (p:i∈T) : ∃ v, Pool L r (C i) (Shell b z) v ∧ ∀ x, F i x*Floor F (crease (insert z (roof X i)) X A) x=v x*Floor F B x := by
      obtain ⟨p₁,l⟩ := mem_erase.mp p; obtain ⟨u,t⟩:=tuft_mem.mp l
      have ht := Attach.meets (nonempty_iff_ne_empty.mpr p₁) t
      have hk : Token L (roof X i) (F i) (heavy w i) (Roofed b (roof X i)) := by
        have he := H.placed i u; refine { he with shape := fun c=>?_ }; refine ⟨trunk ht ?_,le_rfl⟩; intro y v
        obtain ⟨j,g,f⟩:=mem_biUnion.mp v; exact ((t j g).basin (b:=b) (fun k h=>H.built k (u h) (fun e=> c (prod_eq_zero h e)))).2 y f
      obtain ⟨N,v,D'⟩:= subdeliver B (roof X i) (roof X i) k (Subset.refl _) (fun T f x=> ih T (lt_of_le_of_lt f hx) (H.less (Subset.trans f hp)) x) (Pool.within hk)
      exact ⟨N,v.shift (fun S g=>⟨g.1,g.2 ht⟩),fun x=>by rw [←singleton_union,crease_m]; exact D' x⟩
    choose! V P U using he
    refine ⟨fun x=>∑ i∈T,V i x, (Pool.batch T _ _ P).costUp (escrow k H.credit H.cash z), fun x=>?_⟩ -- nonempty proof choose!
    have hP : ∑ i∈T,F i x*Floor F (crease (insert z (roof X i)) X A) x=(∑ i∈T,V i x)*Floor F B x := by rw [sum_mul]; exact sum_congr rfl (fun i p=>U i p x)
    rw [Shelf.door (L:=_) (X:=X) (Finset.Subset.refl _) H z x,hP]; rw [add_mul,one_mul] -- tune
-- log organized by sites
lemma promotion (H : Offer L b A X w F r) (k : 0≤r) : ∀ S:Seal Y,∃ (v : Y→D→E), (∀ y,Pool L r (1/3) (Shell b y) (v y)) ∧ ∀ x, Floor F A x=exp (∑ y∈S,v y x)*Floor F (crease S X A) x := by
  intro S; induction S using Finset.induction_on generalizing A with
  | empty=>
    refine ⟨fun _ _=>0,fun _=>Pool.free.costUp (by norm_num),fun x=>?_⟩
    letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
    simp [crease]
  | insert y S p ih=>
    let B := crease {y} X A
    obtain ⟨V,Q,q⟩:= ascent H k y; obtain ⟨w,P,U⟩:= ih (A:=B) (H.less (filter_subset ..))
    obtain ⟨t,l⟩:= Q.steam_ticket k (shell_k b y); let M : Y→D→E:= fun z=> if z=y then fun x=>steam (V x) else w z
    refine ⟨M,fun z=>?_,fun x=>?_⟩
    · unfold M; split; rename_i he; subst z; exact t; exact P z
    letI : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
    rw [q,show Floor F (crease {y} X A) x=_ from U x, ← mul_assoc,sum_insert p,exp_add, show M y x=steam (V x) by simp [M], l]; rw [←singleton_union,crease_m]
    rw [sum_congr rfl (fun z (g:z∈S)=> show M z x=w z x by unfold M; rw [if_neg (fun (he:z=y)=>p (he ▸ g))])]
lemma forest (H : Offer L b A X w F r) (u : 0<r) {c : ℝ} (p : 0≤c) (g : ∀ (x:Y) m,((bay b x m).card:ℝ)≤ c*((m:ℝ)+1)^4) : ∃ (K : Seal Y→D→E) (d : Seal Y→ℝ), Charge L b (r/2) (bulk r c*(1/3)) K d ∧ ∀ x, Floor F A x=exp (∑ S:Seal Y, K S x) := by
  obtain ⟨v,h,Q⟩:=promotion H u.le univ; obtain ⟨K,d,ch,e⟩:=housing (by norm_num) p u g h; refine ⟨K,d,ch,fun x=>?_⟩
  have hx := (H.less (show crease univ X A⊆A from filter_subset ..)).floor_lo (fun i k=>by apply eq_empty_iff_forall_notMem.mpr; intro z v; exact disjoint_left.mp (mem_filter.mp k).2 v (mem_univ z)) x
  rw [Q,hx,mul_one,e]
end YM.CF.Petal
