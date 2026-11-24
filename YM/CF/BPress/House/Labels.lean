import YM.CF.BPress.Hazel.Atrium
import YM.CF.BPress.Locale.Minty
/-! specialized to post-fix gauge only. Local face readings.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.House
open RG Wilson Push.SectorMeasure MeasureTheory LocalH Lattice Cube Bands Locale Hazel Wealth Letters Net Grid Finset Function SU Mag Branch
open scoped Classical Topology BigOperators
variable {s:Side}{B:BandWidth}(A:Bands s B)(R:Hangar s)
abbrev BlockY := SiteX A R
abbrev Emblem := Bool × Fin 5
abbrev Bank := Patio R→ Emblem
abbrev Old := Seal A.Hcols × (A.Hcols→ Fin 5)
def battered(v:Bank R) : Seal (Patio R):= univ.filter fun i=> (v i).1
def background (j:Fin 5) : Bank R := fun _=> (false,j) -- namespace.House tune

def gather {E:Type*} (w: BlockY A R → Patio R → E)(x:A.Hcols) : E:= w (own A R x) (packB R x.2)
def beset(v:BlockY A R→ Bank R) : Old A:= (univ.filter fun i=> (gather A R v i).1,fun i=> (gather A R v i).2)
def setBank (x: Old A)(b:BlockY A R): Bank R:= fun i=>let u:=porch A R b i; (decide (u∈x.1),x.2 u)
@[simp] lemma gather_p {E: Type*} (g:BlockY A R→ Patio R→ E)(t:BlockY A R)(i:Patio R): gather A R g (porch A R t i)=g t i:=by rw [gather,porch_own,pack_p]
lemma gather_ζ {E: Type*} (g:A.Hcols→E)(i:A.Hcols): gather A R (fun x i=>g (porch A R x i)) i=g i:= congrArg g ((lodge A R).left_inv i)
@[simp] lemma setB_score (x: Old A)(i: A.Hcols): gather A R (setBank A R x) i= (decide (i∈x.1), x.2 i):= gather_ζ A R (fun i=>(decide _,x.2 i)) i
lemma beset_me (u)(i:A.Hcols): i∈ (beset A R u).1 ↔ (gather A R u i).1=true:=by simp [beset]
def bankUp : (BlockY A R→ Bank R)≃ Old A where
 toFun v:= beset A R v; invFun x:=setBank A R x
 left_inv v:=by funext i x; simp only [setBank,beset,mem_filter,mem_univ,true_and,gather_p]; simp
 right_inv x:=Prod.ext (by ext1 i; simp only [beset_me,setB_score,decide_eq_true_eq]) (funext fun i=> congrArg Prod.snd (setB_score A R x i))
-- one parameter per gap (already index = Mag.center code). name lookup is via Hazel. orientation.
def flash (x:A.Hcols→ Fin 5) : A.Slates:=fun i=> if i∈A.dc then 0 else (fun k=> x (i-1,k), fun k=>x (i,k))
def dream (A:Bands s B)(w:A.Slates) := ∀ i∈A.dc,w i=0
lemma flash_day (x:A.Hcols→ Fin 5) : dream A (flash A x):= fun _ b=> if_pos b
lemma flash_code (x:A.Hcols→ Fin 5) : code A (flash A x)=x:=by
 funext i; obtain ⟨i,v⟩:=i; by_cases h:i∈ A.dc; swap; · change orientation A _ i v=_; rw [orientation_right A _ h,flash,if_neg h]
 have ht:i+1∉ A.dc:= fun v=> (A.prev_next i|>.mp ((A.dc_index (i+1)).1 v)) ((A.dc_index i).1 h); change orientation A _ i v=_; rw [orientation,if_pos h, flash,if_neg ht,add_sub_cancel_right] -- tune
lemma dreaming (w:A.Slates)(h:dream A w): flash A (code A w)=w:=by
 funext i; unfold flash; split; exact (h _ ‹_›).symm; next t=> apply Prod.ext <;> dsimp only [code]; exact (orientation_left A _ t); exact (orientation_right A _ t) -- tune ellipsis
variable (T: Sheet.Atlas) (y:ℝ)(U:Micro s)
lemma coastIndex {v:A.Slates}(h:v∈A.permit T y U): dream A v:=fun i u=> by have he:= (Fintype.mem_piFinset.mp h) i; rw [A.choices_D _ _ _ u] at he; exact mem_singleton.mp he
-- encode local permit in only this gap theta. atom predicates of x, two neighbors for gradient test.
def TagGoal (v:A.Hcols→ Fin 5)(i:A.Hcols):Prop:= let W:=Letters.window A U i.1; T.passes y W i.2∧ ∀ j: SpatialDir, group.chord (T.give y W i.2 (v i)*W (i.2,j)*(T.give y W (hop i.2 j 1) (v (i.1,hop i.2 j 1)))⁻¹)≤ sigmaN y
lemma Tag_allow (v:A.Hcols→ Fin 5)(i:A.Index): let W:=Letters.window A U i; T.allowed y W (T.frame y W (fun x=>v (i,x))) ↔ ∀ x, TagGoal A T y U v (i,x):=by
 intro W; constructor; exact fun t x=>⟨(t.1 x).1,fun j=>t.2 (x,j)⟩; intro h; refine ⟨fun x=> ⟨(h x).1,T.frame_pick y _ W x⟩,fun x=>(h x.1).2 x.2⟩ -- tune glide
lemma left_m (x:A.Hcols→ Fin 5){k:A.Index}(h:k∈A.nc): (T.frame y (((A.mark k).reads U).1) (flash A x k).1)= T.frame y (Letters.window A U (k-1)) (fun u=> x (k-1,u)):=by change T.frame y (horizontal _ U) _=_; rw [Letters.window,left_shadow h,flash,if_neg (mem_sdiff.mp h).2]
lemma choice_tag {k:A.Index}(h:k∉A.dc)(x:A.Hcols→ Fin 5): flash A x k∈ A.choices T y U k ↔ (∀ i, TagGoal A T y U x (k-1,i))∧∀ i, TagGoal A T y U x (k,i):=by
 simp only [choices,flash,if_neg h,mem_product]; have hb:= Tag_allow A T y U x (k-1); have ht:= Tag_allow A T y U x k; dsimp only at ht hb; simp only [←hb,←ht,Sheet.Atlas.room_ok]; have g : k∈A.nc:= mem_sdiff.mpr ⟨mem_univ _,h⟩; unfold Letters.window; rw [left_shadow g,right_shadow g]; exact Iff.rfl -- uses Tag_allow let binder rw
lemma awake (x:A.Hcols→ Fin 5):flash A x∈A.permit T y U ↔ ∀ i, TagGoal A T y U x i:=by
 constructor
 · intro v i; obtain ⟨i,j⟩:=i; by_cases t:i∈A.dc; swap; · exact ((choice_tag A T y U t x).1 (Fintype.mem_piFinset.mp v i)).2 j
   have ht:i+1∉ A.dc:=fun v=> (A.prev_next i|>.mp ((A.dc_index (i+1)).1 v)) ((A.dc_index i).1 t); have p:= ((choice_tag A T y U ht x).1 (Fintype.mem_piFinset.mp v _)).1 j; simpa using p -- orientation
 intro h; refine Fintype.mem_piFinset.mpr fun i=>?_ ; by_cases t:i∈ A.dc; rw [A.choices_D _ _ _ t]; exact mem_singleton.mpr (flash_day A x i t); apply (choice_tag A T y U t x).2; exact ⟨fun _=>h _,fun _=>h _⟩ -- tune
lemma bank_sum (f:A.Slates→ℂ): (∑ i∈A.permit T y U,f i)= ∑ i:A.Hcols→ Fin 5,if (flash A i)∈A.permit T y U then f (flash A i) else 0:=by -- tune ambig remove
 symm; apply Eq.trans _ (show (∑ i∈ univ.filter (fun i:A.Hcols→Fin 5=> flash A i∈A.permit T y U), f (flash A i))=_ from ?_); · simp only [Finset.sum_filter]; apply sum_congr rfl; intro i _; by_cases t:flash A i∈ A.permit T y U <;> simp [t]
 apply sum_bij (fun i _=> flash A i); · intro i v; exact (mem_filter.mp v).2
 · intro i _ j _ v; rw [← flash_code A i,v,flash_code]
 · intro i v; have ht:= dreaming A i (coastIndex A T y U v); exact ⟨code A i,mem_filter.mpr ⟨mem_univ _,ht.symm ▸ v⟩,ht⟩
 intro i _; rfl
end YM.CF.BPress.House
