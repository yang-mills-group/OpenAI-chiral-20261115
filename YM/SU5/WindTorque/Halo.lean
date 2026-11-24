import YM.CF.Buffered.Probes
import YM.Extra.ITERATION_NO_LOSS.Atoms
import YM.Work.E01
/-! # reprise of Silk/Span/Rapt on gauge projection masker of WB.
Same core 10 and piece extension. Storage on the cover even at short periods. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.EmberWind
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Fock
attribute [local instance] opCStarAlgebra
def skyDeck (X:Cover)(r:ℕ):Finset Cover := (Lattice.box r).image (·+X)
lemma pav_v (X Y:Cover)(r:ℕ): Y∈ skyDeck X r ↔ ∀ i:Axis, X i - r ≤ Y i ∧ Y i ≤ X i + r:=by
 constructor
 · rintro p; obtain ⟨v,u,rfl⟩:= mem_image.mp p
   intro i; have ht:=(box_test.mp u).1 i; have hp:=(box_test.mp u).2 i
   change X i- r ≤ v i + X i ∧ v i + X i ≤ X i + r; omega
 intro p; refine mem_image.mpr ⟨Y-X,box_test.mpr ⟨fun i=> ?_,fun i=> ?_⟩,sub_add_cancel ..⟩
 all_goals specialize p i; simp only [Pi.sub_apply]; omega
lemma walk_pav (x y:Cover)(w:Walk)(h:y∈visits x w):y∈ skyDeck x w.length:=by
 have he:= Extra.Iteration.along_size x y w h; rw [pav_v]; intro i
 have hp: (y i-x i).natAbs≤ w.length := (single_le_sum (s:=univ) (f:=fun k:Axis=>(y k-x k).natAbs) (fun j _=> Nat.zero_le _) (mem_univ i)).trans he; omega
lemma span_walk (x o u:Cover)(r:ℕ)(w:Walk)(p:x∈ skyDeck o r)(t:u∈ visits x w):u ∈ skyDeck o (r+w.length):=by rw [pav_v]; intro i; have hp:=(pav_v ..).1 (walk_pav x u w t) i; have ht:=(pav_v ..).1 p i; omega
lemma wrap_pav (N:Side)(X:Cover)(r:ℕ): (skyDeck X r).image (wrap N)= halo r {wrap N X}:=by
 ext x; rw [mem_image, halo_spec]; constructor
 · rintro ⟨y,h,rfl⟩; obtain ⟨y,v,rfl⟩:= mem_image.mp h; refine ⟨_,mem_singleton_self _,?_⟩; rw [map_add,separation_comm,separation,add_sub_cancel_right]; exact Work.E01.pdist_wrap_le v
 rintro ⟨y,p,u⟩; rw [mem_singleton.mp p,separation_comm] at u; let z:=wrap N X; let a:= Lattice.lift (x-z)
 have ht(i):-(r:ℤ) ≤ a i ∧ a i ≤ r:=by have hx:(a i).natAbs ≤ r:=(component_le _ i).trans u; omega
 exact ⟨a+X,mem_image_of_mem _ (box_test.mpr ⟨fun i=>(ht i).1,fun i=>(ht i).2⟩), by unfold a; rw [map_add,Lattice.wrap_lift]; exact sub_add_cancel ..⟩
lemma tours_paid (x:Cover)(w:Walk)(n:Side): (visits x w).map (wrap n)=visits (wrap n x) w:=by induction w generalizing x with|nil=>simp [visits]|cons s w p=>simp [visits,p,map_add,wrap_vec]
lemma stroll (x v:Cover)(w:Walk):visits (x+v) w=(visits x w).map (· + v):=by induction w generalizing x with|nil=>simp [visits]|cons i w ih=> simp only [visits,List.map_cons]; congr 1; rw [add_right_comm,ih]

-- compact receipts for all incident squares in the unwrapped mesh
def visa (p:Face ℤ):Finset Cover := (visits p.1 (square p.2.val.1 p.2.val.2)).toFinset
def voyageD (r:ℕ)(X: Cover):Finset (Face ℤ) := ((skyDeck X (r+4)) ×ˢ (univ:Finset PlaqAxes)).filter (fun p=> ¬ Disjoint (skyDeck X r) (visa p))
private lemma nearplus (x y p : ℤ)(r : ℕ) (h:x-r ≤ y ∧ y ≤ x+r)(z:p-4≤y ∧ y≤p+4) : x-(↑(r+4):ℤ)≤p ∧ p≤x+↑(r+4):=by omega
private lemma backtown {r s:ℕ} (x y z:Cover)(w:Walk)(l:w.length=s)(hs:z∈ visits y w)(hv:z∈skyDeck x r): y∈ skyDeck x (r+s):=by
 have ht:= (walk_pav y z w hs); exact (pav_v ..).2 fun a=>by obtain ⟨k,v⟩:= (pav_v ..).1 ht a; obtain ⟨b,c⟩:= (pav_v ..).1 hv a; rw [l] at *; omega
private lemma backclock {r:ℕ} (X:Cover)(p:Face ℤ)(i:Cover)(v:i∈ skyDeck X r)(h:i∈ visa p): p.1∈ skyDeck X (r+4):= backtown X p.1 i (square p.2.val.1 p.2.val.2) (r:=r) (s:=4) rfl (List.mem_toFinset.mp h) v
private lemma sailClock {r:ℕ} (X:Cover)(p:Face ℤ)(h:¬ Disjoint (skyDeck X r) (visa p)):p.1∈skyDeck X (r+4):=by
 let s:= not_disjoint_iff.mp h; exact backclock X p s.choose s.choose_spec.1 s.choose_spec.2
lemma voy{r:ℕ} (X:Cover)(p:Face ℤ) : p∈ voyageD r X ↔ ¬ Disjoint (skyDeck X r) (visa p):=by
 constructor; exact fun t=>(mem_filter.mp t).2
 rintro v; exact mem_filter.mpr ⟨mem_product.mpr ⟨sailClock X p v,mem_univ _⟩,v⟩
lemma voy_sites {r:ℕ}(X:Cover)(p:Face ℤ)(h:p∈ voyageD r X): visa p ⊆ skyDeck X (r+4+4):= fun y hy=> span_walk p.1 X y (r+4) (square p.2.val.1 p.2.val.2) (show p.1∈ skyDeck X (r+4) from (mem_product.mp (mem_filter.mp h).1).1) (List.mem_toFinset.mp hy)
lemma visa_wrap (p:Face ℤ)(n:Side): (visa p).image (wrap n)=touched ((wrap n) p.1,p.2):=by unfold visa touched; rw [← tours_paid]; ext x; simp
lemma stamp_wrap (r:ℕ)(X:Cover)(n:Side)(p:Face (Per n)): (∃ i∈ voyageD r X, (wrap n i.1,i.2)=p) ↔ ¬ Disjoint (halo r {wrap n X}) (touched p):=by
 constructor
 · rintro ⟨i,h,rfl⟩; have hd:= (voy (r:=r) X i).1 h; let P:=skyDeck X r; let Vx:=visa i; change ¬Disjoint P Vx at hd
   obtain ⟨x,u,v⟩:= not_disjoint_iff.mp hd; rw [←visa_wrap i,←wrap_pav]; exact not_disjoint_iff.mpr ⟨wrap n x,mem_image_of_mem _ u, mem_image_of_mem _ v⟩
 rw [← wrap_pav]; intro g; obtain ⟨x,h,t⟩:=not_disjoint_iff.mp g; obtain ⟨x,u,rfl⟩:=mem_image.mp h
 let y:=Lattice.lift p.1; have hp: (wrap n y,p.2)=p:=Prod.ext (wrap_lift _) rfl
 let P:Face ℤ:= (y,p.2); have ht:wrap n x∈ (visa P).image (wrap n):=by rw [visa_wrap,show (wrap n P.1,P.2)=p from hp]; exact t
 obtain ⟨v,w,r0⟩:=mem_image.mp ht
 let L:Face ℤ := (y+(x-v),p.2); have hr:wrap n (x-v)= 0 := by rw [map_sub,r0,sub_self]
 refine ⟨L,(voy (r:=r) X L).2 ?_,?_⟩
 · let P:=skyDeck X r; let Vx:=visa L; change ¬ Disjoint P Vx; apply Finset.not_disjoint_iff.mpr; refine ⟨x,u,?_⟩
   change x∈ (visits (y+(x-v)) (square _ _)).toFinset; rw [stroll,List.mem_toFinset]; exact List.mem_map.mpr ⟨v,List.mem_toFinset.mp w,by abel⟩
 unfold L; simp only [map_add,hr,add_zero]; exact hp

def landingC (r:ℕ)(x: Cover)(T:ℝ)(U:LinksC):Prop:=∀ i∈ voyageD r x,SU.group.chord (faceValue U i)<T
lemma land_wrap (r:ℕ)(n:Side)(U:Pane n)(x:Cover)(T:ℝ): landingC r x T (onC _ U)↔ pingS T (halo r {wrap (More n) x}) U:=by
 let v:=wrap (More n)
 have hp(i:Face ℤ) : faceValue (onC _ U) i=faceValue U (v i.1,i.2):=by unfold onC faceValue; rw [travel_at]; simp [v]
 constructor
 · intro t p h; obtain ⟨p,u,rfl⟩:= (stamp_wrap r x (More n) p).2 h; rw [← (hp p)]; apply t p; exact u
 intro t p h; rw [hp]; exact t _ ((stamp_wrap ..).1 ⟨p,h,rfl⟩)

lemma voyage_local {r:ℕ}(p:Cover)(T:ℝ)(x y:LinksC)(h:Agrees (skyDeck p (r+4+4)) x y):landingC r p T x↔ landingC r p T y:=by
 unfold landingC; apply forall_congr'; intro a; apply forall_congr'; intro k
 have hx:faceValue x a=faceValue y a:= travel_local _ _ _ _ fun i v w=>h i (voy_sites _ a k (List.mem_toFinset.mpr v)) (voy_sites _ a k (List.mem_toFinset.mpr w)); rw [hx]
lemma land_meas (r:ℕ)(x:Cover)(t:ℝ): MeasurableSet (setOf (landingC r x t)):=by
 apply IsOpen.measurableSet; rw [show setOf (landingC r x t)=⋂ i:(voyageD r x),{U:LinksC| SU.group.chord (faceValue U i.val)< t} from ?_]; exact isOpen_iInter_of_finite fun _=> isOpen_lt (SU.group.continuous_chord.comp (continuous_travel _ _)) continuous_const
 ext; simp [landingC]
lemma maskExpel (o:Cover)(x y:ℕ)(n:Side): Lattice.halo y (halo x {wrap n o})=halo (x+y) {wrap n o}:=by
 let T (r):= skyDeck o r; let a:=wrap n o; let U (r):= halo r {a}
 apply Subset.antisymm
 · intro i p; obtain ⟨j,v,l⟩:=halo_spec.mp p; obtain ⟨h,t,q⟩:=halo_spec.mp (show j∈ U x from v); exact halo_spec.mpr ⟨_,t,(separation_triangle h j i).trans (add_le_add q l)⟩
 rw [←wrap_pav]; intro i p; obtain ⟨i,v,rfl⟩:=mem_image.mp p
 let j:Cover:=fun a=>max ((o a)-(x:ℤ)) (min ((o a)+(x:ℤ)) (i a)); have he:T x=(T x):=rfl
 have ht:j∈ T x ∧ i∈ skyDeck j y:=by
    have hν(k):= (pav_v ..).1 v k; constructor
    · refine (pav_v ..).2 fun i=>?_; unfold j; omega
    refine (pav_v ..).2 fun i=>?_ ; specialize hν i; unfold j; omega
 apply halo_spec.mpr; rw [←wrap_pav n o]; refine ⟨wrap n j,mem_image_of_mem _ ht.1,?_⟩; have hv:wrap n i ∈ halo y {wrap n j}:=(wrap_pav n j y) ▸ mem_image_of_mem _ ht.2; simpa [halo_spec] using hv
lemma pav_mono {o:Cover}{r s:ℕ} (h : r ≤ s) : skyDeck o r ⊆ skyDeck o s:=fun i v=> (pav_v ..).2 fun j=>by obtain ⟨e,k⟩:=(pav_v ..).1 v j; omega
lemma owns(o:Cover) (r:ℕ): o∈ skyDeck o r:= (pav_v ..).2 fun i=>by omega
end YM.CF.Buffered.EmberWind
#print axioms YM.CF.Buffered.EmberWind.land_wrap
#print axioms YM.CF.Buffered.EmberWind.maskExpel
