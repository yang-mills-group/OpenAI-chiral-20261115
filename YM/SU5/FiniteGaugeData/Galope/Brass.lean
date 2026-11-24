import YM.SU5.FiniteGaugeData.Galope.Allee
/-! # Gauge conditioning without any global slice of Haar
 Even though Hessian price uses a global tree, integrate at *fixed unintegrated links* (essentially bound rather than equality). Use local trunkwise gauge choice independently on all tiles; enough for upper. Trunk links of local trees have time coord at center OR are vertical. Hence truly given, with wraps OK!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 600000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle Avenue
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge}{M k w i:ℕ}{Z:Finset (Site n)}{o:Site n}
namespace Press
open Beamer
lemma envelope {s:Cover}(p:s≠0)(h:s∈box M): ∃ (d:Axis)(y:Cover), street y<street s∧ y∈box M ∧ ((s=y+step d ∧ trunk y d)∨(y=s+step d∧ trunk s d)):=by
 let i:=Spindle.last s p; have hi:=last_has s p
 have ht: trunk s i:= last_clear s p
 obtain hp|hv:=lt_or_gt_of_ne (show s i≠0 from hi)
 · refine ⟨i,s+step i,?_,?_, Or.inr ⟨rfl,ht⟩⟩
   · have he: street (s+step i)+1= street s:=by rw [← mirror_road s, ← mirror_road (s+_), neg_add, ← sub_eq_add_neg]; exact once_road _ (by exact neg_pos.mpr hp)
     omega
   obtain ⟨u,v⟩:=box_test.mp h; rw [box_test]; constructor <;> intro j <;> have he:=u j <;> have hh:=v j <;> (by_cases p':j=i; subst j; simp only [Pi.add_apply,step_apply,↓reduceIte]; omega; simp only [Pi.add_apply,step_apply,if_neg p',add_zero]; assumption) -- tune
 refine ⟨i,s-step i,by have he:=once_road s hv; omega,?_,Or.inl ⟨(sub_add_cancel s (step i)).symm,?_⟩⟩
 · obtain ⟨u,v⟩:=box_test.mp h; rw [box_test]; constructor <;> intro j <;> have he:=u j <;> have hh:=v j <;> (by_cases p':j=i; subst j; simp only [Pi.sub_apply,step_apply,↓reduceIte]; omega; simp only [Pi.sub_apply,step_apply,if_neg p',sub_zero]; assumption)
 intro j q; simp only [Pi.sub_apply,step_apply,if_neg (ne_of_gt q),sub_zero,ht _ q]
lemma walk_unit{U:CoverConfig G}(i:Axis)(s:Cover)(h:trunk s i): leaves U s * U (s,i)= leaves U (s+step i):= mul_inv_eq_one.mp (vertical U s i h) -- tune
lemma trunk_ranks (V W:CoverConfig G)(p:∀ x∈box M,∀ a, trunk x a→x+step a∈box M→V (x,a)=W (x,a)):∀ x∈box M, leaves V x=leaves W x:=by
 intro x t; induction n0:street x using Nat.strong_induction_on generalizing x with
 | _ k ih=>
   by_cases h:x=0; · simp [h,leaves,travel]
   obtain ⟨a,y,hv,q,h'⟩:=envelope h t; have he:= ih _ (n0 ▸ hv) y q rfl; rcases h' with ⟨h',g⟩|⟨h',g⟩
   · rw [h',←walk_unit a y g, ←walk_unit a y g, he,p _ q a g (h' ▸ t)]
   rw [h', ←walk_unit a x g,←walk_unit a x g,p x t a g (h' ▸ q)] at he; exact mul_right_cancel he
local notation "θ" => timeAxis
lemma trunk_buried (V W:Config G n)(u:k≤M)(v:Z ⊆ zones n M)(h:o∈Z)(p:∀ x:Edge (Site n), x ∉ buy Z k → V x=W x)(x:Cover)(htt:x∈ box M)(a:Axis)(ht:trunk x a): expandAt o V (x,a)=expandAt o W (x,a):=by -- tune
 apply p; intro hh; obtain ⟨i,hi,hx⟩:= mem_biUnion.mp hh; obtain ⟨g,v'⟩:= mem_product.mp hx; obtain ⟨q,e⟩:=mem_filter.mp g; have hm:i=o:= no_double (v hi) (v h) (patch_includes k M u i q) (village_le x ‹x∈box M›); subst i; apply e; have hp:=mem_erase.mp v'; change (x θ:Per n)+o θ=o θ; simp only [ht θ (time_n (show a≠θ from hp.1)),Int.cast_zero,zero_add]
lemma hinge (V W:Config G n)(u:k≤M)(v:Z ⊆ zones n M)(h:o∈Z)(p:∀ x:Edge (Site n), x ∉ buy Z k → V x=W x)(x: Site n)(t:x∈ Spindle.patch M o): fingers V o x=fingers W o x:= trunk_ranks (expandAt o V) (expandAt o W) (fun x q a s _=> trunk_buried V W u v h p _ q a s) _ (Work.E08.lift_mem_box ((doors x).1 t)) -- tune
lemma pitchB (V W:Config G n)(u:k≤M)(v:Z ⊆ zones n M)(h:o∈Z)(p:∀ x:Edge (Site n), x ∉ buy Z k → V x=W x)(x:Edge (Site n))(he:x∈ Room o M) : gauge (fingers W o) V x=spine V o x:=by
 obtain ⟨h1,h2⟩:= (mem_filter.mp he).2; unfold spine Lattice.gauge; rw [←hinge V W u v h p _ h1,←hinge V W u v h p _ h2]
lemma uprise {A:Finset (Face (Per n))}(p:o∈glow A M)(i:Site n)(y:PlaqAxes) (h:i∈Spindle.patch M o): (i,y)∉A:= fun h1=> (mem_sdiff.mp p).2 (mem_filter.mpr ⟨(mem_sdiff.mp p).1, ⟨(i,y),h1,h⟩⟩) -- tune
def balanceX(M:ℕ)(s:ℝ):=4*M*s
lemma flatB (V W:Config G n){A:Finset (Face (Per n))} (v:Z ⊆ glow A M) (h:o∈Z)(t:2*(M+1)<n.val)(u:k≤M)(p:∀ x:Edge (Site n), x ∉ buy Z k→ V x=W x) (δ:ℝ) (hp:0≤δ)(z: ∀ i:Face (Per n), i ∉ A→ G.chord (faceValue V i)≤δ)(x:Edge (Site n))(he:x∈ Room o M): G.chord (gauge (fingers W o) V x)≤ balanceX M δ:=by
 rw [pitchB V W u (Subset.trans v (glow_in ..)) h p x he]; let y:Dim o M:=⟨x,he⟩; rw [show x=y.val from rfl, spun V o t y]
 apply (played_cost _ _ hp (fun i=>?_)).1.trans (mul_le_mul_of_nonneg_right _ hp); · exact_mod_cast lengths_word G t y
 rw [registering M V t]; unfold spine; rw [face_gauge, G.chord_conj]; exact z _ (uprise (v h) (wrap n i.val.1 +o) i.val.2 (Spindle.village_le _ (faceOrigin i)))

-- combine gauges into a SINGLE purchase on all disjoint patches, for affine completion using SAME log coordinate on all sets. Off patches arbitrary.
def mapA (W:Config G n)(Z:Finset (Site n))(M:ℕ)(i:Site n): G.El:= if h: ∃ o∈ Z, i∈ Spindle.patch M o then fingers W (Classical.choose h) i else 1
lemma map_inside (W:Config G n)(v:Z⊆ zones n M)(h:o∈Z)(i:Site n)(p:i∈ Spindle.patch M o): mapA W Z M i= fingers W o i:=by
 let hx: ∃ o∈Z,i∈ Spindle.patch M o:=⟨o,h,p⟩; obtain ⟨q,r⟩:= Classical.choose_spec hx; rw [mapA,dif_pos hx,no_double (v q) (v h) r p]
lemma kits (W:Config G n)(v:Z⊆ zones n M)(h:o∈Z)(i:Edge (Site n))(p:i∈ Room o M)(V:Config G n): gauge (mapA W Z M) V i=gauge (fingers W o) V i:=by unfold Lattice.gauge; obtain ⟨e,e'⟩:=(mem_filter.mp p).2; rw [map_inside W v h _ e,map_inside W v h _ e']
lemma cargoF (V W:Config G n){A:Finset (Face (Per n))} (v:Z ⊆ glow A M) (h:o∈Z)(t:2*(M+1)<n.val)(u:k≤M)(p:∀ x:Edge (Site n), x ∉ buy Z k→ V x=W x) (δ:ℝ) (hp:0≤δ)(z: ∀ i:Face (Per n), i ∉ A→ G.chord (faceValue V i)≤δ)(x:Edge (Site n))(hx:x∈ Room o M): G.chord (gauge (mapA W Z M) V x)≤ balanceX M δ:=by rw [kits W (Subset.trans v (glow_in ..)) h _ hx V]; exact flatB V W v h t u p δ hp z x hx
lemma inRoom {x:Edge (Site n)}(p:x∈ slab o k)(h:k<M): x∈ Room o M:=by
 have hx:= (mem_filter.mp (mem_product.mp p).1).1; have hv: separation x.1 (x.1+step x.2) ≤ 1:= ?_; swap; · rw [separation_comm]; unfold separation; rw [add_sub_cancel_left]; exact pdist_step _
 exact mem_filter.mpr ⟨mem_univ _,patch_includes _ _ h.le _ hx,patch_includes _ _ (show k+1≤M from h) _ (Avenue.extend o x.1 _ hv hx)⟩
end Press
end YM.SU5.FiniteGaugeData.Galope
