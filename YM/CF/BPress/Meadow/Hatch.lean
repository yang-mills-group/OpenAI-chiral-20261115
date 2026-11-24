import YM.CF.BPress.Meadow.Plant
/-! §lem:B-moX interpolation, buys fixed spare. Actually invoked twice with two different target extensions, inside N and in the Guard field. Threshold & size licensed independently. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Finset Filter NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Dial Grid Grid.Entity Delivery Lute.Kite MeasureTheory RG
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {s:Side} {k:Tiling s}(p:k.r=1)
abbrev leaf:ℝ:= (build Zips (1:ℝ) zero_le_one).choose
lemma leaf_one:1≤leaf:= (build Zips (1:ℝ) zero_le_one).choose_spec.1
abbrev seedC(k:Tiling s):= ((build Zips (1:ℝ) zero_le_one).choose_spec.2 s k)
def penB(k:Tiling s):= (seedC k).choose
abbrev Holder (S T:Support s):= T⊆S
variable (k)
def tree (S T: Support s)(U:Micro s)(V:marks s): marks s:= penB k (matsN k S) (matsN k T) (moss S U,crop S V)
lemma tree_m (S T: Support s) : Measurable fun U:Micro s×marks s=> tree k S T U.1 U.2:=((seedC k).choose_spec.2.1 ..).comp (((moss_m _).comp measurable_fst).prodMk ((crop_m _).comp measurable_snd)) -- tune
lemma tree_identical (S S' T T':Support s)(U U':Micro s)(v v':marks s): S=S'→T=T'→Set.EqOn U U' (inside S)→ Set.EqOn v v' S→ tree k S T U v=tree k S' T' U' v':=by
 rintro rfl rfl h t; unfold tree; have hx:moss S U=moss S U':=by funext i; unfold moss; split; exact h ‹_›; rfl
 have he:crop S v=crop S v':=by funext i; unfold crop; split; exact t ‹_›; rfl
 rw [hx,he] -- unused? export

variable {k} {S T:Support s}(U:Micro s)(H:marks s)
abbrev soil (r:Side):= (r.val:ℝ)⁻¹
abbrev climate (r:Side):= ((r.val:ℝ)^2)⁻¹
abbrev inheritance (r:Side):= leaf/r.val
variable (Q:T⊆S) (t:Rings U S (climate k.b)) (e:Alert U T H (soil k.b))
include p Q t e
lemma seeds : (∀ I∈matsN k S,Zips.Speed I (moss S U) (tree k S T U H) leaf) ∧ ∀ I∈matsN k T, ∀ i∈I.hull,(tree k S T U H) i=H i:=by
 let A:=matsN k T; let Z:=matsN k S
 obtain ⟨D,F,V⟩:= (seedC k).choose_spec.1 Z A (graded T k) (graded S k) (fun i h=> (mat_since ..).2 (((mat_since ..).1 h).trans Q)) (moss S U) (crop S H) (fun i h=>valid_curvature i U p ((mat_since ..).1 h) t) (fun i h=>hold i _ T p H Q ((mat_since ..).1 h) (by rw [one_div]; exact e)) -- tune
 refine ⟨fun i h=> D i h (by simpa using card_le_univ i.axes),fun i h x s=>?_⟩; obtain ⟨x,v,rfl⟩:= (hullin ..).1 s; exact (F i h x v).trans (if_pos (Q (((mat_since ..).1 h) s)))
lemma plants (J:Entity k 4)(a:Coord 4)(i:Axis)(h:J.Valid (tick a i))(u:J.hull⊆S): urgent U (J.heart a,i) (tree k S T U H) ≤ inheritance k.b := by
 rw [← speed_normal J U p _ u h]; exact ((seeds p U H Q t e).1 J (mat_since ..|>.mpr u)) a i h
omit Q t e
include p in
lemma city (x:Site s):x∈mesh k.r.val:=by rw [p]; intro i; exact one_dvd _
abbrev cloakT(k:Tiling s):= 2*k.R
lemma centerB {x:Site s}(J:Entity k 4)(u:x∈J.hull): J.hull ⊆ halo (cloakT k) {x}:=by
 intro y w; have ht(y:Site s) (h:y∈J.hull): delta J.origin y≤k.R:= by obtain ⟨a,t,rfl⟩:= hullin ..|>.1 h; exact J.span t
 refine halo_spec.mpr ⟨x,mem_singleton_self _,?_⟩; apply (delta_triangle x J.origin y).trans; rw [delta_comm x]; exact (Nat.add_le_add (ht _ u) (ht _ w)).trans (two_mul k.R|>.symm.le) -- tune
include Q t e
lemma tree_urgent (x:Site s)(i:Axis)(v: halo (cloakT k) {x} ⊆ S): urgent U (x,i) (tree k S T U H) ≤ inheritance k.b:=by obtain ⟨J,a,b,h⟩:= mesh_coord k (city p x); rw [←b]; exact plants p U H Q t e _ _ _ (h i).1 ((centerB p J (x:=x) (b ▸ hull_heart J a (h i).2.2)).trans v)
lemma tree_eq (x:Site s)(v:halo (cloakT k) {x}⊆T) : tree k S T U H x= H x:=by obtain ⟨J,a,b,h⟩:=mesh_coord k (city p x); have ht:x∈J.hull:= b ▸ hull_heart J a (h 0).2.2; exact (seeds p U H Q t e).2 J (mat_since ..|>.mpr ((centerB p J ht).trans v)) x ht
omit Q t e in
lemma tree_read (A B:Support s)(V:Micro s)(G:marks s)(x:Site s): let Y:=halo (9*k.R) {x}; (∀ y∈Y,(y∈ S↔ y∈ A)∧(y∈T↔ y∈B)) → (∀ i:Link s, i.1∈Y→ moss S U i=moss A V i) →(∀ i∈Y,crop S H i=crop A G i) → tree k S T U H x=tree k A B V G x:=by
 intro Y h w v; let n:=4*(2*k.R); have he(j)(t:delta x j≤ 9*k.R):j∈Y:=halo_spec.mpr ⟨x,mem_singleton_self _,t⟩; refine (seedC k).choose_spec.2.2 (matsN k S) (matsN k T) _ _ _ _ x (city p x) (fun D d=>?_) (fun i u t=>w _ (he _ (by omega))) (fun j _ t=>v _ (he _ (by omega))) -- tune
 have hv(j: Site s) (t:j∈ D.hull): j∈Y:= by apply he; obtain ⟨j,p,e⟩:=hullin ..|>.mp t; rw [←e]; refine (delta_triangle x D.origin _).trans ?_; exact (Nat.add_le_add d (D.span p)).trans (by omega)
 rw [mat_since,mat_since]; -- tune
 -- simp all
 simp only [mat_since]; exact ⟨⟨fun p i u=>(h _ (hv _ u)).1.mp (p u),fun p i u=>(h _ (hv _ u)).1.mpr (p u)⟩,⟨fun p i u=>(h _ (hv _ u)).2.mp (p u),fun p i u=>(h _ (hv _ u)).2.mpr (p u)⟩⟩

-- prices purchased independently
omit p Q t e
structure Soil (r:Side) (ε:ℝ): Prop where
 slow : inheritance r ≤ ε
lemma find_s {ε:ℝ}(u:0<ε): ∃ r:Side,Soil r ε:=by
 obtain ⟨n,v⟩:=exists_nat_gt (leaf/ε); refine ⟨⟨n+1,by omega⟩,⟨?_⟩⟩; change leaf/↑(n+1) ≤ _; rw [div_le_iff₀ (by positivity)]; push_cast; exact le_of_lt (by nlinarith [(div_lt_iff₀ u).mp v])
structure Record (r s:Side):Prop where
 divides:r.val∣s.val
 large:r.val<s.val
def Record.key {r s} (H: Record r s): Tiling s:=⟨1,r,by rw [one_mul]; exact H.divides,by rw [one_mul]; exact H.large⟩
lemma Record.K {r s}(H:Record r s):H.key.R=r.val:=one_mul _
end YM.CF.BPress.Meadow
