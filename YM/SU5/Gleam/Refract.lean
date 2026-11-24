import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
import YM.Tree.Cut
/-! # Locate in mesoscopic gauge sector. Pinning ALL trunks is not done adaptively. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
noncomputable section
namespace YM.Gleam
open Function Lattice MeasureTheory Finset RG Wilson Tree Filter Metric
open scoped Matrix.Norms.Frobenius Topology BigOperators ContDiff Classical
variable {c n : Side}{r: Ratio c n}{G:Gauge}{U:Config G n} {x : Site n} {j:Site c} {b : Edge (Site n)}{t:ℝ}
def misdemean (t:ℝ)(U:Config G n) := univ.filter (fun b:Face (Per n)=> t<G.chord (faceValue U b))
def broken (r: Ratio c n) (t:ℝ)(U:Config G n):= halo 10 ((misdemean t U).image fun v=> r.parent v.1)
lemma broken_charge : (broken r t U).card ≤ (misdemean t U).card*21^4 :=(Corona.halo_size ..).trans (Nat.mul_le_mul_right _ (card_image_le))
local notation "W"=> r.count.val
/-- For later use possibly fitting width smaller than any fixed fraction of W. -/
lemma legit (h:j ∉ broken r t U) : Healthy t (halo (W+1) {r.embed j}) U:=by
 apply Finset.disjoint_left.mpr; intro x ht hv; obtain ⟨a,H,G⟩:= halo_spec.mp ht; obtain ⟨z,hz,hh⟩:= (flags_spec ..).1 hv; have he:= Work.E01.sep_touched z x hz; rw [mem_singleton] at H; subst a
 apply h (halo_spec.mpr ⟨r.parent z.1,mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,hh⟩),?_⟩)
 rw [separation_comm]; apply Nat.le_of_mul_le_mul_left  _ r.count.property -- binder?
 have hf:= Corona.foreshorten r (r.embed j) z.1; rw [Ratio.embed_parent] at hf; apply hf.trans; rw [separation_comm]; have hw : 0 < W:= r.count.property; have hx:= separation_triangle z.1 x (r.embed j); rw [separation_comm x _] at hx; change _ ≤ W*10; change separation z.1 (r.embed j)+W ≤ W*10; omega -- rw separation_comm x _ occurrence chain
lemma near_root (r:Ratio c n) {j: Site c} {x: Site n}(h:r.parent x=j) : separation (r.embed j) x ≤ r.count.val:=by rw [←h,separation_comm]; have ht:= Corona.near r x; omega
lemma face_pure {b : Face (Per n)}(p:r.parent b.1∉broken r t U): b∉ misdemean t U:= fun h=> p (halo_subset 10 _ (mem_image_of_mem _ h))
def InHouse (r:Ratio c n) (j:Site c) (b:Edge (Site n)) := r.parent b.1=j ∧ r.parent (b.1+step b.2)=j
private lemma takes (r:Ratio c n)(t:Step){b:Site n}(h:r.parent b=j)(p:r.parent (b+t.vec)=j): InHouse r j (t.used b):=by obtain ⟨t,b'|b'⟩:=t; exact ⟨h,p⟩; exact ⟨(by simpa [Step.used,Step.vec,sub_eq_add_neg] using p),(by simp [Step.used,h])⟩
private lemma capwalk_bound (p:0 ≤ t) (T:Forest r)(X:T.Slice G) (v: j ∉ broken r t (T.drape X))(w:2*(W+1)<n.val): let U:= T.drape X; let D:=4*(t*(1+W)); ∃ g:Site n→G.El, g (r.embed j)=1 ∧ (∀ b : Edge (Site n),r.parent b.1=j → G.chord (Lattice.gauge g U b) ≤ D) ∧ ∀ x,r.parent x=j → G.chord (g x)≤ T.height x* D :=by
 intro U D
 obtain ⟨f,h⟩:= Planned.AtomRegular.Foliage.Cube.anchored _ (legit v) p (subset_refl _) w
 let g:= fun i=> (f (r.embed j))⁻¹ * f i
 have he:g (r.embed j)=1:=by simp [g]
 have hL(b:Edge (Site n))(u:r.parent b.1=j): G.chord (gauge g U b) ≤ D:=by
    rw [show gauge g U b= (f (r.embed j))⁻¹*gauge f U b*((f (r.embed j))⁻¹)⁻¹ by unfold Lattice.gauge g; group,G.chord_conj]; let H:=near_root r u; exact (h b H).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by exact_mod_cast (show 1+separation (r.embed j) b.1 ≤ 1+W from by omega)) p) (by positivity))
 refine ⟨g,he,hL,fun x=> ?_⟩; induction x using Forest.hike.induct T with
 | case2 x Z=>
    intro H; have hx:x=r.embed j:= by rw [←H]; exact Classical.not_not.mp Z
    rw [hx,he,G.chord_one]; unfold D; positivity
 | case1 x hx ih=>
    intro H; have hz:r.parent (x+(T.up x).vec)=j:=(T.stays x hx).trans H; let T' := (T.up x); have h':= takes r T' H hz; let k:=x+T'.vec
    have hg:G.chord (g x*(g k)⁻¹) ≤ D:=by
       have hw:T'.read U x=1:=by unfold Step.read; rw [show U _=1 from T.on_tree X ⟨_,(T.trunk_mem_iff _).mpr ⟨x,hx,rfl⟩⟩]; split_ifs <;> simp
       have hv:=hL _ h'.1; rw [show g x*_=T'.read (Lattice.gauge g U) x from (by rw [Step.gauge_read,hw,mul_one])]; unfold Step.read; split_ifs
       · rw [G.chord_inv]; exact hv
       exact hv
    apply le_trans (b:=G.chord (g x*(g k)⁻¹)+G.chord (g k)); · exact (by simpa using G.chord_triangle (g x*(g k)⁻¹) (g k))
    apply (add_le_add hg (ih hz)).trans; rw [←one_add_mul]; apply mul_le_mul_of_nonneg_right; · exact_mod_cast (show 1+T.height k≤ T.height x from (by have ht:T.height k < T.height x:=T.rise x hx; omega))
    unfold D; positivity
abbrev suitedFee (v:ℕ)(t:ℝ):ℝ:=(8*v+1)*(4*t*(1+v))
lemma suitFee_pos (s:ℕ)(p:0<t): 0< suitedFee s t:=by unfold suitedFee; positivity
lemma purified {T:Forest r}{X:T.Slice G} (p:0 ≤ t) (v: j ∉ broken r t (T.drape X))(w:2*(W+1)<n.val)(f:InHouse r j b): G.chord (T.drape X b) ≤ suitedFee W t:=by
 obtain ⟨g,h,he,hZ⟩:= capwalk_bound p T X v w; let U:= T.drape X; let D:=4*(t*(1+W)); let K:=4*(W:ℝ)
 have hp(i)(v:r.parent i=j):G.chord (g i)≤ K * D:=(hZ i v).trans (mul_le_mul_of_nonneg_right (by unfold K; exact_mod_cast T.bound i) (by positivity))
 let m:= (g b.1)⁻¹ * Lattice.gauge g U b; let l:= b.1+step b.2; have ht: m*g l=U b:=by unfold m l Lattice.gauge; group
 change G.chord (U b) ≤ _; rw [←ht]; apply (G.chord_triangle ..).trans; apply (add_le_add ((G.chord_triangle (g _)⁻¹ _).trans (add_le_add (show G.chord (g b.1)⁻¹ ≤ K*D by rw [G.chord_inv]; exact hp _ f.1) (show _ ≤ D from he b f.1))) (hp _ f.2)).trans_eq ?_
 unfold D K suitedFee; ring
end YM.Gleam
#print axioms YM.Gleam.purified
