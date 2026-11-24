import YM.CF.BPress.Hazel.Atlas
/- N collar amendment. Before any activation taper. Uniform costs across depth- & parameter change. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Hazel
open Function Finset Filter NormedSpace Metric SU SU.Pair Lat Fock Lattice Cube Spin Spin.Paint Dial Lute Lute.Kite Lute.Fort Lute.Music Meadow MeasureTheory Net Meadow.Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ContDiff Classical
attribute [local instance] opCStarAlgebra
variable {s :Side}{B:BandWidth} (z: Fin 5)
open Grid Wealth Tunnel Locale Bands Branch Clipγ Letter
variable {X:Bands s B}{T W :Rental}{A:Letter X}{R:Hangar s}{S:Seal (SiteX X R)}{U: Micro s}{g h c:ℝ}
-- pace h: mark speeds and stitched safe paths, g: mark fundamental speeds incl extensions licensed later
structure Grip (X:Bands s B)(W:Rental)(R:Hangar s)(S:Seal (SiteX X R))(A:Letter X)(U:Micro s)(g h c:ℝ):Prop where
 tint:A.Tint
 power:Dusk B R W
 credit:0≤c
 nSeat (x) : Good X R S 2 x→ chord (A.h x) (Mag.center (A.z x)) ≤ c
 uSeat (i x): i∈inside (halo (Wealth.cloak B) (X.gap x)) → i∈inside (safe X R W S) → Good X R S 2 (panel X i.1) → chord (U i) 1 ≤ c
 settle: stable A.z R S
 safe_g(i):Grains (X.band i ∩ safe X R W S) U (A.plant i) (A.brush i) g h

abbrev levD(B:BandWidth):ℝ:= priceTone*(B.D:ℝ)⁻¹
structure Speed (B:BandWidth)(W:Rental)(g h c:ℝ):Prop where
 gapG : sphereRate*c*3+ levD B≤g
 gapH : μH*c*3+ max (levD B) (priceTone* chk W.H) ≤ h

variable {x:Site s}
lemma GapForm (A:Letter X) (W: Rental) (z:Fin 5) (P:A.Tint){i:X.Index} (f:x∈ X.gap i)(l:A.color x=z)(hc:0≤c)(t:chord (A.frameN x) (Mag.center z)≤ c) : dist (A.G x) (beacon z (zoneD (X:=X) x)) ≤ sphereRate*c ∧ ∀u:ℝ,‖A.H W u x - dict z (zoneD (X:=X) x,u)‖≤ μH*c:=by
 subst z; let d:=sphereRate_cost.positive; by_cases q:Welkin X x
 · obtain ⟨j,u⟩:=q; by_cases b:j∈X.dc
   · rw [Gface A P f u b]; simp only [Heart_face W A P f u b,dist_self,sub_self,norm_zero]; exact ⟨by positivity,fun _=> by unfold μH; positivity⟩
   rw [Gfront A P f u b]; refine ⟨?_,fun u'=>by rw [Hfront W A P f u b]; exact swift _ _ _ (dict_s _ _ (age_t X ((moment_gap X f).symm ▸ f))).1 t⟩
   nth_rw 2 [← scaled_one (beacon _ _)]; apply (scaled_chord ..).trans; rw [close_cost_q]; exact mul_le_mul_of_nonneg_left t d.le
 rw [Gmiss A q]; simp only [Hmiss W A q,dist_self,sub_self,norm_zero]; exact ⟨by positivity,fun _=>by unfold μH; positivity⟩
lemma Amendment (A:Letter X) (W: Rental) (z:Fin 5) (P:A.Tint){i:X.Index} (f:x∈ X.band i)(g:i ∉ X.dc)(p:burial (X.mark i) x ≤ Warm B)(l:A.color x=z)(t:chord (A.frameN x) (Mag.center z)≤ c) (u:ℝ): ‖A.H W u x-neonT z (gamma W.H (burial (X.mark i) x),u)‖≤ μH*c:=by rw [← l] at *; rw [HclanN W A P f g p]; exact swift _ _ _ (neon_traces ..) t -- tune
private lemma triangle_l (U:Micro s)(i:Link s) (P: Meadow.marks s)(c:ℝ)(h: chord (U i) 1≤ c) : urgent U i P≤ sphereRate*c+dist (P (endAt i)) (P i.1):=by unfold urgent; apply (dist_triangle _ (P (endAt i)) _).trans; apply add_le_add _ le_rfl; nth_rw 2 [← scaled_one (P (endAt i))]; exact (scaled_chord ..).trans (mul_le_mul_of_nonneg_left h sphereRate_cost.positive.le)
private lemma drawM (U:Micro s)(i:Link s)(H:Paint s)(c:ℝ)(t: chord (U i) 1 ≤c) (l r:Op Slot)(h:‖H i.1-l‖≤ μH*c)(u:‖H (endAt i)-r‖ ≤ μH*c)(q:MatPlan H)(ε:ℝ)(v: ‖l-r‖≤ ε): fare U H i ≤ μH*c*3+ε:=by
 have hm:= sphereRate_cost.positive; apply (fare_plain ..).trans; rw [norm_κ _ (q _),mul_one]; have he: ‖H i.1-H (endAt i)‖ ≤ μH*c+(ε+μH*c):=by apply (norm_sub_le_norm_sub_add_norm_sub _ l _).trans; apply add_le_add h ((norm_sub_le_norm_sub_add_norm_sub _ r _).trans (add_le_add v ((norm_sub_rev ..).le.trans u))) -- tune
 exact (add_le_add he (mul_le_mul_of_nonneg_left t (by positivity : 0≤2*sphereRate))).trans_eq (by unfold μH; ring)

namespace Grip
variable (p:Grip X W R S A U g h c)(q:Speed B W g h c){i j:X.Index}{l:Link s}(u:l∈ inside (safe X R W S))
include p u
lemma lanes (t:l∈ inside (halo W.U (X.gap j))) : (A.color l.1=A.color (endAt l)) ∧ chord (U l) 1 ≤ c ∧ Good X R S 2 (panel X l.1)∧ Good X R S 2 (panel X (endAt l)) := by
 have ht:= W.um.trans (p.power.summer.trans halfway); obtain ⟨c,d⟩:= inside_iff ..|>.mp t; have hc:= near_mature ((inside_iff ..).1 u).1 c le_rfl; have he:= near_mature ((inside_iff ..).1 u).2 d le_rfl; exact ⟨brake p.settle l hc he ((moment_p X ht c).trans (moment_p X ht d).symm), p.uSeat l j (inside_cov (Corona.halo_mono ht le_rfl) t) u hc,hc, he⟩ -- tune param shadow
lemma lanes2 (f:l.1∈ halo (W.H.val+1) (X.gap j)) : l∈ inside (halo W.U (X.gap j)) := by apply inside_iff .. |>.mpr; refine ⟨Corona.halo_mono (by have h:=W.home; omega : W.H.val+1≤ W.U) le_rfl f,Corona.halo_mono (show W.H.val+1+1 ≤ W.U from W.home) le_rfl (crew_eq X (x:=l.1) (y:=endAt l) (i:=j) (Lat.oneTouch l.1 l.2)  (r:=1) (v:=W.H.val+1) f)⟩ -- remove p u dependencies
omit p u in
lemma dest (l:Link s) (t:l∈inside (safe X R W S))(v:l∈inside (X.band i)): l∈ inside (X.band i∩ safe X R W S):=by simp only [inside_iff] at *; exact ⟨mem_inter.mpr ⟨v.1,t.1⟩,mem_inter.mpr ⟨v.2,t.2⟩⟩ -- inside_iff converts
lemma diff_step (f:l∈ inside (X.gap i)) : |zoneD (X:=X) l.1-zoneD (X:=X) (endAt l)|≤(B.D:ℝ)⁻¹:=by unfold zoneD; rw [moment_gap X ((inside_iff ..).1 f).1,moment_gap X ((inside_iff ..).1 f).2]; exact age_link X _ f -- prune include
include q
lemma ditchG (f:l∈inside (X.gap i)) : urgent U l A.G≤g ∧ ∀ v∈Meadow.active, fare U (H W A v) l ≤ h :=by
 obtain ⟨hc,ht,a,b⟩:= lanes p u (inside_cov (halo_subset _ _) f); let x:= l.1; let y:= endAt l; let z:=A.color y; let Xb:= x; have hy:y∈X.gap i:= ((inside_iff ..).1 f).2; let f1:= (GapForm A W z p.tint ((inside_iff ..).1 f).1 hc p.credit (by rw [show z = A.color l.1 from hc.symm]; exact p.nSeat _ a)); let f2:= GapForm A W z p.tint hy rfl p.credit (p.nSeat _ b); let bx:=zoneD (X:=X) x; let by':=zoneD (X:=X) y; have hp: bx ∈ Hotel:= age_t X (show x∈X.gap (town X x) by rw [moment_gap X ((inside_iff ..).1 f).1]; exact ((inside_iff ..).1 f).1); have hi:by' ∈ Hotel:= age_t X ((moment_gap X hy).symm ▸ hy)
 have hμ:= diff_step p u f; refine ⟨?_,fun v t=> ?_⟩
 · apply (triangle_l U l A.G c ht).trans; apply le_trans _ q.gapG; have hx: dist (A.G y) (A.G x) ≤ sphereRate*c+(levD B+sphereRate*c):= by apply (dist_triangle _ (beacon z by') _).trans; apply add_le_add f2.1; refine (dist_triangle _ (beacon z bx) _).trans (add_le_add ?_ ((dist_comm ..).le.trans f1.1)); rw [dist_comm]; exact ((feed z).2.2.dist_le_mul bx hp by' hi).trans (mul_le_mul_of_nonneg_left (show dist bx by'≤ _ from hμ) priceTone.property)
   exact (add_le_add le_rfl hx).trans_eq (by ring)
 have he:= (safe_h z hp hi t hμ).1; exact (drawM U l (H W A v) c ht (dict z (bx,v)) (dict z (by',v)) (f1.2 v) (f2.2 v) (A.Hplan W p.tint _) _ he).trans (le_trans (add_le_add le_rfl (le_max_left ..)) q.gapH)
lemma beltG(f:l∈inside (X.band i)): urgent U l A.G ≤g ∧ ∀v∈Meadow.active,fare U (H W A v) l ≤ h:=by
 obtain ⟨a,b⟩:= inside_iff ..|>.mp f; let F:=p.safe_g i; have hx:= F.grow _ (dest l u f); refine ⟨?_, fun v t=>?_⟩; · change dist (scaledV _ (A.G (endAt l))) _ ≤ _; rw [A.Gband b, A.Gband a]; exact hx
 by_cases x:correction W i l.1 ∨ correction W i (endAt l); swap; · unfold fare; rw [Hband W A a, Hband W A b, if_neg (not_or.mp x).1, if_neg (not_or.mp x).2]; exact F.timing v t _ (dest l u f)
 have hm:i∉X.dc:= x.elim And.left And.left; let U':= X.mark i; let d:= W.H.val+1; let o:= l.1; let y:= endAt l; have h':burial (X.mark i) o ≤ W.H.val+1 ∧ burial (X.mark i) y≤ W.H.val+1:= by let hV:= Tent.stepDeep (X.mark i) l f; change burial _ l.1 ≤ _∧ burial _ (endAt l)≤ _; rcases x with ⟨p,x⟩|⟨p,x⟩<;> omega
 have hv:= W.hm.trans p.power.summer; obtain ⟨he,hu,g₁,g₂⟩:= lanes p u (lanes2 (j:=town X l.1) p u (buriesN X a (hv.trans halfway) h'.1)); let z:= A.color y; apply (drawM _ _ _ c hu (neonT z (gamma W.H (burial U' o),v)) (neonT z (gamma W.H (burial U' y),v)) (Amendment A W z p.tint a hm (h'.1.trans hv) he (by rw [show z=A.color l.1 from he.symm]; exact p.nSeat _ g₁) v) (Amendment A W z p.tint b hm (h'.2.trans hv) rfl (p.nSeat _ g₂) v) (A.Hplan W p.tint _) ((priceTone:ℝ)* chk W.H) ((safe_h z (lit ..) (lit ..) t (γ_neigh (Tent.stepDeep U' l f).1 (Tent.stepDeep U' l f).2)).2)).trans ((add_le_add le_rfl (le_max_right ..)).trans q.gapH)
omit u in
lemma exterior : Grains (safe X R W S) U A.G (H W A) g h:=by
 have he(l)(t:l∈inside (safe X R W S)): urgent U l A.G ≤g∧∀v∈ Meadow.active,fare U (H W A v) l≤h:=by obtain ⟨i,g|g⟩:= X.links_cover l; exact beltG p q t g; exact ditchG p q t g
 exact ⟨fun i t=>(he i t).1,fun u t i f=>(he i f).2 u t⟩
end Grip
end YM.CF.BPress.Hazel
