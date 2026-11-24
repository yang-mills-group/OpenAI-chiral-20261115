import YM.CF.DPress.FD.Warp.Lug
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
/-!
Mesh anchor transports on balls. We use the patch axial-gauge path estimate
(Cube.anchored arising by those local axial paths) and permit selection of any
transport satisfying its estimate. Coincides with the needed transport
quantitatively: once anchor is set to one, it's uniformly within the accumulated
O(S² u) along the admitted paths. Need not transform path-order data separately.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Cube Lat Scroll Tw Finset
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m:ℕ}{u:ℝ}
namespace Con
abbrev globe (l:ℕ):=110*l
abbrev cost (l:ℕ)(u:ℝ):ℝ:= 4*(u*(1+globe l))
lemma cost_pos (t:0≤ u):0≤ cost l u:=by unfold cost; positivity
abbrev brim(i:Seat n)(r:ℕ):= Hue.cell (More n) i r
local notation "L"=> Seat n
variable (i j: Seat n)
abbrev Space(i:Seat n)(l:ℕ):=brim i (globe l)
abbrev vessel(i:Seat n)(l:ℕ):=brim i (globe l+1)
def Sound(l:ℕ)(u:ℝ)(X:Pane n)(x:Seat n):Prop:= RG.Healthy u (vessel x l) X
def Must (l:ℕ)(u:ℝ)(X:Pane n)(x:Seat n)(G:Reign n):Prop:= G x=1∧∀ i: reach n, ends i⊆ Space x l→group.chord ((gauge G X) i)≤cost l u
lemma use_t (l:ℕ)(u:ℝ) : IsClosed {v:Pane n×Reign n| Must l u v.1 i v.2}:=by
 unfold Must; simp only [Set.setOf_and,Set.setOf_forall]; refine (isClosed_eq ((continuous_apply i).comp continuous_snd) continuous_const).inter ?_; refine isClosed_iInter fun j=> isClosed_iInter fun x=> ?_; refine isClosed_le ?_ continuous_const; unfold Lattice.gauge; fun_prop
lemma licence {U:Pane n}{x:Seat n} (p:0≤ u)(t:Sound l u U x)(h:2*(globe l+1)<(More n).val) :∃ F:Reign n, Must l u U x F:=by
 obtain ⟨F,g⟩:= Planned.AtomRegular.Foliage.Cube.anchored x t p (Finset.Subset.refl (vessel x l)) h; let y(i):= (F x)⁻¹* F i; refine ⟨y,⟨inv_mul_cancel _,fun i hx=>?_⟩⟩; have he:= (cellP i.1 x (globe l)).1 (hx (by simp)); rw [show Lattice.gauge y U i=(F x)⁻¹*Lattice.gauge F U i*((F x)⁻¹)⁻¹ from (by unfold Lattice.gauge y; group),group.chord_conj]; exact (g _ he).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by gcongr) p) (by positivity))
variable {X Y: Pane n}
lemma sounds (s:Sweep n): Sound l u (flashA s X) i↔ Sound l u X (boxA s i):=by
 unfold Sound RG.Healthy; rw [flagsA]; refine ⟨fun p=>?_,fun t=>?_⟩
 · unfold vessel brim; rw [←cellV s (globe l+1) i]; apply disjoint_left.mpr; intro x h y; obtain ⟨x,rfl⟩:= (boxA s).surjective x; exact disjoint_left.mp p ((mem_s s x _).1 h) (by simp [y]) -- rw defin.A.L.W
 apply disjoint_left.mpr; intro x h v; have hp: boxA s x∈ vessel (boxA s i) l:=by rw [vessel,brim,←cellV]; exact (mem_s s x _).2 h
 exact disjoint_left.mp t hp (by simpa using v)
lemma direct {s:Sweep n} {F: Reign n} (t: Must l u X (boxA s i) F) : Must l u (flashA s X) i ((gate n).mv s F):=by
 refine ⟨?_,?_⟩; · rw [gate_e,t.1,map_one]
 intro j h; have hp:lane s j=lane s j:=rfl; have he:ends (lane s j)⊆Space (boxA s i) l:=by unfold Space brim; rw [←cellV s (globe l) i,laneX]; exact Finset.map_subset_map.mpr h
 rw [show Lattice.gauge ((gate n).mv s F) (flashA s X)=flashA s (Lattice.gauge F X) from ?_,flash]; swap; · rw [revG]; congr 1; funext i; rw [gate_e]
 have hl:=t.2 (lane s j) he; have hg(x:E) (b:Bool):group.chord (polarT b x)=group.chord x:=by cases b; exact rfl; exact Reef.cool x
 rw [hg]; split; rw [group.chord_inv]; exact hl; exact hl
lemma sure (l:ℕ)(u:ℝ):MeasurableSet {v:Pane n| Sound l u v i}:= (RG.healthy_closed ..).measurableSet
-- stableB hull cell
lemma stable {X Y: Pane n}{S W:Support (More n)}(h:halo 4 S ⊆ W)(u:ℝ)(p:Agrees W X Y) : RG.Healthy u S X = RG.Healthy u S Y:=by
 unfold RG.Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty]; apply congrArg (fun x:Support (More n)=> x=∅); ext i; rw [mem_inter,mem_inter]; apply and_congr_right; intro v; rw [RG.flags_spec,RG.flags_spec]; refine exists_congr fun j=> and_congr_right fun t=>?_ ; have hp(z:L)(p:z∈ RG.touched j):z∈W:=h (halo_spec.mpr ⟨i,v,(separation_triangle i j.1 z).trans ((Nat.add_le_add ((separation_comm ..).trans_le (Work.E01.sep_touched _ i t)) (Work.E01.sep_touched _ z p)))⟩)
 rw [show faceValue X j= faceValue Y j from travel_local j.1 _ X Y (fun i t v=> p i (hp _ (List.mem_toFinset.mpr t)) (hp _ (List.mem_toFinset.mpr v)))]
-- overhead reserve
lemma stableB (p:Agrees (brim i (globe l+5)) X Y): Sound l u X i=Sound l u Y i:= by
 apply stable _ u p; intro z t; obtain ⟨j,g,h⟩:= halo_spec.mp t; have he:= (cellP j i (globe l+1)).1 g; exact (cellP ..).2 ((separation_triangle i j z).trans ((Nat.add_le_add he h).trans_eq (by omega)))
def cut(i:Seat n)(l:ℕ)(X:Pane n):Pane n:= fun j=> if ends j⊆ Space i l then X j else 1
lemma cut_h {F:Reign n}: Must l u (cut i l X) i F ↔ Must l u X i F:=by
 unfold Must; refine and_congr_right fun _=> forall_congr' fun j=> forall_congr' fun (t:ends j⊆ Space i l)=>?_ ; unfold cut Lattice.gauge; simp only [if_pos t]
lemma cut_t {Y: Pane n}(h:Agrees (Space i l) X Y): cut i l X=cut i l Y:=by
 funext j; unfold cut; split; next p=> exact h j (p (by simp)) (p (by simp))
 next p=> rfl
lemma cut_y(l:ℕ): Continuous (cut i l):=continuous_pi fun j=> by unfold cut; split; exact continuous_apply _; exact continuous_const
lemma promise (l:ℕ)(u:ℝ)(t:0≤u)(p:2*(globe l+1)<(More n).val):∃ g:Pane n→Reign n,Measurable g∧(∀ X,Sound l u X i→Must l u X i (g X))∧ ∀ X Y, Agrees (Space i l) X Y→g X=g Y:=by
 obtain ⟨g,h,v⟩:= BPress.choose_if_closed _ (use_t i l u); refine ⟨g ∘ cut i l,h.comp (cut_y i l).measurable,fun X t'=>?_,fun X Y t=>congrArg g (cut_t i t)⟩; apply (cut_h i).1; apply v; obtain ⟨G,h⟩:=licence t t' p; exact ⟨G,(cut_h i).2 h⟩
end Con
end YM.CF.DPress.FD
