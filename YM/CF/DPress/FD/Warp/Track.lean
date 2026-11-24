import YM.CF.DPress.FD.Warp.Shirt
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row Wilson
open Cube (More assembly)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
variable {a:ℝ}{T:Trophy n l u} {I:Type*}[Fintype I] {V:Vision (More n) r I} (U:Plan V l m)(P:Leader T m 5 a) (x:I) (η μ:Cotton n)(X:Pane n){i j:Seat n}
abbrev pat (x:I)(i:Seat n): Support (More n):=supportT (U.β x i)
local notation "W"=> pat U x
-- focused real Δ
noncomputable def realF (i:Seat n):rug n:= if Grade l u X (W i) then stamp T η i X (U.β x i) else P.F η X (U.β x i)
local notation "Y"=>realF U P x η X
lemma real_M (i:Seat n): Measurable fun X=> realF U P x η X i:=by unfold realF; exact Measurable.ite (grade_M l u (W i)) (seam_M T η i _) ((measurable_pi_apply _).comp (P.m_F η))
-- Plan affine
lemma sight_R(s:Sweep n)(i:Seat n):boxA s i=aura s.s ((assembly n).embed s.b) i:=sitA s i -- affine orientation?
abbrev moveK (s:Sweep n) :Equiv.Perm I:= U.rot s.s ((assembly n).embed s.b)
lemma β_s(s:Sweep n)(i:Seat n): U.β (moveK U s x) i= ωr s (U.β x (boxA s i)):=by funext j; rw [ω_e,sight_R,sight_R]; exact U.act _ _ _ _ _
lemma pat_s(s:Sweep n)(i:Seat n): pat U (moveK U s x) i= ζ s⁻¹ (W (boxA s i)):=by unfold pat; rw [β_s,ω_S]
lemma real_s(s:Sweep n)(i:Seat n): realF U P (moveK U s x) (act s η) (flashA s X) i = Tw.Ω s (Y (boxA s i)):=by
 unfold realF; have he:= P.v_F s η X; rw [pat_s,grade_u,ζ_rev]; split; swap
 · rw [←he,valid_v,β_s]; exact congrArg _ (congrArg _ ((pullW n m).vert s _)) -- maybe inferred wrong
 next p=>
   rw [stamp_x,Equiv.symm_apply_apply,β_s]
-- same-S membership estimates
lemma key_x (v:separation i j ≤1): Clan l (W i∪ W j):=by
 intro t x' y z; have he:= U.prox x i j v t x'; have hp:= U.prox x i j v y z; apply le_trans (separation_triangle t i y); unfold s10; rw [separation_comm t i]; omega -- goal close
lemma clan_i (i:Seat n):Clan l (W i):= (key_x U x (i:=i) (j:=i) (by simp)).mono subset_union_left
lemma due_i(i:Seat n): (W i).card≤5:= (card_le_card (s:=W i) (t:= W i∪W i) subset_union_left).trans (U.dims x i i (by simp)) -- s₁? implicit
lemma path_h (i:Seat n): W i ⊆ brim i (4*l) :=fun j p=> (cellP ..).2 (U.prox x i i (by simp) j (mem_union_left _ p))
lemma pathR (q:x=x)(t:j∈W i): close l j i := by unfold close s10; have he := (cellP j i (4*l)).1 (path_h U x i t); rw [separation_comm]; omega
lemma tip (i:Seat n): U.β x i∈facet (W i):= ⟨U.lives x i,Finset.Subset.refl _⟩
lemma real_ve(i:Seat n)(t:0<m):Y i∈Frame _:=by unfold realF; split; exact rgStamp T η t (U.lives x i); exact (P.ℒ_F (W i) (clan_i U x i) (due_i U x i) η X).choose_spec.legal (tip U x i)
lemma due_R (p:0<m)(t:0≤u)(κ:Treasure l m u)(i: Seat n): Frame.Fits (1/(m:ℝ)) (P.F η X (U.β x i)) (Y i):=by
 unfold realF; split; next l=> rw [P.keep _ _ _ l]; let w:=SeatT (W i) η; have hp: w ∈ W i:= grip η (wave_eq _ (U.lives x i) p); exact ⟨T.G η w X i,step_t T η X _ w i l hp (clan_i U x i) (pathR U x rfl hp) t κ⟩
 next p=> exact ⟨1,by rw [sail_id,dist_self]; positivity⟩
abbrev rate(a:ℝ):ℝ:= 2*a+2
lemma real_pair (h:baseP≤ a) (p:0<m) (t:0≤u)(κ:Treasure l m u) (u':separation i j≤1): Frame.Fits (rate a/(m:ℝ)) (Y i) (Y j):=by
 let wi:=U.β x i; let wj:=U.β x j; obtain ⟨V,pV,hV,v⟩:= P.ℒ_F (W i∪W j) (key_x U x u') (U.dims x i j u') η X; let A:=P.F η X; have hi:wi∈facet (W i∪W j):=⟨U.lives ..,subset_union_left⟩; have hj:wj∈facet (W i∪ W j):=⟨U.lives ..,subset_union_right⟩;
 obtain ⟨g,hg⟩:= Frame.triangle (Frame.transpose (due_R U P x η X p t κ i)) (Frame.triangle (hV _ hi) (Frame.triangle (p:=a*δR wi wj) ⟨1,by rw [sail_id]; exact v _ hi _ hj⟩ (Frame.triangle (Frame.transpose (hV _ hj)) (due_R U P x η X p t κ j))))
 refine ⟨g,hg.trans (le_trans (b:=1/(m:ℝ)+(0+(a*(2/(m:ℝ))+(0+1/(m:ℝ))))) ?_ (le_of_eq ?_))⟩
 · have hz: δR wi wj ≤ 2/(m:ℝ):=div_le_div_of_nonneg_right (by exact_mod_cast U.cost x i j u') (Nat.cast_nonneg m); have ht:= mul_le_mul_of_nonneg_left hz (base_p.trans h); linarith only [ht]
 unfold rate; ring
-- footprints
abbrev Track(l:ℕ) := 4*l+(globe l+5)
lemma rentT : halo (globe l+5) (W i)⊆ brim i (Track l):=by
 intro z p; obtain ⟨j,v,h⟩:= halo_spec.mp p; apply (cellP ..).2; exact (separation_triangle i j z).trans (add_le_add ((cellP j i _).1 (path_h U x i v)) h)
lemma real_K (p:0<m){x':I}{X':Pane n}(t:U.β x i=U.β x' i)(v: Agrees (brim i (Track l)) X X')(W':Prints η μ (W i)):Y i=realF U P x' μ X' i:=by
 unfold realF; rw [show pat U x' i=W i from congrArg supportT t.symm]; let S := W i; have hx:Agrees (halo (globe l+5) S) X X':= agrees_mono v (Finset.coe_subset.mpr (rentT U x)); rw [← t,touch_B hx]; split; next t=> exact stamp_p T η μ _ i W' (agrees_mono hx (Finset.coe_subset.mpr (end_h (Finset.Subset.refl _) (by omega))))
 next t=> exact P.foot _ (U.lives _ _) (clan_i U x i) _ _ _ _ W' hx
end Turf
end YM.CF.DPress.FD
