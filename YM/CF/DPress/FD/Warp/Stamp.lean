import YM.CF.DPress.FD.Warp.Front
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.FD
open Function Filter Lattice Cash Bifold Deck Hue Geo Warm Frame Ramp Spire Skye SU Lat Scroll Tw Finset Con Row
open Cube (More)
open scoped Topology BigOperators ENNReal NNReal Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {n:Side}{r l m N:ℕ}{u:ℝ}
namespace Turf
abbrev MaskU(n:Side):=Support (More n)
abbrev roadmap(v:leaf n m)(i:Seat n):ℝ:= ((v i).val:ℝ)/(m:ℝ)
lemma money(v:leaf n m)(i:Seat n): roadmap v i∈Row.budget:= by unfold roadmap; refine ⟨by positivity,?_⟩; by_cases h:0<m; exact (div_le_one (Nat.cast_pos.mpr h)).2 (by exact_mod_cast Nat.le_of_lt_succ (v i).isLt); rw [show (m:ℝ)=0 from Nat.cast_eq_zero.mpr (Nat.eq_zero_of_not_pos h),div_zero]; exact zero_le_one
lemma nearT(v w:leaf n m)(p:0<m)(i:Seat n): dist (roadmap v i) (roadmap w i)≤ δR v w:=by unfold roadmap; rw [fin_cost p]; exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (tick v w i)) (by positivity)
lemma rm_dim(v:leaf n m)(i:Seat n)(u:i ∉ supportT v): roadmap v i=0:=by have he:v i=0:= Classical.byContradiction fun t=> u ((mem_h ..).2 t); simp only [roadmap,he,Fin.val_zero,Nat.cast_zero,zero_div]
lemma rm_v(s:Sweep n)(v:leaf n m)(i:Seat n): roadmap (ωr s v) i=roadmap v (boxA s i):=by unfold roadmap; rw [ω_e]
variable (T:Trophy n l u) (η μ:Cotton n) {U V:Pane n}
abbrev stamp (x:Seat n)(U:Pane n):Clove n m:= fun v i=> Sum.elim (fun i=> roadmap v i • fund (T.G η i U x)) (fun _=>0) i
def basic (U:Pane n):Clove n m:= fun v=> stamp T η (SeatT (supportT v) η) U v
local notation "B"=> basic
local notation "Z"=>stamp
local notation "ρu"=> supportT
lemma rgStamp {x:Seat n}{v:leaf n m}(t:0<m)(p:Live v) : stamp T η x U v∈ Frame _:=by
 refine ⟨?_,?_⟩; · rintro (i|i); exact Row.swell (Row.plant _) (money v i); exact Row.nil
 obtain ⟨i,p⟩:=p; refine ⟨Sum.inl i,T.G η i U x,Eq.symm ?_⟩; change roadmap v i • fund (T.G η i U x) = fund _; rw [show roadmap v i=1 from ?_,one_smul]; unfold roadmap; rw [p,right,div_self] -- coercion
 exact Nat.cast_ne_zero.mpr t.ne'
lemma last_b (X:Pane n)(v:leaf n m)(i:Fin 5): basic T η X v (.inr i)=0:=rfl
lemma seam_M (x:Seat n)(v:leaf n m): Measurable fun U=> stamp T η x U v:=by
 refine measurable_pi_lambda _ ?_; rintro (i|i); swap; · exact measurable_const
 exact (measurable_const (a:= roadmap v i)).smul (Row.steady.measurable.comp ((measurable_pi_apply x).comp (T.knows η i))) -- tune Key meas both inst
lemma basic_M : Measurable fun U=> basic (m:=m) T η U := measurable_pi_lambda _ fun i=>seam_M T η _ i
abbrev Prints (η μ:Cotton n) (S:MaskU n):Prop:=∀ D⊆S,D.Nonempty→ η D=μ D
lemma prints_η {F:MaskU n}(p:(Salar n r).looks F η μ) : Prints η μ F:= by intro D t h; exact earnings _ h _ _ ((Salar n r).le _ _ t _ _ p) -- F implicit collision SU.F
lemma prints_d {S D:MaskU n}(p:Prints η μ S)(t:D⊆ S):Prints η μ D:=fun i v=> p i (Finset.Subset.trans v t)
lemma stamp_p (v:leaf n m)(x:Seat n)(p:Prints η μ (ρu v))(u:Agrees (halo (globe l) (ρu v)) U V): Z T η x U v= Z T μ x V v:=by
 funext i; rcases i with i|i; swap; exact rfl
 change roadmap v i • fund (T.G η i U x) = roadmap v i • fund _; by_cases h:i∈ρu v; swap; · rw [rm_dim _ _ h,zero_smul,zero_smul]
 rw [T.port i U V η μ (p _ (singleton_subset_iff.mpr h) (singleton_nonempty _)) (agrees_mono u (Finset.coe_subset.mpr (bit_h h _)))]
lemma basic_p (v:leaf n m)(p:Prints η μ (ρu v))(u:Agrees (halo (globe l) (ρu v)) U V) (h:(ρu v).Nonempty): B T η U v= B T μ V v:= by unfold basic; rw [stamp_p T η μ v _ p u,grip_v ..]; exact p _ (Finset.Subset.refl _) h
lemma stamp_x(s:Sweep n)(x:Seat n)(X:Pane n)(v:leaf n m):Tw.Ω s (stamp T η x X v)= stamp T (act s η) ((boxA s).symm x) (flashA s X) (ωr s v):=by
 funext i; rcases i with i|i; swap; · rw [η_w]; exact win_z _
 rw [η_v]; change windX _ (roadmap v _ • fund (T.G _ _ _ _))= roadmap (ωr s v) i • fund (T.G _ _ _ _); rw [wind_h,wind_v,T.turn,gate_e,rm_v,Equiv.apply_symm_apply]
lemma basic_x(s:Sweep n): (clove n m).mv s (B T η U)= B T (act s η) (flashA s U):=by
 funext i; obtain ⟨i,w⟩:= (e (pullW n m) s).surjective i; change ωr s i=_ at w; subst_eqs; rw [valid_v,show ωr s⁻¹ (ωr s i)=i from (pullW n m).vert s i]; unfold basic; rw [ω_S, reachP,stamp_x]
end Turf
end YM.CF.DPress.FD
