import YM.CF.DPress.FD.Warp.Stamp
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
variable (T:Trophy n l u) (η μ:Cotton n) (U:Pane n)
local notation "D"=>supportT
local notation "τ"=> T.G
lemma fixedL (w v:leaf n m)(p:0<m)(x:Seat n):dist (stamp T η x U w) (stamp T η x U v) ≤ Row.rad*δR w v:=by
 apply (dist_pi_le_iff (mul_nonneg alive.le δp)).2; rintro (i|i); swap; · exact (dist_self (0:Key)).trans_le (mul_nonneg alive.le δp)
 rw [dist_eq_norm]; change ‖roadmap w i • _- roadmap v i • _‖ ≤ _; rw [←sub_smul,norm_smul,← dist_eq_norm,bloom,mul_comm]; exact mul_le_mul_of_nonneg_left (nearT w v p i) alive.le
-- any anchor in same simplex uses its basis change at every good active support. both-good edge estimate uses this variant too.
lemma step_t (w:leaf n m)(y z:Seat n)(p:Grade l u U (supportT w))(q:y∈ D w)(h:Clan l (D w))(v:close l y z)(hu:0≤u)(κ:Treasure l m u): dist (sail (stamp T η y U w) (T.G η y U z)) (stamp T η z U w)≤1/(m:ℝ):=by
 refine (dist_pi_le_iff (by positivity: 0≤ 1/(m:ℝ))).2 ?_; rintro (i|i); swap; · change dist ((0:Key)*_) 0≤1/(m:ℝ); rw [zero_mul,dist_self]; positivity
 change dist ((roadmap w i • fund (T.G η i U y))* fund (T.G η y U z)) (roadmap w i • fund (T.G η i U z)) ≤ _; rw [Algebra.smul_mul_assoc,dist_smul₀,Real.norm_of_nonneg (money w i|>.1)]; by_cases t:i∈ D w; swap; · rw [rm_dim w i t,zero_mul]; positivity
 exact (mul_le_of_le_one_left dist_nonneg ((money w i).2)).trans ((Row.spin_cost (T.G η i U y * T.G η y U z) (T.G η i U z)).trans_le (transit hu κ (T.bill _ _ _ (p i t)) (T.bill _ _ _ (p y q)) (h i t y q) v))
lemma wave_eq (w:leaf n m)(p:Live w)(t:0<m): (D w).Nonempty:= by obtain ⟨i,h⟩:=p; exact ⟨i,(mem_h ..).2 (h ▸ right_pos t)⟩
lemma gapZ (w v:leaf n m)(h:w≠v) :1/(m:ℝ) ≤ δR w v:=by
 obtain ⟨i,p⟩:= Function.ne_iff.mp h; have he:0<DistU (w i) (v i):=by unfold DistU; have hv:(w i).val≠(v i).val:= fun t=>p (Fin.ext t); omega
 exact div_le_div_of_nonneg_right (show (1:ℝ) ≤ (Ramp.d w v:ℝ) from mod_cast (show (1:ℕ) ≤ Ramp.d w v from he.trans_le (tick w v i))) (by positivity:0 ≤ (m:ℝ))
abbrev baseP :ℝ:= Row.rad + 2
lemma base_p:0≤baseP:=add_nonneg alive.le (by positivity)
lemma atS(p:0<m)(hu:0≤u)(κ:Treasure l m u)(S:MaskU n)(v:Grade l u U S)(uS:Clan l S): Tends S (basic (m:=m) T η U) baseP:=by
 let F:Clove n m:=basic T η U; by_cases hg:S.Nonempty; swap; · refine ⟨F,⟨?_,fun i _=>Frame.reflex _,?_⟩⟩; all_goals first|exact fun i v=> False.elim (hg ((wave_eq i v.1 p).mono v.2))| exact fun i v=> False.elim (hg ((wave_eq i v.1 p).mono v.2)) -- binder MapsTo implicit.T
 let y:=hg.choose; have hy:y∈S:= hg.choose_spec; let D':=facet (m:=m) S
 let f (x:leaf n m):= stamp T η y U x; let A(x:leaf n m):= SeatT (D x) η; let H(x:leaf n m):= T.G η (A x) U y; let V(x:leaf n m):= sail (F x) (H x); refine ⟨V,⟨fun i w=> rgStamp T η p w.1,fun i w=>⟨H i,(dist_self _).le⟩,?_⟩⟩
 have he(w:leaf n m) (h:w∈facet S) : dist (V w) (f w)≤1/(m:ℝ):= by
    have hw: A w∈ D w:= grip η (wave_eq w h.1 p); exact step_t T η U w (A w) y (v.mono h.2) hw (uS.mono h.2) (uS (A w) (h.2 hw) y hy) hu κ
 intro i h v p'; by_cases e:i=v; · rw [e,dist_self]; exact mul_nonneg base_p δp
 apply (dist_triangle _ (f i) _).trans; apply le_trans (b:=δR i v+(dist (f i) (f v)+δR i v)); exact add_le_add ((he i h).trans (gapZ i v e)) ((dist_triangle _ (f v) _).trans (add_le_add (le_refl _) ((dist_comm ..).trans_le ((he v p').trans (gapZ i v e)))))
 have he:=(fixedL T η U i v p y); unfold baseP; unfold f; nlinarith only [he]
end Turf
end YM.CF.DPress.FD
