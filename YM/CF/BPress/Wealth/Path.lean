import YM.CF.BPress.Wealth.Direct
/-! Taylor row estimates at kept: copy decisions on whole truncated stencils. Applies to lengths up to cutoff. Background leg **not transported derivative** at leading order; using curvature at identity gives ordinary oriented curl (uses id of FiniteGaugeData J); prove true costs incl paths. Use tested background tolerance bound; costs nmarked-only separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side} (M:ℕ) (a:RG.Slot)(v:Signed) (o : Site s) {p:PlaqAxes} {ζ D y κ:ℝ}

def door : Bonding s:=(wrap s a.offset+o,a.plaq)
lemma door_time : stop o a.walk=(door a o).1:=by
 have he(y:Cover)(w:Walk) : Lattice.stop (wrap s y+o) w=wrap s (Lattice.stop y w)+o:=by
    induction w generalizing y with|nil=>simp [Lattice.stop]| cons i w ih=> rw [Lattice.stop,Lattice.stop, ← add_right_comm _ (i.vec), ← wrap_vec s i,← map_add]; apply ih -- tune
 simpa [door, RG.Slot.offset] using he 0 a.walk
lemma door_stencil : touched (door a o) ⊆ foot o a:=by
 rw [foot_native]; intro i p; have he(y:Site s)(w v:Walk) : i∈visits (Lattice.stop y w) v → i∈ visits y (w++v):=by induction w generalizing y with|nil=>simp [Lattice.stop]|cons a w ih=>intro h; exact List.mem_cons_of_mem _ (ih _ h)
 apply List.mem_toFinset.mpr; apply he; rw [door_time]; exact List.mem_toFinset.mp p
lemma nearby (v:M ≤ M)(h:a.length ≤ M) : foot o a⊆ box M o:=by -- redundant? remove
 apply Subset.trans (foot_limit ..|>.2.2.1); intro i p; obtain ⟨j,v,x⟩:=halo_spec.mp p; exact halo_spec.mpr ⟨j,v,x.trans (by omega)⟩
lemma door_leg (h:a.length≤M)(k:Fin 4) : address v (aperture (door a o) k)∈ tickets M (Sum.inr (v,(o,p))):= by
 apply photo_edge v (box M o); refine inside_le ((door_stencil ..).trans (nearby M a o le_rfl h)) (ap_limit ..)
lemma walk_sites (h:a.length ≤ M) : (visits o a.walk).toFinset⊆ box M o:=by
 intro i p; refine halo_spec.mpr ⟨o,mem_singleton_self _, (Paths.to_ball o a.walk p).trans ?_⟩; unfold RG.Slot.length at h; omega
lemma slot_val (U : Micro s) : a.atSite U o= group.adjoint (travel U o a.walk) (group.curvature (faceValue U (door a o))) := by
 unfold RG.Slot.atSite RG.Slot.eval faceValue; simp_rw [travel_at]; simp [door]

lemma rollBack (h:E)(i:ink): ‖group.adjoint h i-i‖ ≤ 2*scr* group.chord h * ‖i‖:=by
 let A:=group.mat h; let C:=group.colorMat i
 have he:A* C* star A-C = (A-1)* C*star A + C*star (A-1) := by simp only [star_sub,star_one, sub_mul, mul_sub,one_mul,mul_one]; abel
 apply le_of_mul_le_mul_left _ group.colorScale_pos; rw [← group.colorMat_norm _, map_sub, group.mat_adjoint]; change ‖A* C*star A-C‖ ≤ scr *_; rw [he]; refine (norm_add_le ..).trans ((add_le_add (?_ : ‖(A-1)*C*star A‖≤ ‖A-1‖*‖C‖) (norm_mul_le ..)).trans ?_); swap -- tune
 · change _ + ‖C‖ * ‖star (A-1)‖ ≤ _; rw [norm_star,show ‖C‖= _ from group.colorMat_norm i, show ‖A-1‖= scr*group.chord h from (by simpa only [Gauge.mat_one,chord.one] using (chord.scale_mul h 1).symm)]; -- first upper metavariable?
   unfold scr; exact Eq.le (by ring)
 rw [Gauge.frob_mul_eq _ _ (by rw [star_star]; exact group.mat_star_mul h)]; apply norm_mul_le

-- geometry yields kept flag test "on"; and projection/clamp small. use separate numeric checks
variable {b:BandWidth}(X : Bands s b) (j:Root s)(q:Dividend D κ ζ y){U:Micro s}{w:Directions group s}
include q
lemma kept_bg (d:Clip) : PathData.kept d (temp y) o (pull v 0 (background y)):=by intro u; refine (back_flag q v u).trans (le_mul_of_one_le_right (temp_pos q.young).le (Real.one_le_exp ?_)); positivity [d.radius_pos]
lemma kept_use (t:Tested D κ y (tickets M (Sum.inr (v,(o,p)))) U w)(d:Clip)(P:BudgetPoint)(h:Checks M P d)(e:P.threshold=temp y) : PathData.kept d (temp y) o (pull v 0 U) := by
 intro x; by_cases u: temp y*Real.exp (separation o x.1 / d.relaxation)<2
 · refine (drawn_flag q v x (fun i=> t.small _ (photo_edge v (box M o) _ ?_))).trans (le_mul_of_one_le_right (temp_pos q.young).le (Real.one_le_exp (by positivity [d.radius_pos]))); apply inside_le (S:=touched x) _ (ap_limit ..); intro i k; refine halo_spec.mpr ⟨o,mem_singleton_self _, (separation_triangle o x.1 i).trans ((add_le_add le_rfl (Work.E01.sep_touched x i k)).trans (h _ ?_))⟩; simpa [e] using u
 refine le_trans (group.chord_le_two _) (le_of_not_gt u)
lemma curv_back : ‖group.curvature (faceR v (background y) (door a o))‖ ≤ ζ*mA y:= (group.curvature_norm _).trans (q.bgChord ..)
lemma c_back : ‖a.atSite (pull v 0 (background y)) o‖ ≤ ζ*mA y:= by rw [slot_val,group.norm_adjoint]; apply curv_back a v o q
variable (t: Tested D κ y (tickets M (Sum.inr (v,(o,p)))) U w) (h : a.length ≤ M)
include t h
lemma curv_use : ‖group.curvature (faceR v U (door a o))‖ ≤ temp y:= (group.curvature_norm _).trans (drawn_flag q v _ fun i=> t.small _ (door_leg M a v o h i)) -- tune
lemma c_actual : ‖a.atSite (pull v 0 U) o‖ ≤ temp y:= by rw [slot_val,group.norm_adjoint]; exact curv_use M a v o q t h
-- need bound on each walked path used both at A and U. `chord.path` dummy id. 
omit t in
private lemma tariff {V:Micro s} (t':∀ i∈ tickets M (Sum.inr (v,(o,p))), group.chord (V i) ≤ (ζ+1) * aA y) : group.chord (travel (pull v 0 V) o a.walk) ≤ M*((ζ+1)*aA y):=by
 let U0:Micro s:=1; have he(z:Site s)(w:Walk) : travel (pull v 0 U0) z w=1:=by
    have h: pull v 0 U0=U0:=by funext x; rw [orient_read]; split; simp [U0]; rfl
    rw [h]; induction w generalizing z with|nil=> rfl|cons i w ih=> simp [travel, Step.read, ih,U0] -- tune
 rw [←chord.one, ←he o a.walk]; refine (chord.path (pull v 0 V) (pull v 0 U0) a.walk o _ ?_).trans (mul_le_mul_of_nonneg_right ?_ (by positivity [q.posC, aA_positive q.young])); · intro i x g; rw [pull_close]; exact (chord.one ..|>.le.trans (t' _ (photo_edge v _ _ (inside_le (walk_sites M a o h) (inside_iff ..|>.mpr ⟨x,g⟩)))))
 exact_mod_cast (show a.walk.length ≤ M by unfold RG.Slot.length at h; omega)
private lemma walkU : group.chord (travel (pull v 0 U) o a.walk) ≤ M*((ζ+1)*aA y):=by
 apply tariff M a v o q (p:=p) h (V:=U); intro i g; rw [←chord.one]; apply le_trans (chord.triangle (U i) (background y i) 1); apply le_trans (add_le_add (((t.small i g).trans q.olive).trans q.fire) ((chord.one ..).le.trans (q.bgView i.2))); exact Eq.le (by ring)
omit t -- separate
private lemma walkA : group.chord (travel (pull v 0 (background y)) o a.walk)≤ M*((ζ+1)*aA y):=by -- need tariff not include t
 apply tariff M a v o q (p:=a.plaq) h; intro i _; apply le_trans (q.bgView i.2); exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (aA_positive q.young).le
-- scale cross product issue
def stretch (ζ : ℝ)(M:ℕ) := 2*scr*M*(ζ+1)
omit h
private lemma rot_scale (i:E)(w:ink)(p:group.chord i≤ M*((ζ+1)*aA y))(h:‖w‖≤temp y): ‖group.adjoint i w-w‖ ≤ stretch ζ M*finer y:=by
 refine (rollBack ..).trans ((mul_le_mul (mul_le_mul_of_nonneg_left p ?_) h (norm_nonneg _) ?_).trans ?_) -- tune
 all_goals first| positivity [show 0<scr from group.colorScale_pos, aA_positive q.young,q.posC]| skip
 have he:aA y*temp y ≤ finer y:=by have hv:= xi_pos q.young; unfold finer; nlinarith [sq_nonneg (temp y)]
 rw [show 2*scr * ((M:ℝ)*((ζ+1)*aA y))*temp y=stretch ζ M*(aA y*temp y) from (by unfold stretch; ring)]; refine mul_le_mul_of_nonneg_left he ?_; unfold stretch; positivity [show 0<scr from group.colorScale_pos,q.posC]
include h
lemma a0_near : ‖a.atSite (pull v 0 (background y)) o-mA y • psi v a.plaq‖ ≤ (stretch ζ M + ζ)*finer y:=by
 let A:= faceR v (background y) (door a o); let f:= curveAbs group; have ht : ‖group.curvature A-mA y • psi v a.plaq‖ ≤ ζ*finer y:= by
    have hg:= q.bgCase s v (door a o); rw [←curved_actual,← curved_canon (psi v a.plaq),← map_smul, ←map_sub]; exact (curve_le ..).trans (hg.trans (mul_le_mul_of_nonneg_left (finer_aA q) q.posC.le))
 rw [slot_val]; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (group.curvature A) _); rw [add_mul]; exact add_le_add (rot_scale M q _ _ (walkA M a v o q h) ((curv_back a v o q).trans (mA_small q))) ht -- tune shadow
include t
lemma near_cost : ‖a.atSite (pull v 0 U) o - a.atSite (pull v 0 (background y)) o - orbitP v (door a o) w‖ ≤ (2*stretch ζ M + ζ)* finer y:=by
 let A:= faceR v (background y) (door a o); let V:= faceR v U (door a o); let x:= group.curvature A; let s':= group.curvature V; let z:= orbitP v (door a o) w; have hb: ‖s'-x-z‖≤ ζ*finer y:= by
    unfold s' x; rw [←curved_actual,←curved_actual,←curved_canon z,←map_sub,←map_sub] -- nested map_sub order
    refine (curve_le ..).trans (q.faceCase s v U (door a o) w (fun i=>t.angle _) (fun i=>t.near _ (door_leg M a v o h i)))
 rw [slot_val,slot_val]; let g:= travel (pull v 0 U) o a.walk; let A':= travel (pull v 0 (background y)) o a.walk; change ‖group.adjoint g s'-group.adjoint A' x-z‖≤ _
 rw [show _ - _ - z = (group.adjoint g s'-s')-(group.adjoint A' x - x)+(s'-x-z) from (by abel)]; apply le_trans (norm_add_le ..); refine (add_le_add ((norm_sub_le ..).trans (add_le_add (rot_scale M q g s' (walkU M a v o q t h) (curv_use M a v o q t h)) (rot_scale M q A' x (walkA M a v o q h) ((curv_back a v o q).trans (mA_small q))))) hb).trans_eq ?_; ring
end YM.CF.BPress.Wealth
