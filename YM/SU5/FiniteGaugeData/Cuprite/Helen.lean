import YM.SU5.FiniteGaugeData.Cuprite.Caesura
/-!
# Phase expense! One regulator edge: the paid angular pressure didn't see the phase field on Loom.
Local estimate with footprint independent Gauge charge. -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 450000
set_option linter.flexible false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Cuprite.Spirit
open Function NormedSpace Filter Finset MeasureTheory Lattice RG Wilson AnalyticBridge Metric Pressure Galope CF CF.Pastry CF.Py.Rate
open SU Fock Cube Lat Window Presidio Tenant Skye Scree Graph CF.Buffered Window.Brique Next.Rank Branch Nacre Pec Font
open Rush Scroll Peaks Tap Tulip Fir Cascade
open Avenue RouteM Spindle Steve
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{t p b e v C r a:ℝ}{k w:ℕ} {T:Pride n}
local notation "W" => More n
namespace PhaseM
abbrev marginA (w:ℕ):ℕ:= (w+w+1)^4
private abbrev hem(A:Finset (Face (Per W))):Support W:= A.image Prod.fst
lemma touches_near {X:Pane n}(o:Site (More n))(h:t≤p)(v:o∈RG.flags p X): o∈ Lattice.halo 4 (hem (misses X t)):= by
 obtain ⟨i,h1,h2⟩:= (RG.flags_spec ..).1 v
 exact halo_spec.mpr ⟨i.1, mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ i,h.trans_lt h2⟩), Extra.Iteration.Shapes.visits_dist _ _ _ (List.mem_toFinset.mp h1)⟩
variable {X:Pane n}{Y:Loom n}(z:Orbit n)(J:Roof n p b k Y)(h:t≤p)
include J h
lemma fleece (i:Face (Per (More n))) (e:i∈misses (Y z) t): i.1∈ Lattice.halo (k+8) (hem (misses z.1 t)):=by
 by_contra v
 have hv:i ∉misses z.1 t:= fun e=> v (halo_subset _ _ (mem_image_of_mem Prod.fst e))
 apply hv; rw [misses,mem_filter]; refine ⟨mem_univ _,?_⟩; rw [show faceValue z.1 i= faceValue (Y z) i from ?_]; exact (mem_filter.mp e).2
 apply travel_local; intro a q r; symm; apply J.lamp; apply Finset.disjoint_left.mpr; intro s o t'
 obtain ⟨b,x,t⟩:=halo_spec.mp t'; obtain ⟨y,p,hg⟩:= halo_spec.mp (touches_near s h o)
 have hk:b∈visits i.1 (square i.2.val.1 i.2.val.2):=by change b∈ insert _ ({_}:Support W) at x; rcases mem_insert.mp x with l|l; rw [l]; exact q; rw [mem_singleton.mp l]; exact r
 have hm:separation i.1 b ≤ 4:= Extra.Iteration.Shapes.visits_dist _ _ _ hk
 apply v; apply halo_spec.mpr; refine ⟨y,p,?_⟩; have he:= separation_triangle y s i.1; have hv:= separation_triangle i.1 b s; rw [separation_comm s] at he; omega
lemma loom_miss : (misses (Y z) t).card ≤ (misses z.1 t).card*marginA (k+8)*Fintype.card PlaqAxes:=by
 let T:= Lattice.halo (k+8) (hem (misses z.1 t)); apply le_trans (card_le_card (t:=T ×ˢ univ) (fun i h'=>mem_product.mpr ⟨fleece z J h i h',mem_univ _⟩)); rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ ((Corona.halo_size (hem (misses z.1 t)) _).trans (Nat.mul_le_mul_right _ card_image_le))
omit J h
private lemma silt_price (U:Pane n)(a:Site W)(x:Face (Per W)): ‖silt a (Sum.inl x) U‖ ≤ SU.group.chord (faceValue U x):=by
 let T:=shiftH a x.1; have ht:= stopH a x.1;
 apply (SU.group.curvature_norm _).trans; apply Eq.le; unfold Nacre.boot; rw [travel_append,travel_append,stop_append]; simp_rw [ht,square_stop]; rw [show travel U x.1 (reverse T)=(travel U a T)⁻¹ from (by nth_rw 1 [←ht]; rw [travel_reverse])]; apply SU.group.chord_conj
private def shelf(V:Pane n)(t:ℝ)(w:ℕ): Finset (Site n) := univ.filter (fun i=> node i∈ Lattice.halo w (hem (misses V t)))
private lemma sunset (X:Pane n)(i:Site n)(v':0<v)(he:t≤v)(d:0<a)(w':w ≤ (More n).val)(hX:i∉ shelf X t w)(q:2≤v*Real.exp (a*w))(j:Ok n) : ‖silt (node i) j X‖ ≤ v*Real.exp (a*dial (node i) j):=by
 have hz: 0<(More n).val:= (More n).property; cases j with
 | inr i'=> exact le_trans ((SU.group.curvature_norm _).trans (SU.group.chord_le_two _)) (q.trans (show v*Real.exp (a*w) ≤ v* Real.exp (a*(More n).val) from by gcongr))
 | inl i'=>
    apply (silt_price X _ _).trans; by_cases h:t < SU.group.chord (faceValue X i'); swap; · refine (he.trans' (le_of_not_gt h)).trans (le_mul_of_one_le_right v'.le (Real.one_le_exp (by positivity)))
    have hp:w≤ dial (node i) (Sum.inl i'):= le_of_not_gt (fun l=>hX (mem_filter.mpr ⟨mem_univ i,halo_spec.mpr ⟨i'.1,mem_image_of_mem Prod.fst (mem_filter.mpr ⟨mem_univ i',h⟩),(separation_comm ..).trans_le l.le⟩⟩))
    exact (SU.group.chord_le_two _).trans (q.trans (by gcongr)) -- tune
lemma shelf_count(X:Pane n)(t:ℝ)(w:ℕ): (shelf X t w).card ≤ (misses X t).card * marginA w:=by
 rw [←card_image_of_injective _ needle]; refine (card_le_card (t:=Lattice.halo w (hem (misses X t))) ?_).trans ((Corona.halo_size ..).trans (Nat.mul_le_mul_right _ card_image_le)); intro i h; obtain ⟨v,l,rfl⟩:= mem_image.mp h; exact (mem_filter.mp l).2
lemma sugar_tag {z:Pane n} (T:Pride n)(i:Site n)(p:Lac T a C)(v':0≤v)(he:∀ j:Ok n, ‖silt (node i) j z‖ ≤ v*Real.exp (a*dial (node i) j)) : ‖Pec.tag (node i) (T i) z‖ ≤ v^2*C := by -- adapt Graph.aurP
 let x:= node i; have ht(h j:Ok n): ‖inner ℝ (silt x h z) (silt x j z)‖ ≤ v^2* nick a (contour x h j):=by
    apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (he h) (he j) (norm_nonneg _) (mul_nonneg v' (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos x h j])) (sq_nonneg v)
 apply (norm_sum_le ..).trans; apply (mul_le_mul_of_nonneg_left (p.pay i) (sq_nonneg v)).trans'; simp_rw [Pec.cents,mul_sum]; refine sum_le_sum fun u _=> (norm_sum_le ..).trans (sum_le_sum fun y _=>?_); rw [norm_smul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht u y) (norm_nonneg _)
abbrev accrues(w k:ℕ)(C:ℝ):= 4*(marginA (k+8)*Fintype.card PlaqAxes* marginA w:ℕ)*C
-- pointwise. Invites independent Beck.
include J h
lemma exactory (u:Lac T a C)(hc:0≤C)(a':0<a)(v':0<v)(ht:t≤v)(w':w ≤ (More n).val)(q:2 ≤ v* Real.exp (a*w)): ‖pigment T (Y z)‖ ≤ v^2*C*n.val^4 + accrues w k C *(misses z.1 t).card := by
 let X:=Y z; let A:= misses z.1 t; apply Graph.sealV; intro i; let V:=Yg (incX i) X
 have hp: (shelf V t w).card ≤ A.card*marginA (k+8)*Fintype.card PlaqAxes *marginA w:=by
    have he:(misses V t).card=(misses X t).card:=by unfold V; rw [Ywin]; exact match_miss X i 0
    exact (shelf_count V t w).trans (Nat.mul_le_mul_right _ ((he.trans_le (loom_miss z J h)))) -- direction
 rw [complX]; have hmo: ‖cSignX (Spire.detX i) (zinger T V)‖=‖zinger T V‖:=by unfold cSignX; split <;> first| rfl| apply norm_star
 rw [hmo]; apply (norm_sum_le ..).trans; let S:=shelf V t w; let f(x:Site n):= ‖Pec.tag (node x) (T x) V‖; rw [← sum_sdiff (s₁:=S) (s₂:=univ) (subset_univ _)]; apply add_le_add
 · apply le_trans (b:= (univ\S).card*(v^2*C)); apply (sum_le_sum (g:=fun _=>v^2*C) (fun i e=>sugar_tag T i u v'.le (sunset V i v' ht a' w' (mem_sdiff.mp e).2 q))).trans_eq; simp [S]
   rw [mul_comm (v^2*C)]; exact mul_le_mul_of_nonneg_right (show ((univ\S).card:ℝ) ≤ (n.val:ℝ)^4 from (Nat.cast_le.mpr (card_le_univ _)).trans_eq (by rw [site_card,Nat.cast_pow])) (mul_nonneg (sq_nonneg _) hc)
 have hK (i:Site n): f i ≤ 2^2*C:= sugar_tag T i u (by norm_num) (fun A=> ((SU.group.curvature_norm _).trans (SU.group.chord_le_two _)).trans (le_mul_of_one_le_right (by norm_num) (Real.one_le_exp (by positivity)))) -- shadow a'
 apply le_trans (sum_le_sum (g:=fun _=>2^2*C) (fun i _=>hK i)); rw [sum_const,nsmul_eq_mul]; apply le_trans (mul_le_mul_of_nonneg_right (show (S.card:ℝ) ≤ (((A.card*marginA (k+8)*Fintype.card PlaqAxes*marginA w):ℕ):ℝ) by exact_mod_cast hp) (mul_nonneg (sq_nonneg _) hc)); apply le_of_eq; unfold accrues A; push_cast; ring -- tune
end PhaseM
end YM.SU5.FiniteGaugeData.Cuprite.Spirit
