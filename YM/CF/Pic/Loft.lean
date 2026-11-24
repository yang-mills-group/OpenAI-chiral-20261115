import YM.CF.Pic.Firm
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N:Side}{u v a j K:ℝ}
-- leave any sector including cutoff boundary from much smaller central chart.
lemma beacon(N:Side)(X Y Z:Bkg N)(p:lawnK X Y u)(q:lawnK Y Z v): lawnK X Z (u+v):=fun i=> (cmp_triangle firstF (X i) (Y i) (Z i)).trans (add_le_add (p i) (q i))
lemma car_v{U V:Bkg N}(p:lawnK U V u):lawnK V U u:= fun i=>by rw [cmp_sym]; exact p _
lemma booth {n:Type*}[Fintype n][DecidableEq n](F:E→* UNI n)(A:Bkg N)(H:∀ i,Cube.cmp F (A i) 1 ≤ u):∀ w:Walk,∀ i:Site N,Cube.cmp F (travel A i w) 1 ≤ w.length*u:=by
 have hk(v:E):Cube.cmp F v⁻¹ 1=Cube.cmp F v 1:=by rw [Cube.cmp,Cube.cmp,map_one,map_inv]; change ‖star _-1‖=_; rw [← star_one (R:=Op n),←star_sub _ (1:Op n),norm_star]; rfl
 intro w; induction w with
 | nil=>simp [travel,cmp_id]
 | cons d w ih=>
   intro i; rw [travel,List.length_cons]; push_cast; rw [add_mul,one_mul,add_comm _ u]; apply (cmp_triangle F _ (travel A (i+d.vec) w) _).trans; refine add_le_add ?_ (ih _)
   let t:=travel A (i+d.vec) w; rw [show Cube.cmp F (_ * travel _ _ _) (travel A _ w)= Cube.cmp F (d.read A i) 1 from ?_]; swap; · exact Eq.trans (congrArg (Cube.cmp F (d.read A i*t)) (one_mul t).symm) (cmp_right F _ 1 t)
   unfold Step.read; split; rw [hk]; exact H _; exact H _
lemma boost(k:ℝ)(p:0<k):∃ r:ℝ,0<r∧ ∀ (N:Side) (U:Bkg N), lawnK U 1 r→ Guard U k :=by
 obtain ⟨C,c,H⟩:=gulf; have hp:0<C:=zero_lt_one.trans_le c; let x:= k/(4*C); have ht:0<x:=by unfold x; positivity
 refine ⟨x,ht,fun n u g=>⟨fun i y z _=> ?_,fun i y z _=>?_⟩⟩
 · have hv:= booth firstF u (u:=x)  g (square y z) i; rw [Cube.cmp,map_one] at hv; apply le_trans hv
   change _*x≤k; have he:(4:ℝ)*C*x=k:=by unfold x; field_simp
   simp only [square,List.length_cons, List.length_nil]; norm_num; nlinarith
 have h(i):Cube.cmp matter (u i) 1≤C*x:=(H _ _).trans (mul_le_mul_of_nonneg_left (g i) hp.le)
 have he:= booth _ u h (square y z) i; rw [Cube.cmp,map_one] at he; apply le_trans he; simp only [square,List.length_cons, List.length_nil]; norm_num; unfold x; field_simp; simp
-- arc length at most delta. interval continuous transK and packed near
lemma allure:∃ (C δ:ℝ),1 ≤ C∧0<δ∧∀ N:Side,∀ (U V:Bkg N) (k:ℝ),0<k→k ≤ δ→lawnK U V k → ∃ p:ℝ→Bkg N,p 0=U ∧ p k=V ∧ ∀ y∈ ball (0:ℝ) (2*k), TransK 1 p y C ∧ lawnK (p y) U (C*|y|):=by
 obtain ⟨b,d,h,u,G⟩:= glow; obtain ⟨C,c,L⟩:=servo (max b 1) (le_max_right ..); refine ⟨C,min d (1/3),c,lt_min u (by norm_num),fun n U V k hk H l=>?_⟩
 have ht(i): ‖fund (V i*(U i)⁻¹)-1‖≤ k:=by apply le_trans _ ((car_v l) i); rw [cmp_g firstF (V i) (U i)]; exact le_rfl
 choose x hz p using fun i=>G _ k (H.trans (min_le_left ..)) (ht i)
 let Y i:= k⁻¹ • x i; have hK(i):‖Y i‖ ≤ b:=by unfold Y; rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤k⁻¹)]; exact (mul_le_mul_of_nonneg_left (p i) (by positivity :0≤k⁻¹)).trans_eq (by field_simp)
 let X(y:ℝ)(i):=SU.group.lieExp (y • Y i)*U i; have he:X 0=U:=by unfold X; simp; -- tune
 have hS(y:ℝ)(e:y∈ball (0:ℝ) (2*k)):TransK 1 (N:=n) X y C:= by
   rw [mem_ball_zero_iff] at e; exact fun i=> L _ (Y i) ((hK i).trans (le_max_left ..)) y (by have hp:k≤1/3:= H.trans (min_le_right ..); change |y|< _ at e; linarith)
 refine ⟨X,he,?_,fun y e=>⟨hS y e,fun i=>?_⟩⟩
 · funext i; unfold X Y; rw [smul_inv_smul₀ hk.ne',hz,inv_mul_cancel_right]
 rw [← he]; change ‖fund (X y i)-fund (X 0 i)‖ ≤ _; simpa only [sub_zero] using (town (x:=y) (y:=0) (fun t=>fund (X t i)) _ (convex_ball 0 (2*k)) e (mem_ball_self (by positivity)) fun a b=> hS a b i) -- rewrite he
-- war freezes near tax. easy angle.
lemma leanC(r:ℝ)(h:0<r):∃ t:ℕ,∀ N:Side,t ≤ N.val→∀ P:Candle, slowT N P→lawnK (N:=N) (Kea.tax P) 1 r:=by
 obtain ⟨s,t,V⟩:= Metric.continuousAt_iff.mp (phase_cont.continuousAt (x:=0)) (r/5) (by positivity)
 obtain ⟨m,u⟩:= exists_nat_gt (40*Real.pi/s); refine ⟨m,fun N e P hp i=>?_⟩
 let X:= waveG (P i.2); change ‖fund X-1‖ ≤ r; unfold X; rw [wave_id]
 apply le_trans (Sods.cost_D _ (k:=r/5) _ (by positivity))
 · simp [F]; linarith
 intro a b; by_cases p:a=b; swap; · simp [Matrix.sub_apply,p, Matrix.one_apply,h.le]; positivity
 rw [p, Matrix.sub_apply,Matrix.diagonal_apply_eq,Matrix.one_apply_eq]; apply le_of_lt; let x:=(P i.2).val b; have he:(40*Real.pi)/s < (N.val:ℝ):=u.trans_le (Nat.cast_le.mpr e); have hh: |x| < s:= (hp _ _).trans_lt (by rw [div_lt_iff₀ t] at he; exact (div_lt_iff₀ (nPos _)).mpr (by linarith)); simpa only [Function.comp_def,phase_z,dist_eq_norm] using V (show dist x 0<s from by simpa using hh) -- tune rwa
end YM.CF.Pic
