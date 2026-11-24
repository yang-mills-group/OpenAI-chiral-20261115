import YM.SU5.Circuit.Lieble
import YM.SU5.Regis.Hospitality
import SatinThinCitizen
/-! # P3. Real clover near a finite motion ruler. Lean proof inspired by bridge
 `Petals`; on actual `Circuit` Gaussian per-lag on period to allow this query. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2500
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Regis.Head
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset Exterior Precision RG Work.F03 Gleam MeasureTheory NormedSpace ProbabilityTheory Wilson Matrix
open Circuit Work.G06 AnalyticBridge.VerifiedReset StressFlux Brecht
open scoped Matrix Topology BigOperators NNReal ENNReal InnerProductSpace ContDiff Classical Matrix.Norms.Frobenius
namespace Etch
variable {n c:Side}{G:Gauge}{k ρ:ℝ}
-- explicit slots plus signs combined in **current** average (sign normalization).
def atTray (a b: Bool) (i:Lattice.PlaqAxes): RG.Slot:= ⟨ if a then if b then [negDir i.val.1,negDir i.val.2] else [negDir i.val.1] else if b then [negDir i.val.2] else [], i ⟩
def petalsCore(i: Lattice.PlaqAxes): RG.Slot:=atTray false false i
lemma square_read (i:Lattice.PlaqAxes)(V:CoverConfig G):
    clover V 0 i.val.1 i.val.2=(4:ℝ)⁻¹ • (((atTray false false i).eval V + (atTray false true i).eval V)+((atTray true false i).eval V+(atTray true true i).eval V)):=by
 let A:=i.val.1; let B:=i.val.2
 have he(a b: Lattice.Step) : StressFlux.plate V 0 a b= slanted [] a b V:=by simp [slanted, StressFlux.plate,travel,stop]
 unfold clover stencil; simp_rw [he]; apply congrArg ((4:ℝ)⁻¹ • ·)
 have hp: slanted [] (posDir A) (negDir B) V = - (atTray false true i).eval V:=by rw [slanted_swap [] (negDir B), ←slanted_next]; rfl
 have hv: slanted [] (negDir A) (posDir B) V= - (atTray true false i).eval V:=by rw [← slanted_next,slanted_swap ([]++[negDir A]) ( (negDir A).rev)]; rfl
 have h': slanted [] (negDir A) (negDir B) V= (atTray true true i).eval V:=by rw [← slanted_next,← slanted_next ]; rfl -- repeat left? choose
 rw [hp,hv,h',show slanted ..= (atTray false false i).eval V from (show slanted [] (posDir i.val.1) (posDir i.val.2) V= (atTray false false i).eval V from rfl)] -- tune implicit
 abel
lemma tray_read (i:Lattice.PlaqAxes)(o:Site n)(V: Config G n):
    clover V o i.val.1 i.val.2=(4:ℝ)⁻¹ • (((atTray false false i).atSite V o + (atTray false true i).atSite V o)+((atTray true false i).atSite V o+(atTray true true i).atSite V o)):=by
 rw [← show clover (expandAt o V) 0 i.val.1 i.val.2=(4:ℝ)⁻¹ • (((atTray false false i).atSite V o + (atTray false true i).atSite V o)+((atTray true false i).atSite V o+(atTray true true i).atSite V o)) from square_read i (expandAt o V)]; have h(a b:Lattice.Step): StressFlux.plate V o a b = StressFlux.plate (expandAt o V) 0 a b:=by apply congrArg G.curvature; rw [travel_at,map_zero,zero_add] -- tune
 simp_rw [clover,stencil,h] -- loop? tune
abbrev Tray:= Bool × Bool
-- bookkeeping
open scoped Classical
abbrev spigot (X:Tray→G.Color): G.Color:= (4:ℝ)⁻¹ • ((X (false,false) + X (false,true))+(X (true,false)+ X (true,true)))
lemma spigot_cost (X Y:Tray→ G.Color): dist (spigot X) (spigot Y) ≤ dist X Y:=by
 have h: spigot X - spigot Y=spigot (X-Y):=by unfold spigot; simp only [smul_add,smul_sub,Pi.sub_apply]; abel
 rw [dist_eq_norm,h,dist_eq_norm]; let V:=X-Y; change ‖spigot V‖ ≤ _; rw [spigot,norm_smul,Real.norm_of_nonneg (by positivity : (0:ℝ)≤4⁻¹)]
 have ht: ‖V (false,false)+V (false,true)+(V (true,false)+V (true,true))‖ ≤ 4*‖V‖:=by have hh(i:Tray): ‖V i‖≤ ‖V‖:= norm_le_pi_norm ..; exact le_trans (norm_add_le ..) ((add_le_add (le_trans (norm_add_le ..) (add_le_add (hh (false,false)) (hh (false,true)))) (le_trans (norm_add_le ..) (add_le_add (hh (true,false)) (hh (true,true))))).trans_eq (by ring))
 exact (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤4⁻¹)).trans_eq (by change _=‖V‖; ring)
lemma spigot_zero : spigot (fun _=> (0:G.Color))=0:=by simp [spigot]
-- adapt Lieble.estimates on ViewMu
private lemma distOne (h:0<k)(x y:ℝ)(p:0≤x)(t:x≤y): |viewμ k (y^2)-viewμ k (x^2)| ≤ (1+k) * (y-x) :=by -- remove G
 let D:=1+x^2/k; let S:=1+y^2/k; have hv:1≤ D:= le_add_of_nonneg_right (by positivity); have ht:0<S:=by unfold S; positivity
 have hp:0<D:=by linarith
 have hc:y+x≤ (1+k)* S:= by unfold S; field_simp; nlinarith only [t,sq_nonneg (y-1),sq_nonneg (y-k),h, mul_le_mul_of_nonneg_left t h.le, mul_nonneg h.le (sq_nonneg y)] -- tune ∼2 \sqrt k
 have ha:0≤ y-x:=sub_nonneg.mpr t
 have he:viewμ k (y^2)-viewμ k (x^2)=(y-x)*((y+x)/S)/D:=by unfold viewμ; change y^2/S-x^2/D=_; field_simp; unfold D S; ring
 rw [he,abs_of_nonneg (by have hp':0≤y:=p.trans t; positivity : 0≤(y-x)*((y+x)/S)/D),mul_comm (1+k)]; exact (div_le_self (by have hp':0≤y:=p.trans t; positivity) hv).trans (mul_le_mul_of_nonneg_left ((div_le_iff₀ ht).mpr hc) ha)
-- single petal port
noncomputable def mellow (G:Gauge)(i:PlaqAxes)(k:ℝ)(p:0<k): Etch G Tray where
 slot u:= atTray u.1 u.2 i
 f x:= viewμ k (‖spigot x‖^2)
 arc:=k
 favor := ⟨1+k,by positivity⟩
 bound i:= (abs_of_nonneg (clipμ p _ (sq_nonneg _)).1).trans_le (clipμ p _ (sq_nonneg _)).2.1
 diff:= by
    let F: (Tray→ G.Color)→ℝ:=fun y=> ‖spigot y‖^2; have he:ContDiff ℝ 1 F:= (contDiff_norm_sq ℝ).comp (show ContDiff ℝ 1 spigot from by unfold spigot; fun_prop)
    apply he.div (contDiff_const.add (he.div_const k)); intro y; change 1+ F y/k≠0; unfold F; positivity
 steady:= LipschitzWith.of_dist_le_mul fun x y=>by
    have ht(w v: Tray→G.Color)(h: ‖spigot v‖≤ ‖spigot w‖) : dist (viewμ k (‖spigot w‖^2)) (viewμ k (‖spigot v‖^2)) ≤ (1+k)*dist w v:= (distOne p _ _ (norm_nonneg _) h).trans (mul_le_mul_of_nonneg_left ((norm_sub_norm_le (spigot w) (spigot v)).trans (by rw [←dist_eq_norm]; exact spigot_cost w v)) (by positivity))
    rcases le_total ‖spigot x‖ ‖spigot y‖ with h|h; · rw [dist_comm x,dist_comm _ (viewμ ..)]; exact ht y x h
    exact ht x y h
 move x y:=by
    rw [show spigot _=G.adjoint x (spigot y) from (?_),G.norm_adjoint]; unfold spigot; rw [map_smul,map_add,map_add,map_add]
lemma mellow_arc(p:0<k)(i:PlaqAxes): (mellow G i k p).arc=k:=rfl -- G removed variable? globally implicit metavariable warn
lemma mellow_favor(p:0<k)(i:PlaqAxes): ((mellow G i k p).favor:ℝ)=1+k:=rfl
lemma mellow_eval (F:Lattice.PlaqAxes)(x:Config G n)(p:0<k)(ρ:ℝ): (mellow G F k p).here ρ x=viewμ k (‖ρ • petals x 0 F‖^2):=by
 rw [Etch.here_eq]; apply congrArg (viewμ k); apply congrArg ((· ^ 2) : ℝ → ℝ); apply congrArg norm; rw [petals,tray_read]; unfold mellow; dsimp only; unfold spigot; rw [smul_comm ρ (4:ℝ)⁻¹]; simp_rw [smul_add] -- tune
end Etch
end YM.Regis.Head
#print axioms YM.Regis.Head.Etch.mellow_eval
