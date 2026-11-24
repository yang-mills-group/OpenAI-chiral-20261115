import YM.CF.Vol.Creche
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
open Tube Next.Fluctuations Work.F03 Nacre
open Next.SectorChange AnalyticBridge.GaussianFieldAlignment Oriented Rows
lemma commercial(K:Teller G)(p:G.Simple)(P:Patch)(hP:P.Branches K.bind G)(l n:ℕ)(hs:3 ≤ n)(W:Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2)):
 ∃ A C e:ℝ,0<A∧0<C ∧0<e ∧∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S)(F:Forest S.ratio), Cert P K S T x → sizedP G P K S T F →∀ (k:S.Choices)(s: Signed), Tabac T x F k s l n (A*(temp x)^(l+1)) C e:=by
 obtain ⟨B,t,b,hB,ht,hb,H⟩:=lift_paid p K P hP n l (by omega) W
 obtain ⟨C,E,hC,hE,H'⟩:=drawn K P (n+2) (by omega) W hP; obtain ⟨Y,e,hY,he,hD⟩:=drip K P hP (n+1) (by omega) W
 obtain ⟨A,v,hA,hv,hF⟩:=pluto K P hP (n+2)
 let M:= 1+Jet.composeCost n B 1; have hM:1 ≤ M:= le_add_of_nonneg_right (by unfold Jet.composeCost; positivity)
 let X:= shade G; have hx:0<X:=shade_pos G
 let R:=Jet.composeCost n Y X; have hR:0<R:=by unfold R Jet.composeCost; positivity
 let Z:= min (min ((min b 1)/2) (E/M)) (e/X); have hZ:0<Z:=lt_min (lt_min (by positivity) (by positivity)) (by positivity)
 refine ⟨1+1+C*t,max (Jet.composeCost n C M) R,Z,by positivity,hR.trans_le (le_max_right ..),hZ,?_⟩
 filter_upwards [H,smallF (n:=l+1) hv A,eventually_gt_atTop (0:ℝ)] with x hx hp hS c f S T F h hc k s
 obtain ⟨z,HZ,HX,hG⟩:=hx S T F h hc; let V:=sol S T k x F l; let F':= choice s k; have hV y (hy:‖y‖<b):=hG k y hy
 obtain ⟨hO,hm,hr⟩:= hV 0 (by simpa)
 let D:= temp x^(l+1); have hD':0<D:=pow_pos (Work.E09.temp_pos hS) _
 obtain ⟨hUL,hJ⟩:= H' S T F h.funds.1 h.got s F' (Stores.till x); have hUL':=hUL 0 (by simpa); have hJ':=hJ 0 (by simpa)
 let U:= pulse V; have hH(y:Ark T F)(hy:‖y‖< min b 1):Jet.Allows n U y M:= gum ((hV _ ((norm_fst_le _).trans_lt (hy.trans_le (min_le_left ..)))).1) ((hy.trans_le (min_le_right ..)).le)
 have hh: ‖(0:Ark T F)‖< min b 1:=by rw [norm_zero]; positivity
 have hu : DifferentiableAt ℝ V 0:= hO.smooth.differentiableAt (by exact_mod_cast (by omega : n≠0)); have hY0:U 0=0:=by simp [U,pulse, V, show V 0=0 from hm] -- tune
 have hK y (hy:‖y‖<Z) (i:Slots S):Jet.Allows n (gloss T x F k i) y R:=by
    let g:=pill T x F; have hy':‖g y‖ ≤ X*‖y‖:= (g.le_opNorm _).trans (mul_le_mul_of_nonneg_right pill_le (norm_nonneg _)); have hh := hy'.trans_lt (show X*‖y‖< e from ((mul_comm ..).trans_lt ((lt_div_iff₀ (shade_pos _)).mp (hy.trans_le (min_le_right ..)))))
    refine ((paper (hD _ T h.got h.funds.1 x k _ hh i)).order (show n ≤ n+1 by omega)).comp (Jet.allows_linear (show ‖g‖≤X from pill_le) (hy'.trans (mul_le_of_le_one_right (shade_pos _).le ((hy.le.trans ((min_le_left ..).trans (min_le_left ..))).trans ((half_lt_self (lt_min hb zero_lt_one)).le.trans (min_le_right ..))))))
 have hg(i):= (hK 0 (show ‖(0:Ark T F)‖ < Z by simpa) i).smooth.differentiableAt (by exact_mod_cast (by omega : n≠0)); let X:=A*Real.exp (-v*Stores.till x);
 have ht' y w:= hF S T F h.got h.funds z (HZ.critical) HX s F' (Stores.till x) y w C hUL'
 have hR:= mart (n:=n+2) T x F k s l h.funds.1 (t*D) C X (mul_nonneg hA.le (Real.exp_pos _).le) hJ' (by omega) (fun y=>⟨(ht' y 0).1,(ht' y 0).2.1⟩) (fun v=>(ht' 0 v).2.2) hg hm hu hr
 have hp : X ≤ D:= (mul_comm ..).trans_le hp; have he'(i):= hK 0 (by simp [hZ]) i
 have hi:X+X+C*(t*D) ≤(1+1+C*t)* D:=by linarith only [hp]
 obtain ⟨hp',hh',ht''⟩:= vehicles _ F h.funds.1 F' s _ hUL'; have hub:ContDiffAt ℝ (3:ℕ) U 0:= ((hH _ hh).order hs).smooth
 refine ⟨⟨fun i=>(hR.roof i).mono hi, fun i=>(hR.jamb i).mono hi, fun i=>(hR.letup i).mono hi, fun i=>(hR.nPole i).mono hi,fun i=>(hR.dPole i).mono hi⟩,fun i=>(down_D T x F k i h.funds.1 (hg i) 0).1,fun i=> (ride_eps ((hJ'.S i).analytic.of_le le_top) U hub hY0 (hp' i)).1,fun i=> (ride_eps ((hJ'.I i).analytic.of_le le_top) U hub hY0 (ht'' i)).1,fun i=>(ride_eps ((hJ'.Q i).analytic.of_le le_top) U hub hY0 (hh' i)).1,fun i=>face_nice (v:=0) h.funds.1 _,fun u hu=>?_⟩
 have hp': ‖u‖< min b 1:=(hu.trans_le ((min_le_left ..).trans (min_le_left ..))).trans (half_lt_self (lt_min hb zero_lt_one))
 have hp'':‖U u‖ < E:=by
    have ht := miles (n:=n) (x:=u) (show 1 ≤ n by omega) hH (lt_min hb zero_lt_one) hp' -- tune
    rw [hY0,sub_zero] at ht; exact ht.trans_lt ((mul_comm ..).trans_lt ((lt_div_iff₀ (zero_lt_one.trans_le hM)).mp (hu.trans_le ((min_le_left ..).trans (min_le_right ..)))))
 have hm := hJ (U u) hp''
 exact fund_s T x F k s l u _ M R (hH u hp') (⟨fun i=>(hm.roof i).order (by omega), fun i=>(hm.jamb i).order (by omega), fun i=>(hm.letup i).order (by omega),fun i=>(hm.dPole i).order (by omega),fun i=>(hm.nPole i).order (by omega),fun i=>(hm.pays i).order (by omega),fun i=>(hm.S i).order (by omega),fun i=>(hm.Q i).order (by omega),fun i=>(hm.I i).order (by omega)⟩) (hK _ hu)
end YM.CF.Vol
