import YM.SU5.CompassRose.Piazza

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine Preparation.Yoke
open CF.Velvet CF.Pannier.Chancel CF.Pannier.Chancel.Rous Pressure
open YM.Stationary (Gaia)
open Onyx Regis.Circuit Regis.Head Regis.Head.Brecht Exterior Hiro

namespace Rose
open EmberWind Jewel
open Lamour Lamour.Bridge
variable (P:Spine)(s:ℕ)(A:ℝ)(β:ℕ→ℝ)
local notation "K"=> P.calibration
local notation "R" s:max=> sPow P.par s A
local notation "K!" f:max => Papal.household P.calibration f
local notation "P$" s:max => P.eReadL s
local notation "ζ⇒" => P.reflectTest 3
local notation "M$" => P.halfShift 3
local notation "lamp" X:max => temp (hat P.par.R.L P.par.x X)

open Fixture Shuttle Arrival
open SpinReceipt Maxwell Aria
-- ticket theorem using Quay & general atrium with common r. Usually have boundary-fit C p-power.
variable (v:ℕ→ℕ) (T:Pools P v β) (X Y:ℕ→ Cover)(x y:Gaia)(e:0<A)(a:Appoint P.par A X x)(b:Appoint P.par A Y y)(h:x≠y)
variable (F G:Fixture) (k:F.r=G.r)(q:P.PhysicalWakeGram){z t:ℝ}(p:Investment P.par z t)(N:Dispatchers P.par)(m:Meritorious P.par)
local notation "$↦" s:max F:max X:max => Fixture.litP P s A β F X
abbrev lampsGoal (F G:Fixture)(x y:Gaia):ℂ := F.dye*G.dye*(shotR F.lampS.spin G.lampS.spin (X:=x-y) * speckleV F.lampS.F G.lampS.F SU.group (x-y))
include T
private lemma passSeam (Y:ℕ→ Family P.calibration)(D:ℂ)(h:∀ s,TestFamily P.calibration true (Y s))(w:Tendsto (fun z:ℕ×ℕ=> Journey.sharp P.run P.large z.1 (Rose.period P (v z.2)) (Rose.cutoff P (v z.2)) (Y z.1)) bobbin (𝓝 D)) : Tendsto (fun s=> P.E s (Y s)) atTop (𝓝 D):=by
 let a(s i:ℕ):= Journey.sharp P.run P.large s (Rose.period P (v i)) (Rose.cutoff P (v i)) (Y s); have ht(s:ℕ):Tendsto (fun i=> a s i) atTop (𝓝 (P.E s (Y s))):=(sharp_on_track P.run P.law P.history s (h s)).comp T.up.tendsto_atTop
 exact reels (f:=fun z=>a z.1 z.2) (Eventually.of_forall fun r=>ht r) w
include q e
local notation "s₀" W:max r:max s:max=> offers P A s (W s) (r s) (κFix β s)
section
variable {W V:ℕ→Staff}{F G:PlaqAxes}{L D:DirSpin}{r w:ℕ→ℕ}(g:LayoutBudget P A x W r w F L)(u:LayoutBudget P A y V r w G D)
include g
lemma onePose : Tendsto (fun s=>P.E s (s₀ W r s)) atTop (𝓝 0):=by
 let X(s):= s₀ W r s; have h(s):TestFamily P.calibration true (X s):= aux_test ((center_goods P g s (κFix β s)).1); exact passSeam P β v T X 0 h (weave_price P T q g e)
include u h
lemma twoPose : Tendsto (fun s=>P.E s ((s₀ W r s)*(s₀ V r s))) atTop (𝓝 (shotR L D (X:=x-y)*speckleV F G SU.group (x-y))):= passSeam P β v T _ _ (fun s=>(aux_test (center_goods P g s (κFix β s)).1).mul (aux_test (center_goods P u s (κFix β s)).1)) (body_price P T q g u e h)
end
include a
lemma one_earn : Tendsto (fun s=> (P$ s) ($↦ s F (X s))) atTop (𝓝 0):=by
 let f(s:ℕ):= offers P A s (F.lampS.supportS (X s)) F.r (κFix β s); let φ(s):= P.E s (f s); have p':=F.lampS.obtains_at P A _ F.fitting e X x a
 have he:= (onePose P A β v T x e q p').const_mul F.dye
 rw [mul_zero] at he; unfold Fixture.litP; simp_rw [map_smul]; exact he
include b h k
local notation "Fg" s:max=> ($↦ s F (X s)) * ($↦ s G (Y s))
lemma two_earn : Tendsto (fun s=> (P$ s) (Fg s)) atTop (𝓝 (lampsGoal F G x y)):=by
 let W(s):=F.lampS.supportS (X s); let V(s):=G.lampS.supportS (Y s)
 let f(s:ℕ):= offers P A s (W s) F.r (κFix β s); let g(s:ℕ):= offers P A s (V s) F.r (κFix β s)
 let θ(s:ℕ):= f s*g s; let φ(s):= P.E s (θ s); let D:= shotR F.lampS.spin G.lampS.spin (X:=x-y)*speckleV F.lampS.F G.lampS.F SU.group (x-y)
 have hh(s:ℕ):g s=(poseP P s A β G (Y s)).val:=by unfold g; rw [k]; try rfl
 have p': LayoutBudget P A x W (fun _=> F.r) (fun _=> F.r) F.lampS.F F.lampS.spin:=F.lampS.obtains_at P A _ F.fitting e X x a
 have q': LayoutBudget P A y V (fun _=> F.r) (fun _=> F.r) G.lampS.F G.lampS.spin:=by rw [k]; exact G.lampS.obtains_at P A _ G.fitting e Y y b
 have he:= twoPose P A β v T x y e h q p' q'
 let ζ:= F.dye * G.dye; have hr(s:ℕ):(P$ s) (Fg s)= ζ * (P.E s (θ s)):=by
    unfold litP; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul]; simp only [smul_eq_mul]; unfold ζ θ; rw [hh,mul_assoc]; rfl
 simp_rw [hr]; exact he.const_mul ζ
omit b h k
include p N m
lemma one_lamp : WakePoll P (fun s=> $↦ s F (X s)) 0:=by
 let U(i:ℕ) (_:Unit):= X i; let V(_ : Unit):= x; let f(_ : Unit):=F; let H:=Piazza.Fbeams f [()] V
 have he : Tendsto (fun s=> (P$ s) ($↦ s F (X s))) atTop (𝓝 H):=by
    apply (Piazza.estimate P A β f U V [()] e p N m v T (fun i=>a) (fun i j _=> Eventually.of_forall fun _=>rfl) (List.pairwise_singleton ..)).congr; intro s; exact congrArg (P$ s) (mul_one ($↦ s F (X s)))
 let z:=Piazza.poll_aperture P A β f U V [()] e p N m v T (fun i=>a) (fun i j _=> Eventually.of_forall fun _=> rfl) (List.pairwise_singleton ..)
 exact (show H=0 from tendsto_nhds_unique he (one_earn P A β v T X x e a F q)) ▸ (show WakePoll P (fun s=> $↦ s F (X s)) H from (show (fun s=>Piazza.openC P s A β f [()] (U s))= _ from funext fun s=> mul_one ($↦ s F (X s))) ▸ z)
include b h k
lemma two_lamp : WakePoll P (fun s=> Fg s) (lampsGoal F G x y):=by
 let U(s:ℕ):= usher (X s) (Y s); let Y':=usher x y; let L:List Bool:=[false,true]; let f:= usher F G; let g(s):= Piazza.openC P s A β f L (U s)
 have ha(i:Bool): Appoint P.par A (fun s=> U s i) (Y' i):=by cases i; exact a; exact b
 have ht:Injective Y':= by rintro (_|_) (_|_) v; all_goals first| rfl | exact (h v).elim | exact (h v.symm).elim
 let w:= lampsGoal F G x y; have hv:g=(fun s=> Fg s):=funext fun s=>congrArg (($↦ s F (X s)) * ·) (mul_one ($↦ s G (Y s)))
 let C:= Piazza.Fbeams f L Y'; let t(i j:Bool)(p:Y' i=Y' j):∀ᶠ s:ℕ in atTop,U s i=U s j:= Eventually.of_forall fun _=> congrArg _ (ht p); let D : L.Pairwise (fun i j=> Y' i ≠ Y' j):= List.pairwise_pair.mpr h
 have he:Tendsto (fun s=> (P$ s) (g s)) atTop (𝓝 C):=Piazza.estimate P A β f U Y' L e p N m v T ha t D; rw [hv] at he; have hp: C=w:=tendsto_nhds_unique he (two_earn P A β v T X Y x y e a b h F G k q); let z:WakePoll P g C:=Piazza.poll_aperture P A β f U Y' L e p N m v T ha t D; rw [hp,hv] at z; exact z
omit a p b k N m T q h e

-- chosen layout target. displacement non-real chirality pairing, spatial gap along axis 2
-- strictly dominates time. large enough factor allows Minkowski aperture costs.
-- dynamic goal choose ← such that LEAD estimator at negative x and (poses/at0).
def leyline : Gaia:= WithLp.toLp 2 ![(1:ℝ),2,16,2]
def copper : Fixture:= ⟨⟨⟨(0,1),by decide⟩,false,false,(0,0),[]⟩,6,le_rfl⟩
abbrev onLey : ℂ := lampsGoal copper copper (-leyline) 0
lemma ley(i:Axis) : 0< leyline i:=by fin_cases i <;> norm_num [leyline]
lemma ley_seen : leyline≠ 0:=by intro e; have he:= ley 3; rw [e] at he; exact lt_irrefl 0 he
lemma weight_dead : onLey ≠0:=by
 let V:= leyline; let F:= copper.lampS.F; let U:= SU.group; let R':ℝ:=(Real.pi^2*‖V‖^4); have h0:=norm_pos_iff.mpr ley_seen; have p:0<R':=by unfold R' V; positivity
 have hV:kP20 V ≠0:=by
    rw [shapeWeyl]; unfold curlWeyl; apply mul_ne_zero (by norm_num); refine mul_ne_zero (show Complex.ofReal R'⁻¹/(2:ℂ)≠0 from div_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero p.ne')) (by norm_num)) (fun v=> (ley 3).ne' ?_)
    exact show V 3=0 from (by simpa using congrArg Complex.re v)
 have ht : specter F F (-V) ≠0:=by
    change (↑(bareCurl 0 1 0 1 (-V)):ℂ)≠0; rw [Maxwell.Bare.even ley_seen,Complex.ofReal_ne_zero]; have hs:‖V‖^2=265:= by
       rw [EuclideanSpace.real_norm_sq_eq]; change (∑ i:Fin 4, V i ^2)=_; norm_num [Fin.sum_univ_four,V,leyline]
       have he : ![(1:ℝ),2,16,2] (2:Fin 4)=16:=rfl; have ht : ![(1:ℝ),2,16,2] (3:Fin 4)=2:=rfl; rw [he,ht]; norm_num
    unfold bareCurl; simp_rw [Pi.sub_apply,Maxwell.Bare.opp_grad ley_seen,second_Green ley_seen]; unfold V at hs; rw [hs]; have h:=normal_pos; norm_num [leyline]; nlinarith
 unfold onLey lampsGoal Fixture.dye; change 1*1* (shotR (0,0) (0,0) (X:=-V-0) * _)≠0; rw [sub_zero,one_mul,one_mul]; apply mul_ne_zero
 · unfold shotR; change -60*kP20 _*kP20 (- - V) ≠ 0; rw [neg_neg,k_flip]; exact mul_ne_zero (mul_ne_zero (by norm_num) (neg_ne_zero.mpr hV)) hV
 change (Fintype.card U.ColorIndex:ℂ)*specter F F (-leyline)≠0; apply mul_ne_zero _ ht; haveI : Nontrivial SU.group.Color:= Thera.yet_one.nontrivial_color; have he:0<SU.group.lieDim:= by rw [Gauge.lieDim,← SU.group.colorIso.finrank_eq]; exact Module.finrank_pos
 change (Fintype.card (Fin SU.group.lieDim):ℂ) ≠0; rw [Fintype.card_fin]; exact_mod_cast he.ne'
#print axioms two_lamp
#print axioms weight_dead
end Rose
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
