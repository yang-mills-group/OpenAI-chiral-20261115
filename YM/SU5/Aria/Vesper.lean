import YM.SU5.Aria.Curtsy
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric Casting
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "ω"=>P.colorZero j x
local notation "X"=> P.ColorHil j x
local notation "Ε"=> (P.physicalEnergy j x).E
local notation "τ✩"=> timeMesh P.par
local notation "γ"=> marks (timeMesh P.par)
local notation "Γ"=> P.VMark
variable (k:Trans j) (n:ℕ)
local notation "B"=>P.blade j x k
local notation "κ"=> P.enter j x
local notation "Θ"=> P.reflectTest k.val
local notation "ε"=> P.emmigrant j
local notation "Ṕ"=> P.voyageF j x
local notation "U" i:max=> ((Ṕ).crew i).play
section
variable {A:Type*}[AddCommGroup A]
noncomputable def mirrorΩ (x:Axis→ A):Axis → A:= fun i=>if i=j then -x j else x i
lemma mirrorΩ_sum(x y:Axis → A): mirrorΩ j (x+y)=mirrorΩ j x+mirrorΩ j y:= by funext i; by_cases p:i=j <;> simp [mirrorΩ,p,add_comm]
lemma mirrorΩ_neg(x : Axis→ A): mirrorΩ j (-x) = -mirrorΩ j x:=by funext i; by_cases p:i=j<;> simp [mirrorΩ,p]
lemma mirrorPose : Continuous (mirrorΩ j (A:=ℝ)):=by apply continuous_pi; intro i; by_cases h:i=j; subst i; simp only [mirrorΩ,if_pos rfl]; exact (continuous_apply _).neg; simp only [mirrorΩ,if_neg h]; apply continuous_apply -- inline h
lemma prism_poses (x:Γ): P.laysM (mirrorΩ j x)= mirrorΩ j (P.laysM x):=by funext i; by_cases h:i=j<;> simp [mirrorΩ,laysM,h]
end
local notation "F" z:max=>P.viewF j x z
lemma marchHeat (a:P.Test)(g:P.birthF j n a)(h:ℝ≥0): B (Ε h ((F n) g)) = Ε h (B ((F n) g)):=by
 let f:= (F n) g; let k':=k.val; let E₀:=P.physicalEnergy j x
 let r(t:ℝ≥0):= B (Ε t f); let s (t:ℝ≥0):= Ε t (B f); have hx:Continuous r:=(B).continuous.comp (E₀.continuousE f); have ht: Continuous s:=E₀.continuousE _
 have hw(t v:ℕ)(g': n≤t): r (whenly τ✩ t v)=s (whenly τ✩ t v):=by
   let u:= P.rig j n t g g'; have hu:f=(F t) u:=(P.view_rig j x n t g g').symm; unfold r s; rw [hu, ← P.releasedLater j x t v u]; rw [P.blade_view j x k t, P.blade_view j x k t,← P.releasedLater j x t v (P.crew_flies j k t u)]; exact P.identical_F j x t _ _ (P.meetrefl j k' _ _ (Ne.symm k.property)).symm
 change r h=s h
 exact tendsto_nhds_unique_of_eventuallyEq ((hx.tendsto h).comp (shade τ✩ h)) ((ht.tendsto h).comp (shade τ✩ h)) ((eventually_ge_atTop n).mono fun i p=> hw i _ p)
lemma blade_cold (t:ℝ≥0)(z:X): B (Ε t z)= Ε t (B z):=DFunLike.congr_fun (starinter _ (P.partner_dense j x) ((B).comp (Ε t)) ((Ε t).comp (B)) fun p=> P.marchHeat j x k p.1 p.2.val p.2.property t) z
private def σ (i:Trans j){A:Type*}[Neg A](x:A):=if i=k then -x else x
lemma norm_blade_shift (i:Trans j)(u:ℤ)(f:P.Test) : P.reflectTest k.val (P.shifts i.val u f)= P.shifts i.val (σ j k i u) (Θ f):=by
 by_cases h:i=k; · subst i; rw [σ,if_pos rfl]; exact meetOwn ..
 rw [σ,if_neg h]; exact (P.meetrefl i.val k.val _ _ fun v=> h (Subtype.ext v)).symm
private lemma shift_matches (t:ℕ)(i:Trans j)(u:ℤ): notch τ✩ t (σ j k i u)= σ j k i (notch τ✩ t u):=by
 unfold σ; split; swap; rfl
 apply Subtype.ext; change bell τ✩ t (-u) = -(bell τ✩ t u); simp [bell]
lemma marchShift (a:P.Test)(g:P.birthF j n a)(i:Trans j)(v: γ): B ((U i) v ((F n) g))= (U i) (σ j k i v) (B ((F n) g)):=by
 obtain ⟨t,u,rfl⟩:= notch_exists τ✩ v
 let W:=max t n; let z:=castor τ✩ t W u
 have he:n≤W:=le_max_right ..; let y:=P.rig j n W g he; have hy:(F n) g=(F W) y:=(P.view_rig j x n W g he).symm
 rw [hy, ← notch_up τ✩ t W (le_max_left ..), P.registered j x W i y z,P.blade_view j x k W (P.passes j W i.property z y), P.blade_view j x k W y, ← P.shift_matches j k W i z, P.registered j x W i (P.crew_flies j k W y)]; exact P.identical_F j x W _ _ (P.norm_blade_shift j k i z _)
lemma blade_vigil (i:Trans j)(v: γ)(y:X) : B ((U i) v y)= (U i) (σ j k i v) (B y):= DFunLike.congr_fun (starinter _ (P.partner_dense j x) ((B).comp ((U i) v)) (((U i) (σ j k i v)).comp (B)) fun p=> P.marchShift j x k p.1 p.2.val p.2.property i v) y
lemma blade_empty : B ω=ω:= by rw [← P.view_one j x 0, P.blade_view]; exact P.identical_F j x 0 _ _ (aureoleUnit ..)
lemma mirrored_truck (r:Γ) (b:X) : B (P.truck j x r b)= P.truck j x (mirrorΩ k.val r) (B b):=by
 unfold truck; generalize look j=L; induction L with
 | nil=> rfl
 | cons i L h=>
   simp only [Alliance.raw_step,ContinuousLinearMap.comp_apply,P.blade_vigil,Function.comp_apply,h]; congr 2; unfold σ mirrorΩ; by_cases p:i=k; · subst i; simp
   simp [p,show i.val ≠ k.val from fun h=>p (Subtype.ext h)]
lemma wings_in {u:X}(p:u∈P.Viewers j x): B u∈ P.Viewers j x:=by
 rw [Alliance.assembled] at p ⊢; intro i t; let V(w: γ):=σ j k i w; have ht:V∘ V=id:=funext fun w=>by by_cases h:i=k <;> simp [V,σ,h]
 have h:Continuous V:=by
   by_cases h:i=k; · simp [V,σ,h]; exact continuous_neg
   simp [V,σ,h]; exact continuous_id
 have hV:∀ w:γ,(U i) w (B u)= B ((U i) (V w) u):= fun w=>by rw [P.blade_vigil, show σ j k i (V w)=w from congrFun ht w]
 change ContinuousAt (fun w=> (U i) w (B u)) _; simp_rw [hV]; exact ((B).continuous.comp (((Ṕ).crew i).far (p i t)).continuous |>.comp h).continuousAt -- parens
noncomputable def fansM : Muse (P.ManyF j x) := ((B).comp ((κ).toContinuousLinearMap)).codRestrict _ (fun y=> P.wings_in j x k y.property)
lemma entersM (y:P.ManyF j x) : (κ) (P.fansM j x k y)= B (κ y):=rfl
lemma twinM (y:P.ManyF j x): (P.fansM j x k) (P.fansM j x k y)=y:= Subtype.ext (P.blade_twins j x k _)
lemma bank_companion (y:X): P.wealth j x (B y)= P.fansM j x k (P.wealth j x y):=by
 apply Subtype.ext; let θ:=B; let z:= (κ) (P.wealth j x y); change P.visitors j x _= θ z; rw [P.visitors_op]; apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (P.wings_in j x k (Alliance.planted _ _ _)); intro t v
 change inner ℂ (θ y-θ z) t=_; rw [←map_sub,← P.blade_twins j x k t]; have a:= P.blade_angle j x k (y-z) (θ t); rw [show inner ℂ (θ (y-z)) _=_ from a]
 rw [show z=(P.Viewers j x).starProjection y from DFunLike.congr_fun (P.visitors_op j x) y]; rw [show inner ℂ (y-(P.Viewers j x).starProjection y) (θ t)=0 from Submodule.starProjection_inner_eq_zero («K»:= P.Viewers j x) y (θ t) (P.wings_in j x k v)]; simp
lemma fan_empty : P.fansM j x k (P.heaven j x)=P.heaven j x:= Subtype.ext (P.blade_empty j x k)
lemma fan_stare (a:ℝ≥0)(u:P.ManyF j x): P.fansM j x k ((P.seasons j x).E a u)=(P.seasons j x).E a (P.fansM j x k u):= Subtype.ext (P.blade_cold j x k a _)
lemma fan_march (r:Vantage)(u:P.ManyF j x): P.fansM j x k (P.cartage j x r u)=P.cartage j x (mirrorΩ k.val r) (P.fansM j x k u):=by
 let A(v:Vantage):=(P.fansM j x k) (P.cartage j x v u); let T (v:Vantage):= P.cartage j x (mirrorΩ k.val v) ((P.fansM j x k) u)
 apply congrFun (P.marksDense.equalizer (g:=A) (h:=T) ((P.fansM j x k).continuous.comp (P.cart_cont j x u)) ((P.cart_cont j x _).comp (mirrorPose k.val)) (funext ?_)) r; intro i; unfold Function.comp A T; rw [← P.prism_poses]; apply (κ).injective; rw [P.entersM,← P.cart_and,← P.cart_and,P.entersM]; apply P.mirrored_truck
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.fan_march
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.bank_companion
