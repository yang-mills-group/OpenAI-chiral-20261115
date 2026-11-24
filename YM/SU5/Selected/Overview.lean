import YM.SU5.Selected.MeshSym
/-!
# Extend the rank-bought character state to the determining tower

Full local Tapestry polynomials, `well` gauge invariant subalgebras and their extensions
in the resolution system (before requiring relativistic restoration). In other words, not a
Wightman/OS field algebra, supports are real spacetime regions and uses the explicit purchase
porch with stencil as part of the support. Heights are independent of cutoffs and periods. ALL
compositions in all levels (even per slot in `Dome`, not a theory of two odd operators at distinct
rungs unless these are written into a single `Dome` test). True multi-resolution state, one ﬁxed
axis as merely a naming choice for the phase, and same even-form star across EVERY axis. The
reflection statement is qualified by vertices/scale; we use `Sunlight` which pays the finer (4B)
plane (also odd parities), no claim here about continuous rotations, nor Lorentz covariance of this
Euclidean slab system. Include gauge action and specify identification at paid level grids of trans
in those coordinates (also LAWS across levels on the `jetty` with allowed rungs; fractional moves
not defined on lower rungs).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
open Tapestry.Exhibition Tapestry.Altitude Set Sunlight
namespace Spine
variable (P : Spine) (R : P.Register) (j : Axis)(x : P.Spectrum0 j)
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "K"=> P.calibration
local notation "Λ"=> P.par
local notation "L₀"=> P.par.R.L.val
local notation "l"=> P.width
local notation "π"=> P.history
local notation "F"=> P.Test
local notation "D"=> P.talks R
local notation "D₁"=> vistaDressing Y H (P.talks R)
local notation "Ψ"=> P.singleState
local notation "θ" n:max => P.singleState j n x
local notation "κ" k:max => P.otherSpectrum j k
local notation "w✓" => P.Spectrum0 j
local notation "λ'" s:max=> Heat.gaugeShift P.par.block s
local notation "R₀" n:max => vistaFinish Y H n (P.talks R)
abbrev Algebra0 := FiniteGaugeDataPoly P.calibration
abbrev Effect := Cloud P.Test
local notation "E"=> P.Effect
lemma passage (s:ℕ): (P.singleState j (s+1) x).comp ((vistaDressing Y H (P.talks R)).surge s) = P.singleState j s x:= LinearMap.ext fun f=>by
  change P.singleState j (s+1) x (P.promote s R f)=_; rw [P.single_state,P.single_state,P.promotes_read]
noncomputable def spirits : Cloud P.Test→ₗ[ℂ]ℂ:= Decking.fadeRead (D₁) (auxiliaryPad K) (fun i=>P.singleState j i x) (fun i=> P.passage R j x i)
local notation "φ"=> P.spirits R j x
lemma useSpirit (s:ℕ) (f:P.Effect) (e:f∈shorter P.Test s) : (P.spirits R j x f)= P.singleState j s x ((R₀ s) f) := Decking.fate _ s f (auxiliaryPad K) _ (fun i=> P.passage R j x i) e
lemma spirit_one : P.spirits R j x 1=1:=by rw [spirits,Decking.fadeOne] ; rw [P.single_state,P.reading_unit,map_one]
abbrev slotHole (s:ℕ) := pinhole P.Test s
lemma oneCup (s:ℕ)(f : P.Test): P.spirits R j x (P.slotHole s f)=(θ s) f:=by rw [P.useSpirit R j x s _ (short_pinhole s f)]; exact congrArg _ (show (R₀ s) (P.slotHole s f)=f from (D₁).outcrop (auxiliaryPad K) s f)
lemma orthogonal_colors (k:Axis)(f:E)(p:f∈FiniteGaugeDataPoly K) : P.spirits R k (P.otherSpectrum j k x) f=P.spirits R j x f:=by obtain ⟨n,p⟩:= curve.mp p; rw [P.useSpirit _ _ _ n f p,P.useSpirit _ _ _ n f p,P.single_agrees]
lemma spirit_gauge (u:GPhysical)(f:E)(p:f∈FiniteGaugeDataPoly K):
    P.spirits R j x (rainfall Λ K u f)=P.spirits R j x f:=by
  obtain ⟨s,t⟩:=curve.mp p
  rw [P.useSpirit R j x s _ (raining_height Λ K s u t),P.useSpirit R j x s _ t, vistaRain Y H s _ _ f t,P.single_state,P.reading_gauge,P.single_state]
-- finitary evaluation & chosen common projection for arbitrary resolution polynomial (cap in Ensemble). E recovers integral over χ.
lemma spirit_cont {f:E}(e:f∈FiniteGaugeDataPoly K): Continuous (fun x=> P.spirits R j x f):=by
  obtain ⟨s,u⟩:= curve.mp e; simp_rw [P.useSpirit R j _ s f u]; exact P.chi_joint j _
lemma spirit_price {f:E}(e:f∈FiniteGaugeDataPoly K): (∫ x, P.spirits R j x f ∂ (P.pillars j))=vistaTake Y H (P.talks R) f:= by
  obtain ⟨s,u⟩:= curve.mp e; simp_rw [P.useSpirit R j _ s f u,P.single_state]; rw [P.recovery,vistaCall Y H s _ D u]; exact P.occupied j s _
/- This actual joint **coherent path** is a purchase for all these readings
   (on earlier geometry/pivot prices). No assertion of selected-Euclidean field
   value as limit of original UV ratios -- they reconstruct only the average. -/
set_option maxHeartbeats 80000 in
private lemma vista_limit (f:E)(e:f∈FiniteGaugeDataPoly K) : Tendsto (fun n:WedgeStage=>taking Y H
      (P.period n.vol) (P.cutoff n.uv) f) followStage (𝓝 (vistaTake Y H (P.talks R) f)):=by
  obtain ⟨n,h⟩:=curve.mp e; obtain ⟨S,u⟩:= anyWords K n f h; obtain ⟨C,v⟩:= issued.mp u; exact (Fashion.livePocket Y H R.exhibition S n v).2
set_option maxHeartbeats 150000 in
lemma spirits_limit (f:E)(e:f∈FiniteGaugeDataPoly K): Tendsto (fun n=>taking Y H
      (P.period (P.projection.rows n)) (P.cutoff (P.projection.columns n)) f) atTop (𝓝 (∫ x, P.spirits R j x f ∂ (P.pillars j))):=by
  let I₀:ℂ:= (∫ x, P.spirits R j x f ∂ (P.pillars j)); let v:ℂ:=vistaTake Y H D f; let t:ℕ→ℂ:=(fun n=>taking Y H (P.period (P.projection.rows n)) (P.cutoff (P.projection.columns n)) f)
  have hh: I₀=v:= P.spirit_price R j e; have h:Tendsto t atTop (𝓝 v):= by
    have he:= (vista_limit P R f e).comp (P.all_heights_here R)
    apply he.congr; intro n; rfl
  change Tendsto t atTop (𝓝 I₀); rwa [hh]

variable (k:Axis)(z:Sunlight P.par)
local notation "S"=> z.arena Λ
local notation "S₀"=> Sunlight.sanctum Λ l k z K
local notation "z₀"=> z.hinge Λ
local notation "ξ"=> z.oppose Λ k K
local notation "ϱ" n:max=> aureole K k (z.marks n)
local notation "T₀" V:max t:max=> jetty Λ l K true V t
lemma reflected_hat_at (n:ℕ)(a:z.start≤ n){f g:E}(p:f∈ z.cloister Λ l k K n)(q:g∈ z.cloister Λ l k K n) :
    P.spirits R j x (z.oppose Λ k K f*g)= P.singleState k n (P.otherSpectrum j k x)
      ((ϱ n) ((R₀ n) f) * (R₀ n) g):=by
  rw [P.useSpirit R j x n _ (show ξ f*g∈shorter P.Test n from (shorter ..).mul_mem (z.respectsCut Λ l k K p) (jettyBan Λ l _ _ _ _ n q)),single_agrees];
  exact congrArg _ (reflectionHat Λ l k z n (D₁) _ (glass Y H D k z) a p q)
lemma spirit_positive (f:E)(p:f∈ Sunlight.sanctum Λ l k z K) : 0 ≤ P.spirits R j x (z.oppose Λ k K f*f):=by
  obtain ⟨n,a,t⟩:= limitsArena Λ l k z K p
  rw [P.reflected_hat_at R j x k z n a t t]
  let u:=glass Y H D k z
  obtain ⟨V,v,g⟩:= crownShelter Λ l n (D₁) (auxiliaryPad K) u.lantern (flank k z₀) u.onward t
  obtain ⟨b,e⟩:= z.shifted n a
  have hp:= (z.rents Λ l k n a).1 g
  rw [e] at hp ⊢; exact P.elevated k n (P.otherSpectrum j k x) ((R₀ n) f) b (show _ from v) (show Tower.region k (λ' b) (K).ℓ V from hp) -- z proof
noncomputable def glow : S₀ →ₗ⋆[ℂ] (S₀→ₗ[ℂ] ℂ):= lustre (φ) (ξ) ((S₀).val.toLinearMap)
lemma glow_positive (x':S₀) : 0≤ P.glow R j x k z x' x' := P.spirit_positive R j x k z _ x'.property
lemma spiritGram {m:Type*}[Fintype m] (f:m→P.Effect) (e:∀ i, f i∈ z.sanctum Λ l k K) :
    Matrix.PosSemidef (Matrix.of fun i k'=> P.spirits R j x (z.oppose Λ k K (f i)*f k')) :=
  lustred (P.glow R j x k z) (P.glow_positive R j x k z) (fun i=> ⟨f i,e i⟩)
variable (O:Set RSpace) (t : Set ℕ)(b: t⊆ z.arena P.par)
-- reflection of whole state, not requiring positive-side labels
include b in
lemma visions (f:ℕ→ P.Test)(p : Officer t (fun i=>keep Λ l i K true O) f)(n:ℕ)(u:z.start ≤ n):
    (D₁).finish n (opponent Λ k z K f)=(ϱ n) ((D₁).finish n f):= by
  let A:= D₁; have he i (x:F): A.perceive i x=x:=rfl
  induction n,u using Nat.le_induction with
  | base=>
    have hw(i)(u:i<z.start) : i∉ t:=fun a=>u.not_ge (b a)
    rw [Decking.finish_alone _ _ (Sunlight.opponent Λ k z K f) ?_, Decking.finish_alone _ _ f (fun i h=>p.forbids i (hw i h))]; rfl
    intro i h; rw [Sunlight.opponent,plumeTail,p.forbids i (hw i h),aureoleUnit]
  | succ n u ih=>
    let Z:= (Sunlight.opponent Λ k z K f); rw [Decking.finish,Decking.finish,ih,aureoleProduct]
    refine congrArg₂ (· * ·) ?_ rfl
    change liftD Y H n _ _ = aureole K k _ (liftD Y H n _ _); rw [Breflect,z.aligned n u]
include b in
lemma visions_cast {n:ℕ}(f:E)(e:f∈jetty Λ l K true O (t ∩ Set.Iic n)) (u:z.start ≤ n):
    vistaFinish Y H n (P.talks R) (z.oppose Λ k K f)=(ϱ n) (vistaFinish Y H n (P.talks R) f):=by
  apply boarded (P:={f| Officer (t∩ Set.Iic n) (fun i=>keep Λ l i K true O) f}) (M:=fun x=>_) ?_ ?_ ?_ ?_ e
  · intro f (p:Officer _ _ f); have he:= p.visible (t∩ Set.Iic n) _ Set.inter_subset_right
    change (R₀ n) (ξ (pureShot K f))= (ϱ n) ((R₀ n) (pureShot K f)); rw [opposes]
    unfold vistaFinish pureShot; rw [Decking.reckon_paid _ _ _ he,Decking.reckon_paid _ _ _ (z.opponentEnough Λ k n K he)]; exact P.visions R k z O (t∩ Set.Iic n) (Subset.trans Set.inter_subset_left b) f p n u
  · simp
  · intro a t p q u v; rw [map_add,map_add,u,v,map_add,map_add]
  intro r a p q; rw [LinearMap.map_smulₛₗ,map_smul,q,map_smul,LinearMap.map_smulₛₗ]
include b
lemma reflections_live {f : E}{wide:Bool} (p:f∈ jetty Λ l K wide O t):
    P.spirits R j x (z.oppose Λ k K f)= star (P.spirits R j x f):=by
  obtain ⟨i,h⟩:= entrusted Λ l _ _ O t ((exposes Λ l K wide O t) p)
  let n:=max i z.start; have a:z.start≤ n:=le_max_right ..; have he:f∈jetty Λ l K true O (t∩ Set.Iic n):=
    admits Λ l K true O O (t∩Set.Iic i) (t∩Set.Iic n) (fun j h=> ⟨h.1,le_trans (show j ≤ i from h.2) (le_max_left ..)⟩) Subset.rfl h
  let d:= P.otherSpectrum j k x
  have hq(f:P.Test): P.singleState j n x f=P.chi k d (P.reading k n f):= (P.single_agrees ..).symm
  rw [P.useSpirit R j x n _ (show ξ f∈ shorter P.Test n from jettyBan Λ l _ true _ t n (z.opposition Λ l k K («S»:=t∩Set.Iic n) (Subset.trans Set.inter_subset_left b) O true he)),P.useSpirit R j x n _ (show _ from jettyBan Λ l K true O t n he),P.visions_cast R k z O t b f he a]
  obtain ⟨c,e⟩:= z.shifted n a
  rw [hq,hq,e,P.lightStar,map_star]
omit b
section
variable (s : ℕ) (d : ℤ)
local notation "r" x:max=> (glare P.par s x)
lemma star_pin (f:P.Test) : z.oppose P.par k P.calibration (pinhole P.Test s f)=pinhole P.Test s (aureole P.calibration k (z.marks s) f):=by
  rw [pinhole_apply,pinhole_apply]; change ξ (pureShot K _)=pureShot K _; rw [Sunlight.opposes]; apply congrArg (pureShot K); funext i
  by_cases h:i=s; · subst i; rw [Sunlight.opponent,plumeTail,update_self,update_self]
  rw [Sunlight.opponent,plumeTail,update_of_ne h,update_of_ne h,aureoleUnit]
noncomputable def along_grid (z z':Sunlight Λ) : P.Effect→ₐ[ℂ] P.Effect := AlgHom.ofLinearMap
  ((z'.oppose Λ k K).comp (z.oppose Λ k K))
  (by change z'.oppose Λ k K (z.oppose Λ k K 1)=_; rw [z.opposeOne,z'.opposeOne])
  (fun x y=>by change z'.oppose Λ k K (z.oppose _ _ _ (x*y))= _; rw [Sunlight.opposeMany,Sunlight.opposeMany]; rfl )
def rotate_grids (z z':Sunlight Λ): P.Effect ≃ₐ[ℂ] P.Effect:= AlgEquiv.ofAlgHom (P.along_grid k z z') (P.along_grid k z' z) (AlgHom.ext (fun _=>congrArg (z'.oppose _ _ _) (z.turns _ _ _ _) |>.trans (z'.turns _ _ _ _))) (AlgHom.ext (fun _=> congrArg (z.oppose _ _ _) (z'.turns _ _ _ _) |>.trans (z.turns _ _ _ _)))
abbrev fullWalk : P.Effect≃ₐ[ℂ] P.Effect:= P.rotate_grids k (r 0) (r d)
-- these spatial symmetry names are on allowed meshes. `rotate_grids` translates by only one coord, not claiming a spatial dilation/rotation.
local notation "q" d:max=> mirrorE k ((glare P.par s d).hinge P.par)
lemma walk_pin {n:ℕ} (p:s ≤ n) (f:P.Test): P.fullWalk k s d (pinhole P.Test n f) = pinhole P.Test n (P.halfShift k (smill P.par s n d) f):=by
  change ((r d).oppose Λ k K) ((r 0).oppose Λ k K (pinhole F n f))=_; rw [P.star_pin,P.star_pin]
  apply congrArg _; apply Subtype.ext
  have h(d:ℤ) : (r d).marks n=gaugeShift (Λ).block (smill Λ s n d):=if_pos p
  rw [h,h,show gaugeShift (Λ).block (smill Λ s n 0)=0 by unfold smill gaugeShift; ring]; rfl
lemma spirit_walk (a:t ⊆ Set.Ici s) {f:E}{wide:Bool} (p:f∈ jetty Λ l K wide O t) :
    P.spirits R j x (P.fullWalk k s d f)=P.spirits R j x f := by
  change φ ((r d).oppose Λ k K ((r 0).oppose Λ k K f))=_
  rw [P.reflections_live R j x k (r d) ((q 0) '' O) t a ((r 0).opposition Λ l k K a O wide p),P.reflections_live R j x k (r 0) O t a p,star_star]
/-- Actual displacement in gauge units. `bell` for the original even spatial grid is in
    **fermion** units; this one offsets by half that shift (i.e., equals bell in gauge units). -/
def translate (z:ℝ)(x:RSpace) : RSpace:= fun i=> if i=k then x i+z else x i
local notation "M"=> timeMesh P.par
lemma move_between : ((q d) ∘ (q 0))=translate k (bell M s d) := by
 funext x i; by_cases p:i=k; swap; · simp [Function.comp_apply,translate,p,mirrorE]
 subst i
 have h(d:ℤ): (glare Λ s d).hinge Λ = markZ Λ s (gaugeShift (Λ).block d):=by
    exact congrArg (markZ Λ s) (glareFound Λ s d)
 simp only [Function.comp_apply,translate,mirrorE,if_true,h]
 unfold markZ precisionAt gaugeShift bell mill timeMesh; change 2*((_:ℝ)/_)-(2*(_/_)-_)=_ + (d:ℝ)*(((8*(Λ).block.val:(ℝ≥0))/((L₀:ℝ≥0)^s):ℝ≥0):ℝ)
 push_cast; ring
lemma walk_local (a:t ⊆ Set.Ici s){f:E}{wide:Bool}(p:f∈ well Λ K l wide O t) :
    P.fullWalk k s d f∈ well Λ K l wide (translate k (bell M s d) '' O) t:=by
  rw [← P.move_between,Set.image_comp]
  exact flipWell Λ K l wide ((q 0) '' O) t k (r d) a (flipWell Λ K l wide O t k (r 0) a p)
lemma walk_jetty (a:t⊆Set.Ici s){f:E}{wide:Bool}(p:f∈ jetty Λ l K wide O t) :
    P.fullWalk k s d f∈ jetty Λ l K wide (translate k (bell M s d) '' O) t:=by
  rw [← P.move_between,Set.image_comp]; exact (r d).opposition Λ l k K a _ wide ((r 0).opposition Λ l k K a _ wide p)
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.useSpirit
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.spirits_limit
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.spiritGram
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reflections_live
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.walk_local
