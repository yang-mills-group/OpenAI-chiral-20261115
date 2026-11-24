import WakeRoad.Pulpwood
/-! # Oriented comparisons and deck legality. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option synthInstance.maxSize 25000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Tenant Tap Tulip Branch Fir Scree Buffered Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Skye Precision Tree Fock
attribute [local instance] opCStarAlgebra
open PhysicalNext.JointLoad.Heir
open YM.WakeRoad CF.Pannier.Chancel Rous Pressure Papal EmberWind Work.E08
open Gleam Regis Regis.Head Gleam.Wake
open CF.Gingham.Ruff
local notation "G₅"=> SU.group
open CF.Gingham.Ruff
namespace ArborJet
variable {N:Side}{m d s:ℕ}{S:Support (More N)}
local notation "M"=> Signed.mirror (3:Axis)
open CF.Gingham.Ruff CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.Gingham.VoyageB

-- Au libraries, mirrored laws
abbrev medley (b:Bool)(z:ℂ) := if b then star z else z
lemma medley_fee (b:Bool)(z:ℂ):‖medley b z‖=‖z‖:=by unfold medley;split <;> simp
lemma medley_scale (b:Bool)(z:ℝ)(x:ℂ):medley b (z • x)=z • medley b x:=by unfold medley; split <;> simp
lemma medley_diff (b:Bool)(x y:ℂ):medley b (x-y)=medley b x-medley b y:=by cases b <;> simp [medley]
lemma medley_sum (b:Bool){I:Type}(s:Finset I)(f:I→ℂ):medley b (∑ i∈s,f i)=∑ i∈s,medley b (f i):=by cases b <;> simp [medley]
lemma stamp_abs (i:Postcard m)(b:Bool):|stamp b i|=1:= by unfold stamp frigid; split<;>first | split<;>simp |simp
/-- scores on reflected poses -/
def portrait(b:Bool)(B:WakeRoad.Press (Postcard m))(i j:Postcard m):ℂ:= ((stamp b i)*(stamp b j)) • medley b (B i j)
lemma portrait_rec (b:Bool)(B:WakeRoad.Press (Postcard m))(x:WakeRoad.Paper m) :
  WakeRoad.Score (portrait b B) x = medley b (WakeRoad.Score B (fun i=> stamp b i*x i)):=by
  unfold WakeRoad.Score portrait; simp_rw [medley_sum, medley_scale,smul_smul]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [show x i*x j*(stamp b i*stamp b j)=stamp b i*x i*(stamp b j*x j) from by ring]
lemma portrait_coin (b:Bool)(B:WakeRoad.Press (Postcard m)): WakeRoad.coin (portrait b B) = WakeRoad.coin B:=by unfold WakeRoad.coin portrait; simp_rw [norm_smul,Real.norm_eq_abs, abs_mul,stamp_abs,medley_fee,one_mul]
variable (w:ℤ)(b:Bool){u:Side}{a δ v c e E:ℝ}{k r:ℕ}{p:BudgetPoint}{Z:Scree.Loom N}
   {f h:Chin N→OP N} (X:Rialto 6 e δ v)(B:GarlandBook u a c e f h)
   (U:Briefly p r e Z)(Y:Arioso X B.pump U)(T:Tagbill a E u k r p.B)(D:Web SU.group)(P:Parasols p δ (p.B/10+1))
local notation "β"=> p.B
local notation "τ"=>p.threshold
local notation "χ"=>p.B/10
local notation "o₀"=> (0:Seat N)
-- NB don't subtract musicA 0, pay constant
-- physical Mark normalization entirely real. hence equivariant
-- naming δ not included! include δ in def signature
abbrev ringmark(la0 δ:ℝ):Mark N:=if b then reflMark 3 w (( ((la0*δ)^2:ℝ):ℂ) • B.fountain U) else ((((la0*δ)^2:ℝ):ℂ) • B.fountain U)
def paletron(la0 δ:ℝ)(x:Pane N):ℂ:= medley b (((la0*δ)^2 :ℝ) • B.fountainQ U (attire w b x))
lemma ring_read (la0 δ:ℝ)(x: Fields N): ringmark w b B U la0 δ x= paletron w b B U la0 δ x.1 • 1:=by
 unfold ringmark paletron; cases b
 · change ((((la0*δ)^2:ℝ):ℂ)) • B.fountain U x=_; rw [B.fountainPure U]; rw [smul_smul]; simp [attire,medley, Complex.real_smul]
 change theta (carR 3 w N) ((((((la0*δ)^2:ℝ):ℂ)) • B.fountain U (reflFields 3 w x)))= _
 rw [B.fountainPure U (reflFields ..), theta_smul,theta_smul,theta_one,smul_smul]; rw [medley,if_pos rfl]; -- paletron medley after explicit change goal maybe implicit
 rw [star_smul];simp [Complex.real_smul,reflFields,attire]
#print axioms ring_read
private def tester(N:Side) : FC (Single N)→ℂ:=fun x=> x ∅ ∅
private lemma at_first (z:ℂ): tester N (z • 1)=z:=by simp [tester]
include T
lemma projected (la0 δ:ℝ)(h:going (N:=N) w b (β+2)⊆ S): AtSupport false S (ringmark w b B U la0 δ) ∧ covariant (ringmark w b B U la0 δ):=by
 have e:=B.fountain_premier U T
 let z:ℂ:= ((la0*δ)^2:ℝ); let F:= z • B.fountain U
 have v:covariant F:=fun u W=>by unfold F; simp only [Pi.smul_apply,e.tint u W,twist_scalar]
 have a:=AtSupport.smulM e.good z
 let L:= beagle (0:Site N) p
 have hp : L = BlockP (β+2) (0:Seat N):=by unfold L beagle BlockP hoop bouton; rw [←Ratio.root_embed,map_zero] -- name Ratio
 have wL: encasing w b L⊆S:= (show _⊆going w b _ by rw [hp,centered]; exact Corona.halo_mono (show β+2≤β+2+debt+12 by omega) le_rfl).trans h
 cases b; · exact ⟨a.mono wL,v⟩
 have hf: ((plane 3 w).anon N) = affine (Signed.mirror 3) (wrap (More N) (2 • w • step 3)) := rfl
 exact ⟨(a.refl 3 w).mono (by rw [hf]; exact wL),covariant_reflected a v w 3⟩
variable (la0:ℝ)
abbrev upperL (u:Side)(a c δ _w la0 t:ℝ):ℝ:= (la0*δ)^2* (refrain δ u a (pepCharge u a c) * t^2)
include Y
omit T in
lemma paletron_sale (V:Pane N):‖paletron w b B U la0 δ V‖ ≤ upperL u a c δ 0 la0 τ:=by rw [paletron,medley_fee,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]; exact mul_le_mul_of_nonneg_left (Y.value _) (sq_nonneg _)
lemma magazine: Envelope (paletron w b B U la0 δ) ∧ GaugeInvariant (paletron w b B U la0 δ):=by
 let A:= ringmark w b B U la0 δ; let f:=paletron w b B U la0 δ
 obtain ⟨p,t⟩:=projected w b B U T la0 δ (Subset.refl _)
 refine ⟨⟨?_,_,fun _=>paletron_sale w b X B U Y la0 _⟩,?_⟩ -- T maybe args?
 · have h : f=(fun i=>tester N (A (i,i))):=funext fun i=> ((congrArg _ (ring_read w b B U la0 δ (i,i))).trans (at_first _)).symm
   have hx: Measurable (tester N):= by apply Continuous.measurable; exact (continuous_apply _).comp (continuous_apply _) -- Op measurable from Matrix L2 conflict
   change Measurable f; rw [h]; exact (hx.comp (p.env.meas.comp (measurable_id.prodMk measurable_id)))
 intro g x; have w' := t g (x,x); simp_rw [ring_read,twist_scalar,map_one] at w'
 exact (at_first _).symm.trans ((congrArg (tester N) w').trans (at_first _))
