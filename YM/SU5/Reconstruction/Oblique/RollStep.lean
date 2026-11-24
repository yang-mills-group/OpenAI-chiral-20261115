import YM.SU5.Reconstruction.Oblique.Natur
/-! # paying the *Tilted* on coarse and sharp. prior frames. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 32000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Tilted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
  Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin SatinVerification
namespace Ramp
open Reed (Fine think)
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG Vault Fir Tree Next.SectorChange Girt Spire Stencil AnalyticBridge.GaussianFieldAlignment
variable {N P : Side} (G : Ratio N P) (A : RG.StepData (More N) (More P))
variable (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)
variable (D:Ramp)
abbrev advance_tag(N:Side):Sweep N:=⟨D.s,0,false⟩
local notation "k" => Ramp.advance_tag D N
private lemma embedRoot {i j:Side} (g:Ratio i j) : g.embed 0=0:=by rw [←map_zero (wrap i),g.embed_wrap,smul_zero,map_zero]
lemma turn_prior (V : Pane N) : flashA k V=D.turnLink N V := by rw [revoke,D.turn_pull, show (k).b=0 from rfl, embedRoot]; rfl
lemma tag_meters: reSweep G k=D.advance_tag P:=by unfold reSweep advance_tag; dsimp only; rw [embedRoot]
variable (p : A.ratio=ratio G)
private lemma forest_move (e : Signed) (a : Seat N) (g : Ratio (More N) (More P)) (p : A.ratio=g) :
    Injective (fun F : Forest g=> ((p ▸ Locations.forest e a (S:=A) (p.symm ▸ F)) : Forest g)) := by
  subst g; intro x y h;
  have he : x.up=y.up := by
    funext i; obtain ⟨i,rfl⟩:= (StepData.sendSites e (A.ratio.embed a)).surjective i
    have hv : (x.up _).rotate e⁻¹=(y.up (affine e (A.ratio.embed a) i)).rotate e⁻¹:= congr_fun (congrArg Forest.up h) i
    have he:= congrArg (fun s:Step=>s.rotate e) hv; simp only [Step.rotate_mul,mul_inv_cancel,Step.rotate_one] at he; exact he
  have ht:x.height=y.height:= by
    funext i; obtain ⟨i,rfl⟩:= (StepData.sendSites e (A.ratio.embed a)).surjective i; exact congr_fun (congrArg Forest.height h) i
  cases x; cases y; congr
private def shuffled : Equiv.Perm (Forest (ratio G)) := Equiv.ofBijective (fun F=>moveTree G A p F k) (Finite.injective_iff_bijective.mp (forest_move A D.s ((assembly N).embed ((k).b)) _ p))
lemma rotate_middle(F:Forest (ratio G))(X:Fields N)(Y:Fields P): middle G q d (moveTree G A p F k) (D.both P Y) (D.both N X)=stanza G D.plan inert (middle G q d F Y X):=by
 let Z:=seine G F q d Y.2 X.2
 refine Prod.ext ?_ rfl; change seine _ _ _ _ (D.turnLink P Y.2) (D.turnLink N X.2)=stir inert (Shape.broad G D.plan) Z
 rw [D.plan_broad G,← turn_prior, ← turn_prior,← tag_meters G D,seine_mv,tag_meters G D,D.turn_prior]; rfl
local notation "pre" => before G j Q M ho q d
local notation "run" => gathered G j Q M ho q d
variable {b : Bool} {S : Support (More N)} {f : Mark N} (h : AtSupport b S f)
include h p
lemma turn_gathered(X:Fields N)(Y:Fields P): run (D.bill f) (D.both P Y) (D.both N X)= Fock.theta (D.vehicle P) (run f Y X) := by
 let Λ:=shuffled G A D p
 unfold gathered avgF; rw [theta_rsmul,theta_sum]; conv_lhs=>rw [←Equiv.sum_comp Λ]; -- keep
 apply congrArg; refine sum_congr rfl fun F _=>?_
 unfold before Ramp.bill; rw [show Λ F=moveTree G A p F k from rfl, rotate_middle,D.retrace]; exact Ramp.sub_natural G j Q M ho D _ (h.allV X)
omit h p
def slantOrbit (D:Ramp)(N:Side):MeasurableEquiv (Orbit N) (Orbit N) :=
 MeasurableEquiv.prodCongr ⟨⟨D.turnLink N,D.turnLink N,D.turnover,D.turnover⟩,(D.link_cont N).measurable,(D.link_cont N).measurable⟩
   ⟨⟨bun (D.advance_tag N),bun (D.advance_tag N)⁻¹,tuftT (D.advance_tag N),fun x=>by simpa using (tuftT (D.advance_tag N)⁻¹ x)⟩,(tuft (D.advance_tag N)).measurable,(tuft (D.advance_tag N)⁻¹).measurable⟩
lemma prior_link(N:Side): MeasurePreserving (D.turnLink N) (Wilson.prior SU.group (More N)) (Wilson.prior SU.group (More N)) := by rw [D.turn_pull]; exact Wilson.prior_pull ..
lemma tilt_mp : MeasurePreserving (D.slantOrbit N) (city N) (city N) := (prior_link D N).prod (tuft k)
variable {B₀ e : ℝ} {r : ℕ}
lemma roof_angles (T: Roof N B₀ e r l): ∀ᵐ x ∂city N, drawn l (D.slantOrbit N x)=D.both N (drawn l x):=by
 filter_upwards [(measurePreserving_snd («μ»:=Wilson.prior group (More N)) («ν»:=depot N)).quasiMeasurePreserving.ae Skye.sepT] with x hx
 rcases x with ⟨v,u⟩; refine Prod.ext ?_ ?_; · rfl
 change l (D.turnLink N v,bun k u)= D.turnLink N (l (v,u)); simp_rw [←turn_prior]; exact T.move v u k hx
variable (B:A.patch.Branches A.kernel SU.group)
include B p
lemma angular_density(X:Pane P)(Y:Pane N): A.density β (D.turnLink P X) (D.turnLink N Y)= A.density β X Y:= by
 rw [D.turn_pull,D.turn_pull, show (0:Site (More P))=A.ratio.embed 0 by rw [embedRoot]]; exact A.channel B ..
private def conjugator (N : Side) (U : UNI (Single N)) : FC (Single N) →L[ℝ] FC (Single N) := LinearMap.toContinuousLinearMap (⟨⟨Fock.theta U,theta_add U⟩,fun a x=>theta_rsmul U x a⟩ : FC (Single N) →ₗ[ℝ] FC (Single N)) -- includes? def include section
include h
local notation "pushM" => pushMark G A j Q M ho q d β l
theorem RampRise (T : Roof N B₀ e r l) {R : ℕ} (g : LaurentRadius j G.count R) (u : 0<d) (hw : 2*d<firstRadius SU.group) :
    pushM (D.bill f)=D.bill (pushM f) := by
  funext z; set Y:=D.both P z; let U := D.vehicle P; let Λ:=slantOrbit D N
  change pushM (D.bill f) z = Fock.theta U (pushM f Y)
  let F (x: Orbit N):= A.density β Y.1 x.1 • run f Y (drawn l x)
  let H (x: Orbit N):= A.density β z.1 x.1 • run (D.bill f) z (drawn l x)
  have ht:Integrable F (city N):= Env.integrableX (Env.scale (Env.along (slice_env A β B Y.1) measurable_fst) (Env.along (g:=fun x : Orbit N=>(Y,drawn l x)) (env_gathered G j Q M ho q d g u hw f h.env) (measurable_const.prodMk (drawn_m l T.bill)))) _
  rw [outright G A j Q M ho q d β l g T.bill B u hw _ (D.term_marked h).env, outright G A j Q M ho q d β l g T.bill B u hw _ h.env]
  change (∫ i,H i ∂city N)=conjugator P U (∫ i,F i ∂city N)
  rw [←ContinuousLinearMap.integral_comp_comm _ ht, ← (tilt_mp (N:=N) D).integral_comp' H]; apply integral_congr_ae; filter_upwards [roof_angles l D T] with x hx; unfold F H; change A.density β z.1 _ • _=Fock.theta U _
  have hp: z=D.both P Y := (D.retrace z).symm
  rw [hx, hp,turn_gathered G A j Q M ho q d D p h, theta_rsmul]; exact congrArg (fun a : ℝ=> a • Fock.theta U (run f Y (drawn l x))) (angular_density G A β D p B Y.1 x.1)
end Ramp
end YM.CF.Buffered.Afterglow.Tower.Tilted
