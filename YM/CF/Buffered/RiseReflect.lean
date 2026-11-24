import YM.CF.Buffered.PushMark
import YM.CF.Buffered.Naturality

/-!
# Geometrical reflection intertwines advancer

In particular, distance from the planes paid in native coordinates;
`theta` means @ that specified representative, outputs on its scaled
plane, as in the hypothesis of gaugeM. Full-measure exception for
priority ties. No epsilon-tie continuity assumption.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Buffered.Advance
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Push.SectorMeasure Scree RG Vault Fir Tree Next.SectorChange Girt Spire Stencil AnalyticBridge.GaussianFieldAlignment
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P : Side} (G : Ratio N P) (A : RG.StepData (More N) (More P))
variable (j : ℕ) (Q : Op SU.Slot) (M : Male) (ho : Odd G.count.val) (q : Chi) (d β : ℝ) (l : Loom N)
variable (i : Axis) (s : ℤ)
local notation "s₂" => (G.count.val * s : ℤ)
def tagMove (i : Axis) (s : ℤ) (N : Side) : Sweep N := ⟨Signed.mirror i, wrap N (s • step i),false⟩
local notation "k" => tagMove i s N
lemma with_tag (V : Pane N) : flashA k V=fling i s N V := by
  rw [revoke,fling_eq,show (assembly N).embed (k).b= _ from (assembly N).embed_wrap (s • step i)]; rfl
lemma tag_scale : reSweep G k = tagMove i s₂ P := by
  unfold reSweep tagMove; dsimp only; congr 1; rw [G.embed_wrap, mul_smul, natCast_zsmul]
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
private def shuffled : Equiv.Perm (Forest (ratio G)) := Equiv.ofBijective (fun F=>moveTree G A p F k) (Finite.injective_iff_bijective.mp (forest_move A (Signed.mirror i) ((assembly N).embed ((k).b)) _ p))
lemma move_middle (F : Forest (ratio G)) (X : Fields N) (Y : Fields P) : middle G q d (moveTree G A p F k) (reflFields i s₂ Y) (reflFields i s X)= stanza G (plane i s) inert (middle G q d F Y X) := by
  let Z := seine G F q d Y.2 X.2
  refine Prod.ext ?_ rfl; change seine G _ q d (fling i s₂ P Y.2) (fling i s N X.2)=stir inert (Shape.broad G (plane i s)) Z
  rw [plane_broad,←with_tag,← with_tag,←tag_scale, seine_mv,tag_scale,with_tag]; rfl
local notation "pre" => before G j Q M ho q d
local notation "run" => gathered G j Q M ho q d
variable {b : Bool} {S : Support (More N)} {f : Mark N} (h : AtSupport b S f)
include h p
lemma reflect_gathered (X : Fields N) (Y : Fields P) : run (reflMark i s f) (reflFields i s₂ Y) (reflFields i s X) = theta (carR i s₂ P) (run f Y X) := by
  let Λ:=shuffled G A i s p
  unfold gathered avgF; rw [theta_rsmul,theta_sum]; conv_lhs=> rw [← Equiv.sum_comp Λ]
  apply congrArg; refine sum_congr rfl fun F _=> ?_
  unfold before reflMark; rw [show Λ F=moveTree G A p F k from rfl, move_middle, reflFields_inv i s X]; exact sub_natural G j Q M ho i s _ (h.allV X)
omit h p
def reflOrbit (i : Axis) (s : ℤ) (N : Side) : MeasurableEquiv (Orbit N) (Orbit N) :=
  MeasurableEquiv.prodCongr ⟨⟨fling i s N,fling i s N,fling_invol i s,fling_invol i s⟩,(fling_cont ..).measurable,(fling_cont ..).measurable⟩
     ⟨⟨bun (tagMove i s N),bun (tagMove i s N)⁻¹,tuftT (tagMove i s N), fun x=> by simpa using (tuftT (tagMove i s N)⁻¹ x)⟩,(tuft (tagMove i s N)).measurable,(tuft (tagMove i s N)⁻¹).measurable⟩ -- (tagMove i s N) notation shadow parameters
lemma reflOrbit_mp : MeasurePreserving (reflOrbit i s N) (city N) (city N) := (fling_mp i s N).prod (tuft k)
variable {B₀ e : ℝ} {r : ℕ}
lemma roof_move (T : Roof N B₀ e r l) : ∀ᵐ x ∂city N, drawn l (reflOrbit i s N x)=reflFields i s (drawn l x) := by
  filter_upwards [(measurePreserving_snd («μ»:=prior group (More N)) («ν»:=depot N)).quasiMeasurePreserving.ae (Skye.sepT)] with x hx; rcases x with ⟨v,u⟩; refine Prod.ext ?_ ?_
  · rfl
  change l (fling i s N v,bun k u)=fling i s N (l (v,u)); simp_rw [←with_tag]; exact T.move v u k hx
variable (B : A.patch.Branches A.kernel SU.group)
include B p
lemma density_turn (X : Pane P) (Y : Pane N) : A.density β (fling i s₂ P X) (fling i s N Y) = A.density β X Y := by
  rw [fling_eq,fling_eq]; let v: Cover:=2 • (s • step i); rw [show wrap (More P) (2 • (s₂ • step i))=A.ratio.embed (wrap _ v) from ?_]; exact A.channel B ..
  rw [p,Ratio.embed_wrap,mul_smul,natCast_zsmul]; change wrap _ _=wrap _ (G.count.val • v); apply congrArg; unfold v; exact smul_comm ..
private def conjugator (N : Side) (U : UNI (Single N)) : FC (Single N) →L[ℝ] FC (Single N) := LinearMap.toContinuousLinearMap (⟨⟨theta U,theta_add U⟩,fun a x=>theta_rsmul U x a⟩ : FC (Single N) →ₗ[ℝ] FC (Single N)) -- includes? def include section
include h
local notation "pushM" => pushMark G A j Q M ho q d β l
theorem rising (T : Roof N B₀ e r l) {R : ℕ} (g : LaurentRadius j G.count R) (u : 0<d) (hw : 2*d<firstRadius SU.group) :
    pushM (reflMark i s f)=reflMark i s₂ (pushM f) := by
  funext z; set Y:=reflFields i s₂ z; let U := carR i s₂ P; let Λ:=reflOrbit i s N
  change pushM (reflMark i s f) z = theta U (pushM f Y)
  let F (x: Orbit N):= A.density β Y.1 x.1 • run f Y (drawn l x)
  let H (x: Orbit N):= A.density β z.1 x.1 • run (reflMark i s f) z (drawn l x)
  have ht:Integrable F (city N):= Env.integrableX (Env.scale (Env.along (slice_env A β B Y.1) measurable_fst) (Env.along (g:=fun x : Orbit N=>(Y,drawn l x)) (env_gathered G j Q M ho q d g u hw f h.env) (measurable_const.prodMk (drawn_m l T.bill)))) _
  rw [outright G A j Q M ho q d β l g T.bill B u hw _ (h.refl i s).env, outright G A j Q M ho q d β l g T.bill B u hw _ h.env]
  change (∫ i,H i ∂city N)=conjugator P U (∫ i,F i ∂city N)
  rw [←ContinuousLinearMap.integral_comp_comm _ ht, ← (reflOrbit_mp (N:=N) i s).integral_comp' H]; apply integral_congr_ae; filter_upwards [roof_move l i s T] with x hx; unfold F H; change A.density β z.1 _ • _=theta U _
  have hp: z=reflFields i s₂ Y := (reflFields_inv i s₂ z).symm
  rw [hx, hp,reflect_gathered G A j Q M ho q d i s p h, theta_rsmul]; exact congrArg (fun a : ℝ=> a • theta U (run f Y (drawn l x))) (density_turn G A β i s p B Y.1 x.1)
end YM.CF.Buffered.Advance
