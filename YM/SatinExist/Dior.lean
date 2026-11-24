import YM.SatinExist.Nugget
import YM.SatinExist.Minnow
import YM.SatinExist.CelesteB
import YM.SatinExist.CeladonA
import YM.SatinExist.Lack
import YM.SatinExist.Amy
import YM.SatinExist.Patina
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4100
set_option maxHeartbeats 430000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open OS.Semigroup (F)
open OS.Semigroup.Balloon
-- introduce double tail filter.P
variable (P:Spine)(x:P.Spectrum0 3) (n s m:ℕ)
open Aria Casting Six
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "q@" n:max => P.asked_at n
local notation "ℓ"=> P.calibration.ℓ
open Chalice
-- different layout for THREE-mark price. V-even on site at 0 allowed (not asserting ordered Pc unless all projections separated, here can ensure both side beams via Punctus)
local notation "∇" => ruler P.calibration.B
variable (f: Lead.Clan)
def latticeFieldEstimatesCost (n:ℕ)(i:Fin 3): Cover:= (![P.myroof n false,0,P.myroof n true]:Fin 3→ _ ) i
local notation "R@" i:max => P.latticeFieldEstimatesCost i
variable (B:ℝ)(A:ℝ)(G: Supplier)(R:P.Register)(T:uniform P R G B A)(d:P.NightCop)
local notation "Δ"=> P.NightCop
def Spinning (o:Cover) (ι:Axis) : P.Test:= ∑ p: Fin 2,∑ q:Fin 2,Window.alpha ι p q • P.onsiteRuby ((f,f.1),p,q) o n
-- extends to actual estimator across all. no claims unconditioned unless participate. pure comparison witness pays there too.
private abbrev QueueType := ℕ × ℕ × P.Spectrum0 3
local notation "Y"=> QueueType P
private def MeterM : Filter P.QueueType:= Filter.bind atTop (fun p:ℕ=> Filter.bind atTop (fun s:ℕ=> Filter.map (fun x:P.Spectrum0 3=>(p,s,x)) ⊤))
private lemma MeterP (x:Y→Prop): (∀ᶠ y in P.MeterM,x y) ↔ ∀ᶠ n:ℕ in atTop,∀ᶠ r:ℕ in atTop, ∀ t:P.Spectrum0 3,x (n,r,t):=by simp_rw [MeterM,eventually_bind,eventually_map, eventually_top]
local notation "D" => P.MeterM
private lemma arrieth : ∀ i:Fin 3,Tendsto (fun s:ℕ=>riseX (s:ℝ) (P.latticeFieldEstimatesCost s i)) atTop (𝓝 ( (corner ∘ (![(-1:ℝ),0,1]:Fin 3→ℝ)) i)):=by
 intro i; fin_cases i
 · exact P.roof_cost false
 · suffices h:(fun s:ℕ=>riseX (s:ℝ) (0:Cover))=fun _=>corner 0 from (h.symm ▸ (tendsto_const_nhds (f:=(atTop:Filter ℕ)) (x:=corner 0))) -- ▸ wrong tune
   ext i j
   change ((0:Cover) j:ℝ)/(i:ℝ)=corner 0 j; simp
 · exact P.roof_cost true
include T d
local notation "μ" i:max=>P.singleState 3 (i:ℕ× ℕ×P.Spectrum0 3).2.1 i.2.2
noncomputable abbrev hitRuby (a b c: Fin 2 × Fin 2) :P.Test:= P.onsiteRuby ((f,f.1),a) (P.myroof n false) n * (P.onsiteRuby ((f,f.1),b) 0 n * P.onsiteRuby ((f,f.1),c) (P.myroof n true) n)
private lemma remembers (a b c: Fin 2 × Fin 2): Tendsto (fun u:Y=> (μ u) (P.hitRuby u.1 f a b c)) (D) (𝓝 (numberX f*Window.sixM (corner (-1)) (corner 0) (corner 1) (Window.index f a.1 a.2) (Window.index f b.1 b.2) (Window.index f c.1 c.2))):=by
 let S':Fin 3→DirSpin:= ![a,b,c]; let Z:= torch S' f; let X:= List.finRange 3
 have ht: Chalice.depictionC Z X (corner ∘ (![(-1:ℝ),0,1]:Fin 3→ℝ))=_:= show _=(numberX f*Window.sixM (corner (-1)) (corner 0) (corner 1) (Window.index f a.1 a.2) (Window.index f b.1 b.2) (Window.index f c.1 c.2)) from Chalice.evening S' _ f 0 1 2 -- infer
 have hx : Tendsto (fun u:Y=> (μ u) (P.tuneK (pressC Z (R@ u.1) X (R:=u.1)))) (D) (𝓝 ( depictionC Z X (corner ∘ (![(-1:ℝ),0,1]:Fin 3→ℝ)))):=by
    apply Metric.tendsto_nhds.mpr; intro e p; apply (P.MeterP _).2
    apply P.matterU R 3 B A G T d Z (fun t i=>P.latticeFieldEstimatesCost t i) X _ e (fun i=>i) tendsto_id P.arrieth ?_ p; intro i j g; have he:=congrArg (fun x:Gaia=>x (3:Axis)) g; fin_cases i <;> fin_cases j <;> first | exact Eventually.of_forall (fun _=> rfl) | norm_num [Function.comp,corner] at he -- many simp
 rw [ht] at hx; apply hx.congr; intro v; apply congrArg (μ v); let X₁ i:=P.onsiteRuby (Z i) (P.latticeFieldEstimatesCost v.1 i) v.1
 change X₁ 0*(X₁ 1*(X₁ 2*(1:P.Test)))=_; rw [mul_one]; rfl
-- signal handedness via comparator already specified (opposite-handed TEMPLATE computed)
lemma chirality_net (v:ℝ)(p:0<v): ∀ᶠ n:ℕ in atTop,∀ᶠ s:ℕ in atTop, ∀ x:P.Spectrum0 3, let F:=P.Spinning n f; dist (P.singleState 3 s x (F (P.myroof n false) 0*(F 0 1 * F (P.myroof n true) 2))) (- ↑(Window.signedCost f (-1) 0 1))< v:=by
 let U(a:Y):= let n:=a.1; let F:=P.Spinning n f; F (P.myroof n false) 0 * (F 0 1 * F (P.myroof n true) 2)
 rw [show -((Window.signedCost f (-1) 0 1:ℝ):ℂ) = _ from (Window.left_price f (-1) 0 1).symm]
 let H(a b c: Window.Component):=(dimf f:ℂ)*Window.sixM (corner (-1)) (corner 0) (corner 1) a b c; let V:= wedgeThree 0 1 2 f H
 have hv(X_:Y): (μ X_) (U X_) = ∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,∑ l:Fin 2,∑ p:Fin 2,∑ q:Fin 2, (Window.alpha 0 i j*Window.alpha 1 k l*Window.alpha 2 p q)*((μ X_) (P.hitRuby X_.1 f (i,j) (k,l) (p,q))):=by
    let n:=X_.1
    unfold U Spinning; simp_rw [_root_.Finset.sum_mul, _root_.Finset.mul_sum,map_sum]; apply Finset.sum_congr rfl; intro i v; apply Finset.sum_congr rfl; intro j t; apply Finset.sum_congr rfl; intro k u
    apply Finset.sum_congr rfl; intro l x; apply Finset.sum_congr rfl; intro P' s; apply Finset.sum_congr rfl; intro q e; unfold hitRuby; rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Algebra.mul_smul_comm, Algebra.mul_smul_comm,map_smul,map_smul,map_smul,smul_eq_mul,smul_eq_mul,smul_eq_mul]; ring
 have hy:Tendsto (fun v:Y=> (μ v) (U v)) D (𝓝 V):=by
    simp_rw [hv]; unfold V wedgeThree
    refine tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun j _=> tendsto_finsetSum _ fun k _=> tendsto_finsetSum _ fun l _=> tendsto_finsetSum _ fun p _=> tendsto_finsetSum _ fun q _=>?_ ; exact (P.remembers f B A G R T d _ _ _).const_mul _
 exact (P.MeterP (fun a=> dist ((μ a) (U a)) V< v)).1 (Metric.tendsto_nhds.mp hy v p)
omit T d
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
