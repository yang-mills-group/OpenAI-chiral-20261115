import YM.SU5.Six.AnchorPos
import YM.SU5.Six.Photos
import YM.SU5.Six.Rates
import YM.SU5.Aria.Grotto
import YM.SU5.Six.KeepCharge
import YM.SU5.Six.MirrorCharge
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)

/-!
# Propagating rank to every macroscopic scale

No real-time/spacelike covariance assumption. Use the axis of variation in
commonWell's own ordered result even for movement of transverse positions;
REAL pose continuation in a strictly Euclidean ordered domain.
-/
section
variable (H:Hilbert)(j:Axis)(S:OS.Semigroup H j)(x y:H)
lemma heat_analytic : AnalyticOnNhd ℝ (fun t:ℝ=> inner ℂ x (S.E t.toNNReal y)) (Set.Ioi 0):= by
  intro t p
  let g(z:ℂ):= inner ℂ x (S.F z y)
  have hp: (t:ℂ)∈ OS.Semigroup.inside := by exact p
  have he: AnalyticAt ℂ g (t:ℂ):= ((innerSL ℂ x).analyticAt _).comp ((ContinuousLinearMap.apply ℂ H.space y).analyticAt _ |>.comp (S.localHeat _ hp))
  have ht: AnalyticAt ℝ (g ∘ Complex.ofRealCLM) t:= he.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
  apply ht.congr
  filter_upwards [isOpen_Ioi.mem_nhds p] with t u
  have h : OS.Semigroup.duration t.toNNReal=(t:ℂ):= congrArg ((↑) : ℝ→ℂ) (Real.coe_toNNReal t (le_of_lt u))
  exact congrArg (fun A:H.Op=>inner ℂ x (A y)) ((congrArg S.F h.symm).trans (S.roots_heat (Real.toNNReal_pos.mpr u)))
end
section
variable (P:Spine)(x:P.Spectrum0 3)(J:P.Ellis 3 x)(s n:ℕ)(Z W:Lead.Clan)(σ:Orders)
open Casting
local notation "A"=> P.gridStory s n Z W
local notation "w"=> P.probeWidth s n
local notation "F"=> P.transmission x s n Z W
local notation "η"=> ([false,true]:List Bool)
local notation "ι"=> P.advocate 3 x
variable (p:Vantage)
include J
lemma transmission_cont (u:2*(w 3) < p 3): ContinuousAt F p:= by
  let q:=usher (0:Vantage)
  have h: Continuous q:=continuous_pi (fun i=>by cases i; exact continuous_const; exact continuous_id)
  exact (P.common_cont 3 x A (usher 0 p) η J ⟨3,η,List.Perm.refl _,P.turnTransmission s n Z W p (by linarith only [u])⟩).comp h.continuousAt
lemma transmission_analytic (j:Axis) : AnalyticOnNhd ℝ (fun t=> F (update p j t)) (OrderSlab σ w j):= by
  let X:= P.advocate 3 x j; let Q:=P.cartage j X; let S:=P.seasons j X; let E:= S.E
  let H:=P.ManyF j X
  let V:= P.gridStory s n Z W false; let D:= P.gridStory s n Z W true
  let B:= P.probeWidth s n j
  unfold OrderSlab
  split
  · rename_i h
    let z:= glareY x V j; let y:=flashY x D j
    let t':= Q p y
    have hT(t:ℝ)(u:2*B<t) : F (update p j t)= inner ℂ z (E ((t-(B+B)).toNNReal) t'):= by
      let p':=update p j t; have he: p' j=t:= update_self ..
      have hp: V.realWidth P j+D.realWidth P j<p' j:= by change B+B<p' j; rw [he]; linarith only [u]
      refine (avail_cross x V D j p' J hp).trans ?_
      have hh: Q p'=Q p:= of_slideP x j p' p (fun i g=>update_of_ne g ..)
      exact congrArg (inner ℂ z) (congrArg₂ (fun (a:ℝ)(v:H)=> E a.toNNReal v) (congrArg (fun x:ℝ=> x-(B+B)) he) (DFunLike.congr_fun hh _))
    intro t g
    have hv: AnalyticAt ℝ (fun u:ℝ=>u-(B+B)) t:= analyticAt_id.sub analyticAt_const
    apply ((heat_analytic H j S z t' (t-(B+B)) (show 0<t-(B+B) by linarith only [show 2*B<t from g])).comp (f:=fun u:ℝ=>u-(B+B)) hv).congr
    filter_upwards [isOpen_Ioi.mem_nhds g] with i f using (hT i f).symm
  rename_i h
  -- reverse order, price memorial at indices swapped and shifted
  let z:= glareY x D j; let y:= flashY x V j
  let t':= Q (-p) y
  have hT(t:ℝ)(u:t< -(2*B)) : F (update p j t)= inner ℂ z (E ((-t-(B+B)).toNNReal) t'):= by
    let p':=update p j t; have he:p' j=t:= update_self ..
    let a:=A; let v:= usher (0:Vantage) p'; let k:=usher (-p') (0:Vantage); let l:List Bool:=[true,false]
    have hp:P.Turnstile j a l k:= List.pairwise_pair.mpr (show (0:ℝ)+B< (-p') j-B by rw [Pi.neg_apply,he]; linarith only [u])
    have hh:l.Perm η:= List.Perm.swap ..
    have hz:P.commonWell 3 x a v η=P.memorial j X a l k:= by
      have Hs: v=settler k p':=by funext i; cases i; exact (add_neg_cancel _).symm; exact (add_zero _).symm
      rw [Hs]; exact (P.common_shift 3 x a k η J ⟨j,l,hh.symm,hp⟩ p').2.trans (P.common_cult 3 x a k η J hh.symm hp)
    have hs:P.memorial j X a l k=P.memorial j X (usher D V) η (usher (0:Vantage) (-p')):=by
      rfl
    have hq:= of_slideP x j (-p') (-p) (fun i g=>by rw [Pi.neg_apply,Pi.neg_apply,show p' i=p i from update_of_ne g ..])
    refine hz.trans (hs.trans ((memorial_two x D V j (-p')).trans ?_))
    exact congrArg (inner ℂ z) (congrArg₂ (fun (a:ℝ)(v:H)=> E a.toNNReal v) (congrArg (fun x:ℝ=> -x-(B+B)) he) (DFunLike.congr_fun hq _))
  intro t g
  have hv:AnalyticAt ℝ (fun u:ℝ=> -u-(B+B)) t:= analyticAt_id.neg.sub analyticAt_const
  apply ((heat_analytic H j S z t' (-t-(B+B)) (show 0< -t-(B+B) by linarith only [show t< -(2*B) from g])).comp (f:=fun u:ℝ=> -u-(B+B)) hv).congr
  filter_upwards [isOpen_Iio.mem_nhds g] with i f using (hT i f).symm
end
-- matrix noncollapse, and analytic on slices. Doesn't need a quotient topology on fields.
variable {P:Spine}{x:P.Spectrum0 3}(J:P.Ellis 3 x)(s n:ℕ)(σ:Orders)
local notation "w"=>P.probeWidth s n
local notation "M"=>P.pointMatrix x s n
local notation "U"=> OrderChamber σ w
private def tourney (a:Matrix Lead.Clan Lead.Clan ℂ):ℂ:= a.det * ∏ i:Lead.Clan, a i i
private lemma tourney_accepts (a:Matrix Lead.Clan Lead.Clan ℂ) : tourney a ≠ 0 ↔ ReadsSix a:= by
  rw [tourney,mul_ne_zero_iff,Finset.prod_ne_zero_iff]; simp [ReadsSix]
include J
lemma first_analytic (p:Vantage)(j:Axis): AnalyticOnNhd ℝ (fun t=> tourney (M (update p j t))) (OrderSlab σ w j):= by
  let F(t:ℝ):=M (update p j t)
  intro t u
  have hh(a b:Lead.Clan): AnalyticAt ℝ (fun t=> F t a b) t:= P.transmission_analytic x J s n a b σ p j t u
  unfold tourney
  refine AnalyticAt.mul ?_ (Finset.analyticAt_fun_prod _ (fun i _=>hh i i))
  change AnalyticAt ℝ (fun t=> (F t).det) t
  simp_rw [Matrix.det_apply']
  exact Finset.analyticAt_fun_sum _ fun a _=> analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _=> hh _ _))
lemma live_isOpen : IsOpen {p|p∈U ∧ ReadsSix (M p)} := by
  apply isOpen_iff_mem_nhds.mpr; rintro p ⟨u,f⟩
  have he: ContinuousAt M p:= continuousAt_pi.mpr (fun Z=>continuousAt_pi.mpr (fun W=>P.transmission_cont x J s n Z W p (order_forward σ w p u)))
  exact inter_mem ((chamber_open σ w).mem_nhds u) (he.preimage_mem_nhds (readsSix_open.mem_nhds f))
lemma live_isDense (h:∃ p∈ (U), ReadsSix (M p)): U ⊆ closure {p| p∈U ∧ ReadsSix (M p)}:= by
  rintro p hp
  apply mem_closure_iff_nhds.mpr
  intro R u
  by_contra f
  let v:= R∩(U)
  obtain ⟨ε,he,hε⟩:= Metric.mem_nhds_iff.mp (show v∈𝓝 p from inter_mem u ((chamber_open σ w).mem_nhds hp))
  let F:= tourney ∘ M
  have hx(L:Finset Axis)(z:Vantage)(y:z∈U)(hz:∀ j:Axis,j∉L→dist (z j) (p j)<ε): F z=0:= by
    induction L using Finset.induction_on generalizing z with
    | empty=>
      have hu:z∈R:=(hε (Metric.mem_ball.mpr ((dist_pi_lt_iff he).2 (fun j=>hz j (Finset.notMem_empty _))))).1
      by_contra g
      exact f ⟨z,hu,y,(tourney_accepts _).1 g⟩ -- tune direction
    | @insert i L hi ih=>
      let W:= OrderSlab σ w i
      let G(t:ℝ):= F (update z i t)
      have hv: IsPreconnected W:= by unfold W OrderSlab; split <;> first| exact (convex_Ioi _).isPreconnected| exact (convex_Iio _).isPreconnected
      have gt : G =ᶠ[𝓝 (p i)] 0 := by
        filter_upwards [(Metric.ball_mem_nhds (p i) he), (slab_open σ w i).mem_nhds (hp i)] with t g ht
        apply ih (update z i t)
        · intro j; by_cases H:j=i
          · subst j; rw [update_self]; exact ht
          rw [update_of_ne H]; exact y j
        intro j hj; by_cases H:j=i
        · subst j; rw [update_self]; exact g
        rw [update_of_ne H]; exact hz j (by simpa only [Finset.mem_insert,not_or] using And.intro H hj)
      have a₁: EqOn G 0 W:= (show AnalyticOnNhd ℝ G W from first_analytic J s n σ z i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hv (hp i) gt
      exact (congrArg F (Function.update_eq_self i z).symm).trans (a₁ (y i)) -- tune
  obtain ⟨q,g,k⟩:=h
  exact (tourney_accepts _).2 k (hx Finset.univ q g (fun j e=> False.elim (e (Finset.mem_univ j))))
-- continuous positions of *both* bodies.
lemma live_poses (h:∃ p∈ (U),ReadsSix (M p)) :
    let V := {x:Vantage × Vantage|x.2-x.1∈U}
    let W := {x:Vantage × Vantage| x∈ V ∧ ReadsSix (M (x.2-x.1))}
    IsOpen W ∧ V⊆closure W:= by
  intro V W
  constructor
  · exact (live_isOpen J s n σ).preimage (continuous_snd.sub continuous_fst)
  rintro ⟨q,p⟩ hp
  let f(z:Vantage):Vantage×Vantage:= (q,z+q)
  have hf: Continuous f:=continuous_const.prodMk (continuous_id.add continuous_const)
  have hu: MapsTo f {p | p∈U ∧ ReadsSix (M p)} W:=by
    rintro z ⟨x,t⟩; change (z+q)-q∈ U∧ ReadsSix (M ((z+q)-q)); rw [add_sub_cancel_right]; exact ⟨x,t⟩
  simpa only [f, sub_add_cancel] using hu.closure hf ((live_isDense J s n σ h) (a:=p-q) hp)
omit J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
