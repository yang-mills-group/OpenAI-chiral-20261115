import YM.SU5.Reconstruction.Hygrometry.Mint
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 30000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Hygrometry
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods Flare Emu Onyx Dial
open Filter Topology
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open YM.CF.Buffered YM.CF.Window
open YM.Stationary (Gaia)
open Mir Reflect Buffered.Lifted Buffered.Afterglow.Tower.Tilted RG Pressure Analysis
open PriceCliff RP
open scoped Classical ComplexOrder
open Wilson Skye Scree Girt Peaks Paige Vault Vale Vale.Grace Pastry
open Py Py.Rate 
variable {N m B:Side}{L:Side}{j:ℕ}{h:Odd L.val}{Y:Pricing j L h (Thread j)}{δ:ℝ}
local notation "N₀"=> CSide m B
variable (A: Grasp Y B δ)(p:Pearl A) (y:Stamped j L h Y)(u:A.roundZ ≤ (CSide m B).val)(g:0<δ)(v:1 ≤ j)
variable (T:Loom (CSide m B)) {k:ℕ}{d:ℝ}(R:Roof (CSide m B) d δ k T)(P:BudgetPoint)(D:PathData group)(Z:Clip) (θ:P.threshold ≤ d)
variable (K:Cascade.Interest (CSide m B))
variable (G': Mark (CSide m B))
namespace MeterFunding
open Metric MeasureTheory
-- real gauge prescription; no estimation of radius from below intended.
lemma clearHere : ∀ᶠ x:Pane N in 𝓝 1, flags P.threshold x=∅:=by
 have hx:pingS P.threshold univ (1: Pane N):= Scree.ping_f P univ
 filter_upwards [(Scree.ping_o (X:=univ) (G:=SU.group) (S:=More N) (e:=P.threshold)).mem_nhds hx] with x e; exact Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=> Finset.disjoint_left.mp (show Disjoint _ _ from Scree.ping_le (show pingS P.threshold univ x from e)) (mem_univ i) hi)
include R p y u g v θ
-- Orientation invariant. Use at WHEN inspecting all real β. viable poses neighbourhood.
private lemma temperate: ContinuousAt (relV (m:=m) A K) (1:Pane N₀):= by
 let U:= {X:Pane N₀| Guard X δ}; have he:U∈ 𝓝 1:= (clearHere (N:=N₀) P).mono fun i h=> beauty_at T R P θ h
 let c(x:↥U):= relV A K x.val; have hc:Continuous c:= Girt.house_k p y g v K u;
 exact ((show ContinuousOn (relV (m:=m) A K) U from continuousOn_iff_continuous_restrict.mpr hc) 1 (atlas_guard g.le)).continuousAt he
private lemma kin (h: Pad j (CSide m B))(c:ContinuousAt (fun U:Pane N₀=> G' (U,U)) 1): ContinuousAt (fun x:Pane N₀=>SpinPrice (relV A K x) (G' (x,x))) 1:= by
 let f(X:Pane N₀):=relV A K X; have hv:ContinuousAt f 1:=temperate A p y u g v T R P θ K; let V0:Wave (Single N₀):= mateK _
 exact
  ((continuousAt_const.inner ((acts_cont.continuousAt.comp c).clm_apply hv)).div (continuousAt_const.inner hv) (SpinPrice_berry A K u g.le v h))
-- canonical. orientation frame.Authority needs covariance only for saturation. 
def Typical (X:Set (Pane N)) := 1∈ X ∧ IsOpen X ∧ ∀ (k:Seat N→SU.E) (x:Pane N), x∈X → Lattice.gauge k x∈ X
variable {C:Hom.Credit}(q:Hom.InterestX C (CSide m B) K)
include q
noncomputable def Fuelled (δ:ℝ)(p:ℂ) (X:Set (Pane N₀)): Prop:= Typical X ∧ ∀ U:Orbit N₀,U.1∈X → flags P.threshold U.1=∅ ∧ ∀ (β:ℝ),
   let Z0:= denZ (construct P D Z K β 0 0) A T
   inner ℂ (mateK N₀) (Z0 U)≠0 ∧ ‖eddy T G' Z0 U-p‖<δ
lemma pier_eligible (h:Pad j (CSide m B))(s:ℂ)(l:ℝ)(e:‖SpinPrice (changeM (m:=m) A 1 K.M) (G' (1,1))-s‖<l)(o:ContinuousAt (fun U:Pane N₀=> G' (U,U)) 1)(t:Buffered.covariant G'):
    ∃ X,Fuelled (m:=m) A T P D Z K G' l s X ∧ 0<(Wilson.prior group (More (CSide m B))) X:= by
 let ξ(V:Pane N₀):= inner ℂ (mateK _) (relV A K V)
 have hx : ContinuousAt ξ 1:= continuousAt_const.inner (temperate A p y u g v T R P θ K)
 let F(V: Pane N₀):= SpinPrice (relV A K V) (G' (V,V)); have hf:ContinuousAt F 1:= kin A p y u g v T R P θ K G' h o
 have hw :∀ᶠ V:Pane N₀ in 𝓝 1,flags P.threshold V=∅ ∧ ξ V≠0 ∧ ‖F V-s‖<l:= (clearHere P).and ((hx.eventually (eventually_ne_nhds (SpinPrice_berry A K u g.le v h))).and (((hf.sub_const s).norm).eventually (gt_mem_nhds (show ‖F 1-s‖<l by unfold F; rwa [freeze_anchor])))) -- tune relative orientations
 obtain ⟨d,dX,k⟩:= Metric.eventually_nhds_iff_ball.mp hw
 let Ω:=ball (1:Pane N₀) d; let X:= ⋃ f:Seat N₀→ SU.E,Lattice.gauge f ⁻¹' Ω
 have hc(k:Seat N₀→ SU.E):Continuous (Lattice.gauge k):= continuous_pi fun i=>by unfold Lattice.gauge; fun_prop
 have hp:1 ∈ X:= Set.mem_iUnion.mpr ⟨(1:Seat N₀→SU.E),by change Lattice.gauge (1:Seat N₀→SU.E) (1:Pane N₀)∈Ω; rw [windy_u]; exact mem_ball_self dX⟩
 have H:Typical X:=by
    refine ⟨hp,isOpen_iUnion (fun i=>isOpen_ball.preimage (hc i)),?_⟩; intro f x p; obtain ⟨i,h⟩:=Set.mem_iUnion.mp p; apply Set.mem_iUnion.mpr; refine ⟨i*f⁻¹,?_⟩; change Lattice.gauge (i*f⁻¹) (Lattice.gauge f x)∈Ω; rw [windy,inv_mul_cancel_right]; exact h -- group name tune
 refine ⟨X,⟨H,?_⟩,?_⟩
 · intro U u'; obtain ⟨f,t'⟩:=Set.mem_iUnion.mp u'
   obtain ⟨h,hv,V⟩:= k (Lattice.gauge f U.1) t'; -- k : Ball conditions maybe implicit ∀⦃v⦄
   have he: flags P.threshold U.1=∅ := (gauge_flags ..).symm.trans (show flags P.threshold (Lattice.gauge f U.1)=∅ from h)
   have hp:= beauty_at T R P θ he; refine ⟨he,fun β=> ⟨(pureBeam A u T R P D Z θ K he β).2 ?_,?_⟩⟩
   · rw [←beamed A p y u g v K q hp f]; exact hv -- positive
   rw [orient A u T R P D Z θ K G' he,←spinsM A p y u g v K G' q hp f t]; exact V
 letI : (prior group (More N₀)).IsOpenPosMeasure:=by unfold prior; infer_instance
 exact H.2.1.measure_pos _ (Set.nonempty_of_mem hp)
end MeterFunding
end YM.CF.Hygrometry
