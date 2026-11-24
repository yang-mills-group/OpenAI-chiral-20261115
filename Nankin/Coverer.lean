import Nankin.Screen
import Taffeta.Stigma
import Rods.Fold
import YM.SU5.FiniteGaugeData.Tower.Baggage
import YM.SU5.FiniteGaugeData.Pannier.FeastDay
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option maxRecDepth 6500
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark
namespace Calico
open Py.Dyad Work.E08 AnalyticBridge.VerifiedReset StressFlux PlaqAxes
variable (K:Calibration)(o:Cover)(D:BudgetPoint)(q:ℝ)
open StressFlux
abbrev mint_ (X:LinksC):ℝ:=(∑ b:PlaqAxes, q*((CF.Compass.decor b):ℝ)/D.threshold^2 * ‖clover (G:=SU.group) X (nodeC o) b.val.1 b.val.2‖^2) / 2
abbrev cord (X:LinksC):ℝ:=if disc o D X then mint_ o D q X else 0
def lining:Family K:=scalar K (fun p=>((cord o D q p.1:ℝ):ℂ))
lemma our_torus(n:Side)(X:Pane n) : cord o D q (onC n X)=tariffB (wrap n o) D q X:=by
 unfold cord tariffB
 by_cases h:disc o D (onC n X)
 · have g:=(disc_cash o D X).mp h; rw [if_pos h,if_pos g]
   unfold mint_ Inkprice AnalyticBridge.VerifiedReset.petals clover StressFlux.stencil StressFlux.plate
   simp_rw [onC,travel_at,add_zero,node_of]
 rw [if_neg h,if_neg ((disc_cash o D X).not.mp h)]
lemma lining_at(m:Side):lining K o D q m=cameo (wrap (K.c m) o) D q:=by funext x; unfold cameo lining scalar; dsimp only; rw [our_torus]

lemma mint_cont: Continuous (mint_ o D q):=by unfold mint_ clover StressFlux.stencil StressFlux.plate; fun_prop
lemma disc_meas : MeasurableSet {X:LinksC|disc o D X}:=by
 have e:{X:LinksC|disc o D X}= ⋂ i: {p:Face ℤ//touchC p o},{X:LinksC|SU.group.chord (faceValue X i.val)<D.threshold}:= by ext; simp [disc]
 rw [e]; apply MeasurableSet.iInter; intro i; exact (isOpen_lt (SU.group.continuous_chord.comp (continuous_travel ..)) continuous_const).measurableSet
lemma coverEnv:Envelope (fun p:PairsC=>((cord o D q p.1:ℝ):ℂ)):=by
 obtain ⟨e,C,h⟩: RG.Envelope (mint_ o D q):=Env.compact (mint_cont ..)
 have t:Measurable (cord o D q):=e.ite (disc_meas o D) measurable_const
 refine ⟨Complex.continuous_ofReal.measurable.comp (t.comp measurable_fst),max C 0,fun x=>?_⟩
 rw [Complex.norm_real]; unfold cord; split; exact (h x.1).trans (le_max_left ..); exact norm_zero.le.trans (le_max_right C 0)

lemma bands_spec {p n}(u:p∈bands o n)(i:Axis): - (n:ℤ)≤ p i-nodeC o i∧p i-nodeC o i≤n:=by obtain ⟨c,h,rfl⟩:=mem_image.mp u; simp only [Pi.add_apply,add_sub_cancel_right]; exact ⟨box_test.mp h|>.1 _,box_test.mp h|>.2 _⟩
lemma inBands{p:Cover}{n:ℕ}(h:∀ i,- (n:ℤ) ≤ p i-nodeC o i ∧p i-nodeC o i ≤ n):p∈bands o n:= mem_image.mpr ⟨p-nodeC o,box_test.mpr ⟨fun i=>(h i).1,fun i=>(h i).2⟩,sub_add_cancel _ _⟩
lemma within_disc{i:Face ℤ}(h:touchC i o) : Tch i ⊆ bands o 22:=by
 intro p w; obtain ⟨y,a,b⟩:=not_disjoint_iff.mp (h: ¬Disjoint ..); apply inBands
 intro j; obtain ⟨l,g⟩:=bands_spec o a j; have H(w:Cover)(v:w∈Tch i):-(4:ℤ)≤w j-i.1 j∧w j-i.1 j≤4:=⟨box_test.mp (shiftF i w v)|>.1 j,box_test.mp (shiftF i w v)|>.2 j⟩; obtain ⟨t,r⟩:= H y b; obtain ⟨e,k⟩:=H p w; omega
lemma within_plate (a b:Step)(y:Cover)(p:y∈visits (nodeC o) (Lattice.oriented a b)): y∈ bands o 22:=by
 apply inBands; intro i
 have h(d:Step):-(1:ℤ)≤ d.vec (R:=ℤ) i∧d.vec (R:=ℤ) i≤1:=by rcases d with ⟨n,k|k⟩ <;> by_cases p:n=i <;> simp [Step.vec,step,Pi.single_apply,p]
 simp only [Lattice.oriented,visits,List.mem_cons,List.not_mem_nil,or_false] at p
 rcases p with e|e|e|e|e <;> subst y <;> have l:=h a <;>have r:=h b <;>have A:=h a.rev <;>have B:=h b.rev <;> simp only [Pi.add_apply,Nat.cast_ofNat] <;> omega
lemma accord: ∀ x y:LinksC, Lattice.Agrees (bands o 22) x y→cord o D q x=cord o D q y:=by
 intro x y h
 have v(i:Face ℤ)(p:touchC i o):faceValue x i=faceValue y i:=travel_local _ _ x y fun e a b=>h e (within_disc o p (List.mem_toFinset.mpr a)) (within_disc o p (List.mem_toFinset.mpr b))
 have u(a b:Step): StressFlux.plate (G:=SU.group) x (nodeC o) a b= StressFlux.plate (G:=SU.group) y (nodeC o) a b:=congrArg SU.group.curvature (travel_local _ _ x y fun i l r=>h i (within_plate o a b _ l) (within_plate o a b _ r))
 have e(i j:Axis): clover (G:=SU.group) x (nodeC o) i j=clover (G:=SU.group) y (nodeC o) i j:=by unfold clover StressFlux.stencil; simp_rw [u]
 have g:disc o D x↔disc o D y:= ⟨fun p i w=>(v i w) ▸ p i w,fun p i w=> (v i w).symm ▸ p i w⟩
 unfold cord mint_; rw [propext g]; simp_rw [e]
lemma lining_test: InTest K true (bands o 22) false (lining K o D q):=InTest.seed ⟨nofun,coverEnv ..,fun x y p _=> congrArg Complex.ofReal (accord o D q x.1 y.1 p)⟩
lemma lining_cov:CovCover K (lining K o D q):=by
 intro n g x; rw [lining_at]; change ((tariffB (wrap (K.c n) o) D q (Lattice.gauge g x.1):ℝ):ℂ) • (1: FC _) = _
 have p:tariffB (wrap (K.c n) o) D q (Lattice.gauge g x.1)=tariffB (wrap (K.c n) o) D q x.1:=by unfold tariffB Inkprice; simp_rw [pingB,petals_gauge]; simp
 unfold cameo; rw [p, twist_scalar,map_one]
#check twist_scalar
#print axioms lining_test
end Calico
end YM.CF.Buffered.Afterglow.Tower
end
