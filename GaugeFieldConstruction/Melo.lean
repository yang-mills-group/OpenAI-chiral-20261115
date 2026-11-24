import GaugeFieldConstruction.Gander
import YM.Planned.PRIMARY_INTEGRAL_295.RollFilm
import YM.Planned.PRIMARY_INTEGRAL_295.Throat
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 50000
set_option quotPrecheck false
noncomputable section
namespace YM.FlightFlux
open Function Filter Metric Lattice Wilson RG OrderedFinpartition Gauge Laurent Bloch Precision Tree Next.Free HarmP Pressure
open Planned.PrimaryIntegral295 Carrier Place
open AnalyticBridge.VerifiedReset
open scoped ContDiff Topology InnerProductSpace BigOperators Classical Matrix Matrix.Norms.Frobenius
variable {c n f:Side}{G:Gauge}{S:StepData c f}{T: Tube G S}{a k v z:ℝ}
open CF.Skye CF.Scree CF.TableF CF.TableF.Axon
open MultiNext.SignedSource
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{m:ℕ}
private lemma papers_to {V:E4→E}(p: V∈ Powers.space E4 E m): V∈rangeLt E (m+1):=by
 apply Powers.next (p:=fun i=>i∈rangeLt E (m+1)) _ (Submodule.zero_mem _) (fun _ _=>Submodule.add_mem _) _ p -- tune
 · rintro f ⟨i,u,h⟩; exact exact_le_band (Nat.lt_succ_of_le u) (can_write.mpr ⟨_,Powers.tensor_form h⟩)
 · intro a x p; exact Submodule.smul_mem _ a p
private lemma papers_from {V:E4→E}(p: V ∈ rangeLt E (m+1)): V∈Powers.space E4 E m:=by
 obtain ⟨T,w,rfl⟩:= range_decompose p; exact Submodule.sum_mem _ fun j _=> Powers.residence (k:=j.val) ⟨exact_smooth (w j) _, fun t x=> exact_scale (w j) x t⟩ (by omega)
lemma shift_degrees (V:Cover→E)(x:Cover)(p:Paper (m+1) V): Paper m (fun y=> V (y+x)-V y):=by
 intro z h
 let W:= loom z V
 have hA: ∀ i:Axis, advance i W=0:=fun i=> p (i::z) (by simp [h]); have he(W:Cover→ E)(z:List Axis)(x:Cover):loom z (fun i=> W (i+x))= fun i=> loom z W (i+x):=by induction z with|nil=>rfl|cons a z ih=>rw [loom_cons,ih,advance_shift,show (fun i=>loom (a::z) W (i+x))= _ from (show _ = fun i=>advance a (loom z W) (i+x) from rfl)]
 rw [show (fun y=> V (y+x)-V y)= (fun y=> V (y+x))+(-1:ℝ) • V from (by funext y; simp [sub_eq_add_neg]), loom_add,loom_smul,he]; funext i; change W (i+x)+(-1:ℝ) • W i=0; rw [tear W hA (i+x), tear W hA i]; simp
variable [FiniteDimensional ℝ E]
-- uniform leading power locked inspected convention
abbrev risen (A : Lines n) (U:Wheel Axis E) (x:Cover):Wheel Axis E:=fun i j=> applyLine A (Function.swap U) (j+x) i
lemma lead_degree (p:0<k)(Q:Flight 4 4)(Y:Wheel Axis E)(x:Cover)(m:ℕ)(e:0 < m)(g:m ≤ 2)(v:∀ i,Paper (m+1) (Y i)) (A:Lines n)(hv:Q.L=n)(he:HEq (linesOf Q k) A):∀ i,Paper m ((risen A Y x-unitStep n^(m+1) • Y) i):=by
 subst n; rw [← eq_of_heq he]; let W:=linesOf Q k
 choose B h hh using fun i=> panels m g (Y i) (v i)
 let B':= fun x:E4=>fun i=> B i x; have hp: B'∈ rangeLt (Axis→E) (m+1):= vector_band B fun i=> papers_to (h i)
 obtain ⟨F,f,t,H⟩:= accepts_V k p Q le_rfl (show m+1 ≤4 by omega) B' hp
 let z:=unitStep Q.L^(m+1); let T:=F-z • B'; have hv: T∈rangeLt (Axis→E) (m-1+1):=by rw [show m-1+1=m by omega]; exact t
 intro i
 have ht(i): Paper m (fun y:Cover=> verdict F y i-z • Y i y):=by
    let S(x:E4):= T x i
    have hr: Paper (m-1+1) (S ∘ Pattern.xyz):= toE4 (m-1) (by omega) S (papers_from (linear_band (ContinuousLinearMap.proj i) _ hv))
    rw [show m-1+1=m by omega] at hr; rw [←hh]; exact hr
 have hu(i):Paper (m+1) (fun y:Cover=> verdict F y i):= toE4 m g (fun x=> F x i) (papers_from (linear_band (ContinuousLinearMap.proj i) _ f)) -- tune
 have hξ: risen W Y x i = fun y=> verdict F (y+x) i:=by
    unfold risen; rw [show Function.swap Y=verdict B' from (by funext x i; exact (congrFun (hh i) x).symm), H]
 rw [Pi.sub_apply,hξ]; rw [show ((fun y=> verdict F (y+x) i)- (unitStep Q.L ^ (m+1) • Y) i)=(fun y=>verdict F (y+x) i-verdict F y i)+(fun y=>verdict F y i-z • Y i y) from (by funext y; change verdict F (y+x) i-z • Y i y= _+_; rw [sub_add_sub_cancel])]
 exact paper_add (shift_degrees _ x (hu i)) (ht i)
omit [FiniteDimensional ℝ E]
variable [CompleteSpace E]
lemma lip_equ {V:Window E}{U:Window E}{t:ℝ}{I:Lines n}{r:ℕ}(x:Cover)(p:0<a)(e:0≤t)(he:I.strip a t)(ht:Carries V m v)(hs:Carries U m z)(h:∀ j,lateral j≤r→ V j=U j):∀ i,‖applyLine I V x i-applyLine I U x i‖ ≤ (v+z)*(Real.exp (-(a/2)*r)*( 4*t*liftCost m x *Real.exp (a/2 * size x)*widthCost (a/2) m)):=by -- size
 intro i; unfold applyLine; rw [← Finset.sum_sub_distrib]; let Y:= cellar n x; apply (norm_sum_le ..).trans; let T:=liftCost m; let f(i':Cover):= (v+z)*(t*(Real.exp (-(a/2)*r)*T i'*Real.exp (a/2 * size i')*widthCost (a/2) m)); apply (Finset.sum_le_sum (g:=fun i=>f Y) (fun j _=>Throat.spared p e (he (wrap n x,Exterior.coord i) (Exterior.coord j)) m r ht hs h Y j)).trans
 have hx:size Y ≤ size x:= Work.F08.carry_size (0:Site n) _
 have he:=ht.1; have hg:= hs.1; have hb:0 ≤ widthCost (a/2) m:= zero_le_one.trans (widthCost_ge (by linarith) _); have hu: f Y ≤ f x := by
    unfold f; have hy:0 ≤ a/2:= half_pos p|>.le; have hT:0 ≤ T Y:= liftCost_pos ..; have ht:0≤ T x:= liftCost_pos ..; gcongr; exact liftCost_cellar n m x
 simp only [Finset.sum_const,nsmul_eq_mul,Fintype.card_fin,Axis,Finset.card_univ]; norm_cast -- tune
 apply le_trans (mul_le_mul_of_nonneg_left hu (show 0≤(↑4:ℝ) by norm_num)); unfold f T; linarith -- tune
end YM.FlightFlux
end
