import YM.CF.BProof.Stint.Functional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
/-! Consistent argument spaces for integration in parameters. These aren't read variables;
a distinction in parameters can always charge 2 (max oscillation for sup bound), even if
close to each other. Borel and continuity in scaled parameter preserved. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {I D G Y :Type}[Fintype I][DecidableEq I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}
abbrev Time:=↥(Set.Icc (0:ℝ) 1)
def tap (x:ℝ): Time :=⟨max 0 (min x 1),le_max_left .., max_le zero_le_one (min_le_right ..)⟩
lemma tap_in {x:ℝ}(h:x∈Set.uIcc (0:ℝ) 1): (tap x).val=x:=by rw [Set.uIcc_of_le zero_le_one] at h; simp [tap,h.2,h.1]
@[fun_prop] lemma tap_c: Continuous tap:= Continuous.subtype_mk (continuous_const.max (continuous_id.min continuous_const)) _
@[simp] lemma tapSelf (i: Time): tap i.val=i:= Subtype.ext (tap_in (by rw [Set.uIcc_of_le zero_le_one]; exact i.property))

def Ella (b:Stage Y I D G): Stage Y I (D×Time) G where
 F:=b.F
 home:=b.home
 drive:=fun g (x,t)=>(b.drive g x,t)
 eval S x y := b.eval S x.1 y.1+(if x.2=y.2 then 0 else 2)
 pos:=fun S x y=> add_nonneg (b.pos ..) (by split<;> norm_num)
 includeV h x y:= add_le_add_left (b.includeV h x.1 y.1) _
def straw(s: Tag b): Tag (Ella b):=⟨s.run,s.keeps⟩
lemma strawBack(s: Tag b): straw s.reverseV=(straw s).reverseV:=rfl
lemma Ella_pay {C:ℝ}(h:Capacity b C): Capacity (Ella b) C:=⟨h.1,h.2,h.3⟩ -- projections tune
lemma jewel {s t:Tag b}{p:Pay}{A:Raw D I} (h:Earn p s t A): Earn p (straw s) (straw t) (fun x=> A x.1):=by
 apply h.restrict _ continuous_fst rfl rfl _ id (fun i x=>rfl) rfl rfl; intro S x y; apply le_add_of_nonneg_right (show 0≤ if x.2=y.2 then (0:ℝ) else 2 from by split<;>norm_num)
section
variable {U:Type}[NormedAddCommGroup U][NormedSpace ℝ U][CompleteSpace U]
abbrev tideD (f:D×Time→U)(x:D):= fun t:ℝ=>f (x,tap t)
def avg (f:D×Time→ U)(x:D) := ∫ t in (0:ℝ)..1,tideD f x t
lemma grain(f:D×Time→ U)(h:Continuous f)(x:D) : IntervalIntegrable (tideD f x) volume 0 1:=(h.comp (continuous_const.prodMk tap_c)).intervalIntegrable .. -- ambiguous
lemma continuous_avg(f:D×Time→ U)(h:Continuous f): Continuous (avg f):= intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f:=tideD f) (h.comp (continuous_fst.prodMk (tap_c.comp continuous_snd))) .. -- tune dots
lemma avg_n(f:D×Time→ U)(x:D){c:ℝ}(h:∀ t, ‖f (x,t)‖≤c): ‖avg f x‖≤c:=by refine (intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=1) (f:=tideD f x) (fun t _=>h (tap t))).trans_eq ?_; simp
lemma avg_use (f:D×Time→ U)(g:ℝ→U)(x:D)(h:∀ z:Time,g z.val=f (x,z)) : ∫ t in (0:ℝ)..1,g t= avg f x:=by apply intervalIntegral.integral_congr; intro z p; exact (congrArg g (tap_in p)).symm.trans (h _)
lemma interior_c (f:D×Time→ U)(h:Continuous f)(g:ℝ→ U)(x:D)(e:∀ z:Time,g z.val=f (x,z)): ContinuousOn g (Set.Icc (0:ℝ) 1):= continuousOn_iff_continuous_restrict.mpr (by rw [show Set.restrict _ g= _ from funext e]; exact h.comp (continuous_const.prodMk continuous_id)) -- tune
end
lemma averaged {s t:Tag b}{p:Pay} {A:D×Time→Op I}(h:Earn p (straw s) (straw t) A) : Earn p s t (avg A):=by
 obtain ⟨P,W,F,H,Z⟩:=h.holds; refine ⟨fun S=>avg (P S),W,fun S=>⟨?_,?_⟩, H, ?_⟩
 · intro i x; unfold avg
   let L:= (ContinuousLinearMap.mul ℝ (Op I)); let V:= L (s.run i).val; let Q:= L.flip (t.run i).val -- orientation
   change Q _= V _; rw [← Q.intervalIntegral_comp_comm (grain (P S) (F S).cont (b.drive i x)), ← V.intervalIntegral_comp_comm (grain (P S) (F S).cont x)]; apply intervalIntegral.integral_congr; intro z _; exact (F S).frame i (x,tap z)
 · intro i j; let L:= (⟨⟨fun A:Op I=>A i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩ : Op I →ₗ[ℝ] ℂ).toContinuousLinearMap; let X:D×Time→ℂ:= fun z=>P S z i j; let u:= (F S).expo i j; have he(x): avg X x=avg (P S) x i j:= L.intervalIntegral_comp_comm (grain (P S) (F S).cont x); dsimp only; refine ⟨u.positive,u.triggered,fun x=> he x ▸ avg_n X x (fun i=> u.bounded _), fun x y=>?_,((continuous_avg (P S) (F S).cont).matrix_elem ..)⟩
   rw [← he,← he]; unfold avg; rw [←intervalIntegral.integral_sub (grain X u.connected x) (grain X u.connected y)]; apply avg_n (fun p:D×Time=>X (x,p.2)- X (y,p.2)) x; intro k; have hu:=u.variation (x,k) (y,k); change ‖X (x,k)-X (y,k)‖ ≤ _ *(b.eval S x y+(if k=k then _ else _)) at hu; simpa only [ite_true,add_zero] using hu
 intro x; unfold avg tideD; simp_rw [Z]; rw [intervalIntegral.integral_finsetSum]; exact fun i _=>grain (P i) (F i).cont x
end YM.CF.BProof.Stint
