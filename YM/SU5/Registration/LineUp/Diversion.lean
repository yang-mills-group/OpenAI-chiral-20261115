import YM.SU5.Registration.LineUp.Forms
import Mathlib.Data.Fin.Tuple.Sort
/-!
 # from generic (all-axis) comparison at M10 axis3 to Eu field on conf
 Includes symmetry, also across rotations changing strict time order.
 compare in M8-10 prices; see `LineUp.SharpRaster` for estimate target.
 adapts Utopia Seld.FiniteGaugeData.Poin (other SO group interface).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed
open Boundary Mink Analysis Function Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
open Courts

abbrev Frames (n:ℕ) := Ortho × Equiv.Perm (Fin n)
-- action for points & labels, permutation Right!
def reFrame (U:Frames n) (q:Points n) := Points.rearrange U.2 (Points.move U.1 q)
def reSup (U:Frames n) (R:Courts V) (v:Fin n→V) := (R.eu U.1) ∘ v ∘ U.2
def reBond (U J:Frames n):Frames n:= (U.1 * J.1, U.2.trans J.2)
abbrev origins (n:ℕ):Frames n:= (1,1)
abbrev fairFrame (U:Frames n):= Lorentz.properTurn U.1
lemma fair_bond {U J:Frames n} (p: fairFrame U) (q:fairFrame J): fairFrame (reBond U J):= proper_mul p q
lemma frame_in {x:Points n}(U:Frames n)(hx:x∈conf n) : reFrame U x∈ conf n:= Points.rearrange_in _ (Points.move_in _ hx)
lemma frame_first (x:Points n) : reFrame (origins n) x=x:=PiLp.ext fun i=> by simp [reFrame]
lemma frame_comp (U J:Frames n) (x:Points n): reFrame U (reFrame J x)=reFrame (reBond U J) x:=PiLp.ext fun i=> by simp [reBond,reFrame,Ortho.move_mul]
lemma frame_inv (U:Frames n)(x:Points n): reFrame U⁻¹ (reFrame U x)=x:=PiLp.ext fun i=> by simp [reFrame]
lemma frame_inv2 (U:Frames n)(x:Points n): reFrame U (reFrame U⁻¹ x)=x:=by simpa using frame_inv U⁻¹ x
lemma sup_first (R:Courts V)(v:Fin n→V): reSup (origins n) R v=v:= by ext i; exact R.eu1 _
lemma sup_comp {U J:Frames n} (p: fairFrame U)(q: fairFrame J) (R:Courts V)(v:Fin n→V): reSup U R (reSup J R v)=reSup (reBond U J) R v:= funext (fun i=>(R.euMul _ _ p q _).symm)
lemma sup_inv {U:Frames n}(p:fairFrame U)(R:Courts V)(v:Fin n→V):reSup U⁻¹ R (reSup U R v)=v:=by ext i; simp [reSup,R.eu_back _ p]
lemma frame_generic (r:Equiv.Perm (Fin n)) (x:Points n)(h:x∈generic n): Points.rearrange r x∈generic n:=fun a=> (h a).comp r.injective

def podium (U:Frames n): Points n ≃ₗᵢ[ℝ] Points n where
 toFun:= reFrame U
 invFun:= reFrame U⁻¹
 left_inv:=frame_inv U
 right_inv:=frame_inv2 U
 map_add' v w:= PiLp.ext fun _=> (U.1.motion).map_add _ _
 map_smul' x v:= PiLp.ext fun _=> (U.1.motion).map_smul _ _
 norm_map' x := by
  change ‖reFrame U x‖ = ‖x‖
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]; simp_rw [reFrame, Points.rearrange_at, Points.move_coord, Ortho.move_norm]; exact Equiv.sum_comp U.2 (fun i=> ‖x i‖^2)
/-- Orders are strictly along time slot 3 (timeAxis). -/
def lineK (q:Points n): Heights n:=YM.time ∘ q.ofLp
@[simp] lemma line_at (q:Points n)(i:Fin n): lineK q i=YM.time (q i):=rfl
lemma line_cont : Continuous (lineK (n:=n)):=by unfold lineK; simp_rw [Function.comp_def]; fun_prop
@[simp] lemma trace_place' (x:SpacePoints n)(y:Heights n) : Boundary.trace (place x y) = x:= by ext1 i; simp [Boundary.trace,place]
@[simp] lemma line_place' (x:SpacePoints n)(y:Heights n) : lineK (place x y)=y:=by ext1 i; simp [place]
lemma place_line (q:Points n): place (Boundary.trace q) (lineK q)=q:=PiLp.ext fun i=> position_eta _
def Wheeled (n:ℕ):Set (Points n):= lineK ⁻¹' east n
lemma wheel_at {q:Points n} (p:q∈Wheeled n) : q∈conf n:= (place_line q) ▸ Boundary.clear (mem_preimage.mp p) (Boundary.trace q) -- dep?
lemma wheel_open (n:ℕ) : IsOpen (Wheeled n) := (open_east n).preimage line_cont
private lemma separateTwo (x y:E4)(p:YM.time x=YM.time y) (q:x≠y) : ∃ Ω:Ortho.Skew, ∀ᶠ t:ℝ in 𝓝[>] 0,
  YM.time (Ortho.move (Ortho.oneParameter Ω t) x) ≠ YM.time (Ortho.move (Ortho.oneParameter Ω t) y) :=by
 suffices h:∃ z: SpaceAxis,x z.castSucc ≠ y z.castSucc by
    obtain ⟨z,h⟩:=h; let k:=Ortho.plane timeAxis z.castSucc; have he:timeAxis≠z.castSucc:= (Fin.castSucc_ne_last z).symm; refine ⟨k,?_⟩; filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds Real.pi_pos)] with t H w; unfold YM.time; rw [(Work.A13.plane_givens he x t).1,(Work.A13.plane_givens he y t).1, show x timeAxis=y timeAxis from p]; intro c; exact h (mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi H w).ne' (add_left_cancel c))
 by_contra! h; exact q (ext_by (PiLp.ext h) p)
private def Apart (q:Points n)(U:Ortho)(j: Fin n × Fin n):= j.1≠ j.2→ lineK (Points.move U q) j.1≠lineK (Points.move U q) j.2
private lemma appoint (q:Points n)(p:q∈conf n)(L:Finset (Fin n × Fin n)): ∃ U:Ortho, Lorentz.properTurn U ∧ ∀ j∈L,Apart q U j:=by
 induction L using Finset.induction_on with
 | empty=> exact ⟨1,proper_one,by simp⟩
 | insert i T e ih=>
    obtain ⟨U,hs,h⟩:=ih; by_cases z: Apart q U i; · exact ⟨U,hs,fun j v=>(Finset.mem_insert.mp v).elim (fun p=>p ▸ z) (h j)⟩
    unfold Apart at z; push Not at z; let X:= Points.move U q; obtain ⟨Ω,m⟩:=separateTwo (X i.1) (X i.2) z.2 (fun v=> z.1 (Points.move_in U p v))
    let Q(t):=Ortho.oneParameter Ω t*U
    have hur (t:ℝ)(j:Fin n) : lineK (Points.move (Q t) q) j=YM.time (Ortho.move (Ortho.oneParameter Ω t) (X j)):=by simp [Q,X,Ortho.move_mul]
    have ht(j:Fin n): Continuous (fun t=> lineK (Points.move (Q t) q) j):=by
       simp_rw [hur]; exact continuous_iff_continuousAt.mpr fun x=> (Work.A13.hasDerivAt_coord Ω _ timeAxis x).continuousAt
    have hm: ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ), ∀ j∈T,Apart q (Q t) j:= by
       refine (eventually_all_finset ..).mpr (fun j w=>?_)
       by_cases p:j.1=j.2; · exact Eventually.of_forall fun _ w=> False.elim (w p)
       have hx: Q 0=U:= by simp [Q,oneParameter_zero]
       refine Eventually.mono (f:=𝓝[>] 0) (p:=fun t=> lineK (Points.move (Q t) q) j.1 ≠ lineK (Points.move (Q t) q) j.2) (nhdsWithin_le_nhds (isOpen_ne_fun (ht j.1) (ht j.2) |>.mem_nhds (?_))) (fun t r _=>r); change lineK (Points.move (Q 0) q) j.1 ≠ lineK (Points.move (Q 0) q) j.2; rw [hx]; exact h _ w p
    obtain ⟨t,hv,k⟩:= (hm.and m).exists; refine ⟨Q t, proper_mul (proper_param Ω _) hs, fun j w=>(Finset.mem_insert.mp w).elim (fun p=>p ▸ show Apart q (Q t) i from fun _=>by rw [hur,hur]; exact k) (hv j)⟩
theorem origin_exists {q:Points n}(p:q∈conf n): ∃ U:Frames n, fairFrame U ∧ reFrame U q∈Wheeled n:=by
 obtain ⟨K,h,t⟩:=appoint q p Finset.univ; let y:=lineK (Points.move K q); have hc:Injective y:= fun i j c=>by_contra fun p=> t (i,j) (Finset.mem_univ _) p c
 let r:= Tuple.sort y; exact ⟨(K,r),h,(Tuple.monotone_sort y).strictMono_of_injective (hc.comp r.injective)⟩
def InkWaves.entrance (F:InkWaves V)(x:Points n):MultilinearMap ℂ (fun _ : Fin n=> V) ℂ := F.F n (fun i=>(lineK x i:ℂ)*Complex.I) (Boundary.trace x)
lemma entrance_cont (F: InkWaves V)(hf:F.Region)(v:Fin n→V) : ContinuousOn (fun x=> F.entrance x v) (Wheeled n):=by
 let A : Points n→ Times n:= fun x=> fun i=>(lineK x i:ℂ)* Complex.I; have h:Continuous A:=by simp_rw[A,line_at]; fun_prop
 exact (hf.together n v).comp (Continuous.prodMk h (show Continuous (Boundary.trace (n:=n)) by unfold Boundary.trace; fun_prop)).continuousOn fun x hx=> ⟨fun i j hij=>by simpa [A] using (mem_preimage.mp hx hij),mem_univ _⟩ -- defeq?
/-- Hypothesis at *generic* inputs (strict order) only. Via BOTH proper carries incl label rule and any reordering
    from wheel to wheel. -/
def Courts.Carriage (R:Courts V)(F:InkWaves V): Prop :=∀ (n:ℕ)(U:Frames n), fairFrame U→ ∀ (x:Points n), x∈generic n → x∈Wheeled n → reFrame U x∈generic n → reFrame U x∈Wheeled n →
 ∀ (v:Fin n→V), F.entrance (reFrame U x) (reSup U R v)=F.entrance x v
lemma both_generic (U:Frames n): ∀ᵐ x:Points n, x∈generic n ∧ reFrame U x∈generic n:= (Extraction.almostGeneric n).and ((podium U).measurePreserving.quasiMeasurePreserving.ae (Extraction.almostGeneric n))
variable {F: InkWaves V}{R:Courts V}(h:R.Carriage F)(p:F.Region)
include h p
lemma wheeled_eq (x:Points n)(hx:x∈Wheeled n)(U:Frames n)(hu:fairFrame U)(e:reFrame U x ∈ Wheeled n)(v:Fin n→V) : F.entrance (reFrame U x) (reSup U R v)=F.entrance x v:=by
 let L:= Wheeled n ∩ reFrame U ⁻¹' Wheeled n; have hc:IsOpen L:= (wheel_open n).inter ((wheel_open n).preimage (podium U).continuous)
 let f(x:Points n):= F.entrance (reFrame U x) (reSup U R v); let g(x:Points n):=F.entrance x v; have heq:EqOn f g L:= by
    refine Measure.eqOn_open_of_ae_eq (μ:=volume) ?_ hc ((entrance_cont F p (reSup U R v)).comp (podium U).continuous.continuousOn fun i hi=>hi.2) ((entrance_cont F p v).mono inter_subset_left)
    exact (ae_restrict_iff' hc.measurableSet).mpr ((both_generic U).mono (fun i hi hv=> h n U hu i hi.1 hv.1 hi.2 hv.2 v))
 exact heq ⟨hx,e⟩
lemma comparable (x:Points n)(U J:Frames n)(f:fairFrame U)(g:fairFrame J)(pU:reFrame U x∈Wheeled n)(pJ:reFrame J x∈Wheeled n)(v:Fin n→V) :
 F.entrance (reFrame U x) (reSup U R v)=F.entrance (reFrame J x) (reSup J R v):=by
 let K:=reBond U J⁻¹; let pK:= proper_inv g; have t: reFrame K (reFrame J x)=reFrame U x:=by rw [show K=reBond U J⁻¹ from rfl,← frame_comp, frame_inv]
 have u: reSup K R (reSup J R v)=reSup U R v:=by rw [show K=reBond U J⁻¹ from rfl,← sup_comp f (show fairFrame J⁻¹ from pK),sup_inv g]
 rw [← t,← u]; exact wheeled_eq h p (reFrame J x) pJ K (fair_bond f (show fairFrame J⁻¹ from pK)) (t.symm ▸ pU) (reSup J R v)
omit h p
abbrev EuLeaflet (V:Type*) [AddCommGroup V] [Module ℂ V] := ∀ n:ℕ,Points n→ MultilinearMap ℂ (fun _:Fin n=>V) ℂ
def framely (Q:InkWaves V)(R:Courts V)(U:Frames n)(x:Points n) : MultilinearMap ℂ (fun _:Fin n=>V) ℂ:=
 (((Q.entrance (reFrame U x)).compLinearMap fun _=> R.eu U.1).domDomCongr U.2)
lemma framely_at (U:Frames n)(x:Points n)(v:Fin n→V) : framely F R U x v = F.entrance (reFrame U x) (reSup U R v):=rfl
noncomputable def helio (R:Courts V)(F:InkWaves V): EuLeaflet V:= by
 classical
 exact fun n x=> if h:x∈conf n then framely F R (origin_exists h).choose x else 0
include h p
lemma helio_price (x:Points n)(U:Frames n)(hx:x∈conf n)(f:fairFrame U)(b:reFrame U x∈ Wheeled n)(v:Fin n→V): helio R F n x v=F.entrance (reFrame U x) (reSup U R v):=by
 unfold helio; rw [dif_pos hx]; exact comparable h p x _ U (origin_exists hx).choose_spec.1 f (origin_exists hx).choose_spec.2 b v
lemma helio_local (x:Points n)(hx:x∈Wheeled n)(v:Fin n→V): helio R F n x v=F.entrance x v:=by
 rw [helio_price h p x (origins n) (wheel_at hx) proper_one (by rw [frame_first]; exact hx), frame_first,sup_first]
lemma helio_cont (v:Fin n→V): ContinuousOn (fun x=> helio R F n x v) (conf n):=by
 intro x hx; obtain ⟨U,f,u⟩:=origin_exists hx
 have t:= (podium U).continuous.continuousAt (x:=x)
 refine ((( (entrance_cont F p (reSup U R v) _ u).continuousAt ((wheel_open n).mem_nhds u)).comp t).congr_of_eventuallyEq ?_).continuousWithinAt
 filter_upwards [(conf_open n).mem_nhds hx, t.tendsto.eventually ((wheel_open n).mem_nhds u)] with y hk hy
 exact helio_price h p y U hk f hy v
lemma helio_carries (U:Frames n)(hx:fairFrame U)(x:Points n)(v:Fin n→V) : helio R F n (reFrame U x) (reSup U R v)=helio R F n x v:=by
 by_cases Hx:x∈conf n
 · have hk:=frame_in U Hx; obtain ⟨J,f,u⟩:=origin_exists hk; rw [helio_price h p _ J hk f u, sup_comp f hx,frame_comp] -- details
   rw [frame_comp] at u; exact (helio_price h p _ _ Hx (fair_bond f hx) u v).symm
 have hv:reFrame U x∉conf n:= fun p=> Hx ((frame_inv U x) ▸ frame_in U⁻¹ p); rw [helio,dif_neg hv]; simp [helio,Hx]
end YM.SatinWFixed
open YM.SatinWFixed
#print axioms helio_price
#print axioms helio_carries
#print axioms helio_cont
#print axioms helio_local
