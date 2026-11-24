import GaugeFieldConstruction.StencilCarton
import GaugeFieldConstruction.StencilLoyal
/-!
# Relative alignment theorem at reconstructed hierarchy
-/
set_option autoImplicit false
noncomputable section
namespace YM.NSF.Boundary
open MeasureTheory Filter Function Set Complex 
open YM.Boundary (Joint)
open scoped Topology BigOperators NNReal ENNReal ContDiff InnerProductSpace
open YM.SatinWFixed InkPort Carton LD
variable {G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}{B:Small S C}
variable {K:Hilbert}{D:YM.OS.Semigroup K timeAxis}
variable {A:Carton D S.Union}
local notation "v₀"=> A.omega
variable {n:ℕ}{U: K→ₗᵢ[ℂ] C.H} (u:PreservesSmall D A.bar A.omega LinearMap.id U B)
variable {W:Surface S}{R: S.Rotation}{x:S.RealSpin}{Φ:Spins S}{F:Waves S}{J:StarOp S}
include u
open NSF.Work.C03 NSF.Boundary.Small NSF.OS.Semigroup
open SatinRegistration (radial)
private lemma jointPay_st {z:Times n}(x: SpacePoints n)(v:Fin n→ S.Union)(p:ℝ≥0) (hp:lit z p)
    (Z:ℂ)(X: Space3)(ht:∀ i, ((p+p:ℝ≥0):ℝ)< (z i).im-Z.im) :
  U (A.trainZ p n z x v Z X)=B.trainB p n z x v Z X:=by
 have he : A.trainZ p n z x v Z X=inkTrain D A.bar A.omega p n z x v Z X:=by
    -- not using h for this comparison. spell out
    clear hp ht
    induction n generalizing Z X with
    | zero=>rfl
    | succ n ih=> rw [Carton.trainZ,inkTrain,ih]; rfl
 rw [he]; exact u.joint _ _ _ hp _ _ ht
lemma shotFundsSt (p:ℝ≥0)(v:Fin n→S.Union)(y: Heights n)(h: ample p y)(x:Points n): B.shot p n v y x=U (A.inkShot_st p n v y x):=by
 cases n with
 | zero=> exact u.money.symm
 | succ n=>
    let z:= Boundary.shift x y; let b:= Boundary.trace x; let a:= Small.interval (z 0) p; let l:= Small.bufferF (b 0); let α:= Fin.tail z; let W:= A.trainZ p n α (Fin.tail b) (Fin.tail v) (z 0) (b 0)
    have he: lit z p:= by simpa [lit,z,Boundary.shift] using h.1
    have ha : U W=B.trainB p n α (Fin.tail b) _ _ _:= jointPay_st u _ (Fin.tail v) _ (tail_lit he) _ _ (tail_ready he)
    have ht: a∈NSF.OS.Semigroup.inside:= (Small.down ..).mpr (by simp only [z,Boundary.shift,Complex.add_im,Complex.ofReal_im,Complex.mul_I_im,Complex.ofReal_re,zero_add]; linarith [h.2 (0:Fin (n+1)), p.coe_nonneg])
    let L(x:K):= A.bar p (v 0) x
    change C.flow.F a (C.flow.U l (B.bar p (v 0) _))= U (D.F a (D.U l (L W)))
    rw [←ha]; exact ((DFunLike.congr_fun (compareHeat D C.flow _ u.heat ht) (D.U l (L W))).trans (congrArg (C.flow.F a) ((DFunLike.congr_fun (u.space (b 0)) (L W)).trans (congrArg (C.flow.U l) (DFunLike.congr_fun (u.links _ h.1.1 (v 0)) W))))).symm
lemma priceCupSt(b:Sentence S) (t:ℝ)(h:0<t): U (A.heatKick_st b t) = B.heatCup b t:= by
 unfold heatKick_st heatCup; rw [←U.integral_comp_comm]; apply integral_congr_ae; filter_upwards with y; rw [U.map_smul]; exact congrArg (fun v:C.H=> Joint.materialize b.length (fun i=>(b.get i).2) y • v) ((shotFundsSt u (logD t) _ (profile t b.length) (suitable h) y).symm)
variable (P: PredictionL W F Φ J B R x) (s:WordLiftSt P.system (H:=K) (radial D) A.row A.activate)
lemma loyaltySt (b:Sentence S): P.mapSpace (P.system.operators.vector b) = U (s.rays (P.system.operators.vector b)):=by
 rw [P.assign,s.onWord]; let Y:= till; have ht(b:Sentence S) := (B.bowls P.link).chase b;
 exact tendsto_nhds_unique_of_eventuallyEq (ht b) ((U.continuous.tendsto _).comp (A.atCorner_st _)) (Eventually.mono (show ∀ᶠ x in till, 0<x from self_mem_nhdsWithin) (fun t q=>(priceCupSt u b t q).symm))
lemma identificationInk_st : P.mapSpace = U.toContinuousLinearMap.comp s.rays.toContinuousLinearMap:=by
 apply ContinuousLinearMap.ext_on (R₁:=ℂ) (s:=Set.range P.system.operators.vector)
 · rw [←P.course.total.cyclic]; exact P.course.total.everywhere
 rintro x ⟨L,rfl⟩; exact loyaltySt u P s L
#print axioms identificationInk_st
end YM.NSF.Boundary
end
