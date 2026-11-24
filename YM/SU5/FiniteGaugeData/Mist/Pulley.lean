import YM.SU5.FiniteGaugeData.Mist.Zinnia
/-!
# Continuous parts of a moving vacuum
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Mist
open Function Filter Metric Finset Lattice Hills
open scoped Topology BigOperators InnerProductSpace
variable {H:Hilbert}{T: Type}[NormedAddCommGroup T]
structure Willow (H:Hilbert)(T:Type)[NormedAddCommGroup T] where
 U : T→ H.Op
 init : U 0=1
 both (x y): U (x+y)=U x*U y
 keep (x:T)(w:H):‖U x w‖= ‖w‖
namespace Willow
variable (Q:Willow H T)(w x:H)(r:T)
lemma both_inner (x y:T)(z:H): Q.U x (Q.U y z) = Q.U (x+y) z:= (DFunLike.congr_fun (Q.both ..) z).symm
lemma keepD (w x:H): dist (Q.U r w) (Q.U r x)=dist w x:=by rw [dist_eq_norm,← map_sub,Q.keep,dist_eq_norm]
lemma remain (w x:H) : inner ℂ (Q.U r w) (Q.U r x)=inner ℂ w x := (⟨(Q.U r).toLinearMap,Q.keep r⟩:H→ₗᵢ[ℂ]H).inner_map_map w x
lemma repute : Q.U (-r)* Q.U r=1:=by rw [← Q.both,neg_add_cancel,Q.init]
lemma remit : (Q.U r).adjoint=Q.U (-r):=by
 ext1 x; apply ext_inner_left ℂ; intro z; rw [ContinuousLinearMap.adjoint_inner_right]; apply Eq.trans ?_ (Q.remain r z (Q.U (-r) x)); apply congrArg; exact (DFunLike.congr_fun (show Q.U r * Q.U (-r)=1 from by rw [←Q.both, add_neg_cancel,Q.init]) x).symm
lemma commute_map (r t:T): Commute (Q.U r) (Q.U t):=(Q.both r t).symm.trans ((congrArg Q.U (add_comm r t)).trans (Q.both ..))
-- continuity vector criterion, choose actual Euclid metric of cost.
def AllowsR (w:H):Prop:= Tendsto (fun k=> Q.U k w) (𝓝 0) (𝓝 w)
lemma admits (u:Q.AllowsR w): UniformContinuous (fun k=> Q.U k w):= by
 refine Metric.uniformContinuous_iff.mpr fun r p=> ?_; unfold AllowsR at u; have hu:= Metric.tendsto_nhds.mp u r p; obtain ⟨d,b,h⟩:= Metric.mem_nhds_iff.mp hu; refine ⟨d,b,fun i j z=>?_ ⟩
 have he: (i-j)∈ball 0 d:=by change dist _ _< _; rw [dist_zero_right,←dist_eq_norm]; exact z
 have ht:dist (Q.U (i-j) w) w<r:= h he; rw [←Q.keepD j] at ht; rwa [Q.both_inner, add_sub_cancel ..] at ht -- lemma tune
lemma grammar (w:H): Q.AllowsR w ↔ Continuous (fun k=> Q.U k w):=by
 refine ⟨fun p=>(Q.admits w p).continuous,fun p=>?_⟩; have hp:=p.tendsto 0; rwa [Q.init,show (1:H.Op) w=w from rfl] at hp
lemma allows_closed : IsClosed (Q.AllowsR:Set H):=by
 apply isClosed_of_closure_subset; intro x h; change Q.AllowsR x
 apply Metric.tendsto_nhds.mpr; intro r v; obtain ⟨y,t,e⟩:= Metric.mem_closure_iff.mp h (r/4) (by positivity)
 filter_upwards [Metric.tendsto_nhds.mp (show Tendsto (fun k=> Q.U k y) (𝓝 0) (𝓝 y) from t) (r/4) (by positivity)] with k ht; have hv:=dist_triangle (Q.U k x) y x; rw [dist_comm y x] at hv; have hh:=dist_triangle (Q.U k x) (Q.U k y) y; rw [Q.keepD] at hh; linarith
abbrev PaidR : Submodule ℂ H where
 carrier := Q.AllowsR
 zero_mem' := by change Q.AllowsR 0; simp [AllowsR]
 add_mem' {x y} hx hy:= by
   change Q.AllowsR _; simp_rw [AllowsR,map_add]; exact Tendsto.add hx hy -- tune
 smul_mem' z x p:= by change Q.AllowsR _; simp_rw [AllowsR,map_smul]; exact Tendsto.const_smul p _ -- tune
abbrev Standard : ClosedSubmodule ℂ H := ⟨Q.PaidR,Q.allows_closed⟩
local notation "S"=>Standard Q
lemma standardH : w∈ Q.Standard ↔ Q.AllowsR w:= Iff.rfl
lemma fair {L:H.Op} (p:∀ r:T, Commute L (Q.U r))(u:x∈ Q.Standard): L x∈ Q.Standard:= by
 change Q.AllowsR _; apply (Q.grammar _).2; have he:(fun k=> Q.U k (L x))=(fun k=> L (Q.U k x)):=funext fun k=>(DFunLike.congr_fun (p k).eq x).symm; rw [he]; exact L.continuous.comp ((Q.grammar ..).1 u)
lemma commute_pay {L:H.Op}(p:∀ x,Commute L (Q.U x)) : Commute L (planeP Q.Standard):=by
 have hh(x:T):Commute L.adjoint (Q.U x):=by
   have he:= congrArg star (p (-x)).eq; rw [star_mul,star_mul,ContinuousLinearMap.star_eq_adjoint, Q.remit,neg_neg,ContinuousLinearMap.star_eq_adjoint] at he -- order first adjoint
   exact he.symm
 ext1 x; -- Commute notation may ext not
 let P:=planeP (S); let y:=L (P x)
 have he:y∈ Q.Standard:= Q.fair _ p (through x); change y=planeP (S) (L x)
 letI : CompleteSpace Q.Standard.toSubmodule:= coreCmp Q.Standard
 letI : Q.Standard.toSubmodule.HasOrthogonalProjection:=Submodule.HasOrthogonalProjection.ofCompleteSpace (S).toSubmodule
 refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K:=Q.Standard.toSubmodule) (show y∈Q.Standard.toSubmodule from he) ?_).symm -- orientation check
 intro z t; rw [inner_sub_left]; unfold y; rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.adjoint_inner_right, planeP_inner, inlet (Q.fair z hh t),sub_self]
lemma hot_keep : Commute (planeP Q.Standard) (Q.U r) := (Q.commute_pay (fun x=> Q.commute_map r x)).symm
lemma bankC {U:Type} [NormedAddCommGroup U](L: Willow H U)(p:∀ x y, Commute (Q.U x) (L.U y)) : Commute (planeP Q.Standard) (planeP L.Standard) := L.commute_pay (fun x=> (Q.commute_pay (fun t=> (p t x).symm)).symm)
end Willow
end YM.CF.Buffered.Afterglow.Hierarchy.Mist
