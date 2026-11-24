import YM.Hilbert.Kolmogorov
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!
# Sequential calculus tools for monotone closed Hilbert compression and ground selection
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Hills
open Function Filter NormedSpace Finset Topology
open scoped Topology BigOperators InnerProductSpace ComplexOrder
variable {F H Y: Hilbert}{U X:ClosedSubmodule ℂ H}
-- use TWO types CoreH and norm.Clarity
instance coreCmp (U:ClosedSubmodule ℂ H) : CompleteSpace U.toSubmodule := by
 apply IsComplete.completeSpace_coe; exact U.isClosed.isComplete
-- declared must be explicit for some tc. use local.Tune.
def CoreH (U:ClosedSubmodule ℂ H): Hilbert := { space:= U.toSubmodule }
local notation "A"=> CoreH U
abbrev dip (U:ClosedSubmodule ℂ H) : H →L[ℂ] CoreH U:= U.toSubmodule.orthogonalProjectionOnto
abbrev cpo (U:ClosedSubmodule ℂ H) : CoreH U→L[ℂ] H:= U.toSubmodule.subtypeL
abbrev planeP (U:ClosedSubmodule ℂ H): H.Op:=U.toSubmodule.starProjection
local notation "D"=> dip U
local notation "I"=> cpo U
local notation "P"=> planeP U
lemma liftL : (cpo U).comp (dip U)=planeP U:=rfl
lemma castC (x:H): (cpo U) (dip U x)=planeP U x:=rfl
lemma allC (x:CoreH U): dip U (cpo U x)=x:= U.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _
lemma through (x:H): planeP U x ∈ U:= U.toSubmodule.starProjection_apply_mem x
lemma among (x:CoreH U): cpo U x∈U:= show (x:↥U.toSubmodule).val∈U from x.property -- `val` reduce def?
lemma yen (x:CoreH U): ‖cpo U x‖= ‖x‖:= rfl
lemma inlet {x:H} (p:x∈U): planeP U x=x:= Submodule.starProjection_eq_self_iff.mpr p
lemma sightL (x:H)(y:CoreH U): inner ℂ (dip U x) y=inner ℂ x (cpo U y):= U.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right _ _
lemma sightR (x:CoreH U)(y:H): inner ℂ x (dip U y)=inner ℂ (cpo U x) y := U.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _
lemma planeP_inner (x y:H): inner ℂ (planeP U x) y= inner ℂ x (planeP U y):= U.toSubmodule.inner_starProjection_left_eq_right x y
lemma planeP_star : star (planeP U)=planeP U:=by ext1 x; apply ext_inner_right ℂ; intro y; rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, planeP_inner]
lemma restrict_deflect (x:H): ‖dip U x‖ ≤ ‖x‖:= by
 rw [←yen,castC]; exact Submodule.norm_starProjection_apply_le _ _ -- tune
lemma withdraw (p:U≤ X) : planeP U * planeP X=planeP U := Submodule.starProjection_comp_starProjection_of_le p
abbrev social (U:ClosedSubmodule ℂ H)(x:H.Op):(CoreH U).Op:= ((dip U).comp x).comp (cpo U)
-- continuous contraction & unitality
lemma social_sum (x y:H.Op): social U (x+y)=social U x + social U y:= ContinuousLinearMap.ext (fun z=> map_add (dip U) (x (cpo U z)) (y (cpo U z)))
lemma social_fee (x:H.Op)(z:ℂ): social U (z • x)= z • social U x:= ContinuousLinearMap.ext fun t=>map_smul (dip U) z _
def broadcast (U:ClosedSubmodule ℂ H) : H.Op →ₗ[ℂ] (CoreH U).Op where
 toFun:= social U
 map_add' x y:= social_sum x y
 map_smul' z x:= social_fee x z
lemma social_bound (x:H.Op): ‖social U x‖ ≤ ‖x‖:= ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun i=> (restrict_deflect (U:=U) _).trans ((x.le_opNorm _).trans_eq (by rfl))
lemma sightS (x:H.Op)(u v:CoreH U): inner ℂ u (social U x v)=inner ℂ (cpo U u) (x (cpo U v)):= sightR u _
lemma social_star (x:H.Op): social U (star x)=star (social U x):=by ext1 y; apply ext_inner_left ℂ; intro z; rw [sightS, ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]; exact (sightL (U:=U) _ _).symm
lemma social_id : social U 1=1:= ContinuousLinearMap.ext (fun i:CoreH U=> allC (U:=U) i)
lemma social_mul (x y:H.Op) : social U (x * planeP U * y)= social U x * social U y:= rfl -- composition defin assoc proof irrelevant
-- SOT viewport
abbrev strong (X:ℕ→ F→L[ℂ]H)(f:F→L[ℂ] H):Prop:=∀ x:F,Tendsto (fun n=>X n x) atTop (𝓝 (f x))
variable {T:ℕ→ F→L[ℂ]H}{R: F →L[ℂ]H}
namespace strong
lemma follows (p:strong T R)(g:H→L[ℂ] Y): strong (fun i=>g.comp (T i)) (g.comp R):= fun x=> g.continuous.continuousAt.tendsto.comp (p x)
lemma leads (p:strong T R)(g:Y→L[ℂ]F): strong (fun i=>(T i).comp g) (R.comp g):= fun x=> p (g x)
lemma socializes {T:ℕ→H.Op}{R:H.Op}(p:strong T R): strong (fun i=> social U (T i)) (social U R):= (p.follows (Y:=CoreH U) (dip U)).leads (Y:=CoreH U) (cpo U)
end strong
lemma descender (C:ℕ→ ClosedSubmodule ℂ H)(w:Antitone C): strong (fun i:ℕ=> planeP (C i)) (planeP (⨅ i,C i)):= by
 let Y (i:ℕ):=(C i).toSubmoduleᗮ; let V:=(⨆ i,Y i).topologicalClosure; let Q:=⨅ i,C i
 have hd:Monotone Y:=fun _ _ h=> Submodule.orthogonal_le (show (C _).toSubmodule≤ (C _).toSubmodule from w h)
 have he: Q.toSubmoduleᗮ=V:=by
   unfold V Q; rw [← Submodule.orthogonal_orthogonal_eq_closure]; congr 1; rw [← Submodule.iInf_orthogonal, ClosedSubmodule.toSubmodule_iInf]; apply iInf_congr; intro i; exact Submodule.orthogonal_orthogonal _|>.symm
 intro x; have hp (i:ℕ):planeP (C i) x=x-(Y i).starProjection x:= by rw [Submodule.starProjection_orthogonal_val]; change _=x-(x-planeP (C i) x); abel
 have hz:planeP Q x=x-V.starProjection x:= by simp only [← he, Submodule.starProjection_orthogonal_val]; abel -- tune
 change Tendsto _ _ (𝓝 (planeP Q x)); simp_rw [hp,hz]; exact (Filter.Tendsto.sub tendsto_const_nhds (Submodule.starProjection_tendsto_closure_iSup Y hd x))

abbrev domQ (f:H.Op): ClosedSubmodule ℂ H:= -- f.eqLocus = submodule.IsClosed.Class
 { toSubmodule := LinearMap.eqLocus f.toLinearMap ((1:H.Op).toLinearMap)
   isClosed' := isClosed_eq f.continuous continuous_id }
lemma domQ_mem (x:H.Op)(z:H): z∈domQ x ↔ x z=z:= Iff.rfl
abbrev meanL (T:ℕ→ H.Op)(n:ℕ):H.Op:= ((n:ℂ)⁻¹) • ∑ i∈range n,T i
lemma mean_s (f:H.Op)(p:‖f‖ ≤ 1): strong (meanL (fun i:ℕ=>f^i)) (planeP (domQ f)):= by
 intro x; let g:= fun i:ℕ=> f^i; have he:∀ i, g i x=f^[i] x:= by
    intro i; induction i with
    | zero=> rfl
    | succ i ih=> rw [Function.iterate_succ_apply']; unfold g; rw [pow_succ',mul_apply_eq_comp]; exact congrArg f ih
 have h(n:ℕ): meanL g n x=birkhoffAverage ℂ f id n x:=by simp_rw [meanL,_root_.smul_apply,_root_.sum_apply,he]; rfl
 simp_rw [show ∀ n, meanL (fun i:ℕ=>f^i) n x=birkhoffAverage ℂ f id n x from h]; exact ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection f p x
lemma equilibrium {f g:H.Op}(p:‖f‖≤1)(e:Commute f g): Commute (planeP (domQ f)) g:= by
 apply ContinuousLinearMap.ext; intro x; let M:=fun n=> meanL (fun i:ℕ=> f^i) n; let S:= planeP (domQ f)
 change S (g x)= g (S x)
 have hv:strong M S:= mean_s f p; refine tendsto_nhds_unique_of_eventuallyEq (hv (g x)) ((g.continuous.tendsto _).comp (hv x)) (Eventually.of_forall fun i=>?_); dsimp only [Function.comp_apply]; have he(n): (f^n) (g x)= g ((f^n) x):= DFunLike.congr_fun (e.pow_left n).eq x
 simp_rw [M,meanL,_root_.smul_apply, _root_.sum_apply,map_smul,map_sum,he]
lemma dom_commute {f g:H.Op}(p:‖f‖≤1)(u:‖g‖ ≤ 1)(e: Commute f g): Commute (planeP (domQ f)) (planeP (domQ g)):= (equilibrium u (equilibrium p e).symm).symm
lemma infP (C X:ClosedSubmodule ℂ H)(p:Commute (planeP C) (planeP X)): planeP (C⊓X)= (planeP C)*(planeP X) := by
 ext1 x; let y:=planeP X x; let z:=planeP C y
 apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
 · refine ⟨show z∈C from through _,?_⟩; change z∈ X.toSubmodule; rw [show z=planeP X (planeP C x) from DFunLike.congr_fun p.eq x]; exact through _
 intro w t; obtain ⟨u,v⟩:= t; change inner ℂ (x-z) w=0; have he:w∈ C:=u; have hz:w∈ X:=v; rw [inner_sub_left]; unfold z y; rw [planeP_inner,planeP_inner] -- second inside? (planeP X x). remaining right transf
 rw [inlet he, inlet hz, sub_self]
#print axioms descender
#print axioms dom_commute
end YM.CF.Buffered.Afterglow.Hierarchy.Hills
