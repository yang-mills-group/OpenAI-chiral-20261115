import YM.SU5.Reconstruction.Quartz.Charon
/-! # Recover enough loyalty for the Wedge bookstore from equality on Wick labels and density. -/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Ship
open Function Set Filter MeasureTheory Spectral Analysis Metric ContinuousLinearMap Picket CrossedFrame Clasp BridgeClub Anvil Waltz Submodule
open scoped BigOperators Topology InnerProductSpace ComplexOrder NNReal ENNReal Complex
variable {H D K:Hilbert} (C:Clasp K H D)
-- easier order on quum, no new net bicomm equivalences
lemma regulator (A:H.Op)(h:∀ t :ℝ,Commute A (boost C t)): Commute A C.plume:=by
 let M:= C.Left.conjStarAlgEquiv; obtain ⟨Z,e⟩:= M.surjective A; have hx:M Z=A:=e; rw [←hx,C.portAngle]; apply Commute.map _ C.Left.conjStarAlgEquiv.toStarAlgHom; apply C.reins; intro u
 have he:=h (-u*Real.pi); unfold boost at he; rw [show -(-u*Real.pi)/Real.pi=u by field_simp] at he
 apply show M (Z*C.Cabin u)=M (C.Cabin u*Z)→Commute Z (C.Cabin u) from fun z=> M.injective z; rw [map_mul,map_mul,hx]; exact he
lemma starCom (P:Submodule ℂ H)[P.HasOrthogonalProjection](f:H.Op)(k:MapsTo f P P)(w:MapsTo (star f:H.Op) P P): Commute f P.starProjection:= by
 have e : MapsTo f Pᗮ Pᗮ:=by intro x hx y hy; change inner ℂ y (f x)=0; rw[← adjoint_inner_left]; exact hx _ (w hy)
 ext1 x; let u:=P.starProjection x; let v₀:=Pᗮ.starProjection x; have hx : u + v₀=x:= P.starProjection_add_starProjection_orthogonal x
 have hp:u∈P:= starProjection_apply_mem ..; have hv:v₀∈Pᗮ:= starProjection_apply_mem ..
 change f u= P.starProjection (f x)
 rw [show f x=f u+f v₀ from (congrArg f hx.symm).trans (map_add ..)]; rw [map_add, Submodule.starProjection_eq_self_iff.mpr (k hp),P.starProjection_apply_eq_zero_iff.mpr (e hv),add_zero]
def parish (M:Net H)(Ω:H): Submodule ℂ H:= (Submodule.span ℂ ((fun x:H.Op=>x Ω) '' (M:Set H.Op))).topologicalClosure
abbrev owns_it (M:Net H)(Ω:H):Prop:= ∀x:H,x∈parish M Ω
local notation "P"=> C.plume
local notation "δ"=> C.shadow
variable (M N:Net H)(Ω:H)(J:Flash H)(p: N≤ M)
local notation "Z"=>parish N Ω
variable (h:owns_it N Ω)(b:∀ t:ℝ,boost C t Ω=Ω)(e:∀t:ℝ,∀ A∈N,ascend t C A∈N) (w:∀ A∈M,C.plume (J.f (star A Ω))=C.shadow (A Ω))
include p h b e w
lemma contribution : Rank J Ω (N:Set H.Op) := by
 let U:= (span ℂ (label J Ω '' (N:Set H.Op))).topologicalClosure; let G(t):= (boost C t:H.Op)
 change ∀ x:H, x ∈ U
 have q(A:H.Op)(h:A∈N) : P (label J Ω A)= A Ω:= (C.formulates _ _ (w A (p h))).1.symm
 have X(t):MapsTo (G t) U U:=by
    let L:= U.comap (G t).toLinearMap; have Y:span ℂ (label J Ω '' (N:Set H.Op))≤L:= by
       apply Submodule.span_le.mpr; rintro _ ⟨x,g,rfl⟩; change G t (label ..) ∈ U; rw [show G t (label J Ω x)= label J Ω (ascend t C x) from ?_]; exact le_topologicalClosure _ (subset_span ⟨_,e t x g,rfl⟩)
       apply C.plume_inj; rw [show P (G t (label J Ω x))=G t (P (label J Ω x)) from DFunLike.congr_fun (C.transBeat t).eq (label ..),q x g,q _ (e t x g)]; unfold ascend; rw [mul_apply_eq_comp,mul_apply_eq_comp,boostStar,b]
    intro x hx; change x ∈ L; have hL: IsClosed (L:Set H):= (Submodule.isClosed_topologicalClosure _).preimage (G t).continuous
    exact closure_minimal (SetLike.le_def.mp Y) hL hx
 have v: Commute U.starProjection P:= regulator C _ fun t=>(starCom U _ (X t) (by rw [boostStar]; exact X (-t))).symm -- class
 intro x; suffices Z ≤ U from this (h x)
 apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_topologicalClosure _)
 apply Submodule.span_le.mpr; rintro _ ⟨a,k,rfl⟩; change a Ω∈ U; rw [← q a k]
 apply U.starProjection_eq_self_iff.mp; change U.starProjection (P _)= _; rw [show U.starProjection (P (label J Ω a))=P (U.starProjection _) from DFunLike.congr_fun v.eq _, U.starProjection_eq_self_iff.mpr (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨_,k,rfl⟩))]
lemma absorbed (S:∀ A∈M, J.shade A∈M.commutant)(j:J.f Ω=Ω) : N=M:= by
 let h': Club C J N Ω (N:Set H.Op):=⟨Subset.rfl,fun _ k=>star_mem k, fun x i=>w x (p i),fun x i=> (VonNeumannAlgebra.mem_commutant_iff).mpr (fun A u=> VonNeumannAlgebra.mem_commutant_iff.mp (S x (p i)) A (p u)),j,contribution C M N Ω J p h b e w⟩
 rw [← N.commutant_commutant, h'.equality (fun x i=> S x (p i)) (fun A i=> VonNeumannAlgebra.mem_commutant_iff.mpr (fun x j=>VonNeumannAlgebra.mem_commutant_iff.mp i x (p j))), M.commutant_commutant]
end YM.Quartz.Ship
#print axioms YM.Quartz.Ship.absorbed
