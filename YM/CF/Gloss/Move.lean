import YM.CF.Gloss.Gee
import YM.CF.Skye.Zap
set_option autoImplicit false
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gloss
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire
attribute [local instance] opCStarAlgebra
variable {m B N:Side}
variable(B)(x:Era m)
lemma αh(u:Bool): MeasurePreserving (doveV u) cloud cloud:=by
 let Y:=polarT u; have he:Continuous (doveV u):=(polarV u).continuous; have hp:Continuous Y:=Skye.rev_C u; constructor
 exact he.measurable
 unfold cloud; have ht:doveV u ∘ turns=turns ∘ Y:=by
    ext1 z; change (xtra u).X (scaledV z _) = _; rw [(xtra u).trek]; congr 1 -- tune first
    exact Subtype.ext (dove_base ..)
 rw [Measure.map_map he.measurable turns_cont.measurable,ht,←Measure.map_map turns_cont.measurable hp.measurable,(Skye.twirl u).map_eq]
lemma sumMove(p v:Cue m)(x:Era m)(i:Index m)(k:Ballot): update (sumX m x p) i (doveV x.charge k)= sumX m x (update p (ρx x i) k):=by
 funext z; unfold sumX; by_cases h:z=i; subst z; rw [update_self, update_self]; rw [update_of_ne h,update_of_ne ((ρx x).injective.ne h)]
lemma ρPay{A:Type}[DecidableEq A](F:Finset A)(U:Skin m B)(H:A→ArrayF m)(r:A→Phase.Zone)(j:Row)(i)(z): priceW m B F (turnV B x U) (fun i=> αRow x (H i)) r j i (sumX m x z) = priceW m B F U H r j (ρx x i) z :=by
 have he(z):draw m B F (turnV B x U) (fun i=>αRow x (H i)) r j i (sumX m x z) = draw m B F U H r j (ρx x i) z:=by
    apply prod_congr rfl; intro b _; unfold dry; rw [show capRow (αRow x (H b)) j _=αRow x (capRow (H b) j z) by funext i; unfold capRow αRow sumX; by_cases h:i.2=j <;> simp [h]]; exact ν_k ..
 unfold priceW; rw [he]; apply congrArg; unfold limitW
 rw [← (αh x.charge).integral_comp ((polarV x.charge).toHomeomorph.measurableEmbedding)]
 apply integral_congr_ae; exact Eventually.of_forall fun y=>by dsimp only; rw [sumMove z z x i y,he]
lemma vpay(U:Skin m B)(Y:Cue m)(i:Index m):water m B (turnV B x U) i (sumX m x Y)=water m B U (ρx x i) Y:= ρPay _ _ _ U (fun _=>slot m Y) ..
lemma lawful(U:Skin m B)(Y:Cue m):law m B (turnV B x U) (sumX m x Y)=law m B U Y:=by unfold law; simp_rw [vpay]; exact Equiv.prod_comp (ρx x) (fun i=> water m B U i Y)
lemma ctS:Continuous (sumX m x):=continuous_pi fun i=> (polarV x.charge).continuous.comp (continuous_apply _)
lemma past(t:Cue m): sumX m x⁻¹ (sumX m x t)=t:=by
 let U:Pack m m:=(1,t); exact congrArg Prod.snd (by rw [bake,mul_inv_cancel,ζ_o]: vest m x⁻¹ (vest m x U)=U)
def pasM : Cue m ≃ₜ Cue m:= {
 toFun:=sumX m x
 invFun:=sumX m x⁻¹
 left_inv:= past x
 right_inv:=fun t=>by simpa only [inv_inv] using past x⁻¹ t
 continuous_toFun:=ctS x
 continuous_invFun:=ctS _ }
lemma ψRain:MeasurePreserving (sumX m x) (rains m) (rains m):=by
 let f(t:Cue m):= t ∘ ρx x; have he: MeasurePreserving f (rains m) (rains m):=by
    convert measurePreserving_piCongrLeft (α:=fun _:Index m=>Ballot) (fun _=>cloud) (ρx x).symm using 1; ext t i : 2; obtain ⟨j,rfl⟩:=(ρx x).symm.surjective i; rw [MeasurableEquiv.piCongrLeft_apply_apply]; simp only [f,Function.comp_apply,Equiv.apply_symm_apply]
    all_goals rfl
 let P:Cue m→Cue m:=fun z i=>doveV x.charge (z i); have hp: MeasurePreserving P (rains m) (rains m):= measurePreserving_pi (μ:=fun _=>cloud) (fun _=>_) (fun _=> αh _) -- tune
 exact hp.comp he
end YM.CF.Gloss
