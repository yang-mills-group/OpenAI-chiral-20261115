import GaugeFieldConstruction.Pinions
import YM.Push.LOOP_COEFFICIENT.Color
import YM.CF.Moto.Thorn
/-! # H1. GE and evaluations of Reel. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 28000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix Classical Matrix.Norms.L2Operator
open Fock Tulip Lat Spire Phase Cube
open FlightFlux Fluxim
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
abbrev Gem : Type:= fluxV ℝ Axis
abbrev Sut : Type:= fluxT ℝ Axis
abbrev ComG : Type:= fluxV SU.group.Color Axis
abbrev ComT : Type:= fluxT SU.group.Color Axis
abbrev leadF (E F:Type*) [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]:= E→L[ℝ](F→L[ℝ]ℂ)
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
def hem (v:Gem)(c:SU.group.Color):ComG:=⟨fun i j=> v.val i j • c,fun i j=>by rw [← add_smul,v.property,zero_smul]⟩
def loomH (v:Sut)(c:SU.group.Color):ComT:=⟨fun i j k=> v.val i j k • c,⟨fun i j k=>by rw [← add_smul,v.property.1 i j k,zero_smul],fun i j k=>by rw [← add_smul,←add_smul,v.property.2 i j k,zero_smul]⟩⟩
def gateC (o:Skye.Seat n)(a:ℝ): ComG→L[ℝ] tangD n:= by
 refine LinearMap.toContinuousLinearMap ⟨⟨(fun v=> plot o (formC v) a),?_⟩,?_⟩
 · intro x y; funext i; let z:=stem o i.1; let h:=x.val; change a • ((1/2:ℝ) • FlightFlux.slope (fun j=> x.val j i.2+y.val j i.2) z) = a • ((1/2:ℝ) • _)+a • ((1/2:ℝ) • _); simp only [FlightFlux.slope,smul_add, Finset.sum_add_distrib]; try rfl
 intro x y; funext i; let z:=stem o i.1; change a • ((1/2:ℝ) • FlightFlux.slope (fun j=> x • y.val j i.2) z) = x • a • ((1/2:ℝ) • _); rw [show FlightFlux.slope _ z=x • FlightFlux.slope (fun i' =>y.val i' i.2) z from ?_]; · rw [smul_comm (1/2:ℝ) x, smul_comm a x]
 unfold FlightFlux.slope; rw [smul_sum]; exact sum_congr rfl fun i p=> smul_comm ..
def gateT (o:Skye.Seat n)(a:ℝ): ComT→L[ℝ] tangD n:= by
 refine LinearMap.toContinuousLinearMap ⟨⟨(fun v=> plot o (formT v) a),?_⟩,?_⟩
 · intro x y; funext i; unfold plot camW formT; simp only [Pi.smul_apply,Submodule.coe_add,Pi.add_apply,smul_add,sum_add_distrib]; try rfl
 intro x y; funext i; unfold plot camW formT; simp only [Pi.smul_apply, RingHom.id_apply, Submodule.coe_smul]; let z:=stem o i.1;
 simp_rw [smul_sum]; refine sum_congr rfl fun j _=> sum_congr rfl (fun k _=>?_); module
def coneC (x:Gem): SU.group.Color→ₗ[ℝ]ComG where
 toFun:= hem x
 map_add' u v:= Subtype.ext (funext₂ fun i j=> smul_add ..)
 map_smul' u v:= Subtype.ext (funext₂ fun i j=> smul_comm ..)
def coneT (x:Sut): SU.group.Color→ₗ[ℝ]ComT where
 toFun:= loomH x
 map_add' u v:= Subtype.ext (funext (fun i=>funext₂ fun j k=> smul_add ..))
 map_smul' u v:= Subtype.ext (funext (fun i=>funext₂ fun j k=> smul_comm ..))
def grayC (z:SU.group.Color): Gem→ₗ[ℝ] ComG where
 toFun:= fun x=> hem x z
 map_add' u v:= Subtype.ext (funext₂ fun i j=> add_smul ..)
 map_smul' u v:= Subtype.ext (funext₂ fun i j=> mul_smul ..)
def grayT (z:SU.group.Color): Sut→ₗ[ℝ] ComT where
 toFun:= fun x=> loomH x z
 map_add' u v:= Subtype.ext (funext (fun i=>funext₂ fun j k=> add_smul ..))
 map_smul' u v:= Subtype.ext (funext (fun i=>funext₂ fun j k=> mul_smul ..))
abbrev term (Q: InkD n)(v: tangD n):= lifeH Q (increment 1 v)
abbrev ploy (Q:InkD n): tangD n →L[ℝ] tangD n→L[ℝ]ℂ:= fderiv ℝ (fderiv ℝ (term Q)) 0
abbrev luke (o:Skye.Seat n)(Q:InkD n)(p:BudgetPoint): leadF ComG ComG:= ((ploy Q).comp (gateC o p.threshold)).flip.comp (gateC o p.threshold)|>.flip
abbrev klem (o:Skye.Seat n)(Q:InkD n)(p:BudgetPoint): leadF ComG ComT:= (((ploy Q).comp (gateC o p.threshold)).flip.comp (gateT o p.threshold)).flip
lemma tintWing (o:Skye.Seat n)(x:Gem)(u:SU.E)(t:ℝ)(v:SU.group.Color):gateC o t (coneC x (SU.group.adjoint u v))= VerifiedReset.colorMove u (gateC o t (coneC x v)):=by
 funext i; let z:=stem o i.1; let A:=SU.group.adjoint u; change t • ((1/2:ℝ) • (∑ j:Axis,digit z j • (x.val j i.2 • A v)))=A (t • ((1/2:ℝ) • (∑ j:Axis,digit z j • (x.val j i.2 • v)))) -- tune
 simp only [map_smul,map_sum]
lemma tintJoint (o:Skye.Seat n)(x:Sut)(u:SU.E)(t:ℝ)(v:SU.group.Color):gateT o t (coneT x (SU.group.adjoint u v))= VerifiedReset.colorMove u (gateT o t (coneT x v)):=by
 funext i; let z:=stem o i.1; let A:=SU.group.adjoint u; change t • ((1/3:ℝ) • (∑ j:Axis,digit z j • (∑ k:Axis,lineSi z i.2 k • (x.val k j i.2 • A v))))= A (t • ((1/3:ℝ) • (∑ j:Axis,digit z j • (∑ k:Axis,lineSi z i.2 k • (x.val k j i.2 • v)))))
 simp only [map_smul,map_sum]
lemma ploy_iter (Q:InkD n)(u v:tangD n): ploy Q u v= iteratedFDeriv ℝ 2 (term Q) 0 ![u,v]:=by rw [iteratedFDeriv_two_apply]; try rfl
variable (e₀:PressB p X Q h c)(p₀:0≤ h)
local notation "γ"=> X.val.1
include e₀ p₀
lemma ploy_value (u v:tangD n)(L:ℂ→L[ℝ]ℝ): L (ploy Q u v) = logHessian (L ∘ lifeH Q) u v:= by
 rw [ploy_iter]; change _= iteratedFDeriv ℝ 2 (L ∘ term Q) 0 _; rw [L.iteratedFDeriv_comp_left (f:=term Q) ((eraF _ _ e₀ p₀ _ (ping_f p X.val.2)).paid) (i:=2) (Nat.cast_le.mpr ((by decide:2 ≤6).trans p.order_ge))]; rfl
lemma ploy_herm (u v:tangD n): ploy Q u v=ploy Q v u:= by
 have he(L:ℂ→L[ℝ]ℝ): L (_)= L (_):=(ploy_value e₀ p₀ u v L).trans ((hessian_symm (cashR Q X e₀ p₀ L _ le_rfl).regular u v).trans (ploy_value e₀ p₀ v u L).symm); exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)
lemma ploy_nil (s:Skye.Seat n→SU.group.Color)(x y:tangD n)(u: Agrees X.val.2 x (gradient s)): ploy Q x y=0:=by
 have he(L:ℂ→L[ℝ]ℝ): L (ploy Q x y)= L (0:ℂ):=by -- tune meta
    rw [show L (ploy Q x y)=_ from ploy_value e₀ p₀ x y L]; let E:=(cashR Q X e₀ p₀ L _ le_rfl).regular; have h:=Thera.yet_one
    rw [hessian_agrees h E u (show Agrees X.val.2 y y from fun _ _ _=>rfl),hessian_gradient h E,map_zero]
 exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)
lemma ploy_move(u v:tangD n)(z:SU.E): ploy Q (colorMove z u) (colorMove z v)= ploy Q u v:=by
 have he(L:ℂ→L[ℝ]ℝ): L (_)= L (_):= (ploy_value e₀ p₀ _ _ L).trans ((hessian_color Thera.yet_one (cashR Q X e₀ p₀ L _ le_rfl).regular z u v).trans (ploy_value e₀ p₀ _ _ L).symm)
 exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)
-- Choose spike once. projection inverse & Lin for slot spaces.
abbrev fave (p:BudgetPoint)(o:Skye.Seat n)(Q:InkD n):leadF Gem Gem:= (( (luke o Q p).comp (grayC (spike SU.group)).toContinuousLinearMap).flip.comp (grayC (spike SU.group)).toContinuousLinearMap).flip
abbrev claw (p:BudgetPoint)(o:Skye.Seat n)(Q:InkD n):leadF Gem Sut:= (( (klem o Q p).comp (grayC (spike SU.group)).toContinuousLinearMap).flip.comp (grayT (spike SU.group)).toContinuousLinearMap).flip
omit e₀ p₀ in
lemma pod_uni{G:Gauge}(h:G.Simple)(f:leadF G.Color G.Color)(i:G.Color)(u:‖i‖=1)(v:∀ x a b,f (G.adjoint x a) (G.adjoint x b)=f a b)(x y:G.Color):f x y=f i i * ↑(inner ℝ x y):=by
 let A:= (show (_ →ₗ[ℝ] _)≃ₗ[ℝ](G.Color→L[ℝ]ℂ) from LinearMap.toContinuousLinearMap).symm.toLinearMap.comp f.toLinearMap
 obtain ⟨k,g⟩:= Push.Loops.scalar_complex h A v; rw [show f i i=k from ?_]; · exact g x y
 change A i i=k; rw [g,real_inner_self_eq_norm_sq,u,one_pow,Complex.ofReal_one,mul_one]
lemma formC_Ps(x y:Gem)(a b:SU.group.Color): luke o Q p (hem x a) (hem y b)= fave p o Q x y* ↑(inner ℝ a b):=by
 let A: SU.group.Color→L[ℝ](SU.group.Color→L[ℝ]ℂ):=((((luke o Q p).comp (coneC x).toContinuousLinearMap).flip.comp (coneC y).toContinuousLinearMap).flip)
 refine (pod_uni Thera.yet_one A _ (spike_norm Thera.yet_one) ?_ a b); intro z a b; let t:=p.threshold; let T:=ploy Q;
 let E:=gateC o t; let V:=gateC o t; change T (E (coneC x (SU.group.adjoint z a))) (V (coneC y (SU.group.adjoint z b)))=T (E (coneC x a)) (V (coneC y b));
 rw [show E (_)=colorMove z (E (coneC x a)) from tintWing o x z t a,show V (_)=colorMove z (V (coneC y b)) from tintWing o y z t b]; exact ploy_move e₀ p₀ _ _ z
lemma formT_Ps(x:Gem)(y:Sut)(a b:SU.group.Color): klem o Q p (hem x a) (loomH y b)= claw p o Q x y* ↑(inner ℝ a b):=by
 let A: SU.group.Color→L[ℝ](SU.group.Color→L[ℝ]ℂ):=((((klem o Q p).comp (coneC x).toContinuousLinearMap).flip.comp (coneT y).toContinuousLinearMap).flip)
 refine (pod_uni Thera.yet_one A _ (spike_norm Thera.yet_one) ?_ a b); intro z a b; let t:=p.threshold; let T:=ploy Q;
 let E:=gateC o t; let V:=gateT o t; change T (E (coneC x (SU.group.adjoint z a))) (V (coneT y (SU.group.adjoint z b)))=T (E (coneC x a)) (V (coneT y b));
 rw [show E (_)=colorMove z (E (coneC x a)) from tintWing o x z t a,show V (_)=colorMove z (V (coneT y b)) from tintJoint o y z t b]; exact ploy_move e₀ p₀ _ _ z
end TableF
end YM.CF
end
