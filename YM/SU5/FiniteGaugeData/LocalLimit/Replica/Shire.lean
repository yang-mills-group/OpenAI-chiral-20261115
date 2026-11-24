import YM.CF.Reflect.Reuse
import YM.CF.Gloss.Feast
import YM.CF.Chaff.Diet
import YM.CF.Continuum.CanYo
import YM.CF.Continuum.CoherentSeams

/-!
# Translating certain scalar marked integrals of the real-time heat history
(The `F` shire-form, shared Page corner / anticut.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP.Str
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator ComplexOrder
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Branch Vale MeasureTheory RG Wilson WilsonStartup RP Nova Spark Sample Reflect Fock
attribute [local instance] opCStarAlgebra
variable {m B: Side} (p:Clip)(S T:ℝ){A D d:ℝ}{c:Foot m B}(W₀: Scroll m B c)(e β t a:ℝ)(u':Foot m B)
local notation "G0"=>SU.group
local notation "n'"=> Domain m B
local notation "U'"=> Pack m B
local notation "μ"=> wheel m B
variable (f:RP.Test m B)
local notation "Ψ" => shireF p S T W₀ e β t a u'
local notation "ψ" => hoistF p S T W₀ e β t a u'
local notation "κ" => ratioRF W₀ e β t a u'

lemma translate_shireF (l:Trip m) (v:∀ j,l.glare j=false) (g:RP.Test m B) (h:∀ x,g (onPack B l x) =
    twist (quantU (fringe (far B l u') u')) (twist (quantU (siteM (fperm m B l))) (f x))) :
    Ψ f = Ψ g := by
 let u := far B l u'; let F':= fun x : U' => twist (star (quantU (fringe (far B l u') u'))) (g x); let M:= (quantU (fringe (far B l u') u'))
 have ht (x : U') : κ f x = κ g (onPack B l x) := by
   apply Eq.trans _ (from_toF β u u' t a _ F' g (by change twist M (twist (star M) _) = _; simpa only [star_star] using twist_inv (star M) (g (onPack B l x))))
   exact (bill_rotF β u' l x v f F' (by unfold F'; rw [h]; exact twist_inv _ _) t a).symm
 have hp(x:U'): primal p _ T S x.1= primal p _ T S (onPack B l x).1:= tendsto_nhds_unique_of_eventuallyEq (going p S T x.1) (going p S T (onPack B l x).1) (Eventually.of_forall fun i : ℕ=> congrArg Real.exp (staff ..).symm)
 unfold shireF; rw [←use_trip l (ψ g)]; apply integral_congr_ae; refine Eventually.of_forall fun i=>?_; unfold hoistF; rw [hp i, ht i]
open Window Scroll Dial Scree Spire
local notation "Λ" => CSide m B
lemma leer_bose(F: Config SU.group (Domain m B)→ℂ)(i:Pack m B): Chaff.leer m B (bosonic Λ F) i= (F i.1) •1 := by unfold bosonic Chaff.leer; rw [cross_scalar,cross_one]
lemma translate_shire_scalar (l: Site (More m)) (X: Config SU.group (Domain m B)→ℂ) :
    Ψ (Chaff.leer m B (bosonic Λ (X ∘ through B (northTrip m l))))= Ψ (Chaff.leer m B (bosonic Λ X)) := by
 apply translate_shireF _ _ _ _ _ _ _ _ _ _ (northTrip m l) (fun _=>rfl) _ _
 intro i
 have hx (U:UNI (Finset (Model (CSide m B)))): twist U 1=1:=by rw [twist_formula,mul_one]; exact U.property.2
 rw [leer_bose,leer_bose,twist_scalar,twist_scalar,hx,hx]; rfl
lemma scalar_of_interest (W:Config SU.group (Domain m B)→ℂ)(v: Envelope W)(H: ScaleK A D W₀)(hp: Budget B e d) : Integrable (ψ (Chaff.leer m B (bosonic Λ W))) μ:= by
 let F(x:U'):= W x.1
 let E: RP.Test m B:= fun _=>1
 have he:Chaff.leer m B (bosonic Λ W)=fun x=>F x • E x:=funext fun x=>leer_bose W x
 have ht: ψ (Chaff.leer m B (bosonic Λ W)) = fun x=>ψ E x * F x:= by
    funext x; rw [he, hoistF, hoistF, weightedF]; ring
 rw [ht]
 exact (obtainRF p S T W₀ e β t a u' E continuous_const H hp).mul_bdd (v.meas.comp measurable_fst).aestronglyMeasurable (Eventually.of_forall fun i : U'=> v.cost.choose_spec i.1)
end YM.CF.RP.Str
