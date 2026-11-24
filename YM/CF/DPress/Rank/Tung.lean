import YM.CF.DPress.Rank.Wing
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Heath
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
open Exa Tap Dial
open Levier Thera Urn Nacre Salt
open Haro -- 
open Cad
variable {d a b c t:ℝ}{N:Side}(T:Elm N (ΘS 1) d a b)
namespace Mercer
abbrev YΩ(d:ℝ)(N:Side): Type:= Openc (More N) d
abbrev priceN(t b:ℝ) := Cad.rent*t*b
lemma future (X:Support (More N)): pendB (badge _) (bail N d) (bail N d) (T.F X) X (T.W X):= T.coat X
-- abstract Suite escalation on pre-granted array
variable {Y I D G:Type*} [Fintype Y][Fintype I][DecidableEq Y][DecidableEq I][TopologicalSpace D]
lemma suit_basis (b:Stage Y I D G)(s:Branch.Tag b) (L:License D)(S:Seal Y)(c:Toll I)(F:ΘS 1 → Raw D I)(f:∀ i,Suite L s s S c (F i))(_u:0≤t)(i:ΘS t): Suite L s s S (fun j k=> Cad.rent*t*c j k) (fun d=> ∑ j:Cad.Index,(econ j i.val:ℂ) • F (unitCell j) d):=by
 let θ(j:Cad.Index):ℂ:=econ j i.val; let O(j:Cad.Index)(k):= θ j • F (unitCell j) k
 have hθ: (∑ j:Cad.Index,‖θ j‖) ≤ Cad.rent * t:=by unfold θ; simp only [Complex.norm_real]; exact (Cad.horizon _).trans (mul_le_mul_of_nonneg_left i.property Cad.pos.le)
 have hv(j:Cad.Index): Suite L s s S (fun k l=>‖θ j‖* c k l) (O j):= (f (unitCell j)).accel _
 let x0:ΘS 1:=⟨0,by rw [norm_zero]; exact zero_le_one⟩; have hx:=f x0
 let g:Toll I:= fun j k=> ∑ l:Cad.Index,‖θ l‖*c j k
 have hp:= Ticket.sumT univ _ _ (fun i (_:i∈(univ:Finset Cad.Index))=>(hv i).toTicket)
 refine ⟨⟨hp.frame,fun j k=>?_⟩,L.suppose univ _ (fun i _=> (hv i).fuel)⟩; have hi: g j k ≤ Cad.rent*t*c j k:=by unfold g; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right hθ (hx.nonn j k)
 let u':= hp.expo j k; -- Expo
 exact ⟨u'.positive.trans hi,fun v=> (hx.expo j k).triggered (right_ne_zero_of_mul v),fun x=> (u'.bounded x).trans hi,fun x y=> (u'.variation x y).trans (mul_le_mul_of_nonneg_right hi (b.pos S x y)),u'.connected⟩
-- choose using Complex SMul.Analytic.R.L. later Real-use.AOP cert.
abbrev Krock (X:Support (More N))(x:YΩ d N) : Cad.Θ→ₗ[ℝ] Op (Single N):= {
 toFun := fun i=>∑ j:Cad.Index,econ j i • T.F X (unitCell j) x
 map_add' := fun i j=> by simp only [map_add,add_smul,sum_add_distrib]
 map_smul' := fun v i=> by simp only [map_smul,smul_eq_mul,RingHom.id_apply, Finset.smul_sum,mul_smul] }
lemma Krockc(X:Support (More N))(x:YΩ d N)(q:Cad.Θ): Krock T X x q=∑ j:Cad.Index, (econ j q:ℂ) • T.F X (unitCell j) x:=by apply sum_congr (s₁:=(univ:Finset Cad.Index)) (f:=fun i=>econ i q • T.F X (unitCell i) x) rfl; intro i _; simp only [Complex.coe_smul]
variable (t) (p:0≤ t)
def rentT : Elm N (ΘS t) d a (priceN t b) := ⟨fun X i x=> Krock T X x i.val,
 fun X i j => Cad.rent*t*T.W X i j,
 fun X=>⟨fun j=>by simp_rw [Krockc]; exact suit_basis _ _ _ _ _ _ (future T X).1 p j, fun x=> (LinearMap.continuous_of_finiteDimensional (Krock T X x)).comp continuous_subtype_val⟩,
 T.bank.funds (mul_nonneg Cad.pos.le p)⟩
abbrev Tip {d a b N}(T:Elm N (ΘS 1) d a b) (G:Chin N→ (Cad.Θ →ₗ[ℝ] Op (Single N))):Prop:= NearL T (fun i p=> G p i.val) -- autoImplicit d a b inferred?
include p
lemma rises(G:Chin N→ (Cad.Θ→ₗ[ℝ] Op (Single N)))(u:Tip T G): NearL (rentT t T p) (fun i k=> G k i.val):=by
 intro j x V g f; change (G x.val j.val)=∑ S:Support (More N),Krock T S x j.val -- maybe implicit annotate
 conv_lhs=>arg 2; rw [←Cad.tagline j.val]
 rw [map_sum]
 change ∑ i:Cad.Index,G x.val (econ i j.val • (Expr i))= ∑ S:Support (More N),∑ i:Cad.Index,econ i j.val • T.F S (unitCell i) x; rw [sum_comm (s:=(univ:Finset (Support (More N))))]; refine sum_congr rfl ?_; intro i _; rw [map_smul,show G x.val (Expr i)= _ from u (unitCell i) x V g f, Finset.smul_sum] -- binder unused
lemma leafJ_s(U:Elm N (ΘS 1) d a b)(s:Sweep N)(f:Bool)(h:leafJ s f T U): leafJ s f (rentT t T p) (rentT t U p) :=by intro i Y V y g; change Krock U _ _ i.val = realR s f (Krock T _ _ i.val); simp_rw [Krockc,real_f,Sour.real_t,h _ _ _ _ g]
end Mercer
end YM.CF.Sour.Heath
