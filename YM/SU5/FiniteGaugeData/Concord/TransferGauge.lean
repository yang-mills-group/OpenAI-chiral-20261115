import YM.SU5.FiniteGaugeData.Concord.Rehearsal
import YM.CF.Pyx.Warp
import YM.CF.Bloom.Piper
/-! # Gauge covariance of this kernel, keeping the actual joint links

Go through ANY fields incl second links; phase, boundary conditions: use `wrap`, spins and
transport as in these `Fine` words. For arbitrary gauge fields, cannot shortcut with e.g. a
claim about invariance only on `legal G e`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 580000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Girt
section colors
variable {N P:Side}(G:Ratio N P)(p: Odd G.count.val)(g:Seat P→SU.E)
local notation "Y"=> ((Peaks.parcel G true 0).run g)
local notation "Z"=> ((Peaks.parcel G false 0).run g)
local notation "γ"=> scaleG G g
local notation "φ"=> tradew N γ
local notation "ψ"=> tradew P g
local notation "M" i:max j:max=> matter (g (Peaks.touch G i j))

-- use Swatch.panel_ticket proof with arbitrary base type to avoid splitting torus
private lemma panel_lift {I:Type*}[Fintype I][DecidableEq I](i j:I) (A B:Op SU.Slot) (f h:I→Op SU.Slot) (p:A*h j=f i*B) :
    panel i j A * jump (Equiv.refl I) h = jump (Equiv.refl I) f * panel i j B := by
  ext ⟨a,k⟩ ⟨c,l⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,jump_apply,Equiv.refl_apply, Tulip.panel,Matrix.of_apply]
  by_cases v:a=i <;> by_cases hh:c=j
  · subst a c; simp only [true_and,and_true,mul_ite,ite_mul]; simp; have he:=Matrix.ext_iff.mpr p k l; simpa [Matrix.mul_apply,SU.Slot,Fintype.sum_prod_type] using he
  all_goals simp [v,hh,ite_mul,mul_ite]
private lemma panel_run (i j:Inta G) (A B:Op SU.Slot) (h : A*(M false j).val=(M true i).val*B) : panel i j A * (Z).val=(Y).val*panel i j B:=by
  rw [warrant,warrant]; exact panel_lift i j A B _ _ h

private lemma shades_lobe (b u:Bool) : Commute (lobe G b) (((Peaks.parcel G u 0).run g).val):=by
  unfold Commute SemiconjBy; rw [lobe_diag, warrant]; ext ⟨y,a⟩ ⟨z,w⟩
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases h:y=z <;> simp [lobe_fine,jump_apply,h,mul_comm]

include p
private lemma shades_drag (x:Coil N P) (o:Lattice.Order) (r t:St G.count)(k:Cover)(c:ℂ) :
    drag G true false r t k c o (Peaks.jazz G g x)*(Z).val=(Y).val * drag G true false r t k c o x:=by
  unfold drag; rw [sum_mul,mul_sum]
  refine sum_congr rfl fun i _=> panel_run G g _ _ _ _ ?_; unfold Peaks.jazz; dsimp only; rw [track_g,worn G true false p r t k o i]
  let A:= M true (i,r); let B:= M false (i+wrap N k,t); change (_ • (A.val*_*star B.val))*B.val=A.val*(_ • _)
  rw [Matrix.smul_mul,mul_assoc _ (star B.val), B.property.1,mul_one, Matrix.mul_smul]

variable (j d:ℕ)(h: LaurentRadius j G.count d)(w: Nom N P)(U:Male)
local notation "ƒ"=> mosaic G true false (tub (brix j G.count))
local notation "C"=> Peaks.cloth j U G
include h
private lemma shades_mosaic (x:Coil N P): ƒ (Peaks.jazz G g x)*(Z).val=(Y).val * ƒ x:=by
  unfold mosaic; simp_rw [douse_sum G j h]
  rw [Matrix.mul_smul, Matrix.smul_mul]; simp_rw [mul_sum,sum_mul,shades_drag G p g]

lemma shades_cloth : Peaks.cloth j U G (unionP (july G g w)) * (Z).val=(Y).val* Peaks.cloth j U G (unionP w):=by
  have he (b:Bool): lobe G b*ƒ (unionP (july G g w))*lobe G b*(Z).val=(Y).val*(lobe G b*ƒ (unionP w)*lobe G b):=by
    let E:= ƒ (unionP w); let A:=ƒ (unionP (july G g w)); let L:= lobe G b; let y:=(Y).val; let z:=(Z).val
    change L*A*L*z=y*(L*E*L); have hp:A*z=y*E:= by unfold A z; rw [jig]; exact shades_mosaic G p g j d h _
    have hk:L*z=z*L:=(shades_lobe G g b false).eq; have hL:L*y=y*L:=(shades_lobe G g b true).eq
    rw [mul_assoc _ L,hk, ←mul_assoc _ z, mul_assoc L,hp, ←mul_assoc L, hL]; simp only [mul_assoc]
  unfold Peaks.cloth; rw [add_mul,mul_add,he,he]

omit h p
open Haro
private lemma fee_commutes (b:Bool) (a:SpaceM) (g:Seat N→ SU.E) : Commute (tradew N g).val (feeL b N a.val) := by
  let X:=tradew N g; let P':= plankP N a.val
  have hv:Commute X.val P':=by
    let W:=love N; apply W.symm.injective; change W.symm _= W.symm _; rw [map_mul,map_mul]; unfold P' plankP Tap.headW X; unfold W; rw [StarAlgEquiv.symm_apply_apply, Cascade.twine]
    simp only [jump_mul]; congr 1; ext1 i; rw [op_kron_mul,op_kron_mul]; simp only [one_mul,mul_one,a.property.firm]; rfl
  unfold feeL; split; exact hv.exp_right; exact hv.neg_right.exp_right
include p h
variable (X:Haro.SpaceM)
lemma shades_mode (b:Bool)(v:Ket (Single N)) : byMode G j X.val U (july G g w) b (acts (tradew N γ).val v) = acts (ψ).val (byMode G j X.val U w b v):=by
  rw [byMode_eq,byMode_eq,route_foot,←act_mul,←(fee_commutes b X γ).eq,act_mul,←Pyx.op_t G g 0, ←act_mul,←act_mul]; exact congrArg (fun a:Op (Iota G)=> trailK (switchG G).symm.toEmbedding (acts a _)) (shades_cloth G p g j d h w U) -- ψ.val notation

open Reed (Fine think)
-- stays in Tset even at colliding sites
omit h p
private lemma stays_up {v:Ket (Single N)} (g:Seat N→SU.E) (t:withinM (Tset N) v): withinM (Tset N) (acts (tradew N g).val v):=by
  unfold withinM; rw [←touchP N,←Cascade.tick_g g,←Fock.swivel,touchP N,t]
private lemma stays_down {v:Ket (Single N)} (g:Seat N→ SU.E)(t:withinM (Tset N)ᶜ v): withinM (Tset N)ᶜ (acts (tradew N g).val v):=by
  rw [within_compl,←touchP N,←Cascade.tick_g g,←Fock.swivel,touchP N,within_compl.mp t, map_zero]
lemma fine_gauge {b:Bool}(g:Seat N→SU.E){A:FC (Single N)}{S:Finset (Single N)}(p: Fine (Tset N) S b A) : Fine (Tset N) univ b (twist (quantU (tradew N g)) A):=by
  induction p with
  | one=> rw [map_one]; exact .one
  | empty=>rw [map_zero]; exact .empty _
  | add _ _ p q => rw [map_add]; exact p.add q
  | grow _ _ p q=> rw [map_mul]; exact p.grow q
  | scale _ c p=>rw [twist_scalar]; exact p.scale c
  | seed i _=>
    by_cases e:i∈ Tset N
    · rw [show (think _).term i=put i from if_pos e, ←create_put,twist_create]; exact fine_create _ (stays_up g (within_basis _ _ e)) (within_univ _)
    rw [show (think _).term i= -takeF i from if_neg e, ←remove_take, map_neg, twist_remove]; exact fine_neg (fine_remove _ (stays_down g (within_basis _ _ (mem_compl.mpr e))) (within_univ _))
include h p
local notation "L₀"=> subF G j X.val U p
lemma shades_subst {b:Bool}{S:Finset (Single N)}{f:FC (Single N)} (u: Fine (Tset N) S b f) :
    subF G j X.val U p (july G g w) (twist (quantU (tradew N γ)) f) = twist (quantU (tradew P g)) (subF G j X.val U p w f):=by
  induction u with
  | one=>rw [map_one,sub_one,sub_one,map_one]
  | empty=>rw [map_zero,map_zero,map_zero,map_zero]
  | seed i _=>
    by_cases t:i∈Tset N
    · have e:= within_basis _ _ t
      rw [show (think _).term _=put i from if_pos t, ←create_put,twist_create,sub_create G j X.val U p _ (stays_up γ e), shades_mode G p g j d h,sub_create G j X.val U p _ e, twist_create]
    have e:= within_basis _ _ (mem_compl.mpr t)
    rw [show (think (Tset N)).term _= -takeF i from if_neg t, ←remove_take, map_neg,map_neg,map_neg,map_neg,twist_remove,sub_remove G j X.val U p _ (stays_down γ e),shades_mode G p g j d h,sub_remove G j X.val U p _ e,twist_remove]
  | add _ _ a b=>rw [map_add,map_add,map_add,map_add,a,b]
  | grow a b P Q=> rw [map_mul,sub_mul G j _ _ p _ (fine_gauge _ a) (fine_gauge _ b),P,Q,sub_mul G j _ _ p _ a b,map_mul]
  | scale _ c a=>rw [twist_scalar,map_smul,map_smul,twist_scalar,a]
end colors

section probability
variable {n f:Side}(g:Ratio n f)(A:StepData (More n) (More f))(j d:ℕ)
variable (Q:Haro.SpaceM)(M:Male)(h:Odd g.count.val)(q:Chi)(v β:ℝ)(l:Scree.Loom n)
variable (h₁:A.patch.Branches A.kernel SU.group) (p:LaurentRadius j g.count d)(u:0<v)(s:2*v < firstRadius SU.group)
variable {b:Bool}{S:Finset (Seat n)}{F:Mark n}(B:AtSupport b S F) (V:covariant F)
local notation "T" => gathered g j Q.val M h q v F

private def exteriorMoves (t:Seat n→SU.E): FC (Single n) →L[ℝ] FC (Single n) := LinearMap.toContinuousLinearMap
  (show FC (Single n)→ₗ[ℝ] FC (Single n) from ⟨⟨fun A=> twist (quantU (tradew n t)) A,map_add _⟩,fun a x=> by simp only [←Complex.coe_smul, RingHom.id_apply,twist_scalar]⟩)

include V p B
lemma gatheredGauge (t:Seat f→SU.E)(x:Fields f)(a:Fields n) :
    gathered g j Q.val M h q v F (simultaneous t x) (simultaneous (scaleG g t) a)=
      exteriorMoves t (T x a):=by
  unfold gathered avgF; rw [map_smul,map_sum]; congr 1
  refine sum_congr rfl fun i _=> ?_
  have hf : middle g q v i (simultaneous t x) (simultaneous (scaleG g t) a)=july g t (middle g q v i x a) := Prod.ext (brake_g g q v i h x.2 a.2 t) rfl
  dsimp only [before]; rw [hf, V]; exact shades_subst g h t j d p _ M Q (B.allV _)

variable {B₀ e :ℝ} {k:ℕ}
include h₁ u s
private def revolution (t:Seat n→SU.E) : MeasurableEquiv (Orbit n) (Orbit n) := ⟨⟨gird t,gird t⁻¹,Pyx.gird_inv _,fun i=>by simpa only [inv_inv] using Pyx.gird_inv t⁻¹ i⟩,((Wilson.prior_gauge t).prod (threads t)).measurable,((Wilson.prior_gauge t⁻¹).prod (threads t⁻¹)).measurable⟩

lemma push_gauge (X:Roof n B₀ e k l) (a:A.ratio=ratio g): covariant (pushMark g A j Q.val M h q v β l F):=by
  intro t W; let τ:=scaleG g t; let W':= simultaneous t W; have ha: τ = t∘ A.ratio.embed:=by rw [a]; rfl
  let r(U:Fields f)(y:Orbit n) := A.density (G:=SU.group) β U.1 y.1 • T U (drawn l y)
  have ht:Integrable (r W) (city n):=Env.integrableX (Env.scale (Env.along (slice_env A β h₁ W.1) measurable_fst) (Env.along (g:=fun x:Orbit n=>(W,drawn l x)) (env_gathered g j Q.val M h q v p u s F B.env) (measurable_const.prodMk (drawn_m l X.bill)))) _
  have he:MeasurePreserving (revolution τ) (city n) (city n):= (Wilson.prior_gauge τ).prod (threads τ)
  simp_rw [outright g A j Q.val M h q v β l p X.bill h₁ u s F B.env]; change (∫ i,r W' i ∂city n)=exteriorMoves t (∫ i,r W i∂city n)
  rw [←ContinuousLinearMap.integral_comp_comm _ ht, ← he.integral_comp' (r W')]; apply integral_congr_ae; apply Eventually.of_forall; intro x
  change r W' (gird τ x)=exteriorMoves t (r W x)
  have hf : drawn l (gird τ x)= simultaneous τ (drawn l x):= Prod.ext rfl (X.rev x.1 x.2 τ) -- args
  have G0 : A.density (G:=SU.group) β W'.1 (gird τ x).1 = A.density (G:=SU.group) β W.1 x.1 := by rw [ha]; exact A.covary h₁ t β W.1 x.1
  unfold r; rw [hf,map_smul,G0, show gathered g j Q.val M h q v F W' (simultaneous τ (drawn l x))=_ from gatheredGauge g j d Q M h q v p B V t W (drawn l x)]
end probability
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.push_gauge
