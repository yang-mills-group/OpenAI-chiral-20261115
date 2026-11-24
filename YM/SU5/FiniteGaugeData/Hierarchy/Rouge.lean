import YM.SU5.FiniteGaugeData.Hierarchy.Aperture
import YM.CF.Pyx.Warp
/-! # Pointwise gauge covariance preserved by `subF` even at seam transforms and all field arguments (not just legal initial fields).

NOT for arbitrary Q in the Step; `Q` needs to be in the commutant as is the actual wave. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace Tint
open Girt Nacre Mir Phase RP

section
variable {I:Type*}[Fintype I][DecidableEq I](p q:I→Op SU.Slot)(i j:I)(U V:Op SU.Slot)(h:U * q j=p i * V)
include h
-- extract helper from Tulip.Swatch
private lemma pennies : panel i j U * jump (Equiv.refl _) q=jump (Equiv.refl _) p * panel i j V:=by
  ext ⟨a,k⟩ ⟨c,l⟩; simp only [Matrix.mul_apply,Fintype.sum_prod_type,jump_apply,Equiv.refl_apply,panel,Matrix.of_apply]; by_cases e:a=i<;>by_cases w:c=j
  · subst a c; simp only [true_and,and_true,mul_ite,ite_mul]; simp; have hk:= Matrix.ext_iff.mpr h k l; simpa [Matrix.mul_apply,SU.Slot,Fintype.sum_prod_type] using hk
  all_goals simp [e,w,ite_mul,mul_ite]
end

variable {N P:Side}(G:Ratio N P)(g:Seat P→ SU.E)(e:ℝ)
set_option quotPrecheck false
local notation "U"=> ((Peaks.parcel G true e).run g).val
local notation "V"=> ((Peaks.parcel G false e).run g).val
local notation "ω"=> (tradew P g).val
local notation "Θᵥ"=> (tradew N (scaleG G g)).val

private lemma dilation (u v:Bool) :
    lobe G u * ((Peaks.parcel G v e).run g).val= ((Peaks.parcel G v e).run g).val*lobe G u := by
  rw [lobe_diag,warrant]; ext ⟨y,a⟩ ⟨z,b⟩; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases h:y=z <;> simp [lobe_fine,jump_apply,h,mul_comm]
variable (j:ℕ)(ho: Odd G.count.val)(x:Nom N P)
local notation "Z"=> Peaks.july G g x
include ho
private lemma scale_drag (o:Lattice.Order)(t u:St G.count)(z:Cover)(c:ℂ) :
    drag G true false t u z c o (unionP Z) * V= U * drag G true false t u z c o (unionP x):=by
  let P(b)(a:Inta G):= (SU.matter (g (Peaks.touch G b a)))
  rw [drag,drag,Finset.sum_mul,Finset.mul_sum,warrant,warrant]; refine sum_congr rfl fun a _=> ?_ ; apply pennies; unfold unionP
  simp only [track_pr]; rw [show (Z).1=gauge g x.1 from rfl,travel_gauge,worn G true false ho, Tulip.brand_mul,Tulip.brand_mul,Tulip.brand_inv];
  let k:= P true (a,t); let y:= P false (a+wrap N z,u); change _ • (k.val * _ * star y.val) * y.val=k.val * (_ • _); rw [Algebra.smul_mul_assoc,mul_assoc _ (star y.val),y.property.1,mul_one,Algebra.mul_smul_comm]

variable (D:ℕ)(p:LaurentRadius j G.count D)
local notation "ℓ"=>mosaic G true false (tub (brix j G.count))
include p
private lemma scale_mosaic : (ℓ) (unionP Z) * V= U * ((ℓ) (unionP x)):=by
  unfold mosaic; simp_rw [douse_sum G j p, Matrix.smul_mul, Matrix.mul_smul,Finset.mul_sum,Finset.sum_mul,scale_drag G g e ho]

lemma bright (M:Male): Peaks.cloth j M G (unionP Z)* V= U*Peaks.cloth j M G (unionP x):=by
  unfold Peaks.cloth; dsimp only; have ht(b): lobe G b * ((ℓ) (unionP Z))* lobe G b * (V)= U * (lobe G b * ((ℓ) (unionP x))* lobe G b):=by rw [mul_assoc _ (lobe G b), dilation, ←mul_assoc _ V (_), mul_assoc (lobe G b) ((ℓ) (unionP Z)),scale_mosaic G g e j ho x D p,←mul_assoc (lobe G b) U,dilation,mul_assoc U,mul_assoc U] -- tune
  rw [add_mul,mul_add,ht,ht]

omit ho p in
private theorem beta_frame {N:Side}(Q:Op SU.Slot)(h:Mind Q)(g:Seat N→SU.E): Commute (tradew N g).val (plankP N Q):=by
  let F:=tradew N g; let P:=Tap.plankP N Q
  have ht: (love N).symm F.val=jump (Equiv.refl (Site N)) (fun i=> (1:Op SpinIdx) ⊗ₖ (matter (g (node i))).val):= Cascade.twine g
  unfold Commute SemiconjBy; apply (love N).symm.injective; rw [map_mul,map_mul]; change (love N).symm F.val * (love N).symm P= (love N).symm P*(love N).symm F.val; unfold P; rw [ht,plankP, headW,(love N).symm_apply_apply,jump_mul,jump_mul]; apply congrArg; ext1 i; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,h.firm]; rfl
-- sewing along every gauge transformation at the fine level; input transformed by exactly its coarse restriction
include ho p
lemma colored_mode (M:Male)(Q:Op SU.Slot)(h:Mind Q)(b:Bool)(v:Ket (Single N)) :
    byMode G j Q M Z b (acts Θᵥ v)= acts ω (byMode G j Q M x b v):=by
  letI : NormedAlgebra ℚ (Op (Single N)) := NormedAlgebra.restrictScalars ℚ ℂ _
  have he:feeL b N Q*(Θᵥ)=(Θᵥ)*feeL b N Q:= by
    cases b
    · exact (Commute.exp_right (beta_frame Q h (scaleG G g)).neg_right).symm.eq
    exact (Commute.exp_right (beta_frame Q h _)).symm.eq
  rw [byMode_eq,byMode_eq,←act_mul,he,act_mul, ←Pyx.op_t G g 1,route_foot,←act_mul (Peaks.cloth j M G (unionP Z)), bright G g 1 j ho x D p]; rw [act_mul]; rfl

variable {S:Finset (Single N)}{f:FC (Single N)}{b:Bool}
omit ho p
private lemma holdT {S:Finset (Single N)}(U':UNI (Single N))(p:twist U' (cutM S)=cutM S) {x:Ket (Single N)}(h:withinM S x): withinM S (acts U'.val x):= by unfold withinM; rw [← p,← Fock.swivel,h]
private lemma staysUp (g: Seat N→SU.E) {i:Single N}(e:i∈Tset N):withinM (Tset N) (acts (tradew N g).val (basisKet i)):= holdT (tradew N g) (touchP N ▸ Cascade.tick_g g) (within_basis _ _ e) -- tune cast
private lemma staysDown (g: Seat N→SU.E) {i:Single N}(e:i∉Tset N):withinM (Tset N)ᶜ (acts (tradew N g).val (basisKet i)):= holdT (tradew N g) (by rw [dim_cut,← touchP,map_sub,map_one,Cascade.tick_g g]) (within_basis _ _ (mem_compl.mpr e))
lemma color_fine (g:Seat N→ SU.E)(h:Fine (Tset N) S b f): Fine (Tset N) univ b (twist (quantU (tradew N g)) f):=by
  induction h with
  | seed i _=>
    by_cases p:i∈ Tset N
    · rw [show (Reed.think (Tset N)).term i=put i from if_pos p,←create_put,twist_create]; exact fine_create _ (staysUp g p) (within_univ _)
    rw [show (Reed.think (Tset N)).term i= -takeF i from if_neg p, map_neg,←remove_take, twist_remove]
    simpa using (fine_remove _ (staysDown g p) (within_univ _)).scale (-1)
  | empty=> rw [map_zero]; exact .empty _
  | one=> rw [map_one]; exact .one
  | add _ _ a b=> rw [map_add]; exact a.add b
  | grow _ _ a b=> rw [map_mul]; exact a.grow b
  | scale _ _ a=> rw [twist_scalar]; exact a.scale _
include ho p
local notation "Y"=> (scaleG G g)
lemma sub_shift (M:Male)(Q:Op SU.Slot)(q: Mind Q)(F:Fine (Tset N) S b f): subF G j Q M ho (Z) (twist (quantU (tradew N Y)) f)= twist (quantU (tradew P g)) (subF G j Q M ho x f):=by
  induction F with
  | seed i _=>
    by_cases h:i∈Tset N
    · rw [show (Reed.think (Tset N)).term i=put i from if_pos h,←create_put,twist_create,sub_create G j Q M ho (Z) (staysUp _ h), sub_create G j Q M ho _ (within_basis _ _ h), colored_mode G g j ho x D p M Q q,twist_create]
    rw [show (Reed.think (Tset N)).term i= -takeF i from if_neg h, map_neg,map_neg,map_neg,map_neg, ←remove_take,twist_remove,sub_remove G j Q M ho (Z) (staysDown _ h), sub_remove G j Q M ho _ (within_basis _ _ (mem_compl.mpr h)), colored_mode G g j ho x D p M Q q,twist_remove]
  | grow a b ih t=> rw [map_mul, sub_mul G j Q M ho _ (color_fine _ a) (color_fine _ b), sub_mul G j Q M ho _ a b, ih,t, map_mul]
  | empty=> simp
  | one=> simp [sub_one]
  | add _ _ a b=> rw [map_add,map_add,map_add,map_add,a,b]
  | scale _ _ a=> rw [twist_scalar,map_smul,map_smul,twist_scalar,a]
#print axioms sub_shift

variable (hF:ℝ)(t:Chi)(W:Fields P)
private lemma canvas {Z':Support (More N)} (k:Mark N)(Q:Op SU.Slot)(M:Male)(h:covariant k)(q:AtSupport b Z' k)(v:Mind Q)(X:Fields N):
    gathered G j Q M ho t hF k (simultaneous g W) (simultaneous (scaleG G g) X)= twist (quantU (tradew P g)) (gathered G j Q M ho t hF k W X) := by
  have he(i:Forest (ratio G)): middle G t hF i (simultaneous g W) (simultaneous (scaleG G g) X)=Peaks.july G g (middle G t hF i W X):= Prod.ext (brake_g G t hF i ho W.2 X.2 g) rfl
  unfold gathered avgF before; simp_rw [he,h _ X,sub_shift G g j ho (middle G t hF _ W X) D p _ _ v (q.allV X),← map_sum]; simp_rw [← Complex.coe_smul, twist_scalar]
omit ho p in
private def turnCLM (U':UNI (Finset (Single P))) : FC (Single P) →L[ℝ] FC (Single P) :=
 ((show FC (Single P) →ₗ[ℂ] FC (Single P) from ⟨⟨twist U', map_add (twist U')⟩,fun a b=> twist_scalar U' b a⟩).toContinuousLinearMap).restrictScalars ℝ
omit ho p in
private lemma dye {N:Side}(g:Seat N→ SU.E):MeasurePreserving (gird g) (city _) (city _):=(Wilson.prior_gauge g).prod (threads g)

lemma color_preserve (A:StepData (More N) (More P))(B:A.patch.Branches A.kernel SU.group)(x:A.ratio=ratio G)
    {r:ℝ}{Z':Support (More N)}{u:ℝ}{d:ℕ}{l:Loom N}(K:Roof N u r d l)(c:0<hF)(s:2*hF<firstRadius SU.group)
    (f:Mark N) (z:AtSupport b Z' f) (h:covariant f) (Q:Op SU.Slot)(v:Mind Q)(M:Male)(β:ℝ):
    covariant (pushMark G A j Q M ho t hF β l f) := by
  intro g W
  let X:= scaleG G g; let Y':= pushMark G A j Q M ho t hF β l f; let F:= simultaneous g W; let T:= turnCLM (quantU (tradew P g)); let W'(y:Fields P)(s:Orbit N):= A.density β y.1 s.1 • gathered G j Q M ho t hF f y (drawn l s)
  have ht(y:Fields P):Integrable (W' y) (city N):= Env.integrableX (Env.scale (Env.along (slice_env A β B y.1) measurable_fst) (Env.along (g:=fun x: Orbit N=>(y,drawn l x)) (env_gathered G j Q M ho t hF p c s f z.env) (measurable_const.prodMk (drawn_m l K.bill)))) _
  have he(y:Fields P):Y' y=∫ s,W' y s∂city N:= outright G A j Q M ho t hF β l p K.bill B c s f z.env _
  let a': MeasurableEquiv (Orbit N) (Orbit N) := ⟨⟨gird X,gird X⁻¹,Pyx.gird_inv X,fun y=>by simpa only [inv_inv] using Pyx.gird_inv X⁻¹ y⟩,(dye X).measurable, (dye X⁻¹).measurable⟩
  change Y' F=T (Y' W)
  rw [he,he, ←ContinuousLinearMap.integral_comp_comm _ (ht W),← (show MeasurePreserving a' (city N) (city N) from dye _).integral_comp' (W' F)]
  apply integral_congr_ae; apply Filter.Eventually.of_forall; intro s
  have hz:drawn l (a' s)=simultaneous X (drawn l s):= Prod.ext rfl (K.rev s.1 s.2 X)
  have hu:A.density β F.1 (a' s).1=A.density β W.1 s.1:= by have h:= A.covary B g β W.1 s.1; rw [x] at h; exact h
  unfold W'; dsimp only
  rw [hu,hz]; unfold F X; rw [canvas G g j ho D p hF t W f Q M h z v,map_smul]; rfl
#print axioms color_preserve
end Tint
