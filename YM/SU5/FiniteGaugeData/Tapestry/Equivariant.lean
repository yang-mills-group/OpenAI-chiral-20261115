import YM.SU5.FiniteGaugeData.Tapestry.Junction
import YM.CF.Levier.Wake
import YM.CF.Pyx.Warp
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Gauge intertwining of the transferred physical insertions

Uses **two** representations on Iota: torch and temper. Warp of cloth
preserves those but they need not coincide on arbitrary offset. At the patch
summit use the true torch law on `scaleG` of upper gauge. Don't use `carR` here.
-/
set_option quotPrecheck false
set_option maxHeartbeats 450000
open Haro Tap Cascade Dial Mir Girt Nacre Pastry
open Reed (Fine think)
open Phase RP

section finite
variable {N P:Side} (G: Ratio N P)(f:Seat P → SU.E)(g: Seat N → SU.E)
local notation "T" => ((Peaks.torch G 1).run f)
local notation "F"=> ((temper G 1).run f)
local notation "ℓ" => Peaks.scaleG G f
local notation "r" => tradew N (Peaks.scaleG G f)

-- `photo` argument in leaps gauge-translated x; AB=BC. adapted Tulip.panel_ticket
private lemma panelsGauge {I: Type*}[Fintype I][DecidableEq I](A B:I→ Op SU.Slot)(i j:I) (x y:Op SU.Slot)(e:y*B j=A i*x):
    Tulip.panel i j y * jump (Equiv.refl _) B = jump (Equiv.refl _) A * Tulip.panel i j x:=by
  ext ⟨a,k⟩ ⟨b,l⟩; simp only [Matrix.mul_apply,Fintype.sum_prod_type,jump_apply,Equiv.refl_apply,Tulip.panel,Matrix.of_apply]; by_cases w:a=i <;> by_cases q:b=j
  · subst a b; simp only [true_and,and_true,and_self,mul_ite,ite_mul]; simp; have h:= Matrix.ext_iff.mpr e k l; simpa [Matrix.mul_apply,SU.Slot,Fintype.sum_prod_type] using h
  all_goals simp [w,q,ite_mul,mul_ite]
-- for polynomial of any supported length, even if some values outside the regions `canUse` buys
variable (j:ℕ){R:ℕ}(p: LaurentRadius j G.count R) (ho:Odd G.count.val) (M:Male)
include ho
private lemma dragEquivariant (a b: St G.count)(z:Cover)(c:ℂ)(o:Lattice.Order)(x:Nom N P):
 drag G true false a b z c o (unionP (july G f x))*(T).val=(F).val*drag G true false a b z c o (unionP x):=by
  unfold drag; rw [sum_mul,mul_sum]; apply sum_congr rfl; intro i _
  change _ * ((Peaks.parcel G false 1).run f).val=((Peaks.parcel G true 1).run f).val * _; rw [Peaks.warrant,Peaks.warrant]; apply panelsGauge
  unfold unionP july; simp only [track_pr]; rw [travel_gauge,worn G true false ho]; let c':= Rush.wind i z*c
  -- unitary endpoint
  rw [show (Tulip.brand _).1=(matter _).val from rfl,map_mul,map_inv,map_mul]
  let m:= matter (f (Peaks.touch G true (i,a))); let s:= matter (f (Peaks.touch G false (i+wrap N z,b)))
  change c' • (m.val * _ * star s.val)* s.val= m.val * (c' • _)
  rw [Matrix.smul_mul, Matrix.mul_smul, mul_assoc _ _ s.val, s.property.1, mul_one]; rfl

include p
private lemma paintMosaic(x:Nom N P):
  Peaks.mosaic G true false (tub (brix j G.count)) (unionP (july G f x))*(T).val=(F).val * Peaks.mosaic G true false (tub (brix j G.count)) (unionP x):=by
  unfold Peaks.mosaic; simp_rw [douse_sum G j p, Matrix.smul_mul, Matrix.mul_smul, Finset.mul_sum, sum_mul];
  apply congrArg (fun (z: Op (Iota G)) => (Fintype.card Lattice.Order : ℝ)⁻¹ • z); exact sum_congr rfl fun i _=> sum_congr rfl fun a _=> sum_congr rfl fun b _=> sum_congr rfl fun t _=> dragEquivariant G f ho a b t _ i x
omit p ho
private lemma lobeComm (p b:Bool)(f:Seat P→ SU.E):
  lobe G b*((Peaks.parcel G p 1).run f).val=((Peaks.parcel G p 1).run f).val*lobe G b:=by
  rw [lobe_diag,warrant]; ext ⟨y,a⟩ ⟨z,c⟩; rw [Matrix.diagonal_mul,Matrix.mul_diagonal]; by_cases h:y=z <;> simp [lobe_fine,jump_apply,h,mul_comm]
include p ho
lemma loomPatchGauge (x:Nom N P): Peaks.cloth j M G (unionP (july G f x))*(T).val=(F).val* Peaks.cloth j M G (unionP x):=by
  let A:= mosaic G true false (tub (brix j G.count)) (unionP (july G f x)); let B:= mosaic G true false (tub (brix j G.count)) (unionP x)
  have he: A*(T).val=(F).val*B:= paintMosaic G f j p ho x
  have ht (b:Bool): (lobe G b*A*lobe G b)*(T).val=(F).val*(lobe G b*B*lobe G b):=by
    rw [mul_assoc,show _ * (T).val=(T).val*lobe G b from lobeComm G false b f,← mul_assoc, mul_assoc (lobe G b) A (T).val, he, ←mul_assoc (lobe G b) (F).val B,show _ * (F).val=(F).val*lobe G b from lobeComm G true b f]; simp only [mul_assoc]
  unfold Peaks.cloth; rw [add_mul,mul_add]; exact congrArg₂ (· + ·) (ht true) (ht false)

omit ho p
local notation "φ"=> patchQ G
private lemma plateauAct (v:Ket (Single N)): acts (T).val (coat φ v)=coat φ (acts (r).val v) := by
  let U:=crest_pose G f 1; have hx: endorse G 1*(T).val=(T).val*endorse G 1 := U.1.trans U.2.symm
  have hw : summit φ (T).val=(r).val:=Matrix.ext fun i z=> Levier.tag_r G 1 f i z
  calc
    _ = acts (cutM (lows φ)) (acts (T).val (coat φ v)) := by rw [←act_mul,←level,edgeDesk,hx,act_mul,←edgeDesk,level,coat_ret]
    _ = _ := by rw [←stance,←summit_rule,hw]

variable (Q:Haro.SpaceM)
lemma localPlank : Commute (tradew N g).val (plankP N Q.val):=by
  let W:=(love N).symm; unfold Commute SemiconjBy; apply W.injective
  change W ((_ : Op _) * _) = W ((_ : Op _) * _); rw [map_mul,map_mul]; unfold W plankP headW; rw [Cascade.twine,StarAlgEquiv.symm_apply_apply,jump_mul,jump_mul]; congr 1; funext x
  simp only [Equiv.refl_apply,op_kron_mul,one_mul,mul_one]; rw [(show Tap.Mind Q.val from Q.property).firm]
lemma localFee (b:Bool): Commute (tradew N g).val (Advance.feeL b N Q.val):=by
  letI : NormedAlgebra ℚ (Op (Single N)):= NormedAlgebra.restrictScalars ℚ ℂ _
  cases b; exact (localPlank g Q).neg_right.exp_right; exact (localPlank g Q).exp_right
include ho p
lemma modeGauge (x: Nom N P)(b:Bool)(v: Ket (Single N)):
    acts (tradew P f).val (byMode G j Q.val M x b v)= byMode G j Q.val M (july G f x) b (acts (tradew N ℓ).val v):=by
  rw [byMode_eq,byMode_eq, route_foot]; let C:=Peaks.cloth j M G
  rw [show foot G (tradew P f).val=(F).val from rfl, ←act_mul, ←loomPatchGauge G f j p ho M,act_mul,plateauAct G f, ←act_mul,(localFee ℓ Q b).eq,act_mul]

omit p ho
lemma keepMode {s: Finset (Single N)}(e:twist (tradew N g) (cutM s)= cutM s){x : Ket (Single N)}(h:withinM s x): withinM s (acts (tradew N g).val x):=by
  unfold withinM; nth_rw 1 [←e]; rw [←Fock.swivel,h]
lemma tradedFine {v: FC (Single N)}{b:Bool}{s:Finset (Single N)}(p:Fine (Tset N) s b v) : Fine (Tset N) univ b (twist (quantU (tradew N g)) v):=by
  have he := Cascade.tick_g (n:=N) g; rw [touchP] at he
  have hk: twist (tradew N g) (cutM (Tset N)ᶜ)= cutM (Tset N)ᶜ:=by rw [dim_cut,map_sub,map_one,he]
  induction p with
  | seed i p=>by_cases t:i∈ Tset N
              · rw [show (think _).term i=put i from if_pos t,←create_put,twist_create]; exact fine_create _ (keepMode g he (within_basis _ _ t)) (within_univ _)
              rw [show (think _).term i= -takeF i from if_neg t,map_neg,← remove_take,twist_remove]; exact fine_neg (fine_remove _ (keepMode g hk (within_basis _ _ (mem_compl.mpr t))) (within_univ _))
  | empty=> rw [map_zero]; exact .empty _
  | one=> rw [map_one]; exact .one
  | add _ _ h k=> rw [map_add]; exact h.add k
  | grow _ _ h k=> rw [map_mul]; exact h.grow k
  | scale _ _ h=>rw [twist_scalar]; exact h.scale _
include p ho
lemma subGauge (x:Nom N P){v:FC (Single N)} {b:Bool} {s:Finset (Single N)}(u: Fine (Tset N) s b v):
    subF G j Q.val M ho (july G f x) (twist (quantU (tradew N ℓ)) v)=twist (quantU (tradew P f)) (subF G j Q.val M ho x v):=by
  have he:= Cascade.tick_g (n:=N) ℓ; rw [touchP] at he
  have hk: twist (tradew N ℓ) (cutM (Tset N)ᶜ)= cutM (Tset N)ᶜ:=by rw [dim_cut,map_sub,map_one,he]
  induction u with
  | seed i u=>by_cases t:i∈ Tset N
              · rw [show (think _).term i=put i from if_pos t,←create_put,twist_create]; have hb:= within_basis _ _ t; rw [sub_create G j Q.val M ho _ (keepMode ℓ he hb),sub_create G j Q.val M ho _ hb, twist_create, modeGauge G f j p ho M Q]
              rw [show (think _).term i= -takeF i from if_neg t, map_neg,map_neg,map_neg,map_neg,← remove_take,twist_remove]; have hb:= within_basis _ _ (mem_compl.mpr t); rw [sub_remove G j Q.val M ho _ (keepMode ℓ hk hb),sub_remove G j Q.val M ho _ hb, twist_remove,modeGauge G f j p ho M Q]
  | empty=> rw [map_zero,map_zero,map_zero,map_zero]
  | one=> rw [map_one, sub_one,sub_one,map_one]
  | add _ _ h k=> rw [map_add,map_add,map_add,map_add,h,k]
  | grow t u h k=> rw [map_mul, sub_mul G _ _ _ _ _ (tradedFine ℓ t) (tradedFine ℓ u), sub_mul G _ _ _ _ _ t u, map_mul,h,k]
  | scale _ _ h=>rw [twist_scalar,map_smul,map_smul,twist_scalar,h]
end finite
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.subGauge
