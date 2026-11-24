import YM.SU5.FiniteGaugeData.Brique.Etude
import YM.SU5.FiniteGaugeData.Hierarchy.Rouge
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.Brique
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric Laurent Bloch Next.Free
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Spire Tenant Fock Fock.Brique Tulip Dial Fir Buffered Skye Scree Nacre
open Paige Vault Cascade
attribute [local instance] opCStarAlgebra
variable {N L B:Side} {σ : Window.Family} {S:Finset (Site N)} {R T U : Support (More N)} {t:List (Site N)} {k n j:ℕ} {a b c e f r:ℝ}
local notation "Μ" => Single N
section
variable (g h:Seat N→SU.E)
abbrev globalH (N:Side) (a:SU.E):Seat N→ SU.E:= fun _=>a
lemma prop_global (x y:SU.E) : globalH N (x*y) = globalH N x*globalH N y:= rfl
lemma prop_global_i (x:SU.E):globalH N x⁻¹=(globalH N x)⁻¹:= rfl
lemma prop_global_one(N:Side):globalH N 1=1:=rfl
lemma Mono_tradew : tradew N g⁻¹=star (tradew N g):=by
 apply mul_left_cancel (a:=tradew N g); rw [Hive.trade_c, mul_inv_cancel,Hive.trade_p]; apply Subtype.ext; exact ((tradew N g).property.2).symm
lemma shifter (S:Support (More N)): twist (tradew N g) (cutM (modesIn N S))=cutM (modesIn N S):=by
 let A:=tradew N g; apply Mir.twist_comm
 ext i j; let p:=A.val i j; rw [cutM,Matrix.mul_diagonal,Matrix.diagonal_mul]; by_cases z:i.1=j.1
 · simp only [modes_at,z]; by_cases w:node j.1.1∈ S <;> simp [w]
 simp [modes_at,tradew,jump_apply,z]
lemma within_tint {S:Finset Μ}(t:twist (tradew N g) (cutM S)=cutM S) (p:Ket Μ)(e: withinM S p) : withinM S (acts (shadeP g) p):=by unfold withinM; nth_rw 1 [←t]; rw [← Fock.swivel, e] -- notation m forced
lemma windFine {b:Bool}{A:FC (Single N)}(p:Reed.Fine (Tset N) (modesIn N T) b A): Reed.Fine (Tset N) (modesIn N T) b (flipsP g A) := by
 let U:= tradew N g; have hU:twist U (cutM (Tset N))=(cutM (Tset N)):=touchP _ ▸ Cascade.tick_g g
 induction p with
 | seed i p=> by_cases h:i∈ Tset N
              · rw [show (Reed.think (Tset N)).term i=put i from if_pos h,←create_put,flipsP,twist_create]; exact fine_create _ (within_tint g hU _ (within_basis _ i h)) (within_tint g (shifter g T) _ (within_basis _ i p))
              rw [show (Reed.think (Tset N)).term i= -takeF i from if_neg h,map_neg,←remove_take,flipsP, twist_remove]; exact fine_neg (fine_remove _ (within_tint g (show twist U (cutM (Tset N)ᶜ)=_ from (by rw [dim_cut,map_sub, map_one,hU])) _ (within_basis _ i (mem_compl.mpr h))) (within_tint g (shifter g T) _ (within_basis _ i p)))
 | empty=>rw [map_zero]; exact .empty _
 | one=>rw [flips_one]; exact .one
 | add _ _ a b=>rw [map_add]; exact a.add b
 | grow _ _ a b=>rw [map_mul]; exact a.grow b
 | scale _ _ a=>rw [flipsP,twist_scalar]; exact a.scale _
lemma flips_identity (A:FC (Single N)) : flipsP (1 : Seat N→SU.E) A=A := by rw [flipsP,Hive.trade_p, show quantU 1=(1:UNI (Finset (Single N))) from Subtype.ext quant_one]; exact one_des _
lemma wind_join (A:FC (Single N)): flipsP (g*h) A= flipsP g (flipsP h A) :=by
 have hp : quantU (tradew N (g*h))=quantU (tradew N g)*quantU (tradew N h):=by rw [←Hive.trade_c h g]; apply Subtype.ext; exact quant_mul ..
 simp only [flipsP,hp,Fock.twin]
lemma zone_t (S:Support (More N)) (p:Set.EqOn g h S) (i:Single N)(z:i∈modesIn N S): acts (shadeP h) (basisKet i) = acts (shadeP g) (basisKet i):=by
 apply PiLp.ext; intro j; rw [basis_act,basis_act]; by_cases w:j.1=i.1 <;> simp only [shadeP,tradew,jump_apply,Equiv.refl_apply,w, ↓reduceIte]; rw [p ((modes_at ..).1 z)]
lemma flips_s (S:Support (More N))(p:Set.EqOn g h S){b:Bool}{A:FC (Single N)}(q:Sector (modesIn N S) b A): flipsP h A=flipsP g A:= by
 induction q with | zero =>rw [map_zero,map_zero] | one=>rw [flips_one,flips_one]| up i z=>rw [←create_put,flipsP,flipsP,twist_create,twist_create]; exact congrArg create (zone_t g h S p i z) | down i z=> rw [←remove_take,flipsP,flipsP,twist_remove,twist_remove]; exact congrArg Fock.remove (zone_t g h S p i z)| add _ _ a b=>rw [map_add,map_add,a,b] | mul _ _ a b=> rw [map_mul,map_mul,a,b] | scale _ _ a=>exact (twist_scalar ..).trans ((congrArg _ a).trans (twist_scalar ..).symm)
lemma shade_cont (N : Side): Continuous (shadeP (N:=N)):=by apply continuous_matrix; intro i j; unfold shadeP tradew; simp_rw [jump_apply,Equiv.refl_apply]; split; exact (SU.matter_cont.comp (continuous_apply (i:=node i.1.1))).matrix_elem _ _; exact continuous_const
lemma flips_cont (A:FC (Single N)) : Continuous (fun g:Seat N→SU.E=> flipsP g A) := by simp_rw [flipsP, twist_formula, quantU]; have hx:= quant_cont.comp (shade_cont N); exact (hx.mul continuous_const).mul hx.star
end
-- Passport on T (matrix seed & smear region); all gauge operations see THIS field. T⊆R purchased in Stump. Extra masks see R. 
structure Corset (T R: Support (More N))(o:Seat N) where
 g:Pane N→Seat N→ SU.E
 up_cont: Continuous g
 locale (i:Seat N)(q:i∈T): Lattice.LocalOn R (fun x=>g x i)
 law (h:Seat N→ SU.E)(x:Pane N): g (gauge h x)= globalH N (h o) * (g x) * h⁻¹
structure Stump (T:Support (More N))(W:Pane N→ℂ):Prop where
 cont : Continuous W
 zone : Lattice.LocalOn T W
 unitB: ∀ x:Pane N, ‖W x‖ ≤ 1
 vision : GaugeInvariant W
variable {W:Pane N→ℂ}{o:Seat N}
variable (F:Corset T R o)
def cargo (Z:Pane N→ℂ)(A:FC (Single N)) : Mark N:=fun x=> Z x.1 • flipsP (F.g x.1)⁻¹ A
local notation "V" => cargo F W
structure Free (T:Support (More N))(A:Mark N):Prop where
 cont : Continuous A
 zone : AtSupport false T A
 fixed (x y:Pane N): A (x,y)=A (x,x)
variable (u:Stump R W)
include u
lemma cargo_bound (A:FC (Single N))(x:Fields N): ‖cargo F W A x‖ ≤ ‖A‖:=by rw [cargo,norm_smul, flipsP,twist_norm]; exact mul_le_of_le_one_left (norm_nonneg _) (u.unitB _)
lemma delivered (h:T⊆R) {A:FC (Single N)}(p:Reed.Fine (Tset N) (modesIn N T) false A) : Free R (cargo F W A) :=by
 let M:= N; let f:= V A; have hx:Continuous f:= (u.cont.comp continuous_fst).smul ((flips_cont A).comp ((F.up_cont.comp continuous_fst).inv))
 refine ⟨hx,⟨⟨hx.measurable,‖A‖,cargo_bound F u A⟩,fun x y ht e=>?_,fun i=> (homes_cash T R (windFine _ p) h).scale _⟩,fun _ _=> rfl⟩; unfold cargo; rw [u.zone _ _ ht]; refine congrArg (fun v: FC (Single N)=> W y.1 • v) (flips_s _ _ _ (fun i hi=>by rw [Pi.inv_apply,Pi.inv_apply]; exact congrArg Inv.inv ((F.locale i hi) _ _ ht).symm) p.sector) -- order orientation p:p from g to h, `=` rewrite u zone. collisions Free constructor invocation
-- global gauge invariance for any EMPTY A (base before field) buys actual local provenance. No gauge slicing at final.
lemma cargos (A: FC (Single N))(H:∀ h:SU.E,flipsP (globalH N h) A=A):Buffered.covariant (cargo F W A):=by
 intro g x; unfold cargo; let y:= x.1; let U:= globalH N (g o); change W (gauge g y) • flipsP (F.g (gauge g y))⁻¹ A= flipsP g _; rw [F.law,u.vision]; rw [show (U* F.g y*g⁻¹)⁻¹=g*((F.g y)⁻¹*U⁻¹) by group]; rw [wind_join,wind_join,show U⁻¹= _ from (prop_global_i (N:=N) (g o)).symm,H]; rw [flipsP, twist_scalar] -- tactic hg
end YM.CF.Window.Brique
