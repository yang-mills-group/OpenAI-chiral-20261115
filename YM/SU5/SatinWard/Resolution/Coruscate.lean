import YM.SU5.SatinWard.Resolution.FuelZ
import YM.CF.Buffered.PushMark
import YM.CF.Buffered.Reflection
import YM.CF.Buffered.StepIdentity
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF.Mezzo
open Function Fock NormedSpace SU Lat Lattice Cube Finset MeasureTheory Branch Reflect Window Wilson Rush Peaks Scroll
open Phase Skye Pastry Tulip Dial Paige Vault Fir Tree Girt Spire
open Push.SectorMeasure Scree RG Tree Next.SectorChange Fock Buffered Buffered.Advance Filter
open Reed (Fine think)
open scoped Topology BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {N P:Side}{Q:Op SU.Slot}{M:Male}{g:UNI SU.Slot}(u:Registrar g)(v:twist g Q=Q)
local notation "T"=> Mezzo.singlet N g
abbrev flavorTurn (g:UNI SU.Slot)(N:Side): FC (Single N)≃⋆ₐ[ℝ] FC (Single N):= twist (quantU (Mezzo.singlet N g))
local notation "Fℝ"=> flavorTurn
variable (G:Ratio N P)(h:Odd G.count.val)(j:ℕ)
lemma fieldTick (g:UNI SU.Slot):twist (Mezzo.singlet N g) (cutM (Tset N))=cutM (Tset N):=by rw [←touchP]; exact roseTick ..
lemma singletPrep (g:UNI SU.Slot)(U:UNI SpinIdx)(s:Shape):Commute (prepU s U inert N).val (Mezzo.singlet N g).val:=by
 unfold Commute SemiconjBy; rw [←love_coat]; unfold prepU; dsimp only; rw [←map_mul,←map_mul]; congr 1; change jump _ _ * ((1:Op (Site N))⊗ₖ _)= _ * jump _ _
 rw [←jump_replicate, jump_mul,jump_mul,Equiv.refl_trans,Equiv.trans_refl]; congr 1; ext1 i; change (_ • (U.val⊗ₖ (1:Op SU.Slot))) *((1:Op SpinIdx)⊗ₖ g.val)=((1:Op SpinIdx)⊗ₖ g.val)*(s.payA i • (U.val⊗ₖ (1:Op SU.Slot))); rw [Matrix.smul_mul,Matrix.mul_smul,op_kron_mul,op_kron_mul,one_mul,mul_one,mul_one,one_mul]
section Q
variable {U:UNI (Single N)}
private lemma turn_basis (s:Finset (Single N))(i:Single N)(h:twist U (cutM s)=cutM s)(p:i∈s):withinM s (acts U.val (basisKet i)):=by unfold withinM; rw [← h, ← Fock.swivel, cut_basis,if_pos p]
lemma turn_expense (x:Support (More N))(g:UNI SU.Slot):twist (Mezzo.singlet N g) (cutM (modesIn N x))=cutM (modesIn N x):=by
 apply Mir.twist_comm; ext ⟨i,a⟩ ⟨y,b⟩; unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; change ((1:Op (Site N×SpinIdx)) i y*g.val a b)* _=_*((1:Op (Site N×SpinIdx)) i y*g.val a b); by_cases p:i=y; subst p; simp only [Buffered.modes_at,Matrix.one_apply_eq, one_mul]; ring -- tune
 rw [show (1:Op (Site N × SpinIdx)) i y=0 from Matrix.one_apply_ne p]; simp only [zero_mul,mul_zero]
lemma fieldSale {z:Support (More N)}{F:FC (Single N)}{b:Bool}(q:Fine (Tset N) (modesIn N z) b F)(g:UNI SU.Slot): Fine (Tset N) (modesIn N z) b (Fℝ g N F):=by
 unfold flavorTurn
 induction q with
 | seed i p=>
    by_cases v:i∈Tset N
    · rw [show (think (Tset N)).term i=put i from if_pos v,←create_put,twist_create]; exact fine_create _ (turn_basis _ _ (fieldTick _) v) (turn_basis _ _ (turn_expense z g) p)
    rw [show (think (Tset N)).term i= -takeF i from if_neg v, map_neg,←remove_take,twist_remove]; apply fine_neg; refine fine_remove _ (turn_basis _ _ ?_ (mem_compl.mpr v)) (turn_basis _ _ (turn_expense z _) p); rw [dim_cut,map_sub,map_one,fieldTick]
 | empty=> rw [map_zero]; exact .empty _
 | one=> rw [map_one]; exact .one
 | add _ _ a b=> rw [map_add]; exact a.add b
 | grow _ _ a b=> rw [map_mul]; exact a.grow b
 | scale _ _ a=> rw [twist_scalar]; exact a.scale _
end Q

include u h v
lemma modeSemaphore(x:Nom N P)(w:Ket (Single N))(b:Bool):
 byMode G j Q M x b (acts (Mezzo.singlet N g).val w)=acts (Mezzo.singlet P g).val (byMode G j Q M x b w):=by
 have he: twist (Mezzo.singlet N g) (feeL b N Q)=feeL b N Q:=by cases b <;> simp only [if_true,Bool.false_eq_true, ite_false,feeL,Tap.plankP,breeze_exp,map_neg,roseHead,v] -- sed
 have hx (w:Ket (Single N)): coat (patchQ G) (acts (Mezzo.singlet N g).val w)=acts (ceremony G g).val (coat (patchQ G) w):=by nth_rw 1 2 [←basis_expand w]; simp_rw [map_sum,map_smul,basis_shell]; apply sum_congr rfl; intro i _; rw [ensemble]
 rw [byMode_eq,byMode_eq, route_foot, foot_rose]
 nth_rw 1 [←he]; rw [← Fock.swivel,hx,Fock.swivel (ceremony G g), cloth_stock _ h g u]
lemma slotSub {z:Support (More N)}{f:FC (Single N)}(x:Nom N P){b:Bool}(p:Fine (Tset N) (modesIn N z) b f): subF G j Q M h x (Fℝ g N f)=Fℝ g P (subF G j Q M h x f):=by
 unfold flavorTurn
 induction p with
 | seed i w=>
    by_cases t:i∈ Tset N
    · rw [show (think (Tset N)).term i=put i from if_pos t,←create_put,twist_create,sub_create G j Q M h x (turn_basis _ _ (fieldTick g) t),sub_create G j Q M h x (within_basis _ _ t),modeSemaphore u v G h j,twist_create]
    rw [show (think (Tset N)).term i= -takeF i from if_neg t,map_neg,map_neg,map_neg,map_neg,←remove_take,twist_remove,sub_remove G j Q M h x (turn_basis _ _ (show twist _ _=_ from ?_) (mem_compl.mpr t)), sub_remove G j Q M h x (within_basis _ _ (mem_compl.mpr t)),modeSemaphore u v G h j,twist_remove]
    rw [dim_cut,map_sub,map_one,fieldTick]
 | grow a b p q=> rw [map_mul, Advance.sub_mul G j Q M h x (fieldSale a g) (fieldSale b g),Advance.sub_mul G j Q M h x a b,p,q,map_mul]
 | empty=>simp
 | one=>simp [Advance.sub_one]
 | add _ _ a b=> rw [map_add,map_add,map_add,map_add,a,b]
 | scale _ _ a=>rw [twist_scalar,map_smul,map_smul,twist_scalar,a]

omit u h v
section Reading
-- even op of any mark, for cov
abbrev freshly (g:UNI SU.Slot): Mark N→ₗ[ℝ] Mark N where
 toFun f V:= flavorTurn g N (f V)
 map_smul' c A:= funext fun i=> (map_smul (flavorTurn g N) c (A i):_)
 map_add' x y:= funext fun i=>map_add (flavorTurn g N) (x i) (y i)
lemma frostyOne(g:UNI SU.Slot) : freshly g (1:Mark N)=1:=funext fun i=>map_one (flavorTurn g N)
lemma frostyMul(g:UNI SU.Slot)(f f':Mark N): freshly g (f*f')= freshly g f*freshly g f':=funext fun i=>map_mul (flavorTurn g N) (f i) (f' i)
lemma frosty_grade (g:UNI SU.Slot){b:Bool}{x:Support (More N)}{F:Mark N}(p:AtSupport b x F): AtSupport b x (freshly g F):=
 ⟨Girt.pole_w F (flavorTurn g N) (Fock.breeze _) p.env,fun i j u v=> congrArg (flavorTurn g N) (p.dep i j u v),fun i=>fieldSale (p.allV i) g⟩ -- tune
lemma frostyShadow (g:UNI SU.Slot){b:Bool}{x:Support (More N)}{F:Mark N}(p:AtSupport b x F)(j:Axis)(i:ℤ): freshly g (reflMark j i F)=reflMark j i (freshly g F):=by funext x; exact twist_inter _ _ _ (singletPrep g (Window.pinLift j) (Buffered.plane j i) (N:=N)).symm.eq (p.allV (reflFields j i x)).sector
lemma wordPass (g:UNI SU.Slot){I:Type*}(f:I→Mark N)(i:List I): ((i.map fun j=> freshly g (f j)).prod)=freshly g ((i.map f).prod):=by induction i with| nil=>simp [frostyOne]| cons _ _ ih=> simp only [List.map_cons,List.prod_cons,ih,frostyMul]
lemma scorePass (x:Orbit N→ Phys N)(q:Concert g) (f:Mark N)(l:Loom N)(h:∀ᵐ i∂city N,performance (Mezzo.singlet N) g (x i)=x i): markedRead (freshly g f) l x = markedRead f l x:=by
 unfold markedRead; apply integral_congr_ae; filter_upwards [h] with i y
 change inner ℂ (mateK N) (acts (twist _ _) (x i))=inner ℂ (mateK N) _; nth_rw 1 [←y,←roseMate N q]; unfold performance; rw [← Fock.swivel,act_unit_inner]; rfl -- tune
include u h v
variable (A:RG.StepData (More N) (More P))
-- without bounds.RQ.Step.Scope. no need BQueue since outer funds. based on Roll.
theorem push_frost (l:Loom N)(q:Chi)(d β:ℝ){f:Mark N}{b:Bool}{S:Support (More N)}(p:AtSupport b S f) :
 pushMark G A j Q M h q d β l (freshly g f)= freshly g (pushMark G A j Q M h q d β l f):=by
 funext z; let T':= twist (quantU (Mezzo.singlet P g)); let L: FC (Single P) →L[ℝ] FC (Single P):= T'.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
 have H(y:Fields P)(v:Fields N):gathered G j Q M h q d (freshly g f) y v= L (gathered G j Q M h q d f y v):=by
    unfold gathered avgF; rw [map_smul,map_sum]; apply congrArg; refine sum_congr rfl fun i _=> slotSub u ‹twist g Q=Q› G h j _ (p.allV v)
 have him:AntilipschitzWith 1 L:=Isometry.antilipschitz (Isometry.of_dist_eq fun a b=>by rw [dist_eq_norm,dist_eq_norm,←map_sub]; exact twist_norm ..)
 change pushMark G A j Q M h q d β l (freshly g f) z=L _; unfold pushMark assembled linkLaw; rw [←L.integral_comp_comm' him]; apply integral_congr_ae; filter_upwards with i; rw [map_smul,← L.integral_comp_comm' him]; simp_rw [H] -- tune
end Reading
end YM.CF.Mezzo
