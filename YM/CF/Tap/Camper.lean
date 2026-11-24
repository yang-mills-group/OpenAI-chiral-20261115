import YM.CF.Tap.Pallet
import YM.CF.Font.Rise
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N F: Side}(G:Ratio N F)(h:Odd G.count.val)(T:Script Male)(j:ℕ)(e:Use j G.count @T)(p:Even j)(u:Bool)(M:Male)
def merry(D:List Axis): Op (Iota G):= grapple D M G 1 * (pine j G.count h @T u M G 1*hood G)
def fan(D:List Axis):=arch G (merry G h T j u M D)
omit G h T M e
include p
set_option maxHeartbeats 500000 in
lemma ferry(D:List Axis)(hx:D.length+2≤j):∃ a C:ℝ,0<a∧0<C ∧∀ {c f:Side}(G:Ratio c f)(w:Odd G.count.val)(T:Script Male),Use j G.count @T → ∀ M:Male,∀ x:Single f, ∑ r,bolt a G x r *‖fan G w T j u M D x r‖≤ C*followV D G.count:=by
 let I:=Σ x:Male×Male,Site x.1.val
 obtain ⟨a,C,v,k,H⟩:=pricelet u j (fun i:I=>i.1.1.val) (fun i=>i.1.2.val) (fun i=>i.1.1.property) (fun i=>i.1.2.property) (fun i=> i.2) D hx
 let b:=Real.exp (2*a); let A:= (Fintype.card SpinIdx:ℝ)*(↑(Fintype.card Slot:ℕ)*b*C)
 refine ⟨a/2,A,by positivity,by unfold A b; positivity,fun {c f} G w T e M x=>?_⟩
 let K:=tub (coverlet u j G.count M.val D); have he:merry G w T j u M D= Rush.cart c K ⊗ₖ (1:Op Slot):=by rw [merry,sticks j G.count w p (by omega) T e G rfl M]; exact pine_stencil j G.count w p (by omega) T e G rfl M u D hx
 let X:=fan G w T j u M D; let P:=Rush.cart c K
 obtain ⟨⟨⟨n,r,i⟩,x'⟩,rfl⟩:= (switchG G).surjective x
 let z:=switchG G ((n,(r,i)),x'); let V:= followV D G.count; let Y (l d):=∑ m: Site c, bolt (a/2) G z ((m,l),d)*‖X z ((m,l),d)‖
 have ht(l d): Y l d≤ b*(C*V):=by
    have hz:Width a (C*V) fun x=> K x (r,i) (0,l):= H (⟨(⟨_,w⟩,M),r⟩:I) i l
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (plate_e (c:=c) v hz n) ((Real.exp_pos _).le))
    unfold Y; rw [mul_sum]; refine sum_le_sum (fun m _=>?_) -- tune width binder
    rw [show X z ((m,l),d)= P (n,r,i) (m,0,l)*(1:Op Slot) x' d from (by unfold X z fan arch; rw [he]; simp only [Matrix.of_apply,Equiv.symm_apply_apply]; rfl), ←mul_assoc b]
    apply mul_le_mul _ _ (norm_nonneg _) (by unfold b Faro; positivity); swap; rw [norm_mul, Matrix.one_apply]; split <;>simp [P]
    unfold bolt b Faro; rw [← Real.exp_add]; apply Real.exp_monotone; have hp:(dish G z ((m,l),d):ℝ)≤ 2*(separation n m)+4:=by exact_mod_cast dish_le G w n m i l _ _ _
    linarith [mul_le_mul_of_nonneg_left hp v.le]
 change ∑ j:Single c,bolt _ G z j* ‖X z j‖ ≤ _; rw [show (∑ j:Single c,bolt _ G z j* ‖X z j‖) =∑ k:SpinIdx,∑ t,Y k t from ?_]; swap
 · unfold Single Y; rw [Fintype.sum_prod_type, Fintype.sum_prod_type,sum_comm]; refine sum_congr rfl (fun l _=>?_); rw [sum_comm]
 refine (sum_le_sum (fun l _=>sum_le_sum (fun k _=> ht l k))).trans ?_; simp only [sum_const, card_univ, nsmul_eq_mul]; unfold A V; exact le_of_eq (by ring)
include h G M T e
private lemma archP (P: Op (Single F))(Y:Op (Iota G)): arch G (foot G P*Y)= P * arch G Y:=by
 ext i j; change (foot G P * Y) _ _=_; rw [Matrix.mul_apply,Matrix.mul_apply,←Equiv.sum_comp (switchG G)]; apply sum_congr rfl; intro m _; unfold arch; rw [Matrix.of_apply,Equiv.symm_apply_apply]; rw [foot]; simp only [Matrix.submatrix_apply,Equiv.apply_symm_apply]
private lemma sumHop (i:Axis)(P:Matrix (Single F) (Single N) ℂ)(x:Site F)(a: SpinIdx)(b:SU.Slot)(y:Single N): ((Rush.echo (F:=F) i⊗ₖ(1:Op Slot))* P) ((x,a),b) y= seam (anticut F) x i * P ((x+step i,a),b) y:=by
 unfold Rush.echo; rw [Matrix.mul_apply]; rw [Finset.sum_eq_single ((x+step i,a),b)]
 · simp [jump_apply,Lat.advance]
 rintro ⟨⟨k,c⟩,d⟩ _ hx; by_cases h:k=x+step i <;> by_cases v:a=c <;> by_cases p:b=d<;> simp_all [jump_apply,Lat.advance,Matrix.one_apply,Ne.symm]
 simp
lemma fans (H:2≤j)(D:List Axis)(i:Axis)(x:Site F)(a b y): fan G h T j u M (i::D) ((x,a),b) y= seam (anticut F) x i * fan G h T j u M D ((x+step i,a),b) y - fan G h T j u M D ((x,a),b) y:=by
 let Y:=merry G h T j u M D; unfold fan; rw [show merry G h T j u M (i::D)=(foot G (trackM i 1)-1)*Y from ?_]; swap; · unfold Y merry; rw [grapple, List.map_cons,List.prod_cons,mul_assoc]; rfl
 rw [show foot G _-1=foot G (trackM i 1-1) from ?_,archP G h T j e p M,track_still j G.count h p (by omega) T e G rfl M,Matrix.sub_mul,Matrix.one_mul,Matrix.sub_apply,sumHop G h T j e p M]
 rw [foot_sub,foot_one]
lemma fan_s (x y): fan G h T j u M [] x y= arch G (pine j G.count h @T u M G 1) x y:=by unfold fan; rw [merry, grapple,List.map_nil,List.prod_nil,one_mul,visitsH] -- overrides
end YM.CF.Tap
