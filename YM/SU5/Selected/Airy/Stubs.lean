import YM.SU5.Selected.Airy.Color
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
variable {d q:Type*}[Fintype d][DecidableEq d][Fintype q][DecidableEq q]
lemma coast_approx (F: Coast→ WRect d q)(Q:d→q→ Cover→Prop)(h:∀ i j, Plasma (Q i j) (fun x=> F x i j)) (ε:ℝ)(p:0<ε) : ∃ G:Coast→WRect d q, (∀ i j, Color (Q i j) (fun x=> G x i j)) ∧ ∀ x, ‖F x-G x‖ ≤ ε:=by
 let K (_:d)(_:q):=(1:ℝ); obtain ⟨v,z⟩:= settlem K (fun i j=>zero_le_one); let e:= ε / stakesize K; have ht:0<e:= by unfold e; positivity
 choose G g u using fun i j=> h i j e ht; refine ⟨fun x=> Matrix.of fun i j=> G i j x, g, fun x=>?_⟩; refine (z _ e ht.le (fun i j=>?_)).trans (le_of_eq (mul_div_cancel₀ _ v.ne')) -- name
 exact (u i j x).trans_eq (one_mul _ |>.symm)
-- signs as per mon. witnesses move separately. approxim ferr.
variable (n p:ℕ)(G:Side)(g:8≤G.val)(e:n≥4)
def Qlate (a:SpinIdx)(v:Fin p)(k: Cover): Prop := a=2∧ k 3= -strikeL n p v
def Qearly (a:SpinIdx)(_:Fin p)(k:Cover):Prop := a∈plusHalf→ ∃ i:Fin p,k 3= -strikeE p i
local notation "V"=> plinth G n p e
local notation "Y"=> artisans G n p e
local notation "Fp"=>children G n p
include g
lemma late_plasma (a:SpinIdx)(v:Fin p): Plasma (Qlate n p a v) (fun x=> Fp x a v):=by
 by_cases t: a=2
 · subst a; let f(w:Torch):ℂ:= soap G w; unfold children nails forge; simp_rw [Matrix.smul_apply,Matrix.of_apply,if_true,smul_eq_mul]; conv in (_*_)=> rw [mul_comm] -- tune occurrence
   exact (Plaza f (Complex.continuous_ofReal.comp (soap_c G g)) _).mono (fun k z => ⟨rfl,z⟩)
 unfold children nails forge; simp only [Matrix.smul_apply,Matrix.of_apply,if_neg (Ne.symm t),smul_zero]; exact Plasma.zero
lemma before_plasma (a:SpinIdx)(x:Fin p): Plasma (Qearly p a x) (fun w:Coast=> artisans G n p e w a x):=by
 by_cases t:a∈plusHalf; swap; · exact (fromStone ((signal G n p e g).2.2.matrix_elem a x)).mono (fun i _ h=> (t h).elim) -- tune
 have he(w:Coast):Y w a x=V w a x:=by
    let M:=Y w; calc
                   _ = ((Fock.cutM plusHalf)*M) a x:= by rw [cutM, Matrix.diagonal_mul,if_pos t,one_mul]
                   _ = _ :=by rw [show cutM plusHalf=Aop from Lat.raising.trans Adef.symm]; unfold M; rw [artisan_plus]
 simp_rw [he,plinth,Matrix.smul_apply,Matrix.mul_apply,smul_eq_mul,staves,forge,Matrix.of_apply]; by_cases t':a=0; swap; · simp only [if_neg (Ne.symm t'), zero_mul,sum_const_zero,mul_zero]; exact Plasma.zero
 subst a; simp_rw [if_true,mul_sum,mul_left_comm (↑(soap G _) :ℂ)]; apply Plasma.sum; intro i _; apply (Plaza (fun w:Torch=> ↑(soap G w)*screens n p e w i x) ((Complex.continuous_ofReal.comp (soap_c G g)).mul ((screens_price n p e).matrix_elem i x)) _).mono; intro s p' _; exact ⟨i,p'⟩
lemma stubs(ε:ℝ)(k:0<ε) : ∃ (x y:Coast→Wq p)(w:ℕ),(∀ i j,Color (fun v=> Piece v w∧ Qlate n p i j v) (fun t=> x t i j)) ∧ (∀ i j,Color (fun v=> Piece v w∧ Qearly p i j v) (fun t=> y t i j)) ∧∀ z, ‖Fp z-x z‖ ≤ ε ∧ ‖Y z-y z‖ ≤ ε:=by
 obtain ⟨x,X,z⟩:= coast_approx _ _ (late_plasma n p G g) ε k
 obtain ⟨y,A,b⟩:= coast_approx _ _ (before_plasma n p G g e) ε k
 obtain ⟨w,c,d⟩:= ((eventually_all.mpr fun i=> eventually_all.mpr fun j=> hedge (X i j)).and (eventually_all.mpr fun i=> eventually_all.mpr fun j=> hedge (A i j))).exists
 exact ⟨x,y,w,c,d,fun p=>⟨z p,b p⟩⟩
omit g
variable {N:Side}
lemma flight_eq (k x:Site N)(v:Cover): Fourier N x k * prefixG v (brim N k) = wind x v * Fourier N (x+wrap N v) k:=by
 unfold Fourier; simp_rw [Matrix.of_apply, ← paddles,← mul_div_assoc, freq_advance]; ring -- hmm use simpler
private def pig (f:Coast→ℂ)(x y:Site N):= ∑ i:Site N, Fourier N x i * f (brim N i) * star (Fourier N y i)
lemma fareFee (k:Cover)(x y:Site N)(p:x+wrap N k≠y) : pig (prefixG k) x y=0:=by
 unfold pig; simp_rw [flight_eq,mul_assoc,←mul_sum]; rw [show (∑ i:Site N, _)=(Fourier N * star (Fourier N)) (x+wrap N k) y from ?_, (fourier_mem N).2,Matrix.one_apply_ne p,mul_zero]; rfl
lemma wageP {Q:Cover→Prop}{f:Coast→ℂ}(h:Color Q f)(x y:Site N)(e:∀ k,Q k→ x+wrap N k≠y) : pig f x y=0:=by
 induction h with
 | zero=>simp [pig]
 | mode v p=> exact fareFee _ _ _ (e _ p)
 | @smul t f h v=> rw [show pig (t•f) x y=t*pig f x y from ?_,v,mul_zero]; unfold pig; rw [mul_sum]; apply sum_congr rfl; intro b _; simp only [Pi.smul_apply,smul_eq_mul]; ring
 | @add f g h q u v=> rw [show pig (f+g) x y= pig f x y+pig g x y by unfold pig; simp [sum_add_distrib,mul_add,add_mul],u,v,zero_add]
lemma leaves {F:Coast→WRect d q}{Q : Cover→Prop}(x y: Site N)(i:d)(j:q)(h:Color Q (fun t=> F t i j))(g: freeze (F∘ brim N) (x,i) (y,j)≠ 0): ∃ z:Cover,Q z∧ x=y-wrap N z:=by
 rw [freeze_charge] at g; by_contra! k; exact g (wageP h x y (fun v z => (fun u=> k v z (eq_sub_of_add_eq u))))
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms stubs
#print axioms leaves
