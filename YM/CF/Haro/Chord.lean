import YM.CF.Haro.Fold
import YM.CF.Levier.CrestD
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(j m:ℕ)(e:Even j)(h:2 ≤ j)
variable {ι:Type*}(S:ι→Male)(K:WG ι)(p:∀ i n,K i n 1=0)(i:ι)(G:Ratio c f)(ho:Odd G.count.val)
private lemma arch_p(A:Op (Single f))(F:Op (Iota G)): arch G (foot G A*F) = A*arch G F:=by ext i j; change (foot G A * F) _ _=_; rw [Matrix.mul_apply,Matrix.mul_apply,←Equiv.sum_comp (switchG G)]; apply sum_congr rfl; intro m _; unfold arch; rw [Matrix.of_apply, Equiv.symm_apply_apply]; rw [foot]; simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
include e h p
variable {t:ℝ}(Y: cro G t)(W: Meter TailB G t)(V: Meter Grave G t)
lemma hue (v:∀ b, Along j G.count ho (Thread j) b (S i) G 1)(s:Y.val=1)(z: fulfills G ho t (j:=j) S K i W V Y)(b:Bool) : let P:= skewE j (S i) (!b) f 1; arch G (∑ X,W (true,b) X Y) = P* fan G ho (Thread j) j (!b) (S i) []:=by
 intro P; -- tune
 let F:=P * fan G ho (Thread j) j (!b) (S i) []
 rw [z.1, mineB, s]; unfold Ash; dsimp only [Prod.fst_one, Prod.snd_one]; rw [glass _ ho j K p S i G _ (v true)]; unfold liftD; rw [grapple,List.map_nil,List.prod_nil,one_mul,mab G.count ho j e (by omega) _ p S (!b) G i v]
 have hp : IsStarProjection P:= footrest j (!b) (S i) (by omega)
 rw [show smoke G j S i (!b) true 1=foot G P from ?_, arch_p]; swap
 · rw [show (1:Coil c f × Chin f)=(1,profile (1: Bkg (More f))) from ?_,smoke_r, ←foot_s]; -- tune Chin namespace
   unfold cope; rw [profile_trivial,if_pos rfl]; exact congrArg _ hp.isSelfAdjoint.star_eq
   exact Prod.ext rfl profile_trivial.symm
 congr 1 -- fan; tune
 unfold fan merry grapple; rw [List.map_nil,List.prod_nil,one_mul]
-- sum EXACT price pre-L for actual ink opened terms
abbrev openQ(x:Support (More f))(b:Bool):Matrix (Single f) (Single c) ℂ:= arch G (W (true,b) x Y) -- tune
abbrev pulled(I:Op (Single f))(J: Finset (Support (More f))):Op (Single c):= ∑ x∈J,∑ y∈J,(openQ G Y W x true)ᴴ * I * openQ G Y W y false
lemma chord(I:Cover→ Pal)(v:∀ b, Along j G.count ho (Thread j) b (S i) G 1)(s:Y.val=1)(z: fulfills G ho t (j:=j) S K i W V Y): let P:=funde j (S i) f 1; pulled G Y W (love f (cart f I)) univ= (fan G ho (Thread j) j false (S i) [])ᴴ*(1-P)*love f (cart f I)*P*fan G ho (Thread j) j true (S i) []:=by
 intro P; let A:=1-P; let F:=love f (cart f I)
 have hp:IsStarProjection P:=footrest j true (S i) (by omega)
 have hr(b): (∑ x: Support (More f), openQ G Y W x b)= skewE j (S i) (!b) f 1* fan G ho (Thread j) j (!b) (S i) []:=by rw [← hue j e h S K p i G ho Y W V v s z b]; ext x y; simp only [openQ,arch,Matrix.of_apply,Matrix.sum_apply]
 unfold pulled; simp_rw [←Matrix.mul_sum]; rw [←Matrix.sum_mul,←Matrix.sum_mul,←Matrix.conjTranspose_sum]; rw [hr,hr]; change (A*_ )ᴴ * F * (P*_) = _ᴴ * A*F*P*_ -- tune
 rw [Matrix.conjTranspose_mul, show Aᴴ=A from hp.one_sub.isSelfAdjoint.star_eq,← Matrix.mul_assoc]; rfl
omit ho p S K i
include h e
lemma thin (p:4 ≤ j)(v:2 ≤ m):∃ C:ℝ,0<C∧∀{c f:Side}{ι:Type*}(S:ι→Male)(K:WG ι),(∀ i n,K i n 1=0)→∀ (i:ι)(G:Ratio c f)(ho:Odd G.count.val){t:ℝ}(Y:cro G t)(W:Meter TailB G t)(V:Meter Grave G t)(I:Cover→ Pal), (∀ b,Along j G.count ho (Thread j) b (S i) G 1)→Y.val=1 → fulfills G ho t (j:=j) S K i W V Y→∀ (X: Momentum→ Pal)(k:ℝ),0≤k→Reads I X→RailP m I k→NullW (potion j (S i) X)→∀ x:Single c,
 paidX (perk m x) (fun y=>pulled G Y W (love f (cart f I)) univ x y) ≤ C*k/G.count.val:=by
 obtain ⟨C,z,H⟩:=grove j m e h p v; refine ⟨C,z,fun {c f ι} S K r i G ho _ Y W V I hv s z X k v h' u q x=>?_⟩; rw [chord j e h S K r i G ho Y W V I hv s z]; exact H G ho (Thread j) (canUse j _ ho) (S i) I X k v h' u q x
end YM.CF.Haro
