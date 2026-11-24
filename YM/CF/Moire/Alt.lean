import YM.CF.Moire.Buds
/-! Extensive *nonperturbative* analytically tilted Weyl sea. Projection complexification with gauge for sector extensions. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Moire
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire Branch Nacre
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m:ℕ}{n:Side}
-- oriented arc with complexification

def rayW(a:Shape)(w:Walk):= w.map (fun i=> i.rotate a.s) -- order
lemma ray_L(a:Shape)(w:Walk): (rayW a w).length=w.length:=by simp [rayW]
lemma ray_s(a:Shape)(x:Site (More n))(w:Walk): stop (a.anon n x) (rayW a w)=a.anon n (stop x w):=by
 induction w generalizing x with
 | nil=>rfl
 | cons d w h=> rw [rayW,List.map_cons,stop,←salt,stop]; exact h _
lemma ray_t(a:Shape)(x:Site (More n))(w:Walk)(U:Bkg (More n)): travel U (a.anon n x) (rayW a w)=travel (Yg a U) x w:=by
 induction w generalizing x with
 | nil=>rfl
 | cons d w h=> rw [rayW,List.map_cons,travel,←salt,travel,show List.map _ w=rayW a w from rfl,h,Yg,veil_x]; rfl

def whirl(x:Site n)(w:Walk)(X:Stem n): Op SU.F := (1/2:ℝ) • ((track X x w).2 - (track X x (reverse w)).2)
lemma wind_g(x: Site n)(w:Walk)(h:stop x w=x)(X: Stem n)(g): whirl x w (relayg g X)= twist (firstF (g x)) (whirl x w X):=by
 unfold whirl; rw [track_g,track_g]; have he:=reverse_stop w x; rw [h] at he; rw [h,he, map_smul, map_sub,twist_formula,twist_formula]; rfl
lemma wind_v(x: Site n)(w:Walk)(h:stop x w=x)(U:Bkg n): whirl x w (profile U) = (1/2:ℝ) • (group.mat (travel U x w)-group.mat (travel U x w)⁻¹):=by
 unfold whirl; rw [track_pr,track_pr]; have he:=travel_reverse w U x; rw [h] at he; rw [he]; rfl
lemma whirl_d(x:Site n)(w:Walk):Differentiable ℂ (whirl x w):=by exact Differentiable.const_smul ((track_d x w).snd.sub (track_d x (reverse w)).snd) (1/2:ℝ)

def east(a:Shape)(x:HopK n): Site (More n) := a.anon n (terse x)
def spark(P:Toy m n)(a:Shape)(x y:HopK n)(i:Trip m n)(X:Chin n): Op Slot:= flaw P x y i (fun k=> whirl (east a x) (rayW a (boot (terse x) (i k))) X) * (track X (east a x) (rayW a (shiftH (terse x) (terse y)))).1
lemma spark_m(P:Toy m n)(a:Shape)(x y:HopK n)(i:Trip m n)(V:Bkg (More n)) : spark P a x y i (profile V)=mold P x y i (Yg a V):=by
 let U:=Yg a V
 unfold spark east; rw [track_pr,ray_t,mold]; congr 1; unfold silt; have ht(k:Fin m): whirl (east a x) (rayW a (boot (terse x) (i k))) (profile V) = (1/2:ℝ) • (group.mat (travel U (terse x) (boot (terse x) (i k)))-group.mat (travel U (terse x) (boot (terse x) (i k)))⁻¹):=by unfold east; rw [wind_v,ray_t]; rw [ray_s,booth]
 unfold east at ht;  rw [flaw_v]; swap
 · intro j; rw [ht]; change star ((1/2:ℝ) • ( (_ :group.Mat) - group.mat (_⁻¹)))=_; exact (show ∀ A:group.Mat, star ((1/2:ℝ) • (A-star A)) = -((1/2:ℝ) • (A-star A)) from fun A=>by rw [star_smul,star_sub,star_star,star_trivial, ← smul_neg,neg_sub]) _
 congr 1; ext1 k; rw [ht]; rfl
lemma spark_g(P:Toy m n)(h:handy P)(a:Shape)(x y: HopK n)(i:Trip m n)(X:Chin n)(g): spark P a x y i (relayg g X)= (matter (g (east a x))).val *spark P a x y i X *star ((matter (g (east a y))).val):=by
 unfold spark; rw [track_g]; simp_rw [fun k: Fin m=> wind_g (east a x) (rayW a (boot (terse x) (i k))) (by unfold east; rw [ray_s,booth]) X g]; rw [show stop _ _ = east a y by unfold east; rw [ray_s,stopH], flaw_g _ h,twist_formula]; let T:=matter (g (east a x)); change T.val*_ *star T.val * (T.val* (_:Op Slot)*star _) =_; rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star _),← Matrix.mul_assoc (star _),T.property.1,one_mul]; simp only [Matrix.mul_assoc]; rfl
lemma spark_d(P:Toy m n)(a:Shape)(x y:HopK n)(i:Trip m n): Differentiable ℂ (spark P a x y i):=by
 refine Differentiable.mul ?_ ((track_d (east a x) _).fst); unfold flaw; apply Differentiable.fun_sum; intro u _; let W(X: Chin n):ℂ:= ∏ k, spurY (u k) (whirl (east a x) (rayW a (boot (terse x) (i k))) X); apply Differentiable.smul (c:=W) _ (differentiable_const _); 
 have hf(p: Finset (Fin m)): Differentiable ℂ (fun X:Chin n=> ∏ k∈p, spurY (u k) (whirl (east a x) (rayW a (boot (terse x) (i k))) X)):=by
   induction p using Finset.induction_on with
   | empty=> exact (show _ from by simp) -- tune
   | @insert a V hc ih=> simp only [prod_insert hc]; exact ((spurY _).differentiable.comp (whirl_d _ _)).mul ih
 exact hf _
end YM.CF.Moire
