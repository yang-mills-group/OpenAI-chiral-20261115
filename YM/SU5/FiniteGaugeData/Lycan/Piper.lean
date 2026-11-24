import YM.SU5.FiniteGaugeData.Lycan.Feld
/-! # Color sum recipe for any label type in species-color sets. -/
set_option autoImplicit false
set_option synthInstance.maxSize 17000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 510000
noncomputable section
namespace YM.CF.Fock.Reduction.Lycan
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama Dinar Relief Rheims Dijon Currency Fist Ziz Thera Spire Scroll Celeste Loyd
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
variable {I n A D:Type*}[LinearOrder n][Fintype n]{P Q:Op n}
variable (σ: I→Finset D)
variable (U V:I×D→Ket n)
local notation "Μ"=> I×D
local notation "Ω"=> Μ×Μ
/-- All color assignments: map each label occurrence to its own color, keep order. -/
def Silk {E:Type*}[AddCommMonoid E](σ:I→ Finset D)(f: List ((I×D)×(I×D))→ E): List I→ E
 | []=> f []
 | (x::X)=> ∑ i∈σ x,Silk σ (fun l=> f (((x,i),(x,i))::l)) X
lemma pureSilk {E:Type*}[AddCommMonoid E](f g:List (Ω) → E) (X:List I)(p:∀ (Y:List (Ω)),Y.length=X.length→ f Y=g Y): Silk σ f X= Silk σ g X:=by
 induction X generalizing f g with
 | nil=> rw [Silk,Silk,p _ rfl]
 | cons a X ih=> rw [Silk,Silk]; exact sum_congr rfl fun i _=> ih _ _ (fun Y v=> p _ (by simp only [List.length_cons, v]))
lemma pureHue {E:Type*}[AddCommMonoid E]{T:I→Finset D}(h:T=σ)(f:List (Ω)→ E)(X:List I): Silk T f X=Silk σ f X:=by rw [h]
abbrev Conv (σ:I→Finset D)(C:I×D→I×D→ℂ):List I→ℂ:=Silk σ (Album C)
-- Wick identity of colored product
abbrev tribe(i:I):FC n:=∑ j∈σ i,mark U V (i,j) (i,j)
abbrev Coral (σ:I→Finset D)(U V:I×D→Ket n)(X:List I):= (X.map (tribe σ U V)).prod
private lemma overflow (W:FC n)(X:List I): Volt Q P (W*Coral σ U V X)=Silk σ (fun l=> Volt Q P (W*studio U V l)) X:=by
 induction X generalizing W with
 | nil=>rw [Silk]; rfl
 | cons i X ih=>
    let A:= mark U V; let Z:=Coral σ U V X; rw [Silk]; change Volt Q P (W*((∑ j∈σ i,A (i,j) (i,j))*Z))=_; rw [←mul_assoc, mul_sum,sum_mul,grain]; refine sum_congr rfl fun j _=> ?_; rw [ih]; refine pureSilk σ _ _ X (fun Y _=>?_); rw [mul_assoc]; rfl
local notation "UV"=>fun (a b:I×D)=> cupE Q P (U a) (V b)
lemma Bodice (g:Standing Q P)(scale0:∀ (a b:I×D),inner ℂ (V b) (U a)=0)(X:List I): Volt Q P (Coral σ U V X)=Conv σ (fun a b=>cupE Q P (U a) (V b)) X:=by
 nth_rw 1 [← one_mul (Coral σ U V X)]; rw [overflow]; refine pureSilk σ _ _ X (fun Y _=>?_); rw [one_mul]; exact adjust g U V scale0 Y
-- Homogeneity & tendsto
variable (C:A→D→ℂ)(k:ℂ)
lemma scaled {V:Type*}[AddCommMonoid V][Module ℂ V] (L:D→ℂ)(W:List (A×D)→ V)(z v:ℂ)(b:D)(X:List (A×D)): slid (fun i=>z* L i) b (fun l=> v • W l) X=(z*v) • slid L b W X:=by
 induction X generalizing W with
 | nil=>rw [slid,slid,smul_zero]
 | cons i l ih=> rcases i with ⟨a,q⟩; rw [slid,slid,ih (fun T=> W ((a,q)::T)), smul_add]; simp only [smul_smul]; rw [mul_right_comm z (L q)] -- tune
lemma hScale (X:List (A×D)): Album (fun a b=> k*C a b) X=k^X.length*Album C X:=by
 suffices h:∀ (n:ℕ)(X:List (A×D)),X.length=n→Album (fun a b=> k*C a b) X=k^n*Album C X from h _ X rfl
 intro n; induction n with
 | zero=>intro X h; rw [List.length_eq_zero_iff.mp h]; change 1=k^0*1; rw [pow_zero,mul_one]
 | succ n ih=>
    intro X h; cases X with
    | nil=> simp at h
    | cons x X => rcases x with ⟨a,b⟩; rw [List.length_cons,Nat.add_left_inj] at h; rw [spindle, spindle, ih _ h]; let Ω':=Album C; let C':=Album (fun a b=>k*C a b); rw [sift_pure (fun q=>k*C a q) b C' (fun l=>k^n • Ω' l) X (fun l v=>ih _ (v.trans h)), scaled (C a) Ω', smul_eq_mul]; unfold Ω'; ring
lemma silkTone (X:List I)(F:List ((I×D)×(I×D))→ℂ)(z:ℂ): Silk σ (fun x=> z*F x) X=z*Silk σ F X:=by
 induction X generalizing F with
 | nil=> rw [Silk,Silk]
 | cons i X ih => rw [Silk,Silk,mul_sum]; refine sum_congr rfl fun j _=>?_ ; exact ih (fun l=> F (((i,j),(i,j))::l))
lemma silkCost (X:List I)(C:Μ→Μ→ℂ): Conv σ (fun a b=>k*C a b) X=k^X.length*Conv σ C X:=by unfold Conv; rw [←silkTone]; exact pureSilk σ _ _ X (fun Y h=>by rw [hScale,h])
-- evaluation along any tendsto (with fixed labels, arbitrary paths/dependent spectra). iterate factored formula. only complex.S.
variable {E:Type*}{f:Filter E}
lemma p_sift{u:E→ D→ℂ}{U:D→ℂ}{v:E→ List (A×D)→ℂ}{V: List (A×D)→ℂ}(x:D)(X:List (A×D))(p:∀ i:D,Tendsto (fun a=>u a i) f (𝓝 (U i)))(q:∀ Y:List (A×D),Y.length=X.length→ Tendsto (fun i=>v i Y) f (𝓝 (V Y))): Tendsto (fun a=>slid (u a) x (v a) X) f (𝓝 (slid U x V X)):=by
 induction X generalizing v V with
 | nil=> simp only [slid]; exact tendsto_const_nhds
 | cons b X ih=>
    rcases b with ⟨a,d⟩; simp only [slid]; exact (((p d).smul (q ((a,x)::X) rfl)).add (ih (v:=fun i Y=>v i ((a,d)::Y)) (V:=fun Y=>V ((a,d)::Y)) fun Y h=> q _ (by simp [h]))) -- tune parentheses
variable (F:E→A→D→ℂ)
lemma priceI (X:List (A×D))(p:∀ i j,Tendsto (fun a=> F a i j) f (𝓝 (C i j))): Tendsto (fun a=>Album (F a) X) f (𝓝 (Album C X)):=by
 suffices h:∀ (n:ℕ)(X:List (A×D)),X.length=n→ Tendsto (fun a=>Album (F a) X) f (𝓝 (Album C X)) from h _ X rfl
 intro n; induction n with
 | zero=> intro X h; rw [List.length_eq_zero_iff.mp h]; change Tendsto (fun a:E=>1) _ (𝓝 (1:ℂ)); exact tendsto_const_nhds
 | succ n ih=>
   intro X h; cases X with
   | nil=>simp at h
   | cons t X=> rcases t with ⟨b,d⟩; rw [List.length_cons,Nat.add_left_inj] at h; simp only [spindle]; exact (((p b d).mul (ih X h)).sub (p_sift d X (p b) (v:=fun i=>Album (F i)) (V:=Album C) (fun Y v=> ih _ (v.trans h)))) -- tune
lemma priceSilk(X:List I)(F:E→List (Ω)→ℂ)(G:List (Ω)→ℂ)(p:∀ l:List (Ω),l.length=X.length→ Tendsto (fun a=>F a l) f (𝓝 (G l))) : Tendsto (fun a=>Silk σ (F a) X) f (𝓝 (Silk σ G X)):=by
 induction X generalizing F G with
 | nil=> exact p [] rfl
 | cons i X ih=> simp only [Silk]; refine tendsto_finsetSum _ (fun j _=>?_); exact ih (fun a l=>F a (((i,j),(i,j))::l)) _ (fun l h=>p _ (by simp [h])) -- cite
lemma priceConv(X:List I)(F:E→Μ→Μ→ℂ)(G:Μ→Μ→ℂ)(p:∀ i j,Tendsto (fun a=> F a i j) f (𝓝 (G i j))): Tendsto (fun i=>Conv σ (F i) X) f (𝓝 (Conv σ G X)):= priceSilk σ X _ (Album G) (fun l _=>priceI G F l p)
#print axioms Bodice
#print axioms priceConv
#print axioms silkCost
end YM.CF.Fock.Reduction.Lycan
