import YM.CF.DPress.Fees.Aura
/- taken union tallB at one footprint with arbitrary full flag mix. $env∞$ convert common price.Lifts. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.DPress.Fees.Moral
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead Rails Wray Finance Receipt Rosy
open Push.AbsoluteSums Trees -- tune reuse Lodge methods
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
variable {n:Side}{P:BudgetPoint}{a L h θ b:ℝ} {S:Aura n}
abbrev Hub0(n:Side) := Support (More n)
abbrev Stake0(n:Side) := Hub0 n → Copy n
-- choose both aggregates as rays.J.Iterator max. 
variable (P h θ S)
abbrev Δ (x:Aura n)(q:Hub0 n) : Credit (Stake0 n):= fun A => Medal P x.val q (A q) h
abbrev tahan(x:Aura n)(q:Hub0 n) := hood (fun k:Stake0 n=> k q) (shield P h x.val q)
def wage_p(n:Side)(v:Bool)(i j:Hub0 n):ℝ:= if v || decide (i=j) then 1 else 0
variable (u:Bool)
abbrev ΦL(S:Aura n) := Measures (Δ P h S) (fullD S) (wage_p n u)
abbrev Φq(S:Aura n) : Dial (Stake0 n):= Relay (tahan P h S) (fullD S) (wage_p n u)
abbrev Ων : Credit (Cusp n):= Wage P θ (ΦL P h u)
abbrev Ωs : Dial (Cusp n):= Lifts P θ (Φq P h u)
abbrev XL := Ων (n:=n) P h θ true -- positive mass; tune param order
abbrev ZL := Ων (n:=n) P h θ false -- sup
variable (t:1≤h)
include t
lemma Z_inst (x:Hub0 n): Finance (Δ P h S x) (tahan P h S x):= Finance.thru (u:=fun i:Stake0 n=>i x) (capM P h S.val x t) (fun _ _=>rfl) (fun _ _=>rfl)
lemma oke : Finance (ΦL P h u S) (Φq P h u S):= Finance.system _ _ _ _ (fun i _=>Z_inst P h S t i) (fun i j _=>ite_nonneg zero_le_one le_rfl)
lemma νreg : Finance (Ων P h θ u) (Ωs (n:=n) P h θ u):= earnings _ _ _ _ (fun _=>oke P h _ u t) -- tune type.
variable (e:0 ≤ θ) (K:Cusp n)
include e
lemma supports (p: Ων P h θ u K a)(i:Hub0 n)(v:i∈fullD S):Medal P S.val i (K S i) h a:= Finance.qualifyZ _ _ _ (wage_p n u) (fun i (_:i∈fullD S)=> Z_inst P h S t i) (fun i j _=> ite_nonneg zero_le_one le_rfl) (affordability P θ _ _ (fun i:Aura n=>oke P h i u t) e p S) i v i (by simp [wage_p]) -- tune
lemma Ξcare (f:ℂ→ Cusp n)(p:∀ z ∈ank L,Ων P h θ u (f z) a)(c:∀ (i:Aura n)(j:Hub0 n), j∈fullD i→ Listen L (fun x=> f x i j) (γGood P (i.val \ j)))(k:1<L): Ων P h θ u (f 1-f 0) (a/(L-1)):=by
 apply credit0 _ _ _ _ (fun i=>oke P h i u t) f p _ k; intro i; apply Brings.covered; intro j x; apply Brings.stage; intro z a; exact Brings.hold (u:=fun x:Stake0 n=>x z) (armorB P h i.val z t _ (c i z a) (fun x p0=> supports P h θ i u t e _ (p x p0) z a) k)
omit e
-- issue to original FiniteGaugeData pricing.Natural.Actuator.
lemma Φc (V:Stake0 n): ΦL P h true S V a↔∃ b:Hub0 n→ℝ,(∀ i∈fullD S,Medal P S.val i (V i) h (b i)) ∧ (∑ i∈fullD S,b i) ≤ a:=by
 refine ⟨fun ⟨t,q,m,f⟩=>⟨q,m,?_⟩,?_⟩; simpa only [wage_p,Bool.true_or,ite_true,one_mul] using (f ∅)
 rintro ⟨b,w,f⟩; refine ⟨(sum_nonneg fun i p=>(w i p).wage (zero_le_one.trans t)).trans f,b,w,fun i=>?_⟩; simp only [wage_p,Bool.true_or,ite_true,one_mul,f]
lemma vouchers : XL P h θ K a ↔ ∃ v:Aura n→ Hub0 n→ℝ,(∀ x:Aura n,∀ t∈fullD x,Medal P x.val t (K x t) h (v x t)) ∧ (∀ i:Seat n,tallB (Vow.hymn v) P.B θ i≤a):=by
 constructor; rintro ⟨F,g,v⟩; choose C' q f using fun i=> (Φc P h i t (K i)).1 (g i); refine ⟨C',q,fun i=>?_⟩; exact le_trans (sum_le_sum (fun S _=> mul_le_mul_of_nonneg_right (f S) (ccur ..))) (v i)
 rintro ⟨v,g,t'⟩; exact ⟨Vow.hymn v,fun i=>(Φc P h i t _).2 ⟨v i,g i,le_rfl⟩,t'⟩ -- tune.
lemma Φu(V:Stake0 n): ΦL P h false S V a↔ 0 ≤ a∧ ∀ i∈fullD S,Medal P S.val i (V i) h a:=by
 constructor; · intro v; exact ⟨v.1,fun i g=> Finance.qualifyZ _ _ _ (wage_p n false) (fun i (_:i∈ fullD S)=>Z_inst P h S t i) (fun i j _=> ite_nonneg zero_le_one le_rfl) v i g i (by simp [wage_p])⟩
 rintro ⟨t,f⟩; exact ⟨t,(fun _=>a),f,fun i=> by unfold wage_p; simp only [ite_mul,Bool.false_or,decide_eq_true_eq,zero_mul,one_mul,sum_ite_eq]; split<;> first|exact le_rfl|exact t⟩ -- tune.
lemma mantle : ZL P h θ K a ↔ ∃ v:Aura n→ℝ,Larch.Anuk K v P h ∧ ∀ i:Seat n,tallB v P.B θ i≤a:=by
 constructor; rintro ⟨w,u,g⟩; exact ⟨w,⟨fun i=>(u i).1, fun i t' φ g=>(Φu P h i t _|>.1 (u i)).2 t' (by simp [fullD,φ,g])⟩,g⟩; rintro ⟨w,u,g⟩; exact ⟨w,fun i=>(Φu P h i t _).2 ⟨u.1 _,fun j v=> u.2 i j (mem_filter.mp v).2.1 (mem_filter.mp v).2.2⟩,g⟩
end YM.CF.DPress.Fees.Moral
