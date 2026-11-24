import YM.CF.DPress.Fees.Tea
import YM.CF.DPress.Fees.Wall
import YM.CF.Roots.Seat
/-! single computation.Rent.V attributes. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.Fees
open Function Lattice MeasureTheory Filter Metric Analytic Finset
open Lat Cube RG Fock Pastry Skye Scree Vow Mew Jet Hake JetRead
open scoped Topology Classical BigOperators ContDiff Matrix Matrix.Norms.L2Operator YM.CF.Mew
attribute [local instance] opCStarAlgebra
abbrev Cribs(n:Side):=Finset (Dwell n)
abbrev Listen (t:ℝ){X Y:Type}[NormedAddCommGroup Y][NormedSpace ℂ Y](f:ℂ→X→Y)(a:Set X):= ∀ i∈a,DifferentiableOn ℂ (fun z=> f z i) (ank t)
variable {n:Side}{P:BudgetPoint} (h:ℝ)(R:Scree.Hub n)(X:Force n)(t:Support (More n)) {a L:ℝ}
variable (P)
namespace Rails
section crumb
variable {W V I:Type*}[Fintype I][DecidableEq I] {J: I→Dial V}{w:I→ℝ}
lemma by_bill {v:I→ℝ}(u:∀ i,0 ≤ v i)(k:∀ i,1≤ w i)(i:I)(t:(∑ i,w i*v i)≤a): v i ≤ a:= ((le_mul_of_one_le_left (u i) (k i)).trans (single_le_sum (f:=fun i=>w i*v i) (fun i _=>mul_nonneg (zero_le_one.trans (k i)) (u i)) (mem_univ _))).trans t
lemma holoB {I:Type}(f:ℂ→I→Cipher n)(x:I)(i:Cribs n)(h:DifferentiableOn ℂ (fun z=> f z x) (ank L)):DifferentiableOn ℂ (fun z=> crumb (f z x).val i) (ank L):=(chipV i).differentiable.comp_differentiableOn h
end crumb
private lemma tariffHigh(o:Seat n)(v:1 ≤ h)(i:Cribs n): 1≤ Scree.tariff P o h i:=one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by simp)) (one_le_pow₀ v)
section Press
abbrev Good(P:BudgetPoint)(S:Support (More n)):Set (Pane n) :={i | pingS P.threshold S i}
abbrev βPay (T: Support (More n))(x: Pane n)(i:Cribs n)(u:InkD n) (a:tangD n): ℂ:= crumb (u (sting P T x a)).val i
lemma β_pay(x:Pane n)(i:Cribs n)(f:InkD n): βPay P ∅ x i f=(fun k=> crumb (f (increment x k)).val i):=funext fun b=> by rw [βPay,interest']
abbrev press(i:Cribs n): Dial (InkD n):= cover (fun x=> hood (βPay P ∅ x i) (loft P R.val.1)) (Good P R.val.2)
abbrev beaming : Dial (InkD n):=staff (press P R) (Scree.tariff P R.val.1 h) univ
variable {f: InkD n}
lemma billLens (h:∃ c,PressB P R f h c)(i:Cribs n): Live (press P R i) f:=by
 obtain ⟨b,h⟩:=h; obtain ⟨c,k,g,v⟩:=h.worth; refine ⟨c i,(covering ..).2 ⟨k _,fun x hx=>landing.mp ?_⟩⟩; let w:=g x hx i; have ht: Signs P R.val.1 (βPay P ∅ x i f) (c i):=by simpa only [β_pay] using w
 exact (loftQ _ ht.paid).1 ht -- tune h shadow h in Type `∃ c`
variable (tH:1≤h)
include tH
lemma ritual : Receipt (fun f v=> PressB P R f h v) (beaming P h R):=by
 let S:=R.val.2; let Z:=Cribs n; let A:=Scree.tariff P R.val.1 h; have hu(i:Z):1≤A i:= tariffHigh _ _ _ tH i; constructor; · intro x a h; obtain ⟨c,w,g,v⟩:=h.worth; refine (staff_up (press P R) A (fun i _=>zero_le_one.trans (hu i)) c (x:=x) (fun i (_:i∈(univ:Finset Z))=>(covering _ _).2 ⟨w i,fun V p=> landing.mp ?_⟩)).up v; have hv:Signs P R.val.1 (βPay P ∅ V i x) (c i) :=(by simpa only [β_pay] using g V p i); exact (loftQ _ hv.paid|>.1 hv)
 rintro x a ⟨b,p⟩ v; let y:=fun i=>meter (press P R i) x; let H(i:Cribs n):=billLens P h R ⟨b,p⟩ i; refine {p with worth:=⟨y,fun i=>(Live.pays (H i)).p,?_ ,staff_due (press P R) A (fun i _=>zero_le_one.trans (hu i)) v (fun i _=>H i)⟩}; intro U l i; have he:=landing.mpr ((covering _ _|>.1 (Live.pays (H i))).2 U l); -- wrong `.2.2`; note
 obtain ⟨c',κ,g,u⟩:=p.worth; have hv:Signs P R.val.1 (βPay P ∅ U i x) (c' i):=by simpa only [β_pay] using g U l i
 simpa only [β_pay] using (loftQ _ hv.paid|>.2 he) -- tune
lemma renter(f:ℂ→InkD n)(g:Listen L f (Good P R.val.2))(v:∀ z∈ank L,PressB P R (f z) h a)(k:1<L): Brings L f (f 1-f 0) (beaming P h R):=by
 apply Brings.stage; intro i _; apply Brings.covered; intro U x; apply Brings.hold; apply JetRead.coal (x:=fun z x=>crumb (f z x).val i) x (fun s v=> holoB _ _ _ (g s v)) (a:=a) _ k; intro z p V w; obtain ⟨b,l,r,t⟩:= (v z p).worth; have he:Signs P R.val.1 (βPay P ∅ V i (f z)) (b i):=(by simpa only [β_pay] using r V w i); exact Prism.high he (by_bill l (tariffHigh P h R.val.1 tH) i t) -- tune `coal f⊚x diff` Lean defeq subtract Ch.val
end Press
end Rails
end YM.CF.DPress.Fees
