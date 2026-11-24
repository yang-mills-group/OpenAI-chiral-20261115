import YM.CF.Vp929.Pre.Fee
import YM.CF.Vp929.Budget.Read
import YM.CF.Pso.Plight
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Push.AbsoluteSums Trees Ursell Push.AbsoluteSums.Graph Bake Gas Wray Larch Nor
variable {a s d δ γ:ℝ}{G H:Pax n}
variable (p:0<d)(vx:0≤a)(h':1≤h)
open Wray
-- sweep obligations. elementary linear algebra lemmas.
open Lilt
namespace Cash
abbrev prominence (P:BudgetPoint) : ℝ := P.supportExponent+1+1

abbrev due (τ:Ids n)(A:Pax n) := Mat_R (fun i=> vault_Z (A i (1,τ)))
abbrev returnV (τ:Ids n)(P:BudgetPoint)(A:Pax n):Pax n:= fun i=> zenS P i.val ∅ (A i -cashV (due τ A) i)
abbrev earn (τ:Ids n) (P:BudgetPoint) (A:Pax n): RegBudget n:= cast_E (returnV τ P A) τ
abbrev owe (τ:Ids n) (A:Pax n): Cusp n:= nextE (due τ A)
abbrev summit (τ:Ids n)(G:Pax n):ℝ:=∑ i:Aura n,due τ G i
abbrev poise (G:Pax n) := Turf G ∧ Sym_a G
variable {F G:Pax n}(τ:Ids n)(pL:MonoQ P h (prominence P) F w)(pA: poise F)
lemma poiseSub (p:poise F)(q:poise G) : poise (F-G) := by
 refine ⟨fun i v u=> congrArg₂ (fun v (u:Cipher n)=> v-u) (p.1 i v u) (q.1 i v u),fun s i v=>?_ ⟩; exact (congrArg₂ (fun v (u:Cipher n)=> v-u) (p.2 s i v) (q.2 s i v)).trans (map_sub ..).symm
lemma zealSub {u v:Cusp n}(p:ZealQ u)(q:ZealQ v): ZealQ (u-v):= fun s V z i D t l=>(congrArg₂ (fun v (u:Cipher n)=>v-u) (p s V z i D t l) (q s V z i D t l)).trans (map_sub ..).symm
lemma zealAdd {u v:Cusp n}(p:ZealQ u)(q:ZealQ v): ZealQ (u+v):=fun s V z i D t l=>(congrArg₂ (fun v (u:Cipher n)=>v+u) (p s V z i D t l) (q s V z i D t l)).trans (map_add ..).symm
lemma zealO {F:Pax n}: ZealQ (owe τ F):= by
 intro s V p i D t v; unfold owe; rw [nextE,due,tally_F]; change _=suit_Y s (-(due _ F i•(1:Cipher n))); rw [map_neg,map_smul,map_one]
lemma subDue : due τ (F-G)= due τ F-due τ G:=by funext i; unfold due Mat_R; rw [Pi.sub_apply]; simp_rw [Pi.smul_apply, Finset.sum_apply,Pi.sub_apply,zeal_F,Function.comp_apply,lift'_E,sum_sub_distrib,smul_sub]
lemma subEarn : earn τ P (F-G)=earn τ P F- earn τ P G:=by
 have he(i): returnV τ P (F-G) i=returnV τ P F i-returnV τ P G i:=by
    funext V; rw [Pi.sub_apply]; unfold returnV zenS; split
    · dsimp only [Pi.sub_apply]; rw [subDue]; unfold cashV Lilt.thim; simp only [Pi.sub_apply,sub_smul]; abel
    exact (sub_self _).symm
 funext i V; change bassH (lagE i) • returnV τ P (F-G) _ _= bassH (lagE i) • returnV τ P F _ _ -bassH (lagE i) • returnV τ P G _ _ ; rw [he,Pi.sub_apply,smul_sub]
lemma subOwe : owe τ (F-G)=owe τ F-owe τ G:=by funext i D V; unfold owe; rw [subDue]; change -((due τ F i-due τ G i) • (1: Cipher n))= -(due τ F i • (1:Cipher n))- -(due τ G i • (1:Cipher n)); rw [sub_smul]; abel
include pA
lemma booths : poise (returnV τ P F):=by
 constructor
 · intro i V B; unfold returnV zenS; split
   · exact congrArg (fun x=> x - (cashV (due τ F) i V)) (pA.1 i V B)
   rfl
 intro s i v; rw [returnV,zenS,←yarnV (P:=P) s v i 0,returnV,zenS]; split
 · next h=> simp only [Pi.sub_apply,map_sub,pA.2,due,cashV,tally_F, Lilt.thim,map_smul,map_one]
 exact (map_zero _).symm
local notation "dF"=> due τ F
omit pA
include h' pL
lemma charter: ∃ L:Aura n→ℝ,(∀ i,‖dF i‖≤L i) ∧ ∀ o:Seat n,tallB L P.B (prominence P) o ≤ w:= by
 obtain ⟨S,T,V⟩:=pL; let U:Orbit n:=(1,τ); have h(i:Aura n): ‖vault_Z (F i U)‖ ≤ S i:= (Complex.abs_re_le_norm _).trans ((YM.CF.norm_entry (F i U).val _ _).trans ((T i).capF h' U (ping_f P _)))
 refine ⟨Mat_R S,fun i=>?_ , labourV S _ _ V⟩; unfold due Mat_R; rw [Pi.smul_apply,norm_smul,Pi.smul_apply, Finset.sum_apply,Finset.sum_apply,Real.norm_of_nonneg (envy n).le]; apply mul_le_mul_of_nonneg_left _ (envy n).le; exact (norm_sum_le ..).trans (sum_le_sum fun j _=> h _)
local notation "fQ"=> Cash.returnV τ P F
include pA
lemma priceRun : IncX Utrue (Cash.earn τ P F) P h (reserveT P.power P.order P.B 1*(w+w)) ∧ Packed P h (prominence P) (Cash.owe τ F) w:=by
 obtain ⟨S,T,V⟩:= charter h' τ pL; have hc(X:Aura n):Vow.Medal P X.val ∅ (cashV dF X) h (S X):= (Medal.oneT.rum (dF X)).big (by rw [mul_one]; exact T X)
 have hg(x:Aura n):0 ≤ S x:=(norm_nonneg _).trans (T x); refine ⟨?_ ,S,⟨hg,fun i D v l=>Larch.nom_F h' P i _ (hc i) D ⟩,V⟩
 let H:MonoQ P h (prominence P) (F-cashV dF) (w+w):= pL.sub ⟨S,hc,V⟩; obtain ⟨L,b,q⟩:=H; exact worth_R P fQ τ (booths τ pA).2 (booths τ pA).1 (zero_le_one.trans h') (fun i=>zen_B P (b i)) q
omit h' pL
lemma budgetIdentity (V:Orbit n)(u:Rue.FleetS P.threshold V.1): coldE P F V= owed_E n (∑ i:Aura n,dF i)+exponentL P (earn τ P F) V.1+fuelV P (Cash.owe τ F) V:= by
 have he: coldE P F V=coldE P (cashV dF+fQ) V:= sum_congr rfl fun i p=> by
    have g: visible P i.val ∅ V.1:= hates (by rw [sdiff_empty]; exact (mem_filter.mp p).2)
    change _= cashV dF i V+zenS _ i.val ∅ _ V; rw [zenS,if_pos g,Pi.sub_apply]; abel
 have hz: (coldE P (cashV dF) V)= owed_E n (∑ i:Aura n, dF i)+fuelV P (Cash.owe τ F) V:= by
    rw [show owed_E n (∑ i:Aura n,dF i) = ∑ i:Aura n, owed_E n (dF i) from Finset.sum_smul ..]; exact (tall_K P dF V u).symm
 unfold earn; rw [he,crep, hz,ocean P (returnV τ P F) τ (booths τ pA).1]; abel
end Cash
end YM.CF.Py.Rate
