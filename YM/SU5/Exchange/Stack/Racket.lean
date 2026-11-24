import YM.SU5.Exchange.Stack.Manor
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v s t Nτ:ℝ}{l q B:ℕ}{p:BudgetPoint}
local notation "Ω"=> Single N
open Sault Leaf
variable {P W:SOp N}{K:Scree.Loom N}{V M:phy N}{h:ℝ}
-- static emission reach. tail activation by shared strict mask on CORE Λ≥shell
variable {O : Site N}
local notation "Θt"=> (offsetMask p.B O)
local notation "Bτ"=> (grooveB l p (node O))
variable {J T:Axis→SOp N}{k:ℕ}(Hx:CrownCar P W O k B a d b)(CV:DockPulse p K t d a h s l q)(HP:Staffer P W d)
variable (hJ:∀ i:Axis,Trunk (node O) (J i) k a b d) (vJ:∀ i:Axis,Soak (node O) (T i) a v d) (hX:Trunk (node O) X k a b d) (hY:Soak (node O) Y a v d)
variable (kV: ∀ i:Axis,∀ z:Openc (More N) d,spur (millIntro P W) O i B z.val=J i z.val+T i z.val)
variable (zV: ∀ z:Openc (More N) d,(P z.val-tickA N)*windmill O B=X z.val+Y z.val)
variable (xP:Solo a c P d)(wP:Solo a c W d)
variable (wB:p.B+2*B ≤ l*p.B)
include CV xP wP
abbrev wζ (a:ℝ)(B:ℕ):ℝ:= stripW a B^4*oneMill a
abbrev huePay(l:ℕ)(p:BudgetPoint)(s h a:ℝ)(B:ℕ):ℝ:=reefCost l p s h*(2*(Tap.wingRent Fir.Aop a*wζ a B))
lemma barSale :let L:= treeEarnings l p s h a c*wζ a B + huePay l p s h a B; Fence P W K p q l (node O) h s (barS0 N B O) L L:=by
 intro L; let V:=voidΛ N B O; let A:= windmillCost (d:=d) O B CV.hint.le
 have ht:= (trimQ h CV xP wP A).sub (glowTrace h CV (aura_Y A (Tap.soil_tick (N:=N) a d) CV.hint.le)); -- tune
 simp only [List.length_ofFn] at ht; exact ht

omit xP wP
include HP kV zV
abbrev frontK (P W:SOp N)(B:ℕ)(O:Site N)(K:Scree.Loom N): phy N:=fun i=>Sault.kerLocal (P (profile (K i))) (tickA N) (windmill O B) (W (profile (K i)))
lemma lanternMil (x:Orbit N) : frontK P W B O K x = blazePlate K X x+ northLine K O J B x-barS0 N B O x+ (blazePlate K Y x+northLine K O T B x) :=by
 let Z:=profile (K x); let P':=P Z; let A:=tickA N; let M:= W Z; let Ψ:= voidΛ N B O
 have hm:(P'-A)* Ψ=X Z+Y Z:= zV (roller CV.pos CV.roof x)
 let Γ:= inward P' Ψ M; have he:= CV.roof.paid x; have hz:= inwardE HP (K x) he O B
 have hp: dg Γ= northLine K O J B x+ northLine K O T B x:=by
    let f: Op Ω →+FC Ω:= ⟨⟨dg,by simp [dg,dyad]⟩,dg_add⟩
    change f Γ= _; rw [show Γ=_ from hz,map_sum]; unfold northLine; simp_rw [Finset.sum_apply,Pi.sub_apply]; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; rw [show ∀ z:Site N,spur (millIntro P W) z i B Z = co_Ψ z O (J i) Z + co_Ψ z O (T i) Z from fun z=> co_Set O z _ _ HP i B (kV i) CV.pos _ he] -- tune lhs `∀ rw` first only
    rw [show spur (millIntro P W) (O-B • step i) i B (profile (K x))=_ from co_Set O (O-B • step i) _ _ HP i B (kV i) CV.pos _ he]; rw [map_sub, map_add,map_add]; change (_+_ -(_+_):FC (Single N))=_; dsimp only [f,AddMonoidHom.coe_mk,ZeroHom.coe_mk, grantLine,firePlate, gapPlus] -- tune
    unfold Z; abel
 change Matrix.trace ((P'-A)*Ψ) • _+ dg Γ- barS0 N B O x= _; rw [hp,hm, Matrix.trace_add, add_smul]
 unfold blazePlate; unfold Z; abel
include wB
omit CV HP kV zV wB
lemma pingMono {S T:Support (More N)}{x:Orbit N}(h:T⊆ S)(t:x∈pingMask p S):x∈ pingMask p T:=fun i v=> t i (fun g=>v (Disjoint.mono h (le_refl _) g)) -- tune binder include many remove
include CV HP kV zV wB
lemma attachLamp : houseK p Bτ (puffLine K p O J X B)=houseK p Bτ (frontK P W B O K - (blazePlate K Y+northLine K O T B)):=by
 let L:= frontK P W B O K; let R:= barS0 N B O; funext x; by_cases t:x∈pingMask p Bτ
 · have hl:x∈ pingMask p Θt:= pingMono (offsetFit O O (by rw [separation_self]; omega) wB) t
   have h(i:Axis)(y:Site N)(A:SOp N)(v:separation O y ≤ B): coverLine K p O y A x=grantLine K O y A x:=Set.indicator_of_mem (pingMono (offsetFit O _ v wB) t) _
   have hg:highLine K p O J B x=northLine K O J B x:=by unfold highLine northLine; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl ?_; intro i _; rw [Pi.sub_apply,Pi.sub_apply, h i _ _ (stopBeam O i B).1, h i _ _ (stopBeam O i B).2]
   rw [houseK,houseK,Set.indicator_of_mem t,Set.indicator_of_mem t,puffLine,Pi.add_apply,houseK,Set.indicator_of_mem hl]; simp only [Pi.sub_apply,Pi.add_apply]; rw [lanternMil CV HP kV zV x,hg]; abel -- order?
 rw [houseK,houseK,Set.indicator_of_notMem t,Set.indicator_of_notMem t]

abbrev veilPay (l:ℕ)(p:BudgetPoint)(s h a c b:ℝ)(B:ℕ) := (reefCost l p s h*b+(treeEarnings l p s h a c*wζ a B+huePay l p s h a B))+salvoX l p s h a c B*b
abbrev tailPay (l:ℕ)(p:BudgetPoint)(s h a c v:ℝ)(B:ℕ) := reefCost l p s h*v+salvoX l p s h a c B*v
abbrev κfront(l:ℕ)(p:BudgetPoint)(s h a c:ℝ)(B:ℕ) := let T:= payΩ a c (wζ a B); let V:=reefCost l p s h; V*(2*(T*(Real.exp a+c)))+V*(2*(c*T))
include xP wP hJ hX hY vJ
lemma taught : let L:=veilPay l p s h a c b B; let S:=tailPay l p s h a c v B
 Fence P W K p q l (node O) h s (puffLine K p O J X B) (κfront l p s h a c B+S+(L+L)) S:=by
 intro L S; let Yx:=puffLine K p O J X B; let V:=frontK P W B O K; have hp: Fence P W K p q l (node O) h s V (κfront l p s h a c B) 0:= spinPlasma h CV xP wP (windmill O B) (show Soak _ _ a (wζ a B) _ from (show Soak _ _ _ _ _ from windmillCost O B CV.hint.le)) -- tune
 let g:=squarePerk (B:=B) O CV xP wP vJ
 have hz: Fence P W K p q l (node O) h s (houseK p Bτ Yx) (κfront l p s h a c B+S) S:=by
    rw [show houseK p Bτ Yx= _ from attachLamp CV HP kV zV wB]; have H:= (hp.sub ((glowTrace h CV hY).arc g)).aft (Subset.refl _)
    rw [zero_add] at H; exact H
 have hv: Fence P W K p q l (node O) h s Yx L L:= (((glowTrace (P:=P) (W:=W) h CV hX.pay).sub (barSale CV xP wP)).aft (offsetFit O O (by rw [separation_self]; omega) wB)).arc (mantlet O CV xP wP wB fun x=> (hJ x).pay)
 have hx: houseK p Bτ Yx+(Yx-houseK p Bτ Yx)=Yx:=by abel
 have HE:= hz.arc (hv.tee (Subset.refl _)); rw [hx,add_zero] at HE; exact HE
end YM.CF.Swell
