import Anomaly.Pose
import YM.SU5.Exchange.Stack.Racket
/-! Use profile-only identities in `Swell.taught` to allow translated
same purchases. This is stronger than requesting independent J for each
root. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
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

theorem co_promise (u x:Site N)(A T:SOp N)(HP:Staffer P W d)(i:Axis)(k:ℕ) (H:∀ z:Pane N, Guard z d →spur (millIntro P W) u i k (profile z)=A (profile z)+T (profile z))(v:0<d)(V:Pane N) (h:Guard V d): spur (millIntro P W) x i k (profile V)= co_Ψ x u A (profile V)+ co_Ψ x u T (profile V):=by
 let t:=x-u; let s:=taxiPlus t; let U:=flashA s V; let Z:=γS s; have hv:Guard U d:=keepC (xtra s.charge) (castX s) V d h
 have hp:= limb (P:=P) V t HP u i h k; have he: u+t=x:= by unfold t; abel
 rw [he] at hp
 apply (twist Z).injective; rw [map_add]; rw [show (twist Z).toRingEquiv (spur (millIntro P W) x i k (profile V))=_ from hp, show (twist Z).toRingEquiv (co_Ψ x u A (profile V))=_ from julius s A V,show (twist Z).toRingEquiv (co_Ψ x u T (profile V))=_ from julius s T V]
 exact H _ hv

lemma windmillMoves (o x : Site N)(m:ℕ) : twist (γS (taxiPlus (x-o))) (windmill x m)=windmill o m:=by
  let t:=x-o
  let F: Op Ω →+ Op Ω := (twist (γS (taxiPlus t))).toRingEquiv.toRingHom.toAddMonoidHom
  have h(y:Site N):F (millQ (y+t))=millQ y:= millMotion t y
  let L:=List.ofFn (id:Axis→Axis)
  calc
    _ = F (squareSum millQ m L (o+t)):= by rw [show o+t=x from (by unfold t; abel)]; rfl
    _ = _ := by rw [←square_move,squareMap F]; simp_rw [h]; rfl

lemma co_wind (u x : Site N)(T Z:SOp N)(HP:Staffer P W d)(H:∀ U:Pane N,Guard U d → (P (profile U)-tickA N)*windmill u B=T (profile U)+Z (profile U)) (V:Pane N)(g:Guard V d):
    (P (profile V)- tickA N)*windmill x B=co_Ψ x u T (profile V)+co_Ψ x u Z (profile V) := by
  let t:=x-u; let a:=taxiPlus t; let Q:= γS a
  let U:=flashA a V
  have he:Guard U d:=keepC (xtra a.charge) (castX a) V d g
  apply (twist Q).injective
  rw [map_mul,map_sub,map_add]; rw [show (twist Q).toRingEquiv (P (profile V)) = _ from (HP.passport t V g).symm,
    show (twist Q).toRingEquiv (windmill x B)=_ from windmillMoves u x B,
    show (twist Q).toRingEquiv (tickA N)=_ from tick_taxi t,
    show (twist Q).toRingEquiv (co_Ψ x u T _)=_ from julius a T V,
    show (twist Q).toRingEquiv (co_Ψ x u Z _)=_ from julius a Z V]
  exact H _ he

variable {O : Site N}
local notation "Θt"=> (offsetMask p.B O)
local notation "Bτ"=> (grooveB l p (node O))
variable {J T:Axis→SOp N}{k:ℕ}(Hx:CrownCar P W O k B a d b)(CV:DockPulse p K t d a h s l q)(HP:Staffer P W d)
variable (hJ:∀ i:Axis,Trunk (node O) (J i) k a b d) (vJ:∀ i:Axis,Soak (node O) (T i) a v d) (hX:Trunk (node O) X k a b d) (hY:Soak (node O) Y a v d)
variable (kV: ∀ i:Axis,∀ z:Pane N, Guard z d → spur (millIntro P W) O i B (profile z)=J i (profile z)+T i (profile z))
variable (zV: ∀ z:Pane N, Guard z d → (P (profile z)-tickA N)*windmill O B=X (profile z)+Y (profile z))
variable (xP:Solo a c P d)(wP:Solo a c W d)
variable (wB:p.B+2*B ≤ l*p.B)
include CV xP wP
omit xP wP
include HP kV zV
lemma lanternMil_for (x:Orbit N) : frontK P W B O K x = blazePlate K X x+ northLine K O J B x-barS0 N B O x+ (blazePlate K Y x+northLine K O T B x) :=by
 let Z:=profile (K x); let P':=P Z; let A:=tickA N; let M:= W Z; let Ψ:= voidΛ N B O
 have hm:(P'-A)* Ψ=X Z+Y Z:= zV _ (CV.roof.paid x)
 let Γ:= inward P' Ψ M; have he:= CV.roof.paid x; have hz:= inwardE HP (K x) he O B
 have hp: dg Γ= northLine K O J B x+ northLine K O T B x:=by
    let f: Op Ω →+FC Ω:= ⟨⟨dg,by simp [dg,dyad]⟩,dg_add⟩
    change f Γ= _; rw [show Γ=_ from hz,map_sum]; unfold northLine; simp_rw [Finset.sum_apply,Pi.sub_apply]; rw [←sum_add_distrib]; apply sum_congr rfl; intro i _; rw [show ∀ z:Site N,spur (millIntro P W) z i B Z = co_Ψ z O (J i) Z + co_Ψ z O (T i) Z from fun z=> co_promise O z _ _ HP i B (kV i) CV.pos _ he] -- tune lhs `∀ rw` first only
    rw [show spur (millIntro P W) (O-B • step i) i B (profile (K x))=_ from co_promise O (O-B • step i) _ _ HP i B (kV i) CV.pos _ he]; rw [map_sub, map_add,map_add]; change (_+_ -(_+_):FC (Single N))=_; dsimp only [f,AddMonoidHom.coe_mk,ZeroHom.coe_mk, grantLine,firePlate, gapPlus] -- tune
    unfold Z; abel
 change Matrix.trace ((P'-A)*Ψ) • _+ dg Γ- barS0 N B O x= _; rw [hp,hm, Matrix.trace_add, add_smul]
 unfold blazePlate; unfold Z; abel
include wB
lemma attachLamp_for : houseK p Bτ (puffLine K p O J X B)=houseK p Bτ (frontK P W B O K - (blazePlate K Y+northLine K O T B)):=by
 let L:= frontK P W B O K; let R:= barS0 N B O; funext x; by_cases t:x∈pingMask p Bτ
 · have hl:x∈ pingMask p Θt:= pingMono (offsetFit O O (by rw [separation_self]; omega) wB) t
   have h(i:Axis)(y:Site N)(A:SOp N)(v:separation O y ≤ B): coverLine K p O y A x=grantLine K O y A x:=Set.indicator_of_mem (pingMono (offsetFit O _ v wB) t) _
   have hg:highLine K p O J B x=northLine K O J B x:=by unfold highLine northLine; rw [Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl ?_; intro i _; rw [Pi.sub_apply,Pi.sub_apply, h i _ _ (stopBeam O i B).1, h i _ _ (stopBeam O i B).2]
   rw [houseK,houseK,Set.indicator_of_mem t,Set.indicator_of_mem t,puffLine,Pi.add_apply,houseK,Set.indicator_of_mem hl]; simp only [Pi.sub_apply,Pi.add_apply]; rw [lanternMil_for CV HP kV zV x,hg]; abel -- order?
 rw [houseK,houseK,Set.indicator_of_notMem t,Set.indicator_of_notMem t]

include xP wP hJ hX hY vJ
lemma taught_for : let L:=veilPay l p s h a c b B; let S:=tailPay l p s h a c v B
 Fence P W K p q l (node O) h s (puffLine K p O J X B) (κfront l p s h a c B+S+(L+L)) S:=by
 intro L S; let Yx:=puffLine K p O J X B; let V:=frontK P W B O K; have hp: Fence P W K p q l (node O) h s V (κfront l p s h a c B) 0:= spinPlasma h CV xP wP (windmill O B) (show Soak _ _ a (wζ a B) _ from (show Soak _ _ _ _ _ from windmillCost O B CV.hint.le)) -- tune
 let g:=squarePerk (B:=B) O CV xP wP vJ
 have hz: Fence P W K p q l (node O) h s (houseK p Bτ Yx) (κfront l p s h a c B+S) S:=by
    rw [show houseK p Bτ Yx= _ from attachLamp_for CV HP kV zV wB]; have H:= (hp.sub ((glowTrace h CV hY).arc g)).aft (Subset.refl _)
    rw [zero_add] at H; exact H
 have hv: Fence P W K p q l (node O) h s Yx L L:= (((glowTrace (P:=P) (W:=W) h CV hX.pay).sub (barSale CV xP wP)).aft (offsetFit O O (by rw [separation_self]; omega) wB)).arc (mantlet O CV xP wP wB fun x=> (hJ x).pay)
 have hx: houseK p Bτ Yx+(Yx-houseK p Bτ Yx)=Yx:=by abel
 have HE:= hz.arc (hv.tee (Subset.refl _)); rw [hx,add_zero] at HE; exact HE
end YM.CF.Swell
