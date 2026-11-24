import YM.CF.Liss.Cut
import YM.CF.Robin.Rook
import YM.CF.Swell.Vote
import YM.CF.Swell.Chill
import YM.CF.Swell.Beam
import YM.CF.Swell.Hush
import YM.CF.Swell.Harp
import YM.CF.Swell.Lawn
import YM.CF.Swell.Bark
import YM.CF.Swell.Tap
import YM.CF.Swell.Fist
import YM.CF.Mew.Tube
import YM.CF.Pso.Pick
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Liss
open Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow Py
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt Leaf
open Metric Drapes Tulip Lat Branch Cube Tenant Hove Haro Hest Dial Proa Tye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Prism Moto Oath Font Levier Rill
attribute [local instance] loreM loreN boreKSpace boreXN
open Push.AbsoluteSums Trees Wray Ione Fief
variable {N B m L:Side}
variable {r:ℕ}
variable {I:Type}[Fintype I][LinearOrder I]
variable {P:BudgetPoint}(E':GramM (mid m B))
open Neon Hom Vale Vale.Grace Kea Nova RP RP.Str Spark Wilson Precision Next.Free Gauge Paige Vault Brace Spire Pressure Jade Oise
variable {A:Teller SU.group}{W:ChartRatio SU.group}{Zp:Patch}(D:Grace A Zp W){d e g x b a t u0 K Kt f l α s':ℝ}
variable {X: Grasp D.U B d}{U:Loom (mid m B)}(R: Roof (mid m B) a e r U)(gP:P.threshold ≤ a)(φp:0<e)(hκ:X.roundZ ≤ (mid m B).val)(hp:e ≤ d)
variable {b0 M0 A0 s ε c γ tQ θQ:ℝ}
variable (hpS:e≤ 1)(hτ:r+10 ≤ P.B)(hΨ:cipherK r ≤5*P.B)(pΨ:HopeT e b t P.order)(hk:P.threshold ≤ t)
variable (gB:10≤ P.B)(h_B:20 < (More (mid m B)).val)(h_X:3 ≤ (mid m B).val)(tΔ: P.threshold=temp x)
open Roots
local notation "iX"=> LabelΩ I
variable (Q h:ℝ)(O:I→Site (mid m B)) -- trim T
variable (σ':(LabelΩ I)→ Seat (mid m B))(C:(LabelΩ I)→(LabelΩ I)→ℂ)(Z a': LabelΩ I→ℂ)
local notation "JΨ"=> Roots.toV_C σ' C
local notation "UV"=> Pane (mid m B)
attribute [-instance] instDecidableEqLex
abbrev holdF (V:Pane (mid m B))(j:LabelΩ I):FC (Single (mid m B)):= (Lull_o (P:=P) Q h O j V-Z j) • (1:FC (Single (mid m B)))+ soundΓ (studΨ O Q h j) V
#check holdF
abbrev ηPhi (V:Pane (mid m B))(j:LabelΩ I):FC (Single (mid m B)):= a' j • (1:FC (Single (mid m B)))+∑ i∈pipe_ζ σ' j,C i j • holdF (P:=P) Q h O Z V i
lemma Φmilk (V:Pane (mid m B))(z:Key (LabelΩ I)) : let F:=Lull_o (P:=P) Q h O; (Neon.α_ξ a' z-Neon.α_ξ Z (Roots.toV_C σ' C z)+filmτ F (Roots.toV_C σ' C z) V) • (1:FC (Single (mid m B))) +Mlaw (studΨ O Q h) (Roots.toV_C σ' C z) V= waveΦ (ηPhi (P:=P) Q h O σ' C Z a' V) z:=by
 let D:=holdF (P:=P) Q h O Z V; let L:=Lull_o (P:=P) Q h O; let q':=Roots.toV_C σ' C z; intro F; unfold waveΦ ηPhi; change _=∑ i:(LabelΩ I),z i • (a' i • (1:FC (Single (mid m B)))+∑ k∈pipe_ζ σ' i,C k i • D k); rw [sum_congr rfl (fun i _=> smul_add (z i) _ _),sum_add_distrib]; have hp:(∑ j: (LabelΩ I),z j • ∑ i∈pipe_ζ σ' j, C i j • D i)=∑ j,q' j • D j:=by
    simp_rw [smul_sum,smul_smul,pipe_ζ,sum_filter]; rw [sum_comm]; refine sum_congr rfl fun i _=>?_; change _=(∑ j∈ pipe_ζ σ' i,_) • D i; unfold pipe_ζ; rw [sum_smul,sum_filter]; refine sum_congr rfl fun j _=>?_ ; split_ifs with h u v; rw [mul_comm]; exact False.elim (u h.symm); exact False.elim (h v.symm); rfl
 change _=_+ ∑ j:LabelΩ I,z j • ∑ i∈pipe_ζ σ' j, C i j • D i; rw [hp]; unfold D holdF; simp_rw [smul_add,sum_add_distrib]; have hv:(∑ j:LabelΩ I,q' j • ((L j V-Z j) • (1:FC (Single (mid m B)))))= (filmτ L q' V-Neon.α_ξ Z q') • (1:FC (Single (mid m B))):=by unfold filmτ α_ξ; rw [←sum_sub_distrib,sum_smul]; refine sum_congr rfl fun j _=>?_ ; rw [smul_smul,mul_sub]
 simp_rw [smul_smul (z _)]; rw [hv]; unfold Mlaw; rw [←sum_smul, ←add_assoc, ←add_smul]; rw [show Neon.α_ξ a' z- Neon.α_ξ Z q'+filmτ F q' V= Neon.α_ξ a' z+ (filmτ F q' V-Neon.α_ξ Z q') from by abel] -- possible no match
lemma φΞk(V: Pane (mid m B)) (i j:(LabelΩ I)):Commute (ηPhi (P:=P) Q h O σ' C Z a' V i) (ηPhi (P:=P) Q h O σ' C Z a' V j):=by
 let U:= (muskPΓ <| studΨ O Q h j); let B'(i:LabelΩ I):= muskPΓ (studΨ O Q h i) V
 let X:=Emu.halfS (mid m B); have hp(i):gradingXp X (B' i):=by
    have he:=sCap (h:=h) (Eraρ Q) (tiν i); let T:= cue_Φ (Eraρ Q) h (tiν i); have hz:=  -- edit
       show Branded (xΞ O i) (B' i) from bornT (xΞ O i) _ (tap_Ψ _ T.2 (Bud_A _ he)) _ -- signature
    exact fun x y p=>⟨(hz x y p).1,(hz x y p).2.1⟩
 unfold ηPhi; apply Commute.add_left; exact (Commute.one_left _).smul_left _; apply Commute.add_right; exact (Commute.one_right _).smul_right _; refine Commute.sum_left _ _ _ (fun k _=> Commute.smul_left (Commute.sum_right _ _ _ (fun i p=>?_)) _) -- smul_left arg
 let U:= holdF (P:=P) Q h O Z V
 change Commute (U k) (_ • U i); apply Commute.smul_right; unfold U holdF; apply Commute.add_left; exact (Commute.one_left _).smul_left _; apply Commute.add_right; exact (Commute.one_right _).smul_right _; exact pop _ _ _ (hp k) (hp i)
#check Bud_A
variable (G:GramM (mid m B))(Zk:Scree.Loom (mid m B)) (Y: Grasp D.U B d)
variable (F':Mew.Key (LabelΩ I)→ RegBudget (mid m B))
variable (v':∀ z∈hill (LabelΩ I),∀ k:ℂ,∀ i:Orbit (mid m B),Rue.FleetS P.threshold i.1→ let z':=Roots.toV_C σ' C z; let Ω:= k-Neon.α_ξ Z z'+filmτ (Lull_o (P:=P) Q h O) z' i.1; denZ (shotτ G (F' z) k) Y Zk i=acts (exp (Ω • (1:FC (Single (mid m B)))+Mlaw (studΨ O Q h) z' i.1)) (denZ G Y Zk i))
set_option maxHeartbeats 400000 in
lemma votM {I E:Type}[Fintype I][LinearOrder I][Fintype E][LinearOrder E](H:I→FC E)(hp:∀ i j, Commute (H i) (H j))(x:Wave E)(l:List I)(p:l.Nodup): tipI (fun z:Key I=> acts (κtag H z) x) l=acts (l.map H).prod x:=by
 let A:FC E→ₗ[ℂ] Wave E:= {toFun:=fun P=>acts P x, map_add':=fun _ _=>act_add .., map_smul':=fun _ _=>act_smul ..}; let L:FC E→L[ℂ] Wave E:={ A with cont:=A.continuous_of_finiteDimensional}
 change tipI (L ∘ κtag H) l= L ((l.map H).prod); rw [← ΘXtip H hp l p]; exact sim_H (hx_H H hp) L l roots
include v'
abbrev σKΛ (s:List (LabelΩ I))(V:Pane (mid m B)):FC (Single (mid m B)):= (s.map (ηPhi (P:=P) Q h O σ' C Z a' V)).prod
set_option maxHeartbeats 1800000 in
lemma lampΞ (x:Orbit (mid m B))(u:Rue.FleetS P.threshold x.1)(l: List (LabelΩ I))(p:l.Nodup) :tipI (fun z: Key (LabelΩ I)=> Scree.denZ (color_b G G.beta (G.F+F' z) G.slip G.K (G.v+Neon.α_ξ a' z)) Y Zk x) l= acts (σKΛ (P:=P) Q h O σ' C Z a' l x.1) (denZ G Y Zk x):=by
 let H(i):=ηPhi (P:=P) Q h O σ' C Z a' x.1 i; let U:=κtag H; have hz:Set.EqOn (fun z:Key (LabelΩ I)=>Scree.denZ (color_b G G.beta (G.F+F' z) G.slip G.K (G.v+Neon.α_ξ a' z)) Y Zk x) (fun z=>acts (U z) (denZ G Y Zk x)) (hill (LabelΩ I)):=by
    intro z v; refine Eq.trans (v' z v (Neon.α_ξ a' z) x u) ?_ ; exact congrArg (fun v: FC (Single (mid m B))=> acts (exp v) (denZ G Y Zk x)) (Φmilk (P:=P) Q h O σ' C Z a' x.1 z)
 have he:=votM H (φΞk (P:=P) Q h O σ' C Z a' x.1) (denZ G Y Zk x) l p
 change tipI (fun z:Key (LabelΩ I)=> Scree.denZ (color_b G G.beta (G.F+F' z) G.slip G.K (G.v+Neon.α_ξ a' z)) Y Zk x) l= _; exact Eq.trans (lace_C l hz roots) he
end YM.CF.Liss
#print axioms YM.CF.Liss.lampΞ
