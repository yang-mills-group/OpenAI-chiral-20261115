import YM.CF.Liss.Perk
import YM.CF.Robin.Tint
import YM.CF.Liss.Lamp
import YM.CF.Chaff.Mite
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
variable (σ':(LabelΩ I)→ Skye.Seat (mid m B))(C:(LabelΩ I)→(LabelΩ I)→ℂ)(Z a': LabelΩ I→ℂ)
local notation "JΨ"=> Roots.toV_C σ' C
local notation "UV"=> Pane (mid m B)
attribute [-instance] instDecidableEqLex

variable {J J':Type}[Fintype J][LinearOrder J][DecidableEq J'](σ:J→J')(G:J→ Pane (mid m B) → FC (Single (mid m B)))(lM:List J)(C1:J→J→ℂ) -- CV scope.t
variable {YΓ:GramM (mid m B)}
variable (FΩ:Pane (mid m B)→FC (Single (mid m B)))
-- tallyΧ real. addressed moments via Comp across Steps.
abbrev rider_V (G:GramM (mid m B))(H:Grasp D.U B d)(L:Scree.Loom (mid m B)):= tallyT fun i:Orbit (mid m B)=> acts (FΩ i.1) (denZ G H L i)
lemma Ψe_R(v:Pane (mid m B)) : Roots.snow σ C1 (fun l=> pactΦ G l v) lM=pactΦ (blend_C σ G C1) lM v:=by
 induction lM with
 | nil=>rfl
 | cons i l ih=>
    rw [Roots.snow]; let L:=pactΦ (blend_C σ G C1) l v; change _= (∑ j∈pipe_ζ σ i,C1 j i • G j v) * L; rw [Finset.sum_mul]; refine sum_congr rfl fun j _=>?_ ; let A:= G j v; let M:=ContinuousLinearMap.mul ℂ (FC (Single (mid m B))) A
    exact (congrArg (C1 j i • ·) (show Roots.snow σ C1 (fun k=>pactΦ G (j::k) v) l=A * L from (tally_l σ C1 M _ l).trans (congrArg M ih))).trans (smul_mul_assoc ..).symm -- may need F function specify
open Push.SectorMeasure
abbrev draw_k {E:Type}[Fintype E][LinearOrder E](w:Wave E)(M:Wave E→L[ℂ]ℂ): FC E→L[ℂ]ℂ:=
 let A: FC E→ₗ[ℂ] Wave E:= {toFun:= fun x=>acts x w, map_add':=fun _ _=>act_add ..,map_smul':=fun _ _=>act_smul ..}; let T':FC E→L[ℂ] Wave E:={ A with cont:= A.continuous_of_finiteDimensional}; M.comp T'
lemma tally_ρM(lM:List J){E:Type}[Fintype E][LinearOrder E](w:Wave E)(M:Wave E→L[ℂ]ℂ)(F:List J→ FC E):Roots.snow σ C1 (fun l=> M (acts (F l) w)) lM= M (acts (Roots.snow σ C1 F lM) w) := tally_l σ C1 (draw_k w M) F lM
attribute [local instance] loreM loreN boreKSpace boreXN
variable (hc':∀ i, Continuous (G i))(Φ:RG.Envelope (Scree.denZ YΓ X U))
include D Φ hc'
variable (iU:Orbit (mid m B))(F:Pane (mid m B)→FC (Single (mid m B)))
#check rider_V
-- integrate exact read. yields snow composition.Aposter.
lemma tallyΦ :Roots.snow σ C1 (fun l=> rider_V D (pactΦ G l) YΓ X U) lM=rider_V D (pactΦ (blend_C σ G C1) lM) YΓ X U:=by
 let L(l:List J):= pactΦ G l
 let W(x:Orbit (mid m B)):= denZ YΓ X U x
 let P(l:List J)(x:Orbit (mid m B)):= acts (L l x.1) (W x); let M:= (innerSL ℂ (mateK (mid m B)))
 let Q(l:List J)(v:Orbit (mid m B)):= M (P l v)
 have he(v:Orbit (mid m B)):Roots.snow σ C1 (fun i=> Q i v) lM=M (acts (pactΦ (blend_C σ G C1) lM v.1) (W v)):=by
    let X:= draw_k (W v) M; refine Eq.trans (tally_ρM σ C1 lM (W v) M (fun i=>L i v.1)) ?_ ; exact congrArg (fun A=> M (acts A (W v))) (Ψe_R σ G lM C1 v.1)
 have hx(l):RG.Envelope (P l):=by
    have h:=Girt.refill (L l) (pod_C G hc' l) (Prod.fst (α:=Pane (mid m B)) (β:=Ids (mid m B))) measurable_fst -- tune
    exact Girt.kitE _ _ (fun T:FC (Single (mid m B))=> (fun i=>acts T i)) (Continuous.clm_apply (acts_cont.comp continuous_fst) continuous_snd) h Φ
 let V:=city (mid m B); change Roots.snow σ C1 (fun l=>∫ v,Q l v∂V) lM= _; have hp:(∫ x,Roots.snow σ C1 (fun i=> Q i x) lM∂V)=_:= (ζment V σ C1 lM Q (fun i=>(M.restrictScalars ℝ).integrable_comp (Env.integrableX (hx i) _))).2
 exact hp.symm.trans (integral_congr_ae (ae_of_all _ he))
end YM.CF.Liss
#print axioms YM.CF.Liss.tallyΦ
