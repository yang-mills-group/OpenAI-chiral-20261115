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
namespace YM.CF.Swell
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
abbrev shotτ (Y:GramM (mid m B))(T:RegBudget (mid m B))(c:ℂ):= color_b Y Y.beta (Y.F+T) Y.slip Y.K (Y.v+c)
structure Basal_G (D:Grace A Zp W) (Y:GramM (mid m B))(P:BudgetPoint):Prop where
 boot : ∃ E:RegBudget (mid m B),∃ s:ℝ, Y= Chaff.fulvia E s (Vale.launch D.L Y.beta P (mid m B))
abbrev muskPΓ (M:SOp (mid m B))(U:Pane (mid m B)):Op (Single (mid m B)):=M (profile U)
def soundΓ (M:SOp (mid m B))(V: Pane (mid m B)): FC (Single (mid m B)):=dg (muskPΓ M V)
structure Leg_P (P:BudgetPoint)(E:RegBudget (mid m B))(pM:SOp (mid m B))(Q:Orbit (mid m B)→ Cipher (mid m B))(xM: Loom (mid m B))(ι:SOp (mid m B)):Prop where
 η(V:Orbit (mid m B)): Rue.FleetS P.threshold V.1 →flags P.threshold V.1=∅→ Q V=exponentL P E V.1
-- calibrate PH & Φ separately.
variable (S:I→ SOp (mid m B))(Kp:I→ Bag (mid m B))(Vx:I→ Aura (mid m B)→ℝ)(p:I→ RegBudget (mid m B))(o:I→ Site (mid m B))
variable (H L' Γ γ:ℝ)
structure Provider_S (i:I) : Prop where
 kernel: Blip_o (node (o i)) (Kp i) (Vx i) P r H Γ L'
 theory(X:Orbit (mid m B)): let y:=U X; let W:= muskPΓ (S i) X.1; let Ψ:= spar A.j babyM y; flags P.threshold X.1=∅→ (∑ Y:Aura (mid m B),Kp i Y X)=Sault.forge (Ψ*W) W (W*(1-Ψ)) (Ψ*W) (Ψ * W*(1-Ψ))
 pay(X:Orbit (mid m B)): let W:=muskPΓ (S i) X.1; Rue.FleetS P.threshold X.1→ flags P.threshold X.1=∅→ exponentL P (p i) X.1=hollow (Matrix.trace (spar A.j babyM (U X)* W))
variable (V':GramM (mid m B))(Y': Basal_G D V' P)(xσ:∀ i:I,Provider_S (P:=P) (A:=A) (r:=Rill.cipherK r) (U:=U) S Kp Vx p o H L' Γ i)
lemma roll_name(B:FC (Single N))(Y:ℂ)(x:Wave (Single N)): Complex.exp Y • acts (exp B) x=acts (exp (Y • 1+B)) x:=by rw [Sault.vert,act_smul]
abbrev filmτ(s:I→ Pane (mid m B)→ℂ)(v:Mew.Key I)(X:Pane (mid m B)):ℂ:=∑ i,v i*s i X
abbrev Mlaw(w:Mew.Key I)(X:Pane (mid m B)):FC (Single (mid m B)):= ∑ i:I,w i • soundΓ (S i) X
variable (T_h:Teller SU.group) -- scratch
variable (E:Aura (mid m B)→ Copy (mid m B))(J:Aura (mid m B)→ℝ) (pE:∀ i, Span_K P H i (E i) (J i)) (htE:Bake.Turf E)
variable (B':Ids (mid m B))(vH:1 ≤ H)(hB:3 ≤ P.B)
variable {ε θ r' ℓ:ℝ}{K0 w HX c u vℝ hτ:ℝ}
variable (Yκ:Tax_R (V_S (Leaf.σ_H (κsum Vx)) J) (Leaf.σ_H (κsum Vx)) (widthK (mid m B) P.B) K0 ℓ w HX c u vℝ)
variable (Θ A':ℝ)(h0:0 ≤ Θ+A')(h_W:0 < A')(h_κ: Θ+A'+1≤ℓ-w) -- ℓ undeclared
abbrev R_mk (z:Mew.Key I) : RegBudget (mid m B):= Υarc E Kp Vx (fun i=>(xσ i).kernel.chant) z B'
variable (hEY: ∀ V:Orbit (mid m B), Rue.FleetS P.threshold V.1→flags P.threshold V.1=∅→ exponentL P V'.F V.1=∑ X:Aura (mid m B),E X V)
variable (F0:I→ RegBudget (mid m B)) (q0:I→ Pane (mid m B)→ℂ)(H0:∀ i,∀ V:Orbit (mid m B),Rue.FleetS P.threshold V.1→flags P.threshold V.1=∅→ exponentL P (F0 i) V.1=Hest.boat (muskPΓ (S i) V.1)+hollow (q0 i V.1)) -- combine F0 gauges canonical.TΘ
local notation "FI"=> (mid m B)
abbrev Raw_X(z:Mew.Key I):RegBudget (mid m B):=EraT F0 z+ EraT p z+Υarc E Kp Vx (fun i=>(xσ i).kernel.chant) z B'
#check Raw_X
section Rig
include R Y' hp φp hκ
lemma crest_M (T:RegBudget (mid m B))(k:ℂ)(u:Orbit (mid m B))(vb:Rue.FleetS P.threshold u.1) :
 let G:=shotτ V' T k; let W:=spar A.j babyM (U u); let p:= flags P.threshold u.1; let Q:=V'.J;
 let Y:=changeM X (U u) babyM; G.betaL U u = V'.betaL U u+k ∧ (p ≠∅→ denZ G X U u=0)∧(p=∅ → denZ G X U u=Complex.exp (G.betaL U u) • acts (tank W (exp (exponentL P V'.F u.1+exponentL P T u.1))) Y):=by
 intro G W p Q Y; have ht:Guard (U u) d:= (R.paid u).shrink hp; have hk:IsStarProjection W:=(X.broadness _ hκ _).projection _ ht; obtain ⟨F,s,hY⟩:=Y'.boot; have he:V'.K= 0∧V'.slip= 0∧V'.J= vanilla (mid m B) ∧V'.p=P:=by rw [hY]; exact ⟨rfl,rfl,rfl,rfl⟩
 obtain ⟨x₁,x₂,x₃,x₄⟩:=he
 have hG:relV X G.J (U u)=changeM X (U u) babyM:=by unfold G shotτ; change relV X V'.J _=_; rw [x₃]; exact curtain X _ U ({R with paid:=fun z=> (R.paid z).shrink hp}:Roof (mid m B) a d r U) hκ _
 have hp0:W=spar A.j G.J.M (U u):=by unfold W G shotτ; change _=spar _ V'.J.M _; rw [x₃]; rfl
 have hx:G.board u= exp (exponentL P (V'.F+T) u.1+exponentL P 0 u.1)*fueled P 0 u:=by change exp (exponentL V'.p (V'.F+T) u.1+exponentL V'.p V'.slip u.1)*fueled V'.p V'.K u=_; rw [x₄,x₁,x₂]
 refine ⟨?_,fun h=>?_ ,fun q=>?_⟩
 · unfold GramM.betaL G shotτ; unfold GramM.H0; dsimp only [Oise.color_b]; abel
 · rw [denZ,hx,still_force P _ h,mul_zero,←hp0,tank_eq _ _ hk, map_zero, act_zero,smul_zero]
 rw [denZ,hx,fuel_one P 0 u q,mul_one,still_Footprint,add_zero, Larch.ripe_H, hG,hp0] -- tune.PT.yep
omit R Y' hp φp hκ
lemma shot_0 : shotτ V' 0 0 = V':=by simp [shotτ, Oise.color_b]
lemma tail_d(X:Op (Single (mid m B)))(e:ℂ)(S: Cipher (mid m B)) (x:IsStarProjection X): tank X (exp (S+hollow e))=Complex.exp e • tank X (exp S):=by
 rw [tank_eq _ _ x, tank_eq _ _ x, add_comm, Pastry.expReal,Poly.rising] -- name
variable(z:Mew.Key I)(hz:z∈hill I)(k':ℂ)(V:Orbit (mid m B))(v:Rue.FleetS P.threshold V.1)(f':flags P.threshold V.1=∅)
include xσ f'
lemma vir_Q : let M:=spar A.j babyM (U V); Qo (τlens Kp z) V=∑ i:I, let Y:=muskPΓ (S i) V.1; z i • Sault.forge (M*Y) Y (Y*(1-M)) (M*Y) (M*Y*(1-M)):=by
 intro M; unfold Qo τlens; rw [sum_comm]; apply sum_congr rfl; intro i p; rw [←smul_sum, show (∑ x:Aura (mid m B),Kp i x V)= _ from (xσ i).theory V f']
include H0 v hB hz vH
lemma run_S : let Z:= θlens Kp Vx (fun i=>(xσ i).kernel.chant) z; ∑ i:Aura (mid m B),ξA Z i V=exponentL P (EraT F0 z+ EraT p z) V.1-hollow (filmτ q0 z V.1):=by
 intro Z; let T:= paceΨ vH Kp Vx (fun i=>(xσ i).kernel.chant) z hz hB; let M:=spar A.j babyM (U V); let W(i:I):=muskPΓ (S i) V.1; let N(i):= M*W i
 let L i:= Sault.forge (N i) (W i) (W i*(1-M)) (M*W i) (M*W i*(1-M)); let Vκ:=Qo (τlens Kp z) V; have he:Vκ=∑ i,z i • L i:=vir_Q S Kp Vx p o H _ Γ xσ z V f'
 let V'':=∑ i:I, z i • (Hest.boat (W i)+hollow (Matrix.trace (N i)))
 have hW(i:I): Sault.rind (L i)=(Hest.boat (W i)+hollow (Matrix.trace (N i))).val:=by
    apply Sault.sky (Sault.skit _) (fineShape _).allP; rw [Sault.tileL]; exact Sault.air ..
 have hp: (∑ i:Aura (mid m B),ξA Z i V)=V'':=by
    apply Subtype.ext; change (Dough (Dwell (mid m B))).val _=(Dough (Dwell (mid m B))).val V''; have hz':V''=∑ i,z i • (Hest.boat (W i)+hollow (Matrix.trace (N i))):= rfl
    rw [map_sum,hz',map_sum]; trans Sault.rind Vκ
    · unfold Vκ Qo Sault.rind; rw [map_sum]; exact sum_congr rfl fun i _=>Leaf.Ω_Q Z T vH V v f' i
    unfold Sault.rind; rw [he,map_sum]; refine sum_congr rfl fun i _=>?_ ; rw [map_smul ((Pastry.cane _).eval)]; exact congrArg (z i • ·) (hW i) -- tune
 rw [hp, Larch.ripe_H]; unfold EraT filmτ V''; simp_rw [Neon.e_s_K P _ _ V, Neon.voc_E _ _ _ V, H0 _ V v f',show ∀ i:I,exponentL P (p i) V.1=hollow (Matrix.trace (N i)) from fun i=> (xσ i).pay V v f',smul_add,sum_add_distrib]
 let C'':= ∑ i:I,z i • (Pastry.hollow (n:=LeanV (Single (mid m B))) (q0 i V.1)); rw [← Chaff.drillL]; have hc : C''=∑ i:I, Pastry.hollow (z i*q0 i V.1):=by apply sum_congr rfl; intro i _; apply Subtype.ext; exact (smul_smul ..)
 change _= (_+C''+_)- _; rw [hc]; unfold W; abel
omit f'
include R gP φp hκ hp vH hB pE htE Yκ Y' h_W h0 h_κ hEY
lemma meterX :
 let G:=shotτ V' (Raw_X S Kp Vx p o H L' Γ xσ E B' F0 z) k'; let W:= (k'+filmτ q0 z V.1) • (1:FC (Single (mid m B))); denZ G X U V=acts (exp (W+Mlaw S z V.1)) (denZ V' X U V):=by
 intro G Lx; have hz0:= crest_M D R φp hκ hp V' Y' 0 0 V v; dsimp only at hz0; rw [shot_0] at hz0; let U':= Raw_X S Kp Vx p o H L' Γ xσ E B' F0 z; have hG:= crest_M D R φp hκ hp V' Y' U' k' V v
 by_cases y:flags P.threshold V.1=∅; swap; · rw [show denZ G X U V=0 from hG.2.1 y,hz0.2.1 y,map_zero]
 let W:= U V; let Q:= spar A.j babyM W; have heW:Guard W d:= (R.paid _).shrink hp; have hQ:IsStarProjection Q:=(X.broadness _ hκ _).projection W heW
 let Z:=θlens Kp Vx (fun i=>(xσ i).kernel.chant) z; let M:= Qo (τlens Kp z) V; let Tz:= nursery Q hQ; let Y:=changeM X W babyM; let L:= (ballL Tz Y).toContinuousLinearMap
 let Kb(i:I):= muskPΓ (S i) V.1; let Vg(i:I):=Sault.forge (Q*Kb i) (Kb i) (Kb i*(1-Q)) (Q*Kb i) (Q*Kb i*(1-Q)); have hZ: M= ∑ i:I,z i • Vg i:=vir_Q S Kp Vx p o H L' Γ xσ z V y
 let kB:=Mlaw S z V.1; have hp': rank2 M:=by rw [hZ]; exact Leaf.δX _ _ fun i _=>Leaf.ψX _ _ (Leaf.ore2 _ _ _ _ _)
 have hw(v:Wave (LeanV (Single (mid m B)))):L (acts M v)=acts kB (L v):=by rw [hZ,act_sum,map_sum,show kB= _ from (show kB= ∑ i:I,z i • soundΓ (S i) V.1 from rfl),act_sum]; refine sum_congr rfl fun i _=>?_ ; rw [act_smul,map_smul,act_smul]; exact congrArg (z i • ·) (Sault.loft hQ (Kb i) Y (Spire.sea_g hκ W heW babyM) v)
 let σ:=Cube.node ∘ o; let q' := filmτ q0 z V.1; let V0:=Υarc E Kp Vx (fun i=>(xσ i).kernel.chant) z B'; let J':= exponentL P V'.F V.1; let s:=∑ i:Aura (mid m B), ξA Z i V; let G':=J'+s+exponentL P V0 V.1
 have hK:= run_S S Kp Vx p o H L' Γ xσ vH hB F0 q0 H0 z hz V v y -- order
 have he:J'+exponentL P U' V.1=G'+hollow q':=by unfold U'; rw [Raw_X, Larch.ripe_H, ← show _= exponentL P (EraT F0 z +EraT p z) V.1 from ((eq_sub_iff_add_eq).mp (show s= _ from hK))]; unfold G' V0 q'; abel -- tune
 have ht:L (acts (exp G').val (vacuum _))=acts (exp kB) (L (acts (exp J').val (vacuum _))):=by
    unfold G' J'; rw [hEY V v y]; exact (Ψgin vH E J pE V v y Kp Vx (fun i=>(xσ i).kernel.chant) z hz σ (fun i X t=> ((xσ i).kernel.pays _ t).1) B' (fun i=> (xσ i).kernel.eats) htE Yκ Θ A' h_W h0 h_κ hB L kB hw hp').2
 have hu(v:Cipher (mid m B)): acts (tank Q v) Y= L (acts v.val (vacuum _)):= (Sault.loaf Tz Y v.val).symm
 let R':= V'.betaL U V; rw [show G=shotτ V' U' k' from rfl,hG.2.2 y,hz0.2.2 y,hG.1,show exponentL P V'.F V.1+_=_ from he,still_Footprint,add_zero]; change Complex.exp (R'+k') • acts (tank Q (exp (G'+hollow q'))) Y=acts (exp ((k'+q') • 1+kB)) (Complex.exp R' • acts (tank Q (exp J')) Y); rw [tail_d Q q' G' hQ, act_smul,hu,hu,ht,map_smul,←roll_name]; simp only [smul_smul]; congr 1; rw [←Complex.exp_add,←Complex.exp_add]; congr 1; ring
end Rig
end YM.CF.Swell
#print axioms YM.CF.Swell.meterX
