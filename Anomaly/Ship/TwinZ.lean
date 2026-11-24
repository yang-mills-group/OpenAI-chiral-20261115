import Anomaly.Ship.Twine
import Anomaly.Apert.Price
import Anomaly.Ship.Salary
import Anomaly.Ship.Tines
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py.Rate.BScale Nor Mew PowerSeries
open scoped Mew

variable {n:Side} {I:Type} [LinearOrder I] [Fintype I]
set_option maxHeartbeats 450000
variable {P:BudgetPoint} {q:ℕ} {h:ℝ}
open Neon Bake Rive QuadClock Stilo Roots
-- earned Root-v keyed regulator rep. Analytic both fresh and old together.
-- expose First pins on separated Θ tests
variable {N B:Side}
local notation "Fᴷ" => mid N B
variable {A:Key I→ I→ Bag (mid N B)}
variable {a b: Key I→I→ Aura (mid N B)→ℝ} {K:Key I→ForceBudget (mid N B)}
variable (H:∀ z∈hill I,∀ i:I,∀ X:Aura (mid N B),Flight P q X h (A z i X) (a z i X) (b z i X))
variable {D:Finset I}{σ:I→Site (mid N B)}{Ω:Occlus P}
variable (T: Crews D K (Cube.node∘σ) Ω A H) (u:1≤ h)
local notation "Θ"=>presse H
variable(m:ℕ)
local notation "YX" x:max=> lensCells (K x) (Θ x) m
local notation "Yφ" x:max=> lensG (P:=P) (K x) (Θ x) m
local notation "Aφ"=> (P.supportExponent+Ω.η+Ω.η)
local notation "Vφ"=> (Aφ+Ω.η)
local notation "Sσ"=>Cube.node∘σ
-- Solves First tips by identity along antler split.
local notation "YN" z:max=> (Yφ z) z
namespace Crews
include T
lemma hold_H (x w:Key I)(p:x∈hill I)(r:w∈hill I): Θ (antler D x w) (antler D x w) = Θ x w:=by
 let X:=antler D x w; let l:= antler_c D x w p r
 funext B Z Y; apply press_eq _ _ _ _ _ _ _ _ l p; unfold pinSeries; refine sum_congr rfl fun i _=>?_
 by_cases g:i∈D
 · rw [show A (antler D x w)=A x from Dorm.arg _ _ T.noise x w p r l, show antler D x w i=w i from if_pos g]
 rw [T.zeroV i g _ l,T.zeroV i g _ p]; simp
lemma pucks (x w:Key I)(p:x∈hill I)(r:w∈hill I) : let A':= antler D x w; (YX A') A'= (YX x) w:=by
 intro Y; have hp:K Y=K x:= Dorm.arg D K T.silent x w p r (antler_c D x w p r) -- tune
 unfold lensCells; rw [hp, show Θ Y Y= Θ x w from hold_H H T x w p r]
lemma hold_F (x w:Key I)(p:x∈hill I)(r:w∈hill I): YN (antler D x w)=(Yφ x) w:=by
 let h:=pucks H T m x w p r; exact congrArg (fun K:Cusp Fᴷ=>FeeD P (fun i:Aura Fᴷ=>K i (∅:Support (More Fᴷ)))) h -- inference annotate
lemma voluble(w:Key I)(v:w∈hill I):Turf ((Yφ w) w):=by obtain ⟨a,b,r,R⟩:= T.wing w v; exact turfK _ (R.plain w m)
lemma quiet0 (x:Key I)(p:x∈hill I) : (Yφ x) 0=0:=by -- notation
 obtain ⟨a,b,r,R⟩:= T.wing x p; have hv:lensSimple (K x) (Θ x) m 0=0:=by unfold lensSimple; rw [R.empty]; exact funext (settle0 _)
 unfold lensG; rw [hv]; exact funext (costBright P)
lemma first_tip (i:I) : τι (fun z:Key I=> (Yφ z) z) [i]= τι (lensG (P:=P) (K 0) (Θ 0) m) [i]:=by
 funext X W; unfold τι tipI; dsimp only [lance,cutI]; apply MeasureTheory.integral_congr_ae; filter_upwards with t
 let x:= update (0:Key I) i (homeB t); have hp:x∈hill I:=fill_I roots i (homeC t) -- syntax
 by_cases p:i∈D
 · have h:antler D (0:Key I) x=x:=funext fun j=>by
      by_cases u:j∈D; · exact if_pos u
      unfold antler; rw [if_neg u]; exact (update_of_ne (show j≠ i from fun v=>u (v ▸ p)) ..).symm
   have ht: (Yφ x) x= (Yφ 0) x:= by have ht:= hold_F H T m 0 x roots hp; rw [h] at ht; exact ht -- tune rewrite also x
   exact congrArg (((homeB t)⁻¹:ℂ) • ·) (congrFun (congrFun ht X) W)
 -- `old only` Key. then Yφ relative source both cases.ZERO
 have hZ{t:Key I}(h:t∈hill I) : Θ t x= Θ t 0:=by
    funext V S K; apply press_eq H _ _ _ _ _ _ _ h h; unfold pinSeries; refine sum_congr rfl fun j w=>?_
    by_cases u:j=i; · rw [u, T.zeroV i p _ h]; simp
    rw [show x j=(0:Key I) j from update_of_ne u ..]
 have he{t:Key I}(h:t∈hill I):(Yφ t) x=0:=by unfold lensG lensSimple; rw [hZ h]; exact quiet0 H T m _ h
 have ht:(Yφ x) x=(Yφ 0) x:=by rw [he hp,he roots]
 exact congrArg (((homeB t)⁻¹:ℂ) • ·) (congrFun (congrFun ht X) W)
variable(G: I→ Cusp (mid N B))
local notation "KΩ" x:max=> mkCup P (K x) (Θ x) m G
local notation "ψN" x:max=>(KΩ x) x- (KΩ x) 0
variable (e:∀ i∉D,G i=0)
include u e
lemma stagger(x w:Key I)(g:x∈hill I)(p:w∈hill I) : let z:=antler D x w; (KΩ z) z=(KΩ x) w∧ (KΩ z) 0=(KΩ x) 0:=by
 intro z; let t:=antler_c D x w g p; have hq:=pucks H T m x w g p
 have ht:Φstack G z=Φstack G w:=by
    refine sum_congr rfl fun i _=> ?_; by_cases s:i∈D; · rw [show z i=w i from if_pos s]
    rw [e i s]; simp
 constructor
 · have hF: lensSimple (K z) (Θ z) m z=lensSimple (K x) (Θ x) m w:= congrArg (fun K:Cusp Fᴷ=> fun i:Aura Fᴷ=> K i ∅) hq; unfold mkCup; rw [hF,show (YX z) z=(YX x) w from hq,ht]
 obtain ⟨a,b,r,R⟩:= T.wing z t; obtain ⟨a,b,r,S⟩:=T.wing x g
 rw [budget_genesis (Θ z) _ _ R m G u,budget_genesis (Θ x) _ _ S m G u, Dorm.arg D K T.silent x w g p t] -- tune press Θ notation
open QuadClock Py
lemma leafTip (i:I) : emberTip (fun z:Key I=> ψN z) i=emberTip (KΩ 0) i:=by
 funext X V; let F:= (KΩ 0)
 have hz: tipI (fun z:Key I=> (F z-F 0) X V) [i]=tipI (fun z:Key I=> F z X V) [i]:=by
    obtain ⟨a,b,r,R⟩:= T.wing 0 roots; let f:=fun z v Y=>pinSeries (A 0) z Y v
    have hX(i:Aura Fᴷ)(D:Support (More Fᴷ))(v:Orbit Fᴷ):River (fun z:Key I=> Φstack G z i D v):=by unfold Φstack; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact rer_C _
    have ht:River (fun z:Key I=> F z X V):= bScale _ (moto_R (P:=P) (YX 0) (Φstack G) (layerRay Ω (K 0) (Θ 0) Sσ q f R m u) (fun i j _=>hX i j) (lensSimpleR Ω (K 0) (Θ 0) Sσ q f R m u) _ _ V) _
    simp only [Pi.sub_apply]; rw [Neon.tip_M ht (zeroR (F 0 X V)),show tipI (fun z:Key I=>F 0 X V) [i]=0 from (mitt (zeroR (I:=I) (F 0 X V)) roots i).unique (hasDerivAt_const ..), sub_zero]
 change tipI (fun z:Key I=> (ψN z) X V) [i]= _; refine Eq.trans ?_ hz; dsimp only [tipI,Mew.lance,cutI]; refine MeasureTheory.integral_congr_ae ?_; filter_upwards with t
 let z:= update (0:Key I) i (homeB t); let hp:z∈hill I:=fill_I roots i (homeC t)
 by_cases p:i∈D
 · have h:antler D 0 z=z:=funext fun j=>by
      by_cases v:j∈D; · exact if_pos v
      unfold antler; rw [if_neg v]; exact (update_of_ne (show j≠ i from fun u=>v (u ▸ p)) ..).symm
   let g:= stagger H T u m G e 0 z roots hp; dsimp only at g; rw [h] at g
   exact congrArg (fun v:ForceBudget Fᴷ=> (homeB t)⁻¹ • v X V) (congrArg₂ (·-·) g.1 g.2)
 have h:antler D z 0=z:=funext fun j=>by
    by_cases v:j∈ D; swap; exact if_neg v
    unfold antler; rw [if_pos v]; exact (update_of_ne (show j≠i from fun u=>p (u ▸ v)) ..).symm
 have hz2:antler D 0 z=(0:Key I):=funext fun j=>by
    unfold antler; split
    next v => exact update_of_ne (show j≠i from fun e=>p (e ▸ v)) ..
    rfl
 have Gt:= stagger H T u m G e z 0 hp roots; have R':=stagger H T u m G e 0 z roots hp; dsimp only at Gt R'; rw [h] at Gt; rw [hz2] at R'
 have he:(KΩ z) z-(KΩ z) 0=(KΩ 0) z-(KΩ 0) 0:=by rw [Gt.1,← R'.1,sub_self,sub_self]
 exact congrArg (fun v:ForceBudget Fᴷ=>(homeB t)⁻¹ • v X V) he
end Crews
end YM.CF.Vow.TreasuryFog
