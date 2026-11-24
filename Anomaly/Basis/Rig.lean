import Anomaly.Basis.Dust
import Anomaly.Basis.Tuft
import YM.SU5.Exchange.Stack.Trestle
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow.TreasuryFog
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tenant Tulip
open Pastry Hake Peaks Fock Branch Drapes Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Palot Cadre Rill Stax Rive Ione Larch Roots Push.AbsoluteSums.Trees Sour Py Py.Rate.BScale Mew PowerSeries
open scoped Mew
open Swell Porticus Tye Bake Neon Pressure Sault Hest
variable {N B n':Side} {P:BudgetPoint} {h v w s:ℝ} {q k m L':ℕ}
local notation "θ" => mid N B
local notation "I"=> Single θ
open Buffered
variable {K:Scree.Loom (mid N B)}{t d a b φ f g₀ x₀:ℝ} {o:Site (mid N B)}{δ C:ℝ}
local notation "Ω"=> (a+a)
open Oath Kennel
structure Channel (P:BudgetPoint)(K:Scree.Loom (mid N B))(t d h s a φ f x:ℝ)(m k q r:ℕ):Prop where
  helm:DockPulse P K t d a h s m q
  cap:axleCap m^3<r
  leaf:16+1+10+q≤ m*P.B
  rad:k+q+10≤P.B
  step:1≤ m
  edg:d≤1
  bank:P.supportExponent+8/(P.B:ℝ) ≤ s
  room:∃ g:ℝ,HopeT d g x P.order
  scent: Sonar.mintQ φ f d P.order
  vV:P.threshold≤ x
  trust:∃ R:Next.Rank.Spindle.Rules SU.group,4*(k:ℝ)*P.threshold≤R.c
  high:2*(k+1)<(More (mid N B)).val
  tap:8*(k:ℝ)*P.threshold < φ
  GalaP:∃ y:ℝ, Gala P.power P.order 100 y 3 ∧1 ≤ Pressure.radiusB y∧ P.threshold=temp y

-- precise envelope retained.R weights. rate. variables chosen to normalize uniformly.
abbrev αlife (a d v:ℝ):ℝ:= νt a d 16*(Haro.horn*v)
abbrev stemLoan (A b d v:ℝ):ℝ:= levPrice A b (αlife A d v)
abbrev flightLoan (A b d v:ℝ):ℝ:= stemLoan A b d v+αlife A d v
abbrev scanLoan (A b d v:ℝ):ℝ:= 2*(b* stemLoan A b d v)
abbrev lowLoan (A b d v:ℝ):ℝ:= 2*(stemLoan A b d v*(Real.exp A+b))
abbrev lowScan (A b d v:ℝ):ℝ:=2*(scanLoan A b d v*(Real.exp A+b))
abbrev spillCost (p:BudgetPoint)(k m:ℕ)(b a s h:ℝ) := Nor.reserveT p.power p.order p.B (p.B:ℝ)⁻¹*|spill_F p k m b a s h|
abbrev fireCost (C:BudgetPoint)(k:ℕ)(h b a f x:ℝ):ℝ := (haloSites k:ℝ)^2 * ((C.order+1:ℝ)*(frostδ k a*b+Φσ C f b k+C.threshold/x*b)*h^2)
abbrev fireTall (C:BudgetPoint)(k:ℕ)(h b a v f x:ℝ):ℝ:= (C.order+1:ℝ)*(frostδ k a*b+Φσ C f b k+C.threshold/x*(b+v))
abbrev Lodger (C:BudgetPoint)(m:ℕ)(o:Seat n')(c:ℝ):ℝ:= cashPoncho (seam_m m C o * c) C.supportExponent m
-- Ledger_E global.Price. report linearly combined metric. use monot.Budg. postL smaller only at issuance.
local notation "gμ" => flightLoan (a+a) b d v
local notation "fμ" => scanLoan (a+a) b d v
local notation "Vq" =>  lowLoan (a+a) b d v
local notation "Vp" => lowScan (a+a) b d v
local notation "Kμ" x:max=> spill_F P k m x a s h
local notation "Sμ" x:max=> spillCost P k m x a s h
local notation "Κ"=> Lodger P m (node o)
local notation "Hg"=> (fireCost P k h (gμ) a f x₀)
local notation "Hq" z:max=> (fireTall P k h (fμ) a z f x₀)
local notation "Ψ" x:max=> AxStamp.Ρpost P x
-- receipts.C.Pensional.World
abbrev fullEarn (P:BudgetPoint)(a b d v:ℝ) (k m:ℕ) (h s u:ℝ):ℝ:= cashPoncho (vaporB P h (αlife a d v)) s m + (cashPoncho (vaporB P h (flightLoan (a+a) b d v)) s m + spill_F P k m (flightLoan (a+a) b d v) a s h)+(cashPoncho u s m + (cashPoncho (vaporB P h (scanLoan (a+a) b d v)+u) s m+spill_F P k m (scanLoan (a+a) b d v) a s h))+ (reefCost m P s h*lowLoan (a+a) b d v+reefCost m P s h*scanLoan (a+a) b d v+ reefCost m P s h*lowScan (a+a) b d v)
-- WigglePay tracks h*, not I*? gM term abs.Price.Back. Pole.W
abbrev thinEarn (n:ℝ) (P:BudgetPoint)(a b d v:ℝ)(k m:ℕ)(h s f x u:ℝ):ℝ:= let g:=flightLoan (a+a) b d v; let μ:=scanLoan (a+a) b d v; let Y:=fireCost P k h g a f x; let X:=fireTall P k h μ a u f x; cashPoncho (n*Y) P.supportExponent m+spillCost P k m g a s h+(cashPoncho (n*X) P.supportExponent m+spillCost P k m μ a s h)
abbrev trustBasis (n:ℝ) (P:BudgetPoint)(a b d v:ℝ)(k m:ℕ)(h s f x u:ℝ):ℝ:= cashPoncho (KazZ P v h) P.supportExponent m+(thinEarn n P a b d v k m h s f x u+ cashPoncho u P.supportExponent m)
variable (H:Channel P K t d h s a φ f x₀ m k q L') 
variable (R W:SOp (mid N B))(z:Solo (a+a) b R d)(l:Solo (a+a) b W d)(u:IsStarProjection (R (profile (1: Pane (mid N B)))))(v0:W (profile (1:Pane (mid N B)))=0)
local notation "Zq" T:max=> (ρlens T)
variable (X:Op (Single (mid N B)))(K0:Moto.Fit o P.power 1 v X)(H0:Tucked o X)
local notation "pη" => seam_m m P (node o)
local notation "Fboot" x:max=> thinEarn (pη) P a b d v k m h s f x₀ x
local notation "X❄"=> Matrix.trace (R (profile 1)*ρlens X (profile 1))
include H z l u v0 K0 H0
set_option maxHeartbeats 1250000 in
lemma pencil_P : ∃ F:Bag θ, Drill P q m L' o h s F (arcLoad o X) (fullEarn P a b d v k m h s ‖X❄‖) (trustBasis (pη) P a b d v k m h s f x₀ ‖X❄‖) (AxStamp.Ρpost P (Fboot ‖X❄‖)) ∧ ∀ x:Orbit θ, JointJ (R (profile (K x))) (W (profile (K x))) 0 (firePlate K (ρlens X) x) (giveB F x):=by
 let Z:= ρlens X; let F:= fun x=> vessel (R x) (W x) (Z x); let T:= H.helm
 have hx:Soak (node o) Z (a+a) (αlife (a+a) d v) d:= Ωcoat K0 H0 T.pos H.edg (by linarith only [T.hint])
 have pp:0 ≤ Ω:=by linarith only [T.hint]
 let E:= fee_Ξ z l pp; have h1:Solo (a+a) (Real.exp (a+a)) (fun _:Chin θ=>(1:Op I)) d:= Crown.ident ..
 let D:=fun x:Chin θ=>1-R x; have hv:Solo Ω (Real.exp Ω+b) D d:=h1.sub z
 have hp:Soak (node o) F (a+a) (stemLoan (a+a) b d v) d:=aura_X (aura_Y hx (h1.sub E) pp) (h1.plus E) pp
 let U:= F-Z
 have he':Soak (node o) U (a+a) (gμ) d:=minus_Q hp hx
 have hU: F (profile 1)=Z (profile 1):=by unfold F vessel; rw [v0]; simp [capT]
 obtain ⟨R₀,tr⟩:=H.trust; obtain ⟨g₀,xV⟩:=H.room; let Qμ := T.high
 let oz:=node o
 obtain ⟨B₁,V₁,G₁⟩:= extra_core (L':=L') T H.scent H.rad H.step R₀ tr H.high H.tap xV H.vV H.bank he' (by change F _-Z _=_; rw [hU]; exact sub_self _) (pal_v _ Qμ)
 let u₀:=X❄; let K₁:=U (profile (1:Pane θ)); let sV:=R*F
 have hP: Soak oz sV Ω (fμ) d:=aura_Y hp z pp
 obtain ⟨B₂,V₂,G₂⟩:= extra_trace (L':=L') T H.scent H.rad H.step R₀ tr H.high H.tap xV H.vV H.bank hP u₀ (by change Matrix.trace (R _ * F _)=_; rw [hU] )
 let D₀:=sV * D; let D₁:= F*D
 have hV : Soak oz D₀ Ω (Vp) d:= aura_X hP hv pp; have hX: Soak oz D₁ Ω (Vq) d:= aura_X hp hv pp
 -- monotone soak. need shrink rate
 have hl(i:SOp θ)(b:ℝ)(q:Soak oz i (a+a) b d):Soak oz i a b d:=by obtain ⟨F,C,f,v,t,k⟩:=q; refine ⟨F,C,f,v,le_trans ?_ t,k⟩; exact sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (Branch.rent_up (le_add_of_nonneg_right T.hint.le) i) (sum_nonneg fun j _=> sum_nonneg fun k _=> (f i).nonn j k)
 obtain ⟨B₃,V₃,G₃⟩:= dead_core (L':=L') T H.bank (hl _ _ hX) (leg_k h Qμ) (fun i=>Sault.urn_stop ..)
 obtain ⟨B₄,V₄,G₄⟩:= dead_core (L':=L') T H.bank (hl _ _ hP) (tail_k h Qμ) (fun i=>Sault.urn_stop ..)
 obtain ⟨B₅,V₅,G₅⟩:= dead_core (L':=L') T H.bank (hl _ _ hV) (less_k h Qμ) (fun i=>Sault.urn_stop ..)
 let Pz:= unitLoadRaw (C:=P) (q:=q) L' H.cap o u₀ Qμ T.most T.hood
 obtain ⟨y,pA,v,s⟩:=H.GalaP
 let C₁:=pozV oz P m (shipInc K (Z) (faceD true false)); let C₂:=pozV oz P m (u₀ • (1:Firing θ))
 let M:= C₁+B₁+(C₂+B₂)+(B₃+B₄+B₅)
 let Kx:=bodyK K0 H0 T H.leaf H.edg pA v s H.cap
 have hp:=(((Kx.gain V₁ Qμ).gain (Pz.gain V₂ Qμ) Qμ).gain ((V₃.gain V₄ Qμ).gain V₅ Qμ) Qμ) -- s shadow.
 simp only [add_zero,zero_add] at hp
 refine ⟨M,?_ ,?_ ⟩
 · convert hp using 1 -- eq costs
   · simp only [trustBasis, thinEarn, fireTall, fireCost, u₀, spillCost]; abel
   · dsimp only [AxStamp.Ρpost, thinEarn, u₀, fireTall, fireCost, spillCost]; simp only [mul_add]
 intro i; let Y:=profile (K i); let V:= W Y; let P:= R Y; let X:= Z Y; let s:=vessel P V X; have hK:giveB M i=Sault.forge (P*s) s (s*(1-P)) (P*s) (P*s*(1-P)):=by
    have e(A B:Bag θ):giveB (A+B)=giveB A+giveB B:=by simp only [giveB, Pi.add_apply, sum_add_distrib]
    unfold M; simp_rw [e]; rw [G₁,G₂,G₃,G₄,G₅,offset_P, offset_P,Sault.forkL]; simp only [Pi.add_apply,Pi.smul_apply,Pi.one_apply,Pi.sub_apply]; unfold shipInc
    dsimp only [sV,D₀,D₁,U,D]; simp only [Pi.sub_apply,Pi.mul_apply]
    rw [show faceD true false (F (profile (K i))-Z (profile (K i)))=faceD true false (F (profile (K i)))-faceD true false (Z (profile (K i))) from ?_]; swap; · simp_rw [(pal_v h Qμ).whirl,Matrix.sub_apply,sub_smul,sum_sub_distrib]
    unfold s P V Y X F; abel
 rw [hK]; refine ⟨Leaf.ore2 _ _ _ _ _,?_⟩; intro p u v A
 have hn:= Sault.plume p (capT P V) 0 (Thera.tag_g V p) u v A X; dsimp only at hn; rw [zero_mul,Matrix.trace_zero,zero_smul,sub_zero,sub_zero] at hn; exact hn.symm
end YM.CF.Vow.TreasuryFog
