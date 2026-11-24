import YM.CF.BPress.Calendar.Angel
/-! build real Budgeting witness at Angle params. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange -- tune
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
local notation "σX"=>K.top.width
local notation "clip'"=>K.top.clip
local notation "VX"=>V.W.bar
local notation "Cp"=>K.top.paths
-- Ring size. use one Orbit.
variable {P:Before V p}{X:P.Between d J.n}{f:Angel X}(t:Currencies X f.toForecast x)
variable {A:Bands (More (mid m B)) (era X x)} {Q: Hangar (More (mid m B))} {T: GramM (mid m B)} {Z:Loom (mid m B)}
namespace Currencies
variable (V)(A) (M:Mantle (x:=x) V J h m T Z)(αM: Record P.tone' (More (mid m B)))(H:Dyadic X.toGapSize f.F x A)
include M t
local notation "Wx"=> f.P_
abbrev Lg(_t:Currencies X f.toForecast x)(M:Mantle (x:=x) V J h m T Z):Fare A:= f.P_.flies x A T.path T.funds (f.r x) T.beta M.work -- notation? tune A implicitly
lemma register : Weave.Budget.Ready f.P_ x A T.path T.funds T.beta M.work (f.r x):=by
 let X':= t.bought; unfold wideSeason at X'; generalize HA: M.work = Hp; clear HA; revert Hp; rw [M.cash]; intro Hp; exact X' _ A _ _ _ Hp t.err.high M.hill -- issue revert M.dependency.Avoid use congr @
def crew(t:Currencies X f.toForecast x)(M:Mantle (x:=x) V J h m T Z) : Crew A:=⟨x,f.κ,Lg V A t M,f.P_,L,f.T,f.F,f.C,f.C',f.steps,Classical.choice (t.existsT _ A H),αM.key,Z⟩ -- H implicit referenced? include vs variable A
local notation "Uκ"=> crew V A αM H t M -- tune argument order
lemma recipe : ∃ W: Recipe (A:=A) T, Budgeting (crew V A αM H t M) W (f.a x) (f.k x) f.η f.ζ f.Jr f.Jc ∧ W.M=f.r x∧W.C= Cp:=by
 let H':=register V t A M; obtain ⟨W,B,K'⟩:=f.P_.buy_jac x A T.path T.funds (f.r x) T.beta M.work H'; let K:Recipe T (A:=A):=⟨f.r x,σX,Cp,VX,M.work,W,B⟩ -- fill M explicit after; witness
 let H'':T.path.Bounds clip' σX Cp VX:= M.cash ▸ M.work; obtain ⟨c,l,u⟩:=t.weak (More (mid m _)) T.path T.p T.beta H'' M.fund M.hill
 refine ⟨K, ?_,rfl,rfl⟩; exact ⟨M.cash.symm ▸ t.err,M.cash.symm ▸ l,M.fund,M.hill,M.cash.symm ▸ c,(f.living _).le,M.cash.symm ▸ u,t.afford,f.charge,H'.poly,H'.summer,K',f.pays,t.stride,M.cash.symm ▸ t.settle⟩ -- tune
section coat
variable (αP:Record P.tone (More (mid m B)))
variable {V}
omit t M
def sbo (H:Angel X) (x:ℝ):= price_p H.A H.ζ x
lemma sb_pl (H:Angel X) : NPL (sbo H):= price_npl H.A H.ζ
-- omit.M d. Spend Later curb
include t
lemma sb_pos :0<sbo f x:=by
 let u:= t.err.dividend; have he:=u.young; unfold sbo price_p; positivity [u.posC,temp_pos he,aA_positive he,t.plenty.plenty.desires] -- tune sbo defined With M issue ^ notation parser
-- locality uses thresholds H post
variable (V)
include M
lemma lodging (q:X.z.M≤ Q.L.val)(g:f.P_.reach x≤ Q.L.val): Crew.Rented Q (crew V A αM H t M) (exhibit X αP) d J.k J.n (sbo f x):=Crew.fat Q (crew ..) (exhibit X αP) αP αM rfl rfl (register V t A M).summer g q M.crown (M.fund ▸ M.pole) X.book t.plenty -- tune
end coat
end Currencies
end YM.CF.BPress.Calendar
