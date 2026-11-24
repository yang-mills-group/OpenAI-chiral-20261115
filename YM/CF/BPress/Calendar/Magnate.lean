import YM.CF.BPress.Calendar.Rural
/-! sufficiently delayed terminal coupling implies all interior estimates. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Calendar
open Function NormedSpace Metric Finset MeasureTheory Filter Lattice RG Precision Pressure
open Cube Py Vale Vale.Grace Paige Scree Skye Fixed Dial Spire SU Wilson
open Net Hazel Chrono Sugar Lilac Grid Mount Recital Habitat Driver Meadow Meadow.Tent Meadow.Frame Meadow.Stamps Locale
open Wealth Weave Port Honey Before Between Recipe RG.PathData Branch LocalH Next.SectorChange Peel Spine Mosaic
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {m s B:Side} {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K R L} {d x h p:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X}{E:Earning X}
namespace Around
open Currencies Pulse Manna Manna.Budget House Huon Stripe Contour Rates Pilot
variable (G:Curb f E)
structure Magnate (x:ℝ):Prop where
  high:Warmth G x
  cool:coolCap (boss G x)≤alpha
  hike:Real.exp (Bcap G x)*breeze G x*(Real.exp (-RR (f:=f) x)+HumK G x)*(breeze G x/alpha)^kroot≤alpha
  happy:HumK G x≤1/2
lemma magnate : ∀ᶠ x:ℝ in atTop,Magnate G x:=by filter_upwards [warm G,(cool_P G).eventually (ge_mem_nhds tiny), (hot_S G).drop.eventually (ge_mem_nhds tiny),(HumPL G).drop.eventually (ge_mem_nhds (half_pos zero_lt_one))] with x a b c d; exact ⟨a,b,c,d⟩
namespace Magnate
variable {G} (u: Magnate G x) {A:Bands (More (mid m B)) (era X x)} {Q: Hangar (More (mid m B))} {T: GramM (mid m B)} {Z:Loom (mid m B)}
variable (M:Mantle (x:=x) V J h m T Z)(αP: Record P.tone (More (mid m B)))(αM: Record P.tone' (More (mid m B)))(H:Dyadic X.toGapSize f.F x A) (p0: Q.L=G.width x)
local notation "Uκ"=> crew V A αM H u.high.pace.age M
local notation "Vκ"=> exhibit X αP
local notation "xv"=> launch X T
abbrev turn(x:ℝ):=μMode f E x
include p0
lemma ticket : Trust (R:=Q) (crew V A αM H u.high.pace.age M) (boss G x) alpha:=by
 refine ⟨u.high.pace.fast, ?_,tiny, min_le_left .., u.cool,?_ ⟩; · let Z':=Q; change 1/2≤ paysP Q (B:=era X x) x; have he:= salary Q x u.high.pace.fast (B:=era X x); apply le_of_sub_nonpos; rw [p0] at he; exact sub_nonpos.mpr (by have ht : HumCost (era X x).D (G.width x).val x≤ 1/2:= u.happy; linarith only [he,ht]) -- tune indent
 unfold hotCap areaB; rw [p0]; exact u.hike
/-- Variant B-xiQ threshold interface suffices for the contour lemma. Can buy
 _any_ fixed strictly-positive upper bound on q (integrated core price
 `(2*q)^|Q|`, see `Manna.Trust.sweet`) for that call, also cofinally late on
 these same width choices. -/
lemma rarity (b:ℝ)(v:0<b)(t:b≤1)(z:coolCap (boss G x)≤b)(w:Real.exp (Bcap G x)*breeze G x*(Real.exp (-RR (f:=f) x)+HumK G x)*(breeze G x/b)^kroot≤b) : Trust (R:=Q) (crew V A αM H u.high.pace.age M) (boss G x) b:= by
 let U:=u.ticket M αM H p0; refine ⟨U.bright,U.reputation,v,t,z,?_⟩; unfold hotCap areaB; rw [p0]; exact w
variable (L': Wish (launch X T) P.H (Spin.First V) (Spin.Second V))(nA:X.age≤(mid m B).val) (B0:Born A Q (exhibit X αP) (launch X T))
include L' nA
lemma currencies (R: Recipe (A:=A) T)(c:R.C=K.top.paths)(g':R.M=f.r x) : Manna.Budget (boss G x) (f.k x) (Between.stipend E x) (limit E x) (f.a x) f.Jc f.ζ f.η (μMode f E x) alpha X.strength E.t (sbo f x) (g x) (p/2) (value E) (small x) X.widthM B0 (crew V A αM H u.high.pace.age M) R J.n:=by
 let Y:= u.high.pace; let t:= u.high; let H':= Uκ; let X':= Vκ; let B':= era X x; let b:=boss G x; let θ:=μMode f E x; let pX:= sbo f x
 refine ⟨Y.oracle M αP αM H p0,Y.short M αP αM H p0, (by rw [g']; exact Y.pillar M αM H p0), Y.rights M αP αM H p0, ⟨ (min_le_left ..).trans (min_le_left ..), (min_le_left ..).trans (min_le_right ..), (min_le_right ..).trans (min_le_left ..),(min_le_right ..).trans (min_le_right ..)⟩, sb_pos u.high.pace.age,t.youth,P.slack,land A Q αP nA B0 (Y.night M αP αM H p0).dusk L',(p0.symm ▸ Y.pace.1),?_,by rw [u.high.pace.cap_]; exact t.size,by rw [u.high.pace.cap_]; exact X.wide.trans (Nat.le_add_right ..),g_pos Y.age.yPos,?_,?_,?_,u.ticket M αM H p0,?_ ⟩ -- tune args & min
 · unfold sheafCost payL payE payJ MicCost errorCost leftCost; rw [p0,c,g',M.cash]; exact t.mud
 · rw [p0]; exact le_rfl
 · rw [u.high.pace.cap_]; unfold costη chargeP leis; rw [p0]; exact le_rfl
 · rw [M.cash]; exact le_rfl
 have ht: alpha ≤ lavish fixedR/4:= min_le_right ..; linarith only [ht,tiny]
end Magnate
lemma eventually_rarer (b:ℝ)(t:0 < b) : ∀ᶠ x:ℝ in atTop, Magnate G x ∧ coolCap (boss G x) ≤ b ∧ Real.exp (Bcap G x)*breeze G x*(Real.exp (-RR (f:=f) x)+HumK G x)*(breeze G x/b)^kroot≤b:=by
 let a(x:ℝ):=Real.exp (Bcap G x)*breeze G x*(Real.exp (-RR (f:=f) x)+HumK G x); let p:=(alpha/b)^kroot
 have h:Tendsto (fun x=> (a x*(breeze G x/alpha)^kroot)*p) atTop (𝓝 0):= by
    simpa using ((hot_S G).drop.mul_const p)
 filter_upwards [magnate G,(cool_P G).eventually (ge_mem_nhds t),h.eventually (ge_mem_nhds t)] with x m u v; refine ⟨m,u,?_⟩; change a x*(breeze G x/b)^kroot ≤ _; rw [show breeze G x/b=breeze G x/alpha*(alpha/b) from (by field_simp [tiny.ne']),mul_pow,←mul_assoc]; exact v

end Around
end YM.CF.BPress.Calendar
