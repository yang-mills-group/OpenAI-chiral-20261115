import GaugeFieldConstruction.StencilOrders
import GaugeFieldConstruction.StencilRawSplit
import YM.LocalFieldBounds.Motif.Primer
import YM.SU5.Thin.Geometry
/-! # Payment helper for co-calibrated estimator of pure charges from amplitude. Extends Motif. Uses doubleCutSt order. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.LocalFieldBounds.Motif

open Filter Function Set Metric MeasureTheory 
open scoped Topology ComplexOrder InnerProductSpace NNReal Classical
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
open CF.QuadClock.ShapeLab SoulField SatinWard.Installment
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open Polaris.Rampart _root_.GarnetAct.Cut

variable (P:Spine) (M:P.par.R.L.val%16=1) (z:Soul) (mu:Axis)
variable {f0:ℕ}{Z:ℕ→ℕ}{H A d c dσ:ℝ}{η:Type}[Fintype η]
variable (pHw:Tendsto Z atTop atTop)(W:HeartClock P f0 H A d c dσ P.jump128 M Z η)(e:Melodic P η A f0 Z)(K:P.NightCop)[Nonempty η]
variable (x₁:P.Spectrum0 3) (T κ:ℝ) (F G:Curtain)
open Set MeasureTheory
open _root_.YM.SatinWFixed Andesite Carton _root_.YM.Boundary Probe
variable {X: InkWaves Dialect}{Y:WView Dialect}(τ:InkPort (galaxy P rayPost rayP M pHw W e K x₁) X Y) {B:ℝ}{ξ₀:skit}(wτ:ℝ) (pW:Wallpaper P M z pHw W e K mu κ wτ ξ₀ x₁ T F G B)
local notation "Other" x:max=> P.advocate 3 x 3
local notation "HH" x:max=> P.ManyF 3 (P.advocate 3 x 3)
local notation "PointA" x:max=> priceX P pHw e mu rayPost M K rayP 3 (Other x) z
local notation "PointB" x:max=> pricedPSE P M 3 (Other x) rayP W.tally
local notation "Buoy" x:max=> ((κ:ℂ) • PointA x)
local notation "S▪"=> P.advocate 3 x₁ 3
local notation "ΩJ☆"=> P.heaven 3 S▪ -- exists notation!
local notation "HCv" => galaxy P rayPost rayP M pHw W e K x₁
local notation "ΓJ"=> ( (κ:ℂ) • choral mu z)
local notation "ΓK"=> omegaCorner

open CF.Buffered.Afterglow.Hierarchy.Seld
open YM.LocalFieldBounds.Easel

local notation "port" => Port P M z mu pHw e K κ
local notation "bay" => Bay P M W
local notation "charZ" => (fun l => P.singleState 3 l x₁)
local notation "leftY" => Y.expect [(ΓJ,Easel.film F)]
local notation "rightY" => Y.expect [(ΓK,Easel.film G)]
local notation "jointY" => Y.expect [(ΓJ,Easel.film F),(ΓK,Easel.film G)]
local notation "J♥" => Jmoney P M z mu pHw e K F κ
local notation "K♥" => Kmoney P W.tally G
local notation "leftA" => tos P M z mu pHw e K x₁ κ
local notation "rightA" => tax P M W x₁
local notation "bothA" => jointSale P M z mu pHw W e K x₁ κ

local notation "gross" L:max => charZ L (J♥ L)
local notation "tarif" L:max => charZ L (K♥ L)
local notation "levy" L:max => charZ L ((J♥ L)*(K♥ L))
local notation "bat" => inkTest Y ΓJ ΓK F G
local notation "wik" => vesper X ΓJ ΓK F G


variable {a ε : ℝ} (L : ℕ)
variable {w : ℝ≥0} {n : ℕ} {A' : Coat F n} {C : Coat G n} (D : Song w A' C)
open CF.Buffered.Afterglow
local notation "r₀" => closedBall (ξ₀ false) wτ
local notation "r₁" => closedBall (ξ₀ true) wτ
local notation "κ₀" => _root_.YM.LocalFieldBounds.Motif.Port P M z mu pHw e K κ
local notation "κ₁" => _root_.YM.LocalFieldBounds.Motif.Bay P M W
local notation "κJ" l:max p:max=> ((port l p,r₀):MeterQueryVU P)
local notation "κW" l:max p:max=> ((bay l p,r₁):MeterQueryVU P)
local notation "fJ" l:max=> ((J♥ l,r₀):MeterQueryVU P)
local notation "fW" l:max=> ((K♥ l,r₁):MeterQueryVU P)
-- Readings also defined for a fixed pair; every cell.
structure SupportFeesSt (L:ℕ):Prop where
 aboard : Rich P L (r₀) (J♥ L) false ∧ Rich P L (r₁) (K♥ L) true
 rows (i:A'.Job)(j:C.Job)(p:(D.coin i j).Job): Rich P L (r₀) (port L (A'.note i)) false ∧ Rich P L (r₁) (bay L ((D.coin i j).eighth p)) true
 separate : Disjoint (r₀) (r₁)
local notation "hire" => Score P M z mu pHw W e K x₁ T κ F G (X:=X) (Y:=Y) wτ B
local notation "Taped"=> SupportFeesSt P M z mu pHw W e K κ F G (ξ₀:=ξ₀) wτ D
section best
include pW
omit [Nonempty η]
lemma support_pack_st (h: hire a ε ξ₀ L D): Taped L:=by
 let p:=h.pack
 let d:= h.placed.left; let f:=h.placed.right; have v:= pW.tempo; let r:=h.padded
 refine ⟨⟨p.club _ d,p.band _ f⟩,fun i j k =>?_, Set.disjoint_left.mpr ?_⟩
 · refine ⟨(p.wharf _ (A'.stays i) _ (mem_closedBall_self (le_trans w.2 r.2.2))).2 _ (fun _ hx=> d ⟨_, A'.stays i,hx⟩),?_⟩
   exact (p.till _ (C.stays j) _ (((D.coin i j).moves k).trans r.2.2)).2 _ (fun _ hx=> f ⟨_, C.stays j,hx⟩)
 intro x hx hy; linarith only [(pW.distinct x hx x hy).1,v]
-- The unique product predictor with calibrated gauge and raw matter marginals
-- (not split of just gauge-invariant probes). Answer to both actual pair queries, including
-- the Mink estimator. District of validity qualified by the pure Mark purchases.
structure CompassDrawSt (L:ℕ)(D : Song w A' C) : Prop where
  has_analogue : ∃! E:P.Test→ₗ[ℂ]ℂ, P.SameRawProduct L x₁ E
  ask (E:P.Test→ₗ[ℂ]ℂ)(p:P.SameRawProduct L x₁ E) :
      D.play (fun y z=> E ((port L y)*(bay L z)))=(E (J♥ L))*(E (K♥ L)) ∧
      E ((J♥ L)*(K♥ L))=(E (J♥ L))*(E (K♥ L)) ∧
      E (J♥ L)= gross L ∧ E (K♥ L)= tarif L ∧ E≠ P.singleState 3 L x₁
omit pW in
lemma richness_test_st (y:P.Test→ₗ[ℂ]ℂ)(p:P.SameRawProduct L x₁ y){u v:P.Test}
    (hu:Rich P L (r₀) u false)(hv:Rich P L (r₁) v true) : y u= charZ L u ∧ y v=charZ L v ∧ y (u*v)= charZ L u * charZ L v:=by
 let S:= p.marginal; have g:RibbonDoc.SpiritGlow P v:= (if_pos rfl).mp hv.2.2
 have h:Six.PureMatter P.calibration u:= (if_neg Bool.false_ne_true).mp hu.2.2
 exact ⟨S.matter u h,S.link v g.pure, Six.Comparison.firstMatterSt _ g.pure h p.marginal⟩
lemma play_split_st (v:Taped L)(h: hire a ε ξ₀ L D): CompassDrawSt P M z mu pHw W e K x₁ κ F G L D :=by
 refine ⟨P.thin_comparator .., fun E p=>?_⟩
 have z':=(fun {u v:P.Test} (t:Rich P L (r₀) u false) (x:Rich P L (r₁) v true) => richness_test_st P x₁ wτ L E p t x)
 obtain ⟨l,r,e'⟩:= z' v.aboard.1 v.aboard.2
 have g:D.play (fun y z=> E ((port L y)*(bay L z)))= (gross L)*(tarif L):=price_check P M z mu pHw W e K x₁ κ F G L D _ fun i j k => (z' (v.rows i j k).1 (v.rows i j k).2).2.2
 let t:=congrArg₂ (·*·) l r; refine ⟨g.trans t.symm,e'.trans t.symm,l,r,fun y=>?_⟩
 rw [y] at e'; have g₀:= h.amber; rw [e',sub_self, Complex.zero_re] at g₀; exact lt_asymm g₀ (half_pos pW.meter)
end best
section path
variable (V:ℕ→ℝ) (U:P.Register) (I K':ℕ→ℕ) (screens:P.Poll 3)
local notation "ιM" l:max Q:max => menuCurrencySt P screens V I K' l Q
local notation "Πl" l:max d:max=> menuCurrencySt P screens V I K' l [fJ l] d
local notation "ℬm" l:max d:max=> menuCurrencySt P screens V I K' l [fW l] d
local notation "ℳ" l:max d:max=> D.play (fun p q=> menuCurrencySt P screens V I K' l [κJ l p,κW l q] d)
local notation "ζv" l:max d:max=> menuCurrencySt P screens V I K' l [fJ l,fW l] d
local notation "∆q" l:max=> D.play (bothA l)
variable {n':ℕ}{δ:ℕ→ℝ}(h:IntervalsSchedule P n' V δ)(k:P.Selects U 3 x₁ screens)(p:BornTape P I K')
omit [Nonempty η] in
lemma fidelity_st (h:IntervalsSchedule P n' V δ)(k:P.Selects U 3 x₁ screens)(p:BornTape P I K')(v:Taped L) : Tendsto (fun d=>ℳ L d) doubleCutSt (𝓝 (∆q L)) ∧ Tendsto (fun d=>Πl L d) doubleCutSt (𝓝 (gross L)) ∧ Tendsto (fun d=> ℬm L d) doubleCutSt (𝓝 (tarif L)) ∧ Tendsto (fun d=> ζv L d) doubleCutSt (𝓝 (levy L)):=by
 obtain ⟨⟨x,y,_⟩,a',b',_⟩:= v.aboard; let e₀:=isCompact_closedBall (ξ₀ false) wτ; let e₁:= isCompact_closedBall (ξ₀ true) wτ
 refine ⟨?_,(launchSoloSt U k h p (J♥ L) ⟨x,y⟩ e₀).2,(launchSoloSt U k h p (K♥ L) ⟨a',b'⟩ e₁).2,(launchDuetSt U k h p _ _ ⟨x,y⟩ ⟨a',b'⟩ e₀ e₁ v.separate).2⟩
 have hi(i:A'.Job)(j:C.Job)(p₀:(D.coin i j).Job):
     let Z:=A'.note i; let q':=(D.coin i j).eighth p₀; Tendsto (ιM L [κJ L Z,κW L q']) doubleCutSt (𝓝 (bothA L Z q')):=by
      intro Z q'; obtain ⟨⟨x,y,_⟩,c,d,_⟩:= v.rows i j p₀; exact (launchDuetSt U k h p _ _ ⟨x,y⟩ ⟨c,d⟩ e₀ e₁ v.separate).2
 exact tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ fun j _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun x _=> Tendsto.const_mul _ (hi i j x)))

local notation "loan" l:max yyy:max t:max ε:max=> MarketwithSt P U V (x:=x₁) (c:=screens) t.1 (I t.2) (K' t.2) l yyy ε
-- Every title to numerator and denominator, both real and eu fees
abbrev WeightScriptSt (l:ℕ)(ε:ℝ):Prop:= ∀ᶠ t in doubleCutSt, loan l [fJ l] t ε ∧ loan l [fW l] t ε ∧ loan l [fJ l,fW l] t ε∧∀ (i:A'.Job)(j:C.Job)(p:(D.coin i j).Job), loan l [κJ l (A'.note i),κW l ((D.coin i j).eighth p)] t ε
include h k p
omit [Nonempty η] in
lemma weight_pack_st (b:0<ε)(v:Taped L): WeightScriptSt P M z mu pHw W e K x₁ κ F G (ξ₀:=ξ₀) wτ D V U I K' screens L ε:=by
 obtain ⟨⟨x,y,_⟩,a',b',_⟩:= v.aboard; let e₀:=isCompact_closedBall (ξ₀ false) wτ; let e₁:= isCompact_closedBall (ξ₀ true) wτ
 have z:∀ (x:List (MeterQueryVU P)), P.EndTapeSt L x → ∀ᶠ t in doubleCutSt, loan L x t ε:=fun _ z =>launchMarketSt U k h p z ε b
 refine (z _ (launchSoloSt U k h p (J♥ L) ⟨x,y⟩ e₀).1).and ((z _ (launchSoloSt U k h p (K♥ L) ⟨a',b'⟩ e₁).1).and ((z _ (launchDuetSt U k h p _ _ ⟨x,y⟩ ⟨a',b'⟩ e₀ e₁ v.separate).1).and ?_))
 simp only [eventually_all]; intro i j k'; obtain ⟨⟨x,y,_⟩,a',b',_⟩:= v.rows i j k'; exact z _ (launchDuetSt U k h p _ _ ⟨x,y⟩ ⟨a',b'⟩ e₀ e₁ v.separate).1
omit h k p
-- Use tiny width at fixed pair before lower normalized estimates.
structure ClockFeesSt (ε:ℝ)(L:ℕ)(v:Song w A' C)(sJ sQ sE sW:ℂ) : Prop where
 costs : ∀ᶠ d in doubleCutSt, dist (v.play (fun p q=>menuCurrencySt P screens V I K' L [κJ L p,κW L q] d)) sE < ε ∧
          dist (Πl L d) sJ < ε ∧ dist (ℬm L d) sQ < ε ∧ dist ((Πl L d)*(ℬm L d)) (sJ*sQ)<ε ∧
          dist (v.play (fun p q=>menuCurrencySt P screens V I K' L [κJ L p,κW L q] d) - (Πl L d)*(ℬm L d)) sW<ε
 wick : ∀ᶠ d in doubleCutSt, dist (ζv L d) (vesper X ΓJ ΓK F G) < ε ∧
          dist (ζv L d - (Πl L d)*(ℬm L d)) (wik - sighting X ΓJ F*sighting X ΓK G)<ε -- equiv onepoint, no_clock
include pW τ
-- parentheses around gross notation. WorldPos.
lemma refinement_math_st {sJ sQ sE sW:ℂ}(h:IntervalsSchedule P n' V δ)(k:P.Selects U 3 x₁ screens)(p:BornTape P I K')(b:0<ε)(f:Taped L)(r:hire a (ε/2) ξ₀ L D)(pJ:sJ=leftY)(pQ:sQ=rightY)(pE:sE=jointY)(pB:sW=bat): ClockFeesSt P M z mu pHw W e K κ F G (X:=X) (ξ₀:=ξ₀) wτ V I K' screens ε L D sJ sQ sE sW:=by
 cases pJ; cases pQ; cases pE; cases pB 
 let half:=half_lt_self b
 obtain ⟨d,g,t,f⟩:= fidelity_st P M z mu pHw W e K x₁ κ F G wτ L D V U I K' screens h k p f
 let u:=g.mul t; have he:= r.eu_cross
 have qe:= no_clock P M z mu pHw W e K x₁ T κ F G τ wτ pW; rw [qe.1,qe.2] at he
 exact ⟨(d.eventually (isOpen_ball.mem_nhds (mem_ball.mpr (r.real_joint.trans half)))).and ((g.eventually (isOpen_ball.mem_nhds (mem_ball.mpr (r.first.trans half)))).and ((t.eventually (isOpen_ball.mem_nhds (mem_ball.mpr (r.last.trans half)))).and ((u.eventually (isOpen_ball.mem_nhds (mem_ball.mpr (r.comparator.trans half)))).and ((d.sub u).eventually (isOpen_ball.mem_nhds (mem_ball.mpr (r.real_cross.trans half))))))), (f.eventually (isOpen_ball.mem_nhds (mem_ball.mpr (r.eu.trans half)))).and ((f.sub u).eventually (isOpen_ball.mem_nhds (mem_ball.mpr (he.trans half))))⟩
end path
#print axioms refinement_math_st
#print axioms support_pack_st
#print axioms play_split_st
end YM.LocalFieldBounds.Motif
end
