import YM.CF.BPress.Calendar.Curb
/-! When curb enough. x-only deadlines. -/
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
variable {m s B:Side} {K_:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
  {V: Grace K_ R L} {d x h p:ℝ} {U:Grasp V.U B d}{W:GivenX V U} {Mstar:Side} {J:Robes Mstar V W}
variable {P:Before V p}{X:P.Between d J.n} {f: Angel X}{E:Earning X}
namespace Around
open Currencies
structure Pocket (G:Curb f E)(x:ℝ): Prop where
  pace: grant f E x (G.width x)
  age: Currencies X f.toForecast x
  near: spanN X x < umbra (era X x)
  ageF : (frameWidth f.F x).val ≤ (era X x).marked.val
  ageX : zMx (P:=P) < umbra (era X x)
namespace Pocket
variable (G:Curb f E)
lemma hobby : ∀ᶠ x:ℝ in atTop,Pocket G x:= by filter_upwards [G.bill,f.tail,dawn X.toGapSize _ span_pl,memory_fee X.toGapSize _ (zero_lt_one.trans_le f.oneF), dawn X.toGapSize (fun _=> zMx (P:=P)) (PL.const _)] with x a b c d r; exact ⟨a,b,c,d,r⟩
variable {G} (K:Pocket G x)
include K
lemma fast : House.Fast x:= ⟨xi_pos K.age.yPos,K.age.plenty.plenty.Xi⟩
lemma thick : X.z.M≤ (G.width x).val∧ spanN X x ≤ (G.width x).val∧hunger f x≤ (G.width x).val∧ κTown X ≤ (G.width x).val:=by have h:=K.pace.2.2.1; unfold spanN at *; omega
lemma hope : f.P_.reach x≤ hunger f x:= by unfold hunger Wander; omega
lemma deacon (b:BandWidth) (q:ℕ)(p:q<umbra b): 2*umbra b+q ≤ b.marked.val /5:=by unfold umbra at *; omega
section
variable {A:Bands (More (mid m B)) (era X x)} {Q: Hangar (More (mid m B))} {T: GramM (mid m B)} {Z:Loom (mid m B)}
variable (M:Mantle (x:=x) V J h m T Z)(αP: Record P.tone (More (mid m B)))(αM: Record P.tone' (More (mid m B)))(H:Dyadic X.toGapSize f.F x A) (p0: Q.L=G.width x)
local notation "Uκ"=> crew V A αM H K.age M
local notation "Vκ"=> exhibit X αP
include p0 in
lemma night : Crew.Rented Q (crew V A αM H K.age M) (exhibit X αP) d J.k J.n (sbo f x):= lodging V K.age A M αM H αP (p0.symm ▸ K.thick.1) (p0.symm ▸ (K.hope.trans K.thick.2.2.1)) -- tune
lemma zoom: zoomM (crew V A αM H K.age M)= zMx (P:=P) := by change 9*(αM.key.R)+1=_; rw [αM.K] -- tune
lemma zoom_span : fundP (exhibit X αP) (crew V A αM H K.age M) = Fspan X:= by unfold fundP Fspan; rw [zoom K]; unfold zoomX; change 9*αP.key.R+_+1+_= _; rw [αP.K]; rfl --
lemma cap_ : mcap (exhibit X αP) (crew V A αM H K.age M) (small x)=spanN X x:= by unfold mcap; rw [K.zoom_span]; rfl --
include p0
lemma rights : RightsC (exhibit X αP) Q (crew V A αM H K.age M) (μMode f E x):=by
 have h:= K.pace; refine ⟨⟨p0.symm ▸ h.2.1, ?_,K.ageF⟩,?_,μMode_p f E x⟩; · exact lt_of_le_of_lt (Nat.le_add_right X.z.M (small x + Fspan X)) K.near
 unfold Fac overhead magicC; rw [p0,K.zoom_span]; exact h.2.2.2
lemma short : ShortP (exhibit X αP) (crew V A αM H K.age M) Q (small x):=⟨ (cap_ K M αP αM H).trans_lt K.near,(cap_ K M αP αM H).le.trans (p0.symm ▸ K.thick.2.1)⟩ -- tune Eq.trans_lt
lemma oracle : Seer (crew V A αM H K.age M) Q (exhibit X αP) J.n:=by
 have he:= exhibit X αP; let U:= K.age; let p:= crew V A αM H K.age M; have ht:attach (exhibit X αP) J.n+4=κTown X:=rfl; refine ⟨⟨Peel.hosting ?_ (p0.symm ▸ (show (crew V A αM H K.age M).P.reach (crew V A αM H K.age M).y≤ _ from K.hope.trans K.thick.2.2.1)) U.plenty.plenty, ht.le.trans (p0.symm ▸ K.thick.2.2.2),?_⟩,rfl,rfl,?_ ⟩ ; exact (U.register V A M).summer; exact lowP ((ht.le.trans K.thick.2.2.2).trans K.pace.2.1); intro i; rw [K.zoom,Meadow.Tent.body,A.mark_n]; exact deacon K _ _ K.ageX -- tune order
lemma pillar : Mangrove Q (crew V A αM H K.age M) (f.r x):=by have ht:=K.pace.2.2.1; exact ⟨p0.symm ▸ K.thick.2.2.1,p0.symm ▸ (show f.P_.heightClose x ≤ (G.width x).val from by omega)⟩
end
end Pocket
end Around
end YM.CF.BPress.Calendar
