import YM.CF.BProof.Seam.Drive
import YM.CF.BProof.Bias.Temple

/-! Apply purchases both on actual Pole and hom configuration. No shared orientations assumed. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Seam
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
-- frame & pressure orientation proofs. Loft and Pose. gap D fixed.
structure School (r:ℕ) where
 small:δ≤ E.pre.limit
 size_: E.pre.size ≤ N.val
 buyS : Rhythm.Season E rₜ L a Δ y d (S:=S)
 stageU: SiteUp Y E.H Δ.clock r
 lineT: Line Y stageU T θ ν δ rₜ U
 m : Side
 n : Side
 f: Ratio m (More N)
 f0: f.count=E.H.body
 p: Ratio n (More N)
 p0: p.count=E.H.whole
 ft:4 ≤ m.val
 pt:4 ≤ n.val
 -- allow links after oti. buysS also provides H.u pre
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
abbrev Pouch (Y:S.Setup L a (More N) d y) (P:Entice S L a d y)(T:PathData (SU.group)) (θ:ℝ):= {x:Pod Y// Cabinet.Ready P Y T θ x}
namespace School
local notation "εx" => Rhythm.Lease.wearC S y
local notation "ΨN" => Pouch Y P T θ
local notation "ζ_"=>framesL Y P T θ
local notation "κ_"=>rawG Y P T θ
local notation "C'"=>Δ.clock
include Z P
abbrev μwage := MaxFeet Z.f Δ.clock Z.p
abbrev footprintL:= silhouette Δ.clock.extentT E.H.body.val E.H.whole.val
lemma silhouette_p : Z.μwage =silhouette Δ.clock.extentT E.H.body.val E.H.whole.val:=by unfold μwage MaxFeet; rw [Z.f0,Z.p0]
abbrev Shot(w:Pod Y):=Seam.paint Y P T θ w U
abbrev clothing:= Seam.wear Y P T θ Z.f
lemma lic_ (x:Pod Y)(p: Cabinet.Ready P Y T θ x): Trek.Permit (Seam.wear Y P T θ Z.f x) Δ.clock (κ_ x) Y.g (Cabinet.sick Y x) (εx):= Rhythm.Lease.lit P Y T θ (tool Y x) Z.lineT.raw Z.lineT.ok p E.H C' Z.f Z.stageU.podium Z.buyS.warm Z.f0 Z.ft (Instructions E P Y Δ Z.buyS).2.1 Z.buyS.look
lemma lamp_ (x:Pod Y)(p: Cabinet.Ready P Y T θ x): Trek.Lamp Δ.clock Y.g (Cabinet.sick Y x) δ (κ_ x) (Shot (U:=U) (T:=T) (θ:=θ) P x):= beam_ Y P T θ x p Z.stageU Z.lineT
lemma warmZ : Hero.Width Z.f Y.yard.long := by rw [Hero.Width,Z.f0,Y.length P]; exact Z.buyS.warm.length
abbrev easyMoney (w:ΨN) (i:Seat N) := HH_ Y P T θ w.val Z.f Δ.clock Z.p U i
lemma capital (w:ΨN)(i:Seat N): Money (easyMoney P Z w i) := Rhythm.rideH E P Y Δ Z.buyS (Cabinet.sick Y w.val) (Z.lamp_ P w.val w.property) (Z.lic_ P w.val w.property) Z.pt Z.p0 i
abbrev ske(w:ΨN) := Tape.drawB (easyMoney P Z w) (capital P Z w)
abbrev counterK (x:Pod Y): Counter (More N) δ:= ⟨U (F_' Y P T θ x), Z.lineT.roof.paid _⟩ -- replace A
lemma cash (w:ΨN) : Tape.Lease E.pre Δ.stage (Pins mH g₀ (sick Y w.val)) (Z.counterK P w.val) (Z.ske P w) := (Rhythm.stands E P Y Δ Z.buyS (sick Y w.val) (Z.lamp_ P _ w.property) (Z.lic_ P _ w.property) Z.pt Z.p0 _ rfl).1 -- proof irrel
variable (A: Core j a₁ b l r N)
def pose (w:ΨN) : Loft A δ Δ.stage.c rateH Δ.stage.η:=⟨_, (Z.cash P w).ride _ Z.size_ Z.lineT.safe Z.small A⟩
def hom (i:Fin 5): Loft A δ Δ.stage.c rateH Δ.stage.η:= Bias.claimH E P Y Δ Z.buyS Z.p Z.pt Z.p0 δ Z.lineT.safe Z.lineT.height i A Z.size_ Z.small
abbrev stun(w:Pod Y): Dial.Stun N := XX_ Y P T θ w Z.f Δ.clock Z.p U
abbrev homX (i:Fin 5): Dial.Stun N := (homeScript mH i).XX Δ.clock Y.g ∅ 1 Z.p
lemma age : Honor D A δ:= E.pre.first N Z.size_ A δ Z.lineT.safe Z.small
@[simp] lemma sceneT(w:ΨN): Tape.carried (pose P Z A w).val.1 = U (F_' Y P T θ w.val):=rfl
@[fun_prop] lemma tracks_stun : Measurable (stun P Z):= by exact XX_m Z.f C' Z.p Z.lineT.roof.bill
@[fun_prop] lemma tracks_ske : Measurable (Z.ske P) := by
 apply Tape.skein_m; exact fun t i=> (HH_m Z.f C' Z.p Z.lineT.roof.bill i t).comp measurable_subtype_coe
@[fun_prop] lemma tracks_X : Measurable (Z.counterK P):=(Z.lineT.roof.bill.comp (draw_P ..)).subtype_mk
@[fun_prop] lemma tracks_P : Measurable (Z.pose P A):=by
 have he: Measurable (fun w: ΨN=> Pins mH g₀ (sick Y w.val)):= (measurable_of_countable (f:=Pins mH g₀)).comp ((sick_m Y).comp measurable_subtype_coe)
 exact ((((Z.tracks_X P).comp measurable_subtype_coe).prodMk he).subtype_mk.prodMk (Z.tracks_ske P)).subtype_mk -- tune defeq
lemma lightV (i:Fin 5): sunny (Z.hom P A i) ∧ Tape.week (Z.hom P A i).val.2.val (true,false) 0=postC (Z.homX i) ∧ Lat.Slow (1:Pane N) (hook (Z.homX i)) u :=by
 let d:= (Bias.homerL E Y Δ δ Z.lineT.safe Z.lineT.height); let z:= Rhythm.stands E P Y Δ Z.buyS ∅ d (Bias.homerP E Y Δ i) Z.pt Z.p0 _ rfl; exact ⟨z.2.1, z.2.2.1,z.2.2.2.1⟩ -- tune vm type let.
lemma serial(i:Fin 5): Bias.Portrait i mH (Z.hom P A i):= Bias.homP E P Y Δ Z.buyS Z.p Z.pt Z.p0 δ Z.lineT.safe Z.lineT.height i A Z.size_ Z.small
lemma aboutW (w:ΨN) : sunny (Z.pose P A w) ∧ Tape.week (Z.pose P A w).val.2.val (true,false) 0=postC (Z.stun P w.val) ∧ Lat.Slow (Tape.carried (Z.pose P A w).val.1) (hook (Z.stun P w.val)) u:=by
 have z:= Rhythm.stands E P Y Δ Z.buyS (sick Y w.val) (Z.lamp_ P w.val w.property) (Z.lic_ P w.val w.property) Z.pt Z.p0 _ rfl; exact ⟨z.2.1,z.2.2.1,z.2.2.2.1⟩ -- tune
end School
end YM.CF.BProof.Seam
