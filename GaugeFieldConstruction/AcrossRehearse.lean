import GaugeFieldConstruction.AcrossCalendar
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Altitude Tapestry.Exhibition
open TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
open Heat Buffered Dial Tapestry.Fashion Py.Rate.Branch Haro
/-!
# Morphing *all* resolution-step legs. To be made on the SAME appointments
as the path estimates. Compare *actual* canonical (β,wave, histories, Prop) there.
Still no assertion of replacing P's actor/Mark/Pole choices. On inputs `P.Effect`,
root ticket as syntax. Rerun with these perturbed betas and waves,
reserving all support & real prices. ``mixed operations'' in the Mark transport
picture, not inventing a new Actor system. Careful with the order of taking heights:
the formulas represent **primed**, earned observations only at these defined meters.
-/
local notation "Κ" i:max=> P.run.voyage i
local notation "Τ" k:max=> P.run.uv k
local notation "Πβ" i:max k:max => Actual (Y).meter (Κ i).funds (Κ i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) (Τ k)
abbrev roadFareSt(i k s:ℕ)(r:Bet (Τ k)) : Tariff:= ((lobbyTape (i:=i) P k r (s+1)).beta, ((Πβ i k).wave P.par.P r s)) -- port
noncomputable abbrev roadArtSt (i k s:ℕ)(r:Bet (Τ k)):= rhythm Y s i (P.roadFareSt i k s r)
def roadMeterSt (i k:ℕ)(r:Bet (Τ k)): Decking (Dome P.calibration) (fun s=>Ward (side P.run i s)) :=⟨fun s=>roving Y B s i, fun s=>(P.roadArtSt i k s r).toLinearMap, fun s=>rhythm_one Y s i (P.roadFareSt i k s r)⟩
noncomputable abbrev roadScriptSt (i k s:ℕ)(r:Bet (Τ k)): P.Effect→ₗ[ℂ] Ward (side Y i s):= (roadMeterSt P i k r).crown (auxiliaryPad P.calibration) s
variable {R:P.Register}{t:ℝ}{r : Bet (P.run.uv k)}{ε:ℕ→ℝ}(p: P.WalletDebtSt v (ε:=ε) i k t r)
lemma roadLensFareSt {i k s:ℕ} (r:Bet (Τ k))(f: Ward (side Y i s)) : attire (roadArtSt P i k s r f)= P.climbTape (i:=i) s r (attire f):=by
 have he: P.climbTape (i:=i) s r (attire f) = pushMark (Vale.apt ((Y).ir i) (Γ).block (Γ).R.L s) (patternA Y s i 0) (Γ).K.j (P.roadFareSt i k s r).2.val (⟨1,odd_one⟩:Male) (Γ).R.odd_side Chi.canonical (Γ).J.d (P.roadFareSt i k s r).1 ((Κ i).CapeT s) (attire f):= by
    rw [← singleStep Y s i k]; rfl
 exact he.symm

lemma overheadSt (f:P.Effect)(e:f∈ shorter P.Test s) : attire (P.roadScriptSt i k (s+1) r f)=P.climbTape s r (attire (P.roadScriptSt i k s r f)):=by
 unfold roadScriptSt; rw [(roadMeterSt P i k r).joins s f _ e]; exact roadLensFareSt ..

lemma fileSt (S:BillOfWork)(x:Employee S) : accolading (fun j=>side Y i j) (fun s=>P.roadArtSt i k s r) s (impetus Y B i (employ P.calibration S x))=(P.roadMeterSt i k r).finish s (employ P.calibration S x):=by
 induction s with
 | zero=> rfl
 | succ n ih=> rw [awards_succ,Decking.finish,ih]; rfl

lemma advanceSingleSt (A:P.Test) : attire (P.roadScriptSt i k s r (pinhole P.Test s A)) = exhibit Y B s i A.1:=by unfold roadScriptSt; rw [Decking.outcrop]; rfl

include p
private lemma ckL (h: s < Τ k) : dist (roadFareSt P i k s r) (rawTariff Y s i k) ≤ ε (Τ k)/(1+totalTickets P i k (Τ k)):=by
 rw [Prod.dist_eq]; exact max_le ((p.owes (s+1) h).2.1) ((p.owes s h.le).2.2 h)
lemma deltaSt (a:s≤ Τ k) : dist (lobbyTape (i:=i) P k r s).beta (((Κ i).X (Τ k)).gram s).beta ≤ ε (Τ k)/(1+totalTickets P i k (Τ k)) ∧
   (s< Τ k→ dist (roadFareSt P i k s r) (rawTariff Y s i k) ≤ ε (Τ k)/(1+totalTickets P i k (Τ k))):= ⟨(p.owes s a).2.1,ckL P v p⟩
-- update ensures AtSupport precisely at test footprints with same Hill; goes to top.
lemma coverPartSt (w:ReserveTape (P:=P) n i k)(S:BillOfWork)(x:Employee S)(a:s≤ Τ k): AtSupport false (Satin.region (frameBudget S P.par P.width s) (side Y i s)) (attire ((P.roadMeterSt i k r).finish s (employ P.calibration S x))):=by
 induction s with
 | zero=> exact presented Y B 0 i (S 0) (x 0)
 | succ s ih=>
    let X:=(P.roadMeterSt i k r).finish s (employ P.calibration S x)
    have H:= P.raisedReadingSt v w p s a (frameBudget S P.par P.width s) (attire X) (ih (by omega))
    change AtSupport false _ (attire (P.roadArtSt i k s r X * roving Y B (s+1) i _))
    rw [attire_mul,roadLensFareSt]; exact (H.1.mono (image_subset_image subset_union_left)).mulM ((presented Y B (s+1) i (S (s+1)) (x (s+1))).mono (image_subset_image subset_union_right))
lemma coverSt (w:ReserveTape (P:=P) n i k)(a:s≤ Τ k) {S:BillOfWork}{A:P.Effect}{b:ℝ}(e:Pocket P.calibration S s b A): AtSupport false (Satin.region (frameBudget S P.par P.width s) (side Y i s)) (attire (P.roadScriptSt i k s r A)):=by
 induction e with
 | stone x h=> unfold motif roadScriptSt; rw [Decking.reckon_paid _ _ _ h]; exact P.coverPartSt v p w S x a
 | no=> rw [map_zero]; exact AtSupport.zeroM -- needs attire
 | blend _ _ u f=> rw [map_add]; exact AtSupport.addM u f
 | shade a _ h=> rw [map_smul]; exact AtSupport.smulM h a
 | fully _ _ u=> exact u

omit p
-- Uniform tolerance BEFORE choosing β, by location & actual B crew. Get δ allowing all s≤k simultaneously. independent of size of wallet & list of queries.
lemma roadSpendStL (s i k:ℕ)(b:ℝ)(h:0<b) : ∃ d:ℝ,0< d ∧ ∀ r:Bet (Τ k), (∀ t<s, ‖P.roadArtSt i k t r - Tapestry.music Y t i k‖ ≤ d) →
    ∀ (S:BillOfWork)(c:ℝ)(A:P.Effect), Pocket P.calibration S s c A → ‖P.roadScriptSt i k s r A - breathing Y B s i k A‖ ≤ b*cloudSpan s S*c:=by
 let Gm:=fun s:ℕ=>side Y i s; let W:=fun s:ℕ=> Ward (side Y i s); let U:= awardStart (side Y i 0); let V:=fun t:ℕ=> blossom (Gm (t+1)); let M:= Tapestry.stageRoll Y i k
 let D(t:ℕ):=1+‖M t‖; let Ψ(t:ℕ):ℝ:=1
 let c:= discrepancy (X:=W) («Y»:=W) U V M D Ψ s; let d:= min 1 (b/(1+c))
 have he:0 ≤ c:= feePos (X:=W) («Y»:=W) U V M D (fun s=> add_nonneg zero_le_one (norm_nonneg (M s))) Ψ s (fun s=>zero_le_one)
 have ht:0<d:= lt_min zero_lt_one (by positivity)
 have hp:d*c≤b:=by have hv:d*(1+c)≤ b:=(le_div_iff₀ (by positivity : 0 < 1+c)).1 (min_le_right ..); linarith
 refine ⟨d,ht,fun r z S y A p=>?_⟩
 apply p.bequeath (P.roadScriptSt i k s r-breathing Y B s i k) (mul_nonneg h.le (cloudSpan_pos s S)); intro x q
 let T:= impetus Y B i (employ P.calibration S x)
 let f(t:ℕ):=P.roadArtSt i k t r; have hu(t:ℕ)(p':t < s): ‖f t‖ ≤D t:= opPriceBelow ((z t p').trans (min_le_left _ _)) le_rfl
 have hv:= reckons (X:=W) («Y»:=W) U V f M D Ψ s (a:=d) (fun i h=> (by change ‖_‖ ≤ d*1; rw [mul_one]; exact z i h)) hu T
 change ‖(roadMeterSt P i k r).crown _ s (motif _ S x)-breathing Y B s i k (motif _ S x)‖≤ _
 unfold motif; rw [Decking.reckon_paid _ _ _ q, breathing_pure _ _ _ _ _ _ q, ← fileSt, ← enjoying]; refine hv.trans ((mul_le_mul hp (fanPrice Y B i s S x) (Altitude.licensedN s T) h.le).trans_eq (mul_assoc _ _ _).symm)
#print axioms roadSpendStL
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
