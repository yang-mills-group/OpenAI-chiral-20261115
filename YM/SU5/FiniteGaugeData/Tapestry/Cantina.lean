import YM.SU5.FiniteGaugeData.Tapestry.Ultraviolet
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin Haro
attribute [local instance] opCStarAlgebra
open Pastry Tap Nacre Ember Pec
open Push.BetaTransport
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill

/-!
# Actual sharp Course + local norm Exhibition + selecting the parameters

Even when proofs tying Ward to Swatch are not qualified because of the size of
the support or price constraints at this level of a hierarchy, we can perform
the UV limit for operator maps. State what operator these actually correspond
to on the row. Precisely evaluating the real finite-cutoff reading (numerator &
preserved nonzero Z, scale-by-scale); match the payments on BOTH torus spaces.

Bridge to determine all pre-thermodynamic-limit polynomials of test families at
all participating rows (e.g. consistency before passing to the selected periods).
Also upgrade the `row UV` one-level claim of Boutique (threshold period-dependent)
to op-norm convergence ALL Tor Ward (fixed period). This statement coexists
with, and doesn't replace, the sup-coeff budget & geometric prices of Crimson at
fixed support and observation level that really pay inside the joint-cutoff cone.
Assign no physical meaning to values of arbitrary probes after non-paid heights.
-/
set_option quotPrecheck false
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
instance Ward.topo (N:Side): TopologicalSpace (Ward N):= inferInstanceAs (TopologicalSpace ↥(Tapestry.tor N))
attribute [instance 5000] Ward.topo

variable (S:Finset Cover)(s i k:ℕ)
local notation "Ω" i:max s:max => side Y i s
local notation "Xs"=> (((Y.voyage i).X (Y.uv k)))
local notation "Cape"=> (Y.voyage i).CapeT s -- no space
local notation "G" => Vale.apt (Y.ir i) Λ.block Λ.R.L s
lemma singleStep : patternA Y s i k=patternA Y s i 0:=by rw [alignedMarks,alignedMarks]
lemma pilotShape : (patternA Y s i 0).ratio= ratio (G):= by
  obtain ⟨k',v⟩:= (eventualPairIdx Y s i).exists; rw [←singleStep Y s i k']; exact (fullness Y i k' v.1).cap_grant.aligned s v.2
-- `M` is irrelevant in the *advance* operation. (Unlike other data in Gram.)
lemma sameMaleUse (f:Mark (Ω i s)) : ascender Y s i k f= pushMark G (patternA Y s i 0) Λ.K.j (patternQ Y s i k).val (⟨1,odd_one⟩:Male) Λ.R.odd_side Chi.canonical Λ.J.d (patternβ Y s i k) (Cape) f:=by rw [←singleStep Y s i k]; rfl
-- playing and clipping. rhythm/sharp tune respond identically to the tariff.
def rhythm (x:Tariff): Ward (side Y i s) →L[ℂ] Ward (side Y i (s+1)):= tune (G) Λ.K.j (⟨1,odd_one⟩:Male) Λ.R.odd_side (Cape) Chi.canonical Λ.J.d _ (Journey.legal Λ) (pilotShape Y s i) (threshold Y).1 (threshold Y).2 ((Y.voyage i).ownership s).paid.bill (Journey.tissue Y i s) (Y.pilot_steps s i 0).2.2 x
lemma streaming : Continuous (rhythm Y s i):= continuous_iff_continuousAt.mpr fun x=> tuneMoves (G) Λ.K.j (⟨1,odd_one⟩:Male) Λ.R.odd_side (Cape) Chi.canonical Λ.J.d _ (Journey.legal Λ) (pilotShape Y s i) (threshold Y).1 (threshold Y).2 ((Y.voyage i).ownership s).paid.bill (Journey.tissue Y i s) (Y.pilot_steps s i 0).2.2 x
lemma compact_tone (x): IsCompactOperator (rhythm Y s i x) := compactRhythm (G) Λ.K.j (⟨1,odd_one⟩:Male) Λ.R.odd_side x Chi.canonical Λ.J.d (Journey.legal Λ) (threshold Y).1 (threshold Y).2 (Cape) (patternA Y s i 0) (pilotShape Y s i) ((Y.voyage i).ownership s).paid.bill (Journey.tissue Y i s) (Y.pilot_steps s i 0).2.2
lemma flowing (f: Ward (side Y i s)): attire (rhythm Y s i (rawTariff Y s i k) f)= ascender Y s i k (attire f):= (sameMaleUse Y s i k (attire f)).symm
lemma rhythm_one (x:Tariff): rhythm Y s i x 1=1:= tuneGlee (G) Λ.K.j (⟨1,odd_one⟩:Male) Λ.R.odd_side (Cape) Chi.canonical Λ.J.d _ (Journey.legal Λ) (pilotShape Y s i) (threshold Y).1 (threshold Y).2 ((Y.voyage i).ownership s).paid.bill (Journey.tissue Y i s) (Y.pilot_steps s i 0).2.2 x
noncomputable abbrev music : (Ward (side Y i s) →L[ℂ] Ward (side Y i (s+1))):= rhythm Y s i (rawTariff Y s i k)
local notation "F" k:max=> music Y s i k
-- music is offered at ALL k but we only read it on participation: p. CLIPPED reader.
-- `T.entangled etc`.`rawTariff` after cutoff is present for computational use.
lemma compatibility_boutique (q:Spanned Y S s i k):
    (wearStep Y H (followBox (Λ:=Λ) (l:=l) S) (s+1) i).comp (coupon Y H S s i k)=
     (music Y s i k).comp (wearStep Y H S s i):=ContinuousLinearMap.ext (fun x=>by
       apply attireL_inj; simp only [ContinuousLinearMap.comp_apply]; rw [attire_wear,onSpanned Y H S s i k q,show attire ((music Y s i k) (wearStep Y H S s i x)) = _ from flowing Y s i k (wearStep Y H S s i x),attire_wear])
variable (p:Pay Y s i k)
local notation "L₀" => Journey.compass Y i k s
abbrev torCost :ℝ:= Real.exp (Y.debt s*sites (side Y i s))
def savingsₗ : Ward (side Y i s)→ₗ[ℂ] ℂ where
  toFun x:= Journey.compass Y i k s (attire x)
  map_add' x y:= plusReader Y s i k (Ward.signs x).env (Ward.signs y).env p
  map_smul' z x:= scaleReader Y s i k z (attire x)
lemma afforded (x: Ward (side Y i s)): ‖savingsₗ Y s i k p x‖≤torCost Y s i * ‖x‖:=by
  let U:= attire x
  have l := Y.each_level i k s p.1 p.2
  have he : L₀ U= markedRead U (Cape) (ratioField Λ.V ((Xs).gram s) (Cape) Λ.U) := Marks.normalized ..
  let D:=torCost Y s i; change ‖L₀ U‖ ≤ _; rw [he]; unfold markedRead
  apply (norm_integral_le_of_norm_le_const (C:=D*‖x‖) (μ:=city (Ω i s)) ?_).trans_eq
  · simp [D]
  refine Filter.Eventually.of_forall fun z=> ?_; refine le_trans (mark_bound ..) ?_
  exact (mul_le_mul (Ward.pay x _) (l.rate z) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm ..)
noncomputable def savings : Ward (side Y i s)→L[ℂ] ℂ := if p:Pay Y s i k then (savingsₗ Y s i k p).mkContinuous (torCost Y s i) (afforded Y s i k p) else 0
lemma trueSavings (x:Ward (side Y i s)) (p:Pay Y s i k): savings Y s i k x= Journey.compass Y i k s (attire x):=by unfold savings; rw [dif_pos p]; rfl
lemma conserve_exact (p:Satin.PairIdx Y s i k):
    (savings Y (s+1) i k).comp (music Y s i k)= savings Y s i k:= ContinuousLinearMap.ext (fun x=>by
        rw [ContinuousLinearMap.comp_apply,trueSavings _ _ _ _ _ ⟨p.1,p.2⟩,flowing, trueSavings _ _ _ _ _ ⟨p.1,p.2.le⟩]; exact (partake Y s i k p (Ward.signs x)).symm )
lemma savingsOp : ‖savings Y s i k‖ ≤ torCost Y s i := by
  unfold savings; split
  · exact LinearMap.mkContinuous_norm_le _ (Real.exp_pos _).le _
  simpa [torCost] using Real.exp_nonneg (Y.debt s*sites (side Y i s))
lemma swatchSavings : (savings Y s i k).comp (wearStep Y H S s i)= tapReader Y H S s i k:=by
  by_cases h:Pay Y s i k; exact ContinuousLinearMap.ext (fun x=> (trueSavings _ _ _ _ _ h).trans (tapReader_compass Y H S s i k x h).symm)
  unfold savings tapReader; rw [dif_neg h,dif_neg h,ContinuousLinearMap.zero_comp]
lemma whereSavings (p:Tapestry.Pay Y s i k): savings Y s i k 1=1:= (trueSavings Y s i k 1 p).trans (oneReader Y s i k p) -- maybe proof omitted
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.streaming
#print axioms YM.CF.Buffered.Afterglow.Tapestry.compatibility_boutique
#print axioms YM.CF.Buffered.Afterglow.Tapestry.conserve_exact
