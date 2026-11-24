import YM.SU5.Regis.Visitations

/-! # Y.4 switch. Read again at the present invoice, adapted from (non-build) Silk/Span/Frost and Thin/Aisle/Terrace. Need its rate even in switching final *sharp* checker back to heat on joint diagonal. -/

/-!
# Variant of bridge for the actual-first normalization route

This version yields uniform price loss *on the cone* from real horizontal rates.
Apply it after each-period elections at the common pivot; it does not extend
CapP pricing to unsampled periods or cutoffs.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {h x delay wα y : ℝ} {C D Q R0 E Cf δ Fp : ℝ→ℝ} {P : Prescription R B} {W0 : Cape m B R.L}
    {n b N0 : ℕ} {T : Month x 1 6 2 N0 V W} {f B0 : ℕ → ℝ} (ht : T.q ≤ m.val)
    {D' : Heron V 1 2 6 N0 0 J q h wα R0 E Cf δ y} {hy : y ≤ x} {V0 Jx : ℕ → ℝ}
local notation "Ω" => cell m B R.L
local notation "kT" => trunkY n b
local notation "kS" => buoy n
local notation "B'" => ActualSpine T ht W0 f kT
local notation "BT" => Actual T ht W0 f kT
local notation "Yb" i:max => dleaf R.L (hat R.L x i)
local notation "Γ" => StarPS kT
local notation "Φ" i:max => wage_B n b i R.L x
open FullBill Marks
namespace Donor
lemma funnel_pose (i:ℕ) (b:ℕ)(ρ ε τ:ℝ) (he:0 < ε) : ∀ᶠ n in atTop, ∀ m:Side, cone b n m → Real.exp (ρ*game m)*divisionBill T C τ i n m ≤ ε:=by
 let Vq:= volumePrice T i+1; let t:= thermalCost C R x τ i*postage B R.L i; let u:=expense C R x τ i + |serviceCost T i|; let v:= u * postage B R.L i
 have p:= collapse b (c:=Real.log 2) (Real.log_pos (by norm_num)) (half_pos he) (horizontalPrice T i)
 filter_upwards [p (Vq+t+ρ),p (Vq+t+v+ρ)] with n h0 h1 m u0; specialize h0 m u0; specialize h1 m u0
 let x':= horizontalPrice T i* decay n (Real.log 2); let M:=game m; let V':= Real.exp (Vq*M); let T':= Real.exp (t*M); let E:=Real.exp (ρ*M); let C':= Real.exp (v*M); rw [show divisionBill T C τ i n m=(1+C')*(x'* V')*T' from ?_]; swap
 · unfold divisionBill outage T' C' V' x' M t v Vq u; rw [sites_postage, ←mul_assoc (thermalCost ..),←mul_assoc (_+|_|)];
 change E*((1+C')*(x'*V')*T') ≤ _
 simp only [add_mul,Real.exp_add] at h0 h1; have ht: x'*(V'*T'*E)≤ε/2:=h0; have hp: x'*(V'*T'*C'*E)≤ε/2:=h1; linarith only [ht,hp]
end Donor
open Preparation Buffered Afterglow Journey
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))
set_option maxHeartbeats 360000
namespace Papal
local notation "N" s:max i:max=> count Y s i
/-- Including exponentially small ratio errors. -/
lemma pose_change (b C D:ℝ)(h:0<b)(s:ℕ):∀ᶠ k:ℕ in atTop,∀ i:ℕ,∀ h:(Y.voyage i).kick≤k,∀ f: Mark (count Y s i), Envelope f → (∀ x, ‖f x‖ ≤Real.exp (C*sites (count Y s i)))→ ‖compass Y i k s f-solder Y i k h s f‖ ≤ b/Real.exp (D*sites (count Y s i)):=by
 let y:= postage Λ.block Λ.R.L s; let C':=C*y; let D':=D*y
 filter_upwards [Y.heatGap s,Y.UV.tendsto_atTop.eventually (Donor.funnel_pose (T:=Y.meter) (C:=Λ.C) s Λ.b (C'+D') b Y.τ h)] with k t u i h' f p v
 have ht:=mark_pay ((Y.voyage i).ownership s|>.paid.bill) p
 let Q:= sites (count Y s i); let β:= Donor.divisionBill Y.meter Λ.C Y.τ s (Y.ivory k) (Y.ir i); let a:=game (Y.ir i)
 have hQ:Q=y * a:=sites_postage ..
 have hz: Real.exp ((C'+D')*a)*β ≤ b:= u (Y.ir i) ((Y.voyage i).domain k h')
 apply le_trans (( (t.2 i h').mark_bound (Y.voyage i).funds _ ht.meas (fun x=> v _)).2.2); apply (le_div_iff₀ (Real.exp_pos _)).mpr
 change Real.exp (C*Q)* β* Real.exp (D * Q) ≤ _; rw [mul_right_comm, ←Real.exp_add, hQ, show C*(y*a)+D*(y*a)=(C'+D')*a by unfold C' D'; ring]; exact hz
end Papal
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.pose_change
