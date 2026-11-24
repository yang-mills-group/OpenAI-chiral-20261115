import YM.SU5.Selected.Dais.Loom
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew
open Chene.Perks
namespace LocalLimit
open Preparation
namespace Rundle
open CF.Pannier Chancel Chancel.Rous Damask Dais.Parity Papal Buffered Afterglow.Journey
variable {Λ:Preparation} {l':ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l'))
local notation "G₅"=>SU.group
local notation "ε₀"=>Papal.Mileage.austere
variable {t u Q ε v:ℝ}
abbrev capNorm (s i k:ℕ)(F:Mark (age Y i s))(T:Orbit (age Y i s)):ℂ:=let V:= RootBook Y i k s; let f:= dawnM Y s i; letterRead (F (T.1,f T)) (Graph.recX Λ.U V f T) / milli Y i k s
def eternal (t ε:ℝ):Prop:= ∀ κ:ℝ, ∀ᶠ s in atTop, ∀ i k:ℕ,s≤ Y.uv k→ (Y.voyage i).kick≤k → ∀ (T:ℝ)(F:Mark (age Y i s)),Envelope F → IcyBudget Y t T s i k κ F → ∫ x, ‖capNorm Y s i k F x‖ ∂ city (age Y i s) ≤ Real.exp (ε*sites (age Y i s)+T)
lemma creedI (s i k:ℕ)(F:Mark (age Y i s)): compass Y i k s F=∫ x, capNorm Y s i k F x∂city (age Y i s):=by
 unfold Afterglow.Journey.compass; rw [←same_ratio]; unfold capNorm; rw [integral_div] ; rfl
lemma eternal_c (p:Λ.d≤ ε₀)(H:Scooped Λ)(h:0<t)(u:t≤1)(v:0<ε): eternal Y t (season_tip (Λ:=Λ)*t^2+ε):=by
 intro κ; filter_upwards [theta_upper Y t h u p (ε/2) (half_pos v) κ,signsF Y H _ (half_pos v)] with s P Q i k hs hh T F e he
 let R:= marks Y i k s; let N:=age Y i s; let n:= sites N; let f:= dawnM Y s i; let V:= RootBook Y i k s; let Z:= ∫ x, ‖letterRead (F (x.1,f x)) (Graph.recX Λ.U V f x)‖ ∂city N; let A:=milli Y i k s; let L:= (season_tip (Λ:=Λ)*t^2+ε)*sites N+T
 have hA: Real.exp (R-ε/2*n) ≤ ‖A‖:= Q i k hh hs; have hv:0<‖A‖:=(Real.exp_pos _).trans_le hA
 simp_rw [capNorm,norm_div,integral_div]; change Z/‖A‖ ≤ Real.exp L; apply (div_le_iff₀ hv).mpr; refine le_trans (P i k hs hh T F e he) ((mul_le_mul_of_nonneg_left hA (Real.exp_pos L).le).trans' ?_); apply Eq.le; rw [←Real.exp_add]; unfold R L n; congr 1; ring
lemma eternal_m (h:eternal Y t u)(p:u≤v) : eternal Y t v:= fun k=> (h k).mono (fun _ g i j b α c F pF hF=> (g i j b α c F pF hF).trans (Real.exp_le_exp_of_le (add_le_add (mul_le_mul_of_nonneg_right p (zero_le_one.trans (sites_pos _))) le_rfl)))
theorem frost_voice(t:ℝ)(h:0<t)(u:t≤1)(l:Λ.d≤ε₀)(H:Scooped Λ) : eternal Y t ((season_tip (Λ:=Λ)+1)*t^2):= eternal_m Y (eternal_c Y l H h u (pow_pos h 2)) (by rw [_root_.add_mul,one_mul])
theorem compass_p (p:eternal Y t v)(κ:ℝ): ∀ᶠ s in atTop, ∀ i k:ℕ,s≤ Y.uv k→ (Y.voyage i).kick≤k → ∀ (T:ℝ)(F:Mark (age Y i s)),Envelope F → IcyBudget Y t T s i k κ F → ‖compass Y i k s F‖ ≤ Real.exp (v*sites (age Y i s)+T):=by
 filter_upwards [p κ] with s p i k α β c F h u; rw [creedI]; exact (norm_integral_le_integral_norm ..).trans (p i k α β c F h u)
structure Strobe(t:ℝ)(T:ℝ)(s i:ℕ)(F:Mark (age Y i s)): Prop where
 epoch: ∀ x, ∃ n, Riser n (F x) ∧ t⁻¹^n* ‖F x‖≤Real.exp T
lemma strobe_meet(p:0<t)(u:t≤1)(h:t⁻¹≤Λ.h) (s i k:ℕ){F:Mark (age Y i s)}(l:Strobe Y t Q s i F): IcyBudget Y t Q s i k 0 F:=by
 intro x; let M:=blood Y i k s; let f:=dawnM Y s i; let E:= F (x.1,f x); let W:=spar Λ.K.j M (f x); let N:=age Y i s; obtain ⟨e,v⟩:=Papal.safety Y s i k x; obtain ⟨n,d,g⟩:=l.epoch (x.1,f x); have ht:= psych (M:=mateK N) e p u h v d; refine ht.weigh ?_ (zero_le_one.trans Λ.height); let f₀:=‖driftW (cards W t) (mateK N)‖; apply (mul_le_mul_of_nonneg_right g (show 0≤f₀ from norm_nonneg _)).trans_eq
 rw [show f₀= Real.exp (logo t Λ.K.j M (f x)) from powerR e p u, zero_mul,add_zero,Real.exp_add] -- tune
lemma strobe_cost(p:0<t)(u:t≤1)(h:t⁻¹≤Λ.h)(t':eternal Y t ε): ∀ᶠ s in atTop,∀ i k,s≤Y.uv k → (Y.voyage i).kick≤k → ∀ (T:ℝ)(F:Mark (age Y i s)), Envelope F → Strobe Y t T s i F→ (∫ x, ‖capNorm Y s i k F x‖ ∂ city (age Y i s)) ≤ Real.exp (ε*sites (age Y i s)+T):=
 (t' 0).mono fun s v i k α β c F hF X=> v i k α β c F hF (strobe_meet Y p u h s i k X)
-- actual signed total variation (no sources) near arbitrary ε can be purchased WITH this. This is absolute scalar integrals, not sup operator norm.
lemma strobe_one(s i:ℕ):Strobe Y t 0 s i 1:=⟨fun x=>⟨0,Riser.one,by simp⟩⟩
def wavering (ε:ℝ) := ∀ᶠ s in atTop,∀ i k,s≤Y.uv k → (Y.voyage i).kick≤k → (∫ x,‖capNorm Y s i k 1 x‖∂city (age Y i s))≤ Real.exp (ε*sites (age Y i s))
lemma minute(p:0<t)(u:t≤1)(h:t⁻¹≤Λ.h)(t':eternal Y t ε): wavering Y ε:=(strobe_cost Y p u h t').mono fun i v n k hn p=> by simpa only [add_zero] using v n k hn p 0 1 (Girt.rite_c (1:FC _)) (strobe_one Y ..) -- tune Envelope 1 not Measure? F matrix; use Girt
end Rundle
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Rundle.frost_voice
#print axioms YM.CF.Py.Rate.LocalLimit.Rundle.minute
