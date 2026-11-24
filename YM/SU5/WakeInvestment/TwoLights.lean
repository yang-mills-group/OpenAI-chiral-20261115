import YM.SU5.WakeInvestment.Viewport
import YM.SU5.WakeInvestment.StageLease
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
variable {z A c:ℝ}
local notation "ξ" s:max => meterC (hat P.R.L P.x s)
open Regis Gleam Tempest
open scoped Topology ContDiff
local notation "θ" s:max => (Papal.xhood (P:=P) s)
local notation "N" s:max i:max => (side Y i s)
open MeasureTheory

/-! Combining Hodge & RootV — WA.11 whole signed Wick comparison.
 SLA is read requested first-Pane civic/Wick signature Φ, testing Forecast on that signature
 (scheduled with s only witnesses transfers to further fixed aperture appointments through
 mpi/k). LightBar on *any* copy or pose furnishing Mark τ and its interpolants. As usual this
 is tested against the actual chart in use. α kept for ALL configurations separately on same Pane;
 even shifting from gauge test to Fock hypotheses. No volume priced relative to races not counted
 in this chloral computation. Slight renewal WA: requires signed leading hypothesis directly
 on real W cost in both types of tests. Later Mark purchasers must PROVE Tag premises for their
 comparisons, especially for point-force hypotheses actually at the torus calibrations (do not
 assume their transfers to finite-difference derivatives).
 -/
open WakeInvestment Gleam.Wake
open Lamour.Bridge Celeste Clock Hookah Tapestry Cliplet
variable (s i k : ℕ)
local notation "X" s:max => hat P.R.L P.x s
local notation "χ" s:max c:max => WakeInvestment.chip (hat P.R.L P.x s) c
local notation "Θ" T:max=> tollR T
local notation "Υ" T:max=> tabμ T
local notation "wax" s:max=> (Υ (θ s))
local notation "ℓop" s:max i:max k:max t:max=> (WakeInvestment.weighted (spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))) t (flatShear Y s i k))

abbrev possession {n:Side}(S:Support (More n)) := univ.filter (fun i:Lattice.Face (Per (More n))=> touched i⊆S)

abbrev LeadVision (s i k:ℕ)(α:ℝ)(j:Side)(r:Ratio j (More (N s i))) (S:Support (More (N s i)))(φ:Pane (N s i)→ℝ):= let G:=RootBook Y i k s; let L:=Y.uv k-s; Forecast (P.V.L.mood L) (P.V.L.tied L) (tollR (hat P.R.L P.x s)) G.p r (radiusB (hat P.R.L P.x s)) α G.beta (ageC (X s)) (shieldC (X s)) (tabμ (X s)) (tabμ (X s)) S φ
structure LightBar (m:ℕ) (α:ℝ) (F:Hookah (N s i)) (φ:Pane (N s i)→ℝ) : Prop where
 owner: AtSupport false F.S F.x
 weld: covariant F.x
 charge: ∀ x:Fields (N s i), ∀ t:ℝ,0≤t→ t≤1→ ‖(ℓop s i k t).glow (F.x x-1)‖ ≤ χ s (-198)
 line: ∀ U:Fields (N s i), ordinary (n:=N s i) (possession (n:=N s i) F.S) (α*(RootBook Y i k s).p.threshold) U.1 → Tiny F.S U.1 (skyline (hat P.R.L P.x s)) →
   ∃ (G:FC (Single (N s i)))(δ:ℝ),
     Lyrics (modesIn _ F.S) m (χ s (-199)) G ∧
     (noble Y s i k G).re+δ ≤ φ U.1+tabμ (hat P.R.L P.x s) ∧
     ∀ t:ℝ,0 ≤ t→ t≤1→ ‖(ℓop s i k t).glow (F.x U-1) - (ℓop s i k t).glow G‖ ≤ δ

lemma possession_move {S:Support (More n)} (f:ℝ) (U:Pane n) (p: ordinary (possession (n:=n) S) f U) (g:Seat n→SU.E) : ordinary (possession (n:=n) S) f (Lattice.gauge g U):= fun i q=> by rw [face_gauge,Gauge.chord_conj]; exact p _ q
variable {b d m p:ℕ} {A:ℝ}
variable {L:List (Hookah (side Y i s))}{φ:Fin L.length → Pane (side Y i s) →ℝ}
local notation "F0" i:max => L.get i
variable {α:ℝ} {F:Hookah (side Y i s)} {H:Real.exp 1≤P.x}
-- report. omitting root-count via `shell horizon` not allowed.
local notation "Ϟ" s:max => gateC (X s)
local notation "𝐃" NN:max => (More NN).val^4
abbrev crescent (z:ℝ)(L:List (Hookah (N s i)))(φ:Fin L.length→ Pane (N s i)→ℝ) (x:Pane (N s i)):ℝ:= let T:= RootBook Y i k s; let v:=tollR (X s); (∑ j, φ j x)+ (2*tabμ (X s))*L.length+ Ϟ s *flakes (shieldC (X s)) x+2*v*flakes (z*T.p.threshold) x
variable (q:castLeases Y s H A)(S:Shellac F p L) (h:∀ j,LightBar Y s i k m α (L.get j) (φ j))(wTall:(terrace (hat P.R.L P.x s)).val≤ (More (side Y i s)).val)
variable {c:Side}{r:Ratio c (More (side Y i s))}(pL:affordableRatio Y s i c r)(w:∀ j,LeadVision Y s i k α c r (L.get j).S (φ j))
include S
lemma afar_fitting : Set.PairwiseDisjoint Set.univ (fun j:Fin L.length=> (L.get j).S) :=by
 intro i t j c v; have ht:Distant (p+1) (L.get i).S (L.get j).S:= ((lt_or_gt_of_ne v).elim (fun v=> S.annex.rel_get_of_lt v) fun p=> Distant.symm (S.annex.rel_get_of_lt p)); apply disjoint_left.mpr; intro i w l; have hv:=ht i w i l; rw [separation_self] at hv; omega

include q pL w
lemma count_hall :
     LeadHall Y s i k α 1 (spectacles φ) c r (3*tabμ (X s)* L.length) := by
 constructor; intro v; have he:0≤ Θ (θ s):=(chip_pos ..).le; have hz:0≤tabμ (X s):=(chip_pos ..).le
 let C:= tollR (X s); let n:=side Y i s; let D:=RootBook Y i k s; let F:=Y.uv k-s
 obtain ⟨W,hW,b1,b2,c0,e⟩:=scenery (α:=α) (P.V.L.mood F) (P.V.L.tied F) (afar_fitting Y s i S) w v 0 pL.paying pL.horizon he hz _ q.wall;
 refine ⟨W,Fintype.card (Fin L.length)*tabμ (X s), C*(Fintype.card (Fin L.length):ℝ), C*Real.sqrt (Fintype.card (Fin L.length)), hW,b1,b2,?_,e⟩
 rw [mul_pow C,Real.sq_sqrt (Nat.cast_nonneg _),one_pow,mul_one]; rw [Fintype.card_fin] at * -- maybe lengths
 linarith only [c0, mul_le_mul_of_nonneg_left q.gauss (Nat.cast_nonneg (α:=ℝ) L.length)]

omit pL
include h wTall
lemma thickly (B:ℕ)(x:Orbit (N s i)) (t:(B:ℝ)≤ sPow P s A) (he:𝐃(N s i)≤ L.length*(4*(B+addgap (tent Y H)))^4) : Fitting Y s i k (χ s (-199)) (χ s (-198)) (crescent Y s i k α L φ x.1) m (strips Y s i L) x:= by
 let κ:= χ s (-198); let ε:=χ s (-199); let G:=RootBook Y i k s; let C:= (Y.voyage i).CapeT s; let n:=side Y i s; let Ng:= More n
 let I:=Fin L.length; let g:= atFrame Y s i x; let Z:Fields n:= (x.1,C x); let T:= simultaneous g Z; let Xc:= hat P.R.L P.x s; let D:= α*G.p.threshold; let τ:= tabμ Xc
 let U:= gauge g x.1; let M:= shoreline (shieldC Xc) (terrace Xc) P.J.n C x
 let A'(i:I):=(L.get i).S; let A''(i:I):= modesIn n (A' i); let focal (j:I):=flatSeat Y s i (strips Y s i L) j x; let N' (j:I):= possession (n:=n) (A' j); let Y'(j:I):=ordinary (N' j) D x.1; let F'(j:I):= A' j⊆ M; let V:= tollR Xc; let a:= shieldC Xc; let Wd:=terrace Xc
 let E ℓ:=(ℓop s i k ℓ); have hp:Set.PairwiseDisjoint Set.univ A':= afar_fitting Y s i S; have ht:focal=fun j=> (L.get j).x T-1:=by
    funext j; unfold focal flatSeat; rw [moved_root]; change twist (quantU (tradew n g)) ((L.get j).x Z-1)=(L.get j).x T-1; rw [map_sub,map_one, show (L.get j).x T = _ from (h j).weld g Z]
 have hh: Tiny M U (skyline Xc):= (near_lamp _ _ (Papal.roofage Y i s) (BProof.coin_pos .. |>.le) q.shellL x).raise (Subset.refl _) q.siren
 have hζ:κ ≤ V:=q.toll_ge; let ypd0:=t; have hV:0≤V:=(chip_pos ..).le; have hT:0≤τ:=(chip_pos ..).le
 have hz (j:I): ∃ u δ, Lyrics (A'' j) m ε u ∧ (noble Y s i k u).re+δ ≤ φ j x.1+τ+ ((if Y' j then 0 else 2*V) + if F' j then 0 else 2*V) ∧ ∀ ℓ:ℝ,0≤ℓ→ ℓ≤1→ ‖(E ℓ).glow (focal j)-(E ℓ).glow u‖ ≤ δ := by
    have hc:0 ≤ if Y' j then 0 else 2*V:=by split <;> positivity
    have hv:0 ≤ if F' j then 0 else 2*V:=by split <;> positivity
    rw [ht]; have hB (x):= (h j).charge x
    by_cases k':Y' j∧ F' j
    · obtain ⟨a,e,g1,h,z⟩:=(h j).line T (possession_move _ x.1 k'.1 g) (hh.raise k'.2 le_rfl);
      rw [show T.1=U from rfl, show φ j U = _ from (w j).inv g x.1] at h; exact ⟨a,e,g1,h.trans (le_add_of_nonneg_right (add_nonneg hc hv)),z⟩
    refine ⟨0,κ,(Lyrics.zeroS ..).expend le_rfl (chip_pos ..).le,?_,?_⟩
    · rw [noble_linear,map_zero,Complex.zero_re,zero_add]; have hl: - V ≤ φ j x.1:= (abs_le.mp ((w j).price_ x.1)).1; by_cases h:Y' j; · rw [if_pos h,if_neg (show ¬ F' j from fun b=> k' ⟨h,b⟩),zero_add]; linarith only [hT,hV,hζ,hl]
      rw [if_neg h]; linarith only [hT,hV,hζ,hl,hv]
    · intro ℓ p b; rw [show (E ℓ).glow 0=0 from map_zero (E ℓ).glowHom,sub_zero]; exact hB _ ℓ p b
 let R:= gateC Xc; let T:=L.length; choose u δ hL hM w' using hz
 refine ⟨⟨A'',?_,u,δ,hL,fun j y k l=>⟨w' j y k l,?_⟩,?_⟩,fun _ _=>strip_comm Y s i S _ _ _⟩
 · intro i z j h v; exact disjoint_left.mpr (fun x e f=> disjoint_left.mp (hp z h v) ((modes_at ..).mp e) ((modes_at ..).mp f))
 · change ‖(E y).glow (focal j)‖ ≤ κ; rw [ht]; exact (h j).charge _ y k l
 apply le_trans (sum_le_sum (fun j _=> hM j)); rw [sum_add_distrib,sum_add_distrib,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin]
 have he':Set.PairwiseDisjoint Set.univ N':= fun j u k p v=> disjoint_left.mpr (fun i t w=>disjoint_left.mp (hp u p v) ((mem_filter.mp t).2 (Work.E01.base_touched i)) ((mem_filter.mp w).2 (Work.E01.base_touched i)))
 let H0:= flakes a x.1; have hA:0 ≤ H0:= Nat.cast_nonneg _; let Yc:= shoreDust P.J.n Wd
 let hm:= mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).2 (satellites N' D x.1 he')) (mul_nonneg (by norm_num:(0:ℝ)≤2) hV)
 have hu:(∑ j:I, if Y' j then 0 else 2*V) ≤ 2*V*flakes D x.1:=by
    have hh(j:I):(if Y' j then 0 else 2*V)=(if ¬Y' j then 2*V else 0):=by simp
    simp_rw [hh,←sum_filter]; rw [sum_const,nsmul_eq_mul]; change (missAll N' D x.1:ℝ) * (2*V)≤_; rw [mul_comm (2*V) (flakes ..)]; exact hm
 have hz:(∑ j:I, if F' j then 0 else 2*V) ≤ T*τ+ R*H0 :=by
    have hh(j:I):(if F' j then 0 else 2*V)=(if ¬F' j then 2*V else 0):=by simp
    simp_rw [hh]; rw [←sum_filter]; rw [sum_const,nsmul_eq_mul]; let K:ℝ:= Ng.val; let y:= (4*((B:ℝ)+(addgap (tent Y H):ℝ)))^4; have hf: K^4 ≤ T*y:=by unfold K y; exact_mod_cast he
    have hv:= mul_le_mul_of_nonneg_right ((Nat.cast_le (α:=ℝ).mpr (lacking A' hp M)).trans (surcharge (Papal.roofage Y i s) q.shellL x Wd wTall) : ((univ.filter fun j=> ¬ F' j).card:ℝ)≤ 24/(Wd.val:ℝ)*K^4 + Yc* H0) (show 0≤2*V from by positivity)
    refine hv.trans ?_; have he:2*V*(24/(Wd.val:ℝ))*y ≤ τ := q.costC _ t
    nlinarith only [mul_le_mul_of_nonneg_right q.frameCoin hA,mul_le_mul_of_nonneg_left hf (show 0≤V*(24/(Wd.val:ℝ)) from by positivity),mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (α:=ℝ) T)]
 unfold crescent; linarith only [hu,hz]
#print axioms thickly
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
