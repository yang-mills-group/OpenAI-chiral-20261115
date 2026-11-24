import ForceSatin.Outpost
import YM.SU5.Reconstruct.Bare
import YM.CF.Nova.Era
import YM.SU5.Six.RawWard
import YM.SU5.Hiro.Fresh
import YM.SU5.FiniteGaugeData.Tower.Baggage
import ForceSatin.Wallet
import ForceSatin.Ramp
import ForceSatin.Falcon
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey

open _root_.YM.Gleam.Luster.Risa Gentle Tiling
open BProof (scaleY PL)
open _root_.YM.Work.F03 _root_.YM.Regis
local notation "Uₛ" s:max i:max k:max => gram Y s i k
local notation "Kₛ" s:max k:max => Y.uv k - s
local notation "π₀"=> P.K.top.clip

-- uniform scalar exponents charges
open _root_.YM.Next.Rank.Spindle
open Gentle.Solace Rail
open _root_.YM.Regis.Resonance Lull
open Fineness
namespace Moon
-- genuine Mark polynomial & cost. Keep support and masks explicit; period registration asserted separately
variable {N:Side}{cN:Side}{r:Lattice.Ratio cN (More N)} (T:Tiling cN N r)
variable (S:Support (More N)){H₁:Bed} {Z:PathData SU.group}  {q:Clip} {η CS W t x β y:ℝ}
variable (R:Rules SU.group)(B:Z.Bounds q η CS W) (P₁:Attached H₁ Z)(L:Side)
variable {v' τ:ℝ}(M0:Floor H₁ q (More N) τ v') (O:Bid.Sworn H₁ (More N) SU.group)
open ProbabilityTheory
open Lifted Afterglow Satin Cygnet Loaves Horizons InnerProductSpace
open _root_.YM.Regis.Head
-- EB. proof. Bare β function & actual unweighted path. Off-path qualified support.Plan reweights all uses of auxiliaries. Not an iterated period limit of a common bare comparator.
open Tower Tapestry
open Reconstruction
namespace BareProgram
variable (b:ℕ→ℝ) (Hb:Real.exp 1≤P.x)
variable (i k s:ℕ)
local notation "Νℓ" => Journey.side Y i (Y.uv k)
noncomputable abbrev wKet (K:Evaluation (Journey.side Y i (Y.uv k))) (U:Pane (Journey.side Y i (Y.uv k))) := inner ℂ (mateK Νℓ) (acts (K U) (Vale.capP (K:=P.K) P.U (b (Y.uv k)) (Y.meter.a (Y.uv k)) U))
noncomputable abbrev bareW (A: Evaluation (Journey.side Y i (Y.uv k))) : ℂ:= ∫ U:Pane (Journey.side Y i (Y.uv k)), wKet Y b i k A U∂prior SU.group (More Νℓ)
noncomputable abbrev reR (ci t:ℝ) {n:Side}(U:Pane n):ℝ:= Real.exp (-((ci-t)*Vale.basicP P.K.top.clip U))
lemma reR_positive (ci t:ℝ) {n:Side} (U:Pane n):0<reR (P:=P) ci t U:=Real.exp_pos _
lemma reR_meas (ci t:ℝ) {n:Side}: Envelope (reR (P:=P) ci t (n:=n)):= Env.compact (Real.continuous_exp.comp (continuous_const.mul (Nova.ren_c ..)).neg)
abbrev bareβ :ℝ:=(gram Y (Y.uv k) i k).beta
lemma piWend {α β:ℝ}(U:Pane (Journey.side Y i (Y.uv k))) :
    (reR (P:=P) α β U:ℂ) • Vale.capP (K:=P.K) P.U β (Y.meter.a (Y.uv k)) U = Vale.capP (K:=P.K) P.U α (Y.meter.a (Y.uv k)) U:=by
 unfold Vale.capP reR; by_cases t: flags (Y.meter.a (Y.uv k)).threshold U=∅; swap; · simp [Set.indicator,t]
 simp_rw [Set.indicator_of_mem (show U∈ {U:Pane (Journey.side Y i (Y.uv k))| flags (Y.meter.a (Y.uv k)).threshold U=∅} from t), Complex.ofReal_exp,smul_smul,←Complex.exp_add]; congr 2; push_cast; ring
noncomputable abbrev reW {n:Side} (α β:ℝ)(A:Evaluation n) (U:Pane n): Fock.FC (Single n):=(reR (P:=P) α β U : ℂ) • A U
lemma reW_price (A:Evaluation (Journey.side Y i (Y.uv k))): wKet Y b i k (reW (P:=P) (bareβ Y i k) (b (Y.uv k)) A) = bareAmplitude Y i k A:=by
 funext t; unfold wKet reW bareAmplitude; rw [act_smul,← map_smul,piWend] -- argument implicit i,k dependencies
variable (p:(Y.voyage i).kick≤ k)
include p
lemma eb_reweighted (A:Mark (Journey.side Y i (Y.uv k)))(h:Envelope A):
    let T:=reW (n:=Journey.side Y i (Y.uv k)) (P:=P) (bareβ Y i k) (b (Y.uv k)); let D:=bareW Y b i k
    Integrable (wKet Y b i k (T 1)) (prior SU.group (More Νℓ)) ∧ Integrable (wKet Y b i k (T (diagMark A))) (prior SU.group (More Νℓ)) ∧ D (T 1) ≠0 ∧ Journey.compass Y i k (Y.uv k) A=D (T (diagMark A))/ D (T 1):=by intro T D; unfold D bareW T; rw [reW_price,reW_price]; exact ⟨(partitionIncome Y i k p).1,compassIncome Y i k h p⟩
lemma eb_off_integrable (A: Evaluation (Journey.side Y i (Y.uv k)))(h:Envelope A): Integrable (wKet Y b i k A) (prior SU.group (More Νℓ)):=by
 let t:= bareβ Y i k; let β := b (Y.uv k)
 let X:=reW (P:=P) β t A
 have hp:Envelope X:= Girt.kitE (reR (P:=P) β t) A (fun t V=> (t:ℂ) • V) (by fun_prop) (reR_meas β t) h
 have he: reW (P:=P) t β X=A:=funext fun u=>by unfold X reW reR; rw [smul_smul,← Complex.ofReal_mul,← Real.exp_add, show - (_*_)+(-((β-t)*_))=0 from ?_,Real.exp_zero,Complex.ofReal_one,one_smul]; ring
 rw [← he]; exact (eb_reweighted Y b i k p (toMark X) (Env.along hp measurable_fst)).2.1
-- top output journey. retain ASC tree of ascender, **support** through lemma.sch.Forest. (covariance if input is, including team mark_.).
def RampCore (Y:Course P (VolumeCape.Dream.Nimbus l)) (i k s:ℕ) (S:Finset Cover) (t:ℕ) (F:Mark (Journey.side Y i s)) : Mark (Journey.side Y i (s+t)):= match t with| 0=> F| n+1=> ascender Y (s+n) i k (RampCore Y i k s S n F) -- s+n+1 defeq
noncomputable abbrev topW (g:s≤ Y.uv k) : Mark (Journey.side Y i s)→Mark (Journey.side Y i (Y.uv k)) := fun V=> (show s+(Y.uv k-s)= Y.uv k from (by omega)) ▸ RampCore Y i k s ∅ (Y.uv k-s) V -- type notational.cast.See simplify.S argument phantom: remove
noncomputable abbrev stackB (P:Preparation)(l:ℕ)(t:ℕ)(S:Finset Cover):= (followBox (Λ:=P) (l:=l))^[t] S
lemma ramp_paid(s t:ℕ)(e:s+t ≤ Y.uv k)(V:Mark (Journey.side Y i s)){S:Finset Cover} (P':AtSupport false (Satin.region S _) V): let Z:= RampCore Y i k s ∅ t V
    Journey.compass Y i k s V=Journey.compass Y i k (s+t) Z ∧ AtSupport false (Satin.region (stackB P l t S) _) Z ∧ (covariant V→covariant Z):=by induction t with
 | zero=>exact ⟨rfl,P',fun x=>x⟩
 | succ n ih=>
    obtain ⟨t,f,g⟩:= ih (by omega); let Yρ:= RampCore Y i k s ∅ n V; let q:Satin.PairIdx Y (s+n) i k:=⟨p,e⟩; intro Z
    have hw:stackB P l (n+1) S = _ := show stackB P l (n+1) S=followBox (stackB P l n S) (Λ:=P) (l:=l) from iterate_succ_apply' _ _ _ -- notation binder
    rw [hw]; exact ⟨t.trans (partake Y (s+n) i k q (f.mono (subset_univ _))),ascendSupport Y (s+n) i k _ q f,fun hh=>Tapestry.ascendGauge Y (s+n) i k q f (g hh)⟩ -- dot
lemma ramp_top (s:ℕ)(e:s≤ Y.uv k)(V:Mark (Journey.side Y i s)){S:Finset Cover} (P':AtSupport false (Satin.region S _) V):
    let Z:=topW Y i k s e V; Journey.compass Y i k s V=Journey.compass Y i k (Y.uv k) Z ∧ AtSupport false (Satin.region (stackB P l (Y.uv k-s) S) _) Z ∧ (covariant V→covariant Z):=by
 -- cast via `s+k-s`; not rewriting at scale elsewhere
 let h:= show s+(Y.uv k-s)= Y.uv k from (by omega); exact aux_ _ _ _ h (ramp_paid Y i k p s _ h.le V P')
where
 aux_ {S :Finset Cover} (z:ℂ) (t:Prop){j: ℕ}(v:Mark (Journey.side Y i j)){t':ℕ}(h:j=t')(p:z=Journey.compass Y i k j v ∧ AtSupport false (Satin.region S _) v ∧ (t→covariant v)) : z= Journey.compass Y i k t' (h ▸ v) ∧ AtSupport false (Satin.region S _) (h ▸ v :Mark (Journey.side Y i t')) ∧ (t→covariant (n:=Journey.side Y i t') (h ▸ v)):=by subst t'; exact p
lemma off_belong (Q:s≤ Y.uv k)(F:Mark (Journey.side Y i s)){S:Finset Cover}(u:AtSupport false (Satin.region S _) F): let Z:=topW Y i k s Q F; let T:= reW (n:=Journey.side Y i (Y.uv k)) (P:=P) (bareβ Y i k) (b (Y.uv k)); let V:= bareW Y b i k;
    Journey.compass Y i k s F= V (T (diagMark Z)) / V (T 1) ∧ V (T 1)≠0 ∧ AtSupport false (Satin.region (stackB P l (Y.uv k-s) S) _) (toMark (diagMark Z)) ∧ (covariant F→ covariant (toMark (diagMark Z))):=by
 obtain ⟨h,f,v⟩:= ramp_top Y i k p s Q F u; let U:= eb_reweighted Y b i k p _ f.env; intro Z T V; exact ⟨h.trans U.2.2.2,U.2.2.1,diagAt f,diag_cov ∘ v⟩
omit p
-- actual path on the coherent Spine only. later specializations pass Picker with U≤ and coupled s. No second election. shift EB θ.
variable {u v A D:ℕ→ℕ} {I E} (U: Universal Y Hb u v I E){F} (Q: Tower.Coherent Y Hb (i:=u) (k:=v) (E:=E) F A D)
local notation "t₀"=> u ∘ A
local notation "t₁"=> v ∘ D
local notation "tₚ"=> Y.uv ∘ t₁
def BareChosen (i k:ℕ→ℕ) (b:ℕ→ℝ):Prop:= (∀ i,0<b i)∧∀ n, b (Y.uv (k n))= bareβ Y (i n) (k n)
include U Q in
lemma patriarch : ∃ b:ℕ→ℝ, BareChosen Y t₀ t₁ b:=by
 have h: StrictMono (tₚ):= Y.uv_grows.comp (U.pick.grow_k.comp Q.growsB); let t:= fun i=> bareβ Y (t₀ i) (t₁ i)
 let w(f:ℕ):= if a:∃ i,tₚ i=f then t (Classical.choose a) else 1; refine ⟨w,fun i=>?_,fun n=>?_⟩
 · unfold w; split; swap; · exact zero_lt_one
   have hp(i): 0<t i:=by let s:=tₚ i; have he:0<ℶ s:= (Real.exp_pos 1).trans_le (Hb.trans (Vale.crown ..)); exact (half_pos he).trans_le (prices_plot Y s (t₀ i) (t₁ i) (show s ≤ Y.uv (t₁ i) from le_rfl)).2.2.2.1.1; -- tune
   exact hp _
 let p:∃ i,tₚ i=tₚ n:=⟨n,rfl⟩; change w ((tₚ) n)=t n; unfold w; rw [dif_pos p,h.injective (Classical.choose_spec p)]
lemma reW_self (a:ℝ) {n:Side} : reW (P:=P) (n:=n) a a=_root_.id:=by funext A U; simp [reW,reR]
include U Q in
lemma on_itinerary (B:BareChosen Y (t₀) (t₁) b)(s:ℕ) : ∀ᶠ n in atTop,∀ V:Mark (Journey.side Y ((t₀) n) s),∀ S:Finset Cover, AtSupport false (Satin.region S _) V →
    let i:=t₀ n; let k:= t₁ n; let U:=bareW Y b i k
    U 1≠0 ∧ ∃ h:s≤Y.uv k,let W:= toMark (diagMark (topW Y i k s h V)); Journey.compass Y i k s V= U (diagMark (topW Y i k s h V))/U 1 ∧ AtSupport false (Satin.region (stackB P l (Y.uv k-s) S) _) W ∧ (covariant V→ covariant W):=by
 filter_upwards [Q.finance s] with i p V S h i0 k W; obtain ⟨s',w,P,t⟩:= off_belong Y b i0 k s p.depth p.enters V h
 have E: b (Y.uv k)= bareβ Y i0 k:=B.2 i
 simp_rw [E,reW_self] at s' w -- rewrite changes U? unfolds reprogram issue
 exact ⟨w,p.enters,s',P,t⟩
#print axioms off_belong
#print axioms on_itinerary
end BareProgram
end Moon
end Papal
end LocalLimit
end Rate
end YM.CF.Py
