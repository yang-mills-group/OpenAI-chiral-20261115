import ForceSatin.Boater
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
variable {h z:ℝ}
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


variable {N:Side} {b C:ℝ} (c:0<b)(mail:CF.Papyrus.Franc.postage 4 b)
-- all checker boards tested (need not preserve actual history under a mirror). Used through one aperture and all genders.
variable {cN:Side}{r:Lattice.Ratio cN (More N)}{T:Tiling cN N r}{H:Precision.Bed}{Z:PathData G5}{P₁:Attached H Z}
 {p:BudgetPoint} {q:Clip} {η CS W:ℝ}{B: Z.Bounds q η CS W}
 {m n D:ℕ} {τ β ψ A L ν δ cost:ℝ}{Q:Wave (Single N)}

-- data type of all tester x; depend T to apply switch lemma
structure Page (N:Side) {c:Side} {r:Lattice.Ratio c (More N)} (T:Tiling c N r) (L:Side)(m:ℕ){q:Clip}(B:Z.Bounds q η CS W)(P₁:Attached H Z)(p:BudgetPoint)(τ β x d ψ Υ ℓ:ℝ)(Q:Wave (Single N)) where
 test_ : Evaluation N
 S : Support (More N)
 permit : WaxCheck T L m B P₁ p τ β x d ψ Υ ℓ Q test_ S

variable {L₀:Side}{x d ℓ Υ:ℝ}
namespace Page
local notation "℘" => Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q
lemma pageEnv (G:Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q): Envelope (1+toMark G.test_) := ((AtSupport.oneM _).addM G.permit.1).env

lemma swipe {J:Type}(L:List J)(f:J→ Evaluation N)(h:J→ Mark N)(p:∀ i,h i=1+toMark (f i)): (L.map h).prod= veilProd (f ∘ L.get) (List.finRange L.length):=by
 rw [veilEq]; let V(i:Fin L.length):= L.get i; rw [show L.map h=((List.finRange _).map (fun i:Fin L.length=>h (V i))) from (by rw [show ((fun i:Fin L.length=>h (V i)))= Function.comp h V from rfl,← List.map_map,List.map_get_finRange])]; simp [p, V] -- dependent rewrite cast

def board {K:Calibration}{m':Side} {r:Lattice.Ratio cN (More (K.c m'))} {T:Tiling cN (K.c m') r} (pH:HaloTw 4 (K.c m')){Q:Wave (Single (K.c m'))}{M:Male}(hQ:Sea (FlatPaneP 4 M (K.c m')) Q):
   Sport K m' (K.c m') (Page (K.c m') T L₀ m B P₁ p τ β x d ψ Υ ℓ Q) where
 place G:= G.S
 pose G:= 1+toMark G.test_
 mirror i z G := ⟨Buffered.refl i (Heat.gaugeShift K.B z) G.test_,G.S.image ((Buffered.plane i (Heat.gaugeShift K.B z)).anon (K.c m')),reflW pH hQ G.permit i (Heat.gaugeShift K.B z)⟩
 castM _ z:=z
 stage _ _ o u:= ((AtSupport.oneM _).addM o.permit.1).mono u
 charge a z o _:=by
    let N:=(K.c m'); let t:= Heat.gaugeShift K.B z; let U:=carR a t N; funext x; change 1+toMark (Buffered.refl a t o.test_) x = theta U (1+toMark (o.test_) _); rw [reflEval,theta_add,theta_one]; rfl
 town _ _ _:=rfl
lemma portrait (X:Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q): ∀ i:Fields N,‖(1+toMark X.test_:Mark N) i‖ ≤ Real.exp (180^m*d):=by
 intro i; let K₀:=tailor (1:UNI (Single N)); have hv:fiber K₀ 1:=by constructor <;> intro i <;> simp [basisKet, K₀,tailor] -- name
 have hg:‖X.test_ i.1‖ ≤ (180:ℝ)^m*d :=by
    have h:= Credential.glow (X.permit.2.2.1 i.1).harvest hv le_rfl; rw [one_pow,mul_one, show K₀.glow (X.test_ i.1)=(X.test_ i.1) from ?_] at h; exact h
    unfold K₀ Shaft.glow tailor; dsimp only; change quant 1*_ *quant (star 1)=_; rw [star_one,quant_one,one_mul,mul_one]
 exact (norm_add_le ..).trans ((add_le_add (le_of_eq norm_one) hg).trans (((Real.add_one_le_exp ((180:ℝ)^m*d))).trans' (le_of_eq (add_comm ..))))
lemma switched {m':Side} {K:Calibration} (U : Mark N→ℂ)(Z:Mark N→ℂ) (lV:ℝ)(g:N=K.c m') {M:Male}(A₀:HaloTw 4 N)(v:Sea (FlatPaneP 4 M N) Q) (q₀:Twosome K N U)(w:0<lV)(X:Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q) (x0 poseHere:ℝ)
 (lo:∀ F:Mark N,Envelope F→(∀ i, ‖F i‖ ≤ Real.exp (x0 * sites N))→ ‖Z F-U F‖ ≤ lV)
 (h:∀ L:List (Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q), sites N ≤ L.length * poseTill ((poseHere):ℝ) → -- add poseHere parameter
   L.Pairwise (Disjoint on Page.S) → ‖Z (veilProd (Page.test_ ∘ L.get) (List.finRange L.length))‖ ≤ Real.exp (L.length*lV))
 (b:ℕ)(pD:b+addgap K≤ N.val)(u: (↑(4*(b+addgap K):ℕ):ℝ)^4 ≤ poseTill ((poseHere):ℝ)) (c:∀ i,cows i X.S b)(wN:180^m*d ≤ x0):
    ‖Z (1+ toMark X.test_)‖ ≤ Real.exp (3*lV) := by
 subst N; let N:=K.c m'; let S:=(board (K:=K) (m':=m') A₀ v : Sport K m' N (Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q)); let F:= 1+ toMark X.test_; let T0:=sites N
 have he: Sport.race S [X]:=List.pairwise_singleton _ _
 obtain ⟨n,L,G,H,P,Qq,V⟩:= Sport.team S U q₀ [X] pD (fun i=>by change cows i (X.S ∪ ∅) b; simpa using c i) he
 rw [List.length_singleton,mul_one] at Qq
 let t:ℝ:= L.length; have hz:t≥1:=by unfold t; rw [Qq]; push_cast; exact one_le_pow₀ (one_le_pow₀ (by norm_num))
 have hl:t≤T0:=by unfold t T0 sites; rw [Qq]; exact_mod_cast G
 rw [show Sport.film S [X]=F from mul_one F,←Qq] at V
 let A:= Sport.film S L
 have hu:‖Z A-U A‖≤lV:=by
    have he(L:List (Page N T L₀ m B P₁ p τ β x d ψ Υ ℓ Q)) : Envelope (Sport.film S L) ∧ ∀ i:Fields N,‖Sport.film S L i‖≤Real.exp (x0*L.length):=by induction L with
    | nil=> exact ⟨(AtSupport.oneM univ).env,fun i=>by change ‖(1:FC _)‖ ≤ _; rw [norm_one]; simp⟩
    | cons i L ih=>
       let f:=1+ toMark i.test_; let F:=Sport.film S L
       change Envelope (f*F) ∧ _
       refine ⟨env_mult ((AtSupport.oneM _).addM i.permit.1).env ih.1, fun z=>?_⟩
       change ‖f z * F z‖ ≤ _
       apply (norm_mul_le ..).trans; apply (mul_le_mul ((i.portrait z).trans (Real.exp_monotone wN)) (ih.2 z) (norm_nonneg _) (Real.exp_pos _).le).trans; apply Eq.le; rw [←Real.exp_add,List.length_cons,Nat.cast_add,Nat.cast_one,mul_add,mul_one,add_comm]
    exact lo A (he L).1 (fun i=> ((he L).2 i).trans (Real.exp_monotone (mul_le_mul_of_nonneg_left hl (le_trans (mul_nonneg (by positivity) (X.permit.2.2.1 (1:Pane N)).nonneg) wN))))
 have hz': T0 ≤ t*(↑(4*(b+addgap K):ℕ):ℝ)^4:=by unfold T0 t sites; rw [Qq]; exact_mod_cast H
 have hg: ‖Z A‖≤ Real.exp (t*lV):=by
   unfold A Sport.film; rw [swipe L Page.test_ S.pose (fun _=>rfl)]; apply h L (hz'.trans (mul_le_mul_of_nonneg_left u (zero_le_one.trans hz))) P
 have hw:L.length≠0:=by intro e; unfold t at hz; rw [e] at hz; norm_num at hz
 have hw: ‖U F‖≤ Real.exp (2*lV):=by
    apply le_of_pow_le_pow_left₀ hw (Real.exp_pos _).le (V.trans ((norm_le_norm_sub_add (U A) (Z A)).trans _))
    rw [norm_sub_rev,←Real.exp_nat_mul, show (L.length:ℝ)*(2*lV)=t*lV+t*lV from (by unfold t; ring),Real.exp_add]
    have hh:lV+1≤Real.exp (t*lV):=(add_le_add_left (le_mul_of_one_le_left w.le hz) _).trans (Real.add_one_le_exp _); nlinarith only [hh,hu,hg,w]
 have hv: ‖Z F-U F‖ ≤ lV:= lo F ((AtSupport.oneM _).addM X.permit.1).env (fun i=> (portrait X i).trans (Real.exp_monotone (wN.trans (le_mul_of_one_le_right (le_trans (mul_nonneg (by positivity) (X.permit.2.2.1 (1:Pane N)).nonneg) wN) (hz.trans hl)))))
 refine (norm_le_norm_sub_add (Z F) (U F)).trans ((add_le_add hv hw).trans ?_); rw [show 3*lV=2*lV+lV from (by ring),Real.exp_add]; nlinarith only [Real.one_le_exp (show 0≤ 2*lV by positivity),Real.add_one_le_exp lV,w]
#print axioms switched

end Page
end Papal
end LocalLimit
end Rate
end YM.CF.Py
