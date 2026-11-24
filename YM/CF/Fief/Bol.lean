import YM.CF.Fief.Bank
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Fief
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open SectorNext.Remainder.Scales
variable {D L K:ℝ} (Q':Patch)
local notation "μ_"=>(Fintype.card SU.group.ColorIndex:ℝ)
local notation "B"=>radiusB
variable {q':Patch}{C t d w e A:ℝ}{f g :ℝ→ℝ}{n l m:ℕ}
def loomP(Q':Patch)(v:ℕ):ℕ:= Fintype.card Axis*Q'.L.val^4*(v+v+1)^4
lemma plo : sizeK Q'.L 0 (fun x=> (loomP Q' (3*radiusB x):ℝ)):=by
 unfold loomP; push_cast; let W:=(sizeK.Bcash Q'.L).scale 3; exact (((W.accrue W).accrue (sizeK.mild _ 1)).powC 4).scale _ -- type coercion direction check
lemma boon (k l:ℕ):sizeK Q'.L 0 (fun x=>(barkQ l k (radiusB x):ℝ)):=by
 unfold barkQ diameterW; push_cast; let P:= sizeK.Bcash Q'.L; let Q:= (P.scale (3*k)).accrue (P.scale ((l:ℝ)+70)); exact ((Q.accrue Q).accrue (sizeK.mild _ 1)).powC 4
lemma take_a(K:ℝ)(p:sizeK Q'.L 1 f) :∀ᶠ x:ℝ in atTop, 16* (loomP Q' (3*radiusB x):ℝ)*Real.exp (K*pathPay l)*μ_*2^n*f x ≤1/2:=by
 let C:= Real.exp (K*pathPay l); let A:=(16*C*μ_*2^n); filter_upwards [(((plo Q').tint p).scale A|>.spine).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2))] with x h; refine (le_of_eq ?_).trans h; unfold A C; ring
lemma grips{σ:ℝ}{f f':ℝ→ℝ}(hb:0 ≤σ)(hu:0 < d)(p:sizeK Q'.L 1 f)(q:sizeK Q'.L 1 f')(ht:∀ᶠ x in atTop,0 ≤ f x ∧0≤ f' x)(hc:0≤ C) :∀ᶠ x in atTop, Tip C d (f x) (f' x) σ n l (radiusB x) (loomP Q' 1) (loomP Q' (3*radiusB x)) x := by
 filter_upwards [take_a (l:=l) (n:=n) Q' σ ((sizeK.tip _ d hu).low (show 1≤2 by omega)|>.scale C), take_a (l:=l) (n:=n) Q' σ p,take_a (l:=l) (n:=n) Q' σ q,ht] with x f g h v using ⟨hb,hc,v.1,v.2,f,g,h⟩ -- tune
variable(C a:ℝ)(F W:ℝ→ℝ)(l n:ℕ)(d:ℝ)
def bill_l(x:ℝ):=let v:=radiusB x; (2:ℝ) * ((barkQ l 3 v:ℝ)* ↑(loomP Q' 1*loomP Q' (3*v)^4) *tapeQ l 3 d*fareI C a (F x) (W x) x n 3)
lemma score_q (hp:0<a)(t:sizeK Q'.L 1 F)(u:sizeK Q'.L 1 W): sizeK Q'.L 3 (bill_l Q' C a F W l n d):=by
 unfold bill_l; dsimp only; push_cast
 have he(G G':ℝ→ℝ)(p:sizeK Q'.L 0 G)(t:sizeK Q'.L 1 G'):sizeK Q'.L 3 (fun x=> Lich.Muster.quota n 3 (G x) (G' x)):=by
    simp_rw [Lich.Muster.quota]; exact ((p.scale _).tint ((t.scale _).square 3)).scale _ -- tune parentheses
 exact (((((boon Q' 3 l).tint (((plo Q').powC 4).scale _)).tint (sizeK.mild _ _)).tint (((he _ _ (sizeK.mild _ _) (((sizeK.tip _ a hp).low (show 1 ≤2 by omega)).scale C)).accrue ((he _ _ (t.low (Nat.zero_le _)) t).scale _)).accrue (he _ _ (u.low (Nat.zero_le _)) u)))).scale 2 -- tune
section
variable {N P B':Side}{S:StepData (Domain N B') (Domain P B')}{G:Ratio (mid N B') (mid P B')}{e:ℝ}{T:Tube SU.group S}{x:ℝ}(A:Muster G S x e T)
variable {C a F W l n Q' d}
variable {W' V' :ℝ}{U: Monk SU.group S}
lemma talent (p:NameX T U x A.trot A.room l n C a (F x) (W x) V')(h:NameX T (kist U) x A.trot A.room l n C a (F x) (W x) V')(g:A.post=l)(ht:S.patch=Q')(hs:ShardIncome n x L K D T U.key U.park U.V U.k) (hG:0<B x)(p₁:Tip C a (F x) (W x) d n l (radiusB x) (loomP Q' 1) (loomP Q' (3*radiusB x)) x)(p₂:Tip (C+1) a (F x+W') (W x+ W') d n l (radiusB x) (loomP Q' 1) (loomP Q' (3*radiusB x)) x)(hW:0<W') :
 let X:= costL A n C a (F x) (W x);
  (∀ i, 0 ≤ X i) ∧ (∀ i, Allows n (fun y=> Lich.Muster.massX A (U.atop y x) i) 0 (X i)) ∧ ∀ i:Site (Domain N B'),(∑ z:Palot.leaf (Site (Domain N B')), tallyL i z d (radiusB x)*X z) ≤ bill_l Q' C a F W l n d x:=by
 intro X; have he(k): loomP Q' k=ratioB S k:=by rw [←ht]; rfl
 simp_rw [he] at p₁ p₂; subst l; refine ⟨roof_n A p₁,fun i=>?_,fun i=>?_ ⟩ -- tune
 · apply birth T n A U p h (lt_add_one C) (lt_add_of_pos_right _ hW) (lt_add_of_pos_right _ hW) (ContinuousAt.sub ((transX hs.kernel).continuousAt) continuousAt_const) p₁.pos_b p₁.pos_c (gproof p₂.rate p₂.act (mul_nonneg p₂.pos_t (Real.exp_pos _).le)) (gproof p₂.rate p₂.mat p₂.pos_b) (gproof p₂.rate p₂.cot p₂.pos_c) -- tune
 unfold bill_l; dsimp only; rw [he,he]; exact roof_l A p₁ hG i
end
end YM.CF.Fief
