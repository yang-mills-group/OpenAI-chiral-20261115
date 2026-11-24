import YM.SU5.Selected.Sponsor
import YM.SU5.Selected.ReynoldsCont
/-! # Fund the reflected-square bill of a coherent mixed tile at our elected E.

Tile from Papal, chosen with extra pose & financing. Also keep ungauged
mixed inputs (as `g`), certify exactly that they have the same compressed
operators as gauged `f`. Cost used for operator on seat0 (mean-square),
not an unproved separated factorization assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
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
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
open Satin Tapestry
open Lifted (nodeC node_of)
local notation "K" => tent Y H
local notation "o₀" => scheduled (payout d q w) (addgap K)
local notation "F₀" => Sen o₀ (payout d q w)
local notation "LA"=>Buffered.Family K

structure Squared (v:ℕ→Buffered.Family (tent Y H)→ℂ) (z:SU.Slot) (a:Axis) (q d w:ℕ) (s:ℕ) (f g:Buffered.Family (tent Y H)) : Prop where
  first : f∈ Filigree K (Window.family z) (booty (scheduled (payout d q w) (addgap K)) d q) (Sen (scheduled (payout d q w) (addgap K)) (payout d q w))
  scalarTest : g∈ Filigree K (Window.family z) (booty (scheduled (payout d q w) (addgap K)) d q) (Sen (scheduled (payout d q w) (addgap K)) (payout d q w))
  neutralF : Neutral K f
  same : let S:=Sen (scheduled (payout d q w) (addgap K)) (payout d q w); ∃ m, Hosp S ((K).c m) ∧ f m=molasses (g m) ∧ Continuous (g m)
  roof : ‖v s (Tower.mirror K a 0 (1+g) * (1+g))‖≤1/1000

private lemma perspective (S:Finset Cover)(J:Calibration)(W:Window.Family) (m n:Side)(e:J.c m=n)
    (F:Mark n) {k:ℕ} (r:Fin k→ Cover) (he:Roomy S n)
    (t:AtSupport false (Satin.region S n) F)(g:Continuous F)(p:∀ x y:Fields n,x.1=y.1→F x=F y)
    (u:∀ i,nodeC (r i)∈S)(w:∀ x,F x∈ Hap W ((wrap n)∘r) (Satin.region S n))
    (v:VolumeX ((wrap n) ∘ r) ⊆ Satin.region S n) :
    ∃ (f h:Buffered.Family J), f∈ Filigree J W r S ∧ h∈ Filigree J W r S ∧ Neutral J f ∧ arrange _ _ e (h m)=F ∧ f m=molasses (h m) ∧ Continuous (h m):=by
  subst n
  obtain ⟨h,h₀,H₀⟩:= Filigree.shaft he _ t g p u w
  obtain ⟨f,f₀,B₀⟩:= Filigree.shaft he _ (CF.Pannier.Chancel.refines g w t v) (sweet g) (first_cook p) u (Hapsen g w)
  refine ⟨f,h,f₀,h₀,onceNeutral (FilTest f₀).widen (m:=m) (Roomy.seats he) (B₀.symm ▸ (preserves_s g)),H₀,?_,H₀.symm ▸ g⟩
  rw [H₀,B₀]

open Tower
variable (j:Axis)(z:SU.Slot)
lemma squareTile (s i k:ℕ)
    (t:CoupleCost Y H γ R j d q w s i k z)(p:Roomy (F₀) (Papal.count Y s i))
    (g:∀ b S, Sparse d S→ HearthB R (sp b P.K.j (gram Y s i k).J.M (1:Pane (Papal.count Y s i))) S):
    ∃ f h:LA, f∈ Filigree K (Window.family z) (booty (o₀) d q) (F₀) ∧ h∈ Filigree K (Window.family z) (booty (o₀) d q) (F₀) ∧ Neutral K f ∧
      let m:=momentm Y i s
      let V:= taggin Y s i k q d w (o₀) z
      let B:= payout d q w
      exhibit Y H s i (1+h)=V.frame ∧ f m=molasses (h m) ∧ Continuous (h m) ∧
        ‖Journey.sharp Y H s i k (Tower.mirror K j 0 (1+h) * (1+h))‖≤1/2000 ∧ (∀ i, ‖h m i‖≤(1+R)^(q^4)+1) ∧ (∀ i, ‖f m i‖≤(1+R)^(q^4)+1) := by
  let B:=payout d q w; let o:=scheduled B (addgap K)
  let W:=Window.family z; let O:=Papal.count Y s i
  let m:=momentm Y i s; let F:=taggin Y s i k q d w o z
  obtain ⟨sP,F',p'⟩:=t.price
  let fM:=F.frame-1; have hf : F.broad=Satin.region (F₀) O:=sen_islet ..
  let z_:= booty o d q; let Z:=wrap O ∘ z_; let S':=Sen o B; let ν:=Satin.region S' O
  change F.broad=ν at hf
  have hv:VolumeX Z⊆ ν:=hf ▸ (show VolumeX Z ⊆ F.broad from sP.enter)
  have hu :∀ i, fM i∈ Hap W Z ν := fun i'=>hf ▸ (show fM i' ∈ Hap W Z F.broad from blossomHap (P.kJ ▸ (by decide)) sP.enter (g false _ sP.far).1 i') -- argument order
  let L:=terrain Y H (Y.ir i) s; have he :AtSupport false ν fM:= by
    unfold fM; rw [sub_eq_add_neg, ← neg_one_smul ℂ (1:Buffered.Mark O)]; exact (hf ▸ (show AtSupport false F.broad F.frame from sP.atCost)).addM ((AtSupport.oneM ν).smulM _)
  have hy(x y:Fields O)(e:x.1=y.1): fM x=fM y:=by exact congrArg (·-(1:FC (Single O))) (repast_one _ _ x y e) -- implicit args of repast
  obtain ⟨f,h,z',hZ,hn,L₀,C,h'⟩:= perspective S' K W m O L fM z_ p he ((feastReady ..).sub continuous_const) hy (stake_centers Y H _ _ _ _) hu hv
  have h₀: exhibit Y H s i (1+h)=F.frame:=by rw [actual_add,actual_one,show exhibit Y H s i h=fM from L₀]; unfold fM; abel
  have hδ:∀ x, ‖h m x‖≤(1+R)^(q^4)+1 := by
    refine (displayPositive L _ _).2 fun i=>?_ ; rw [L₀]; apply (norm_sub_le (F.frame i) 1).trans (add_le_add (F' i) (by simp))
  refine ⟨f,h,z',hZ,hn,h₀,C,h',?_,hδ,fun x=>?_⟩
  · rw [Tapestry.actualRead, actual_product,show exhibit Y H s i (Tower.mirror K j 0 (1+h))= Buffered.reflMark j 0 (exhibit Y H s i (1+h)) from displayRef ..,h₀]; exact p'
  change ‖f m x‖≤_; rw [C]; exact sweet_budget hδ x

variable {i k:ℕ→ℕ} {E:ℕ→ Buffered.Family (tent Y H)→ℂ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}
local notation "Θ"=>Tower.mirror K j 0
lemma squarePaid (u : Universal Y H i k I E) (p:Policy Y H q d w A R γ) :
    ∀ᶠ s in atTop, ∃ (f g:Buffered.Family (tent Y H)), Squared Y H E z j q d w s f g := by
  filter_upwards [p.focus j] with s Pp
  let B:= (1+R)^(q^4)+2; let D:= B*B; have hD:0<D:=by have h:0<R:=p.positive.1;
                                                         unfold D B; positivity
  let S':= Sen (scheduled (payout d q w) (addgap K)) (payout d q w)
  let W':=reflectedBox j 0 S' ∪ S'
  let v:=(1/4000)/D; have h':0<v:= by unfold v; positivity
  obtain ⟨d',v'⟩:= Satin.boutique Y H u W' s
  let H':= u.pick.grow_i.tendsto_atTop; let ht:= H'.eventually ((d'.and Pp).and ((roomyTail Y H s S').and (roomyTail Y H s W')))
  obtain ⟨t,⟨⟨d₀,P₀⟩,v₀,v₁⟩,a⟩:= (ht.and (v' v h')).exists
  obtain ⟨T,⟨_,_,H₁,c⟩,hX⟩:= ((u.pick.grow_k.tendsto_atTop.eventually P₀).and (d₀ v h')).exists
  obtain ⟨f,g,h,G,w,H',u',t',g',c',c₀⟩:= squareTile Y H j z s (i t) (k T) (c z) v₀ H₁
  let m:=momentm Y (i t) s; let L:=terrain Y H (Y.ir (i t)) s
  refine ⟨f,g,h,G,w,⟨m,L.symm ▸ Roomy.seats v₀,u',t'⟩, ?_⟩
  let y:= 1+g; let x:LA:=Θ y*y
  have hy: InTest K true S' false y:= InTest.add InTest.one (FilTest G).widen
  have hx:InTest K true W' false x:= InTest.mul ((axial K j 0 hy).mono Finset.subset_union_left) (hy.mono Finset.subset_union_right)
  have hb : ∀ x,‖y m x‖≤ B:=fun x'=> (norm_add_le (1:FC (Single ((K).c m))) (g m x')).trans (by rw [norm_one]; dsimp [B]; linarith only [show ‖g m x'‖≤ _ from c' x'])
  have hp(x':Fields ((K).c m)):‖x m x'‖≤D:=by
    change ‖Θ y m x' * y m x'‖≤D; have hv: ‖Θ y m x'‖ ≤ B:= bladeBudget hb x' -- tune
    exact (norm_mul_le ..).trans (mul_le_mul hv (hb x') (norm_nonneg _) ((norm_nonneg _).trans (hb x')))
  have he: Hosp W' ((K).c m):= L.symm ▸ Roomy.seats v₁
  let ξ:=Journey.sharp Y H s (i t) (k T); have hx0: ‖ξ x-I s x (i t)‖≤ v*D:=hX x hx m he _ hp; have hi:‖I s x (i t)-E s x‖≤v*D:=(a x hx m he _ hp).1
  rw [show v*D=1/4000 from div_mul_cancel₀ _ hD.ne'] at hx0 hi; change ‖ξ x‖≤1/2000 at g'; change ‖E s x‖≤1/1000
  linarith only [hx0,hi,norm_sub_norm_le (E s x) (ξ x),g', norm_sub_le_norm_sub_add_norm_sub (ξ x) (I s x (i t)) (E s x), norm_sub_rev (E s x) (ξ x)] -- shadow u etc
where
 bladeBudget {x:Buffered.Family (tent Y H)} {C:ℝ}{n:Side} (p:∀ y,‖x n y‖ ≤ C) (i:Fields ((tent Y H).c n)): ‖Tower.mirror (tent Y H) j 0 x n i‖ ≤ C:=by change ‖Fock.theta _ _‖≤ C; rw [theta_fee]; exact p _
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.squarePaid
