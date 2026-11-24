import ForceSatin.Hollow
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

-- LP.17 variant, all configurations in comparison measure, any disjoint supports of satellite boxes (need not be `small' or thin only). Mark-cost Sigma for Lambda.
variable (t fee b:ℝ) (H:ℝ→ℝ) (ht:0<t)(p:t≤1)(hPL:PL H)
universe u
variable {J:Type u}[DecidableEq J]{N:Side}
lemma chilly_card (t:ℝ)(X:Pane N)(σ:Signed) (b:Seat N) : (weak (G:=G5) t (pull σ b X)).card=(weak (G:=G5) t X).card:=by
 let i:Equiv.Perm (Cell (More N)):= Equiv.ofBijective (Face.send σ b) ⟨Face.injective_send σ b,Finite.injective_iff_surjective.mp (Face.injective_send σ b)⟩
 have h(z:Cell (More N)): z∈weak (G:=G5) t (pull σ b X) ↔ i z∈weak (G:=G5) t X:=by rw [weak_mem,weak_mem,Face.send_price X z σ b (SU.group.chord) SU.group.chord_inv (fun l t=> SU.group.chord_conj t l)]; rfl
 apply Finset.card_equiv i h
noncomputable abbrev whiteToll {N:Side}(t z:ℝ)(U:Pane N):ℝ:= z*(weak (G:=G5) t U).card
lemma white_env {N:Side}(z:ℝ)(p:BudgetPoint):Envelope (whiteToll (N:=N) (t*p.threshold) z):=by unfold whiteToll; simp_rw [←counts_weak]; apply Envelope.sum _ (fun i x=> if i∈weak (G:=G5) (t*p.threshold) x then z else 0); exact fun i=> Envelope.piece (p:=fun U=> i∈weak (G:=G5) (t*p.threshold) U) (poll ..) (Envelope.const _) (Envelope.const _)
lemma lenient {s i k:ℕ} (d:ℝ) {c:Side}{r:Lattice.Ratio c (More (nₛ s i))}(A:Tiling c (count Y s i) r): Milage Y s i k t d 0 A (whiteToll (t*(Uₛ s i k).p.threshold) d):=by
 let V:= Uₛ s i k; let l:=t*V.p.threshold; let X:=ℶ s; let N:= count Y s i
 have he(k:Seat N→SU.group.El)(v:Pane N): weak (G:=G5) l (gauge k v)=weak (G:=G5) l v:=by ext i; rw [weak_mem,weak_mem,face_gauge, SU.group.chord_conj]
 refine ⟨white_env t _ _,fun i _ t=> congrArg (fun X:Finset _=> d*X.card) (he _ _),?_⟩
 refine ⟨0,0,0,0,by ring_nf; rfl,(fun _ _ _=>0),fun _ _=>contDiff_const,fun _ _ _=>by simp,fun _ _ _=> by simp,?_,fun _ _=>by simp [plumeCost]⟩
 intro a b S U x y h' v _ _; rw [v]; change whiteToll l d U ≤0+(0+snags _ _ _ _+whiteToll l d U); have ht:0≤ snags r (radiusB X) a (weak (G:=G5) l U):=by unfold snags; positivity; -- statements scope
 change _ ≤ 0+(0+snags r (radiusB X) a (weak (G:=G5) l U)+_); linarith only [ht]
include ht p hPL
lemma at_white : ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤ Y.uv k →
 (∫ U:Pane (count Y s i), mountain Y fee s i k U * Real.exp (whiteToll (t*(Uₛ s i k).p.threshold) (H (ℶ s)) U) ∂prior SU.group (More (count Y s i))) ≤ Real.exp (grassClear Y s i k):=by
 filter_upwards [lake_credit Y t fee H ht p hPL,block_widths P] with s l q i k u
 let N:= count Y s i; obtain ⟨W,j,h0,h1,c,r,e,w⟩:= q (Y.ir i); let d:= H (ℶ s); let t':= (Uₛ s i k).p; let Y':=whiteToll (N:=N) (t*t'.threshold) d; have hj:Odd r.count.val:=w.symm ▸ j; obtain ⟨T⟩:=Tree.select r hj; let A:= Tiling.mk (n:=N) (r:=r) hj e T; let f(X:Pane N):=mountain Y fee s i k X * Real.exp (Y' X); let μ:= city N
 have E:Envelope f:= (mountainLease Y fee u).mul (white_env (N:=N) t d t').exp; 
 have he:=l i k u c r (by rw [coveredWidth,w]; exact ⟨h0,h1⟩) A 0 (fun _=>Y') (fun _=>lenient Y t d A) (fun u=> f u.1) 0 (E.meas.comp measurable_fst|>.aestronglyMeasurable)
 change (∫ x,f x∂prior SU.group (More N))≤ _; rw [← usesPrior _ (E.integrable _)]; apply le_trans (_ : _ ≤ Real.exp (grassClear Y s i k+0+0)) (by simp); apply (he _).2
 filter_upwards with x; exact ⟨mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le, fun σ=> Eq.le (by unfold f Y' whiteToll silhouette; rw [chilly_card,zero_add])⟩
#print axioms at_white
-- LP.
omit hPL ht p
noncomputable def failedCut (u:ℝ)(S:J→Support (More N))(L:Finset J)(X:Pane N):= L.filter (fun i=>∃ F∈weak (G:=G5) u X, F.1∈ S i)
theorem failed_bound (u:ℝ)(S:J→Support (More N))(L:Finset J)(p:Set.PairwiseDisjoint (L:Set J) S)(X:Pane N): (failedCut u S L X).card ≤ (weak (G:=G5) u X).card:=by
 let F:= failedCut u S L X; let V:=weak (G:=G5) u X
 choose a h w using (fun i:F=> (mem_filter.mp (show i.val ∈ F from i.property)).2); let f(i:F):V:=⟨a i,h i⟩
 rw [← Fintype.card_coe (failedCut ..), ←Fintype.card_coe _]; refine Fintype.card_le_of_injective f (fun i j e=>?_)
 apply Subtype.ext; by_contra v; let g:= p (mem_filter.mp i.property).1 (mem_filter.mp j.property).1 v
 exact disjoint_left.mp g (w i) (show (a i).1 ∈ S j.val from ((congrArg (fun y:V=> y.val.1) e).symm ▸ w j))
lemma failed_env {N:Side}(u:ℝ)(S:J→Support (More N))(L:Finset J)(w:ℝ): Envelope (fun x:Pane N=> w*(failedCut u S L x).card):=by
 let Y(i:J)(x:Pane N):= if ∃ F∈weak (G:=G5) u x, F.1 ∈ S i then w else 0
 have hh(i:J): Envelope (Y i):= Envelope.piece (p:=fun x=> ∃ F∈weak (G:=G5) u (x:Pane N), F.1 ∈ S i) (by simp only [Set.setOf_exists]; apply MeasurableSet.iUnion; intro i'; by_cases h:i'.1 ∈ S i; simp only [h,and_true]; exact poll ..; simp [h]
                                                                                                       ) (Envelope.const _) (Envelope.const _)
 have e(x:Pane N): w*(failedCut u S L x).card=∑ i∈L,Y i x:=by unfold Y failedCut; rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
 simp_rw [e]; exact Envelope.sum L Y hh

include ht p -- hPL free P_*
theorem lp_nearcut (Ptax:ℝ)(pT:0≤Ptax): ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s≤ Y.uv k → ∀ S:J→Support (More (count Y s i)),∀ L:Finset J,Set.PairwiseDisjoint (L:Set J) S →
 (∫ U:Pane (count Y s i), mountain Y fee s i k U * ((ℶ s)^(Ptax*(failedCut (t*(Uₛ s i k).p.threshold) S L U).card):ℝ) ∂prior SU.group (More (count Y s i))) ≤ Real.exp (grassClear Y s i k):=by
 let W:ℝ→ℝ:=fun i=> Real.log i*Ptax
 filter_upwards [at_white Y t fee W ht p (BProof.PL.log_y.mul (BProof.PL.const Ptax)),(turnover P).eventually_ge_atTop 1] with s h p i k u S L q
 let N:= count Y s i; let H:= mountain Y fee s i k; let v:=t*(Uₛ s i k).p.threshold; let d:=ℶ s; let w:=W d; let A:=whiteToll (N:=N) v w; let f(x:Pane N):=w*(failedCut v S L x).card
 simp_rw [Real.rpow_def_of_pos (zero_lt_one.trans_le p) (Ptax * _),←mul_assoc]
 change (∫ x:Pane N,H x*Real.exp (f x) ∂prior G5 (More N))≤_
 have hH:= mountainLease Y (i:=i) fee u
 exact (integral_mono ((hH.mul (failed_env v S L w).exp).integrable _) ((hH.mul (white_env t w _).exp).integrable _) (fun i=> mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (failed_bound v S L q i)) (mul_nonneg (Real.log_nonneg p) pT))) (Real.exp_pos _).le)).trans (h i k u)
#print axioms lp_nearcut
end Papal
end LocalLimit
end Rate
end YM.CF.Py
