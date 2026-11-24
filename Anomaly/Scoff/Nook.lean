import Anomaly.Scoff.Penny
/-! Applies boost to actual occupancy. All tips preserved on old port complements. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.QuadClock
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
variable {N n B:Side}
set_option autoImplicit false
open Mew Waxy

variable {P:Side}{l:Patch}{K:Teller SU.group}{L:ChartRatio SU.group}
  (V:Grace K l L) {e:ℝ}(P_:Grasp V.U B e)
  (G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(G₀:Scree.Loom (mid N B))(G₁:Scree.Loom (mid P B))(X:GramM (mid N B))(Y:GramM (mid P B))(Xp:Op SU.Slot)(q:Chi)(d h Vp Vf T W C BQ Rt Zt b g κp:ℝ) -- b,g∶ b call budgets all same, g Sized
variable {J: Type}[LinearOrder J][Fintype J]
open Oise Rive
open Ione.Clock
variable {I:Type}[Fintype I][LinearOrder I]
local notation "Tc"=> mid N B
local notation "Tf"=> mid P B
local notation "Wν" => (duty_Q X.p.order X.p.power*W)
-- CP protocol reports.
variable {j k mc:ℕ}
variable {r:I→Site (mid N B)}{A:I→ArcΦ}{a:I→ℝ}{X₁:Key I→RegBudget (mid P B)}{X₂:Key I→ForceBudget (mid P B)}
open Vow.TreasuryFog Roots Sour
variable {Ω':Occlus X.p}{O:Finset I}{J₀:I→ Bag (mid N B)} {A₀:I→ Swell.phy (mid N B)} {Y₀:I→RegBudget (mid N B)}{F₁:I→Cusp (mid N B)} {E:Key I→RegBudget (mid N B)}{F':Key I→ForceBudget (mid N B)}{D:Key I→RegBudget (mid N B)}{K':Key I→ForceBudget (mid N B)}{x t':I→ℂ}{f c y:ℝ}
variable {k':ℕ}{nM:ℕ}
-- Crest. note shadow V in structure not captured? likely passed first V Grasp.Hi.P
variable (Tκ: BornEconomy V P_ G₀ X h Ω' O k r E F' x J₀ A₀ Y₀ F₁ t' D K' k' f c y)
variable (hv:Furnace X O k' r E F' (α_ξ x) h T b g) (hz:CrestPay X.p (Cube.node ∘r) E (X.p.supportExponent+1) h T) (u:8≤ X.p.B)(pδ:Ω'.η=(X.p.B:ℝ)⁻¹)(hp:1≤h)
local notation "Zσ"=> Cube.node ∘ r
local notation "EΦ"=> clearRoot r (E+D)
local notation "KΦ"=> bustle (Cube.node ∘r) (F'+ K')
variable (M:I→I→ℂ)
local notation "Λ"=> toV_C (Cube.node ∘r) M
local notation "Υx"=> EΦ ∘ Λ
local notation "ΥF"=> KΦ ∘ Λ
local notation "τ"=> (x+t')
local notation "Bol" F:max G:max T:max z:max=> color_b X X.beta (X.F+F z) X.slip (X.K+G z) (X.v+α_ξ T z)
include Tκ hv hz u pδ hp
variable (P₁:Finset I)(t:I→ℂ)
abbrev nTempo {I:Type}[Fintype I][LinearOrder I] (O:Finset I)(t:I→ℂ)(A:I→Swell.phy Tc):I→Swell.phy Tc:=fun i=> if i ∈ O then fun _=> t i • 1 else A i
omit Tκ hv hz u pδ hp
lemma unit_roll {A:I→Swell.phy Tc} (v:P₁ ⊆ O)(l:List I)(i:Orbit Tc) : (((Leit P₁ l).map t).prod) • ((Leit O (Leit (Finset.univ\ P₁) l)).map (fun j=>A j i)).prod = ((Leit O l).map fun j=> nTempo P₁ t A j i).prod:=by
 induction l with
 | nil=> rw [show Leit P₁ []=[] from rfl, List.map_nil,List.prod_nil,one_smul]; rfl
 | cons j l ih=>
    by_cases h:j∈P₁
    · have hz:=v h; simp only [Leit,List.filter_cons,Finset.mem_sdiff,Finset.mem_univ,true_and,h,hz,not_true_eq_false,decide_false,↓reduceIte,decide_true,Bool.false_eq_true,List.map_cons,List.prod_cons] at ih ⊢; rw [nTempo,if_pos h, mul_smul, ih,Algebra.smul_mul_assoc,one_mul]
    by_cases p:j∈O; swap
    · simpa [Leit,h,p] using ih
    simp only [Leit,List.filter_cons,Finset.mem_sdiff,Finset.mem_univ,true_and,h,p,not_false_eq_true,decide_false,↓reduceIte,decide_true,Bool.false_eq_true,List.map_cons,List.prod_cons] at ih ⊢; rw [nTempo,if_neg h,←Algebra.mul_smul_comm, ih] -- smul assoc maybe orientation
lemma fern_Q (E:Key I→RegBudget Tc)(F:Key I→ForceBudget Tc)(r:I→Site (mid N B))(t:I→ℂ)(u:Notice r E F)(i:Orbit Tc): River (fun z:Key I=>denZ (Bol E F t z) P_ G₀ i):=by
 let p:=Cube.node∘r; have he {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]{g:Key I→E}(q:River g): Law_C p 0 [] g g:=⟨q,q,fun i u=>by rw [List.sublist_nil.mp u]; rfl⟩
 exact (pulse_H (U:=P_) V p 0 [] (by simp [ψS]) X G₀ (fun z=>X.F+E z) _ (fun _=>X.slip) _ (fun z=>X.K+F z) _ (fun z=>X.v+α_ξ t z) _ i (fun x y=>he (dub_V (zeroR _) (river_all _ (u.varE x y)))) (fun i x=>he (zeroR _)) (fun i x=> he (dub_V (zeroR _) (river_all _ (u.varF i x)))) (he (dub_V (zeroR _) (rer_C t)))).1
include Tκ hv hz u pδ hp
lemma ravine (sP:P₁⊆O)(uP:∀ i∉P₁,t i=0)(L':List I)(vS:L'.length ≤ k)(q:ψS (Cube.node∘r) L') (i:Orbit (mid N B))(tΩ:IsStarProjection (Dial.spar K.j X.J.M (G₀ i))) (p:Injective (priorP i.2))(xH:FleetS X.p.threshold i.1)(fP:∀ j∈P₁,A₀ j i=0) (z:∀ l:List I,l.map (Cube.node∘r)=L'.map (Cube.node∘r)→(Leit O l).Pairwise fun x y=> Commute (A₀ x i) (A₀ y i)) : tipI (fun j:Key I=> denZ (Bol (Υx) (ΥF) (markerCore (Zσ) M (τ+t)) j) P_ G₀ i) L' = snow (Zσ) M (fun j=> acts (((Leit O j).map fun z=> nTempo P₁ t A₀ z i).prod) (tipI (fun z:Key I=> denZ (color_b X X.beta (X.F+E z) X.slip (F' z) (X.v+ α_ξ x z)) P_ G₀ i) (Leit (Finset.univ\ O) j))) L':=by
 obtain ⟨f,v,w,H⟩:=Tκ.grant; let A':=lease_ticket P_ G₀ w H hv hz u pδ hp
 have h:=sworn_den (C:=G₀) (U':=P_) r (E+D) (F'+K') M V X (τ+t) L' q i
 refine h.trans (rer _ _ _ fun l eL=>?_); have hz:l.length=L'.length:= by simpa using congrArg List.length eL
 have he: ψS (Cube.node∘ r) l := (show (l.map (Cube.node∘r)).Nodup from eL.symm ▸ q)
 let e(j:Key I):= denZ (Bol EΦ KΦ τ j) P_ G₀ i; let f'(z:Key I):= denZ (color_b X X.beta (X.F+E z) X.slip (F' z) (X.v+ α_ξ x z)) P_ G₀ i
 have hg (l':List I)(p':l'.Sublist l): tipI e l'= acts (((Leit O l').map fun j=> A₀ j i).prod) (tipI f' (Leit (Finset.univ \ O) l')):=by
    unfold e; rw [sum_ring]; exact A'.2.2 l' (p'.length_le.trans (hz.symm ▸ vS)) ((List.Sublist.map _ p').nodup he) i tΩ p xH ((z l eL).sublist (p'.filter _))
 let d:=Leit (Finset.univ \ P₁) l; let c':=(Leit P₁ l).map t
 have ht:tipI (fun z:Key I=> Complex.exp (α_ξ t z) • e z) l= (c').prod • tipI e d:=by
    refine boost_Q _ t uP (fern_Q V P_ G₀ X EΦ KΦ _ τ A'.1 _) (uS_b _ he) (fun l' q j x y=>?_)
    have hv:0∈((Leit O l').map fun j=> A₀ j i):= List.mem_map.mpr ⟨j,(by simp [Leit,y,sP x]),fP j x⟩
    rw [hg l' q,List.prod_eq_zero hv,act_zero]
 change tipI (fun j:Key I=> denZ (Bol EΦ KΦ (τ+t) j) P_ G₀ i) l=_
 have he(j:Key I):denZ (Bol EΦ KΦ (τ+t) j) P_ G₀ i = Complex.exp (α_ξ t j) • e j:=by
    rw [sum_ring]; change denZ (color_b X X.beta (X.F+EΦ j) X.slip (X.K+KΦ j) (X.v+(α_ξ τ j+ α_ξ t j))) P_ G₀ i =_; rw [←add_assoc]; exact vig_v V i ..
 rw [funext he]
 refine ht.trans ?_; have hf:Leit (Finset.univ \ O) d=Leit (Finset.univ \ O) l:=by
    clear ht; unfold Leit d Leit -- expansion filter_filter. Can ext
    rw [List.filter_filter]
    congr 1; funext i; by_cases h:i ∈ O; simp [h]; simp [h,show i∉P₁ from fun p=>h (sP p)]
 rw [hg d List.filter_sublist,hf,←act_smul,show c'.prod • _ =_ from unit_roll _ t sP l i (A:=A₀)]
end YM.CF.QuadClock
