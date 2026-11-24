import YM.SU5.Diva.Updraft
import Velour.Board.Birth
import Velour.Board.Relate
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8000
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

open YM.CF.Lamour.Bridge.Celeste Sonnet
open YM.CF.Lamour.Bridge
open Tower.SlabMark VelourBoard Tapestry
variable {r d p w:ℕ}{σ θ C ε ξ:ℝ}
variable (o:VelourBoard.Cell)
local notation "K"=> tent Y H
/--
With one Meringue and a tile fee, all sharp Decks for
any fresh housed Sonnet pay product charge. We work with kick &
resolution (in Ferry), and the **actual** normalization (broken_ratio).
-/
theorem feast
 (g:Meringue.{0} Y p r (180*d) ε ξ C σ θ) 
 (u:0<σ)(c:0≤θ)(z:θ*((↑(2*pitch (K) w:ℕ):ℝ)^4) ≤1):
 ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop, 
 HaloTw P.K.j (count Y s i) ∧ ∀ k:ℕ,
  Ferry Y s i k → ∀ (F:Buffered.Family (tent Y H))
  (A:Sonnet (count Y s i)), exhibit Y H s i F = A.x →
   Sonnet.Cost P.K.j r d (gram Y s i k).J.M ε ξ C σ A → 
   (∀ y∈A.S, Shield (K) w o (p+1) 0 y) → 
   ∀ (l':List (VelourBoard.Tile (tent Y H))) (L U : VelourBoard.Cell),

      Deck (momentm Y i s) w o F l' L U →
 ‖Journey.sharp Y H s i k (VelourBoard.Representation l')‖ ≤ (Real.exp 1 * σ)^l'.length:=by
 filter_upwards [g] with s h
 filter_upwards [h,(count_la Y s).eventually (ownsHalo (j:=P.K.j)
      (P.kJ.symm ▸ (by decide : 1 ≤ (4:ℕ))))] with i h H'
 let N:= count Y s i
 have V: HaloTw P.K.j N:= H' (Vale.val_e ..)
 refine ⟨V,?_⟩
 intro k X F A e q t l' L U R
 let a := Sonnet.Cost (N:=N) P.K.j r d (gram Y s i k).J.M ε ξ C σ
 let G:=fun (b:VelourBoard.Cell) (A:Sonnet N)=> 
     a A ∧ ∀y∈A.S, Shield (K) w o (p+1) b y
 have xb:(K).c (momentm Y i s) = N := terrain Y H (Y.ir i) s
 have Fit:FitsSide (K) w N L U:=by rw [←xb]; exact R.fits
 let f:=R.fill
 let sep:=fun (A B:Sonnet N)=>Distant (p+1) A.S B.S
 have hs:∀ b b',RangeAt L U b→RangeAt L U b'→ b≠b' → ∀A B,G b A→G b' B→ sep A B:=by
   intro b b' h r k A B v v' x e y z₁
   exact le_trans (by omega:p+1≤ 2*(p+1)) (separates Fit h r k (v.2 x e) (v'.2 y z₁))

 obtain ⟨ys,m,n,J₀,J₁⟩:=inscribe Y H s i G Sonnet.x ⟨A,⟨q,t⟩,e⟩ 
   (by intro b A v j D
       refine ⟨_,⟨v.1.reflect V j (PaneCut (K) w o j D),?_⟩,rfl⟩
       intro y hy; obtain ⟨x,hx,rfl⟩:=mem_image.mp hy
       exact turned j D x (v.2 _ hx))
   R.paved a (fun _ _ p=>p.1) sep hs

 have s0: sites N ≤ (ys.length:ℝ)*↑((2*pitch (K) w)^4:ℕ):=by
   rw [m]; let v:=f.1
   unfold sites
   have r': (More N).val^4 ≤ l'.length*((2*pitch (K) w)^4:ℕ):=by
     change (N.val*2)^4 ≤ _
     change ((K).c (momentm Y i s)).val ^ 4 ≤ _ at v
     rw [xb] at v
     linarith only [Nat.mul_le_mul_left 16 v]
   exact_mod_cast r'
 have ht':θ*sites N ≤ ys.length:=by
   rw [Nat.cast_pow] at s0
   linarith only [mul_le_mul_of_nonneg_left s0 c, 
     mul_le_mul_of_nonneg_left z (Nat.cast_nonneg (α:=ℝ) ys.length)]
 rw [actualRead,n,←m]
 refine (broken_ratio Y i s k _).trans ?_; 
 change BrokenMark Y s i k (buffet ys) ≤ _
 rw [striking ys]; apply le_trans (h k X.depth X.enters (Fin ys.length) _ _ (Sonnet.S∘ ys.get) (Sonnet.o ∘ ys.get) ?_ ?_)
 · rw [mul_pow,←Real.exp_nat_mul,show σ^ys.length=Real.exp ((ys.length:ℝ)*Real.log σ) from (by rw [Real.exp_nat_mul,Real.exp_log u]), ←Real.exp_add]
   rw [mul_one,Finset.card_univ,Fintype.card_fin]; exact Real.exp_le_exp_of_le (add_le_add ht' (le_refl _))
 · intro i x; exact Sonnet.Cost.issued (J₀ _ (List.get_mem ys i)) V.1
 · intro i _ j _ u
   rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne u) with t|t
   · exact J₁.rel_get_of_lt (show i < j from t)
   exact Distant.symm (J₁.rel_get_of_lt (show j < i from t))

end Papal
end LocalLimit
end Rate
end YM.CF.Py

