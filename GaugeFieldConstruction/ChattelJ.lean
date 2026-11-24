import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.FloorΙJ
import GaugeFieldConstruction.PirangaJ
import GaugeFieldConstruction.PeakJ
import GaugeFieldConstruction.GypA
import GaugeFieldConstruction.StepWorthJ
import GaugeFieldConstruction.OrbisJ
import GaugeFieldConstruction.YieldRampJ
import GaugeFieldConstruction.Budgets
import GaugeFieldConstruction.FairNumJ
import GaugeFieldConstruction.CapriceJ
import GaugeFieldConstruction.NurmaJ
import GaugeFieldConstruction.SamarsJ
import GaugeFieldConstruction.Norwood
import GaugeFieldConstruction.TurnBridgeJ
import GaugeFieldConstruction.FineAlJ
import GaugeFieldConstruction.PaceDoorJ
import GaugeFieldConstruction.EssenceJ
import GaugeFieldConstruction.SambaJ
import GaugeFieldConstruction.Passport
import GaugeFieldConstruction.QuerentJ
import SatinThinCarry
import SatinThinConvoy
import SatinThinGutter
set_option maxHeartbeats 1050000
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
namespace Promena
open Tapestry Advance CoeffArc Frugal Directory Ing
set_option autoImplicit false
set_option maxHeartbeats 200000
variable (i k s f j:ℕ) {m n:ℕ}
open Papal AUbard Directory
local notation "η_"=>Y.uv k
local notation "Pq"=>P.R.L
variable (D C t:ℕ→ℝ) (α c τ u0:ℝ)(Nkey:ℕ) -- price scale functions C unused.
open XGarden XGarden.Ledger XGarden.Echo XGarden.MastTin XGarden.Shield XGarden.MastTin.MintB Ing Ing.Iona Ing.Ivey Ing.Ivey.ShoreQ
open Sour Sour.SliceRoof SeasonH Fock.Wosk TableF TableF.Lenten TableF.Lenten.Layout
open Oath Wray
local notation "µs" s:max=> Papal.gram Y s i k
variable (K :ℕ→ℝ)
local notation "NY_" s:max=> Papal.count Y s i
local notation "Zmat" s:max=> KeyUp ((Papal.gram Y s i k).p)
local notation "Γω" s:max=> (PlaceOf Y i k s).step P.V
local notation "vΓ"=>Y.uv k
local notation "Ζτ"=> Journey.side Y i (Y.uv k)
open Girt
-- inductive price coefficient calculus. assign label q only; area exponential C per *nonunit* ≤ per group. F at f
inductive ChargedJ {T W:Type} [Add T][One T][SMul ℂ T]{X:Type} (x:X)(F:W→X)(c:ℝ)(M:W→T): T→ℝ→Prop
 | one : ChargedJ x F c M 1 1
 | coin (i:W)(p:F i=x): ChargedJ x F c M (M i) c
 | add {P Q:T}{d e:ℝ}: ChargedJ x F c M P d→ChargedJ x F c M Q e→ ChargedJ x F c M (P+Q) (d+e)
 | smul(z:ℂ){P:T}{Q:ℝ}: ChargedJ x F c M P Q→ChargedJ x F c M (z•P) (‖z‖*Q)
 | lift{P:T}{Q L:ℝ} (v:Q ≤ L): ChargedJ x F c M P Q → ChargedJ x F c M P L
namespace ChargedJ
section ban
variable {T W V :Type}[AddCommGroup T][One T][Module ℂ T] {x:V}{F: W→V}{c:ℝ}{M:W→T}
variable {u v:T}{p e:ℝ}
lemma paid(p':ChargedJ x F c M u p)(t:0≤c): 0≤p:=by induction p' with|one=>exact zero_le_one|coin=>exact t|add _ _ a b=>exact add_nonneg a b|smul _ _ p=>exact mul_nonneg (norm_nonneg _) p| lift v _ p=>exact p.trans v
lemma ζzero :ChargedJ x F c M 0 0:= by simpa only [zero_smul,norm_zero,zero_mul] using ((ChargedJ.one (x:=x) (F:=F) (c:=c) (M:=M)).smul 0) -- .smul q notation order
lemma minus (h:ChargedJ x F c M u p)(t:ChargedJ x F c M v e):ChargedJ x F c M (u-v) (p+e):=by simpa [sub_eq_add_neg] using h.add (t.smul (-1))
lemma sums {I:Type} (l:Finset I)(G:I→T)(x':I→ℝ)(p:∀i∈l,ChargedJ x F c M (G i) (x' i)): ChargedJ x F c M (∑ i∈l,G i) (∑ i∈l,x' i):=by
 classical
 induction l using Finset.induction_on with
 | empty=> simpa using (ζzero (x:=x) (F:=F) (c:=c) (M:=M)) -- simp?
 | insert i U h ih=> rw[sum_insert h,sum_insert h]; exact (p i (mem_insert_self _ _)).add (ih (fun i' d=>p _ (mem_insert_of_mem d)))
end ban
variable {W X : Type}{c d:ℝ}{U:W→ Mark (Journey.side Y i (Y.uv k))}{T:W→X}{p:X}
variable {r:Finset (Seat (Journey.side Y i (Y.uv k)))} {F: Mark (Journey.side Y i (Y.uv k))}
lemma lake (h:ChargedJ p T c U F d)(v:∀ i,T i=p →PostSupport false r (U i)):PostSupport false r F:=by
 induction h with
 | one=> exact PostSupport.of (AtSupport.oneM _)
 | coin i h=> exact v i h
 | add _ _ t w=> exact t.addM w
 | smul z _ w=> exact w.smulM z
 | lift _ _ h=> exact h
lemma enviros (h:ChargedJ p T c U F d)(v:∀ i,PostSupport false univ (U i)):Envelope F:=(lake Y i k h (r:=univ) (fun i _=>v i)).env
end ChargedJ
section price
variable (X I:Type)[LinearOrder X](g:X)(T:I→X)(v:I→Mark (Journey.side Y i (Y.uv k)))
variable (H a b:ℝ)(p:0≤b)(q:1≤ H)(Q:0≤a)
abbrev Cap_ZΛ (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i k:ℕ): Mark (Journey.side Y i (Y.uv k))→ ℂ:= Journey.compass Y i k (Y.uv k)
local notation "ΖQ"=> Cap_ZΛ Y i k
variable (Pay:∀ (l:List I),(l.map T).Pairwise (· < ·) → ‖Cap_ZΛ Y i k (l.map v).prod‖≤ H*a^l.length*b^l.length) -- H? area factor per group a=exp 2u0≥1
variable (Xv:∀ i,PostSupport false univ (v i))
-- induction via arbitr.Legs carrying a prefix of bought coin labels. visiting in order.
variable (Hk: (Y.voyage i).kick≤ k)(hp:1≤a)
include p q Pay Xv Hk hp
lemma Sermon (u:X→Mark (Journey.side Y i (Y.uv k)))(w:X→ℝ)(l:List X)(g:∀ i∈ l, ChargedJ i T b v (u i) (w i))(f:List I) (mJ:(f.map T ++ l).Pairwise (·<·)): ‖Cap_ZΛ Y i k ((f.map v).prod * (l.map u).prod)‖≤ (H*a^(f.length+l.length)*b^f.length)*(l.map w).prod:=by
 let R(x:List I)(l:List X):=(x.map v).prod*(l.map u).prod; have qA:=zero_le_one.trans hp
 induction l generalizing f with
 | nil=>simp only[List.map_nil,List.prod_nil,mul_one,List.length_nil,Nat.add_zero]; apply Pay; simpa using mJ
 | cons i' l ih=>
   have gz(i'':X)(p:i''∈l):= g i'' (List.mem_cons_of_mem _ p); have hE:= Xv
   have hb: (f.map T ++ l).Pairwise (·<·):=mJ.sublist ((List.sublist_cons_self _ _).append_left _) -- tune args
   let G:=(l.map u).prod; let F:=(f.map v).prod; let U:=Journey.side Y i k; let C':=H*a^(f.length+(l.length+1))*b^f.length
   have hx:∀ l':List (Mark Ζτ),(∀ m∈l',PostSupport false univ m)→ PostSupport false univ (l'.prod):=by
      intro l'; induction l' with|nil=>exact fun _=>PostSupport.of (AtSupport.oneM _)|cons i l ih=> intro p; exact (p i List.mem_cons_self).mulM (ih (fun j v=>p j (List.mem_cons_of_mem _ v)))
   have hF:= hx _ (show ∀ W∈ f.map v,_ from (by intro W w; obtain ⟨a,b,rfl⟩:=List.mem_map.mp w; exact hE _)); have hG: PostSupport false univ G:=hx _ (by intro W w; obtain ⟨a,t,rfl⟩:= List.mem_map.mp w; exact ChargedJ.lake Y i k (gz a t) (fun i _=>Xv i)); have hg:0≤(l.map w).prod:=List.prod_nonneg (by intro r t; obtain ⟨i',q,rfl⟩:=List.mem_map.mp t; exact (gz i' q).paid p)
   have hc:0≤ C':=by unfold C'; have h:=zero_le_one.trans q; positivity
   suffices h: ∀ (t:Mark Ζτ)(c:ℝ), ChargedJ i' T b v t c→ ‖Cap_ZΛ Y i k (F*(t*G))‖≤ C'*(c*(l.map w).prod) from h _ _ (g i' List.mem_cons_self)
   intro t c h; induction h with
   | one=> rw [one_mul,one_mul]; refine (ih gz f hb).trans ?_; apply mul_le_mul_of_nonneg_right _ hg; unfold C'; gcongr; omega
   | coin j h=> rw [←mul_assoc];
                let l₀:=f ++ [j]; have ht:(l₀.map T ++ l).Pairwise (·<·):=by simpa [l₀,h] using mJ -- tune
                have he:=ih gz l₀ ht; unfold l₀ at he; simp only[List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one,List.length_append,List.length_cons,List.length_nil,Nat.zero_add] at he; unfold C'; apply le_trans he (le_of_eq ?_); rw [pow_succ,show f.length+1+l.length=f.length+(l.length+1) from by omega]; ring -- tune indent
   | add h1 h2 p1 p2=> 
      rw [add_mul,mul_add,Cap_ZΛ,Tapestry.plusReader]; swap; · exact (hF.mulM ((ChargedJ.lake Y i k h1 (r:=univ) (fun i _=>Xv i)).mulM hG)).env
      swap; · exact (hF.mulM ((ChargedJ.lake Y i k h2 (r:=univ) (fun i _=>Xv i)).mulM hG)).env
      swap; · exact ⟨Hk,le_rfl⟩
      exact (norm_add_le ..).trans ((add_le_add p1 p2).trans_eq (by rw[add_mul,mul_add])) -- tune swap
   | smul z _ w=> rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Cap_ZΛ,Tapestry.scaleReader,smul_eq_mul,norm_mul]; refine (mul_le_mul_of_nonneg_left w (norm_nonneg _)).trans (le_of_eq ?_); ring
   | lift v _ w=> exact w.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right v hg) hc)
#print axioms Sermon
end price
end Promena
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
end
