import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
variable {P N B: Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B))(p:S.ratio=ratio G)(f:Sweep (mid N B))(X:Stores S)(r k:ℕ)
open Acorn Plume Atala Eire
local notation "H"=> Hos S r
local notation "Ζ"=> laden S f r
local notation "Θ"=> reSweep G f
local notation "Λ"=> luckP G S f r
local notation "L"=> liftK S
variable (Y:Finset (Kite S r))(A:Ids (mid P B))
local notation "W"=> (mid P B)
variable (U V:Pane (mid P B))(Bv:Finset (Hos S r))
lemma lex_h(i: Edge (Site (Domain P B)))(V:Support (Domain N B)): tastes S i V↔∃ x∈ Skye.ends i,S.ratio.parent x∈V:=by simp [Skye.ends,tastes]
include p
lemma shape_s (i: Edge (Site (Domain P B)))(Z:Hos S r): tastes S i ((laden S f r Z).val.dome k) ↔ tastes S (Skye.lane Θ i) (Z.val.dome k):=by
 rw [lex_h,lex_h,laneX]; constructor; rintro ⟨x,u,v⟩; refine ⟨boxA Θ x, mem_map_of_mem _ u,?_⟩; rw [show S.ratio.parent _= _ from (show S.ratio.parent (boxA Θ x)=_ from congrFun (pace_k G S p f) x)]; exact (Locations.dome_map ..).mp v
 rintro ⟨i,v,h⟩; obtain ⟨x,l,rfl⟩:= mem_map.mp v; refine ⟨x,l,(Locations.dome_map ..).mpr ?_⟩; change boxA f (S.ratio.parent x)∈ _; rw [← show _ = _ from (show S.ratio.parent (boxA Θ x)=boxA f (S.ratio.parent x) from congrFun (pace_k G S p f) x)]; exact h
lemma rumor : valve S (flashA Θ U) (flashA Θ V) (Bv.image Ζ) k= flashA Θ (valve S U V Bv k):=by
 funext i; have hx: (∃ j∈Bv.image Ζ,tastes S i (j.val.dome k))↔∃ j∈Bv,tastes S (Skye.lane Θ i) (j.val.dome k):=by simp only [exists_mem_image]; apply exists_congr; intro j; refine and_congr_right fun _=> shape_s _ _ p _ r k i j
 rw [flash Θ (valve S U V Bv k)]; unfold valve; simp_rw [hx]; split_ifs with u t <;> rw [flash] <;> split_ifs with t1 <;> first|rfl| contradiction -- tune
lemma vote_s (F:Kite S r)(b:Bool) : Eire.printG S k (flashA Θ U) (flashA Θ V) (Bv.image Ζ) (Λ F).1 b= flashA Θ (Eire.printG S k U V Bv F.1 b):=by have h:(Λ F).1= Ζ F.1:=rfl; unfold Eire.printG; rw [h]; split; rw [←image_insert]; apply rumor G S p; apply rumor G S p
variable {D:Side}{j k' κ:ℕ}{o:Odd D.val}{P₀:Pricing j D o (Thread j)}{e:ℝ}{P':Grasp P₀ B e}{Q:Aim (mid P B)}{J:Pride (mid P B)}{M:Male}{α τ v a c b m w y:ℝ}
variable (C:∀ Y: Support (Domain P B), Lend P B e Y)(Q':Tints P B e)(B₁:Dyes τ e J k' Q' v m)(B₂:Hive.Vista P' M Q C k' α y w a)
variable (U₀ U₁ V₀ V₁:Pane (mid P B))
abbrev Paths(U V: Pane (mid P B))(T:Finset (Kite S r)):Prop:=∀ i∈T,Agrees (↑(i.2.1∪i.2.2):Set (Site (Domain P B))) U V -- Agrees takes Set
variable (pV: Paths S r U₀ U Y)(tV:Paths S r V₀ V Y)(tU:Paths S r (flashA (reSweep G f) U₀) U₁ (Y.image (luckP G S f r)))(gU: Paths S r (flashA (reSweep G f) V₀) V₁ (Y.image (luckP G S f r)))(h₀:HullK S k Y U V e)(h₁:HullK S k (Y.image (luckP G S f r)) U₁ V₁ e)(hA:Injective (priorP A))
lemma tag_a (F: Finset (Hos S r))(i: Hos S r)(b:Bool)(D:Support (Domain P B))(p:Agrees D U V)(t:Agrees D U₁ V₁): Agrees D (Eire.printG S k U U₁ F i b) (Eire.printG S k V V₁ F i b):=by intro i v h; unfold Eire.printG; split <;> unfold valve <;> split <;> first|apply p i v h|apply t i v h
include pV tV tU gU h₀ h₁ hA B₁ B₂
lemma oars (i: Kite S r)(φ:i∈Y)(h:Bv⊆ liftK S Y) : postM S k C Q' U₁ V₁ (bun Θ A) (Bv.image Ζ) (Λ i)=teen Θ (postM S k C Q' U V A Bv i):=by
 let i':=Λ i; have hp:i.1∈ L Y:=mem_image_of_mem Prod.fst φ; have he:printG S k U V Bv i.1 ∈MonoX P B e (danceL S i.1.val r):= pays_l S k U V Y h₀ Bv h _ hp; have ht:=pays_l S k U₁ V₁ (Y.image Λ) h₁ (Bv.image Ζ) (by rw [rushB]; exact image_subset_image h) i'.1 ((duck_b G S f r Y _).mpr hp)
 unfold postM; rw [dif_pos ht,dif_pos he]; let X:Castle P B e (danceL S i.1.val r):=⟨_,he⟩
 let Z:=danceL S i.1.val r; change _= teen Θ (Scion.stock e Z Q' C X A i.2); rw [← show Scion.stock e (actY Θ Z) Q' C (pullT Θ X) (bun Θ A) i'.2=_ from Scion.axis e Z Q' C X A Θ i.2 B₂ (dance_g ..) hA] -- tune
 let P':=i.2.1 ∪ i.2.2; let T':Support (Domain P B):=i'.2.1 ∪ i'.2.2
 have gX{Ω:Support (Domain P B)}(hp:Ω=danceL S i'.1.val r)(V:Castle P B e Ω)(A_: Castle P B e (danceL S i'.1.val r))(p:∀ b,Agrees (↑T') (A_.val b) (V.val b)):Scion.stock e (danceL S i'.1.val r) Q' C A_ (bun Θ A) i'.2= Scion.stock e Ω Q' C V (bun Θ A) i'.2:=by subst Ω; exact lit_i S C Q' i' B₂ J B₁ _ _ _ _ (fun _ _=>rfl) p
 let X':= pullT Θ X; apply gX (twirl G S p f r i.1).symm
 intro b; change Agrees (↑T') (printG S k U₁ V₁ (Bv.image Ζ) (Λ i).1 b) (flashA Θ (printG S k U V Bv i.1 b))
 have hz': (T':Support _)=actY Θ (i.2.1 ∪ i.2.2):=(map_union ..).symm -- tune
 let hq:(Agrees (↑T') (flashA Θ (printG S k U₀ V₀ Bv i.1 b)) (flashA Θ (printG S k U V Bv i.1 b))):=by
    apply flashD; rw [hz', actY,Finset.map_map,show Finset.map _ (i.2.1 ∪ i.2.2) = i.2.1∪i.2.2 from ?_]; swap; · ext; simp
    exact tag_a G S p r k _ _ _ _ Bv i.1 b _ (pV i φ) (tV i φ)
 have hx:= mem_image_of_mem (luckP G S f r) φ; intro j v w; refine Eq.trans (Eq.symm ?_) (hq j v w)
 rw [← vote_s G S p]; exact tag_a G S p r k _ U₁ _ V₁ _ (Λ i).1 b _ (tU _ hx) (gU _ hx) j v w
end YM.CF.Salt
