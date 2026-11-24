import YM.CF.Salt.Flax
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
variable {D:Side}{j k' κ:ℕ}{o:Odd D.val}{P₀:Pricing j D o (Thread j)}{e:ℝ}{P':Grasp P₀ B e}{Q:Aim (mid P B)}{J:Pride (mid P B)}{M:Male}{α τ v a c b m w y:ℝ}
variable (C:∀ Y: Support (Domain P B), Lend P B e Y)(Q':Tints P B e)(B₁:Dyes τ e J k' Q' v m)(B₂:Hive.Vista P' M Q C k' α y w a)
variable (U₀ U₁ V₀ V₁:Pane (mid P B))
variable (pV: Paths S r U₀ U Y)(tV:Paths S r V₀ V Y)(tU:Paths S r (flashA (reSweep G f) U₀) U₁ (Y.image (luckP G S f r)))(gU: Paths S r (flashA (reSweep G f) V₀) V₁ (Y.image (luckP G S f r)))(h₀:HullK S k Y U V e)(h₁:HullK S k (Y.image (luckP G S f r)) U₁ V₁ e)(hA:Injective (priorP A))
variable (q:Seat (mid P B)→SU.E)(F:List (Hos S r))(B': Ride S)(l:ℕ)
lemma doors: valve S (gauge q U) (gauge q V) Bv k= Lattice.gauge q (valve S U V Bv k):=by funext i; unfold valve Lattice.gauge; dsimp only; split<;> rfl
lemma seal_g (K:Kite S r)(b:Bool): Eire.printG S k (gauge q U) (gauge q V) Bv K.1 b=gauge q (printG S k U V Bv K.1 b):=by unfold Eire.printG; split <;> exact doors ..
variable (hq:Paths S r (Lattice.gauge q U₀) U₁ Y)(hg:Paths S r (Lattice.gauge q V₀) V₁ Y)(hk:HullK S k Y U₁ V₁ e)
include p pV tV hk h₀ hq hg B₁ B₂
lemma glow_g (K:Kite S r)(v:K∈ Y)(h:Bv⊆ L Y): postM S k C Q' U₁ V₁ (threadG q A) Bv K=Gaze q (postM S k C Q' U V A Bv K):=by
 have he : K.1∈ L Y:=mem_image_of_mem Prod.fst v; let X:=danceL S K.1.val r; let Z:Castle P B e (danceL S K.1.val r):= ⟨_,pays_l S k U V Y h₀ _ h _ he⟩
 unfold postM; rw [dif_pos (pays_l S k U₁ V₁ Y hk _ h _ he),dif_pos Z.property]; change _=Gaze q (Scion.stock e X Q' C Z A K.2); rw [←gauge_p e X Q' C Z A q _ B₂ (dance_g ..)] -- tune
 apply lit_i S C Q' K B₂ J B₁ _ _ _ _ (fun _ _=>rfl); intro b; let V': Support (Domain P B):=K.2.1∪K.2.2
 have hT:=tag_a G S p r k U₀ U V₀ V Bv K.1 b _ (pV K v) (tV K v); have hy:= tag_a G S p r k _ U₁ _ V₁ Bv K.1 b _ (hq K v) (hg K v)
 rw [show _= _ from seal_g S r k U₀ V₀ Bv q K b] at hy
 intro j w p; refine Eq.trans (hy j w p).symm ?_; change gauge q _ _=gauge q _ _; unfold Lattice.gauge; rw [hT j w p]
lemma plot_g : paint S k C Q' U₁ V₁ (threadG q A) Y (Plume.walksK (threadG q A))= Gaze q (paint S k C Q' U V A Y (Plume.walksK A)):=by
 have ht(z:List (Hos S r)): paint S k C Q' U₁ V₁ (threadG q A) Y z=Gaze q (paint S k C Q' U V A Y z):=by
    induction z with
    | nil=>rw [Eire.paint,Eire.paint,map_one]
    | cons i z ih=>rw [Eire.paint,Eire.paint,map_mul,ih]; congr 1; unfold rankG; split; rw [map_sum]; exact sum_congr rfl fun j v=> glow_g G S p r k Y A U V _ C Q' B₁ B₂ U₀ U₁ V₀ V₁ pV tV h₀ q hq hg hk _ (mem_filter.mp v).1 inter_subset_left; rw [map_one]
 exact ht (Plume.walksK A) -- proof threadG priority rfl
omit hk hq hg
include h₁ tU gU hA
lemma ports_o(i:Hos S r) : rankG S k C Q' U₁ V₁ (bun Θ A) (Y.image Λ) (F.map Ζ) (Ζ i) = teen Θ (rankG S k C Q' U V A Y F i):=by
 let Qy:= Y.image Λ; unfold rankG; by_cases v:i∈ L Y; swap; · rw [if_neg (mt (duck_b ..).1 v),if_neg v,map_one]
 rw [if_pos ((duck_b ..).2 v),if_pos v,map_sum]; have hp: clipM S Qy (F.map Ζ)=(clipM S Y F).image Ζ:=by
    ext i; obtain ⟨j,rfl⟩:=(laden S f r).surjective i; rw [clipM, mem_inter, show laden S f r j∈ L Qy↔ _ from duck_b G S f r Y j]; conv_rhs=> rw [mem_image]; simp only [(laden S f r).injective.eq_iff,exists_eq_right]
    simp only [clipM,List.mem_toFinset,mem_inter,List.mem_map,(laden S f r).injective.eq_iff, exists_eq_right]
 change ∑ j∈legend S Qy _,postM _ _ _ _ _ _ _ (clipM S Qy (F.map Ζ)) j= _; rw [hp]; symm; refine Finset.sum_equiv Λ ?_ fun j p=>?_ ; intro t; unfold legend Qy; simp only [mem_image,mem_filter,(luckP G S f r).injective.eq_iff,exists_eq_right]; apply and_congr_right; intro l; exact (laden S f r).injective.eq_iff.symm
 exact (oars G S ‹_› f r k Y A U V _ C Q' B₁ B₂ U₀ U₁ V₀ V₁ pV tV tU gU h₀ h₁ hA _ (mem_filter.mp p).1 inter_subset_left).symm
lemma ports_p(v:pureK S Y) : Eire.paint S k C Q' U₁ V₁ (bun Θ A) (Y.image Λ) (Plume.walksK (bun Θ A))= teen Θ (Eire.paint S k C Q' U V A Y (Plume.walksK A)):=by
 have ht(l:List (Hos S r)): Eire.paint S k C Q' U₁ V₁ (bun Θ A) (Y.image Λ) (l.map Ζ)=teen Θ (Eire.paint S k C Q' U V A Y l):=by
    induction l with
    | nil=> exact (map_one (teen Θ)).symm
    | cons i l ih=> rw [List.map_cons,Eire.paint,Eire.paint,map_mul,ih]; congr 1; exact ports_o G S p f r k Y A U V C Q' B₁ B₂ _ _ _ _ pV tV tU gU h₀ h₁ hA l i -- tune
 rw [← jug S k _ _ _ _ _ (Y.image Λ), work_t G S p f r Y A v hA, ht,jug]
end YM.CF.Salt
