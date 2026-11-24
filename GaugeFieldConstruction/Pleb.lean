import GaugeFieldConstruction.Diro
import GaugeFieldConstruction.PressureB
import GaugeFieldConstruction.Kuriso
import GaugeFieldConstruction.Kans
import GaugeFieldConstruction.Trump
import GaugeFieldConstruction.IconF
import YM.SU5.Selected.Lantern.Petrol
import YM.SU5.Celeste.Pass
import GaugeFieldConstruction.Payola
import GaugeFieldConstruction.Lycoris
import GaugeFieldConstruction.Pelota
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Postmark
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open scoped YM.CF.Mew
open Fock.Flux Girt TableF TableF.Lenten.Layout Gleam.Guide CF.XGarden CF.XGarden.MastTin ArtCart Zpress ScopeU Buffered
open FrameP
open Violets ProbabilityTheory Regis.Head Regis.Head.Brecht
open Gleam.Guide.Pitcher Coins Pacts Prims
-- notation state.
open Lamour.Bridge.Celeste (liftMoney)
open Vale.Veins Exterior Matrix
variable (s:ℕ) (i k:ℕ→ℕ)(h:Tendsto i atTop atTop)(g:Tendsto k atTop atTop)
namespace SpaΘ
variable {t r:ℝ}{x y z:Cover}{F H Q:ℕ→Paper N}{C D T: MastTin.ArtCart.Genre}
-- generic facet arcs for sum.S
abbrev Ringα (j:ℕ)(x y:Wα):= RingW Y s i k x y j
abbrev RingF (j:ℕ)(x y:Wφ):= RugF Y s i k x y j
def Pokes (c d:Chip) : Prop:= match c,d with
 | .litt i j,.litt p q=> Gutter i.1 p.1 ∧ Gutter j.1 p.1∧ Gutter i.1 q.1 ∧ Gutter j.1 q.1
 | .creel i _ _,.creel j _ _ =>Gutter i.1 j.1
 | .litt i j,.creel k _ _ => Gutter i.1 k.1∧Gutter j.1 k.1
 | .creel i _ _,.litt k l=> Gutter i.1 k.1∧ Gutter i.1 l.1
 | _,_=>True
include h g
lemma sigmL (j l:Chip)(p:Pokes j l): Tendsto (fun k' => Chip.budget2 (Ringα Y s i k k') (RingF Y s i k k') j l) atTop (𝓝 (Chip.budget2 κg κF j l)):=by
 let F:= Swalin Y s i k h g; let K:=Salmon Y s i k h g
 cases j with
 | litt a b=> cases l with
              | litt u v=> exact (((K a u p.1).mul (K b v p.2.2.2)).add ((K a v p.2.2.1).mul (K b u p.2.1)))
              | _=> exact tendsto_const_nhds
 | cuff a b=> cases l with
              | cuff j l=> exact ((F a l).mul (F j b)).neg
              | _=> exact tendsto_const_nhds
 | creel c a b=>cases l with
                | creel d r u=> exact (((F a u).mul (F r b)).neg.mul (K c d p))
                | _=> exact tendsto_const_nhds
lemma Tolo (a b c:Chip)(p:Pokes a b)(r:Pokes b c)(t:Pokes a c): Tendsto (fun k' => Chip.budget3 (Ringα Y s i k k') (RingF Y s i k k') a b c) atTop (𝓝 (Chip.budget3 κg κF a b c)):=by
 let F:=Swalin Y s i k h g; let K:=Salmon Y s i k h g
 have hM(a b c d r t:Wφ):Tendsto (fun j=> Δρ (RingF Y s i k j) a b c d r t) atTop (𝓝 (Δρ κF a b c d r t)):= (((F a d).mul (F c t)).mul (F r b)).add (((F a t).mul (F r d)).mul (F c b))
 cases a with
 | litt u v=>
   cases b with
   | litt a b=>
     cases c with
     | litt c d=>
        have ht:= K u a p.1; have hv:= K v a p.2.1; have hx:= K u b p.2.2.1; have hp:=K v b p.2.2.2
        have He:=K u c t.1; have Ht:=K v c t.2.1; have Hx:=K u d t.2.2.1; have Hp:=K v d t.2.2.2
        have hq:=K a c r.1; have hl:=K b c r.2.1; have hY:=K a d r.2.2.1; have hZ:=K b d r.2.2.2
        exact (((ht.mul ((Ht.mul hZ).add (Hp.mul hl))).add (hx.mul ((Ht.mul hY).add (Hp.mul hq)))).add (He.mul ((hv.mul hZ).add (hp.mul hY)))).add (Hx.mul ((hv.mul hl).add (hp.mul hq)))
     | _=>exact tendsto_const_nhds
   | creel f a b=> cases c with
                   | creel q c d=> exact (((F a d).mul (F c b)).neg).mul (((K u f p.1).mul (K v q t.2)).add ((K u q t.1).mul (K v f p.2)))
                   | _=> exact tendsto_const_nhds
   | cuff a b=> cases c<;>exact tendsto_const_nhds
 | cuff a u=> cases b with
              | cuff j k'=> cases c with
                             | cuff h tζ => exact hM a u j k' h tζ
                             | _=>exact tendsto_const_nhds
              | creel f v w=> cases c with
                             | creel r' i j=> exact (hM a u v w i j).mul (K f r' r)
                             | _=>exact tendsto_const_nhds
              | _=> cases c<;> exact tendsto_const_nhds
 | creel z l w =>cases b<;>cases c<;> exact tendsto_const_nhds
omit h g
abbrev StrictP (N: Side)(C D:Genre)(x y: Cover):Prop:= ∀ u v,Pokes (ChipUp N x C u) (ChipUp N y D v)
-- eventual universals Path on arbitrary s. Telescope error multiplied $separate Caps$. GL.Sp $Ten$.W1.
abbrev SeatPulse (x:Cover)(G:Genre)(F:ℕ→ Paper N)(r:ℝ): Prop:=∀ᶠ t:ℕ in atTop,F t∈ Glamor (Θk N x) G r
def FitE (X:ℕ→ℂ):Prop:= ∃ c>0,∀ᶠ x:ℕ in atTop, ‖X x‖≤ c
lemma Fwd (w:300<N.val)(f: SeatPulse x C F t) (d:ShapeZ N x C):FitE (fun i=> CrispC (F i) x C d):=by obtain ⟨c,p,h⟩:=kiosk (n:=N) C t w; exact ⟨c,zero_lt_one.trans_le p,f.mono fun x v=>h _ _ v _⟩
lemma Fitsμ (u v:ℕ→ℂ)(p:FitE u)(q:FitE v):FitE (fun j=>u j*v j):=by
 obtain ⟨c,t,p⟩:=p; obtain ⟨m,w,v⟩:=q; refine ⟨c*m,mul_pos t w,(p.and v).mono fun i p=> (norm_mul ..).le.trans (mul_le_mul p.1 p.2 (norm_nonneg _) t.le)⟩
lemma Zux (X Y:ℕ→ℂ)(p:FitE X)(v:Tendsto Y atTop (𝓝 0)):Tendsto (fun i=>X i*Y i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero]; obtain ⟨c,t,w⟩:=p; refine squeeze_zero' (g:=fun i=> c*‖Y i‖) ?_ ?_ ?_; · exact Eventually.of_forall fun _=>norm_nonneg _
 · exact w.mono fun i h=> (norm_mul ..).le.trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
 simpa only [norm_zero,mul_zero] using v.norm.const_mul c -- tune
include h g
abbrev pulseS (x:Cover)(C:Genre)(F:ℕ→ Paper N)(t:ℕ): Payν N:= (x,C,F t)
def TingC (a b: ℕ→ Payν N)(j:ℕ):= if p:s≤Y.uv (k j) then pari Y s (i j) (k j) p (a j) (b j) else 0
def TingX (a b c: ℕ→ Payν N)(j:ℕ):= if p:s≤Y.uv (k j) then tripC Y s (i j) (k j) p (a j) (b j) (c j) else 0
local notation "Rφ" t:max => RingF Y s i k t
local notation "Rα" t:max => Ringα Y s i k t
lemma objective (w:300<N.val)(L:StrictP N C D x y) (p:SeatPulse x C F t)(e:SeatPulse y D H r): let A:= pulseS x C F; let B:=pulseS y D H; Tendsto (fun j=>TingC Y s i k A B j - quotaZ (A j) (B j) κg κF) atTop (𝓝 0):=by
 intro A B; let Q(j:ℕ)(a:ShapeZ N x C)(b:ShapeZ N y D):ℂ:= CrispC (F j) x C a*CrispC (H j) y D b; let V:= ChipUp N x C; let W:=ChipUp N y D; let E(a:ShapeZ N x C)(b:ShapeZ N y D)(j):=Chip.budget2 (Rα j) (Rφ j) (V a) (W b)-Chip.budget2 κg κF (V a) (W b)
 have hx(j':ShapeZ N x C)(t₀:ShapeZ N y D): Tendsto (fun j=>Q j j' t₀ * E j' t₀ j) atTop (𝓝 0):=Zux _ _ (Fitsμ _ _ (Fwd w p _) (Fwd w e _)) (by simpa only [sub_self] using (sigmL Y s i k h g (V j') (W t₀) (L j' t₀)).sub_const (Chip.budget2 κg κF (V j') (W t₀)))
 have hp:Tendsto (fun j:ℕ=>∑ a:ShapeZ N x C,∑ b:ShapeZ N y D, Q j a b*E a b j) atTop (𝓝 0):=by
    convert tendsto_finsetSum univ (fun j _=> tendsto_finsetSum univ fun i _=> hx j i) using 1; simp
 refine hp.congr' ?_; filter_upwards [(Y.uv_grows.tendsto_atTop.comp g).eventually_ge_atTop s,p,e,pad_T Y s i h] with j h t v G; change s≤ Y.uv (k j) at h; rw [TingC,dif_pos h, gala _ _ _ _ h G w (A j) (B j) ⟨_,t⟩ ⟨_,v⟩]; unfold Q E; simp_rw [mul_sub,sum_sub_distrib]; rw [show Rα j=GaWin Y s (i j) (k j) h from (funext fun x=>funext fun y=> dif_pos h)]; try rfl
lemma tre_j (w:300<N.val)(L:StrictP N C D x y)(L':StrictP N C T x z)(V':StrictP N D T y z)(c:C≠ Genre.mixed)(p:SeatPulse x C F t)(e:SeatPulse y D H r)(Kκ:ℝ)(pT:SeatPulse z T Q Kκ): let A:= pulseS x C F; let B:=pulseS y D H; let U:=pulseS z T Q; Tendsto (fun j=>TingX Y s i k A B U j - quotas (A j) (B j) (U j) κg κF) atTop (𝓝 0):=by
 intro A B U; let Z(j:ℕ)(a:ShapeZ N x C)(b:ShapeZ N y D)(r:ShapeZ N z T):ℂ:= CrispC (F j) x C a*CrispC (H j) y D b*CrispC (Q j) z T r; let V:= ChipUp N x C; let W:=ChipUp N y D; let Yk:= ChipUp N z T; let E(a:ShapeZ N x C)(b:ShapeZ N y D)(r:ShapeZ N z T)(j):=Chip.budget3 (Rα j) (Rφ j) (V a) (W b) (Yk r)-Chip.budget3 κg κF (V a) (W b) (Yk r)
 have hx(j':ShapeZ N x C)(t₀:ShapeZ N y D)(l₀:ShapeZ N z T): Tendsto (fun j=>Z j j' t₀ l₀* E j' t₀ l₀ j) atTop (𝓝 0):=Zux _ _ (Fitsμ _ _ (Fitsμ _ _ (Fwd w p _) (Fwd w e _)) (Fwd w pT _)) (by simpa only [sub_self] using (Tolo Y s i k h g (V j') (W t₀) (Yk l₀) (L j' t₀) (V' t₀ l₀) (L' j' l₀)).sub_const (Chip.budget3 κg κF (V j') (W t₀) (Yk l₀)))
 have hp:Tendsto (fun j:ℕ=>∑ a:ShapeZ N x C,∑ b:ShapeZ N y D,∑ r:ShapeZ N z T,Z j a b r*E a b r j) atTop (𝓝 0):=by
    convert tendsto_finsetSum univ (fun j _=> tendsto_finsetSum univ fun i _=>tendsto_finsetSum univ fun k _=> hx j i k) using 1; simp
 refine hp.congr' ?_; filter_upwards [(Y.uv_grows.tendsto_atTop.comp g).eventually_ge_atTop s,p,e,pT,pad_T Y s i h] with j h t v pG G; change s≤ Y.uv (k j) at h; rw [TingX,dif_pos h, gleam _ _ _ _ h G w (A j) (B j) (U j) ⟨_,t⟩ ⟨_,v⟩ ⟨_,pG⟩ c]; unfold Z E; simp_rw [mul_sub,sum_sub_distrib]; rw [show Rα j=GaWin Y s (i j) (k j) h from (funext fun x=>funext fun y=> dif_pos h)]; try rfl
#print axioms tre_j
end SpaΘ
#print axioms SpaΘ.objective
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
