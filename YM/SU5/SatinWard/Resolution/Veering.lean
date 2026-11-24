import YM.SU5.SatinWard.Resolution.Portal
import Velour.Crepe.GapSet
import YM.SU5.Reconstruction.Oblique.TiltAxis
import YM.SU5.Reconstruction.Oblique.Consulting
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 85000
noncomputable section
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
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
open Ione Beau Haro Cascade Fief
open scoped Mew
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
open BScale Vow.TreasuryFog Sour Roots Exa Vow Rive Mew Stax Swell Porticus QuadClock Ione.Clock Moto Neon Taxi Lor
open Oise Buffered
open Pitching Focus QuadClock.ShapeLab
open Oise Buffered
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ)) (Γ:ℝ)(Pay kc:ℝ)(Tξ:Hove.Grant P.K.j 2)(nmc m:ℕ) (Z V K W:ℝ→ℝ)
variable {η ι:Type}[Fintype ι][DecidableEq ι][Fintype η](F:ResolutionFrame ι)(C H A:ℝ)
open Pail.Dew Swell.Porticus QuadClock.ShapeLab.ResolutionFrame
open Lampshade SignSlot Waxy Tap
variable {a b c d U ε f r ψ:ℝ}{s i k:ℕ}
local notation "Λ" => P.Ctor (Y.ir i) s
local notation "θ"=>lapQ Y s
local notation "ωs"=> hat P.R.L P.x s
open Hove Yoke Buffered Afterglow Journey ShapeLab.ResolutionFrame
namespace Tabletop

open ResolutionFrame Vow.TreasuryFog Swell
open ResolutionFrame Rue Advance Tapestry
variable {I:Type}[Fintype I][LinearOrder I]{v z:ℕ}
attribute [-instance] instDecidableEqLex
local notation "WK"=> Booth I η
local notation "Θ"=> P.Ctor (Y.ir i) (s+1)
local notation "εμ"=> Primary ι η
local notation "Φ"=> F.colors (P.Ctor (Y.ir i) s)
local notation "Xp"=> RootBook Y i k s
local notation "Xf"=> RootBook Y i k (s+1)
local notation "G★"=> Vale.apt (Y.ir i) P.block P.R.L s
-- lean abbrev turnover step receipts. ensure proof printed. preserve all Step assumptions to reuse for grafts later.
variable [DecidableEq η](D:ArmorK)
set_option maxHeartbeats 240000
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Pressure.Worth Worth.Pays Graph
-- all annual payments. `Invoices` even in integrating on that partition, with q^{-1} radius when earned. Normed.Check.
open Again Tapestry Tower.SlabMark Tower.Tilted VelourBoard
variable {f₀ g y:ℕ}{F:Site (side Y i s)→ Mark (side Y i v)}(x:SeatsPriced A Y s i k v F f) (j:Axis) (q:ℤ)
def SwingP (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i s v:ℕ)(F:Site (side Y i s)→ Mark (side Y i v)):Prop:=∀ (j:Axis)(d:ℤ)(x:Site (side Y i s)), reflMark j (highTurn P s v d) (F x)= F ((plane j d).mills (side Y i s) x)
variable {U R S N:Side}(Z0: Tower.Tilted.Ramp)
local notation "M"=> Z0.plan
lemma heelingTurn (p:s≤v)(x:Site (side Y i s)): upRoot Y i p ((M).mills _ x)= (M).mills _ (upRoot Y i p x):=by
 induction p with
 | refl=> simp only [upRoot,climbing_refl]
 | @step y p ih=>
   let G':=Vale.apt (Y.ir i) P.block P.R.L y
   apply QuadClock.node_inj
   -- Shape.broad plan
   have h:Shape.broad G' Z0.plan=Z0.plan:= by simp [Shape.broad,Ramp.plan,incX]
   simp only [upRoot,climbing_succ _ _ p]; rw [mansion_L G' P.R.odd_side]; unfold upRoot at ih; rw [ih,Shape.nodex,Shape.nodex,Shape.foldsT,mansion_L G' P.R.odd_side,h]
def transportT (V':Site S→Mark U):Site S→Mark U := fun i=> Z0.bill (V' ((M).mills _ i))
include x in
lemma SeatsPriced.transported (p:Tapestry.Pay Y v i k) : SeatsPriced A Y s i k v (transportT Z0 F) f:=by
 constructor; · exact fun i=>(Z0.term_marked (x.fieldT _)).mono (subset_univ _)
 intro l w; let T:= (M).mills (side Y i s) -- binder implicit?
 let Y₀:=l.map T; have ht: outdoor (rural (RootBook Y i k s).p.B) Y₀:= List.pairwise_map.mpr (w.imp (by intro i j h; simp only [T,Shape.nodex,Shape.anon,affine,separation_translate,separation_signed]; exact h))
 have hi {I:Type}(l:List I)(x:I→Mark (side Y i v)): Z0.bill (l.map x).prod= (l.map (Z0.bill ∘ x)).prod:=by
    induction l with
    | nil=> exact funext fun i=> Fock.theta_one ..
    | cons i l ih=> simp only [List.map_cons,List.prod_cons]; rw [←ih]; exact funext fun i=> Fock.theta_mul ..
 have he:(l.map (transportT Z0 F)).prod=Z0.bill (Y₀.map F).prod:= by unfold Y₀; rw [List.map_map,hi]; rfl
 have Q:=x.buys Y₀ ht; rw [show Y₀.length=l.length from List.length_map T] at Q -- occurrences
 rw [he,all_steps Y Z0 i k v p (receipt_word x.fieldT Y₀ (fun _ _=> Finset.Subset.refl _)), norm_star]
 exact Q
variable (p:SwingP Y i s v F)
include p
lemma SwingP.transported (x':∀y, AtSupport false univ (F y)) : SwingP Y i s v (transportT Z0 F):= by
 let u:=Z0.s; intro k L A
 obtain ⟨i,rfl⟩:= (Z0.s.perm).surjective k; let q:=hush (u.flip i) L; have hh:hush (Z0.s.flip i) q=L:=by unfold q u; rw [hush_comp,Bool.xor_self,hush_false]
 let V:= (M).mills _ A
 have he:hush (Z0.s.flip i) (highTurn P s v q)= highTurn P s v L:=by rw [←hh]; unfold highTurn; cases Z0.s.flip i <;> simp
 unfold transportT; rw [←he,←Z0.tilt_pair i _ (x' V),p i]
 have h:= Z0.plan_pins i q; rw [hh] at h
 unfold V; rw [←Nacre.yen,←Nacre.yen,h]

variable (H:Real.exp 1 ≤ P.x) (w:ℕ)(o:VelourBoard.Cell)(τ:Site (side Y i s))(er₁:s ≤ v)(hr:0 < f)
local notation "N✲" u:max=> side Y i u
local notation "W✲" => tent Y H
local notation "R✲"=> P.R.L.val ^ (v-s)
local notation "p₀"=> pitch W✲ w
local notation "d₀"=>rural (RootBook Y i k s).p.B+1
abbrev owedP (A:ℝ)(f:ℝ):= Real.exp (4*A+1)*f
include x p er₁ hr
theorem gapLayer (b:Shield (W✲) w o (d₀) 0 (node τ)) (fee:14*meterC (ωs)*((↑(2*pitch (W✲) w:ℕ):ℝ)^4)≤1)(G:Buffered.Family (tent Y H))(x':exhibit Y H v i G=F τ)(l:List (VelourBoard.Tile (W✲))) (U Z:VelourBoard.Cell)(h:Deck (momentm Y i v) (R✲*w) (fun i=> (↑(R✲:ℕ):ℤ)*o i) G l U Z): ‖Journey.sharp Y H v i k (VelourBoard.Representation l)‖ ≤ (owedP A f)^l.length:=by
 let Q:=fun i'=> (↑(R✲:ℕ):ℤ)*o i'; have hz:((W✲).c (momentm Y i v)).val=(R✲:ℕ)*(N✲ s).val:=by rw [terrain Y H (Y.ir i) v,←refine_side,Nat.add_sub_of_le er₁]
 have vp:0 < (R✲:ℕ):=pow_pos P.R.L.property _; have hfit:= at_coarser vp hz h.fits; have hp:=coarser_fill vp hz h.fill
 let D:= (d₀); let G0:=fun a (y:Site (N✲ s))=> Shield W✲ w o D a (node y)
 have turns:∀ a y,G0 a y→∀ j d,∃ y',G0 (tipped j d a) y' ∧ reflMark j (PaneCut W✲ ((R✲:ℕ)*w) Q j d) (F y)= F y':=by
    intro a y v' j d; let s':=PaneCut W✲ w o j d; refine ⟨(plane j s').mills _ y,?_,?_⟩
    · unfold G0; rw [Shape.nodex]; exact turned j d _ v'
    unfold Q; rw [scaled_plane, show (↑(R✲:ℕ):ℤ)* _ =highTurn P s v s' from by unfold highTurn s'; rw [Nat.cast_pow]]; exact p j s' y -- inferred term
 let sep:=fun (x y:Site (N✲ s))=> rural (RootBook Y i k s).p.B < separation (node x) (node y)
 obtain ⟨L',length,val,_,a⟩:= inscribe Y H v i G0 F ⟨τ,b,x'⟩ turns h.paved (fun _=>True) (fun _ _ _=>trivial) sep (fun _ _ p₁ p₂ n _ _ h₁ k₁=> lt_of_lt_of_le (by unfold D; omega : rural (RootBook Y i k s).p.B < 2*D) (separates hfit p₁ p₂ n h₁ k₁)) -- h shadows ok? k shadows name in rural!
 rw [actualRead,val]
 apply (x.buys L' a).trans; rw [length]; let ε:=meterC (ωs); have hi: sites (N✲ s) ≤ (↑(2*p₀:ℕ):ℝ)^4 * (l.length:ℝ):=by
    unfold sites; have hm:=hp.1; exact_mod_cast (show (More (N✲ s)).val^4 ≤ (2*p₀:ℕ)^4*l.length from by change ((N✲ s).val*2)^4 ≤ _; linarith only [Nat.mul_le_mul_left 16 hm])
 have hv:0≤ε:= Real.exp_nonneg _; have hs:14*ε*sites (N✲ s) ≤ l.length:=by
    nlinarith only [mul_le_mul_of_nonneg_left hi (show 0≤14*ε by linarith), mul_le_mul_of_nonneg_right (show 14*ε*_≤1 from fee) (Nat.cast_nonneg (α:=ℝ) l.length)]
 unfold laserRent owedP; rw [mul_pow,←Real.exp_nat_mul,mul_comm (f^_)]; apply mul_le_mul_of_nonneg_right (Real.exp_le_exp_of_le _) (pow_nonneg hr.le _); linarith only [show 14*meterC (ωs)*_ ≤ l.length from hs]
#print axioms SeatsPriced.transported
#print axioms gapLayer
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
