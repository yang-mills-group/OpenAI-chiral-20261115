import YM.SU5.SatinWard.Resolution.Veering
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
def TwistP (Y:Course P (VolumeCape.Dream.Nimbus ℓ))(i s v:ℕ)(F:Site (side Y i s)→ Mark (side Y i v)):Prop:=∀ (j:Axis)(d:ℤ), ∃ c:ℝ, ‖c‖=1∧∀ (x:Site (side Y i s)), reflMark j (highTurn P s v d) (F x)= c • F ((plane j d).mills (side Y i s) x)
lemma SwingP.become {F:Site (side Y i s)→Mark (side Y i v)} (p:SwingP Y i s v F):TwistP Y i s v F:= fun j d=> ⟨1,norm_one,fun x=> (p j d x).trans (one_smul ..).symm⟩
open Hove
lemma TwistP.moveBill (Z0:Ramp)(x':∀ y, AtSupport false univ (F y))(p:TwistP Y i s v F) : TwistP Y i s v (transportT Z0 F):=by
 let u:=Z0.s; intro k L
 obtain ⟨i,rfl⟩:= (Z0.s.perm).surjective k; let q:=hush (u.flip i) L; have hh:hush (Z0.s.flip i) q=L:=by unfold q u; rw [hush_comp,Bool.xor_self,hush_false]
 obtain ⟨c,hc,t⟩:=p i q; refine ⟨c,hc,fun A=>?_⟩; let V:=(Z0.plan).mills _ A
 have he:hush (Z0.s.flip i) (highTurn P s v q)= highTurn P s v L:=by rw [←hh]; unfold highTurn; cases Z0.s.flip i <;> simp
 unfold transportT; rw [←he,←Z0.tilt_pair i _ (x' V),t]; have h:= Z0.plan_pins i q; rw [hh] at h; simp_rw [← Complex.coe_smul]
 have eq:{N:Side}→∀ f:Mark N,Z0.bill ((↑c:ℂ) • f)= (↑c:ℂ) • Z0.bill f:= fun f=> funext fun i=>by unfold Ramp.bill; simp only [Pi.smul_apply,theta_smul,Complex.star_def,Complex.conj_ofReal]
 rw [eq,←Nacre.yen,←Nacre.yen,h]
section
-- ψ. Use dimensionless label multiplied by real sign occupations inside powered orbit.
private lemma mountNorm {ι:Type} (F:ι→ Mark (side Y i v))(G:ι→ℝ)(V:∀ i,‖G i‖=1)(l:List ι) : ‖Journey.compass Y i k v (l.map (fun i=> G i • F i)).prod‖= ‖Journey.compass Y i k v (l.map F).prod‖:=by
 let c':ι→ℂ:= fun i=> G i; have eq(l:List ι): (l.map (fun i=>G i • F i)).prod=(l.map c').prod • (l.map F).prod:=by
    induction l with| nil=>simp | cons i l ih=>
                         rw [List.map_cons,List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,List.prod_cons]; rw [ih,← Complex.coe_smul,mul_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm] -- mathlib type instances? .FC, Mark norm not ring op?
 have hp(l:List ι): ‖(l.map c').prod‖=1:=by induction l with | nil=> simp| cons i l ih=>simp_rw [List.map_cons, List.prod_cons,norm_mul, show ‖c' i‖=_ from (Complex.norm_real _).trans (V i), ih,mul_one] -- Mark or Complex.
 unfold Journey.compass; rw [eq,mark_smul,mul_div_assoc,norm_mul,hp,one_mul]
include x in
lemma SeatsPriced.scale (c:ℝ)(t:‖c‖=1) : SeatsPriced A Y s i k v (c • F) f:=by
    simp_rw [←Complex.coe_smul]; refine ⟨fun i=> (x.fieldT _).smulM (c:ℂ), fun i g=>?_⟩; rw [show (c:ℂ) • F= (fun i=>c • (F i)) from (by rw [Complex.coe_smul]; rfl),mountNorm Y _ _ (fun _=>t)]; exact x.buys i g
end
variable (p:TwistP Y i s v F)
variable (H:Real.exp 1 ≤ P.x) (w:ℕ)(o:VelourBoard.Cell)(τ:Site (side Y i s))(er₁:s ≤ v)(hr:0 < f)
local notation "N✲" u:max=> side Y i u
local notation "W✲" => tent Y H
local notation "R✲"=> P.R.L.val ^ (v-s)
local notation "p₀"=> pitch W✲ w
local notation "d₀"=>rural (RootBook Y i k s).p.B+1
include x p er₁ hr
theorem stemLayer (b:Shield (W✲) w o (d₀) 0 (node τ)) (fee:14*meterC (ωs)*((↑(2*pitch (W✲) w:ℕ):ℝ)^4)≤1)(G:Buffered.Family (tent Y H))(x':exhibit Y H v i G=F τ)(l:List (VelourBoard.Tile (W✲))) (U Z:VelourBoard.Cell)(h:Deck (momentm Y i v) (R✲*w) (fun i=> (↑(R✲:ℕ):ℤ)*o i) G l U Z): ‖Journey.sharp Y H v i k (VelourBoard.Representation l)‖ ≤ (owedP A f)^l.length:=by
 let Q:=fun i'=> (↑(R✲:ℕ):ℤ)*o i'; have hz:((W✲).c (momentm Y i v)).val=(R✲:ℕ)*(N✲ s).val:=by rw [terrain Y H (Y.ir i) v,←refine_side,Nat.add_sub_of_le er₁]
 have vp:0 < (R✲:ℕ):=pow_pos P.R.L.property _; have hfit:= at_coarser vp hz h.fits; have hp:=coarser_fill vp hz h.fill
 let D:= (d₀); let W':= {c:ℝ // ‖c‖=1}; let L_:= Site (N✲ s)× W'; let G0:=fun a (y:L_)=> Shield W✲ w o D a (node y.1); let R₀(y:L_):= y.2.val • F y.1
 let scale(k:Axis)(x:ℤ)(Y:Mark (N✲ v))(a:ℝ): reflMark k x (a • Y)=a • reflMark k x Y:=by
    simp_rw [←Complex.coe_smul]; exact funext fun i=> by unfold reflMark; simp only [Pi.smul_apply,theta_smul,Complex.star_def,Complex.conj_ofReal]
 have turns:∀ a y,G0 a y→∀ j d,∃ y',G0 (tipped j d a) y' ∧ reflMark j (PaneCut W✲ ((R✲:ℕ)*w) Q j d) (R₀ y)= R₀ y':=by
    rintro a ⟨y,z⟩ v' j d; let s':=PaneCut W✲ w o j d; obtain ⟨c,hc,t⟩:= p j s'; refine ⟨⟨(plane j s').mills _ y,⟨z.val*c,by rw [norm_mul,hc,z.property,mul_one]⟩⟩,?_,?_⟩ -- norm_mul
    · unfold G0; rw [Shape.nodex]; exact turned j d _ v'
    unfold R₀ Q; dsimp only; rw [scaled_plane, show (↑(R✲:ℕ):ℤ)* _ =highTurn P s v s' from by unfold highTurn s'; rw [Nat.cast_pow],scale,t,smul_smul]
 let sep:=fun (x y:L_)=> rural (RootBook Y i k s).p.B < separation (node x.1) (node y.1)
 obtain ⟨L',length,val,_,a⟩:= inscribe Y H v i G0 R₀ ⟨⟨τ,⟨1,norm_one⟩⟩,b,x'.trans (one_smul ..).symm⟩ turns h.paved (fun _=>True) (fun _ _ _=>trivial) sep (fun _ _ p₁ p₂ n _ _ h₁ k₁=> lt_of_lt_of_le (by unfold D; omega : rural (RootBook Y i k s).p.B < 2*D) (separates hfit p₁ p₂ n h₁ k₁))
 rw [actualRead,val]; rw [show ‖_‖=‖Journey.compass Y i k v (L'.map fun i=> F i.1).prod‖ from mountNorm Y (fun y:L_=> F y.1) (fun y=>y.2.val) (fun y=>y.2.property) L', show (L'.map fun i=> F i.1)= (L'.map Prod.fst).map F from (List.map_map ..).symm]
 apply (x.buys (L'.map Prod.fst) (List.pairwise_map.mpr a)).trans; rw [List.length_map,length]; let ε:=meterC (ωs); have hi: sites (N✲ s) ≤ (↑(2*p₀:ℕ):ℝ)^4 * (l.length:ℝ):=by
    unfold sites; have hm:=hp.1; exact_mod_cast (show (More (N✲ s)).val^4 ≤ (2*p₀:ℕ)^4*l.length from by change ((N✲ s).val*2)^4 ≤ _; linarith only [Nat.mul_le_mul_left 16 hm])
 have hv:0≤ε:= Real.exp_nonneg _; have hs:14*ε*sites (N✲ s) ≤ l.length:=by
    nlinarith only [mul_le_mul_of_nonneg_left hi (show 0≤14*ε by linarith), mul_le_mul_of_nonneg_right (show 14*ε*_≤1 from fee) (Nat.cast_nonneg (α:=ℝ) l.length)]
 unfold laserRent owedP; rw [mul_pow,←Real.exp_nat_mul,mul_comm (f^_)]; apply mul_le_mul_of_nonneg_right (Real.exp_le_exp_of_le _) (pow_nonneg hr.le _); linarith only [show 14*meterC (ωs)*_ ≤ l.length from hs]

#print axioms stemLayer
end Tabletop
end YM.CF.Py.Rate.LocalLimit.Preparation
