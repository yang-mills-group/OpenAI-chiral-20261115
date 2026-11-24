import GaugeFieldConstruction.Oblo
import GaugeFieldConstruction.Fangs
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
open BellPrice PinRack
open BellPrice PinRack
open Py.Rate.Pitching.Focus Py.Rate.Pitching
variable {N P B:Side}{X:GramM (mid N B)}{Y:GramM (mid P B)}{h t s a b μ g τ:ℝ}{L:Side}{H:Scree.Hub (mid N B)}{o:Seat (mid P B)}{i j l k D:ℕ}
structure Chords (t s a g μ h τ:ℝ)(X':BudgetPoint)(Y':BudgetPoint)(L:Side) :Prop where
  full: 0≤μ
  thin :s ≤ 2*t
  price :a ≤ Rateκ L 3*t
  sky: g ≤ Rateκ L 3*t
  reachF: 0 ≤ h
  edge: t>0
  calm : 8≤τ
  stance :αN L*RamoK L ≤1
  ratioT : 1/2 ≤ s/t  -- space
  ratioY : 1/2 ≤ X'.threshold / Y'.threshold
private lemma vane_m (p: Chords t s a g μ h τ X.p Y.p L): 0 ≤ s:=by have he:= p.edge; have hp:= (le_div_iff₀ he).mp p.ratioT; linarith -- tune
variable {F:RegBudget (mid P B)}{W:Vow.Pax (mid N B)}{U:Aura (mid N B)}
variable (p:Chords t s a g μ h τ X.p Y.p L) (Y_: FuelKey X Y H o h a b g μ (RamoK L*s) U F W L) (hq:D ≤2)
include hq Y_ p
lemma GroundK (T:TollsK Y.p o Y.J.M F L s h (RamoK L) D 0) : let G:=Brow H X.J.M h X.p W L D; Basalt X.p H.val.1 L.val (L.val+1) G (Gapμ L μ*(Rateκ L (D+1)*t)) 2 b h D X.J.M := (Y_.gross D (D+1) hq (by omega) (over_C T hq p.reachF)).sharpen (LeftF p.thin p.full hq p.price p.edge.le) (le_refl _)
-- useful D+1 norm
abbrev T_w (L:Side)(r:ℕ)(q:ℝ)(p:BudgetPoint)(o:Seat N)(f: Male)(h:ℝ)(D:ℕ)(X:Zone N): Waves:=((((q*Rateκ L r)⁻¹:ℝ):ℂ)) • CardT X (KeyUp p) f h o D
abbrev BxMir (μ τ:ℝ):=SectorVal*Winner μ τ
variable (V:Waves) (Z:TollsK Y.p o Y.J.M F L s h (RamoK L) D V)(v:i≤ D)(hx: Cresc L.val Y.p (Zhub o))(h0: ∀ j:ℕ,ΓProj j V= if i ≤ j then V else 0) (hV: ‖V‖ ≤ τ)
omit p hq Y_
lemma N_prW {T:Type}(P:TPack T){s:ℝ}(p:0 ≤ s):letI:=P.G; letI:=P.S;∀ x:T, ‖(s:ℂ) • x‖=s*‖x‖:=by letI:=P.G; letI:=P.S; intro x; rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg p]
lemma OpX_pr {T:Type}(P:TPack T)(s:ℂ):letI:=P.G; letI:=P.S; ∀ x y:T,s • x-s • y=s • (x-y):=by letI:=P.G; letI:= P.S; intro x y; rw [smul_sub]
include p hq Y_ Z v hx h0 hV
set_option maxHeartbeats 400000 in
lemma Zenith_κ : let q:=H.val.1; let G:=Brow H X.J.M h X.p W L D; let J:= T_w L i t X.p q X.J.M h D G;
 Basalt X.p q L.val (L.val+1) G (Winner μ τ*(Rateκ L i*t)) 2 b h D X.J.M ∧
 ‖J‖ ≤ BxMir μ τ ∧ ‖ΓProj i J- PrintQ (s/t) (X.p.threshold / Y.p.threshold) V‖ ≤ Slipρ L μ ∧ ΓProj D J= J:=by
 intro q G J; let R:=Rateκ L i; let Z':=ToneQ F Y.p o Y.J.M h; have hf: ΓProj D Z'=(s:ℂ) • V:=Z.cen
 obtain ⟨u₀,u₁⟩:= Y_.perks D i hq v Z' (driver Z v hq p.reachF hx h0)
 have hJ: ΓProj i Z'=(s:ℂ) • V:=by
    rw [←show ΓProj i (ΓProj D Z')=ΓProj i Z' from MStore Z' v,hf,(ΓProj i).map_smul,h0,if_pos (by omega)]
 have hs : 0 ≤ s:=vane_m p
 have hR:0 < R:= Rate_pr ..; have he:= p.edge
 have ho :‖MSlot i Z'‖ ≤ s*τ:=by change ‖ΓProj i Z'‖ ≤ _; rw [hJ,N_prW Packs_U hs]; exact mul_le_mul_of_nonneg_left hV hs
 have hB:= (u₀.sharpen (RightF _ p.thin p.full (v.trans hq) p.price ho (by have hu:=p.calm; linarith) he.le p.stance) (le_refl b))
 refine ⟨hB,?_,?_,?_⟩
 · refine le_trans (b:=(t*R)⁻¹*(SectorVal*(Winner μ τ*(R*t)))) ?_ ?_
   · change ‖(((t*R)⁻¹:ℝ):ℂ) • (CardT G (KeyUp X.p) X.J.M h q D)‖ ≤ _; rw [N_prW Packs_U (show 0 ≤ (t*R)⁻¹ by positivity) -- need change
       ]; exact mul_le_mul_of_nonneg_left (CardT_note hB p.reachF (by norm_num) _) (by positivity)
   unfold BxMir; exact le_of_eq (by field_simp) -- ring tune
 · let J':=CardT G (KeyUp X.p) X.J.M h q i; let V':=MoonIdeal i L (KeyUp X.p) (KeyUp Y.p) Z'; let z:ℂ:= ((t*R)⁻¹:ℝ)
   have hk : ΓProj i J=z • J':=(show _ from (map_smul (ΓProj i) z (CardT G (KeyUp X.p) X.J.M h q D)).trans (congrArg (z • ·) (show ΓProj i (CardT G (KeyUp X.p) X.J.M h q D)= J' from MStore _ v)))
   rw [hk, ← show z • V'=PrintQ (s/t) (X.p.threshold / Y.p.threshold) V from fees_ideal V i D v hq (KeyUp X.p) (KeyUp Y.p) L Z' s t p.edge hf h0,OpX_pr Packs_U]; change ‖(((t*R)⁻¹:ℝ):ℂ) • (J'-V')‖ ≤ _
   rw [N_prW Packs_U (show 0 ≤ (t*R)⁻¹ by positivity)]
   calc
     _≤ (t*R)⁻¹*(Gapμ L μ*(Rateκ L (i+1)*t)):=mul_le_mul_of_nonneg_left (u₁.trans (LeftF p.thin p.full (v.trans hq) p.sky he.le)) (by positivity)
     _ = _:=by rw [show Rateκ L (i+1)=R*αN L from pow_succ ..]; unfold Slipρ; field_simp -- tune
 exact ((ΓProj D).map_smul (↑((t*R)⁻¹):ℂ) (CardT G (KeyUp X.p) X.J.M h q D)).trans (congrArg ( ((↑((t*R)⁻¹):ℂ)) • ·) (show ΓProj D (CardT G (KeyUp X.p) X.J.M h q D)=_ from MStore _ (le_refl _))) -- tune
end
end YM.CF.Oath
end
