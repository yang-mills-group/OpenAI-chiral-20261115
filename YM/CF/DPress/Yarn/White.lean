import YM.CF.DPress.Yarn.Log
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
abbrev JStep (p : Sweep (cell M B R.L i)→Prop)(X:Yds (cell M B R.L i))(e:ℝ):Prop:= Léon (Δ.a i) C.h R.L.val X e∧SecureD p (D.venue i).J.M (Δ.a i) R.L.val K.j X
lemma rank_none (y:LogH (cell M B R.L i))(e:ℝ): JStep (i:=i) D Utrue y.fuel e ↔ D.stipend_h i y e none:=by
 constructor; · rintro ⟨p,v⟩; exact ⟨⟨p.E.weight,v.ru⟩,rfl,⟨p.K.weight,v.du⟩,p.oily,v.mint⟩
 intro v; exact fromLaurel (P:=mesh M R.L i) v -- names
omit D in
abbrev Lore(M:Side)(B:Side)(R:Patch)(k:ℕ):= ∀ i:ℕ, Blend (cell M B R.L i) k
local notation "nW"=> cell M B R.L
local notation "μH"=> hat R.L x
variable (Z: Lore M B R A.μ)
local notation "Tk" h:max => (σp D i h)
local notation "εΦ"=> (jC i)
local notation "D_" g:max=> (locale D i g)
-- relation includes commitment to projections. only at h, independent of lower β. use with FTC.
inductive Spell (i:ℕ)(β α:ℝ)(u:LogH (cell M B R.L (i+1)))(v:LogH (cell M B R.L i)) : Prop
| via (g:i<n)(X:LobbyP D g β)(G:HonestL X)(tp:Silo.Can (D.locale i g) P_ (Λ.O (hat R.L x i)).δ α)(s:u.fuel=X.F0)(p:u.v=X.J)(ζ:v=postH D β X (Z i) α G tp):Spell i β α u v
local notation "τh" h:max=> D.locale i h
variable {β α δ:ℝ}{u:LogH (cell M B R.L (i+1))}{v:LogH (cell M B R.L i)}
lemma Spell.step (p:Spell D Z i β α u v):∀ z:Orbit (cell M B R.L i), Rue.FleetS (Δ.a i).threshold z.1 → denZ (D.render i v (β + D.toll i-v.δ)) U (F.Y i) z=Real.exp ((Z i).Φ (h:=(Δ.a i).threshold) α z.1) • stove U (F.Y i) (D.render (i+1) u β) (F.Y (i+1)) (apt M B R.L i) (jS i) C.q' J.d (v.r).val z:=by
 obtain ⟨g,X,G,t,s,e,p⟩:=p; subst v; intro z η; have ht:= packaged D β X (Z i) α G t; dsimp only at ht; rw [ht,←D.clk.point,show D.render (i+1) u β = X.Y from (by unfold render; rw [s,e])]; exact Silo.PI_step (σp D i g) (Z i) α X G t z η _ -- order
lemma Spell.valid (p:Spell D Z i β α u v): JStep (i:=i) D (Silo.ok_turn (Z i) α) v.fuel (A.meter (Λ.w (hat R.L x i))) :=by
 obtain ⟨g,X,G,t,s,e,p⟩:=p; subst v; rw [Λ.getW]; exact ⟨Silo.standard (Tk g) (Z i) α X G t (F.epoch i).tax.sponsors,Silo.secure (Tk g) (Z i) α X G t⟩
variable (h: D.stipend_h (i+1) u (Tew.tiny R (hat R.L x (i+1))) none) -- use before stamp
include h
lemma smallU : JStep (i:=i+1) D Utrue u.fuel (Tew.tiny R (hat R.L x i)):=by
 apply (rank_none D ..).2; exact h.towers ((F.epoch i).tiny _ (F.age i (by omega))) -- h projection. include h.
include h D Z
set_option maxRecDepth 4096 in
lemma Spell.core (p:Spell D Z i β 0 u v) : D.stipend_h i v (Tew.tiny R (hat R.L x i)) none ∧ ‖v.r‖≤ P_.Rs (hat R.L x i) ∧ |v.δ|≤ Ψs (P_:=P_) (hat R.L x i)∧ ‖Complex.exp u.v‖*F.c_ps i≤ ‖Complex.exp v.v‖ :=by
 obtain ⟨g,Ux,G,t,z,r,p⟩:=p; subst v; let t':= F.epoch i; let Y0:= Tk g; have ht:= (smallU D h).1; rw [z] at ht; let T:= ht.toAccountY; let W:=F.loaf i (n-1-i); have hv:Tew.tiny R (hat R.L x i)≥0:= t'.tax.Dust0.tiny.le
 refine ⟨?_ , Urban.powerS Y0.p Y0.u Ux G T,Y0.αlow _ _ T, ?_ ⟩ -- ht defeq. POWER might fail i vs i+1 but T is level i+1. `CoreD δ=q`. field.notation q.validate.
 · exact Provides.towers (show Provides R.L K.j (D.render i (D.postH β Ux (Z i) 0 G t) 1) C.h (A.meter (Tew.tiny R (hat R.L x i))) none from ⟨Y0.standardSmR (Z i) Ux G T,rfl,Y0.standardSmK _ _ G T t'.tax.sponsors,(Y0.R_terms _ 0 Ux G t).2.1,(Y0.R_terms _ 0 Ux G t).2.2.2⟩) (Λ.η_upper hv)
 rw [r]; change _≤ ‖Complex.exp (vπ (Tk g) (Z i) _ Ux G t (monus _))‖; rw [Silo.zero_vπ]; exact W.earn _ (D.locale i g) Λ.ξ (Tk g) (Z i) β Ux G
local notation "Xp"=> (Λ.O (hat R.L x i))
def lowX (g:i<n)(p:matchedX (hat R.L x (i+1)) β)(u:LogH (cell M B R.L (i+1)))(h:D.stipend_h (i+1) u (Tew.tiny R (hat R.L x (i+1))) none): LobbyP D g β :=⟨u.fuel,u.v,(yearβ g _|>.2 p),(smallU D h |>.1).more C.uB (F.epoch i).tax.Dust0.coins⟩ -- tune include h / Z implicit needed
omit Z
lemma litX(g:i<n)(p:matchedX (hat R.L x (i+1)) β) : HonestL (lowX D g p u h):= (smallU D h|>.2).small (fun _ _=>trivial)
end Crib
end FitD
end YM.CF.Py.Kay
