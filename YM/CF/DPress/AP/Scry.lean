import YM.CF.DPress.AP.Rack
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
namespace Privilege
open Chess Wall Sermon Thrift RoomF Crib
open scoped YM.CF.BPress ComplexOrder
variable {F: RoomF J Λ M Δ}{D:Crib F n}{Z:Lore M B R A.μ}
 {Q:Source P_ J}{Y:StarPS n}{Z0:VestM M B R}
 {T: LedgerL D Z Y Z0}{Jp:ℕ→ℝ→ℝ}
 {ℓ k':ℕ}(G:Fixes Q D Z Y Z0 T Jp k)
variable (X:Wall) (h:X.aligned R.L) (p:Grip J ℓ k') (t:Told F) (v0: Articles Z)
local notation "Nt" t:max => cell M B R.L t
structure Entitle(W:Wall)(B L:Side)(n i:ℕ):Prop where
 g : W.aligned L
 p : (B.val:ℤ)∣ (L.val:ℤ)^(n-i)*W.o
namespace Entitle
lemma step {R:Side}(p:Entitle X B R n i)(h:i<n): Entitle (X.boost R) B R n (i+1):=by
 refine ⟨X.boost_align R p.g,?_⟩; have ht:=p.p; rw [show n-i=n-(i+1)+1 from (by omega),pow_succ,mul_assoc] at ht; change (B.val:ℤ)∣ _*(R.val • X.o); rwa [nsmul_eq_mul]
include G
lemma grant (h:i≤ k)(p:X.aligned R.L): Entitle X B R.L n i:=by
 refine ⟨p, dvd_mul_of_dvd_left ?_ _⟩; have hz:= G.side; rw [Q.pov]; push_cast; apply pow_dvd_pow; omega -- PNat.val_pow
end Entitle
include G X
lemma High (v:Entitle X B R.L n n) : Porch.TopTrace (den G n) ∧∀ A:Fixed.Test (Nt n), Boss (Nt n) (X.crop (Nt n) Wall.rail) A→ 0 ≤ Fixed.functional (den G n) (peer X A*A):=by
 have u:= v.p; rw [Nat.sub_self,pow_zero,one_mul] at u; obtain ⟨l,h⟩:= Green.purchase X (mesh M R.L n) B u; obtain ⟨Y,u,Yp,Ue⟩:=G.top; let H:= den G n; let t:= G.envelope (i:=n) le_rfl; have ht: H=denZ (Chaff.fulvia Y u (Vale.launch V.L (G.bot n).beta (Δ.a n) (cell M B R.L n))) U (F.Y n):= congrArg (fun x=>denZ x U (F.Y n)) Yp; change Porch.TopTrace H ∧ _;
 refine ⟨?_,?_⟩; · rw [ht]; exact Green.Chime.aurora V Ue (F.bloom.tint n)
 intro q p; rw [show den G n=_ from ht]; exact Green.Chime.daylight X V Ue h (Nat.cast_nonneg _) (F.bloom.tint n) (ht ▸ t) (Q.τF _) Q.ox q p
abbrev Gett(i:ℕ)(ℓ:ℕ):Prop:=∀ A:HT (Nt i),Learn X ℓ A→0 ≤ gram (F.Y i) (den G i) (peer_H X A A)
include t p v0
lemma pupil (v:Entitle X B R.L n i)(u:i<n)(q:Gett G (X.boost R.L) (i+1) ℓ): Gett G X i ℓ:=by
 obtain ⟨z,hz,g,Y⟩:= Main_p G X v.g v0 t u; let Q:=Classical.choice (G.payments u); obtain ⟨A,g,S⟩:= schooling X Q Y (Privilege.grant p t n i) hz g p.tagS; exact fun F h=> (S F F h h).symm ▸ q _ (g F h)
lemma forward (q:i ≤ n)(u:Entitle X B R.L n i): Gett G X i ℓ:=by
 induction q using Nat.decreasingInduction generalizing X with
 | self=> -- may be base
    obtain ⟨a,v⟩:= High G X u; obtain ⟨Y,q,S⟩:= Porch.release X a (F.rocket n).paid (t n) (G.envelope (i:=n) le_rfl) p.layout; intro U h; exact (S U U h h).symm ▸ v _ (q U h)
 | of_succ i l IH=> exact pupil G X p t v0 u l (IH (X.boost R.L) (u.step X l))
include h
lemma positive (v:i ≤ k){S:Fixed.Test (Nt i)}(u:Boss (Nt i) (X.crop (Nt i) (2*ℓ)) S) : 0 ≤ Fixed.numerator U (G.bot i) (F.Y i) (peer X S*S):=by
 have hu:= Wall.Lot_h p.layout; obtain ⟨q',g,v'⟩:= Porch.base X (show _≤2*ℓ from (by omega)) hu.1 (F.Y i) (den G i); change 0 ≤ Fixed.functional (den G i) _; exact (v' S S u u).symm ▸ forward G X p t v0 (v.trans G.order) (Entitle.grant G X v h) (q' S) (g S u) -- name clash h order & subst.DefLit.Foot need include h
end Privilege
end FitD
end YM.CF.Py.Kay
#print axioms YM.CF.Py.Kay.FitD.Privilege.positive
