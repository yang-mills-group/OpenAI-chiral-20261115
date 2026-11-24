import YM.SU5.FiniteGaugeData.Tapestry.Pinnacles
/-!
Breadth `nonzero advanced` guarantees visibility of the opening observations already on actual joint draws,
not a figment of testing & distinguishing off-draw values of marks after NativeFaith.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 3500
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude

variable {Λ:Preparation} {l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1 ≤ Λ.x) (i k s:ℕ)
local notation "Ωs" => side Y i s
local notation "C" => (Y.voyage i).CapeT s
local notation "K" => tent Y H
lemma awakenAscVU (q:PairIdx Y s i k) (F:Mark (side Y i s))(u:Envelope F)(e: ∀ᵐ x∂city (side Y i s), F (drawn ((Y.voyage i).CapeT s) x)=0) : ascender Y s i k F =0:=by
 let A:= (fullness Y i k q.1).cap_grant
 let G:=Vale.apt (Y.ir i) Λ.block Λ.R.L s
 obtain ⟨L⟩:= A.grant s q.2
 let Z:=((Y.voyage i).X (Y.uv k)).gram (s+1); let f:=gathered G Λ.K.j (patternQ Y s i k).val Z.J.M Λ.R.odd_side Chi.canonical Λ.J.d F; funext W
 let d(x:Orbit (side Y i s)):= (patternA Y s i k).density (G:=SU.group) Z.beta W.1 x.1
 have hr: ascender Y s i k F W=∫ x,d x • f W (drawn ((Y.voyage i).CapeT s) x)∂city Ωs:= outright G (patternA Y s i k) Λ.K.j (patternQ Y s i k).val Z.J.M _ _ _ _ _ (Journey.legal _) ((Y.voyage i).ownership s).paid.bill (A.branch s q.2) L.legal.1 L.legal.2 _ u W
 rw[hr]; apply integral_eq_zero_of_ae
 filter_upwards [e] with x p; unfold f gathered avgF; simp only [before,p,map_zero,sum_const_zero,smul_zero]; rfl
lemma firstCoinVU (F:Dome (tent Y H)) : attire (breathing Y H s i k (pinhole _ s F))= exhibit Y H s i F.val:=by unfold breathing; rw[Decking.outcrop]; rfl
lemma coinBondVU {x:Cloud (Dome (tent Y H))}(w:x∈shorter _ s): breathing Y H (s+1) i k x= music Y s i k (breathing Y H s i k x):=(tidalDressing Y H i k).joins s x _ w
lemma emptyBondVU {x:Cloud (Dome (tent Y H))}(w:x∈shorter _ s)(e:breathing Y H s i k x=0){j:ℕ}(p:s≤j): breathing Y H j i k x=0:=by
 induction j,p using Nat.le_induction with
 | base=> exact e
 | succ t h ih=>rw [coinBondVU Y H _ _ t (climbs _ h w), ih, map_zero]
lemma awakeningRootVU(q:PairIdx Y s i k)(F:Dome (tent Y H))(e:∀ᵐ x∂city (side Y i s),(exhibit Y H s i F.val) (drawn ((Y.voyage i).CapeT s) x)=0): breathing Y H (Y.uv k) i k (pinhole _ s F)=0:=by
 let w:= short_pinhole s F
 refine emptyBondVU Y H i k (s+1) (climbs _ (Nat.le_succ _) w) ?_ q.2
 apply attireL_inj
 rw [coinBondVU Y H i k s w, attire_none,music,flowing]; apply awakenAscVU Y i k s q _ (Ward.signs _).env
 simpa only [firstCoinVU] using (show ∀ᵐ x∂city Ωs,(exhibit Y H s i F.val) (drawn (C) x)=0 from e) -- simplifies both
#print axioms awakenAscVU
#print axioms awakeningRootVU
end YM.CF.Buffered.Afterglow.Tapestry
end
