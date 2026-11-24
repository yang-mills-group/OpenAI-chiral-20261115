import YM.CF.DPress.Yarn.Table
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
open Chaff Gloss Maize Tye RP RP.Str Brace
open Source
variable {T : Source P_ J}{Jp:ℕ→ℝ→ℝ}
variable (p:Workshop T Λ Jp x)
-- table notation k bottom of table, i-k = index. sizes.
structure Beacon (T:Source P_ J)(F:RoomF J Λ M Δ)(n:ℕ)(Jp:ℕ→ℝ→ℝ)(k:ℕ): Prop where
 h : n=k+(T.b+1)
 ok : Workshop T Λ Jp x
variable (hk:Beacon T F n Jp k)
abbrev εM(j:ℕ)(x:ℝ):=Jp (j-k) x
abbrev need(j:ℕ)(v:LogH (cell M B R.L j)):Prop:= D.stipend_h j v (Jp (j-k) (hat R.L x j)) (Source.rank (j-k))
local notation "μ@"=> Jp
local notation "ht'"=>hat R.L x
include D hk
lemma funding(v:i<n)(p:k ≤ i) :∃ (r:ℝ),0 < r∧(i ≠ k → r = 1) ∧ Duty V C.w C.p C.i (Ntop P_) J C.q' C.h (jS i) (apt M B R.L i) (ht' i) r (grant_B R.L (ht' i)) (Jp (i-k) (ht' i)) (Jp (i+1-k) (ht' i)) 0 (Source.rank (i-k)) (Source.rank (i+1-k)):=by
 have hp:i-k<T.b+1:=by have hv:= hk.h; omega
 obtain ⟨r,b,c,h⟩:= (hk.ok _ (F.time (i:=i))).1.move (⟨i-k,hp⟩); refine ⟨r,b,fun t=>c (by change i-k≠0; omega),?_⟩; rw [show i+1-k=i-k+1 from (by omega)]; exact h (jS i) _
def radiusX (i:ℕ) := if h:k ≤ i∧i<n then Classical.choose (funding D hk h.2 h.1) else (1:ℝ) -- include p in def? hk
lemma borrow(v:k ≤ i∧ i<n):let r:= D.radiusX hk i; 0 < r∧(i ≠ k → r = 1) ∧ Duty V C.w C.p C.i (Ntop P_) J C.q' C.h (jS i) (apt M B R.L i) (ht' i) r (grant_B R.L (ht' i)) (Jp (i-k) (ht' i)) (Jp (i+1-k) (ht' i)) 0 (Source.rank (i-k)) (Source.rank (i+1-k)):=by dsimp only [radiusX]; rw [dif_pos v]; exact Classical.choose_spec (funding D hk v.2 v.1)
lemma borrow_r : 0< D.radiusX hk i:=by by_cases h:k ≤ i∧ i<n; exact (D.borrow hk h).1; rw [radiusX,dif_neg h]; norm_num
lemma alphaP0(i:ℕ)(v:i≤T.b+1) :0 ≤ Jp i (ht' j) := ((hk.ok _ (F.time (i:=j))).1.wage i v).1
lemma higher {l:ℕ}(z:i≤j)(v:l≤T.b+1) : Jp l (ht' j)≤Jp l (ht' i):=((hk.ok _ (F.time (i:=i))).1.wage l v).2 _ (F.age i z) -- add {l}
omit hk D
private lemma adaptL0 (m B ηL:Side)(k:ℕ)(v:B=ηL^k)(s:Sweep (CSide m B))(p:ply_U ηL k s):Chaff.LabelB m B s:=by subst B; exact ply_J _ _ s p
abbrev Lendc(A: Source P_ J)(Z:RegBudget (cell M B R.L n))(v:ℝ) :Prop:= Lives_B (H:=C.h) V (A.F0 (mesh M R.L n)) Z (radiusB (hat R.L x n)) (A.KFp (hat R.L x n)) (Δ.a n) (F.Y n) U v
abbrev νhead (A:RegBudget (cell M B R.L n))(z:ℝ) : LogH (cell M B R.L n):= ⟨⟨A,0⟩,0,0,z⟩
include D in
lemma χtop (A:RegBudget (cell M B R.L n))(z:ℝ)(b:ℝ) : D.render n (νhead (M:=M) (n:=n) (B:=B) (R:=R) A z) b=Chaff.fulvia A z (Vale.launch V.L b (Δ.a n) (cell M B R.L n)):=by rw [render,venue, hue_top]; rfl -- tune
include D hk
lemma urn :∃ (A: RegBudget (cell M B R.L n))(z:ℝ), Lendc (F:=F) (n:=n) T A z∧ need (k:=k) (Jp:=Jp) D n (νhead (M:=M) (B:=B) (R:=R) (n:=n) A z) :=by
 let x0:= hat R.L x n; let X:= Δ.a n; let m:=mesh M R.L n; let Φ:= (hk.ok x0 (crown ..)); have hp:= Δ.boot n; obtain ⟨z,E,w⟩:= Φ.1.boot m X (F.Y n) (F.rocket _).paid ⟨hp.2.2.2.1,hp.2.2.2.2,hp.1,hp.2.1,hp.2.2.1⟩ (J.gran.trans (F.rocket _).size) ((hp.2.1).symm ▸ Φ.1.smallest) (F.bloom.pose _) (by
     have he:100*(1+X.B)≤ (Domain m B).val:=by rw [show X.B=radiusB (ht' n) from hp.2.1]; exact (Δ.clear F.legal 0 n).1.size
     omega)
 refine ⟨E,z,w,?_⟩; have ht:= hk.h; have hB:T.KFp x0 ≤ Jp (T.b+1) (ht' n):=Φ.1.useF; unfold need; rw [show n-k=T.b+1 from by omega]; let P:LogH (cell M B R.L n):=νhead (M:=M) (B:=B) (R:=R) (n:=n) E z; have hg :=w.weight; have hv:IncX (LabelB m B) E (Xt n).p C.h (Jp (T.b+1) x0):=Provides.liftE C.h (Xt n) _ _ hg hB; have hp:0≤ Jp (T.b+1) x0:= ((Φ.1.wage (T.b+1) le_rfl).1)
 change Provides R.L K.j (render D n P 1) C.h _ (some T.b); exact ⟨⟨hv.weight,fun s v=> hv.face s (adaptL0 m B R.L T.b T.pov s v)⟩,rfl,Provides.liftQ C.h (Xt n) _ _ (Vale.lye (ply_U R.L T.b) _ _).2 hp⟩ -- tune : ply namespaces
end Crib
end FitD
end YM.CF.Py.Kay
