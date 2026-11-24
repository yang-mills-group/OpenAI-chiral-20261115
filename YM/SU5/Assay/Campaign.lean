import SatinFixedContrastNovember4
import YM.SU5.Assay.Tickets
import YM.SU5.Assay.Entrance
import YM.SU5.Assay.Flock
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set Casting Six Ballad Cordial Prototype
variable (P:Spine)(R:P.Register)(c r:ℕ→ℕ)(x:P.Spectrum0 3)
/-!
 Always reapply the experiment on the election actually used; not trying
 to reinstall a ledger or infer a uid for votes on different courses. Same
 launch and coupling qualification, same history and register; even the
 FLASH WIRE can then be kept, n in the new stock charges identical to
 the chosen (henceforth fixed) old n, at every new billed height.
-/
structure Strategy :Prop where
 elect: ∃J:P.Ellis 3 x,P.Experiment R c r x J
 powers:P.Transmission x c r
 host:P.Roster
 reserves:Tasting.Paid P.par
 medals:∀ a:ℝ,0<a→∀ᶠ n:ℕ in atTop, ∃ M:P.Menagerie,P.Company n M a
-- used also with supplemental requirements on P.par in Admission
lemma survey_purchase {Lux:Preparation→Prop}(u:Admission Lux)(Y:Supplier)(L B:ℝ)(p:0<B)(z:ℕ→ℕ):
 ∃(P:Spine)(R:P.Register), uniform P R Y L B ∧ Lux P.par ∧ ∃ (c r:ℕ→ℕ)(x:P.Spectrum0 3), z≤r ∧ P.Strategy R c r x:=by
 obtain ⟨P,R,h,l,g,d,c,r,x,q,J,i,k⟩:=macro_with u Y _ _ p z
 exact ⟨P,R,h,g,_,_,_,q,⟨J,i⟩,k,l,d,fun _ t=>funded_company h d t⟩

variable (s n:ℕ)(D N:Doorway)(σ:Orders)
local notation "o"=>D.turnCut N
local notation "w"=>P.probeWidth s n
structure Taps :Prop where
 sep:D.Later N σ 0
 extent:P.calibration.ℓ<n
 axis:D.Later N σ (w)
 left:D.Stash w
 right:N.Stash w
 opens:P.AllOpens x s n D N σ
 inside:P.AllOpens x s n D.spare N.spare σ
 bills:∀ t≥s, P.Tickets D t ∧ P.Tickets N t

/-- `P.Fresco`: commitments to the original pose experiment bills; cuts
 explicit mid and box endpoints. Budget even for caliper receipts over
 the smaller claim of **space** inside invitations. In particular retains
 EVERY requirement of `reviewTwoFixedProbes` for those specific doors.
-/
structure Fresco (F G:SampleDose):Prop where
 taps : P.Taps x s n D N σ
 oil : F.Normalized
 water : G.Normalized
 fixed1:tsupport F.val ⊆ D.spare.invites
 fixed2:tsupport G.val ⊆ N.spare.invites
 paid:P.ReturnsSix x s n o F G
 verified:P.FixedSatinReadings R x s n o F G

variable {s n x D N σ c r P R}
lemma Strategy.launch (P₀:P.Strategy R c r x):Launch P c r:=let ⟨_,v⟩:=P₀.elect;v.launch
lemma Strategy.offer (P₀:P.Strategy R c r x) {a:ℝ}(p:0<a):
 ∀ᶠ i in atTop, ∃M:P.Menagerie,P.Company (r i) M a:=P₀.launch.eager.tendsto_atTop.eventually (P₀.medals _ p)
lemma Strategy.reaches (P₀:P.Strategy R c r x)(t:D.Later N σ 0):
 ∀ᶠ i in atTop,P.Taps x (c i) (r i) D N σ:=by
 obtain ⟨b,p⟩:=P₀.elect
 have hx:=P₀.powers
 have u:=p.launch
 obtain ⟨k,h⟩:= eventually_atTop.mp ((Tickets.late P D).and (Tickets.late P N))
 filter_upwards [atDoors p,hx.prescribe D N _ t,Doorway.Stash.receive D hx.widths,Doorway.Stash.receive N hx.widths,
   u.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ),u.smaller.tendsto_atTop.eventually (eventually_ge_atTop k)] with i I H f g e l
 exact ⟨t,e,H,f,g,I _ _ _ H,I _ _ _ (D.spareLater H),fun _ y=> h _ (l.trans y)⟩

variable {F G:SampleDose}
lemma Taps.portrait (P₀:P.Taps x s n D N σ)(R:P.Register)(J:P.Ellis 3 x)
 (e:F.Normalized)(r:G.Normalized)(f:tsupport F.val ⊆D.spare.invites)(g:tsupport G.val ⊆N.spare.invites){b:ℝ}(q:P.ReturnsSix x s n b F G):P.Fresco R x s n D N σ F G:=by
 have t:Walled 3 F (D.lower 3) o ((w) 3):=Doorway.first P₀.left f P₀.sep
 have u:Walled 3 G o (N.upper 3) ((w) 3):=Doorway.second P₀.right g P₀.sep
 have ht:∀Z,P.WallBefore (P.RTest Z s n) F o:=fun _=> Walled.WallBefore t
 have hu:∀Z,P.WallAfter (P.FTest Z s n) G o:=fun _=> Walled.WallAfter u
 have hg:= tendsto_nhds_unique q.steady (P.answersTogether x s n o J F G ht hu)
 have m:=P.paidReturn x s n o F G ht hu J ((congrArg ReadsSix hg).mp q.poles) P₀.extent
 exact ⟨P₀,e,r,f,g,m,P.reviewWardContrast R _ _ _ _ _ _ m⟩
lemma Taps.paints (P₀:P.Taps x s n D N σ)(R:P.Register)(J:P.Ellis 3 x):∃F G,P.Fresco R x s n D N σ F G:=by
 obtain ⟨b,h,g,⟨F,G,e,r,k,u,v⟩,_⟩:=P₀.inside.reading
 exact ⟨F,G,P₀.portrait R J e r k u v⟩
lemma Strategy.exposes (P₀:P.Strategy R c r x)(v:P.Taps x s n D N σ): ∃F G,P.Fresco R x s n D N σ F G:=
 v.paints R P₀.elect.choose

-- For every earlier experiment we shall fix under the strategy.
namespace Fresco
variable (v:P.Fresco R x s n D N σ F G)
include v
lemma first : tsupport F.val ⊆ D.invites:= v.fixed1.trans (subset_closure.trans D.sparesDoor)
lemma second : tsupport G.val ⊆ N.invites:= v.fixed2.trans (subset_closure.trans N.sparesDoor)
lemma owns (Z:Lead.Clan):P.spacePrice (P.RTest Z s n) F⊆ D.invites ∧ P.spacePrice (P.FTest Z s n) G⊆ N.invites:=
  -- ∪ footprint budgets inside, use shelf stepOut
 ⟨bounded_within _ _ v.fixed1 (by
    intro j; change _+(w) j<_ ∧ _+(w) j<_
    have h:=v.taps.left j; simp only [Doorway.spare,Doorway.changeDue] at h ⊢;constructor <;> linarith only [h,D.clearance j]),
  bounded_within _ _ v.fixed2 (by
    intro j; change _+(w) j<_ ∧ _+(w) j<_
    have h:=v.taps.right j; simp only [Doorway.spare,Doorway.changeDue] at h ⊢;constructor <;> linarith only [h,N.clearance j])⟩
end Fresco
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
