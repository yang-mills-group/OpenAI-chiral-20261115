import YM.SU5.Hiro.Choux
/-!
# fully spread in the new apparatus. Even though support uses plaquette at time 0 coord, apertures measured with resolution s ground policy. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 260000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Hiro Ballad Papal Regis.Head Regis.Head.Brecht
open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Morn
open Germ Alliance Aria
namespace Spine
variable (P:Spine) (n s:ℕ)
local notation "K"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "F"=> Prototype.goldF
local notation "δ"=> ruler P.par.block
private def chartFee(L:List Axis)(a:Cover)(X:Finset Cover): Finset Cover:= L.foldr (fun i=> plow K i (a i)) X
lemma charterSupport (q:Bool)(L:List Axis)(a:Cover)(f:P.Test){V:Finset Cover}(v:f∈bay K V q): P.cruise L a f ∈ bay K (chartFee P L a V) q:=by induction L with
 | nil=> exact v
 | cons i L h=> rw [P.cruise_step,AlgHom.comp_apply]; change _ ∈ bay K (plow K i (a i) (chartFee P L a V)) q; exact P.shifts_support i (a i) _ h
lemma charterSize (L:List Axis)(a:Cover)(e:L.Nodup)(f:Finset Cover)(p:Cover)(v:p∈chartFee P L a f):∀ j:Axis,∃ z∈f,p j=z j+if j∈L then δ*a j else 0:=by
 intro i; induction L generalizing p with
 | nil=>exact ⟨p,v,by simp⟩
 | cons j L h=>
   obtain ⟨k,g,rfl⟩:=plow_stays K j (a j) (chartFee P L a f) v; obtain ⟨t,hV,p⟩:= h (List.nodup_cons.mp e).2 _ g; refine ⟨t,hV,?_⟩; rw [SlabMark.moves,p]; by_cases v:i=j; · subst j; simp [show ruler (K).B=δ from rfl,(List.nodup_cons.mp e).1]
   simp [v] -- left
private lemma cruise0 (f:P.Test) : P.chartAll 0 f=f:=Subtype.ext ((P.followsChart ..).trans (Vacancy.cad_zero _ _ ((marque ..).1 f.property))) -- width defeq
local notation "X" r:max => δ • r
local notation "Ξ" r:max=> platePin F (nodeC (r))
lemma plate_bound (x:Cover) (v: Cover)(p:v∈ platePin F x)(i:Axis): x i-1≤v i ∧ v i≤ x i+3:=by
 simp [platePin,Lattice.visits,Lattice.square] at p; rcases p with h|h|h|h|h <;> rw [h] <;> first | (fin_cases i <;> norm_num [Prototype.goldF] <;> omega) | omega
variable (a:Cover)(f:P.Test)
local notation "μ"=> P.platterWidth
lemma chouxSize(x:Cover)(v:x∈ chartFee P Vacancy.ordinate (-(2 • a)) (Ξ (X a))) (i:Axis) : -δ*(μ:ℤ)+ℓ ≤ x i∧ x i + (ℓ:ℤ) ≤ δ*(μ:ℤ):=by
 obtain ⟨k,p,s⟩:= P.charterSize Vacancy.ordinate (-(2 • a)) Vacancy.ordinate_one (Ξ (X a)) _ v i; obtain ⟨e,t⟩:=plate_bound (nodeC (X a)) k p i; rw [s, if_pos (Vacancy.ordinates i)]; rw [show (-(2 • a):Cover) i = -(2*a i) from (by simp [Pi.smul_apply])]; have he:i∈Vacancy.ordinate:= Vacancy.ordinates i; have hp:nodeC (X a) i=2*(δ*a i)+1:=by simp [nodeC]; -- tune syntax macro
 rw [hp] at e t; rw [neg_mul]; have ht:1≤δ:=ruler_gene _; have hh:0≤ (ℓ:ℤ):=by positivity
 change -(δ*(P.platterWidth:ℤ)) + _ ≤ _ ∧ _ + _ ≤ _
 unfold platterWidth; push_cast; constructor <;> nlinarith only [ht,hh,t,e,mul_le_mul_of_nonneg_right ht hh]
lemma pasture(f:P.Test)(v:f∈ bay K (Ξ (X a)) false)(u:f∈enclave K):∃ D:P.Apron,D.s=s∧ (∀ i,D.u i=P.platterWidth)∧P.chartAll (2 • a) (D.full P s)=f:=by
 let p:=2 • a; let q:=P.chartAll (-p) f; let D:P.Apron:= ⟨s,fun _=>P.platterWidth,fun _=>by unfold platterWidth; omega,q,chartFee P Vacancy.ordinate (-p) (Ξ (X a)), P.charterSupport true Vacancy.ordinate (-p) f (widerBay K _ _ v),P.cruise_color Vacancy.ordinate (-p) u,fun i v h=> chouxSize P a v h i⟩; refine ⟨D,rfl,fun i=>rfl,?_⟩; change P.chartAll p (P.conveying _ _ q)=_; change P.chartAll p (P.conveying s (s-s) q)=_; rw [Nat.sub_self] -- fix
 have h: P.chartAll p q=f:=by unfold q; rw [P.chart_ids,add_neg_cancel,P.cruise0] -- private
 exact h
local notation "δP"=> P.rangeClasp n
local notation "Pe"=> P.rosemary n
local notation "Zs"=> (timeMesh P.par)
variable {k:ℝ}(p:0<k)
local notation "φ"=>P.jade pairMood n F (δP) p s
local notation "ψ"=>P.jade pairMood n F 0 p s
noncomputable def parsley : P.Apron:= (P.pasture s (Pe) (φ) (P.proper_own pairMood n F δP p s).1 (P.proper_own pairMood n F δP p s).2).choose
private lemma offFee(P:Spine): platePin F (nodeC ((ruler P.par.block) • (0:Cover)))= platePin F (nodeC 0):=by rw [smul_zero]; -- horizon
lemma off_pose: ∃ D:P.Apron,D.s=s∧(∀ i,D.u i=P.platterWidth)∧ P.chartAll 0 (D.full P s)= (ψ):=by
 obtain ⟨D,x,e,u⟩:= P.pasture s 0 (ψ) (by rw [offFee P]; exact (P.proper_own pairMood n F 0 p s).1) (P.proper_own pairMood n F 0 p s).2; exact ⟨D,x,e,(by simpa only [smul_zero] using u)⟩
noncomputable def aloe : P.Apron := (P.off_pose n s p).choose
def seatingFlag : Bool→ Cover:= fun i=> if i then 2 • (Pe) else 0
noncomputable def listing : Bool→ P.Apron := fun i=> if i then P.parsley n s p else P.aloe n s p -- variable order
protected abbrev placed : Bool→ Vantage:= P.laysM ∘ (P.vtile s ∘ P.seatingFlag n)
lemma listing_bills (i:Bool): let r:=P.listing n s p i; r.s=s∧ (∀ i,r.u i=P.platterWidth) ∧ P.chartAll (P.seatingFlag n i) (r.full P s)=(if i then φ else ψ):=by
 intro r; cases i
 · exact (P.off_pose n s p).choose_spec
 exact (P.pasture s (Pe) φ (P.proper_own pairMood n F δP p s).1 (P.proper_own pairMood n F δP p s).2).choose_spec
lemma theater_rank(i:Axis): P.resignY i (P.listing n s p) (P.placed n s) false < P.porchY i (P.listing n s p) (P.placed n s) true:=by
 let A:=P.listing n s p; let Q := P.seatingFlag n; let H:=P.placed n s
 let t:=bell Zs s; have he(v:Bool): (A v).zoom P s i=P.platterWidth:=by unfold Apron.zoom; rw [(P.listing_bills n s p v).1, (P.listing_bills n s p v).2.1 i]; simp
 rw [←P.begins i A Q s true (P.listing_bills n s p true).1.le,←P.endsAt i A Q s false (P.listing_bills n s p false).1.le]; apply lt_of_not_ge; intro u; have ht:= (bell_le Zs s _ _).1 u; change (Q true i:ℤ)-(A true).zoom P s i ≤ Q false i + ↑((A false).zoom P s i) at ht; rw [he, he, show Q true i=2*(Pe) i from ?_, show Q false i=0 from rfl] at ht; swap; · simp [Q,seatingFlag]; -- tune
 have hv:=P.rosemary_hi n i; unfold platterWidth at *; omega
lemma theater_stile (i:Axis): P.Turnstile i (P.listing n s p) [false,true] (P.placed n s):=List.pairwise_pair.mpr (P.theater_rank ..)
lemma theater_world : P.Plenum (P.listing n s p) [false,true] (P.placed n s):= ⟨fun i=> ⟨_,List.Perm.refl _, P.theater_stile n s p i⟩⟩
lemma theater_price : P.fullScroll s (P.listing n s p) (P.seatingFlag n) [false,true]=φ*ψ:=by change P.chartAll (P.seatingFlag n false) _ *(P.chartAll (P.seatingFlag n true) _*1) = _; rw [(P.listing_bills n s p false).2.2, (P.listing_bills n s p true).2.2,mul_one]; exact mul_comm _ _
-- visibility on these actual disjoint physical supports (spaced in spacetime). Continuum metric.
abbrev plotSpace (i:Bool): Set RSpace := (P.listing n s p i).scenery P (P.placed n s i)
lemma theater_visible (U':P.Register) (i:Bool): let D:= if i then φ else ψ; D ∈ keep P.par P.width s K true (P.plotSpace n s p i):=by
 intro d; let L:=P.listing n s p i; change d ∈ _; rw [show d =P.chartAll _ _ from (P.listing_bills n s p i).2.2.symm]; exact P.calibrated_location s L (P.seatingFlag n i) U' (P.listing_bills n s p i).1.le
lemma theater_printed(i:Bool) : let v:=if i then δP else 0; printedHere P.par P.width s (platePin F (nodeC v)) (P.plotSpace n s p i):=by -- also actual footprints; through shifts real
 intro v x u y l j; let t:=P.placed n s i; let r:= P.seatingFlag n i
 let f:= precisionAt P.par s; have hp:0<f:=positiveScale ..; have h0: 1 ≤ (δ:ℤ):=ruler_gene _; have he(i':Axis): 2*(t i')=markZ P.par s (δ*r i'):=Apron.distance_mark P s _; let D:=P.listing n s p i; have ht: 2*D.realWidth P j= markZ P.par s (δ*P.platterWidth):=by unfold Apron.realWidth; rw [(P.listing_bills n s p i).1, (P.listing_bills n s p i).2.1 j]; exact Apron.distance_mark P s _;
 obtain ⟨hx,hy⟩:= abs_le.mp (l j); obtain ⟨hz,h⟩:= plate_bound (nodeC v) x u j; have hB: nodeC v j= δ*r j+1:=by cases i<;> simp [v,r,seatingFlag,rangeClasp,nodeC]; try ring
 rw [hB] at hz h; change -↑(ℓ) ≤ f*y j-_ at hx; change f*y j-_ ≤ ↑(ℓ) at hy; have ha: (δ:ℤ)*r j - (δ:ℤ)*P.platterWidth+ℓ ≤ x j:= by unfold platterWidth; push_cast; nlinarith only [h0,hz, show 0 ≤ ((δ:ℤ)-1)*↑(ℓ) from (by positivity)];
 have hb:x j+(ℓ:ℤ) ≤ (δ:ℤ)*r j+ (δ:ℤ)*P.platterWidth:= by unfold platterWidth; push_cast; nlinarith only [h0,h, show 0≤ ((δ:ℤ)-1)*↑(ℓ) from (by positivity)]
 change |y j-2*t j|≤_; rw [he, show 2*(P.listing n s p i).realWidth P j=_ from ht,markZ,markZ,abs_le]
 have ha': (((δ)*r j:ℤ):ℝ)-↑(δ*(μ:ℕ))+(ℓ:ℝ) ≤ (x j:ℝ):=by exact_mod_cast ha
 have hb': (x j:ℝ)+(ℓ:ℝ) ≤ (((δ)*r j:ℤ):ℝ)+↑(δ*(μ:ℕ)):= by exact_mod_cast hb
 constructor <;> (field_simp [positiveScale] ; nlinarith only [ha',hb',hx,hy])
lemma theater_disjoint : Disjoint (P.plotSpace n s p false) (P.plotSpace n s p true):=P.separated_keeps 3 (P.listing n s p) (P.placed n s) false true (P.theater_rank ..)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.pasture
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.theater_visible
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.theater_price
