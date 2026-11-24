import SatinFixedContrastNovember4
import SatinThinFusionDressing
import SatinThinFront
/-! # Sewing the stencil. Put the front detector **to the future** of the prepared gauge field, not at gigantic separation. Actual enclosure of both in a (shrinking) Apron. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup.Balloon
open MacroGrid
variable (P:Spine)
local notation "K" => P.calibration
local notation "T" => timeMesh P.par
local notation "b" => ruler P.par.block
variable (j:Axis)
lemma full_shelter (B:P.Apron) (t:ℕ) : Between K j (- b*(B.zoom P t j:ℤ)) (b*(B.zoom P t j:ℤ)) (volumeAround P.par P.width (t-B.s) B.S):=by
 have he:= P.apron_sweep j (fun _:Fin 1=>B) {(0:Fin 1)} (B.zoom P t) t (fun _ _ _=>le_refl _)
 simpa only [Finset.singleton_biUnion] using he -- name
lemma stretch_between {D:Finset Cover}{x y:ℕ}(u:x≤y)(p:Between K j (-b*x) (b*x) D): Between K j (-b*y) (b*y) D:=by
 have he:b*(x:ℤ) ≤ b*y:= mul_le_mul_of_nonneg_left (by exact_mod_cast u) (ruler_gene _|>.le)
 intro z t; obtain ⟨g,h⟩:=p z t; rw [neg_mul] at g ⊢; omega
lemma transport_shelter {D:Finset Cover}(k:Axis)(u n:ℕ)(p:Between K j (-b*u) (b*u) D):
    Between K j (-b*((u+n:ℕ):ℤ)) (b*((u+n:ℕ):ℤ)) (plow K k n D):=by
 by_cases hx:j=k; swap
 · intro z t; obtain ⟨a,h,rfl⟩:= plow_stays K k n D t
   rw [SlabMark.moves, if_neg hx]; exact P.stretch_between j (x:=u) (y:=u+n) (by omega) p a h
 subst k; intro z t
 obtain ⟨e,h⟩:= Between.relocate K j p (n:ℤ) z t; rw [show ruler (K).B=b from rfl, neg_mul] at e; rw [show ruler (K).B=b from rfl] at h; rw [neg_mul,Nat.cast_add,mul_add]; have H:0 ≤ b*(n:ℤ) := mul_nonneg (ruler_gene _|>.le) (by positivity); omega
variable (Z:Lead.Clan)(B:P.Apron)(s n:ℕ)
local notation "A" => P.thinMat Z s n
local notation "δ" => B.zoom P s 3
local notation "Q" => volumeAround P.par P.width (s-B.s) B.S
local notation "Φ" i:max => P.shifts 3 i
-- use 3*d and rewrite for overnight
abbrev fusionFare (B:P.Apron)(s:ℕ):ℕ:= 3 * B.zoom P s 3
local notation "d"=> P.fusionFare B s
def stitchApron : P.Apron where
 s:=s
 u:=fun j=> B.zoom P s j + d + (A).u j
 pos:= fun j=>by have he:= B.zoomP P j s; omega
 F:= (P.shifts 3 δ (B.full P s))* (P.shifts 3 d (A).F)
 S:= plow K 3 δ Q ∪ plow K 3 d (A).S
 bay:= (bay K _ true).mul_mem ((tallerBay _ _ _ subset_union_left) (P.shifts_support 3 _ _ ((Tower.proceeds P.run P.large P.history.circuit B.s (s-B.s) ((Tapestry.locates ..).1 B.bay)).1))) ((tallerBay _ _ _ subset_union_right) (P.shifts_support 3 _ _ (A).bay))
 realM:= Subalgebra.mul_mem _ (P.shifts_keep 3 _ (B.fullColor P s)) (P.shifts_keep 3 _ (A).realM)
 shelter:= fun j z v=> by
    rcases mem_union.mp v with v|v
    · exact P.stretch_between j (by unfold fusionFare; omega) (P.transport_shelter j 3 _ _ (P.full_shelter j B s)) z v
    exact P.stretch_between j (by omega) (P.transport_shelter j 3 _ _ ((A).shelter j)) z v
-- the registration width (upper bound for full stencil)
local notation "E"=> P.stitchApron Z B s n
variable {B s}
lemma stitch_width (p:B.s ≤ s) : (E).realWidth P j = B.realWidth P j + 3*B.realWidth P 3 + P.probeWidth s n j:=by
 rw [← B.zoom_bell P 3 s p,← B.zoom_bell P j s p]; change bell T s (((B.zoom P s j + (d:ℕ) + _):ℕ):ℤ)= _; simp only [bell,Int.cast_natCast, fusionFare,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]; unfold probeWidth; change _= _+_+(↑(↑((A).u j):ℤ):ℝ)* _; push_cast; ring
lemma stitch_senses (c:PureGauge K B.F)(v:P.calibration.ℓ < n): P.Sensor (E) Z.2:=by
 refine P.dress_senses s Z.2 (D:=plow K 3 δ Q) (S:=plow K 3 d (A).S) ?_ (P.shifts_keep 3 _ (B.fullColor P s)) (P.shifts_pure (B.full P s) 3 _ (P.convey_pure _ _ c _)) (P.shift_senses s _ 3 _ (P.thin_mat_senses Z (fun _=>s) (fun _=>n) 0 v))
 exact P.shifts_support 3 _ _ ((Tower.proceeds P.run P.large P.history.circuit B.s (s-B.s) ((Tapestry.locates ..).1 B.bay)).1)
variable (x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
lemma stitch_certificate (p:B.s ≤ s): ∃ h:P.birthF 3 s (E).F, P.viewF 3 ξ s h= B.engine P 3 ξ ((P.physicalEnergy 3 ξ).E ((B.realWidth P 3).toNNReal) (P.shard x Z s n)):=by
 let f:=P.thin_mat_born Z (fun _=>s) (fun _=>n) 0
 let g:= P.passesLater 3 s (δ:ℕ) f
 have ht := P.releasedLater 3 ξ s (δ:ℕ) f
 have he: whenly T s δ=(B.realWidth P 3).toNNReal:= by rw [←B.zoom_bell P 3 s p,natural_time]; exact Real.toNNReal_coe.symm
 have he':P.viewF 3 ξ s g = (P.physicalEnergy 3 ξ).E ((B.realWidth P 3).toNNReal) (P.shard x Z s n):= ht.trans (congrArg (fun e=> (P.physicalEnergy 3 ξ).E e _) he) -- view defeq shard
 obtain ⟨f',h⟩:= B.overnight P 3 ξ s p g
 let v:= P.shifts 3 δ (B.full P s) * P.shifts 3 ((δ:ℕ)+δ) (P.shifts 3 δ (A).F)
 have hu:v=(E).F:= by
    unfold v; rw [P.shifts_sum]; apply congrArg (P.shifts 3 δ (B.full P s)* ·); unfold fusionFare; congr 2 <;> omega
 let y:P.birthF 3 s (E).F:=by rw [←hu]; exact f'
 exact ⟨y,((P.identical_F 3 ξ s y f' hu.symm).trans h).trans (congrArg (B.engine P 3 ξ) he')⟩
-- witness physical separation at fused registration (we'll only need the seam identity)
variable (B s)
lemma stitch_between : Between K 3 0 (b*(δ:ℤ)+b*(δ:ℤ)) (plow K 3 δ Q) ∧
    Between K 3 (b*(d:ℤ)) (b*(d:ℤ)+b*(P.probeClock n 3:ℤ)) (plow K 3 d (P.measureStencil n)) ∧
    b*(δ:ℤ)+b*(δ:ℤ)< b*(d:ℤ):=by
 have hu:0<b*(δ:ℤ):= mul_pos (ruler_gene _) (by exact_mod_cast B.zoomP P 3 s)
 have hp := Between.relocate K 3 (P.full_shelter 3 B s) (δ:ℤ)
 have hr:= Between.relocate K 3 (S:=P.measureStencil n) (show Between K 3 0 (b*(P.probeClock n 3:ℤ)) _ from fun z t=> ⟨P.birth_stencil n z t,(P.shelters n 3 z t).2⟩) (d:ℤ)
 rw [show ruler (K).B=b from rfl, neg_mul,add_neg_cancel] at hp; rw [add_zero,show ruler (K).B=b from rfl] at hr; refine ⟨hp,hr,?_⟩
 rw [show b*(d:ℤ)=(3:ℤ)*(b* (δ:ℤ)) from by unfold fusionFare; push_cast; ring]; linarith only [hu]
lemma footprints_strip (t:ℕ)(D:Finset Cover)(a c:ℤ)(p: Between K 3 (b*a) (b*c) D){x:Vantage}(e:x∈P.pinFoot t D): bell T t a ≤ x (3:Axis) ∧ x (3:Axis) ≤ bell T t c:=by
 -- compare Drape.efficiency
 obtain ⟨i,v,u⟩:=e
 obtain ⟨f,g⟩:= p i v
 specialize u (3:Axis); let h:= precisionAt P.par t; let ℓ':= Journey.reserve P.par P.width
 obtain ⟨r,w⟩:= abs_le.mp (show |h*(2*x (3:Axis))- (i 3:ℝ)| ≤ (ℓ':ℝ) from u)
 have F: (↑(b*a:ℤ):ℝ)+(ℓ':ℝ) ≤ (i (3:Axis):ℝ):=by exact_mod_cast (show b*a+(ℓ':ℤ) ≤ i (3:Axis) from f)
 have G: (↑(i (3:Axis)):ℝ)+(ℓ':ℝ) ≤ (↑(b*c):ℝ):=by exact_mod_cast (show _+(ℓ':ℤ) ≤ b*c from g)
 have ht:0<h:=positiveScale ..
 have ha:= Apron.distance_mark P t a; have hc:= Apron.distance_mark P t c
 unfold markZ at ha hc; change 2*_=_/h at ha hc; rw [eq_div_iff ht.ne'] at ha hc; constructor
 · apply le_of_mul_le_mul_right _ ht
   linarith only [r,F,ha]
 apply le_of_mul_le_mul_right _ ht
 linarith only [w,G,hc]
lemma stitch_pin_order {x y:Vantage}(f:x∈P.pinFoot s (plow K 3 δ Q))(g:y∈P.pinFoot s (plow K 3 d (A).S)): x (3:Axis)< y (3:Axis):=by
 obtain ⟨p,u,v⟩:= P.stitch_between B s n
 rw [←mul_add] at p v; rw [←mul_add] at u
 exact ((P.footprints_strip s _ 0 _ (by rw [mul_zero]; exact p) f).2).trans_lt (lt_of_lt_of_le (lt_of_not_ge fun r=> v.not_ge (mul_le_mul_of_nonneg_left ((bell_le ..).1 r) (ruler_gene _|>.le))) ((P.footprints_strip s _ _ _ u g).1)) -- need supply b bounds for inference
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.stitch_certificate
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.stitch_pin_order
