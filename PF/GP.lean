import PF.Sensor
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

-- Physical gating on a single LP satellite
namespace PureForce.GP
open BPress Push.Local AnalyticBridge.VerifiedReset Push.AbsoluteSums Work.F03
variable {N n : Side}
local notation "G" => SU.group
-- old to new. direct clipping branch stability from flags gate; no global tie charges.
variable {U V : Config G n}
structure Toggle (e : Edge (Site n))(τ δ:ℝ)(U V: Config G n): Prop where
  off : ∀ i≠e, V i=U i
  cost : ∀ i, BPress.chord (V i) (U i) ≤ δ
  decisions : ∀ p:Face (Per n), ∀ r:ℝ, τ≤r→ (SU.group.chord (faceValue V p) ≤ r ↔ SU.group.chord (faceValue U p) ≤ r)
  old  : ∀ p:Face (Per n), e.1∈RG.touched p→ SU.group.chord (faceValue U p) ≤ τ
variable {e : Edge (Site n)}{τ δ : ℝ}(H:Toggle e τ δ U V)
include H
lemma Toggle.healthy (s:Signed)(x:Site n)(S:Support n) : Healthy τ S (Lattice.pull s x U) ↔ Healthy τ S (Lattice.pull s x V):= by
  rw [←healthy_pull, ←healthy_pull]
  have hf: RG.flags τ U= RG.flags τ V:=by
    ext i; rw [flags_spec, flags_spec]; exact exists_congr fun p=> and_congr_right fun _=>
      lt_iff_lt_of_le_iff_le ((H.decisions p τ le_rfl).symm)
  simp only [Healthy,hf]
lemma Toggle.pulled (s:Signed)(x:Site n) : ∀ i, BPress.chord ((Lattice.pull s x V) i) ((Lattice.pull s x U) i) ≤ δ:=by
  rintro ⟨y,j⟩; unfold Lattice.pull
  cases hv : Lattice.Step.rotate (posDir j) s with| mk i t => cases t; exact H.cost _; exact le_trans (chord.inv ..).le (H.cost _)
lemma Toggle.keeps (s:Signed)(x:Site n)(c:RG.Clip)(g:0≤τ)(y:Site n): PathData.kept c τ y (Lattice.pull s x V) ↔ PathData.kept c τ y (Lattice.pull s x U) := by
  unfold RG.PathData.kept; refine forall_congr' ?_; intro p
  simp_rw [Face.send_price _ p s x (Gauge.chord G) SU.group.chord_inv (fun k h=>SU.group.chord_conj h k)]
  exact H.decisions _ _ (le_mul_of_one_le_right g (Real.one_le_exp (div_nonneg (by positivity) c.radius_pos.le)))
omit H
/-- full-length cost of a slot via chord (no small path on old transport needed, unitary LP instead); use path of double material length going back to root -/
lemma slot_cost (δ:ℝ)(c:∀ i,BPress.chord (V i) (U i) ≤δ) (l:RG.Slot) (o:Site n)(p:0 ≤ δ) :
    ‖l.atSite V o - l.atSite U o‖ ≤ 2 * (l.length:ℝ)*δ:=by
  simp_rw [atSite_path, ←SU.group.curvature_conjugate]
  refine (Spin.curv_diff ..).trans ?_
  let w(A:Config G n):=Lattice.travel A o l.walk
  let f(A:Config G n):=faceValue A (slotFace l o)
  have ht:BPress.chord (w V) (w U) ≤ l.walk.length*δ:=chord.path V U _ _ _ (fun i _ _=>c i)
  have hf:BPress.chord (f V) (f U) ≤ 4*δ:=chord.face V U _ _ (fun i _ _=>c i)
  refine (chord.product (w V*f V) (w U*f U) (w V)⁻¹ (w U)⁻¹).trans ((add_le_add ((chord.product ..).trans (add_le_add ht hf)) (by simpa only [chord.inv] using ht)).trans ?_)
  unfold RG.Slot.length; push_cast; linarith
variable {R:PathData G}{c:Clip}{p:BudgetPoint}
open BPress.Wealth
/-- supports of clipped-price & pair terms excluding kept data. -/
def lowerSeat (R:PathData G)(d:Low)(o:Site n) := d.2.elim (fun _=> RG.touched (o,d.1)) (fun j=> Paths.bundle o (Paths.duplex R d.1 j))

section
variable (R)(d:Low)
lemma lowerShape (o:Site n): o∈lowerSeat R d o ∧ Branch.Grove (Grid.field 4 n) (lowerSeat R d o) ∧
    lowerSeat R d o ⊆ halo (8+d.length R) {o} ∧ (lowerSeat R d o).card ≤ d.length R+8:=by
  unfold lowerSeat Low.length; cases h:d.2 with
  | inl _ =>
    dsimp only [Sum.elim_inl]; obtain ⟨ha,hb,hc⟩:= touched_limit (o,d.1); refine ⟨ha,hb,hc.trans (Corona.halo_mono (by norm_num) (Finset.Subset.refl _)), (walks_n o (square d.1.val.1 d.1.val.2)).trans (by simp [square])⟩ -- definitional touches?
  | inr j=>
    dsimp only [Sum.elim_inr]; let A:= Paths.duplex R d.1 j; obtain ⟨ha,hb,hc⟩:=bundle_limit o A; have he :Paths.length A=(d.left R j).length+(d.right R j).length:= Paths.duplex_price R d.1 j; rw [he] at hc; refine ⟨ha,hb,fun i ht=> halo_spec.mpr ⟨o,mem_singleton_self _,?_⟩,by change (Paths.bundle o A).card ≤ _; omega⟩; exact (Paths.where_slot o A i ht).trans (he.le.trans (Nat.le_add_left ..))
end
-- if U,V equal on this (no kept) support and pass the same gates, live is equal.
lemma lowLocal {d:Low}{o:Site n}(h:Agrees (lowerSeat R d o) V U)(t:PathData.kept c p.threshold o V ↔ PathData.kept c p.threshold o U):
    d.live R c p o V = d.live R c p o U:=by
  unfold Low.live; cases z:d.2 with
  | inl _ => exact congrArg (fun u=> PathData.clipped c p.threshold (SU.group.chord u)) (WilsonStartup.face_local _ _ _ (by simpa only [lowerSeat,z,Sum.elim_inl] using h))
  | inr j =>
    dsimp only [Sum.elim_inr]; simp_rw [propext t]; congr! 1 -- try
    let A:=Paths.duplex R d.1 j
    have hh (i:Fin 2) : (A i).atSite V o=(A i).atSite U o := slot_reads _ _ V U
      (agrees_mono h (Finset.coe_subset.mpr (show BPress.Wealth.foot o (A i) ⊆ lowerSeat R d o from by unfold lowerSeat; rw [z]; intro x hx; exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩))))
    unfold Low.plain; rw [z,Sum.elim_inr]
    have hl: A 0=d.left R j:=rfl; have hr:A 1=d.right R j:=rfl
    simp_rw [←hl,←hr,hh 0,hh 1]
    rfl
private lemma abs_diff_price {s t:ℝ} {h k:ℝ}(hs:0 ≤ s)(ht:0 ≤ t)(hu:s ≤ h)(hv:t ≤ h)(w:|s-t| ≤ k): |s^2-t^2| ≤ 2*h*k:=by
  rw [show s^2-t^2=(s+t)*(s-t) by ring,abs_mul,abs_of_nonneg (add_nonneg hs ht)]
  exact mul_le_mul (by linarith) w (abs_nonneg _) (by linarith)
private lemma ch_dist (u v:SU.E): |SU.group.chord u-SU.group.chord v|≤ BPress.chord u v := by
  apply abs_le.mpr
  simpa only [chord.one,chord.comm v u] using (show -BPress.chord u v ≤ BPress.chord u 1-BPress.chord v 1 ∧ BPress.chord u 1-BPress.chord v 1 ≤ BPress.chord u v by
    have hu:= chord.triangle u v 1; have hv:=chord.triangle v u 1; rw [chord.comm v u] at hv; constructor<;>linarith only [hu,hv])
-- clipping discontinuity: you only get this after funding the flags
lemma directUnit (f:Face (Per n))(H:Toggle e τ δ U V)(c:Clip)(t:0≤τ) :
    |PathData.clipped c τ (SU.group.chord (faceValue V f))-PathData.clipped c τ (SU.group.chord (faceValue U f))| ≤
    c.direct * τ * (4 * δ):=by
  by_cases he:e.1∈ RG.touched f
  · have hs:=H.old f he; have ht:=(H.decisions f τ le_rfl).2 hs
    simp only [PathData.clipped, ht, hs, ↓reduceIte] -- c in simp???
    have hv:=abs_diff_price (SU.group.chord_nonneg _) (SU.group.chord_nonneg _) ht hs
      ((ch_dist (faceValue V f) (faceValue U f)).trans (chord.face V U f δ (fun i _ _=> H.cost _)))
    rw [←sub_div, ←mul_sub,abs_div,abs_mul,abs_of_pos c.quadratic_pos,abs_of_pos (by norm_num:(0:ℝ)<2)]
    linarith only [mul_le_mul_of_nonneg_left hv c.quadratic_pos.le]
  rw [show faceValue V f=faceValue U f from WilsonStartup.face_local _ _ _ fun i h _=> H.off i (by rintro rfl; exact he h),sub_self,abs_zero]; have w:0 ≤ δ:=(chord.positive ..).trans (H.cost e); have :=c.quadratic_pos; positivity
private lemma dotCost (u v i j : SU.group.Color)(a b:ℝ){Y:ℝ}(he:‖u-i‖≤a)(hh:‖v-j‖ ≤ b)(hv:‖i‖ ≤ Y)(hp:‖v‖ ≤Y)(_:0 ≤ b):
    |inner ℝ u v-inner ℝ i j| ≤ Y*(a+b):=by
  rw [show inner ℝ u v-inner ℝ i j=inner ℝ (u-i) v + inner ℝ i (v-j) by rw [inner_sub_left,inner_sub_right]; ring]
  exact (abs_add_le ..).trans ((add_le_add ((abs_real_inner_le_norm ..).trans (mul_le_mul he hp (norm_nonneg _) ((norm_nonneg _).trans he))) ((abs_real_inner_le_norm ..).trans (mul_le_mul hv hh (norm_nonneg _) ((norm_nonneg _).trans hv)))).trans_eq (by ring))

variable {T:ℝ}
lemma lowSense (o:Site n)(d:Low)(s:Signed)(x:Site n)(H:Toggle e p.threshold δ U V):
    |d.live R c p o (pull s x V)-d.live R c p o (pull s x U)| ≤
      |d.mark R c| * (p.threshold * Real.exp (d.length R / c.relaxation)) * (4*(1+(d.length R:ℝ))*δ):=by
  unfold Low.live; have hs:=p.threshold_pos; have hr:=c.radius_pos; have hd:0≤δ:=(chord.positive ..).trans (H.cost e)
  cases hj:d.2 with
  | inl _ =>
    simp only [Sum.elim_inl,Low.mark,hj,Low.length,abs_of_pos c.quadratic_pos,Nat.cast_zero,zero_div,Real.exp_zero,mul_one,add_zero]
    simp_rw [Face.send_price _ (o,d.1) s x (Gauge.chord G) SU.group.chord_inv (fun k h=>SU.group.chord_conj h k)] -- simp mul_one
    simpa using directUnit (f:=_) H c hs.le -- infer? 
  | inr j=>
    have hw := H.keeps s x c p.threshold_pos.le o; dsimp only [Sum.elim_inr]
    by_cases hv:PathData.kept c p.threshold o (pull s x U)
    · let D:=d.length R
      have hz:D=(d.left R j).length+(d.right R j).length:= by simp only [D,Low.length,hj,Sum.elim_inr]
      have hl (l:RG.Slot)(h:l.length≤D){W:Config G n}(hW:PathData.kept c p.threshold o W): ‖l.atSite W o‖ ≤ p.threshold* Real.exp (D/c.relaxation):=(kept_slot l hW).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right (Nat.cast_le.mpr h) hr.le)) hs.le)
      have ht (l:RG.Slot): ‖l.atSite (pull s x V) o-l.atSite (pull s x U) o‖ ≤ 2*(l.length:ℝ)*δ:= slot_cost δ (H.pulled s x) l o hd
      let a:= d.left R j; let b:=d.right R j
      have ha:a.length≤D:=by unfold a; rw [hz]; omega
      have hb:b.length≤D:=by unfold b; rw [hz]; omega
      rw [if_pos (hw.mpr hv),if_pos hv]; unfold Low.plain; simp only [hj,Sum.elim_inr]
      rw [←mul_sub,abs_mul, mul_assoc _ (p.threshold*_)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have he:= dotCost _ _ _ _ _ _ (ht a) (ht b) (hl a ha hv) (hl b hb (hw.mpr hv)) (mul_nonneg (by positivity) hd)
      rw [←sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
      refine (div_le_self (abs_nonneg _) (by norm_num)).trans (he.trans ?_)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hs.le (Real.exp_pos _).le)
      rw [←add_mul]; gcongr ?_ * _; nlinarith only [(Nat.cast_le (α:=ℝ)).mpr ha,(Nat.cast_le (α:=ℝ)).mpr hb,Nat.cast_nonneg (α:=ℝ) D]
    · simp only [if_neg hv,if_neg (mt hw.mp hv),sub_zero,abs_zero]; positivity
variable {k:ℕ}
lemma atomShape {k:ℕ} (a: RG.Atom G k) (x:Site n) (hp:k≤4) : x∈a.footprint x ∧ Branch.Grove (Grid.field 4 n) (a.footprint x) ∧ a.footprint x ⊆ halo (8+a.length) {x} ∧ (a.footprint x).card ≤ a.length+8:=by
  rw [Paths.atom_foot]; obtain ⟨t,r,h⟩:=bundle_limit x a.leg
  exact ⟨t,r,fun i hi=>halo_spec.mpr ⟨x,mem_singleton_self _,(Paths.where_slot x a.leg i hi |>.trans (Nat.le_add_left _ _))⟩,h.trans (show _≤ a.length+8 by change a.length+k+1 ≤ _; omega) ⟩ -- placeholder
lemma atomLocal {a:RG.Atom G k}{x:Site n}(hr:Agrees (a.footprint x) U V)(hf:Healthy p.threshold (a.footprint x) U ↔ Healthy p.threshold (a.footprint x) V):
    a.placed p U x=a.placed p V x:=by
  unfold RG.Atom.placed; by_cases h:Healthy p.threshold (a.footprint x) U
  · rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ (hf.mp h)]; unfold RG.Atom.unmasked
    congr! 1; ext1 i; refine slot_reads _ _ U V (agrees_mono hr (Finset.coe_subset.mpr (show (BPress.Wealth.foot x (a.leg i))⊆ _ from by
      rw [Paths.atom_foot]; exact fun j h=>Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨i,mem_univ i,h⟩))))
  rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt hf.mpr h)]
-- product comparison telescoping
private lemma prodSense {v w:Fin k→ℝ}{D:Fin k→ℝ}{J:Finset (Fin k)} (h:0≤τ) (f:∀ i,|v i|≤τ)(g:∀ i,|w i| ≤ τ)(t:∀ i,|v i-w i| ≤ D i) :
    |(∏ i∈J, v i) - ∏ i∈J, w i| ≤ (∑ i∈J,D i) * τ^(J.card-1):= by
  induction J using Finset.induction_on with
  | empty => simp
  | insert j J hj ih =>
    rcases J.eq_empty_or_nonempty with hJ|hJ; · subst J; simpa using t j
    have hh:=hJ.card_pos
    simp_rw [prod_insert hj,sum_insert hj,card_insert_of_notMem hj, Nat.add_sub_cancel, add_mul]
    rw [show v j*(∏ i∈J,v i)-w j*(∏ i∈J,w i)=(v j-w j)*(∏ i∈J,v i)+ w j*((∏ i∈J,v i)-(∏ i∈J,w i)) by ring]
    have hv: |(∏ i∈J, v i)|≤ τ^J.card:=by rw [Finset.abs_prod,←Finset.prod_const]; exact prod_le_prod (fun i _=>abs_nonneg _) (fun i _=>f i)
    refine (abs_add_le ..).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul (t j) hv (abs_nonneg _) ((abs_nonneg _).trans (t j))
    rw [abs_mul]; calc
      _ ≤ τ * ((∑ i∈J,D i)*τ^(J.card-1)) := mul_le_mul (g j) ih (abs_nonneg _) h
      _ = (∑ i∈J,D i)*τ^(J.card) := by nth_rw 2 [show J.card=J.card-1+1 by omega]; rw [pow_succ]; ring
lemma atomSense {a:RG.Atom G k}(s:Signed)(o x:Site n)(H:Toggle e p.threshold δ U V)(hk:2≤k):
    |a.placed p (pull s o V) x-a.placed p (pull s o U) x| ≤ a.magnitude*p.threshold*(4*(1+a.length)*δ):=by
  unfold RG.Atom.placed; have hs:=p.threshold_pos; have ht:=p.threshold_le; have hd:0≤δ:=(chord.positive ..).trans (H.cost e)
  have hm:0≤a.magnitude:=by unfold RG.Atom.magnitude; positivity
  by_cases he:Healthy p.threshold (a.footprint x) (pull s o U)
  · have hf:= (H.healthy s o _).mp he
    rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ hf]; unfold RG.Atom.unmasked RG.Atom.poly RG.Atom.magnitude
    simp only [sum_mul,←sum_sub_distrib,←mul_sub]
    refine (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _=>?_)
    rw [abs_mul,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    let C (A:Config G n)(b:Fin k):=(a.leg b).atSite A x
    have hi (F:SU.group.Color)(i:SU.group.ColorIndex):|F i| ≤ ‖F‖:=by
      simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one,one_mul] using abs_real_inner_le_norm (EuclideanSpace.basisFun _ ℝ i) F
    have hh(b:Fin k) : |C (pull s o V) b (i b)-C (pull s o U) b (i b)| ≤ 2*((a.leg b).length:ℝ)*δ :=
      (hi (C (pull s o V) b-C (pull s o U) b) _).trans (slot_cost δ (H.pulled s o) _ x hd)
    apply (prodSense hs.le (fun j=> (hi _ _).trans (healthy_leg a x _ _ hf j)) (fun j=> (hi _ _).trans (healthy_leg a x _ _ he j)) hh).trans
    rw [←sum_mul, ←mul_sum, ←Nat.cast_sum, card_univ,Fintype.card_fin]
    unfold RG.Atom.length
    have hh:p.threshold^(k-1)≤ p.threshold:=by simpa only [pow_one] using pow_le_pow_of_le_one hs.le ht (show 1 ≤ k-1 by omega)
    refine (mul_le_mul_of_nonneg_left hh (show 0≤ 2*↑(_ : ℕ)*δ by positivity)).trans ?_
    let L:= (∑ b:Fin k, (a.leg b).length)
    have hL:0≤ (L:ℝ):=by positivity
    change 2*(L:ℝ)*δ*p.threshold ≤ p.threshold*(4*_*δ)
    rw [mul_comm _ p.threshold]; gcongr <;> linarith
  rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ (mt (H.healthy s o _).mpr he)]; simp only [sub_zero,abs_zero]; positivity
-- Joint label offers. Strength C independent of p,R once Bounds, Clip, Width fixed.
-- Keep raw cost (include /|Signed|), abs sum incl every direction, center and path arity.
inductive TypeA where | cycle | tri | tetra deriving DecidableEq, Fintype

def TypeA.arity : TypeA→ ℕ | .cycle=> 2 | .tri=> 3| .tetra=> 4

def TypeA.atom (R:PathData G) (t:TypeA)(j:ℕ) : RG.Atom G t.arity := match t with
  | cycle=> R.loop j| tri=>R.cubic j| tetra=>R.quartic j

def TypeA.price (β:ℝ) : TypeA→ℝ| cycle=>1|tri=>β|tetra=>β

abbrev Arm := Low ⊕ (TypeA×ℕ)
namespace Arm
-- β from Gauge, not epsilon
variable (R)

def read (c:Clip)(p:BudgetPoint)(β:ℝ)(d:Arm)(o:Site n)(U:Config G n):ℝ:=d.elim (fun l=>β*l.live R c p o U)
    (fun v=>v.1.price β*((v.1.atom R v.2).placed p U o))

def stem (d:Arm):ℕ:= d.elim (fun l=>l.length R) (fun v=> (v.1.atom R v.2).length)
def footprint (d:Arm)(o:Site n):= d.elim (fun l=>lowerSeat R l o) (fun v=> (v.1.atom R v.2).footprint o)
def weight (c:Clip) (d:Arm):= d.elim (fun l=> |l.mark R c|) (fun v=> (v.1.atom R v.2).magnitude)
variable {R}

lemma shape (d:Arm)(o:Site n): o∈d.footprint R o ∧ Branch.Grove (Grid.field 4 n) (d.footprint R o) ∧ d.footprint R o⊆ halo (8+d.stem R) {o} ∧ (d.footprint R o).card ≤ d.stem R+8:=by
 cases d with| inl i=> exact lowerShape R i o|inr i=> exact atomShape _ o (by rcases i with ⟨_ | _ | _,y⟩ <;> norm_num [TypeA.arity])

lemma loc {d:Arm}{o:Site n}{β:ℝ}(h:Agrees (d.footprint R o) V U)(t:PathData.kept c p.threshold o V ↔ PathData.kept c p.threshold o U)(x:Healthy p.threshold (d.footprint R o) V ↔ Healthy p.threshold (d.footprint R o) U):
    d.read R c p β o V=d.read R c p β o U:=by cases d with|inl i=> exact congrArg (β*·) (lowLocal h t)|inr u=> exact congrArg (u.1.price β*·) (atomLocal h x)

lemma sense (d:Arm)(o:Site n)(s:Signed){β:ℝ}(v:1≤β)(H:Toggle e p.threshold δ U V):
    |d.read R c p β o (pull s 0 V)-d.read R c p β o (pull s 0 U)| ≤
      (β*p.threshold*δ*4) * (d.weight R c*(1+(d.stem R:ℝ))*Real.exp (d.stem R/c.relaxation)):=by
  cases d with
  | inl i=> simpa only [read, Sum.elim_inl,stem,weight,←mul_sub,abs_mul,abs_of_pos (lt_of_lt_of_le zero_lt_one v),mul_assoc,mul_left_comm,mul_comm] using
              mul_le_mul_of_nonneg_left (lowSense (R:=R) (c:=c) o i s 0 H) (zero_le_one.trans v)
  | inr z=>
    simp only [read,Sum.elim_inr,weight,stem,←mul_sub,abs_mul]; let A:=z.1.atom R z.2; let l:=A.length; have hm: |z.1.price β| ≤β :=by rcases z with ⟨_|_|_,j⟩ <;> simp [TypeA.price,abs_of_pos (lt_of_lt_of_le zero_lt_one v),v]
    have hp:0≤δ:=(chord.positive ..).trans (H.cost e); have he:= p.threshold_pos; have ht:= c.radius_pos
    refine (mul_le_mul hm (atomSense (a:=A) s 0 o H (by rcases z with ⟨_|_|_,j⟩ <;> norm_num [TypeA.arity])) (abs_nonneg _) (zero_le_one.trans v)).trans (le_trans (b:= (β*p.threshold*δ*4) * (A.magnitude*(1+(l:ℝ))*1)) (by unfold l A; ring_nf; rfl) ?_)
    change (β*p.threshold*δ*4)*(A.magnitude*(1+(l:ℝ))*1) ≤ _
    gcongr; · unfold RG.Atom.magnitude; positivity
    · apply Real.one_le_exp; exact div_nonneg (Nat.cast_nonneg (α:=ℝ) l) ht.le

def allowed (c:Clip)(C Λ:ℝ):=Geo.lowerSize c C+(Λ+C+C)
lemma coeff {σ C Λ:ℝ} (h:R.Bounds c σ C Λ) : SumBudget
    (fun d:Arm=> d.weight R c * Real.exp (σ*d.stem R)) (allowed c C Λ):=by
  unfold allowed; apply Extra.Iteration.Cost.sum -- namespace check
  · exact Geo.lower_budget G R h
  let f: TypeA × ℕ →ℝ:=fun d=> (d.1.atom R d.2).budget σ
  let m (i:TypeA):ℝ:= match i with | .cycle=> Λ | .tri=>C| .tetra=>C
  have hs(i):SumBudget (fun j:ℕ=> f (i,j)) (m i):=by cases i; exact h.two; exact h.three; exact h.four
  -- via sum/fiberwise
  have hb: SumBudget f (∑ i, m i) := budget_fiberwise Prod.fst (fun i=>(hs i.1).1 i.2) ?_ (budget_finite (fun i=> budget_nonneg (hs i)) le_rfl)
  · -- Fintype.sum enumeration
    have he: (∑ i, m i)=Λ+C+C:= by
      rw [show (Finset.univ:Finset TypeA)={TypeA.cycle,TypeA.tri,TypeA.tetra} from Finset.ext fun u=>by cases u <;> simp [Finset.mem_insert]]; simp [m,add_assoc]
    rw [he] at hb; exact hb
  intro k v p; calc
    _ = ∑ j∈v.image Prod.snd, f (k,j):=by
      rw [sum_image (by intro i hi j hj h; exact Prod.ext ((p i hi).trans (p j hj).symm) h)]; apply sum_congr rfl; intro i hi; simp only [←p i hi,Prod.mk.eta]
    _ ≤ m k:= budget_sum (hs k) _
lemma weight_nonneg (d:Arm): 0 ≤ d.weight R c:=by cases d with|inl i=> exact abs_nonneg _|inr i=> unfold weight RG.Atom.magnitude; simp only [Sum.elim_inr]; positivity
variable {σ C Λ:ℝ}(h:R.Bounds c σ C Λ)(st:12≤c.relaxation*σ)
include h st
private def priceF (σ:ℝ) := (σ/8)⁻¹ * Real.exp (σ/8) * Real.exp ((σ/4)*8)
private def sticker (R)(c:Clip)(σ:ℝ)(d:Arm):= d.weight R c*(1+(d.stem R:ℝ))*Real.exp (d.stem R/c.relaxation)*Real.exp ((σ/4)*(8+(d.stem R:ℝ)))
lemma lam : SumBudget (fun d:Arm=> sticker R c σ d * Real.exp ((σ/4)*d.stem R)) (priceF σ * allowed c C Λ) := by
  let P:=σ/8; have ht:= h.width; have hp:0<P:=div_pos ht (by norm_num); have hr:=c.radius_pos; let F:=priceF σ; have hv: 0 ≤ priceF σ:=by unfold priceF; positivity
  refine budget_mono (budget_scale hv (coeff h)) (fun i=>?_) fun i=>?_
  · unfold sticker; have hi:= weight_nonneg (R:=R) (c:=c) i; positivity
  let l:=(i.stem R:ℝ); have hl:0≤l:=Nat.cast_nonneg _; have hi:=weight_nonneg (R:=R) (c:=c) i
  have hd: 1+l ≤ (P⁻¹ * Real.exp P)*Real.exp (P*l):= by simpa using polynomial_cost hp hl 1
  let w:= i.weight R c
  change w*(1+l)*_*_*_≤_
  calc
    _ ≤ w*((P⁻¹ * Real.exp P)*Real.exp (P*l))*Real.exp (l/c.relaxation)*Real.exp ((σ/4)*(8+l))*Real.exp ((σ/4)*l) := by gcongr
    _ = w*priceF σ*Real.exp (P*l+l/c.relaxation+(σ/4)*l+(σ/4)*l):= by simp only [mul_add,Real.exp_add,priceF]; unfold P; ring
    _ ≤ w*priceF σ*Real.exp (σ*l):= by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hi hv); apply Real.exp_monotone
      have hu: l/c.relaxation ≤ σ*l/8 := (div_le_iff₀ hr).mpr (by nlinarith only [mul_le_mul_of_nonneg_right st hl,hl])
      unfold P; nlinarith only [hu,mul_nonneg ht.le hl]
    _ = priceF σ*(w*Real.exp (σ*l)):=by ring

variable {β:ℝ}(v:1 ≤ β)
def Rate (σ:ℝ):= σ/4

def treasure (R:PathData G)(β:ℝ)(c:Clip)(p:BudgetPoint)(s:Signed)(U V:Config G n)(d:Site n×Arm):ℝ:= d.2.read R c p β d.1 (pull s 0 V) - d.2.read R c p β d.1 (pull s 0 U)

def house (R:PathData G)(s:Signed)(d:Site n× Arm) := (d.2.footprint R d.1).image (turnSites s (0:Site n))

def paid (R:PathData G)(d:Arm) := 8 + d.stem R

omit h st
lemma rooted (R:PathData G)(d:Site n × Arm)(s:Signed): let t:=turnSites s (0:Site n); let Y:= house R s d;
    t d.1∈Y ∧ Branch.Grove (Grid.field 4 n) Y ∧ Y⊆ halo (paid R d.2) {t d.1} ∧ Y.card ≤ paid R d.2:=by
  intro t Y; obtain ⟨a,b,c,h⟩:=shape (R:=R) d.2 d.1
  refine ⟨mem_image_of_mem _ a,photo_g s _ b,fun i hv=>?_,card_image_le.trans (h.trans_eq (Nat.add_comm ..))⟩ -- photo_g t vs s
  obtain ⟨j,hj,rfl⟩:= mem_image.mp hv; obtain ⟨l,hl,z⟩:=halo_spec.mp (c hj)
  exact halo_spec.mpr ⟨_,mem_singleton_self _,(turn_sep ..).trans_le (Finset.mem_singleton.mp hl ▸ z)⟩

-- new support pull tags; TurnSites eq photo right
lemma endpoints (d:Site n×Arm)(s:Signed)(H:Toggle e p.threshold δ U V)
    (hm: treasure R β c p s U V d≠0):e.1∈house R s d ∧ e.1+step e.2∈house R s d:=by
  by_contra! θ
  let S:=d.2.footprint R d.1
  have he:Agrees S (pull s (0:Site n) V) (pull s 0 U):=agrees_pull s 0 (fun i t v=>H.off i (fun l=> θ (l ▸ t) (l ▸ v)))
  exact hm (sub_eq_zero.mpr (loc he (H.keeps _ _ c p.threshold_pos.le _) ((H.healthy _ _ _).symm)))

def stocked (c:Clip)(σ C Λ:ℝ):= Wt (σ/4) 8 * (priceF σ * allowed c C Λ)

include h st v
lemma issued (s:Signed)(H:Toggle e p.threshold δ U V): SumBudget (fun d:Site n × Arm => |treasure R β c p s U V d| * Real.exp (Rate σ *(paid R d.2:ℝ)))
    ((β*p.threshold*δ*4)*stocked c σ C Λ):=by
  have hp:0<Rate σ:= div_pos h.width (by norm_num); have he:0 ≤ δ:=(chord.positive ..).trans (H.cost e)
  have hv:= current_bound (turnSites s (0:Site n)) 8 (fun d:Arm=> d.stem R) (house R s)
    (fun i=> (rooted R i s).2.2.1) (b:=sticker R c σ)
    (fun i=> by unfold sticker; have hi:= weight_nonneg (R:=R) (c:=c) i; positivity)
    hp (a:=0) (fun i=> by rw [zero_mul]; positivity) (lam h st)
  refine budget_mono (budget_scale (show 0≤β*p.threshold*δ*4 by have ht:= p.threshold_pos; have hb:=zero_le_one.trans v; positivity) (hv.hits e.1)) (fun i=>by positivity) fun i=>?_
  unfold BPress.Ledger.score; split
  · simp only [zero_mul, Real.exp_zero,one_mul]; unfold treasure
    refine (mul_le_mul_of_nonneg_right (sense i.2 i.1 s v (c:=c) (R:=R) H) (Real.exp_pos _).le).trans_eq ?_
    unfold sticker Rate paid; push_cast; ring
  next hx =>
    have hi: treasure R β c p s U V i=0:=Classical.not_not.mp fun t=> hx (endpoints i s H t).1
    rw [hi]; simp
-- get Geo.Width p condition eventually (or prove for st direct). st implies sum of mark coeff budget & shapes; no hb.
omit v
lemma liveTotal (o:Site n)(U: Config G n): Summable (fun i:Low=> i.live R c p o U) ∧
    ∑' (i:Low), i.live R c p o U=∑ a,R.baseTerm c p U (o,a):=by
  let f(i:Low) := i.live R c p o U
  have hd:0≤ 2*p.threshold:=mul_nonneg (by norm_num) p.threshold_pos.le
  have hu: Summable f := Summable.of_norm_bounded ((Geo.lower_budget G R h).2.1.mul_left (2*p.threshold)) fun i=>by
    rw [Real.norm_eq_abs]; refine (i.shapeBound R c (p:=p) o U).trans ?_
    calc
      _ = (2*p.threshold)*(|i.mark R c| *Real.exp (i.length R/c.relaxation)):=by ring
      _ ≤ _ := by apply mul_le_mul_of_nonneg_left _ hd; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); apply Real.exp_monotone; apply (div_le_iff₀ c.radius_pos).mpr; have hp:= mul_le_mul_of_nonneg_right st (Nat.cast_nonneg (α:=ℝ) (i.length R)); linarith only [hp,Nat.cast_nonneg (α:=ℝ) (i.length R)] -- nlinarith?
  refine ⟨hu,(Low.label_sum (f:=_) hu).trans (Finset.sum_congr rfl fun a _=>?_)⟩
  by_cases he: PathData.kept c p.threshold o U <;> simp only [f,Low.live,he,↓reduceIte,PathData.baseTerm,Sum.elim_inl,Sum.elim_inr,tsum_zero,Low.rowPair h]

omit h st in
private lemma type_sum (f:TypeA→ℝ):(∑ i,f i)=f TypeA.cycle+f TypeA.tri+f TypeA.tetra:=by
 rw [show (Finset.univ:Finset TypeA)={TypeA.cycle,TypeA.tri,TypeA.tetra} from Finset.ext fun u=>by cases u <;> simp [Finset.mem_insert]]; simp [add_assoc]

-- due β=1 edge ok.
lemma liveAction (β:ℝ)(U:Config G n)(o:Site n): Summable (fun i=> read R c p β i o U) ∧
    ∑' i, read R c p β i o U=
      β * (∑ a: PlaqAxes,R.baseTerm c p U (o,a)) + β* (PathData.atomSeries R.cubic p U o+ PathData.atomSeries R.quartic p U o) + PathData.atomSeries R.loop p U o:=by
  let f(i:Arm):=read R c p β i o U
  obtain ⟨hh,he⟩:=liveTotal (p:=p) h st o U
  have hs: Summable (fun i:Low=> f (.inl i)):=hh.mul_left β
  have hg(k : TypeA): Summable (fun j:ℕ=> f (.inr (k,j))) := by
    let u(j):= (k.atom R j).placed p U o
    change Summable (fun j=> (k.price β)*u j)
    apply Summable.mul_left; cases k <;> unfold u -- h
    · exact ((PathData.atom_dominated _ p o h.width h.two).absolute _).of_norm
    · exact ((PathData.atom_dominated _ p o h.width h.three).absolute _).of_norm
    exact ((PathData.atom_dominated _ p o h.width h.four).absolute _).of_norm
  have hp:Summable (fun i:TypeA×ℕ=> f (.inr i)):=by
    -- summable_prod_of_summable_norm?
    let q(i:TypeA×ℕ):= f (.inr i)
    exact Summable.of_norm ((summable_prod_of_nonneg (f:=fun i=>‖q i‖) (fun _=>norm_nonneg _)).mpr ⟨fun k=>(hg k).abs,Summable.of_finite⟩)
  constructor
  · exact Summable.sum f hs hp -- check
  rw [Summable.tsum_sum (f:=fun i=>f i) hs hp,hp.tsum_prod,tsum_fintype (fun k:TypeA=> ∑' (j:ℕ), f (.inr (k,j))),type_sum]
  change (∑' (i:Low),β*i.live R c p o U) + ((∑' i,1*(R.loop i).placed p U o)+(∑' i,β*(R.cubic i).placed p U o)+(∑' i,β*(R.quartic i).placed p U o))=_
  simp_rw [one_mul,tsum_mul_left, he,PathData.atomSeries]; ring
end Arm
abbrev Book (n:Side) := Signed×Site n×Arm
private abbrev signfee := (Fintype.card Signed:ℝ)⁻¹
open Arm
-- precisely (part of) LP.6 first-row purchases with its own sign
variable (R)(c)(p)(n)
def offset : Book n→ ℕ := fun d=> paid R d.2.2

def estate : Book n→Support n := fun d=> house R d.1 d.2

def chip (β:ℝ)(U V:Config G n) : Book n→ℝ := fun d=> -signfee * treasure R β c p d.1 U V d.2

variable {R c p n} {β σ C Λ:ℝ}
def guaranteed (c:Clip)(σ C Λ:ℝ):=4*stocked c σ C Λ

variable (h:R.Bounds c σ C Λ)(st:12≤ c.relaxation*σ)
include h st
lemma energySeries (β:ℝ)(U:Config G n):HasSum (fun d:Book n => d.2.2.read R c p β d.2.1 (pull d.1 0 U))
    (∑ s:Signed,R.principal c p β (pull s 0 U)):=by
  let f(d:Book n):= d.2.2.read R c p β d.2.1 (pull d.1 0 U); have he(s:Signed)(x: Site n):=(liveAction (p:=p) h st β (pull s 0 U) x)
  have hf(s:Signed): Summable fun i:Site n×Arm=> f (s,i):= Summable.of_norm ((summable_prod_of_nonneg
    fun i=>norm_nonneg (f (s,i))).mpr ⟨fun x=>(he s x).1.abs,Summable.of_finite⟩)
  have hp: Summable f:= Summable.of_norm ((summable_prod_of_nonneg fun i=>norm_nonneg (f i)).mpr ⟨fun s=>(hf s).abs,Summable.of_finite⟩)
  have hx: ∑' i,f i = _:= hp.tsum_prod; rw [tsum_fintype (fun s:Signed=> ∑' i,f (s,i))] at hx
  change HasSum f _; rw [←show (∑' i, f i) = (∑ s : Signed,R.principal c p β (pull s 0 U)) from ?eq]; exact hp.hasSum
  case eq=>
    rw [hx]; apply sum_congr rfl; intro s _
    let W:=pull s (0:Site n) U
    rw [(hf s).tsum_prod,tsum_fintype]; change (∑ b, ∑' i:Arm, read R c p β i b (pull s 0 U))=R.principal c p β W; simp_rw [(he s _).2]; unfold PathData.principal; rw [Fintype.sum_prod_type]; simp only [sum_add_distrib,←mul_sum]; ring

-- Expense buys exponential true LENGTH rate and therefore also same estimation just using connected support costs. independent of other payer h.
lemma LPSeven (e:Edge (Site n))(H:Toggle e p.threshold δ U V)(v:1 ≤ β):
    HasSum (chip n R c p β U V) (R.inChannels c p β U - R.inChannels c p β V) ∧
    SumBudget (fun d:Book n=> |chip n R c p β U V d| * Real.exp (Rate σ * (offset n R d:ℝ)))
      (guaranteed c σ C Λ * β*p.threshold*δ):=by
  suffices z : SumBudget (fun i:Book n=> |chip n R c p β U V i| * Real.exp (Rate σ*(offset n R i:ℝ))) (guaranteed c σ C Λ * β * p.threshold * δ) by
    have ht:= ((energySeries (p:=p) h st β V).sub (energySeries (p:=p) h st β U)).mul_left (-signfee)
    refine ⟨?_,z⟩; have he: R.inChannels c p β U-R.inChannels c p β V = -signfee*((∑ i:Signed,R.principal c p β (pull i (0:Site n) V))-(∑ i:Signed,R.principal c p β (pull i (0:Site n) U))) := by unfold PathData.inChannels signfee; ring
    rw [he]; exact ht
  let X:=β*p.threshold*δ*4*stocked c σ C Λ
  let g(i:Book n):= |chip n R c p β U V i| * Real.exp (Rate σ*(offset n R i:ℝ))
  have hh:0 ≤ signfee:=by unfold signfee; positivity
  have hf(j:Signed) : SumBudget (fun i=> g (j,i)) (signfee*X):= by
    convert! budget_scale hh (issued h st v j H) using 1; ext i
    simp [g,chip,abs_mul,abs_of_nonneg hh,offset,mul_assoc]
  have hw : ∑ _i:Signed,signfee*X = guaranteed c σ C Λ * β*p.threshold*δ:=by
    simp only [sum_const,nsmul_eq_mul,card_univ,←mul_assoc]; unfold signfee; rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]; unfold guaranteed X; ring
  refine budget_loosen (budget_fiberwise (f:=g) Prod.fst (fun i=>by unfold g; positivity)
    (fun j a hv=>?_ ) (budget_finite (C:=∑ _i:Signed,signfee*X) (f:=fun _:Signed=>signfee*X) (fun j=> budget_nonneg (hf j)) le_rfl)) hw.le -- check parameter
  calc
    _ = ∑ i∈a.image Prod.snd,g (j,i):=by
      rw [sum_image (by intro i hi k hk h; exact Prod.ext ((hv i hi).trans (hv k hk).symm) h)]; refine sum_congr rfl fun i hi=>?_ ; simp only [←hv i hi,Prod.mk.eta]
    _ ≤ signfee*X:= budget_sum (hf j) _
-- Chp LP.6 spoil: comparison across assignments needs U elsewhere,
-- gates still at U (same decisions); triangle bounds didn't localize the masks in ell counting.
def Rules (c:Clip) (p:BudgetPoint) (A A':Config G n) (s:Signed):Prop := flags p.threshold A=flags p.threshold A' ∧ ∀ (x:Site n),PathData.kept c p.threshold x (pull s 0 A)↔PathData.kept c p.threshold x (pull s 0 A')

variable (d:Book n)
omit h st
private lemma focal {A A':Config G n} {β:ℝ}(q:Agrees (estate n R d) A A')(t:Rules c p A A' d.1):
    d.2.2.read R c p β d.2.1 (pull d.1 0 A) = d.2.2.read R c p β d.2.1 (pull d.1 0 A'):= Arm.loc (agrees_pull d.1 0 q) (t.2 _) (by rw [←healthy_pull,←healthy_pull,Healthy,Healthy,t.1])
theorem prices {β:ℝ}{A A' W W':Config G n}(q: Agrees (estate n R d) A A')(g:Agrees (estate n R d) W W')(h:Rules c p A A' d.1)(i:Rules c p W W' d.1):
    chip n R c p β A W d=chip n R c p β A' W' d := congrArg₂ (fun x y=> -signfee*(x-y)) (focal d g i) (focal d q h)

theorem orientation (H:Toggle e p.threshold δ U V)(β:ℝ):
    let x:= turnSites d.1 (0:Site n) d.2.1; let Y:=estate n R d;
    x∈Y ∧ Branch.Grove (Grid.field 4 n) Y ∧ Y⊆ halo (offset n R d) {x} ∧ Y.card ≤ offset n R d ∧
    (chip n R c p β U V d≠0→ e.1∈Y ∧ e.1+step e.2∈Y):=by
    intro x Y; obtain ⟨a,b,t,v⟩:=Arm.rooted R d.2 d.1; exact ⟨a,b,t,v,fun h=>Arm.endpoints d.2 d.1 H (fun z=>h (by unfold chip; rw [z,mul_zero]))⟩
@[fun_prop] lemma chip_meas (β:ℝ): Measurable fun x: Config G n × Config G n=> chip n R c p β x.1 x.2 d:= by
    have h: Measurable fun i=> d.2.2.read R c p β d.2.1 (Lattice.pull d.1 0 i):= by
      unfold Arm.read; cases hj:d.2.2 with
      | inl i=>
        dsimp only [Sum.elim_inl]; refine measurable_const.mul ((i.live_meas ..).comp ?_); fun_prop
      | inr j=>
        dsimp only [Sum.elim_inr]; refine measurable_const.mul ((RG.masked_measurable _ _ _ (RG.Atom.unmasked_cont ..).measurable).comp (by fun_prop))
    exact measurable_const.mul ((h.comp measurable_snd).sub (h.comp measurable_fst))
end PureForce.GP
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
