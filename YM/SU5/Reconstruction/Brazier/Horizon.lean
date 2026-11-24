import YM.SU5.Reconstruction.Brazier.Aperture
import YM.SU5.Reconstruction.Brazier.Steps
/-! Computing conditional phase readings in the Ark arena with boundary marks. This is before the selection itself or use of its spectra. Then use at actually progressing cutoffs. -/
set_option autoImplicit false
set_option synthInstance.maxSize 31000
set_option maxRecDepth 6200
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry Altitude Exhibition Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  (G : GroundExtension (i := i) (k := k) (E := E) Y H)
variable {L : Rack Λ l} {B : Clay Λ l} (Z : Exhibition Y H i k I E L B)
variable (j : Axis) (C : Arena Y H G.history.circuit j 0 false)
  (χ : displayAlgebra Y H V G.history G.clipped j false C →⋆ₐ[ℂ] ℂ)
local notation "Gt" => marks (timeMesh Λ)
local notation "t₀" => insideAt Λ l (tent Y H)
local notation "D" => Domain Y H G
local notation "A"=> Ark.Ht Y H G.history.circuit j 0 false C
local notation "Π"=>Aurora Y H V G.history j false C
local notation "X" => Cloud (Dome (tent Y H))
local notation "Kx" t:max=> vistaFinish Y H t Z
local notation "Px" => LightBudget.prepaid Y H V G j C
open Chambers Tarmac
structure Hearth where
 roof:ℕ
 height: MeshClock.marks (timeMesh Λ)
 -- permit entire far mark as Θ pair
 token:Dome (tent Y H)
 pilot: Sky (tent Y H)
 distance:0 < height
 prepared : token ∈ insideAt Λ l (tent Y H) true (flank j height) roof
 earnest : pilot ∈ Domain Y H G true (flank j 0)
 registered : ticket Y H G roof token = Pub Y H j height pilot
-- lean insertion H/G for structure auto
namespace Hearth
variable (r:Hearth Y H G j)
local notation "hh"=>r.height
local notation "gg"=>r.token
local notation "π"=>pinhole (Dome (tent Y H)) (r.roof)
local notation "P"=> Pub Y H j
local notation "κ"=> ticket Y H G (r.roof)
noncomputable def upper : Cloud (Dome (tent Y H)):= pinhole _ r.roof r.token
noncomputable def lower : Cloud (Dome (tent Y H)):= pinhole _ r.roof (aureole (tent Y H) j 0 r.token)
abbrev gate (r:Hearth Y H G j) : Dome (tent Y H):= r.token*aureole (tent Y H) j 0 r.token
abbrev spanMark (r:Hearth Y H G j): Cloud (Dome (tent Y H)):= upper Y H G j r * lower Y H G j r
local notation "L₀"=>r.lower Y H G j
local notation "U₀"=>r.upper Y H G j
local notation "W₀"=>r.spanMark Y H G j
lemma gratuity : (π) (r.gate Y H G j)=r.spanMark Y H G j:= map_mul (π) _ _
local notation "st"=> flank j (r.height:ℝ)
local notation "st'"=> mirrorE j 0 '' st
lemma upperMemo : r.upper Y H G j ∈ questions Λ l K true (flank j r.height) := one_question Y H _ r.token r.prepared
lemma lowerMemo : r.lower Y H G j ∈ questions Λ l K true (mirrorE j 0 '' flank j r.height) := one_question Y H _ _ (mirror_inside Y H j r.token r.roof r.prepared)
lemma funding : r.spanMark Y H G j∈ questions Λ l K true (flank j r.height ∪ mirrorE j 0 '' flank j r.height):=
 mul_mem (questions_mono subset_union_left (r.upperMemo Y H G j)) (questions_mono subset_union_right (r.lowerMemo Y H G j)) -- tune
lemma reflected (t:ℝ):∀ x∈mirrorE j 0 '' (flank j t), x j≤-t := by
 rintro _ ⟨x,h,rfl⟩; simp [mirrorE]; exact h
lemma disjointness : Disjoint (flank j r.height) (mirrorE j 0 '' flank j r.height):= Set.disjoint_left.mpr fun x v w=> by
 have h:0 < (hh:ℝ):= r.distance; linarith [reflected j (hh:ℝ) _ w,(show (hh:ℝ) ≤ x j from v)]
local notation "f₁"=> realize Y H Z
local notation "Ξ"=> vistaTake Y H Z
lemma with_support {a:Tarmac}{w:ℕ}(p:Tarmac.Stage Λ l j a w)(v:lantern Λ a.roof w<r.height) : Disjoint (a.land Λ l) (flank j r.height ∪ mirrorE j 0 '' flank j r.height):=by
 apply Set.disjoint_left.mpr; intro x h q; have ht:= p.fits h; rw [←lantern_clock] at ht
 have hw: (lantern Λ a.roof w:ℝ)< (hh:ℝ):= v; rcases q with a|a
 · linarith [ht.2,(show (hh:ℝ) ≤ x j from a)]
 linarith [ht.1,reflected j (hh:ℝ) _ a]
include V in
lemma funded {t: Gt} (h:0≤t) : Pub Y H j t r.pilot∈ Domain Y H G false (flank j 0) :=
 later_frame Y H V G j r.pilot _ (domain_loose Y H G _ r.earnest) (by rw [eject_at]; exact h)
include V in
lemma realized_bundle (hm : spanMark Y H G j r∈ FiniteGaugeDataPoly (tent Y H)) : realize Y H Z ⟨r.spanMark Y H G j,hm⟩=Pub Y H j r.height r.pilot* flipMark j (tent Y H) (Pub Y H j r.height r.pilot):=by
 let u:FiniteGaugeDataPoly K:=⟨U₀,questions_polynomials (r.upperMemo Y H G j)⟩; let v:FiniteGaugeDataPoly K:=⟨L₀,questions_polynomials (r.lowerMemo Y H G j)⟩
 rw [show (⟨_,hm⟩:FiniteGaugeDataPoly K) = u*v from rfl, realize_separated Y H V G Z (x:=u) (y:=v) (r.upperMemo Y H G j) (r.lowerMemo Y H G j) (r.disjointness Y H G j)] -- r.disj args
 rw [←r.registered,flipMark_ticket]; exact congrArg₂ (· * ·) (one_realized Y H V G Z (r.roof) _ _) (one_realized Y H V G Z (r.roof) _ _)
local notation "Q"=>flipMark j (tent Y H)
local notation "H₀"=> advance Y H V G.history.circuit j 0 false C
noncomputable def home : (Ark.Ht Y H G.history.circuit j 0 false C):= LightBudget.prepaid Y H V G j C ⟨r.pilot,domain_loose Y H G _ r.earnest⟩
local notation "v₀"=> r.home Y H V G j C
lemma hire (t:Gt)(z:0≤t): Px ⟨P t r.pilot,r.funded Y H V G j z⟩ = H₀ (Real.toNNReal (t:ℝ)) v₀:= warmth Y H V G j C _ _ z
lemma selfPay : Ξ W₀ = ( (‖H₀ (Real.toNNReal (hh:ℝ)) v₀‖^2:ℝ):ℂ) := by
 let u:FiniteGaugeDataPoly (tent Y H) := ⟨W₀,questions_polynomials (r.funding Y H G j)⟩; let z:D false (flank j 0) :=⟨P hh r.pilot,r.funded Y H V G j r.distance.le⟩
 let f : D false univ:=⟨Q z.val*z.val,paired_forever Y H G j _ _ z.property z.property⟩
 have h:f₁ u =f.val:= (realized_bundle Y H V G Z j r u.property).trans (mul_comm ..)
 have he:= vista_on Y H V G Z u (h.symm ▸ f.property)
 rw [← r.hire Y H V G j C hh r.distance.le, ← he, show (⟨_,h.symm ▸ f.property⟩:D false univ)=f from Subtype.ext h]; change courseValue Y H V G f=_
 exact (LightBudget.initial_pair Y H V G j C z z).symm.trans ((inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (Px z)).trans (Complex.ofReal_pow _ _).symm) -- tune
lemma purchase {a:Tarmac}{w:ℕ}(p:Tarmac.Stage Λ l j a w)(v:lantern Λ a.roof w<r.height){α:ℝ}{x:Cloud (Dome (tent Y H))} (hx:Pocket (tent Y H) a.book a.roof α x) :
 let z₀:= H₀ (( (r.height - lantern Λ a.roof w:marks (timeMesh Λ)):ℝ).toNNReal) v₀
 vistaTake Y H Z (x*W₀) = inner ℂ z₀ ((credit Y H V G Z j C p hx).val z₀):=by
 intro z₀; let d:=lantern Λ a.roof w; let H':D false (flank j 0):=⟨P (hh-d) r.pilot,r.funded Y H V G j (sub_nonneg.mpr v.le)⟩
 let Y':=Q H'.val; let f:= ticket Y H G a.roof ((Kx (a.roof)) x)
 let X':FiniteGaugeDataPoly K:= ⟨x,a.quay Y H hx.populated⟩; let K':FiniteGaugeDataPoly K:= ⟨W₀,questions_polynomials (r.funding Y H G j)⟩; let W:=X'*K'; let o:=P hh r.pilot
 let A':= representationOf Y H Z j p hx
 obtain ⟨Xg,Cg,e⟩:= rootGraph Y H V G j C a.roof (w+w) A' (p.hwords j) H' -- p.hwords j order?
 let op := credit Y H V G Z j C p hx; let Z' : D false univ:= ⟨f₁ W,always_realizes Y H V G Z W⟩
 have hr:P d f= ticket Y H G a.roof (base Y H j a.roof (w+w) A').val:= PubL Y H V G j _ w _
 have he: Z'.val=f*(o*Q o):= by
   have hg: (X'.val)∈ questions Λ l K false (a.land Λ l):= by
     exact admits Λ l K true _ _ _ _ Set.inter_subset_left Set.Subset.rfl (a.storm Y H hx.populated) -- tune
   change f₁ W=_; rw [show W=X'*K' from rfl, realize_separated Y H V G Z (x:=X') (y:=K') hg (r.funding Y H G j) (with_support Y H G j r p v)]; exact congrArg₂ (· * ·) (realize_ticket Y H V G Z a.roof X' hx.funded) (realized_bundle Y H V G Z j r _)
 have hg : Q H'.val= P d (Q o):= by change Q (P (hh-d) r.pilot)=P d (Q (P hh r.pilot)); rw [pub_negflip,pub_negflip,pub_sum]; congr 2; abel
 have hk : P (lantern Λ a.roof (w+w)) H'.val=P d o:= by change P _ (P _ r.pilot)=P _ (P _ r.pilot); rw [pub_sum,pub_sum,lantern_add]; congr 2; dsimp only [d]; abel
 have ht : P d Z'.val=Y'*Xg.val:= by
   unfold Y'; rw [he,Cg,hg,hk, ←hr]; unfold Pub; rw [move_prod,move_prod]; ac_rfl
 let Qy:D false univ:=⟨Y'*Xg.val,paired_forever Y H G j _ _ H'.property Xg.property⟩
 calc _ = courseValue Y H V G Z' := (vista_on Y H V G Z W Z'.property).symm
      _ = courseValue Y H V G Qy:= by
          rw [←root_shift Y H V G j C (eject j d) Z'.property (ht.symm ▸ Qy.property)]; exact congrArg _ (Subtype.ext ht)
      _ = inner ℂ (Px H') (Px Xg):= (LightBudget.initial_pair Y H V G j C H' Xg).symm
      _ = _:= by rw [e,show Px H'= z₀ from hire Y H V G j C r (hh-d) (sub_nonneg.mpr v.le)]; rfl
end Hearth
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Brazier
