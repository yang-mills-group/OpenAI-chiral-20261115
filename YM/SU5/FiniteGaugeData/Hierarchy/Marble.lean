import YM.SU5.FiniteGaugeData.Hierarchy.Rhapsody
/-! # Dictionary with the same physical signed event, on the mixed profiles

Every receipt supported on a `Z ℕ→Finset Cover` is active: no matter which
s are read (but only finitely many read per Theater element, co-representative
redundancies permitted). Location may advance with gauge padding through the
global recipe's higher factors. Increases are accounted in `folio`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Charm
namespace Playlist
namespace Show
open Tint

section statements
variable (Z:ℕ→Finset Cover)
-- in fact each general Theater element is local in this multires sense; only finite S(s) needed.
lemma has_support (x:Theater (tent Y h)) : ∃ p:ℕ, ∃ Z:ℕ→Finset Cover, (∀ i, p < i → Z i=∅) ∧ Arrive Y h x p ∧ x ∈ active (tent Y h) (localChord (tent Y h) Z):=by
  classical
  obtain ⟨k,t⟩:= (arrived Y h x).exists; choose S m using testimony (tent Y h)
  let Z(i:ℕ):Finset Cover:=if i≤k then x.coeff.support.biUnion fun v=> S (v.val i) else ∅
  refine ⟨k,Z,fun i p=>if_neg (by omega),t,(active_iff ..).mpr fun i a u=>?_ ⟩; unfold Z; split
  next e=> exact locate_sub _ (m _) (subset_biUnion_of_mem (fun (v:Motif Kₜ)=> S (v.val u)) a)
  next e=> rw [t i a u (by omega)]; exact locate_one ..

-- accum area: all the same choir sizes but per-resolution; no assertions on `Z` restriction when observing high physical units

abbrev folio (Λ:Preparation)(l:ℕ)(Z:ℕ→Finset Cover): ℕ→ Finset Cover
 | 0=> Z 0
 | k+1=> GridStep Λ l (folio Λ l Z k) ∪ Z (k+1)

variable (m:Motif (tent Y h))(p: Region (tent Y h) m Z)
local notation "ζ" t:max=> folio Λ l Z t
local notation "T₀"=> GridStep Λ l
-- if using `J` or `P` or ANY `V` table. Always Catalog vector.
def erupt (A:Call Λ l) : (s:ℕ) → Catalog (folio Λ l Z s)
 | 0=> (reading Kₜ (Z 0) _ (p 0))
 | s+1=> timesQ Kₜ subset_union_left subset_union_right (A (folio Λ l Z s) s (erupt A s)) (reading Kₜ (Z (s+1)) _ (p (s+1)))

include K R
include p
lemma loc_origin : Locator (tent Y h) (preRoll Y h K R m s) (folio Λ l Z s) := by
  induction s with
  | zero=> exact p 0
  | succ i ih=> exact locate_join Kₜ _ (locate_sub Kₜ (locate_next Y h _ _ K R _ ih) subset_union_left) (locate_sub _ (p _) subset_union_right)
omit p
lemma sagacity (p:Region Kₜ m Z) : composeQ Kₜ (ζ s) (erupt Y h Z m p P s)=(preRoll Y h K R m s).val:=by
  induction s with
  | zero=> exact reading_p ..
  | succ i ih=>rw [erupt,timesQ_id, ← next_cert Y h _ _ K R _ (loc_origin Y h _ K R Z m p) _ ih,reading_p]; rfl

omit K R
private lemma sold_color_any (x: W Kₜ):covariant (sold Y h s i x.val):=by
  rw [sold_v]; apply castK _ (terrain Y h (Y.ir i) s) ((well_for Kₜ x).2 _)
where castK {m n:Side}(f:Mark m)(p:m=n)(v:covariant f):covariant (show Mark n from p▸f):=by subst m; exact v

-- actual upward read. no need hZ/pay to define; includes finite point-corners interpreted by integral conventions.
def story (m:Motif (tent Y h)): (s:ℕ)→ Mark (side Y i s)
 | 0=> sold Y h 0 i (m.val 0).val
 | t+1=> ingress Y t i k (story m t) * (sold Y h (t+1) i (m.val (t+1)).val)

-- native grants and identification with the Catalog approximants
abbrev Works (x:ℕ→Finset Cover) (i k s:ℕ): Prop := ∀ j≤ s, Offered Y (folio Λ l x j) j i k
abbrev Simulated (Z:ℕ→Finset Cover) (i s:ℕ):Prop:= ∀ j ≤ s,Solvent Y (folio Λ l Z j) j i  -- joint + inner fit distinct
abbrev tour (i k:ℕ):Call Λ l:= fun S t=> snag Y h S t i k

include p
lemma recognized (g:Works Y Z i k s): sold Y h s i (composeQ Kₜ (ζ s) (erupt Y h Z m p (tour Y h i k) s))= story Y h i k m s:=by
  induction s with
  | zero=> change sold Y h 0 i (composeQ Kₜ (Z 0) (reading Kₜ (Z 0) _ _))=_; rw [reading_p]; rfl
  | succ s ih=>
    let t:= g s (by omega); rw [erupt]
    rw [timesQ_id,sold_mult, show tour Y h i k _ s= _ from snag_pay Y h (ζ s) s i k t,transitionQ_apply,reading_p,exchanged,story, ih (fun j v=>g j (by omega))]

-- gauge covariance propagated on all actually read forms. (No question about orientation of average.)
include p
lemma native_account (g:Works Y Z i k s): AtSupport false (region (folio Λ l Z s) (side Y i s)) (story Y h i k m s) ∧ covariant (story Y h i k m s):=by
  have h'(s:ℕ)(g:Works Y Z i k s): Durable Kₜ (composeQ Kₜ (folio Λ l Z s) (erupt Y h Z m p (tour Y h i k) s)):=by
    induction s with
    | zero=> change Durable Kₜ (composeQ Kₜ (Z 0) _); rw [erupt, reading_p]; exact (well_for ..).2
    | succ s ih=>
      rw [erupt,timesQ_id];
      apply (Charm.allG (tent Y h)).mul_mem (show Durable Kₜ _ from ?_) (show Durable Kₜ _ from ?_)
      · exact snag_durable Y h (ζ s) s i k (g s (by omega)) _ (ih (fun j v=> g j (by omega)))
      rw [reading_p]; exact (well_for ..).2
  rw [←recognized Y h s i k Z m p g]; exact ⟨sold_affair Y h (ζ s) s i (compose_t ..), sold_color_any Y h s i ⟨_,⟨compose_test .., h' s g⟩⟩⟩

omit p
-- all awards for this element. Doesn't assume Works to evaluate the recipe; needs it to price/identify the walk.
abbrev Contract (x : Theater (tent Y h)) :Prop := x∈ active Kₜ (localChord Kₜ Z)
lemma contract_song (x:Theater Kₜ)(a:Contract Y h Z x)(v:x.coeff.support): Region Kₜ v.val Z:= (active_iff ..).mp a _ v.property

def major (x:Theater (tent Y h))(p:Contract Y h Z x) (A:Call Λ l) : Catalog (folio Λ l Z s):=∑ i:x.coeff.support, (x.coeff i.val) • erupt Y h Z i.val (contract_song Y h Z x p i) A s

include K R in
lemma major_score (x:Theater (tent Y h))(a:Contract Y h Z x): composeQ Kₜ (folio Λ l Z s) (major Y h s Z x a P) = (collapse Y h s K R x).val := by
  classical
  unfold major collapse; rw [fills, ←sum_attach x.coeff.support]; rw [map_sum]; simp_rw [map_smul, sagacity Y h _ K R]; apply Eq.symm; exact map_sum (well Kₜ).val.toLinearMap ..

def actual (x:Theater (tent Y h)) : Mark (side Y i s):= ∑ m ∈ x.coeff.support,x.coeff m • story Y h i k m s
lemma actual_eq (g:Works Y Z i k s)(x:Theater (tent Y h))(a:Contract Y h Z x):
    sold Y h s i (composeQ Kₜ (ζ s) (major Y h s Z x a (tour Y h i k)))=actual Y h s i k x:=by
  classical
  unfold major actual; rw [map_sum,map_sum]; simp_rw [map_smul,recognized (i:=i) (p:=contract_song Y h Z x a _) (k:=k) (g:=g)];
  rw [←sum_attach x.coeff.support]; rfl
lemma actual_inside (g:Works Y Z i k s)(x:Theater (tent Y h))(a:Contract Y h Z x):
    AtSupport false (region (folio Λ l Z s) (side Y i s)) (actual Y h s i k x) ∧ covariant (actual Y h s i k x):=by
  constructor
  · rw [← actual_eq Y h s i k Z g x a]; exact sold_affair Y h (ζ s) s i (compose_t ..)
  unfold actual; intro f p; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; refine sum_congr rfl fun z H=>?_ ; rw [Pi.smul_apply, Pi.smul_apply, twist_scalar, (native_account Y h s i k Z z ((active_iff ..).mp a _ H) g).2 f]

lemma covers (g:Works Y Z i k s) : MarkGate Y s i k:= ⟨(g s le_rfl).calendar,(g s le_rfl).age.le⟩

-- exact unnormalized numerator convention all marks with ONE Loom on entry; take prices on this reading
abbrev readout (x:Theater (tent Y h)) := Journey.compass Y i k s (actual Y h s i k x)
lemma real_receipt (g: Works Y Z i k s)(x:Theater (tent Y h)) (a:Contract Y h Z x):
    let T:=(Y.voyage i).CapeT s; let N:= side Y i s; let A:= actual Y h s i k x; let X:= Tᵣ i k s
    let z:= partitionZ X Λ.U T; let f:= fun v:Orbit N=> inner ℂ (Dial.mateK N) (acts (A (v.1,T v)) (denZ X Λ.U T v));
    Integrable f (city N) ∧ z≠0 ∧ readout Y h s i k x=(∫ v, f v ∂city N)/ z ∧ readout Y h s i k x=mkForm Y h (folio Λ l Z s) s i k (major Y h s Z x a (tour Y h i k)):=by
  intro t n A X z f; let V:= covers Y s i k Z g
  refine ⟨?_,vac_valid Y s i k V,rfl,by rw [mk_read _ _ _ _ _ _ V, sold_sharp, actual_eq _ _ _ _ _ _ g]⟩
  unfold f A; rw [← actual_eq _ _ _ _ _ _ g x a]; exact mark_legit Y h (ζ s) s i k V _ -- type lap

lemma zone_available {I:Type*}[Fintype I](f:I→ Theater (tent Y h)): ∃ (Z:ℕ→Finset Cover)(s:ℕ), (∀ i, s < i → Z i=∅) ∧ ∀ i:I, Arrive Y h (f i) s ∧ Contract Y h Z (f i):=by
  classical
  choose t Z u a q using fun i:I=> has_support Y h (f i)
  let T:= (Finset.univ:Finset I); let Z'(j):= T.biUnion (fun i=>Z i j); let s':=T.sup t; have hm(i:I): t i ≤ s':= le_sup (mem_univ i)
  refine ⟨Z',s',?_,fun i=> ⟨fun j p=> ends_mono Y h _ _ j (a i j p) (hm i),?_⟩⟩
  · intro k h; unfold Z'; ext x; simp [u _ k ((hm _).trans_lt h)] -- need ∀ i
  apply (active_iff ..).mpr; intro j v k; refine locate_sub _ ((((active_iff ..).mp (q i) j v):Region Kₜ j (Z i)) k) ?_
  exact subset_biUnion_of_mem (fun i=> Z i k) (mem_univ i)
#print axioms real_receipt
end statements
end Show
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
