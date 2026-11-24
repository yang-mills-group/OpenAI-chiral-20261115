import YM.SU5.Selected.PairedProtocol
/-!
# Pack LONG line banners with actually eligible Cliplets

New step for `the construction notes`. Nominal K.c colors; can replace receipts modulo
explicit period length identity at consuming in the history CCS tests. Note uses
integer ARCS even for THE OPPOSITE SATURATED seam: when we compute the Banner
line and reflect near the terminal length, no extra short-axis enlargement.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 460000
noncomputable section
namespace YM.CF.Pannier.Chancel.Cliplet
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG Brace
open Py.Rate (sites)
open Py.Rate.Pannier
open Buffered.Afterglow Buffered.Afterglow.Journey
open Mir Phase RP Reflect Advance Nacre Vale Girt Lifted Scree Tower
open Tower.SlabMark
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K:Calibration}{N m n:Side}{B l: ℕ} {M:Tulip.Male} {j k w d t:ℕ}{γ τ R:ℝ}
namespace Mural

variable {A S : Finset Cover}{a b c x : ℤ}{i:Axis}
lemma rub (K:Calibration) : 0<K.ℓ:=by
 have h:=K.buffer; have ht:0<K.R.L.val:=K.R.L.property
 unfold Margin r₃ r₁ at h; nlinarith

lemma no_collision (u:Between K i a b A)(v:Between K i b x S)
    (e:x-a≤ ((More n).val:ℤ)) : Disjoint (Satin.region A n) (Satin.region S n):=by
 apply disjoint_left.mpr; intro p f g
 obtain ⟨m,mh,rfl⟩:=mem_image.mp f; obtain ⟨l,lh,e₁⟩:=mem_image.mp g
 have he : ((More n).val:ℤ) ∣ l i-m i := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (congrFun e₁.symm i)
 obtain ⟨c,p⟩:=u m mh; obtain ⟨d,t⟩:=v l lh; have ht:=rub K
 have hx:=Int.le_of_dvd (by omega) he; omega

variable {ν:Mark (K.c m)→ℂ}(h:StageTw K ν j R d M) -- R implicit
variable (i: Axis){X : Axis → ℤ}{F : Buffered.Family K}
open Buffered.Afterglow.Tower (mirror)
/-- A priced flight witnessing a painting with cover temporal register & transverse savings. -/
def Cargo (K:Calibration)(m:Side)(j k w d t:ℕ)(γ τ:ℝ)(M:Male)(i:Axis)
  (a x : ℤ)(X:Axis→ℤ)(B:ℕ)(l:ℕ)(F:Buffered.Family K) := ∃ U : List (Cliplet (K.c m) k), Flight j M w d t γ τ U ∧
    F m=probe U ∧ U.length=l ∧ ∃ A, Between K i a x A ∧ Transom i A X B ∧ whereV U ⊆ Satin.region A (K.c m)
local notation "ℭ" a:max x:max p:max z:max=>Cargo K m j k w d t γ τ M i a x X B p z
local notation "c₀"=>ruler K.B
include h
private lemma reflects (p:ℭ a x l F)(n:ℤ) : ℭ (2*n-x) (2*n-a) l (Tower.mirror K i n F) := by
 obtain ⟨U,l,hF,v,A,hX,W,u⟩:=p
 let C:=U.map fun a=> a.mirror i n
 refine ⟨C,l.reflect i n (h.across i n) h.hire,?_,(by simpa [C] using v),reflectedBox i n A,hX.mirror K i n,W.mirro i n,?_⟩
 · change reflMark i n (F m)=_
   rw [hF,← Flight.reflect_probes]
 unfold C; rw [Flight.reflect_consistent]; intro y p
 obtain ⟨x,hx,rfl⟩:= mem_image.mp p; obtain ⟨q,b,e⟩:=mem_image.mp (u hx)
 subst x; rw [Shape.anno]; exact mem_image_of_mem _ (mem_image_of_mem _ b)
omit h
private lemma androgyny {Y:Buffered.Family K}{r:ℕ} (p:ℭ a b l F)(q:ℭ b x r Y)
    (v:x-a≤ ((More (K.c m)).val:ℤ))(e:a≤b)(u:b≤x) : ℭ a x (l+r) (F*Y):= by
 obtain ⟨U,f,g,k,A,l₁,l₂,l₃⟩:=p; obtain ⟨V,h,i',b,W,kx,ky,kz⟩:=q
 refine ⟨U++V,f.tack _ h ((no_collision l₁ kx v).mono l₃ kz),?_,?_,A∪W,pair_between K i l₁ kx e u,trans_union i l₂ ky,?_⟩
 · rw [probe_combine,Pi.mul_apply,g,i']
 · rw [List.length_append,k,b]
 rw [combine]; unfold Satin.region; rw [image_union]; exact union_subset_union l₃ kz
include h
private lemma displaced (p:ℭ a x l F)(v:ℤ) : ℭ (c₀*v+a) (c₀*v+x) l (relocate K i v F):=by
 have e:=reflects h i (reflects h i p 0) (gaugeT K v)
 rw [ruler_offset] at e
 ring_nf at e ⊢; exact e

private lemma vintage {u : ℤ} (p:ℭ 0 (c₀*u) l F)(r:ℕ) : ℭ 0 (c₀*u) l (toward K i u F r):=by
 induction r with
 | zero=> exact p
 | succ r ih=>
    rw [toward_step]; have e:=reflects h i ih (gaugeT K u)
    rwa [ruler_offset, sub_self,sub_zero] at e

private lemma lacework {u : ℤ} (p:ℭ 0 (c₀*u) 1 F)(y:0≤u)(r:ℕ)
   (v:c₀*u*r ≤ ((More (K.c m)).val:ℤ)) : ℭ 0 (c₀*u*r) r (lace K i u F 1 r) := by
 induction r with
 | zero=> exact ⟨[],⟨by simp,List.Pairwise.nil⟩,rfl,rfl,∅,(fun _ h=>by simp at h),fun _ _ _ h=>by simp at h,(by simp [whereV])⟩
 | succ r ih=>
    have ht :0≤ c₀*u:=mul_nonneg (ruler_gene K.B).le y
    rw [Nat.cast_add_one] at v ⊢
    let L:=toward K i u F r; let C:=lace K i u F 1 r
    have hh:=ih (le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) ht) v)
    rw [lacing]
    have hd:=displaced h i hh u; rw [add_zero] at hd
    have hep:=androgyny i (vintage h i p r) hd (by nlinarith) ht (by nlinarith)
    rw [mul_add,mul_one,add_comm (c₀*u*↑r),Nat.add_comm]; exact hep

lemma banners {u : ℤ}(p:ℭ 0 (c₀*u) 1 F)(y:0≤u)(r:ℕ)
   (v:2*(c₀*u*r)≤ ((K.c m).val:ℤ))(s:ℤ):
   let H:=c₀*(s-u*r); ℭ (H-2*(c₀*u*r)) (H+2*(c₀*u*r)) (4*r) (SlabMark.banner i u s r F):= by
 intro H'; let N:=K.c m
 let C:= c₀*u*r; let L:= lace K i u F 1 r; let S:= chambers i u s F 1 r
 have hp:0≤ c₀*u*r:= mul_nonneg (mul_nonneg (ruler_gene K.B).le y) (by positivity)
 have hh: ((More N).val:ℤ)=2*(N.val:ℤ):=by change ((↑(N.val*2):ℤ)=_); push_cast; ring
 have he:= lacework h i p y r (by unfold N at hh; linarith)
 have ht:=reflects h i he 0; rw [mul_zero, zero_sub,sub_zero] at ht
 have hd:= androgyny i ht he (by unfold N at hh; linarith) (by linarith) hp; have hk:=displaced h i hd s
 have hΩ : ℭ H' (H'+2*C) (r+r) S:= by
    rw [show H'+2*C = c₀*s+c₀*u*↑r by unfold C H'; ring,show H'=c₀*s+ -(c₀*u*r) by unfold H'; ring]; exact hk
 have hL:=reflects h i hΩ (gaugeT K (cliff u s r))
 have hy : gaugeT K (cliff u s r)=H':= centered_index (K:=K) u s r
 rw [show 2*gaugeT K (cliff u s r)-(H'+2*C)=H'-2*C by rw [hy]; ring, show 2*gaugeT K (cliff u s r)-H'=H' by rw [hy]; ring] at hL
 rw [show 4*r=r+r+(r+r) by omega]; exact androgyny i hL hΩ (by unfold N at hh; linarith) (by linarith) (by linarith)

end Mural
end YM.CF.Pannier.Chancel.Cliplet
#print axioms YM.CF.Pannier.Chancel.Cliplet.Mural.banners
