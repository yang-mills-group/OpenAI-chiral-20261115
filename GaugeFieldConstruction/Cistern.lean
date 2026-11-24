import GaugeFieldConstruction.Equinox
import GaugeFieldConstruction.Regulator
import GaugeFieldConstruction.Jupiter
import GaugeFieldConstruction.Tudor
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.Gleam
open Lattice RG Wilson Tree Finset
open scoped Matrix BigOperators Classical
variable {c n:Side}{r: Ratio c n} {y j:Site n}{T:Forest r}{G:Gauge}{A:Config G n}{θ:ℝ}

abbrev Loose (s:Signed)(T: Forest r)(A:Config G n):Site n→G.El:= (T.foldAt (pull s 0 A)) ∘ affine s⁻¹ 0
lemma wilted (s:Signed) (T:Forest r) (A:Config G n) : pull s⁻¹ 0 (tailored T (pull s 0 A))= gauge (Loose s T A) A:=by
 unfold Loose tailored; rw [Work.F05.pull_gauge_zero,pull_pull,mul_inv_cancel,affine,s.act_zero,add_zero,pull_id]; rfl -- kg of gauge
lemma swinging (s:Signed) (T:Forest r)(A:Config G n) : pull s 0 (gauge (Loose s T A) A)=tailored T (pull s 0 A):=by rw [←wilted,pull_pull,inv_mul_cancel]; simp only [affine,Signed.act_zero, add_zero, pull_id]
lemma flags_pale (h:r.parent j∉ broken r θ A): j∉ flags θ A:=by
 intro hj; apply Finset.disjoint_left.mp (legit h) _ hj; exact halo_spec.mpr ⟨r.embed (r.parent j),mem_singleton_self _,by have he:= near_root (x:=j) r rfl; exact he.trans (Nat.le_add_right ..)⟩
private lemma endpoints (r:Ratio c n)(x:Step)(a:Site n)(j:Site c)(p:r.parent a=j)(q:r.parent (a+x.vec)=j): InHouse r j (x.used a):=by obtain ⟨i,j'|j'⟩:=x; exact ⟨p,q⟩; exact ⟨(by simpa [Step.used,Step.vec,sub_eq_add_neg] using q),(by simp [Step.used,p])⟩
lemma native_price (s:Signed) (T:Forest r) -- remove dummy
 (A:Config G n){b:Edge (Site n)}(l:0≤θ)(w:2*(r.count.val+1)<n.val)
 (z:Site c)(u:z∉broken r θ (pull s 0 A))(t:r.parent (affine s⁻¹ 0 b.1)=z)(f:r.parent (affine s⁻¹ 0 (b.1+step b.2))=z): G.chord ((gauge (Loose s T A) A) b) ≤ suitedFee r.count.val θ:=by
 let V:=pull s 0 A; let X:= tailored T V; let g:Step:=(posDir b.2).rotate s⁻¹; let o:=affine s⁻¹ 0 b.1
 have hz:InHouse r z (g.used o):= endpoints r g o z t (by unfold g o; rw [Step.vec_rotate,Step.vec_pos, show affine s⁻¹ 0 b.1+s⁻¹.act (step b.2)=affine s⁻¹ 0 (b.1+step b.2) by simp [affine]]; exact f)
 have hV:z∉ broken r θ X:=by rw [show broken r θ X=broken r θ V by unfold X tailored broken; rw [malaise_home]]; exact u
 have hp : G.chord (X (g.used o)) ≤ suitedFee r.count.val θ:=by
    let i:=tailor_cut T V; rw [show X=_ from i] at hV ⊢; exact (purified l hV w hz)
 rw [←wilted]; change G.chord (g.read X o) ≤ _; unfold Step.read; split_ifs; · exact (G.chord_inv _).trans_le hp
 exact hp
end YM.Gleam
namespace YM.CF.Sour.SliceRoof
open Finset Function Lattice Wilson RG Branch Skye Scree Cube Tenant Tulip Lat Rush Spire
open YM.Gleam Tree
open scoped BigOperators Classical Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {c n:Side}{r:Ratio c (More n)}{T:Forest r}{S:Loom n}{a b d u t θ:ℝ}{A:Orbit n}{k m:ℕ}
local notation "E"=> SU.group
lemma arc (s:Signed){N:Side}(x y:Site N): separation (affine s 0 x) (affine s 0 y)=separation x y:=by simp only [affine, add_zero, separation_signed]
lemma native (s:Signed){N:Side}(x:Site N): affine s⁻¹ 0 (affine s 0 x)=x:=by simp only [affine, add_zero,Signed.inv_act]
lemma span_pale (V:Orbit n)(s:Signed)(h:Skye.Roof n t d k S)(l:0≤ θ)(u:θ≤  t)(p:2*(r.count.val+1)<(More n).val) (w:k≤ m) (T:Forest r)(x:Site (More n))
 (g:YM.Gleam.Safe r (broken r θ (pull s 0 V.1)) (hallBill m) (affine s⁻¹ 0 x)): BPress.chord.Close (Lattice.gauge (Loose s T V.1) (S V)) 1 (bayS _ x m) (suitedFee r.count.val θ):=by
 intro i y z; change _∈bayS _ _ _ at y z; let B:= pull s 0 V.1; let a:=affine s⁻¹ (0:Site (More n)); let c:=r.parent (a x)
 have hp(j)(h:separation x j≤ hallBill m) : r.parent (a j)=c:=g.2 _ ((arc s⁻¹ x j).le.trans h)
 have hy(j)(e:j∈bayS (More n) x m): separation x j≤ m:= by exact (bay_mem ..).1 e
 have ht:m≤ hallBill m:=by unfold hallBill Sequest; omega -- only height. tune
 have hu:(S V) i=V.1 i:=by
    apply h.lamp; apply Finset.disjoint_left.mpr; intro j p f; have he : j∈ flags θ V.1:=by obtain ⟨p,h,q⟩:= (flags_spec ..).1 p; exact (flags_spec ..).2 ⟨p,h,lt_of_le_of_lt u q⟩
    rw [← Work.H03.flags_send s 0] at he; obtain ⟨q,h,rfl⟩:= mem_image.mp he; obtain ⟨i',p,e⟩:= halo_spec.mp f
    have h₀:r.parent q=c:=by rw [← native s q]; -- q appears? c independent
                             apply hp; apply (separation_triangle _ i' _).trans; have hi:i'∈ bayS (More n) x m:= insert_subset_iff.mpr ⟨y,singleton_subset_iff.mpr z⟩ p; have hv:=hy _ hi; simp only [hallBill,Sequest]; omega
    apply flags_pale (r:=r) (h₀.symm ▸ g.1) h
 change BPress.chord (gauge _ _ i) 1 ≤  _; rw [BPress.chord.one,show gauge (Loose s T V.1) (S V) i=gauge (Loose s T V.1) V.1 i by unfold Lattice.gauge; rw [hu]]; exact native_price s T V.1 l p c g.1 (hp _ ((hy _ y).trans ht)) (hp _ ((hy _ z).trans ht))
end YM.CF.Sour.SliceRoof
end
