import GaugeFieldConstruction.RankClasses
-- Chart column receipt is invariant to rescaling/payment conventions.
-- Exact Scan statements over complex readings; use Vouchers, no Gaussian software trust.
-- Description in the construction notes.
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.U1.TableDictionary
open Finset Function Raw Cauchy Row Record Vouchers Certificate Submodule
open scoped BigOperators
variable {M B Q : Type*} [AddCommGroup B][AddCommGroup Q][Module ℂ B][Module ℂ Q]
-- elementwise scaling relation (nonzero factors may differ per column)
inductive Tracks : List B → List B → Prop where
 | nil : Tracks [] []
 | step {p : ℂ} (hp:p≠0)(b:B){x y:List B}(h:Tracks x y): Tracks (b::x) ((p • b)::y)
namespace Tracks
variable {x y: List B}
lemma transfer (F:B→ₗ[ℂ] Q) (t:Tracks x y) : Tracks (x.map F) (y.map F) :=by
 induction t with
 | nil=>exact Tracks.nil
 | step p b q e=>rw[List.map_cons,List.map_cons,map_smul];exact Tracks.step p _ e -- tune
lemma combine (t:Tracks x y){a b:List B}(u:Tracks a b):Tracks (x++a) (y++b):=by
 induction t with
 | nil=>exact u
 | step hp _ _ e=>exact Tracks.step hp _ e
lemma slice (t:Tracks x y)(b:List Bool):Tracks (pick b x) (pick b y):=by
 induction t generalizing b with
 | nil=>cases b <;> exact Tracks.nil
 | step hp c q I=>
   match b with
   | [] => exact Tracks.nil
   | false :: a=> exact I _ -- tune
   | true :: a=> exact Tracks.step hp _ (I a)
lemma charted (t:Tracks x y) (b:List Bool) (H:Submodule ℂ B)(s:scan x b H):scan y b H:=by
 induction t generalizing b H with
 | nil => exact s
 | @step p hp a l w t I =>
   have he (U:Submodule ℂ B) : p • a∈U ↔ a∈U:= by
     refine ⟨fun z=>?_,fun z=>U.smul_mem _ z⟩
     rw[←inv_smul_smul₀ hp a]; exact U.smul_mem _ z
   have xeq : span ℂ {p • a}=span ℂ {a}:=le_antisymm
      ((span_singleton_le_iff_mem ..).mpr ((he _).mpr (mem_span_singleton_self _)))
      ((span_singleton_le_iff_mem ..).mpr ((he _).mp (mem_span_singleton_self _))) -- tune
   match b with
   | [] => exact False.elim s
   | true :: c=> exact ⟨mt (he _).mp s.1, xeq.symm ▸ I _ _ s.2⟩
   | false :: c=> exact ⟨(he _).mpr s.1, xeq.symm ▸ I _ _ s.2⟩
end Tracks
section Scan
-- Lift Scan to image by inj.
lemma grows (F:B→ₗ[ℂ]Q)(h:Injective F)(l b)(H:Submodule ℂ B)(u:scan l b H):scan (l.map F) b (map F H):=by
 induction l generalizing b H with
 | nil => cases b<;>exact u
 | cons a v I=>
   have w : F a∈map F H ↔ a∈ H:= ⟨by rintro ⟨p,hp,w⟩; rwa[← h w], fun z=>⟨a,z,rfl⟩⟩
   have xeq : map F (H⊔span ℂ {a})=map F H ⊔ span ℂ {F a}:=by rw[Submodule.map_sup,map_span]; simp
   match b with
   | []=>exact False.elim u
   | true::b => exact ⟨mt w.mp u.1, xeq ▸ I _ _ u.2⟩
   | false::b => exact ⟨w.mpr u.1, xeq ▸ I _ _ u.2⟩
lemma pivot_image (F:B→ₗ[ℂ] Q)(h:Injective F) {x y:List B}(t:Tracks x y){b: List Bool}(p:Scan0 x b) : Scan0 (y.map F) b:=by
 have w:= grows F h _ _ _ (t.charted b _ p); rw[Submodule.map_bot] at w; exact w
end Scan
section
variable {O U S : Type*} (C:S→J U→ₗ[ℂ]ℂ)(h:DeterminedBy C)
/-- Upgrade columns to full chart evaluated readings, all output components. -/
def photo (O:Type*) : (O→J U)→ₗ[ℂ] S → O → ℂ := LinearMap.pi fun s=>LinearMap.pi fun k=> C s ∘ₗ LinearMap.proj k
include h
lemma paid_photo : Injective (photo C O):=fun _ _ H=>funext fun i=>ext_jet h fun s=>congr_fun (congr_fun H s) i
omit h
variable [Fintype M] [DecidableEq M] [DecidableEq O](A:Labels M)(D:Labels O)(f:M→ J U)
abbrev xfactor (w:M×O) := ((A.tensorProd D).orbit ℂ w w)⁻¹
/-- Manusc columns, normalized perm impulse once. -/
def payment (w:M×O): M×O→ℂ:= xfactor A D w • (A.tensorProd D).orbit ℂ w
lemma proper_one (p:M×O)(t:(A.tensorProd D).coheres p)(s:(A.tensorProd D).evenAt p)(σ:Equiv.Perm Axis) :
    payment A D p ((A.tensorProd D).move (unsigned σ) p)= pay ((A.tensorProd D).cost (unsigned σ) p) (1:ℂ):=by
 let X:=A.tensorProd D
 have e:X.orbit ℂ p∈ X.fixed ℂ := X.orbit_mem p s
 have z:= (X.fixed ℂ).smul_mem (xfactor A D p) e
 change payment A D _∈ _ at z -- tune
 change payment A D p (X.move (unsigned σ) p)=_
 rw [(X.fixed_def ..).mp z]
 have ht: payment A D p p = 1:= inv_mul_cancel₀ (X.not_zero_self p t); rw[ht]
lemma unpaid (p j : M×O)(h:∀ σ, (A.tensorProd D).move (unsigned σ) p≠j): payment A D p j=0:=by
 rw [payment, Pi.smul_apply, Labels.orbit_value, Finset.sum_eq_zero,smul_zero]; intro k _; rw[if_neg (Ne.symm (h k))]
abbrev receiptMat (v: List (M×O)):= v.map fun w=> Record.dot f (payment A D w)
lemma transfers (v: List (M×O))(w:∀ i∈v, (A.tensorProd D).coheres i):
    Tracks (v.map (Record.column D A f)) (receiptMat A D f v):=by
 induction v with
 | nil => exact Tracks.nil
 | cons i t I=>
   change Tracks (_::_) (Record.dot f (payment A D i) :: _)
   rw[payment,map_smul]; exact Tracks.step (inv_ne_zero ((A.tensorProd D).not_zero_self i (w _ (by simp)))) _ (I (fun i p=>w _ (by simp[p])))
end
end YM.GaugeFieldConstruction.U1.TableDictionary
