import YM.SU5.FiniteGaugeData.Marked.Variation.Velvet

set_option autoImplicit false
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)(j:ℕ){R:ℕ}(p:LaurentRadius j G.count R)
local notation "I" => Iota G
local notation "T" => St G.count
local notation "V" => tub (brix j G.count)
def pick (k:I)(z:Cover)(r:T)(f:SU.Slot): Iota G:= (((k.1.1-wrap N z,r)),f)
def fall (k:I)(z:Cover)(r:T)(f:SU.Slot)(o:Lattice.Order)(x:Nom N P):ℂ :=
  wind (k.1.1-wrap N z) z * (tub (brix j G.count) z r k.1.2) *
    (SU.matter (travel x.1 (touch G true (k.1.1-wrap N z,r)) (runD true false G.count r k.1.2 z o))).val f k.2
-- include lobe products inside the sums to avoid operator coercions.
def half (k:I)(b:Bool)(x:Nom N P):Ket (Iota G):=((Fintype.card Lattice.Order:ℝ)⁻¹) •
    ∑ o:Lattice.Order,∑ r:St G.count,∑ z∈ LabelSet R,∑ f:SU.Slot,
      (let i:=pick G k z r f; lobe G b i i * fall G j k z r f o x * lobe G b k k) • basisKet (pick G k z r f)
include p
private lemma at_pick (k i:I)(b:Bool)(o:Lattice.Order)(r:T)(z:Cover)(x:Nom N P):
 (∑ f:SU.Slot,(let u:=pick G k z r f; lobe G b u u * fall G j k z r f o x * lobe G b k k) * (basisKet (pick G k z r f)).ofLp i)=
 lobe G b i i * drag G true false r k.1.2 z (tub (brix j G.count) z r k.1.2) o (unionP x) i k * lobe G b k k:=by
 rw [drag_entry G j x o r k.1.2]; split
 next v=>
    let l:= i.2; have h0:i=pick G k z r l:=by
       have he:i.1.1=k.1.1-wrap N z:=by rw [v.2,Prod.fst,(add_sub_cancel_right ..)]; -- tune
       change i=((_,r),i.2); exact Prod.ext (Prod.ext he v.1) rfl
    rw [h0,sum_eq_single l]; swap
    · intro a _ ha; have ht: pick G k z r l≠ pick G k z r a:= fun g=> ha (congrArg Prod.snd g).symm; rw [basis_apply, if_neg ?_]; simp; exact ht
    swap; · simp
    rw [basis_apply,if_pos rfl,mul_one]; rfl
 next h=>
    simp only [mul_zero,zero_mul]; apply sum_eq_zero; intro a _; apply mul_eq_zero_of_right
    rw [basis_apply,if_neg ?_]; intro e; apply h; change i= _ at e; rw [e]; simp [pick]
private lemma unusedD (k i:I)(o:Lattice.Order)(r t:T)(z:Cover)(x:Nom N P)(e:t≠k.1.2):
 drag G true false r t z (tub (brix j G.count) z r t) o (unionP x) i k=0:=by
 rw [drag_entry G j x]; split; swap; rfl
 next h=> exact False.elim (e (congrArg Prod.snd h.2).symm)
private lemma half_entry (k i:I)(b:Bool)(x:Nom N P):
 (half G j (R:=R) k b x).ofLp i=lobe G b i i * mosaic G true false (tub (brix j G.count)) (unionP x) i k * lobe G b k k:=by
 rw [half,mosaic_entry G j p]
 -- evaluation smul sums
 simp only [WithLp.ofLp_smul, WithLp.ofLp_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
 have he (o:Lattice.Order)(r:St G.count):
   ∑ t:St G.count,∑ z∈LabelSet R, drag G true false r t z (V z r t) o (unionP x) i k=
     ∑ z∈LabelSet R, drag G true false r k.1.2 z (V z r k.1.2) o (unionP x) i k :=by
   rw [Finset.sum_eq_single k.1.2 (fun m _ q=>Finset.sum_eq_zero fun w _=> unusedD G j p k i o r m w x q) (by simp)]
 simp_rw [at_pick G j p k i b,←sum_mul,←mul_sum,he,Complex.real_smul]; ring
lemma cloth_column (k:I)(M:Male)(x:Nom N P): acts (Peaks.cloth j M G (Peaks.unionP x)) (basisKet k)=half G j (R:=R) k true x+half G j (R:=R) k false x:=by
 apply PiLp.ext; intro i; rw [basis_act,cloth_entry,WithLp.ofLp_add,Pi.add_apply,half_entry G j p,half_entry G j p]
#check Complex.real_smul
