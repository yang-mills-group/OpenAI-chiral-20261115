import Gingham.Ruff.Bud
import YM.SU5.FiniteGaugeData.Tower.Baggage
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Buffered Afterglow Satin Tapestry
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
attribute [local instance] opCStarAlgebra
open Pastry


open Tower SlabMark
variable {K:Calibration}{S T:Finset Cover}{C D:ℝ}{H:Bool}

abbrev Cluster (K:Calibration) := Option ℕ → Buffered.Family K

/-- With uniform price at every size, including early. -/
structure Bouquet (S:Finset Cover)(C:ℝ)(H:Bool)(A:Cluster K):Prop where
 test(i): InTest K true S false (A i)
 pays(i):Flora K H (A i) C
 spills:∀δ:ℝ,0<δ→∀ᶠ n in atTop,pay (A (some n)-A none) δ

variable {A B:Cluster K}

lemma Bouquet.nonneg(b:Bouquet S C H A):0≤C:= pay_nonneg (F:=A none) (b.pays none).1
lemma Bouquet.expand(b:Bouquet S C H A)(h:S⊆T):Bouquet T C H A:=
  ⟨fun i=>(b.test i).mono h,b.pays,b.spills⟩
lemma Bouquet.dismount(b:Bouquet S C H A): Bouquet S C false A:=by
 refine ⟨b.test,?_,b.spills⟩
 intro i;obtain ⟨u,v,w,_⟩:=b.pays i
 exact ⟨u,v,w,fun _=>by contradiction⟩

lemma Bouquet.check(b:Bouquet S C H A):BQueue S (fun i=>A (some i)) (A none):=by
  have h(i):pay (A i) (C+1):=fun _ _=> le_trans ((b.pays i).1 ..)
          (le_add_of_nonneg_right zero_le_one)
  exact ⟨fun _=>b.test _,b.test _,⟨C+1,add_pos_of_nonneg_of_pos b.nonneg zero_lt_one,
           h _, Eventually.of_forall fun i=>h _⟩,b.spills⟩

lemma Bouquet.nil: Bouquet (K:=K) S 0 H 0:=
  ⟨fun _=>InTest.zero,
    fun i=> ⟨by simp,fun _ _ _=>(map_zero _).symm,fun _ _ _ _=>rfl,
                  fun _ _ _=>⟨0,(zero_smul ..).symm⟩⟩,
    fun _ t=> Eventually.of_forall fun _ m x=> by simp; exact t.le⟩

lemma Bouquet.addW(b:Bouquet S C H A)(c:Bouquet S D H B):
       Bouquet S (C+D) H (A+B):=by
   refine ⟨fun i=>(b.test i).add (c.test i),fun i=>?_,?_⟩
   · obtain ⟨u,v,w,x⟩:=b.pays i; obtain ⟨t,g,s,j⟩:=c.pays i
     change Flora K H (A i+B i) (C+D)
     refine ⟨pay_add u t,?_,?_,fun p n f=>?_⟩
     · intro m y z
       simp only [Pi.add_apply,map_add,v m y z,g m y z]
     · intro m y z t
       exact congrArg₂ (·+·) (w m y z t) (s m y z t)
     obtain ⟨a,r⟩:= x p n f;obtain ⟨c,t⟩:=j p n f
     exact ⟨a+c,by rw [add_smul,←r,←t];rfl⟩
   intro e t
   filter_upwards [b.spills _ (half_pos t),c.spills _ (half_pos t)]
       with i a f
   rw [Pi.add_apply,Pi.add_apply,add_sub_add_comm]
   exact (add_halves e) ▸ pay_add a f -- rw too much?
lemma Bouquet.scaleW (b:Bouquet S C H A)(z:ℂ):
       Bouquet S (‖z‖*C) H (z • A):=by
   refine ⟨fun i=>(b.test i).smul z,fun i=>?_,?_⟩
   · obtain ⟨u,v,w,x⟩:=b.pays i
     change Flora K H (z • A i) _
     refine ⟨pay_scale u z,?_,?_,fun p n f=>?_⟩
     · intro m y x';simp only [Pi.smul_apply,v m y x',twist_scalar]
     · intro m a t h;simpa only [Pi.smul_apply] using congrArg (z • ·) (w m a t h)
     obtain ⟨a,r⟩:= x p n f
     exact ⟨_,by rw [Pi.smul_apply,Pi.smul_apply,r];exact smul_smul ..⟩
   intro e t
   have h:0<e/(‖z‖+1):= by positivity
   filter_upwards [b.spills _ h] with i f
   rw [Pi.smul_apply,Pi.smul_apply,←smul_sub]
   exact fun m x=> (pay_scale f z m x).trans ((mul_le_mul_of_nonneg_right
     (le_add_of_nonneg_right zero_le_one) h.le).trans_eq (mul_div_cancel₀ e (by positivity:‖z‖+1≠0)))
lemma Bouquet.subW (b:Bouquet S C H A)(c:Bouquet S D H B):
        Bouquet S (C+D) H (A-B):=by
  simpa [sub_eq_add_neg] using b.addW (c.scaleW (-1))

lemma Bouquet.sumW {I:Type*}{G:I→Cluster K}{r:I→ℝ}(p:Finset I)
    (b:∀i∈p,Bouquet S (r i) H (G i)): Bouquet S (∑i∈p,r i) H (∑i∈p,G i):=by
 induction p using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty];exact Bouquet.nil
 | insert i p v ih=>
    rw [sum_insert v,sum_insert v]
    exact (b i (mem_insert_self ..)).addW (ih (fun j t=>b j (mem_insert_of_mem t)))

lemma Bouquet.moveW(b:Bouquet S C H A)(a:Axis)(z:ℤ):
 Bouquet (reflectedBox a z S) C H (fun i=>Tower.mirror K a z (A i)):=by
 have h:= (b.check.revolve a z)
 refine ⟨fun i=>axial K a z (b.test i),?_,h.saved⟩
 intro i
 obtain ⟨u,v,w,t⟩:=b.pays i
 refine ⟨pay_flips K (F:=A i) u a z,
         fun m=>covariant_reflected ((b.test i).support m) (v m) z a,?_,?_⟩
 · intro m x y p
   exact congrArg (theta _) (w m _ _ (show (reflFields a z x).fst=(reflFields a z y).fst by
     simp [reflFields,p]))
 intro p n x
 obtain ⟨c,r⟩:= t p n (reflFields a z x)
 exact ⟨star c,by rw [Tower.mirror, reflMark,r,theta_smul,theta_one]⟩

lemma Bouquet.shiftW(b:Bouquet S C H A)(a:Axis)(v:ℤ):
 Bouquet (plow K a v S) C H (fun i=>relocate K a v (A i)):=by
 have h:= (b.check.station a v)
 exact ⟨fun i=>flow_port K a _ (b.test i),
     ((b.moveW a 0).moveW a (gaugeT K v)).pays,h.saved⟩

lemma Bouquet.raised (b:Bouquet S C H A) (h:C≤D):
    Bouquet S D H A:=by
 refine ⟨b.test,?_,b.spills⟩
 intro i; obtain ⟨u,v,w,t⟩:=b.pays i
 exact ⟨fun _ _=>(u _ _).trans h,v,w,t⟩
