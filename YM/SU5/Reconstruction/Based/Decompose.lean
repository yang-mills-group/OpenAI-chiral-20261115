import YM.SU5.Reconstruction.Based.Separables
import YM.SU5.Reconstruction.Based.Markers
import YM.SU5.Reconstruction.Based.Forms
set_option autoImplicit false
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option maxHeartbeats 900000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Rooted
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Fock Lat Cube SU Spire Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Next.Free Bloch Drapes Lifted Skye Girt Nacre Sound Tapestry Satin MeasureTheory Rush
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
open WalkRoots Push.SectorMeasure
set_option quotPrecheck false
variable {S:Finset Cover}(R:RouteMap S)
variable {k:ℕ}(K:Calibration)(W:Window.Family)(p: Fin k → Cover)
variable {A:(Multiset Cover)→₀ Family K}
local notation "Γ" => raw S K W p
local notation "B" => Stitches K W p S
local notation "Ω" => A.support
variable {F: Family K}
variable (t:Breakdown (S:=S) K W p F A)
include t
lemma persist_visits {μ}(u:μ∈ A.support): ∃ l:List (Fin k), l≠[]∧ l.Nodup∧ ∃ w:Family K, Stitches K W p S (removal K) (creation K) l μ w:=
 Rooted.was_here K W p _ _ _ (Finsupp.mem_support_iff.mp u) (t.1 μ)
lemma persist_discriminates {μ ν}(u:μ∈ A.support)(e:ν∈ A.support)(h:μ≠ν): ∃ x:Cover, nodeC x∈ S∧∃ z:unitary ℂ,z.val^μ.count x≠ z.val^ν.count x:=by
 have hz:¬∀ x:Cover, μ.count x=ν.count x:=fun v=> h (Multiset.ext.mpr v)
 obtain ⟨x,g⟩:=not_forall.mp hz; refine ⟨x,?_,Mixing.discriminant _ _ g⟩; by_cases m:x∈μ; · obtain ⟨l,p,e,q,v⟩:= persist_visits K W p t u; exact v.reaches _ m
 have hu:x∈ν:=by by_contra d; exact g ((Multiset.count_eq_zero.mpr m).trans (Multiset.count_eq_zero.mpr d).symm)
 obtain ⟨l,p,e,q,v⟩:= persist_visits K W p t e; exact v.reaches _ hu
open Mixing
lemma paying_single (a: Tapestry.Neutral K F) (μ: Multiset Cover): Tapestry.Neutral K (A μ):= by
 let Q:= A μ; have p':A μ∈raw S K W p μ:= t.1 μ
 obtain ⟨m,u⟩:= (Buffered.separates K S).exists; let n:=K.c m; let v:Hosp S n:= ⟨u⟩
 apply Tapestry.onceNeutral (CF.Pannier.Chancel.FilTest (visible K W p μ S p')).widen v
 intro g x; let U:= quantU (tradew n g); let T:= twist U
 let D (j:Multiset Cover) := A j m (simultaneous g x)- T (A j m x)
 apply sub_eq_zero.mp; change D μ=0
 by_cases hm: μ∈ A.support; swap; · unfold D; rw [Finsupp.notMem_support_iff.mp hm]; simp
 apply Segregate.isolate_by_rot hm D
 · intro y hv e; obtain ⟨w,h,z,hz⟩:= persist_discriminates K W p t hm hv (Ne.symm e)
   let Cm(j:Multiset Cover):= z.val^j.count w; let Z:= quantU (toneUnit w z n); refine ⟨{ toFun:= twist Z, map_add':= fun _ _=> map_add _ _ _, map_smul':= fun _ _=> twist_scalar .. },Cm,hz,fun j _=> ?_⟩
   change twist Z (A j m (simultaneous g x)- _) = Cm j • _; rw [map_sub]; unfold D
   have e:= raw_eval w z K _ p v h (t.1 j) -- implicit argument U binder?
   let x':= A j m x; have et:twist Z (T x')= T (twist Z x'):= by unfold T; rw [←Fock.twin,← Fock.twin]; exact congrArg (fun i=> twist i x') (tone_kind w z g).eq
   rw [show twist Z (T (A j m x))= T (twist Z (A j m x)) from et, show twist Z (A j m x)= _ from e x, show twist Z (A j m (simultaneous g x))=_ from e _, show T _= _ from (show T (Cm j • x')= Cm j • T x' from twist_scalar ..), smul_sub] -- tune let W overshadow x'
 · unfold D; rw [Finset.sum_sub_distrib]; rw [← map_sum (twist U)]
   have e(v:Fields n): (∑ i∈Ω, A i m v)= F m v:= by rw [←t.2]; simp_rw [Finset.sum_apply]
   rw [e x,e (simultaneous g x)]; exact sub_eq_zero.mpr (a m g x)
end YM.CF.Buffered.Afterglow.Rooted
#print axioms YM.CF.Buffered.Afterglow.Rooted.paying_single
