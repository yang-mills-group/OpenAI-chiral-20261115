import Merino.Brooch.Tour
import Merino.Salon
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxRecDepth 2500
set_option maxHeartbeats 600000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Tiara
open Function Filter Metric SU Lat Lattice Cube Finset Spire Scroll Tulip Skye Window Vale Girt Buffered Fock
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Branch Sault Dial Vow BProof Reed Brooch Thera Kennel Hest

variable {N:Side}

variable {n:Type*} [Fintype n][LinearOrder n]
 {V:UNI n}{r b:Bool}{Y s t:Finset n}{i:n}{j:Bool}{P:Fock.FC n}


lemma slipFine (u:Fine s t j P)(b:Bool):Fine s t j (windX b P):=by
 induction u with
 | empty => simp [windX];exact .empty _
 | one => rw [win_i];exact .one
 | seed i p =>
   have e:windX b ((think s).term i)=(think s).term i:=by
      by_cases v:i∈s
      · rw [show (think s).term i=put i from if_pos v,win_up]
      rw [show (think s).term i= -takeF i from if_neg v,takeF]
      have h(X:FC n):windX b (-X)= -windX b X:=by cases b <;> simp [windX]
      rw [h,win_s,win_up]
   rw [e];exact .seed _ p
 | grow _ _ a c => rw [win_m];exact a.grow c
 | add _ _ a c => rw [win_a];exact a.add c
 | scale _ _ a => rw [win_c];exact a.scale _
lemma shuffles (e:twist V (cutM t)=cutM Y)
 (a:twist V (cutM s)=cutM s) (u:Fine s t j P):
 Fine s Y j (twist (quantU V) P):=by
 have hy{g h:Finset n}(k:twist V (cutM g)=cutM h){x:Ket n}
   (l: withinM g x):withinM h (acts V.val x):=by
    unfold withinM; rw [←act_mul,←k,twist_product,act_mul,l]
 induction u with
 | empty => rw [map_zero];exact .empty _
 | one => rw [map_one];exact .one
 | seed i p =>
   have z:=hy e (within_basis _ _ p)
   by_cases f:i∈s
   · rw [show (think s).term i=put i from if_pos f,←create_put,twist_create]
     exact fine_create _ (hy a (within_basis _ _ f)) z
   rw [show (think s).term i= -takeF i from if_neg f,map_neg,←remove_take,twist_remove]
   have a':twist V (cutM sᶜ)=cutM sᶜ:= by rw [dim_cut,map_sub,map_one,a]
   exact fine_neg (fine_remove _ (hy a' (within_basis _ _ (mem_compl.mpr f))) z)
 | grow _ _ v w=>rw [map_mul];exact v.grow w
 | add _ _ v w=>rw [map_add];exact v.add w
 | scale _ _ v=>rw [twist_scalar];exact v.scale _
lemma creasing (e:twist V (cutM t)=cutM Y)
 (a:sings b V (cutM s) = swapX r (cutM s))(u:Fine s t j P):
 Fine s Y j (tourP V b r P):=by
 have c:windX b (cutM s)=cutM s:= by
    cases b
    · rfl
    change cc _=_
    ext;rw [cc_apply,cutM]; simp [Matrix.diagonal_apply];split<;>simp
 rw [singT,c] at a
 cases r
 · exact shuffles e a (slipFine u b)
 change twist V (cutM s)=1-cutM s at a
 have k:twist V (cutM sᶜ)=cutM s:=by rw [dim_cut,map_sub,map_one,a];abel
 exact Fine.arrive e k (slipFine u b)

open Hive Levier
lemma sewn (s:Sweep N){P:FC (Single N)}{j:Bool}{A:Support (More N)}
    (h:Fine (Tset N) (modesIn N A) j P):
    Fine (Tset N) (modesIn N (Bide.regionD s A)) j (teen s P):=by
 rw [←region] at h ⊢
 have p:=tick_move s
 rw [touchP] at p
 exact creasing (Bide.eligible ..) p h
/-- All sweeps, even those incorporating charge. -/
lemma inlay (s:Sweep N){F:Evaluation N}{A}
 (h:LicenseY A F) : LicenseY (mount s A) (Bide.move s⁻¹ F):=by
 have j:= outAllowed s (allowedX h)
 refine ⟨AtSupport.fromEval _ j.bounded j.reads
   (fun V=> sewn s⁻¹ (h.loc.allV (flashA s⁻¹⁻¹ V,flashA s⁻¹⁻¹ V))),
   j.bounded, fun g x=>?_⟩
 change teen _ (F (flashA s⁻¹⁻¹ _))=twist _ (teen _ (F (flashA s⁻¹⁻¹ _)))
 rw [inv_inv,revG,h.gauge_x]
 let l:=fun i=>polarT s.charge (g (boxA s i))
 change teen s⁻¹ (Hive.Gaze l (F _))=Hive.Gaze g _
 rw [yoT _ _ _ (Bide.plain (allowedX h) _)]
 congr 2
 funext i
 change polarT s.charge (polarT s.charge (g (boxA s (boxA s⁻¹ i))))=g i
 rw [sitU, Equiv.apply_symm_apply,polar_t,Bool.xor_self];rfl

end YM.CF.Merino.Tiara
