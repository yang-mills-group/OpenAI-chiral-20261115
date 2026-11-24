import Organdy.Parka

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

open Hive Levier Urn

variable (T:Shape) (b:Bool) (U:UNI SpinIdx)
def suede {K:Calibration}(T:Shape)(b:Bool)(U:UNI SpinIdx)(f:Buffered.Family K):Buffered.Family K:=fun m x=>
 (Urn.lotB b b (styleB_U U T (K.c m))) (f m ((stir (xtra b) T x.1),(stir (xtra b) T x.2)))

section
variable{K:Calibration}{f g:Buffered.Family K}{S:Finset Cover}
local notation "L"=>suede (K:=K) T b U
lemma suede_scale(a:ℂ):L (a • f)=a • L f:=by
 funext m v
 unfold suede
 rw [Pi.smul_apply,Pi.smul_apply,visage,Bool.xor_self]
 rfl
lemma suede_add:L (f+g)=L f+L g:=funext fun m=>funext fun x=>map_add _ _ _
lemma suede_mul:L (f*g)=L f*L g:=funext fun m=>funext fun _=>map_mul _ _ _
lemma suede_zero:L 0=0:=funext fun m=>funext fun _=>map_zero _
lemma suede_one:L 1=1:=funext fun m=>funext fun _=>map_one _
lemma suede_seed{c:PairsC→ℂ}(p:Coeff true S c):InTest K true (S.image T.motion) false (L (scalar K c)):=by
 let F:=drape T b; let G(x:PairsC):= c (F x.1,F x.2)
 have t: L (scalar K c)= scalar K G:=by
   funext m v
   unfold scalar suede
   rw [visage,map_one,Bool.xor_self]
   dsimp only
   rw [drape_seen,drape_seen];rfl

 rw [t]
 refine .seed ⟨fun _=>by contradiction,Env.along p.env ((drapeC ..).prodMap (drapeC ..)).measurable,fun x y a q=>?_⟩
 exact p.locus _ _ (drape_agree T b a) (drape_agree T b q)

lemma shallow_left (x:Cover)(i:SpinIdx)(l:SU.Slot):
 suede (K:=K) T false U (creation K x i l)= ∑ j,U.val j i • creation K (T.flee x) j l :=by
 funext n v
 simp_rw [Finset.sum_apply, Pi.smul_apply]
 change twist (quantU (styleB_U U T (K.c n))) (create _)=_
 rw [twist_create,sunWings,map_sum]
 simp_rw [map_smul];rfl

lemma shallow_right (x:Cover)(i:SpinIdx)(l:SU.Slot):
 suede (K:=K) T false U (removal K x i l)= ∑ j,star (U.val j i) • removal K (T.flee x) j l :=by
 funext n v
 simp_rw [Finset.sum_apply, Pi.smul_apply]
 change twist (quantU (styleB_U U T (K.c n))) (Fock.remove _)=_
 rw [twist_remove,sunWings]
 simp only [Fock.remove,map_sum,map_smul,star_sum,star_smul];rfl

lemma venture_left(x:Cover)(i:SpinIdx)(l:SU.Slot):
 suede (K:=K) T true U (creation K x i l)= -Complex.I • ∑ j,star (U.val j i) • removal K (T.flee x) j l:=by
 funext n v
 simp_rw [Pi.smul_apply, Finset.sum_apply,Pi.smul_apply]
 change theta (styleB_U U T (K.c n)) (windX true (create _))=_
 rw [Spire.stove,chord_dove,theta_upV,sunWings]
 simp only [Fock.remove,map_sum,map_smul,star_sum,star_smul];rfl

lemma venture_right(x:Cover)(i:SpinIdx)(l:SU.Slot):
 suede (K:=K) T true U (removal K x i l)= Complex.I • ∑ j,U.val j i • creation K (T.flee x) j l:=by
 funext n v
 simp_rw [Pi.smul_apply, Finset.sum_apply,Pi.smul_apply]
 change theta (styleB_U U T (K.c n)) (windX true (Fock.remove _))=_
 rw [show ∀ w:Ket (Single (K.c n)),windX true (Fock.remove w)=Fock.remove (dove true w) from ?_,
     chord_dove,theta_downV,sunWings,map_sum]
 · simp_rw [map_smul];rfl
 intro w
 rw [Fock.remove,Fock.remove,←Spire.stove];exact cc_star ..

open Reed
lemma faux_tint {s:Signed}(h:JetS s b b U):
 twist U (cutM plusHalf)=(if b then cutM plusHalfᶜ else cutM plusHalf):=by
 cases b
 · change twist U _=cutM _
   rw [raising,Fir.Adef.symm]
   exact angleX h true
 change twist U _=cutM _
 rw [dim_cut,raising,Fir.Adef.symm]
 have t: windX true Fir.Aop = Fir.Aop:=by
    rw [Fir.Adef,←raising];exact win_cut true _
 have p:=angleX h true
 change twist U (windX true Fir.Aop)=1-Fir.Aop at p
 rwa [t] at p

lemma inSuede {z:Bool}{s:Signed} (h:JetS s b b U)(hf:InTest K true S z f):
 InTest K true (S.image T.motion) z (suede T b U f):=by
 have t:=faux_tint b U h
 induction hf with
 | @creator x i a v w=>
   have p: nodeC (T.flee x) ∈ S.image T.motion:=mem_image.mpr ⟨_,w,Shape.mote ..⟩
   cases b
   · rw [shallow_left]
     refine InTest.sum _ _ (fun j _=>?_)
     by_cases c:j∈plusHalf
     · exact .smul _ (.creator _ c p)
     rw [show U.val j i=0 from Fine.entry (show twist U _= cutM plusHalf from t) v c, zero_smul]
     exact .zero
   rw [venture_left]
   refine .smul _ (InTest.sum _ _ fun j _=>?_)
   by_cases c:j∉plusHalf
   · exact .smul _ (.remover _ c p)
   rw [show U.val j i=0 from Fine.entry (show twist U _=cutM plusHalfᶜ from t) v (fun d=>c (mem_compl.mp d)),star_zero,zero_smul]
   exact .zero
 | @remover x i a v w=>
   have p:nodeC (T.flee x) ∈ S.image T.motion:=mem_image.mpr ⟨_,w,Shape.mote ..⟩
   cases b
   · have u:twist U (cutM plusHalfᶜ)=cutM plusHalfᶜ:=by simp [dim_cut,t]
     rw [shallow_right]
     refine InTest.sum _ _ fun j _=>?_
     by_cases c:j∉plusHalf
     · exact .smul _ (.remover _ c p)

     rw [show U.val j i=0 from Fine.entry u (mem_compl.mpr v) (fun d=>c (mem_compl.mp d)),star_zero,zero_smul]
     exact .zero
   have u:twist U (cutM plusHalfᶜ)=cutM plusHalf:=by rw [dim_cut,map_sub,map_one,t];change 1-cutM plusHalfᶜ=_;rw [dim_cut];abel
   rw [venture_right]
   refine .smul _ (InTest.sum _ _ fun j _=>?_)
   by_cases c:j∈plusHalf
   · exact .smul _ (.creator _ c p)
   rw [show U.val j i=0 from Fine.entry u (mem_compl.mpr v) c, zero_smul]
   exact .zero
 | seed p=>exact suede_seed T b U p
 | zero=>rw [suede_zero];exact .zero
 | one=>rw [suede_one];exact .one
 | add _ _ a d=>rw [suede_add];exact .add a d
 | mul _ _ a d=>rw [suede_mul];exact .mul a d
 | smul a _ u=>rw [suede_scale];exact .smul _ u
end
