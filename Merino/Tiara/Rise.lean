import Merino.Tiara.Rider
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
open Levier Mir.Trip BProof Hive Swell Hem Merino.Mitre Plume
open Afterglow Tower Lifted Journey

-- Signed average = Z + displacement of a signed vector worth of stencils.
-- Also identify on arbitrary translated presentations.
variable (K:Calibration)(m:ℤ)(i:Axis)(x:ℤ)
def danceAt(i:Axis)(x:ℤ):Cover:=(2*x) • step i
lemma at_pose {h:LinksC→ℂ} :
 Tower.chime K i x (Plume.present K h)=
 Plume.present K (h ∘ Lattice.pull 1 (danceAt i x)):=by
 funext n v
 change theta _ (theta _ ((h (onC _ (fling i 0 _ (fling i x _ _)))) • 1))=_
 rw [theta_smul,theta_smul,theta_one,theta_one,star_star]
 simp only [Plume.present,scalar,comp_apply]
 congr 2
 have e(a:ℤ)(U:Pane (K.c n)):fling i a _ U=flashA (flipL i a) U:=(stir_e (plane i a) false U).symm
 rw [e,e,lights,fl_prod]
 -- pose gauge displacement 2*x
 rw [revoke]
 trans Lattice.pull 1 (danceAt i x) (onC (K.c n) v.1)
 · have j := slush 1 (danceAt i x) false v.1
   rw [show (assembly _).embed (taxiPlus (wrap (K.c n) (x • step i))).b =
       wrap (More (K.c n)) (danceAt i x) from ?_]
   · exact j.symm
   change (assembly (K.c n)).embed (wrap _ _) =_
   rw [Ratio.embed_wrap]
   change wrap _ (2 • (x • step i))=_
   rw [danceAt,mul_smul];congr 1
 rfl
def central (K:Calibration)(i:Axis)(x:ℤ): Horse K →ₗ[ℂ] Horse K where
 toFun:=Tower.chime K i x
 map_add' _ _:=chime_plus ..
 map_smul' _ _:=chime_scale ..

def tally (K:Calibration)(m:ℤ):(Axis→Horse K)→ₗ[ℂ]Horse K where
 toFun:=rolling K m
 map_add' x y:=by
   unfold rolling;rw [←sum_add_distrib]
   refine sum_congr rfl fun j _=>?_
   rw [Pi.add_apply,chime_plus,chime_plus];abel
 map_smul' c k:=by
   change rolling _ _ _= c • rolling _ _ _
   unfold rolling; rw [smul_sum]
   refine sum_congr rfl fun j _=>?_
   rw [Pi.smul_apply,chime_scale,chime_scale,smul_sub]

variable (c Q T:ℝ)(f:LinksC→ℂ)(J:Reins K)
def roses:Horse K:= ∑ σ:Signed,(ramp σ:ℂ) • scene K f J m σ c i x
def tassels:Axis→Horse K:= (Q:ℂ) • ∑ σ:Signed,(ramp σ:ℂ) • staff J σ
def allair:Horse K:=∑ σ:Signed,(ramp σ:ℂ) • air K f σ

lemma airChaste :central K i x ((c:ℂ) • allair K f)=present K (chaste (danceAt i x) c f):=by
 have a:(c:ℂ) • allair K f=present K (chaste 0 c f):=by
    funext n V
    simp only [allair,air,present,scalar,Pi.smul_apply,Finset.sum_apply,comp_apply,chaste]
    rw [mul_smul, sum_smul]
    congr 1
    apply sum_congr rfl
    intro σ _
    rw [mul_smul]
 rw [a,show central K i x _ = _ from at_pose K i x]
 have e: chaste 0 c f ∘ Lattice.pull 1 (danceAt i x)=chaste (danceAt i x) c f:=by
    ext1 V;simp [chaste,Plume.snow,Lattice.pull_pull,Lattice.affine]
 rw [e]

/-- Literal (128) equation with both readings on the same stencils. -/
lemma sword (scale:c=T*Q):
 roses K m i x c f J=
   present K (chaste (danceAt i x) c f) +
    (T:ℂ) • Tower.chime K i x (rolling K m (tassels K Q J)):=by
 rw [← airChaste]
 change _= _+ (T:ℂ) • central K i x (tally K m (tassels K Q J))
 unfold allair tassels
 rw [map_smul,map_sum,map_smul,map_smul,map_sum,map_sum,smul_smul,←Complex.ofReal_mul,
      ←scale,smul_sum,smul_sum,←sum_add_distrib]
 unfold roses
 apply sum_congr rfl
 intro σ _
 rw [map_smul,map_smul,map_smul]
 change (ramp σ:ℂ) • (central K i x) ((c:ℂ) • (air K f σ + tally K m (staff J σ)))=_
 rw [map_smul,map_add,smul_comm,smul_add,smul_add]

end YM.CF.Merino.Tiara
