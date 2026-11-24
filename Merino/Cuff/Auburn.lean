import Merino.Cuff.Ink
import Zephyr.Chern.Bends
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Finset Lattice Wilson
open scoped InnerProductSpace Topology
variable {G:Gauge}{N:Side}

open _root_.Zephyr.Chern
open SU Lat Cube Tulip
open scoped Matrix.Norms.Frobenius
local notation "T0"=>group.Mat


def tinaDiag:T0:=Matrix.diagonal fun i=> Complex.I * dye.val i

lemma tina_same (t:ℝ): group.mat (arc t)=NormedSpace.exp (t • tinaDiag):=by
 have hx:group.mat (arc t)= (moor t).2:=congrArg Prod.snd (brand_arc t)
 rw [hx,tinaDiag,← Matrix.diagonal_smul,Matrix.exp_diagonal]
 change Matrix.diagonal _ = _
 congr 1


 funext i; simp [Complex.exp_eq_exp_ℂ,mul_comm]


lemma tina_G:tinaDiag∈group.lie:= group.mem_lie.mpr (fun t=>⟨arc t,tina_same t⟩)
def tina:group.Color:=group.colorIso.symm ⟨_,tina_G⟩
lemma tina_reads: group.colorMat tina=tinaDiag:=
 congrArg Subtype.val (group.colorIso.apply_symm_apply ⟨_,tina_G⟩)
lemma tina_line(t:ℝ): group.lieExp (t • tina)=arc t:=by
 apply group.mat_injective
 rw [tina_same,group.mat_lieExp,map_smul,tina_reads]

def zig (n:Side): RG.Directions group (More n):=fun i=>stream n i • tina

lemma petals_zig (n:Side)(t:ℝ):
   petals (stream n) t=RG.increment (1:Bkg (More n)) (t • zig n):=by
 funext i
 change Zephyr.Chern.arc (stream n i*t)=group.lieExp (t • stream n i • tina)*1
 rw [mul_one,smul_smul,tina_line,mul_comm t]

local notation "H"=>Stripe group
abbrev flav(P:PlaqAxes):group.Color:=flux (step P.val.1) (step P.val.2) • tina
def hueInk (h:H):ℝ:=dust h.2 (flav h.1)
variable {n:Side}

lemma zig_curl (x:Site (More n)) (v:PlaqAxes)
    (h:4*separation x 1+1<n.val):
    cref (x,v) (zig n)=flav v:=by
 let a:=v.val.1; let b:=v.val.2; let u:=rel x+1
 have e:cref (x,v) (zig n)=
     (zig n (x,a)+zig n (x+step a,b))-(zig n (x,b)+zig n (x+step b,a)):=by
   simp only [cref,square,Exterior.linkSum,posDir,negDir,Step.vec,Step.used,a,b]
   simp [sub_eq_add_neg]; abel_nf
 have g(i:Axis):rel (x+step i)+1=u+step i:=by
   rw [←wrap_step,rel_add _ _ (step_size _ ▸ h) _ le_rfl]
   unfold u; abel
 rw [e]
 simp only [zig,stream,twistAt,g,flux_left u,←add_smul,←sub_smul]
 change (flux u (step a) / 2+(flux u (step b)+flux (step a) (step b))/2 -
   (flux u (step b)/2 + (flux u (step a)+flux (step b) (step a))/2)) • tina=flux (step a) (step b) • _
 rw [flux_switch (step b) (step a)]
 ring_nf


lemma seam_same {T:Inky (Husk group (More n))}{k:ℕ}{C:ℝ}
    (u:Sheath 0 k C T)(b:4*(k+4)+1<n.val):
    dripQ T (cseed (zig n)) (cseed (zig n))=
    dripQ T (hueInk ∘ ridge) (hueInk ∘ ridge):=by
 have e (x:Site (More n))(h: separation 0 x≤k):4*separation x 1+1<n.val:=by
    have q:separation (0:Site (More n)) 1≤4:=by
       have l:1=wrap (More n) 1:=by funext i; change 1=((1:ℤ):ZMod _); rw [Int.cast_one]
       rw [l,separation,zero_sub,pdist_neg]
       exact (pdist_wrap ..).trans (by simp [Laurent.size,Axis])
    rw [separation_comm] at h
    have a:=separation_triangle x (0:Site (More n)) 1
    omega
 have g(i:Husk group (More n))(h:separation 0 i.1.1≤ k):
   cseed (zig n) i=hueInk (ridge i):=by
    rcases i with ⟨⟨x,v⟩,i⟩
    simp only [cseed,zig_curl x v (e _ h),hueInk]
 refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_
 by_cases v:T i j=0
 · rw [v,zero_mul,zero_mul]
 rw [g i (u.both v).1,g j (u.both v).2]; rfl
end YM.CF.Merino.Cuff

