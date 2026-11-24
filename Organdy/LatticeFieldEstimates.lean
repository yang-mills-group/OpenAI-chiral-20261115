import Organdy.Stylus
import Zephyr.Chern.Bends
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Pressure Wilson Work.F03 Next.Rank.Spindle Payne

open Kea
def nebi:Matrix SU.F SU.F ℂ:= Matrix.diagonal (fun i=>Complex.I * dye.val i)
def latticeFieldEstimates:SU.group.Color:= SU.group.projectColor nebi

lemma openUp (t:ℝ):
 SU.group.mat (arc t)=NormedSpace.exp (t•nebi):=by
 have p:t•nebi=Matrix.diagonal (fun i=>(t:ℂ)*(Complex.I*dye.val i)):=by
   ext i j;by_cases e:i=j
   · subst j; simp [nebi,Complex.real_smul]
   simp [nebi,e]
 rw [p,Matrix.exp_diagonal]
 change Matrix.diagonal (fun i=> Complex.exp (((diluted t).val i : ℂ)*Complex.I))=_
 congr 1
 funext i
 rw [Pi.coe_exp,Complex.exp_eq_exp_ℂ]
 congr 1; unfold diluted; simp only [Complex.ofReal_mul]; ring
lemma eye (t:ℝ):
   arc t=SU.group.lieExp (t•latticeFieldEstimates):=by
 have h: nebi∈ SU.group.lie:= show SU.group.Generates nebi from fun u=> ⟨_,openUp u⟩
 apply SU.group.mat_injective
 rw [openUp,SU.group.mat_lieExp,map_smul,latticeFieldEstimates,SU.group.colorMat_project_self h]
 rfl

def hueD (N:Side):Dir (More N):= fun x=>stream N (x.1,axisEquiv.symm x.2) • latticeFieldEstimates
lemma recreate (N:Side)(t:ℝ):
 petals (stream N) t=represent (t•hueD N):=by
 funext e
 rw [petals,represent,RG.increment,eye,Pi.one_apply,mul_one]
 simp only [collect,hueD,Pi.smul_apply,←coord_map,axisEquiv.symm_apply_apply, smul_smul,mul_comm t]

def decree (y:Tint) :ℝ :=
    flux (step y.1.val.1) (step y.1.val.2)*latticeFieldEstimates y.2

variable {i:ℕ}
lemma baroque (p:4*i+1<N.val)
  (u:Chip (More N))(m: separation u.1.1 1≤ i):
  blush (hueD N) u = decree (dot u):=by
 rcases u with ⟨⟨x,w⟩,j⟩
 have g(y:Site (More N))(b:Axis): parts G 1 (hueD N) j (y,coord b) =
     twistAt (rel y +1) b *latticeFieldEstimates j:=by
   unfold parts hueD
   rw [←coord_map,axisEquiv.symm_apply_apply]
   rfl
 change (Exterior.d 1 (More N) *ᵥ parts G 1 (hueD N) j) (x,plaquette w)= flux (step w.val.1) (step w.val.2) * latticeFieldEstimates j
 rw [d_plaquettes,g,g,g,g]
 have h(j:Axis): rel (x+step j)+1=(rel x+1)+step j:=by
   have e:=rel_add (step j) i (by rw [step_size];exact p) x m
   -- wrap step
   rw [wrap_step] at e
   rw [e];abel
 rw [h,h]
 simp only [twistAt,flux_left,flux_switch (step w.val.2) (step w.val.1)]
 ring
