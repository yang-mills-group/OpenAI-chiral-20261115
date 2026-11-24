import Gingham.Ruff.Apron
import Gingham.Ruff.Floss
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}
open Nacre

lemma prep_nonzero (a: Shape)(b:Bool)(U:UNI SpinIdx){i j:Single N}
    (p:(prepU a U (xtra b) N).val i j≠0): a.mills N (cabin i) = cabin j:= by
  rcases i with ⟨⟨x,i⟩,k⟩
  rcases j with ⟨⟨y,j⟩,l⟩
  change jump (Tofu a N) (fun i=>(milU a U (xtra b) i).val) (x,(i,k)) (y,(j,l)) ≠0 at p
  rw [jump_apply] at p
  split at p
  · assumption
  contradiction

lemma twist_WW (a:Shape)(b:Bool)(U:UNI SpinIdx)(x:Site N):
    let v:= prepU a U (xtra b) N
    twist v (WW (a.mills N x))=WW x:=by
  let v:= prepU a U (xtra b) N
  show twist v (WW _) = _
  rw [twist_formula,show v.val * WW _ = WW x * v.val from ?_,mul_assoc,v.property.2,mul_one]
  ext i j
  rw [WWi,WWj]
  by_cases h:v.val i j=0
  · simp [h]
  simp only [←prep_nonzero a b U h,a.mills_b.1.eq_iff]

-- center shift on matter tori; omits the -1 shift of negative direction nodes since describes even gauge centers
def finale (a:Shape) (x:Site N):Site N:=
 affine a.s (wrap N a.t) x
def gyre (s: Signed): Cover → Cover:=(incX s).flee


lemma gyre_perm (s:Signed)(x:Cover)(i:Axis):
    gyre s x (s.perm i)=if s.flip i then - x i -1 else x i:=by
  have v:=congr_fun ((incX s).mote x) (s.perm i)
  change (s.act ((2:ℕ)•x+1)+(2:ℕ) • (0:Cover):Cover) (s.perm i) = ((2:ℕ) • gyre s x+1 :Cover) (s.perm i) at v
  simp only [smul_zero,Pi.zero_apply,add_zero, Signed.act_at,Pi.add_apply,Pi.one_apply,two_smul] at v
  split
  · rename_i h;rw [if_pos h] at v; omega
  rename_i h; rw [if_neg h] at v;omega


lemma gyre_inv (s:Signed)(x:Cover):gyre s⁻¹ (gyre s x)=x:=by
  have t:= plait (incX s⁻¹) (incX s) x -- join=inc id
  have e:joinX (incX s⁻¹) (incX s) = incX 1 :=by
    simp [joinX,incX]
  rw [e] at t
  unfold gyre; rw [←t]
  have z:∀i,(incX 1).flee x i=x i:=by
    intro i; show gyre 1 x i = x i; simpa using gyre_perm 1 x i
  exact funext z

lemma gyre_apron (s:Signed){u:Side}{x:Cover}(h:x∈apron u):
    gyre s x∈apron u:=by
  apply apron_spec.mpr; intro i; obtain ⟨j,rfl⟩:=s.perm.surjective i
  have := apron_spec.mp h j
  rw [gyre_perm]; split <;> omega

lemma mill0 (a:Shape)(x:Site N)(y:Cover):
 a.mills N (x+wrap N y)=finale a x + wrap N (gyre a.s y):= by
  unfold gyre Shape.mills finale affine Shape.flee incX
  simp only [Signed.act_zero,Signed.act_add,map_add,zero_add,wrap_signed,add_zero]
  -- left private dune a, dune (incX)=...

  rw [add_assoc (a.s.act x),add_assoc (a.s.act x),add_left_comm (wrap N (a.s.act y))]
  rfl -- dune definitional uniqueness 


lemma twist_block (a:Shape)(b:Bool)(U:UNI SpinIdx)(u:Side)(y:Site N):
  twist (prepU a U (xtra b) N) (block u (finale a y))=block u y:=by
  let v:= prepU a U (xtra b) N
  rw [block,block,map_sum]
  symm; refine sum_bij (fun x _=>gyre a.s x)
    (fun _=>gyre_apron _) (fun x _ y _ h=>
      (LeftInverse.injective (g:=gyre a.s⁻¹) (gyre_inv a.s) h))
    ?_ (fun x _=> (mill0 a y x) ▸ (twist_WW a b U (y+wrap N x)).symm)
  intro x hx
  exact ⟨gyre a.s⁻¹ x, gyre_apron _ hx, by simpa using gyre_inv a.s⁻¹ x⟩


lemma finale_lag (s:Cover)(x:Site N): finale (lagX s) x=x+wrap N s:=by simp [finale,lagX,affine]

lemma mills_lag (s:Cover)(x:Site N): (lagX s).mills N x=x+wrap N s:=by
  have v:= mill0 (lagX s) x 0
  rw [finale_lag,show (lagX s).s=1 from rfl] at v
  have q:gyre 1 0=0:= funext fun i=>by simpa using gyre_perm 1 0 i
  simpa only [q,map_zero,add_zero] using v

