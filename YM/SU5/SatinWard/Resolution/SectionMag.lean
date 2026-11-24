import YM.SU5.SatinWard.Resolution.ProbeDegree
import YM.SU5.SatinWard.Resolution.Trachea
set_option autoImplicit false
set_option synthInstance.maxSize 32000
noncomputable section
namespace Zephyr.Chern.IndexMag
open YM YM.Lattice YM.CF YM.Laurent CF.LitCurrent CF.LitCurrent.Chamber MeasureTheory Silk Filter Topology
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Classical Topology Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary
open Tulip
variable (d:Division)
abbrev LabelD (d: Division):Type:={x:SU.Slot//x∈ Finset.univ.filter fun i=> SU.charge i∈d} -- Decidable Pred must be stable across files; favor regular Classic.
abbrev RegionD(d:Division):Type:= SpinIdx × LabelD d
abbrev codeD : RegionD d→ IS := fun i=>(i.1,i.2.val)
abbrev moneyD {A:Type*}(F:Matrix IS IS A):= F.submatrix (codeD d) (codeD d)
def homeWeight :Op (LabelD d):= Matrix.diagonal fun i=> lock i.val
abbrev starD (d:Division):ℝ:= -(homeWeight d*homeWeight d).trace.re
local notation "Cab"=>homeWeight d
local notation "Ξ"=> (fun z=> moneyD d z)
local notation "α"=>codeD d
-- Convergence.HESS checkout directly.Fence retains all three. π.IndexMag.Client
variable {ι:Type*} {j:ℕ} {L:Filter ι}{X:Cross j L} {p:Stack} [L.NeBot]
lemma charm_pay {a r e:ℝ}{n:Side}(F:Oil n) (q:Tulip.Solo a r F e)(y:0<e){x:Cover} (u:StemA n) (i:RegionD d) (l:IS) (k:Fin 3) (p: SU.charge l.2 ∉ d): tuft F u (-x) 0 (codeD d i) l k=0 := by
 have g: tap F u (-x) 0 (α i) l =ᶠ[𝓝 0] fun _=>0:=by
    filter_upwards [petals_open y u] with v hv
    let Z:= petals u v; let Y:= F (profile Z); have hz:= Chamber.sits d Z q hv
    let V:= tag n (-x) (α i); let M:=tag n 0 l; have h : (markG d n * Y) V M=(Y*markG d n) V M:=congrFun (congrFun hz.eq V) M; rw [atLeft,atRight,if_pos (by simp only [Chamber.fortune, Finset.mem_filter, Finset.mem_univ, true_and]; exact (Finset.mem_filter.mp i.2.property).2),if_neg (by simp only [Chamber.fortune,Finset.mem_filter,Finset.mem_univ,true_and]; exact p)] at h; change _*Y V M=_; rw [h,mul_zero]
 let b:= (Bloom.constant 0).congr g; unfold tuft; rw [b.bud_eq]; fin_cases k<;>rfl
include X p in
lemma restrictBend (h:X.Relax p) (i:RegionD d) (l:IS) (k:Fin 3) (w:SU.charge l.2 ∉ d) (x:Cover) : seam x (p k) (codeD d i) l = 0:=by
 obtain ⟨a,r,e,u,k',v,t⟩:= X.oils; refine tendsto_nhds_unique_of_eventuallyEq (f:=fun n=> X.test x (codeD d i) l k n) (h ..) tendsto_const_nhds ?_; exact t.mono (fun i' p=>charm_pay d _ p v _ i l k w)

lemma sub_sum {A:Type*}[AddCommMonoid A](f:IS→A)(h:∀ i:IS,SU.charge i.2 ∉ d→ f i=0): (∑ i:RegionD d,f (codeD d i))=∑ i:IS,f i:=by
 rw [Fintype.sum_prod_type,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _
 let S:Finset SU.Slot:=Finset.univ.filter fun i => SU.charge i∈ d
 calc
  _ = ∑ v∈ S, f (i,v) := (Finset.sum_subtype S (p:=(·∈ S)) (fun _=>Iff.rfl) (fun x=>f (i,x))).symm
  _ = _ := Finset.sum_subset (Finset.subset_univ _) (fun a _ y=> h _ (fun k=> y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,k⟩)))
-- Or sum via equiv.
variable (h:X.Relax p)
local notation "Z"=> (1:Op SpinIdx) ⊗ₖ homeWeight d
include h in
lemma braidP (a b:ℕ)(t u: Fin 3)(x y:Cover) : moneyD d (braidE (p t) (p u) x y)=braidE (moneyD d (p t)) (moneyD d (p u)) x y:=by
 unfold braidE; ext i j; rw [moneyD,Matrix.submatrix_apply,Matrix.mul_apply,Matrix.mul_apply]; exact (sub_sum d _ (fun i' w=>(by rw [restrictBend d h i i' t w,zero_mul]))).symm
lemma waveValue{F:Coats IS}{f:Cover→ Cover→Op IS} (p:Fits F f):Fits (moneyD d F) (fun i j=> moneyD d (f i j)):= fun x i j=> p x (α i) (α j)
private lemma coreProfile : Z=Matrix.diagonal fun i=> lock i.2.val:=by ext i j; by_cases h:i.2=j.2<;> by_cases g:i.1=j.1<;>simp [Matrix.one_apply,homeWeight,Matrix.diagonal_apply,h,g,Prod.ext_iff]
private lemma cab_b (z:Op IS) : moneyD d (((1:Op SpinIdx) ⊗ₖ cab)*z)= Z * moneyD d z:=by rw [coreProfile,cab_diag]; ext i j; simp [moneyD,Matrix.diagonal_mul]
include h in
lemma scoreless : Gains (moneyD d (p 0)) (moneyD d (p 1)) (moneyD d (p 2)) ((1:Op SpinIdx) ⊗ₖ homeWeight d):=by
 let u:= h.toGains; refine ⟨?_,?_,?_⟩
 · have e:= waveValue d u.zero; simp_rw [braidP d h 0 0] at e; exact e
 · have hx :∀ (a b:Op IS),moneyD d (a+b)=moneyD d a+moneyD d b:= fun _ _=> rfl; have hv(t:ℂ)(a:Op IS): moneyD d (t • a)= t • moneyD d a:=rfl; have he:=waveValue d u.one; simp_rw [hx,cab_b,hv,braidP d h 0 0] at he; exact he
 have hx :∀ (a b:Op IS),moneyD d (a+b)=moneyD d a+moneyD d b:= fun _ _=> rfl; have hv(t:ℂ)(a:Op IS): moneyD d (t • a)= t • moneyD d a:=rfl; have he:=waveValue d u.two; simp_rw [mul_assoc,hx,cab_b,hv,hx,cab_b,hv,braidP d h 0 0] at he; simpa only [mul_assoc] using he
lemma end_snow(F:Streams): moneyD d (snow SU.Slot F)= snow (LabelD d) F:=by
 have ht(ι:Type)[Fintype ι][DecidableEq ι](X: Op SpinIdx)(u:Silk):True:=trivial
 rw [snow,snow]; change (2:ℂ)⁻¹ • ((Ξ (1:Coats IS))+Ξ (shade SU.Slot F))=_; have e:(Ξ (1:Coats IS))=1:=by
    apply Matrix.ext; intro i j; simp only [moneyD,Matrix.submatrix_apply,Matrix.one_apply]; apply if_congr _ rfl rfl; cases i; cases j; simp [codeD]

 rw [e]; congr 2
 apply Matrix.ext; intro i j; apply E_ext; intro v; change flash v (shade SU.Slot F) (α i) (α j)= flash v (shade (LabelD d) F) i j; rw [shadeF,shadeF]; by_cases h:i.2=j.2<;> simp [Matrix.one_apply,codeD,h] -- Subtype.ext_iff
include h in
lemma region_price (u:Streams)(v:p 0=snow SU.Slot u): (seam 0 (moneyD d (p 2))).trace=(-6) * (homeWeight d*homeWeight d).trace * Silk.τ (jac u):=by
 have q:= Gains.jet (scoreless d h); rw [v,end_snow] at q; exact q.receipt
#print axioms region_price
end Zephyr.Chern.IndexMag
