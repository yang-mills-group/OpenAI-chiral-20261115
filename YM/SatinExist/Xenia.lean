import YM.SatinExist.PalmGroves
set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
namespace Xara
variable (K:Calibration)(S T:Finset Cover)(x y:Cover)(s t:Fin 3)(a b c d:SU.F)(i j:Fin 2)
local notation "Ω"=> Dome K
def bum : Ω:= by
 let X:=removal K x (dnSpin i) (Bun s a); let Y:=creation K y (upSpin j) (Bun t b)
 refine ⟨X*Y,broadCompile K {nodeC x,nodeC y} ?_⟩
 exact InTest.mul (InTest.remover _ (dn_half i) (by simp)) (InTest.creator _ (up_half j) (by simp))
lemma bum_bay(hx:nodeC x∈S)(hy:nodeC y∈S): bum K x y s t a b i j∈ bay K S true:= by
 apply (locates ..).2; exact InTest.mul (InTest.remover _ (dn_half i) hx) (InTest.creator _ (up_half j) hy)
lemma bum_mat: PureMatter K (bum K x y s t a b i j):= fun _ _ _=>rfl
variable (E: Dome K→ₗ[ℂ]ℂ) (g:Cover→SU.E)
lemma bum_ward {z z':ℂ}(p:Sends (g (nodeC x)) a b z)(q:Sends (g (nodeC y)) c d z'):
    pennant K g ((z * star z') • bum K x y s t b d i j) = bum K x y s t a c i j:=by -- pennant circular F=source, source spin after on torus equals twist dest
 let S:Finset Cover:={nodeC x,nodeC y}; refine appointed K S g _ _ ?_ (bum_bay K _ x y _ _ _ _ _ _ (by simp [S]) (by simp [S]))
 intro n h u v
 let N:= K.c n
 let X:=fun i s a=>basisC N x (dnSpin i) (Bun s a); let Y:=fun i s a=>basisC N y (upSpin i) (Bun s a); change (z*star z') • (Fock.remove (X i s b)*Fock.create (Y j t d))=_
 change _=twist _ (Fock.remove (X i s a)*Fock.create (Y j t c)); rw [map_mul,twist_remove, twist_create, show acts (tradew N h).val (X i s a)=star z • X i s b from basisMove _ _ _ _ _ _ _ h ((u (nodeC x) (by simp [S])).symm ▸ p), show acts (tradew N h).val (Y j t c)=star z' • Y j t d from basisMove _ _ _ _ _ _ _ h ((u (nodeC y) (by simp [S])).symm ▸ q)]
 unfold Fock.remove; simp only [map_smul,star_smul,star_star, Matrix.mul_smul, Matrix.smul_mul,smul_smul]; rw [mul_comm z]
variable {E}
variable (f:Dome K)(r: MatterWard K E) (F:PureMatter K f) (o:f∈bay K S true)(u:nodeC x ∉ S)
include r F o u s t i j
lemma same_diag (a b:SU.F) : E (bum K x x s t a a i j*f)= E (bum K x x s t b b i j*f):=by
 by_cases h:a=b
 · rw [h]
 obtain ⟨k,p⟩:= patchSwap a b h
 let g:Cover→SU.E:=Function.update 1 (nodeC x) k; have u':g (nodeC x)=k:=Function.update_self ..
 have t':= bum_ward K x x s t a b a b i j g (u'.symm ▸ p) (u'.symm ▸ p); simp only [star_neg,star_one, neg_mul_neg,one_mul,one_smul] at t'
 have he: pennant K g f=f:= fixed_local K S g (fun i v=> Function.update_of_ne (fun (e : i=nodeC x)=>u (e ▸v)) ..) o
 have hp:= r g _ (matterPure_mul K (bum_mat K x x s t b b i j) F); rw [map_mul,t',he] at hp; exact hp
include a b
lemma not_diag (p:a≠b) : E (bum K x x s t a b i j * f)=0:=by
 obtain ⟨k,v,w⟩:= dualD a b p; let g:Cover→SU.E:= Function.update 1 (nodeC x) k; have u':g (nodeC x)=k:=Function.update_self ..
 have t':= bum_ward K x x s t a a b b i j g (u'.symm ▸ v) (u'.symm ▸ w); have hx:star (-Complex.I)=Complex.I:=by simp [Complex.star_def]
 let d:= bum K x x s t a b i j
 have hv:pennant K g (-d)= d:=by simpa only [hx,Complex.I_mul_I,neg_smul,one_smul] using t'
 have he: pennant K g f=f:= fixed_local K S g (fun i v=> Function.update_of_ne (fun (e : i=nodeC x)=>u (e ▸v)) ..) o
 have hp:= r g _ (matterPure_mul K (bum_mat K x x s t a b i j) F); rw [map_neg,neg_eq_iff_eq_neg] at hv; rw [map_mul,show pennant K g d = -d from hv,he,neg_mul,map_neg] at hp; exact (neg_eq_self.mp hp) -- tune d unfold
lemma offNode (p:x ≠ y) (q:nodeC y ∉ S) : E (bum K x y s t a b i j*f)=0:=by
 let X:Finset Cover:={nodeC x}; let Y:Finset Cover:={nodeC y}; let g:Cover→SU.E:= Function.update 1 (nodeC x) SU.central; have u':g (nodeC x)=SU.central:=Function.update_self ..
 have hw: nodeC x ≠ nodeC y:=by intro h; apply p; unfold nodeC at h; exact nsmul_right_injective (by decide) (add_right_cancel h) -- tune
 have h:Disjoint Y X:= Finset.disjoint_left.mpr (by simp [X,Y,Ne.symm hw]); let χ:= phaseName false; let B:= bum K x y s t a b i j
 have hk:B.val∈ RawPair K false Y X:=Submodule.subset_span (show B.val∈_ from ⟨_,pocket_removal K false X (Finset.mem_singleton_self _) (bun' s a) (dn_half i),_, pocket_creation K false Y (Finset.mem_singleton_self _) (bun' t b) (up_half j),rfl⟩)
 have hz:= pocket_charge K false Y X (Y∪X) g (Finset.Subset.refl _) (fun i p=>Function.update_of_ne (by intro e; rw [Finset.mem_singleton] at p; exact hw (e.symm.trans p)) ..) (fun i p=>(Finset.mem_singleton.mp p).symm ▸ u') hk
 have ht:pennant K g B= χ • B:= appointed K _ g B _ hz (.smul _ (raw_test K false _ _ hk|>.1)) -- membership def
 have he: pennant K g f=f:= fixed_local K S g (fun i v=> Function.update_of_ne (fun (e : i=nodeC x)=>u (e ▸v)) ..) o
 have hp:=r g (B*f) (matterPure_mul K (bum_mat K x y s t a b i j) F); rw [map_mul,ht,he,smul_mul_assoc,map_smul,smul_eq_mul] at hp; change E (B*f)=_
 by_contra k; exact pname_ne false (mul_right_cancel₀ k (hp.trans (one_mul _).symm))
#check @same_diag
#print axioms offNode
#check @same_diag
#print axioms not_diag
end Xara
end YM.CF.Buffered.Afterglow.Six
