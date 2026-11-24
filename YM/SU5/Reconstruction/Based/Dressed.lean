import YM.SU5.Reconstruction.Based.Loops
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
variable (K:Calibration)
open Tapestry
/- Dress BOTH fundamental letter types with the actual Wilson paths & spin convention.
No assertion of that motion being an element of Lorentzian local algebra. -/
noncomputable def leg(x:Cover)(j a:SU.Slot)(U:LinksC):ℂ:= (matter (fromRoot R (nodeC x) U)⁻¹).val j a
noncomputable def legColor(x:Cover)(j a:SU.Slot)(U:PairsC):ℂ:= leg R x j a U.1
noncomputable def minusColor(x:Cover)(j a:SU.Slot)(U:PairsC):ℂ:= star (legColor R x j a U)
-- matrix reads applied to the color of ANY genuine $Window.family here
noncomputable def rootCreate(x:Cover)(i:SpinIdx)(a:SU.Slot): Buffered.Family K:=
 ∑ j:SU.Slot, scalar K (legColor R x j a)*creation K x i j
noncomputable def rootRemove(x:Cover)(i:SpinIdx)(a:SU.Slot): Buffered.Family K:=
 ∑ j:SU.Slot, scalar K (minusColor R x j a)*removal K x i j
variable {x:Cover}{i:SpinIdx}{b c a:SU.Slot}
lemma leg_family(x:Cover)(h:Window.family a≠Window.family b): leg R x a b=0:= funext fun _=> neq_block _ h
lemma color_narrow(wide:Bool)(h: nodeC x∈ S)(a b:SU.Slot):Coeff wide S (legColor R x a b):=
 Coeff.fromC wide S ((matter_cont.comp (fromRoot_cont ..).inv).matrix_elem a b) (fun _ _ p=> congrArg (fun g:SU.E => (matter g⁻¹).val a b) (route_local R h _ _ p))
lemma minus_narrow(wide:Bool)(h: nodeC x∈ S)(a b:SU.Slot):Coeff wide S (minusColor R x a b):=
 Coeff.fromC wide S (f:=fun u=> star (leg R x a b u)) (((matter_cont.comp (fromRoot_cont ..).inv).matrix_elem a b).star) (fun _ _ p=> congrArg (fun g:SU.E => star ((matter g⁻¹).val a b)) (route_local R h _ _ p))
lemma rootCreate_test(wide:Bool)(h:nodeC x∈ S)(u:i∈plusHalf)(a):InTest K wide S true (rootCreate R K x i a):=
 InTest.sum _ _ (fun j _=> InTest.mul (.seed (color_narrow R wide h j a)) (.creator j u h))
lemma rootRemove_test(wide:Bool)(h:nodeC x∈ S)(u:i∉plusHalf)(a):InTest K wide S true (rootRemove R K x i a):=
 InTest.sum _ _ (fun j _=> InTest.mul (.seed (minus_narrow R wide h j a)) (.remover j u h))
variable {m:Side}
noncomputable def rootBasis(n:Side)(x:Cover)(i:SpinIdx)(a:SU.Slot)(U:LinksC): Ket (Single n):= ∑ j, leg R x j a U • basisC n x i j
lemma rootCreate_apply (v:Fields (K.c m)): rootCreate R K x i a m v=create (rootBasis R (K.c m) x i a (onC _ v.1)):=by
 unfold rootCreate rootBasis; simp_rw [map_sum,map_smul,Finset.sum_apply,Pi.mul_apply]; exact sum_congr rfl fun j _=> (by change (_ • (1:FC _))*_= leg _ _ _ _ _ • _; rw [Algebra.smul_mul_assoc,one_mul]; rfl)
lemma rootRemove_apply (v:Fields (K.c m)): rootRemove R K x i a m v= Fock.remove (rootBasis R (K.c m) x i a (onC _ v.1)):=by
 unfold rootRemove rootBasis Fock.remove; simp_rw [map_sum,map_smul,star_sum,star_smul,Finset.sum_apply,Pi.mul_apply]; exact sum_congr rfl fun j _=> (by change (_ • (1:FC _))*_ = star (leg _ _ _ _ _) • _; rw [Algebra.smul_mul_assoc,one_mul]; rfl)

/-- This certifies the quality of gauge fixing for even and odd tests before any reference
 to neutrality. On any torus where this trace of g is available. -/
noncomputable def ReadAs(f f':Buffered.Family K):Prop:=∀ (m:Side)(v:Fields (K.c m))(g:Seat (K.c m)→ SU.E), TraceGauge S (fun x=> fromRoot R x (onC (K.c m) v.1)) g → f m (simultaneous g v)= twist (quantU (tradew (K.c m) g)) (f' m v)
namespace ReadAs
variable {K R} {f f' q q': Buffered.Family K}
lemma mul (p:ReadAs R K f f')(u: ReadAs R K q q'): ReadAs R K (f*q) (f'*q'):= fun m v g t => by simp only [Pi.mul_apply, p m v g t,u m v g t,map_mul]
lemma scale (v:ℂ)(h:ReadAs R K f f'): ReadAs R K (v • f) (v • f'):= fun m w g t=> by simp only [Pi.smul_apply,h _ w g t,twist_scalar]
lemma add (p:ReadAs R K f f')(u: ReadAs R K q q'): ReadAs R K (f+q) (f'+q'):= fun m v g t=> by simp only [Pi.add_apply, p m v g t,u m v g t,map_add]
variable (R K)
lemma zero : ReadAs R K 0 0:= fun _ _ _ _=> (map_zero _).symm
lemma one : ReadAs R K 1 1:= fun _ _ _ _=> (map_one _).symm
lemma createLink (h:nodeC x∈ S): ReadAs R K (creation K x i a) (rootCreate R K x i a):=by
 intro m v g t; rw [rootCreate_apply,twist_create]; let f:= summonBasisC (K.c m) g x i a; rw [t _ h] at f; exact congrArg create f.symm
lemma removeLink (h:nodeC x∈ S): ReadAs R K (removal K x i a) (rootRemove R K x i a):=by
 intro m v g t; rw [rootRemove_apply, twist_remove]; let f:= summonBasisC (K.c m) g x i a; rw [t _ h] at f; exact congrArg Fock.remove f.symm
lemma gaugeCoe {wide:Bool}{F:PairsC→ℂ}(h: Coeff wide S F): ReadAs R K (scalar K F) (scalar K (ask R F)):=by
 intro m v g t; unfold scalar; rw [twist_scalar,map_one]; exact congrArg (fun a:ℂ=>a • (1:FC _)) (h.locus _ (loopData R _) (gauge_trace _ t _) (gauge_trace _ t _)) -- tune implicit
end ReadAs
end YM.CF.Buffered.Afterglow.Rooted
