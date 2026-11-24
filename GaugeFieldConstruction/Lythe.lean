import YM.CF.Buffered.Melody
import GaugeFieldConstruction.Thole
/- Reflected Rotor is monomial in *all* the cover letters. Includes the AP wind. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Lifted
open Function Fock Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RP Reflect Advance
open Window Nacre Spire Scroll Peaks Rush Tulip Skye
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra

abbrev sparge (i:Axis)(s:SpinIdx):SpinIdx:= (!![3,2,1,0;3,2,1,0;2,3,0,1;2,3,0,1]:Matrix (Fin 4) (Fin 4) (Fin 4)) i s
-- Melody private `pinned` used another indexing; recompute support
set_option maxHeartbeats 1900000 in
lemma pin_sparse (i:Axis)(s t:SpinIdx)(p:sparge i s≠t): Mir.pin i t s=0:=by
 fin_cases t <;> fin_cases s <;> fin_cases i <;>
   first | exact False.elim (p rfl) | norm_num [sparge, Axis, SpinIdx, Matrix.of_apply, Mir.pin, gammaOp, grading,Matrix.mul_apply,Fin.sum_univ_succ,      show (2:Fin 4)=Fin.succ (1:Fin 3) from rfl,show (3:Fin 4)=Fin.succ (Fin.succ (1:Fin 2)) from rfl]
open Fock.Flux Tenant
variable {n:Side}(i:Axis)(s:ℤ){S:Support (More n)}
lemma polarMirror (x:Single n): ∃ a:ℂ,∃ y:Single n, ‖a‖=1 ∧ node y.1.1=(plane i s).anon n (node x.1.1) ∧
   acts (carR i s n).val (basisKet x)= a • basisKet y:=by
 rcases x with ⟨⟨r,p⟩,t⟩; let k:=((r,p),t); let u:=(plane i s); let b':= natural r
 let c:=sparge i p; let y:=Lifted.index n (u.flee b') c t
 let V:= carR i s n; let W:= winding n b'; let z:= winding n (u.flee b')
 let a:=W*(Mir.pin i c p*z)
 have he(ℓ:Ket (Single n)):basisKet ((r,p),t)= ℓ → basisC n b' p t=W • ℓ:=fun g=>by subst ℓ; unfold basisC; rw[show Lifted.index n b' p t=((r,p),t) from congrArg (fun h=>((h,p),t)) (nat_true _)]
 have h:basisKet ((r,p),t)=W • (basisC n b' p t):=by rw [he _ rfl,smul_smul,show W*W=1 from fee_one _,one_smul]
 have hp: acts V.val (basisKet ((r,p),t))=a • basisKet y:=by
    rw[h,map_smul, show acts V.val _= _ from acted_basisC i s n b' p t,sum_eq_single c]; swap; · intro j m w; rw [pin_sparse i _ _ w.symm,zero_smul]
    swap; · simp
    unfold a y; rw [basisC,smul_smul,smul_smul,mul_assoc]
 refine ⟨a,y,?_,?_,hp⟩
 · have hv:= act_unit_norm V (basisKet ((r,p),t)); rw[hp,norm_smul] at hv; simpa using hv
 have hv: y.1.1=u.mills n r:=by
    change wrap n (u.flee _) = _; rw [←Shape.mill u,show wrap n b'=r from nat_true r] -- tune
 change node y.1.1=_; rw [hv,Shape.nodex]

open Py.Rate Py.Rate.LocalLimit.Papal
local notation "Uy"=> carR i s n
private lemma swingAngle(k: Creduct (Single n)) (p:k.2 ∈ onPage n S):∃ (a:ℂ)(y: Creduct (Single n)), ‖a‖=1 ∧ y.2∈onPage n (S.image ((plane i s).anon n)) ∧
 theta Uy (RootBay k) = a • RootBay y :=by
 rcases k with ⟨b,k⟩; obtain ⟨a,y,hp,h,q⟩:=polarMirror i s k
 have hy:y∈onPage n (S.image ((plane i s).anon n)):=mem_filter.mpr ⟨mem_univ _, h ▸ mem_image_of_mem _ (mem_filter.mp p).2⟩
 cases b
 · refine ⟨(-Complex.I)*(star a), (true,y), by simp [hp], hy,?_⟩
   change theta Uy (create (basisKet k))= _ • Fock.remove (basisKet y)
   rw [theta_upV,q, Fock.remove,map_smul,star_smul,smul_smul]
 refine ⟨Complex.I*a,(false,y),by simp [hp],hy,?_⟩
 change theta Uy (Fock.remove (basisKet k)) = _• create _; rw[theta_downV,q,map_smul,smul_smul]
private lemma swingAngles (L:List (Creduct (Single n)))(h:∀ j∈L,j.2∈onPage n S):∃ (a:ℂ)(A:List (Creduct (Single n))), ‖a‖=1∧ A.length=L.length∧ (∀ j∈A,j.2∈onPage n (S.image ((plane i s).anon n))) ∧ theta Uy (rollC RootBay L)=a•rollC RootBay A:=by
 induction L with
 | nil=> refine ⟨1,[],by simp,rfl,by simp,?_⟩; change theta Uy 1=(1:ℂ)•1; rw [theta_one,one_smul]
 | cons ι l ih=>
    obtain ⟨b,A,p,t,hq,x⟩:=ih (fun j u=>h j (List.mem_cons_of_mem _ u)); obtain ⟨u,k,r,v,e⟩:= swingAngle i s ι (h ι (by simp)) -- i shadow tune
    refine ⟨u*b,k::A,by simp [p,r],by rw [List.length_cons,List.length_cons,t],fun j p=> (List.mem_cons.mp p).elim (fun e=>e ▸ v) (fun m=>hq j m),?_⟩
    change theta Uy (RootBay ι * rollC RootBay l)=_ • (RootBay k* rollC RootBay A); rw[theta_mul,e,x,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
lemma turn_press {k:ℝ}{m:ℕ}{F:FC (Single n)} (p:pressedF (onPage n S) m k F):
 pressedF (onPage n (S.image ((plane i s).anon n))) m k (theta Uy F):=by
 obtain ⟨w,t,v,rfl⟩:=p
 suffices h: ∃ L:List (SignWave (Single n)), nestM (onPage n (S.image ((plane i s).anon n))) m L∧ meterK L =meterK w∧ orchestrate L=theta Uy (orchestrate w) by obtain ⟨X,h,g,b⟩:=h; exact ⟨X,h,g ▸ v,b⟩
 clear v
 induction w with
 | nil=> exact ⟨[],by simp [nestM],rfl, (theta_zero Uy).symm⟩
 | cons j l ih=>
    obtain ⟨L,p,w,k⟩:=ih (fun a v=>t a (List.mem_cons_of_mem _ v))
    obtain ⟨v,g,y⟩:=t j (by simp); obtain ⟨c,Q,x,u,h,H⟩:=swingAngles i s j.2 y
    let K:SignWave (Single n):=(star j.1*c,Q)
    refine ⟨K::L, ?_,?_,?_⟩
    · intro j' f; obtain rfl|r:=List.mem_cons.mp f; exact ⟨u ▸ v,u ▸ g,h⟩; exact p _ r
    · change ‖star j.1*c‖+meterK _= ‖j.1‖+meterK _; simp [w,x]
    change (star j.1*c) • _+ orchestrate L=theta Uy (j.1 • rollC RootBay j.2+orchestrate l)
    rw [theta_add,k,theta_smul,H,smul_smul]
end YM.CF.Buffered.Lifted
end
