import YM.SU5.LitCurrent.Initial
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Salt
/-- destination in pull-by-s Pane -/
def pose (s:Sweep N)(x:Site N):Site N:= (castX s⁻¹).mills N x
lemma pose_node (s:Sweep N)(x:Site N): node (pose s x)= (boxA s).symm (node x):=by
 rw [←sitU]; exact Shape.nodex ..
lemma pose_mul (s t:Sweep N)(x:Site N): pose t (pose s x)=pose (s*t) x:=by
 apply unaryN; rw [pose_node,pose_node,pose_node,←sitU,←sitU,←sitU,sitV,mul_inv_rev]

/- direction rotations. Use Dir rather than imposing an instance globally -/
abbrev FaceDir := Axis× Bool
def strideD (d:FaceDir): Step:=⟨d.1,d.2⟩
def axisFlip (d:FaceDir): FaceDir :=(d.1,!d.2)
lemma step_flip (d:FaceDir): strideD (axisFlip d)=(strideD d).rev:= rfl
lemma step_inj : Injective strideD:= fun ⟨_,_⟩ ⟨_,_⟩ e=>
 Prod.ext (congrArg Lattice.Step.dir e) (congrArg Lattice.Step.neg e)
def faceAt (s:Sweep N)(d:FaceDir): FaceDir:=let f:= (strideD d).rotate s.s⁻¹; (f.dir,f.neg)
lemma stride_at (s:Sweep N)(d:FaceDir): strideD (faceAt s d)=(strideD d).rotate s.s⁻¹:=rfl
lemma face_at_mul (s t:Sweep N)(d:FaceDir): faceAt t (faceAt s d)=faceAt (s*t) d:=by
 apply step_inj; rw [stride_at,stride_at,stride_at,Step.rotate_mul,show (s*t).s=s.s*t.s from rfl,mul_inv_rev]
lemma face_one (d:FaceDir): faceAt (1:Sweep N) d=d:=by
 apply step_inj; rw [stride_at,show (1:Sweep N).s=1 from rfl,inv_one,Step.rotate_one]
def bearings (s:Sweep N) : FaceDir ≃ FaceDir:= ⟨faceAt s,faceAt s⁻¹,fun x=>by rw [face_at_mul,mul_inv_cancel,face_one],fun x=> by rw [face_at_mul,inv_mul_cancel,face_one]⟩
lemma face_at_flip (s:Sweep N)(d:FaceDir): faceAt s (axisFlip d)=axisFlip (faceAt s d):=by
 apply step_inj; rw [stride_at,step_flip,step_flip,stride_at,Step.rev_rotate]
abbrev destSite (x:Site N)(r:ℕ)(d:FaceDir):Site N:=x+r • (strideD d).vec
lemma pose_hop (s:Sweep N)(x:Site N)(r:ℕ)(d:FaceDir): pose s (destSite x r d)=destSite (pose s x) r (faceAt s d):=by
 let S:=castX s⁻¹
 unfold pose Shape.mills affine destSite
 rw [Signed.act_add, stride_at, Step.vec_rotate]
 change s.s⁻¹.act x+s.s⁻¹.act (r • (strideD d).vec)+_= _
 have h:s.s⁻¹.act (r • (strideD d).vec)=r • s.s⁻¹.act ((strideD d).vec:Site N):=map_nsmul (s.s⁻¹.actEquiv (R:=Per N)) _ _
 rw [h]; change s.s⁻¹.act x+_+_=(s.s⁻¹.act x+_)+_; abel

lemma house_move (s:Sweep N)(x:Site N): ech s (houseW x) = houseW (pose s x):=by
 simp only [house_cell,millSt]; nth_rw 1 [show node x=(boxA s) (node (pose s x)) from by rw [pose_node,Equiv.apply_symm_apply]]
 exact Tye.proM (boxA _) (boxA _).injective _ _ (fun i j h=> Tye.birth_l i j _ _ _ h) _
lemma echo_add (s:Sweep N)(A B:Op I): ech s (A+B)=ech s A+ech s B:=by
 simp [ech]
lemma echo_zero (s:Sweep N):ech s (0:Op I)=0:=by simp [ech,win_z]
lemma echo_sub (s:Sweep N)(A B:Op I): ech s (A-B)=ech s A-ech s B:=by simp [ech]
lemma echo_mult (s:Sweep N)(A B:Op I): ech s (A*B)=ech s A*ech s B:=singm ..
lemma echo_one (s:Sweep N): ech s (1:Op I)=1:=by simp [ech,win_i]
lemma echo_half (s:Sweep N)(A:Op I): ech s ((2:ℂ)⁻¹ • A)=(2:ℂ)⁻¹ • ech s A:=by
 simp only [ech,singT,win_c,twist_scalar]; congr 1; cases b:s.charge<;>simp [cSignX]
lemma echo_star (s:Sweep N)(A:Op I): ech s (star A)=star (ech s A):=by simp only [ech,singT,win_s,map_star]
private lemma rake_motion (s:Sweep N)(i:Axis)(X Z:Site N→Op I)
    (h:∀ x,ech s (X x)=Z (pose s x))(r:ℕ)(x:Site N):
    ech s (StressExchange.rake (step i) X r x)= StressExchange.rake (step (s.s⁻¹.perm i)) Z r (pose s x):=by
 induction r with
 | zero=>exact echo_zero s
 | succ r p=>
   let j:=s.s⁻¹.perm i
   have ps (t:ℕ): pose s (x+t • step i)=pose s x+t • (strideD (faceAt s (i,false))).vec:= pose_hop s x t (i,false)
   have ns (t:ℕ): pose s (x-t • step i)=pose s x+t • (strideD (faceAt s (i,true))).vec:= by
      change _=destSite (pose s x) t (faceAt s (i,true)); rw [←pose_hop (x:=x) (d:=(i,true)) (s:=s) (r:=t)]; simp [destSite,strideD, Step.vec,sub_eq_add_neg]
   rw [StressExchange.rake,StressExchange.rake,echo_add,echo_add,echo_add,echo_add,p,h,h,h,h,ps,ps,ns,ns]
   by_cases g:s.s⁻¹.flip i=true
   · simp only [faceAt,strideD,Step.rotate, Bool.false_xor, Bool.true_xor,Step.vec,g,ite_true] -- neg true simplification
     simp [sub_eq_add_neg]; abel
   have hg:s.s⁻¹.flip i=false:=Bool.eq_false_iff.mpr g
   simp [faceAt,strideD,Step.rotate,Step.vec,hg,sub_eq_add_neg]
private lemma cube_motion (s:Sweep N)(r:ℕ)(L:List Axis)(x:Site N):
    ech s (cubelet r L houseW x)= cubelet r (L.map (s.s⁻¹.perm)) houseW (pose s x):=by
 induction L generalizing x with
 |nil=>exact house_move ..
 |cons i L h=>exact rake_motion s i _ _ h r x
lemma room_move (s:Sweep N)(r:ℕ)(x:Site N): ech s (roomW x r)=roomW (pose s x) r:=by
 have hp:(arcOrder.map s.s⁻¹.perm).Perm arcOrder:=by
   apply List.perm_ext_iff_of_nodup ?_ ?_ |>.2 -- inspect
   · intro i; constructor; intro _; simp [arcOrder,Axis]; intro _; exact List.mem_map.mpr ⟨_,(show s.s⁻¹.perm.symm i∈ arcOrder from (by simp [arcOrder,Axis])),Equiv.apply_symm_apply _ _⟩
   · exact (show arcOrder.Nodup from List.nodup_finRange _).map s.s⁻¹.perm.injective
   exact List.nodup_finRange _
 rw [roomW, cube_motion, cubelet_perm _ hp]; rfl
lemma room_star (x:Site N)(r:ℕ): star (roomW x r)= roomW x r:=by
 let f:Op I →+ Op I:=⟨⟨star,star_zero _⟩,star_add⟩
 have hx : f ∘ houseW=houseW:=funext fun x=>
    (cutM_idp (inhabit x)).isSelfAdjoint
 exact (congrFun (cubelet_natural f _ r arcOrder) x).trans (by rw [hx]; rfl)
lemma tick_star (N:Side):star (tickA N)=tickA N:=by rw [touchP]; exact (cutM_idp _).isSelfAdjoint
lemma tick_travel (s:Sweep N): ech s (tickA N)=swapX (det_S s) (tickA N):=by
 rw [touchP]; exact tickR _ _ _ (spinZ s.charge s.s) N

structure Permission (P T:SOp N) (d:ℝ) : Prop where
 projection (V:Pane N)(h:Guard V d): IsStarProjection (P (profile V))
 stepP (s:Sweep N)(V:Pane N)(h:Guard V d): ech s (P (profile V))=swapX (det_S s) (P (profile (flashA s V)))
 stepT (s:Sweep N)(V:Pane N)(h:Guard V d): T (profile (flashA s V))= Thera.jazz (det_S s) (ech s (T (profile V)))
namespace Permission
variable {P T:SOp N}(p:Permission P T d) {V: Pane N}(h:Guard V d)
include p h
lemma tax_self (x:Site N): IsSelfAdjoint (taxKernel P x r (profile V)):= by
 unfold IsSelfAdjoint taxKernel
 simp only [star_smul,star_add,star_mul,star_sub, star_inv₀, star_ofNat, room_star,tick_star,(p.projection V h).isSelfAdjoint.star_eq,add_comm]
lemma tax_move (s:Sweep N)(x:Site N) : realR s true (taxKernel P x r (profile V))=taxKernel P (pose s x) r (profile (flashA s V)):=by
 let A:=taxKernel P x r (profile V); let q:= det_S s
 have he:star (ech s A)=ech s A:=by rw [←echo_star,p.tax_self h x] -- change
 change Thera.jazz (det_S s) (ech s (taxKernel P x _ _))=_
 unfold Thera.jazz; split <;> rename_i k
 · rw [show star (ech s (taxKernel P x r (profile V)))= _ from he]
   simp only [A,taxKernel, echo_half,echo_add,echo_mult,echo_sub,tick_travel,room_move,p.stepP s _ h,k,swapX,ite_true]
   rw [show (1:Op I)-P (profile (flashA s V))-(1-tickA N)= -(P (profile (flashA s V))-tickA N) from by abel]
   simp only [neg_mul,mul_neg,smul_add,smul_neg]; abel
 have hv:det_S s=false:=by simpa using k
 simp only [taxKernel,echo_half,echo_add,echo_mult,echo_sub,tick_travel,room_move,p.stepP s _ h,hv,swapX,Bool.false_eq_true,ite_false]
lemma inward_move (s:Sweep N)(x:Site N): realR s false (Sault.inward (P (profile V)) (roomW x r) (T (profile V)))=
    Sault.inward (P (profile (flashA s V))) (roomW (pose s x) r) (T (profile (flashA s V))):=by
 let G:= profile (flashA s V)
 have hP:= p.stepP s V h
 let P':=P G; let W:=roomW (pose s x) r
 let Y:=P (profile V); let T':=T (profile V); let C:= capT Y T'
 have hf:= p.projection (flashA s V) (share s V h); have hs : star P'=P':= hf.isSelfAdjoint
 have hc : capT P' (T G) = Thera.jazz (det_S s) (ech s C):= by
   unfold G; rw [p.stepT s V h]; exact Levier.prima (γS s) _ _ T' hf hP
 change (if det_S s then star (ech s _) else ech s _)=_
 unfold Sault.inward Sault.blockD
 simp only [echo_sub,echo_mult,echo_add,echo_one,hP,room_move]
 -- now identify orientation
 dsimp only [C,P',G,Y,T'] at hc hs
 rw [hc]; by_cases k:det_S s=true
 · simp only [k,ite_true,swapX,Thera.jazz,sub_neg_eq_add, ←sub_eq_add_neg,star_sub,star_mul,star_add,star_one,room_star,hs,sub_sub_cancel,mul_assoc]
   rw [add_comm ((1-P (profile (flashA s V))) * (roomW (pose s x) r*_))]
 have hv:det_S s=false:= by simpa using k
 simp [Thera.jazz,hv,swapX]
end Permission
end YM.CF.LitCurrent
