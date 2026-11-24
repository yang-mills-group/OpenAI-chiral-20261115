import YM.CF.Spire.Quartz
import YM.CF.Vault.Horse
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spire
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch Paige Brace Vault
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N:Side}(a:Shape){b r:Bool}(Z:ColorT b)(U: UNI SpinIdx)(h:JetS a.s b r U)
def Tset (N:Side):Finset (Single N):= (upperP N).preimage (helix N) (helix N).injective.injOn
lemma touchP(N):tickA N=cutM (Tset N):=by ext; simp [tickA,Tset,portW,cutM,Matrix.diagonal_apply] -- tune
private lemma fossil (G:Ratio N N): Injective (foot G):=by intro x y h; ext i j; obtain ⟨i,rfl⟩:= (switchG G).surjective i; obtain ⟨j,rfl⟩:= (switchG G).surjective j; exact Matrix.ext_iff.mpr h i j
lemma perpet(a:Shape)(N): Shape.broad (idrat N) a=a:=by simp [Shape.broad,idrat]
include h in
lemma tickR(N): sings b (prepU a U Z N) (cutM (Tset N))=swapX r (cutM (Tset N)):=by
 let G:=idrat N; have hv:b=b:=rfl; have ho:Odd G.count.val:=odd_one; have hk:=perpet a N
 apply fossil G; rw [←touchP,←hk,←portFoot G ho]; rw [←lobe_t, taxL G a Z U h]; cases r; exact lobe_t G; change lobe G false=foot G (1-tickA _); rw [foot_sub,←lobe_t,foot_one,lobe_plus] -- tune hk nth
lemma LxxX(x: Stun N): postC x ∈unitary (Op (Single N)):=by
 rw [Matrix.mem_unitaryGroup_iff]
 let A:=hook x∘node
 have he:= (C_unit (N:=N) A (fun i=> hookN ..)).2; let V:= love N; change V (Cfield A)*(star (V (Cfield A)))=1; rw [← map_star,←map_mul, he,map_one]
lemma stoneQ(x:Stun N):Commute (cutM (Tset N)) (postC x):=by
 have he:=onsite_ref (hook x ∘ node)
 rw [←touchP]; change portW _ _* portW _ _=portW _ _*portW _ (cutM (upperP _)); unfold portW; rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,he.eq]
include h
lemma tickX(x:Stun N): congrC (prepU a U Z N) (windX b (postC x))=postC (fume Z a x):=by
 let G:= idrat N; have ho:Odd G.count.val:=odd_one; let X:Sew N N:=(1,x,x); apply fossil G
 have ht:= tyL G ho a Z U h true X; rw [square_true,square_true, ←tick_hold,←tick_hold] at ht; unfold congrC at *
 rw [foot_mul,foot_mul]; change (pflux _ _ _ _).val*windX b (foot G (postC x))*(pflux _ _ _ _).valᵀ=foot G (postC (fume Z (Shape.broad G a) x)) at ht; rw [puff G ho] at ht -- tune
 rw [show Shape.broad G a=a from perpet a N] at ht
 have hp(Q:Op (Single N)): (foot G Q)ᵀ=foot G Qᵀ:=rfl
 have hb (b:Bool)(Q:Op (Single N)):foot G (windX b Q)=windX b (foot G Q):=by cases b <;> rfl
 rw [hb, ←hp]; exact ht
variable {j:ℕ}(p:1≤j){M:Male}{k:ℝ}(A:Bkg (More N))(t:∀ x:Bkg (More N),Guard x k→PaidG j k x)(g:Guard A k)
include t g p
lemma arum_post (x:Stun N): arum (prepU a U Z N) b r (mateK N) (coneP j M A x)= coneP j M (stir Z a A) (fume Z a x):=by
 let V:=prepU a U Z N; let y:= fume Z a x
 have he:(arum V b r (mateK N)) (pairWave (postC x))=pairWave (postC y):=arum_pair V b r (Tset N) (touchP N ▸ tickB N) (tickR a Z U h N) ⟨_,LxxX x⟩ ⟨_,LxxX y⟩ (starC _ (fun i=>hookN ..)) (starC _ (fun i=> hookN ..)) (stoneQ x) (stoneQ y) (by rw [← touchP]; exact constB _ (fun i=>hookN ..)) (by rw [←touchP]; exact constB _ (fun i=>hookN ..)) (tickX a Z U h _)
 unfold coneP filled; rw [arum_act, tour_line (prepU a U Z N) b r (spar j M A) (spar j M (stir Z a A)) _ (funde_f a Z U h A j p M _ t g)]; swap
 · unfold spar funde; split<;> first |exact (t A g).1.projection|exact ((t A g).2 M).projection
 rw [show arum (prepU a U Z N) b r (mateK N) (pairWave (postC x))= _ from he]
end YM.CF.Spire
