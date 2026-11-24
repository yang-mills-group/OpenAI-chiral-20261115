import YM.CF.Rush.Knoll
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators
attribute [local instance] opCStarAlgebra
-- Lift conventions allow frame origins to differ by full winds.
structure Shape where
 s : Signed
 t : Cover  -- in fermion coords (doubled on gauge lattice)
namespace Shape
variable {N F:Side}(a:Shape)(G: Ratio N F)
def motion (x:Cover):Cover := a.s.act x+2 • a.t
lemma motion_v (x y:Cover): a.motion (x+y)=a.motion x+a.s.act y:=by simp only [motion,a.s.act_add]; abel
-- fermion offset α
private def dune (a:Shape):Cover:= fun i => if a.s.flip (a.s.perm.symm i) then -1 else 0
private lemma due : a.s.act (1:Cover)= 2 • a.dune+1:=by
 funext i; obtain ⟨i,rfl⟩:= a.s.perm.surjective i; simp only [Signed.act_at,dune]; cases h:a.s.flip i<;> norm_num [h,dune]
def flee (a:Shape) (x:Cover):Cover:=a.s.act x+a.t+dune a
lemma flee_p(x u:Cover):a.flee (x+u)=a.flee x+a.s.act u:=by simp only [flee,a.s.act_add]; abel
lemma mote(x:Cover):motion a (2 • x+1)= 2 • flee a x+1:=by
 rw [motion, Signed.act_add,a.due,flee,two_smul,two_smul,two_smul,a.s.act_add]; abel

def mills (N:Side)(x:Site N):=affine a.s (wrap N (flee a 0)) x
def anon(N:Side)(x:Site (More N)):=affine a.s (wrap _ (2 • a.t)) x
lemma mill(x:Cover): mills a N (wrap N x)=wrap N (flee a x):=by rw [←show a.flee 0+a.s.act x=a.flee x from by rw [← flee_p,zero_add]]; simp only [mills,affine, map_add, wrap_signed,add_comm]
lemma anno(x:Cover): anon a N (wrap (More N) x)=wrap (More N) (a.motion x):=by simp [anon,motion,affine]
lemma tow (x:Site N)(y:Cover): a.mills N (x+wrap N y)=a.mills N x+wrap N (a.s.act y):=by simp [mills,affine, add_right_comm]
private lemma aff_b {I:Type*}[AddCommGroup I][One I](s:Signed)(t: Four I): Bijective (affine s t) :=by
 refine ⟨fun x y h=> s.act_injective (add_right_cancel (show _+t=_+t from h)),fun x=> ⟨s⁻¹.act (x-t),by simp [affine]⟩⟩
lemma mills_b: Bijective (a.mills N):= aff_b ..
lemma anon_b: Bijective (a.anon N):= aff_b ..
lemma nodex(x:Site N):node (a.mills N x)=a.anon N (node x):=by
 let p:=natural x
 have he (p:Cover):node (wrap N p)= wrap (More N) (2 • p+1):=by rw [Cube.node,Ratio.root_embed,Ratio.embed_wrap,map_add,show wrap (More N) 1=1 by ext; change ((1:ℤ):Per _)=(1:Per _); simp]; rfl
 rw [←nat_true x,mill,he,he,anno,mote]

def broad (G: Ratio N F)(a:Shape): Shape:= ⟨a.s,G.count.val • a.t⟩
lemma onnode' (x i): (broad G a).anon F (x+wrap _ i)=(broad G a).anon F x+wrap _ (a.s.act i):=by simp [anon,broad,affine,add_right_comm]
lemma foldsT(x:Site (More N)): (Rush.ratio G).embed (a.anon N x)=(broad G a).anon F ((ratio G).embed x):=by unfold anon affine; rw [←Ratio.root_embed,map_add,Ratio.root_embed,Ratio.root_embed,Ratio.signed,Ratio.embed_wrap]; rw [smul_comm]; rfl
lemma mogul(h:Odd G.count.val)(x:Cover)(u:Site G.count): (broad G a).flee (G.count.val • x+Lattice.lift u+offset G.count)= G.count.val • a.flee x+Lattice.lift (a.s.act u)+offset G.count:=by
 let b:=a.s; have hE:b.act (G.count.val • x)= G.count.val • b.act x:=by funext i; obtain ⟨k,rfl⟩:= a.s.perm.surjective i; rw [show ∀ (x:Cover),b.act x (a.s.perm k)=_ from (fun x=>Signed.act_at a.s x k)]; cases hf:a.s.flip k<;> simp [hf,b] -- tune
 have hv : b.act (offset G.count)+a.dune=offset G.count+G.count.val • a.dune:=by
    funext i; obtain ⟨k,rfl⟩:= b.perm.surjective i
    have hz:= Next.Free.mid_double G.count h
    cases ht:a.s.flip k <;> simp [dune,b,ht,offset] <;> omega -- tune
 simp only [flee,broad,Signed.act_add,smul_add]
 rw [Ratio.lift_signed_of_odd h]
 change b.act _+b.act _+b.act _+_+ a.dune = _; rw [hE]; linear_combination (norm := abel) hv
lemma folds(h:Odd G.count.val)(x:Site N)(u): (broad G a).mills F (isle G (x,u))= isle G (a.mills N x,a.s.act u):=by
 apply (fun x y h => (assembly F).embed_injective (add_right_cancel (show _ + (1:Site (More F))=_+_ from h)) : Injective (node (N:=F)))
 rw [nodex,embed_node G h, embed_node G h,onnode',Ratio.lift_signed_of_odd h]; rw [nodex,foldsT]; congr 2; exact map_nsmul (a.s.actEquiv (R:=ℤ)) .. -- tune

def rent (x:Site N):Cover:= periods N (a.flee (natural x))
def payA (x:Site N):ℂ:= fee (a.rent x)
lemma reflex (x:Site N): a.payA x*a.payA x=1:= fee_one _
lemma real_payA(x:Site N):star (a.payA x)=a.payA x:=fee_real _
lemma vibes(x:Site N): natural (a.mills N x)+N.val • a.rent x=a.flee (natural x):=by
 unfold Shape.rent; rw [show a.mills N x=wrap N (a.flee (natural x)) from by rw [← mill,nat_true],carrying]
lemma tolls(h:Odd G.count.val)(x:Site N)(u): (broad G a).payA (isle G (x,u))=a.payA x:=by
 suffices hr: (broad G a).rent (isle G (x,u))=a.rent x by unfold payA; rw [hr]
 have he:= vibes (broad G a) (isle G (x,u)); have hy:= vibes a x
 rw [folds a G h, data_isle G h, data_isle G h,mogul a G h, ←hy,smul_add] at he
 apply nsmul_right_injective (M:=Cover) (show G.count.val*N.val≠0 by positivity); rw [←mul_smul,G.exact_size,mul_comm N.val] at he; change (G.count.val*N.val) • _=_ • _; linear_combination (norm := abel) he
end Shape
end YM.CF.Scroll
