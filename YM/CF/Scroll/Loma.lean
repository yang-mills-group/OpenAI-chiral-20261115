import YM.CF.Scroll.Coat
set_option autoImplicit false
noncomputable section
namespace YM.CF.Scroll
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}
-- charge, flavor support
structure ColorT (p:Bool) where
 lens: E≃* E
 V: UNI Slot
 X:Ballot≃ᵢ Ballot
 trek(g:E)(x:Ballot): (X (scaledV g x))=scaledV (lens g) (X x)
 shore(g:E): (matter (lens g)).val=  sings p V (matter g).val
 born (x y:E):‖fund (lens x)-fund (lens y)‖=‖fund x-fund y‖
 facing(x:Ballot): Pair.fullM (X x).val=congrC V (windX p (Pair.fullM x.val))
variable {b:Bool}(u:ColorT b)(a:Shape)(G:Ratio N P)
def stir (x: Bkg (More N)): Bkg (More N):=u.lens ∘ Lattice.pull a.s (wrap _ (2 • a.t)) x
def fume (x: Stun N):Stun N:= fun i=>u.X (x (a.anon N i))
lemma salt (s: Step)(x):a.anon N (x+s.vec)=a.anon N x+(s.rotate a.s).vec:=by rw [Shape.anon,Shape.anon,Step.vec_rotate]; simp [affine,Signed.act_add,add_right_comm]
lemma veil_x (x:Bkg (More N))(z)(w:Step): w.read (stir u a x) z=u.lens ((w.rotate a.s).read x (a.anon N z)):=by unfold stir; rw [Shape.anon,← Step.pull_read]; cases w with | mk _ p=> cases p<;> simp [Step.read]
lemma levity (x:Bkg (More N))(z)(w:Walk): travel (stir u a x) z w=u.lens (travel x (a.anon N z) (w.map (·.rotate a.s))):=by
 induction w generalizing z with
 | nil=>simp [travel]
 | cons i w h=> rw [List.map_cons, travel,travel,h, salt,veil_x,map_mul]
lemma swayX (x:Bkg (More N))(t:Stun N)(p:ℝ)(k: Slow x (hook t) p): Slow (stir u a x) (hook (fume u a t)) p:=by
 have he(y)(d:Step): dist (scaledV (d.read x y) (t (y+d.vec))) (t y) < p:=by
   rcases d with ⟨i,h|h⟩; exact (by rw [Subtype.dist_eq,dist_eq_norm]; exact k _ _)
   change dist (scaledV ((negDir i).read x y) (t (y+ -step i))) (t y)<p -- tune unnecessary
   rw [Step.neg_read, ←sub_eq_add_neg]; change dist _ _<_; rw [Subtype.dist_eq,dist_eq_norm,norm_sub_rev]
   let Y:=y-step i; have hh:= k Y i; rw [show Y+step i=y by unfold Y; rw [sub_add_cancel]] at hh
   rw [←turn_norm (x (Y,i)),turn_sub]; change ‖turn _ (hook t y)-turn (x (Y,i)) (turn _ (hook t Y))‖<_; rw [show turn _ (turn _ (hook t Y))=hook t Y from ?_]; exact hh
   rw [← turn_seq,mul_inv_cancel, turn,fund_one,act_one]
 intro z i; let d:=(posDir i).rotate a.s; let y:=a.anon N z; change ‖(scaledV (u.lens _) _).val - _‖<_ -- tune notation
 rw [← dist_eq_norm]
 change dist (scaledV (u.lens (d.read x y)) (u.X (t (a.anon N (z+step i))))) (u.X (t y)) < p
 rw [← u.trek,show a.anon N (z+step i)=y+d.vec from salt a (posDir i) z, IsometryEquiv.dist_eq]
 exact he _ _
lemma norm_cc {I:Type*}[Fintype I][DecidableEq I][Nonempty I](x:Op I): ‖cc x‖=‖x‖:=by
 have hk:IsSelfAdjoint (star x*x):=by rw [isSelfAdjoint_iff]; simp
 obtain ⟨p,t,H⟩:= spectral_exists (star x*x) hk
 rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),sq,sq,← CStarRing.norm_star_mul_self, ← CStarRing.norm_star_mul_self,← cc_star,← cc_mul,H,cc_spectral]; simp only [spectral,twist_norm] -- tune
lemma singN {I:Type*}[Fintype I][DecidableEq I][Nonempty I] (p:Bool)(W:UNI I)(x:Op I): ‖sings p W x‖=‖x‖:=by rw [singT,twist_norm]; cases p; rfl; exact norm_cc _
lemma keepD(x:Bkg (More N)) (p:ℝ) {I:Type*}[Fintype I][DecidableEq I](F:E→*UNI I)(k:PlaqBound F x p)(hh:∀ g:E,‖(F (u.lens g)).val-1‖=‖(F g).val-1‖): PlaqBound F (stir u a x) p:=by
    intro z i j g
    let y:=(posDir i).rotate a.s; let v:=(posDir j).rotate a.s
    rw [levity, hh,show List.map _ (square i j)=Lattice.oriented y v by unfold square Lattice.oriented; simp only [List.map_cons,List.map_nil,←Step.rev_pos,Step.rev_rotate]; rfl]
    let P(g:E):=‖(F g).val-1‖; change P _ ≤ p
    rw [price_shift_pos P x]; exact k _ (a.s.perm i) (a.s.perm j) (a.s.perm.injective.ne g)
    · intro g; unfold P; rw [map_inv]; change ‖star _-_‖=_; rw [← star_one (R:=Op I),←star_sub,norm_star,star_one]
    intro g u; unfold P; rw [map_mul,map_inv,map_mul]; change ‖(F u).val*(F g).val* star (F u).val-1‖=_; rw [←twist_formula, show twist (F u) (F g).val-1=twist (F u) ((F g).val-1) by rw [map_sub,map_one],twist_norm];
lemma keepC(x: Bkg (More N)) (p:ℝ)(h:Guard x p): Guard (stir u a x) p:=by
 refine ⟨keepD u a x p firstF h.1 (fun g=>?_),keepD u a x p matter h.2 (fun g=>?_)⟩
 · change ‖fund (u.lens g)-1‖=‖fund g-1‖; simpa only [map_one,fund_one] using u.born g 1
 rw [u.shore,singT,show (twist u.V) _ - 1= sings b u.V ((matter g).val-1) by rw [singT,win_l,win_i,map_sub,map_one],singN]

lemma ticket_dist (x y:E):‖brand (u.lens x)-brand (u.lens y)‖=‖brand x-brand y‖:=by
 have hx:‖(matter (u.lens x)).val-(matter (u.lens y)).val‖=‖(matter x).val - (matter y).val‖:=by rw [u.shore,u.shore,singT,singT,←map_sub,←win_l,←singT,singN]
 rw [Prod.norm_def,Prod.norm_def]; exact congrArg₂ max hx (u.born x y)
lemma ticket_inv (x y:E): ‖brand x⁻¹-brand y⁻¹‖= ‖brand x-brand y‖:=by rw [brand_inv,brand_inv,←star_sub,norm_star]
lemma alongS (x:Nom N P)(e:ℝ)(p:JointB G x e): JointB G (stir u (a.broad G) x.1,stir u a x.2) e:=by
 refine ⟨keepC u _ _ _ p.fg,keepC u a _ _ p.cg,?_⟩
 rintro ⟨z,i⟩; rw [levity]; set y:= a.anon N z; set w:=a.s.perm i
 rw [←Shape.foldsT]; change ‖brand (u.lens (((posDir i).rotate a.s).read x.2 y))-brand (u.lens (travel x.1 ((ratio G).embed y) _))‖≤_
 rw [ticket_dist]
 have hk(i):pathL G i= List.replicate G.count.val (posDir i):=by simp [pathL,straight,posDir]
 cases t:a.s.flip i
 · have ht:(posDir i).rotate a.s=posDir w:=by unfold posDir Step.rotate w; rw [t]; rfl
   rw [ht,Step.pos_read,show List.map _ (pathL G i)=pathL G w by rw [hk,hk, List.map_replicate]; simp [ht,Shape.broad]]; exact p.follow (y,w)
 have ht:(posDir i).rotate a.s=negDir w:=by unfold posDir Step.rotate w; rw [t]; rfl
 rw [ht, Step.neg_read, show List.map _ (pathL G i)=Lattice.reverse (pathL G w) by rw [hk,hk]; simp [Lattice.reverse,ht,Shape.broad]]
 let Z:= y-step w; rw [show (ratio G).embed y= stop ((ratio G).embed Z) (pathL G w) by rw [stopG, show Z+step w=y by unfold Z; rw [sub_add_cancel]], travel_reverse,ticket_inv]; exact p.follow (Z,w)
end YM.CF.Scroll
