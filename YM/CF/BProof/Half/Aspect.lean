import YM.CF.BProof.Transit.Action
import YM.CF.BProof.Site.Interval
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Lattice Wilson Lat SU Fock Cube Mir Finset Spire Skye Rush
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
namespace Half
variable {N P:Side}(i:Axis) {a b c s:ℕ}
def toward (b:Bool) (z:Per (More N)):= if b then z else -z
def shade (N:Side)(i:Axis)(b:Bool)(s:ℕ):Finset (Seat N):=univ.filter fun y=> s ≤ (toward b (y i)).val ∧ (toward b (y i)).val+s≤N.val
lemma shine{y:Seat N}{q:Bool}: y ∈ shade N i q s ↔ s ≤ (toward q (y i)).val ∧ (toward q (y i)).val+s≤ N.val:=by simp [shade]
abbrev reflect (N:Side) := boxA (Fixed.reflectSweep N i)
lemma shade_carry(q):regionD (Fixed.reflectSweep N i) (shade N i q s)=shade N i (!q) s:=by
 ext y; have he:toward q (reflect i N y i)=toward (!q) (y i):=by rw [reflect,Fixed.box_reflect]; rw [show (Signed.mirror i).act y i=-(y i) from by simp [Signed.act,Signed.mirror]]; cases q <;>simp [toward]
 unfold regionD; simp only [Finset.mem_map_equiv, Equiv.symm_symm,shine]; rw [he]
include i in
lemma delta (q:Bool)(x y:Per (More N)) : delta1 (More N) (toward q x) (toward q y)=delta1 (More N) x y:=by cases q; change delta1 (More N) (-x) (-y)=_; unfold delta1; rw [show -x- -y= -(x-y) from by abel,ZMod.natAbs_valMinAbs_neg]; rfl
lemma fortuna(x y:Per (More N))(h:a ≤ x.val)(v:x.val+a ≤ N.val)(t:delta1 (More N) x y≤ b)(he:b+c≤a) : c ≤ y.val ∧ y.val + c ≤ N.val:=by
 let L(z:Per (More N)):=along 0 z; have hx(z:Per (More N)):along 0 z=z.val:=by simp [along]
 by_cases g:x=y; subst y; omega
 have hz:= Circle.lag x y g; rcases (Circle.δle x b y).1 t with q|q; · have hp:=Circle.deposit 0 x y (by rw [hx]; have := natM N; have hk:0<N.val:=N.property; omega); rw [hx,hx] at hp; omega
 have h':= Circle.triangle (0:Per (More N)) y x; rw [hx,hx] at h'; by_cases hp:y.val≤ x.val; omega
 have hM:= Circle.distance 0 x y (by rw [hx,hx]; omega); rw [hx,hx] at hM; have hk:=natM N; have hh:= ZMod.val_lt y; omega -- wrap backwards impossible (if c=0,b=a? y x path crosses plane requires >)
lemma moveS (q:Bool){x y:Seat N}(h:x∈shade N i q a)(v:separation x y≤b)(x':b+c≤a): y∈shade N i q c:=by
 obtain ⟨k,l⟩:= (shine i).mp h; apply (shine i).2; exact fortuna _ _ k l (by rw [delta i]; exact (component_le (x-y) i).trans v) x' -- tune varying ends ν
lemma mono (p:b≤c)(q:Bool): shade N i q c⊆ shade N i q b:=fun _ h=>moveS i q h (le_of_eq (separation_self _)) (by omega)
lemma hedge (p:b+c≤a)(q:Bool): halo b (shade N i q a) ⊆ shade N i q c:=fun _ h=> let ⟨x,v,w⟩:=halo_spec.mp h; moveS i q v w p
lemma splits(q:Bool)(p:0<b) : Disjoint (shade N i q b) (shade N i (!q) b):=by
 have h(z:Seat N)(t:z∈ shade N i true b) (v:z∈shade N i false b):False:=by
    obtain ⟨l,k⟩:= (shine i|>.1 t); obtain ⟨r,s⟩:= (shine i|>.1 v); simp only [toward,Bool.false_eq_true,↓reduceIte] at *; rw [ZMod.neg_val, if_neg] at s r; have he:=natM N; omega; intro e; rw [e,ZMod.val_zero] at l; omega; intro e; rw [e,ZMod.val_zero] at l; omega
 apply Finset.disjoint_left.mpr; intro z v t; cases q; exact h z t v; exact h z v t
lemma gap(q:Bool){x y:Seat N}(h:x∈shade N i q a)(g:y∈shade N i (!q) a)(p:b<a):b<separation x y:=by
 apply lt_of_not_ge; intro v; have he:= moveS i q h v (c:=1) (by omega); exact Finset.disjoint_left.mp (splits (N:=N) i q (b:=1) (by omega)) he (mono i (by omega) _ g)
lemma north (N) (z:ℕ): shade N i true z ⊆ RP.north N i:=fun x p=> RP.north_mem x i |>.2 (show (x i).val ≤ N.val from by have h: (x i).val+z ≤ N.val:=((shine i).1 p).2; omega)
variable (G: Ratio N P)
lemma val_m (q:Bool)(p:Seat N): (toward q ((ratio G).embed p i)).val=(toward q (p i)).val*G.count.val:=by
 have hx(x:Per (More N)) : (base (ratio G) x).val=x.val*G.count.val:=by
    have hp:=subdiv_val (ratio G) x (show 0<G.count.val from G.count.property); rw [Nat.cast_zero,add_zero] at hp; exact hp
 rw [base_apply]; cases q; change (-base (ratio G) (p i)).val= _; rw [show -base _ (p i)=_ from neg_eq_of_add_eq_zero_right (by rw [←base_add,add_neg_cancel, base_zero] : base (ratio G) (p i)+base (ratio G) (-p i)=0)]; exact hx _ -- tune name
 exact hx _
lemma embedW (q:Bool)(x:Seat N): (ratio G).embed x∈ shade P i q (a*G.count.val) ↔ x∈ shade N i q a:=by
 rw [shine,shine,val_m,G.exact_size, ←add_mul, mul_le_mul_iff_left₀ (show 0 < G.count.val from G.count.property), mul_le_mul_iff_left₀ (show 0 < G.count.val from G.count.property)] -- tune
end Half
end YM.CF.BProof.Bide
