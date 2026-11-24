import YM.CF.Nacre.Tow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font Spire
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}
lemma mores(a:Shape)(U:Bkg (More n)): Yg a U= Lattice.pull a.s (wrap _ (2 • a.t)) U:=rfl
lemma van(a:Shape)(g:Site (More n)→E)(U:Bkg (More n)): Yg a (Lattice.gauge g U)= Lattice.gauge (g∘ a.anon n) (Yg a U):=by
 funext ⟨x,i⟩; change (posDir i).read (stir inert a (Lattice.gauge g U)) x= (g (a.anon n x)) * Yg a U (x,i)* (g (a.anon n (x+step i)))⁻¹; rw [veil_x,Step.gauge_read]; rw [show a.anon n (x+Lattice.step i)=a.anon n x+((posDir i).rotate a.s).vec from salt a (posDir i) x]; rfl
lemma envoy (a:Shape)(U:UNI SpinIdx)(g:Site (More n)→E): (prepU a U inert n) * tradew n g=tradew n (g ∘ a.anon n)*(prepU a U inert n):=by
 let G(g:Site (More n)→ E)(x:Site n):Op (SpinIdx×Slot):=1⊗ₖ (matter (g (node x))).val
 have he(g:Site (More n)→E):(tradew n g).val=love n (jump (Equiv.refl _) (G g)):=by
   ext ⟨⟨x,i⟩,k⟩ ⟨⟨y,j⟩,l⟩; change jump (Equiv.refl (Site n × SpinIdx)) (fun i=> (matter (g (node i.1))).val) ((x,i),k) ((y,j),l)= jump (Equiv.refl _) (G g) (x,(i,k)) (y,(j,l)); by_cases hx:x=y <;> by_cases hg:i=j<;> simp [G,hg,hx,jump_apply]
 apply Subtype.ext; change (love n ((mealU a U inert n).val))*(tradew ..).val=_*(love n _); rw [he,he,←map_mul,← map_mul]; apply congrArg (love n)
 let f:=(Tofu a n); let p:=g ∘ a.anon n
 change jump f (fun i=>(milU a U inert i).val)*_= _*jump f _; rw [jump_mul,jump_mul,Equiv.trans_refl,Equiv.refl_trans]; congr 1; ext1 i
 change ((a.payA i) • (U.val ⊗ₖ (1:Op Slot)))*(1 ⊗ₖ (matter (g (node (a.mills n i)))).val)=( (1:Op SpinIdx) ⊗ₖ (matter (p (node i))).val)* (a.payA i • (U.val ⊗ₖ (1:Op Slot))); rw [Shape.nodex,Matrix.smul_mul,Matrix.mul_smul,op_kron_mul,op_kron_mul,mul_one,one_mul,mul_one,one_mul]; rfl
lemma GaugeT(a:Shape)(g:Site (More n)→E)(X:Op (Single n)): ZoneH a (twist (tradew n g) X)= twist (tradew n (g ∘ a.anon n)) (ZoneH a X):=by
 rw [zone_c,zone_c]; unfold ape; rw [←twin,envoy,twin]; unfold Thera.jazz; split; rw [map_neg,map_star]; rfl

lemma Ywin(a:Signed)(U:Bkg (More n)): Yg (incX a) U= Lattice.pull a 0 U:=by rw [mores]; simp only [incX,smul_zero,map_zero]
lemma Ylag(t:Cover)(U:Bkg (More n)):Yg (lagX t) U=Lattice.translate (wrap _ (2 • t)) U:=by rw [mores]; exact Lattice.pull_one ..
lemma vines(u:Cover)(v:Signed): joinX (lagX u) (incX v) = ⟨v,u⟩:=by simp [joinX,incX,lagX]
lemma wink (a b:Signed): joinX (incX a) (incX b)=incX (a*b):=by simp [joinX,incX]
lemma trips(u v:Cover): joinX (lagX u) (lagX v)=lagX (u+v):=by simp [joinX,lagX,add_comm]
lemma scone(u:Signed)(x:Cover): joinX (incX u) (lagX x)= joinX (lagX (u.act x)) (incX u):=by simp [joinX,lagX,incX]
end YM.CF.Nacre
