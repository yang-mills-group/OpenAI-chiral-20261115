import YM.CF.Laic.Nerve
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n c:Side}{ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{Z: Positions ι→Bkg (More n)}{k:ℕ}{l:ι→Site c}{u:κ→Site n}{x:Positions ι}{a b d:ℝ}
lemma faroS (s:Signed)(u:Site (More n)): (incX s).anon n u=s.act u:=by simp [Shape.anon,affine,incX]
lemma lagY (s:Signed){V:Site (More n)→Site c}{B:ℕ}(p:Yoke l Z V B) : Yoke l (Yg (incX s) ∘ Z) (V ∘ (incX s).anon n) (2*B):=by
 let a:= (incX s); constructor
 · intro i j; unfold Function.comp; rw [faroS,faroS]; apply (p.meter ..).trans; rw [separation_signed]; gcongr; omega
 intro x y i he; let t:= (posDir i.2).rotate s; let z:= s.act i.1; have hh:together l (V (t.used z).1) B x y:=by
    intro j g; apply he; unfold Function.comp; rw [faroS]; apply (separation_triangle _ (V (t.used z).1) _).trans; apply (add_le_add (p.meter ..) g).trans; have h:= Nat.mul_le_mul_left B (letter_position z t); linarith
 have ht:= p.serves (t.used z) hh; simp only [Function.comp_apply,Ywin]; unfold Lattice.pull Step.read; simp only [affine,add_zero]; rw [ht]
lemma absW {t:κ→ Site c}{α:Type}(s:Finset α)(C:α→ℝ){F:α→ Positions ι → Op κ}(h:∀ i∈s,CableM l t t a k (F i) x (C i))(v:∀ i∈s,ContDiffAt ℝ ω (F i) x):CableM l t t a k (fun x=> ∑ i∈s,F i x) x (∑ i∈s,C i):=by
 intro r i j; have hx: (∑ v∈s,C v)*Decay a (t i) (t j) * Planned.JetPort.thread none a (t i)=∑ v∈s, C v*Decay a (t i) (t j)*Planned.JetPort.thread none a (t i):=by simp_rw [Finset.sum_mul];
 rw [hx]; simp only [Function.comp_apply,coinZ,Matrix.map_apply,Matrix.sum_apply,map_sum]; exact beacon_sum (s:=s) (p:=x) (C:=fun k=> C k*Decay a (t i) (t j)*Planned.JetPort.thread none a (t i)) (f:=fun k x=> coinZ r (F k x) i j) (fun k hk=>h k hk r i j) (fun k ht=> inkJet r (Nacre.tort.mp (v _ ht)) i j)
lemma inkD {F:Positions ι→ Op κ}{t:κ→ Site c}(v:smooth F x)(h:CableM l t t a k F x b)(p:ℝ):CableM l t t a k (fun x=>p • F x) x (|p| *b):=by
 intro r; convert Cable.scale (F:=(coinZ r ∘ F)) (inkJet r v) (h r) p using 1; funext i; apply Matrix.ext; intro x y; exact map_smul (matte r) p _
lemma savoy (a b:ℝ)(k m B:ℕ)(p:0<a)(v:0≤b):∃ c C:ℝ,0<c∧0<C ∧∀{n r:Side}{ι:Type}[Fintype ι]{l:ι→Site r}{Z:Positions ι→ Bkg (More n)}{z:Site (More n)→ Site r}, (∀ i:Signed, Yoke l (Yg (incX i) ∘ Z) (z ∘ (incX i).anon n) B) → Z 0=1→ EnvM k Z 0 b →∀ (J:Toy m n)(V:ℝ),0≤V→(∀ i,balance a J i ≤V)→ ContDiffAt ℝ ω (sumU (cavil J) ∘ Z) 0 ∧ CableM l (z ∘ place_x) (z ∘ place_x) c k (sumU (cavil J) ∘ Z) 0 (V*C):=by
 obtain ⟨d,b',h,hb,H⟩:=stout m k p v B; have hp:0 < insD:=by unfold insD; positivity
 refine ⟨slip k d, insD*b',slip_pos k h, mul_pos hp hb,?_⟩
 intro n r ι I l Z z e w P J V q t; let f:=cavil J; let T(i: Signed):=foil i f ∘ Z; let A:= (z ∘ place_x); let S(i: Signed):= Yg (incX i⁻¹) ∘ Z
 have hz(i):=H (e i⁻¹) (show S i 0=1 from by unfold S; rw [Function.comp_apply,w,Ywin]; exact congrArg Prod.fst (Stationary.twistUniform_one (G:=group) (f:=More n) (c:=More n) _)) (swellT P _) J V t
 have hh(a):ContDiffAt ℝ ω (T a) 0:= (ZoneH _).contDiff.contDiffAt.comp _ (Nacre.tort.mpr (hz a).1)
 let u:= (Fintype.card Signed:ℝ)⁻¹; have hv := ContDiffAt.sum (f:=fun i x=>T i x) (s:=Finset.univ) (fun i _=>hh i); refine ⟨hv.const_smul u,?_⟩
 have hs:=absW (Finset.univ) _ (F:=T) (fun i _=> show CableM l A A (slip k d) k (T i) 0 (insD*(V*b')) from billW (hz i).1 i (hz i).2 (mul_nonneg q hb.le) h) (fun i _=>hh i) -- tune
 apply (inkD (Nacre.tort.mp hv) hs u).books; simp only [sum_const,card_univ,nsmul_eq_mul]; unfold u; rw [abs_of_nonneg (by positivity), inv_mul_cancel_left₀ (by positivity)]; exact le_of_eq (by ring)
end YM.CF.Laic
